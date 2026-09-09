import SparseFockFormal.NamedBands
import SparseFockFormal.FiniteHilbert
import SparseFockFormal.TypedBlockCS
import SparseFockFormal.ParsevalFrame
import SparseFockFormal.ConcreteLadder
import SparseFockFormal.DirectionalConcrete
import SparseFockFormal.MatrixTail
import SparseFockFormal.BandCoefficientBounds
import SparseFockFormal.BandEnvelope
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

/-!
# Concrete heavy--heavy band estimates

This module realizes the heavy row legs from the paper on the literal finite
pattern basis and proves the restricted heavy-band bounds.
-/

namespace SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The row-local occupation grade used in the heavy-leg argument. -/
def rowGrade (p : Pattern m n) (r : Fin m) : ℕ :=
  (p.lightInRow r).card + 2 * (p.heavyInRow r).card

theorem sum_rowGrade (p : Pattern m n) :
    (∑ r, rowGrade p r) = p.grade := by
  classical
  simp only [rowGrade, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Pattern.card_light_eq_sum_card_lightInRow,
    ← Pattern.card_heavy_eq_sum_card_heavyInRow,
    Pattern.grade_eq_card_light_add_two_mul_card_heavy]

/-- Replace the level at one concrete site. -/
def setSite (p : Pattern m n) (s : Site m n) (a : Level) : Pattern m n :=
  Function.update p s a

@[simp] theorem setSite_apply_self (p : Pattern m n) (s : Site m n) (a : Level) :
    setSite p s a s = a := by
  simp [setSite]

theorem setSite_apply_of_ne (p : Pattern m n) {s t : Site m n}
    (hst : t ≠ s) (a : Level) :
    setSite p s a t = p t := by
  simp [setSite, hst]

theorem setSite_restore (p : Pattern m n) (s : Site m n) {a b : Level}
    (hs : p s = a) : setSite (setSite p s b) s a = p := by
  funext t
  by_cases h : t = s
  · subst t
    simpa using hs.symm
  · simp [setSite, h]

theorem agreesOutsideSite_setSite (p : Pattern m n) (s : Site m n) (a : Level) :
    agreesOutsideSite s p (setSite p s a) := by
  intro t hts
  symm
  exact setSite_apply_of_ne p hts a

theorem eq_setSite_iff {out inp : Pattern m n} {s : Site m n} (a : Level) :
    inp = setSite out s a ↔ agreesOutsideSite s out inp ∧ inp s = a := by
  constructor
  · rintro rfl
    exact ⟨agreesOutsideSite_setSite out s a, setSite_apply_self out s a⟩
  · rintro ⟨hout, hs⟩
    funext t
    by_cases hts : t = s
    · subst t
      simpa using hs
    · rw [setSite_apply_of_ne out hts]
      exact (hout t hts).symm

/-- Exact coefficient of a lifted one-site rank-one transition. -/
theorem siteKernel_ketBra_apply (s : Site m n) (outLevel inpLevel : Level)
    (out inp : Pattern m n) :
    siteKernel s (ketBra outLevel inpLevel) out inp =
      if out s = outLevel ∧ inp = setSite out s inpLevel then 1 else 0 := by
  classical
  simp only [siteKernel, ketBra]
  by_cases hoff : agreesOutsideSite s out inp
  · rw [if_pos hoff]
    by_cases ho : out s = outLevel
    · have heq : inp = setSite out s inpLevel ↔ inp s = inpLevel := by
        rw [eq_setSite_iff]
        simp [hoff]
      by_cases hi : inp s = inpLevel
      · simp [ho, hi, heq.mpr hi]
      · have hne : inp ≠ setSite out s inpLevel := by
          intro h
          exact hi (heq.mp h)
        simp [ho, hi, hne]
    · simp [ho]
  · rw [if_neg hoff]
    have hne : inp ≠ setSite out s inpLevel := by
      intro h
      apply hoff
      rw [h]
      exact agreesOutsideSite_setSite out s inpLevel
    simp [hne]

/-- A pattern with one marked site in a specified local state. -/
structure MarkedSite (m n : ℕ) (a : Level) where
  pattern : Pattern m n
  row : Fin m
  col : Fin n
  state : pattern (row, col) = a
  deriving DecidableEq, Fintype

theorem MarkedSite.ext' {a : Level} {x y : MarkedSite m n a}
    (hp : x.pattern = y.pattern) (hr : x.row = y.row) (hc : x.col = y.col) :
    x = y := by
  cases x
  cases y
  simp_all

def markedSiteEquivSigma (a : Level) :
    MarkedSite m n a ≃
      Σ p : Pattern m n, Σ r : Fin m, {i : Fin n // p (r, i) = a} where
  toFun z := ⟨z.pattern, ⟨z.row, ⟨z.col, z.state⟩⟩⟩
  invFun z :=
    { pattern := z.1
      row := z.2.1
      col := z.2.2.1
      state := z.2.2.2 }
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨p, r, i⟩; rfl

/-- Expand a sum over a marked-state subtype into its literal pattern/row/site
sum.  This is the bookkeeping bridge used by both marked reindexings. -/
theorem sum_markedSite (a : Level) (f : Pattern m n → Fin m → Fin n → ℝ) :
    (∑ p, ∑ r, ∑ i ∈ Finset.univ.filter (fun i ↦ p (r, i) = a), f p r i) =
      ∑ z : MarkedSite m n a, f z.pattern z.row z.col := by
  classical
  calc
    (∑ p, ∑ r, ∑ i ∈ Finset.univ.filter (fun i ↦ p (r, i) = a),
        f p r i) =
        ∑ p, ∑ r, ∑ i : {i : Fin n // p (r, i) = a}, f p r i := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_subtype _ (by simp) (f p r)
    _ = ∑ z : Σ p : Pattern m n,
          Σ r : Fin m, {i : Fin n // p (r, i) = a},
          f z.1 z.2.1 z.2.2.1 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro p _
      rw [Fintype.sum_sigma]
    _ = ∑ z : MarkedSite m n a, f z.pattern z.row z.col := by
      have h := Equiv.sum_comp (markedSiteEquivSigma (m := m) (n := n) a)
        (fun z : Σ p : Pattern m n,
          Σ r : Fin m, {i : Fin n // p (r, i) = a} ↦
            f z.1 z.2.1 z.2.2.1)
      simpa [markedSiteEquivSigma] using h.symm

/-- Changing the marked local state is a genuine finite equivalence. -/
def markedTransition (a b : Level) :
    MarkedSite m n a ≃ MarkedSite m n b where
  toFun z :=
    { pattern := setSite z.pattern (z.row, z.col) b
      row := z.row
      col := z.col
      state := setSite_apply_self _ _ _ }
  invFun z :=
    { pattern := setSite z.pattern (z.row, z.col) a
      row := z.row
      col := z.col
      state := setSite_apply_self _ _ _ }
  left_inv z := by
    cases z with
    | mk p r i h =>
      simp only
      exact MarkedSite.ext' (setSite_restore (b := b) p (r, i) h) rfl rfl
  right_inv z := by
    cases z with
    | mk p r i h =>
      simp only
      exact MarkedSite.ext' (setSite_restore (b := a) p (r, i) h) rfl rfl

/-- A marked-site sum may be reindexed without multiplicity loss. -/
theorem sum_markedTransition (a b : Level)
    (f : MarkedSite m n b → ℝ) :
    (∑ z : MarkedSite m n a, f (markedTransition a b z)) =
      ∑ z : MarkedSite m n b, f z :=
  Equiv.sum_comp (markedTransition a b) f

theorem sum_marked_reindex (a b : Level) (f : MarkedSite m n a → ℝ) :
    (∑ z : MarkedSite m n a, f z) =
      ∑ z : MarkedSite m n b, f ((markedTransition a b).symm z) := by
  have h := Equiv.sum_comp (markedTransition a b).symm f
  simpa using h.symm

theorem heavyInRow_setSite_two {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) ≠ .two) :
    (setSite p (r, i) .two).heavyInRow r = insert i (p.heavyInRow r) := by
  classical
  ext j
  simp only [Pattern.mem_heavyInRow, Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    simp
  · have hpair : (r, j) ≠ (r, i) := by
      intro h
      exact hji (congrArg Prod.snd h)
    rw [setSite_apply_of_ne p hpair]
    simp [hji]

theorem lightInRow_setSite_one {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) ≠ .one) :
    (setSite p (r, i) .one).lightInRow r = insert i (p.lightInRow r) := by
  classical
  ext j
  simp only [Pattern.mem_lightInRow, Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    simp
  · have hpair : (r, j) ≠ (r, i) := by
      intro h
      exact hji (congrArg Prod.snd h)
    rw [setSite_apply_of_ne p hpair]
    simp [hji]

theorem card_heavyInRow_setSite_two {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .one) :
    ((setSite p (r, i) .two).heavyInRow r).card =
      (p.heavyInRow r).card + 1 := by
  rw [heavyInRow_setSite_two (by simp [hi])]
  have hnot : i ∉ p.heavyInRow r := by simp [hi]
  simp [hnot]

theorem card_lightInRow_setSite_one {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .two) :
    ((setSite p (r, i) .one).lightInRow r).card =
      (p.lightInRow r).card + 1 := by
  rw [lightInRow_setSite_one (by simp [hi])]
  have hnot : i ∉ p.lightInRow r := by simp [hi]
  simp [hnot]

theorem card_heavy_after_promote_le_rowGrade
    {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .one) :
    ((setSite p (r, i) .two).heavyInRow r).card ≤ rowGrade p r := by
  rw [card_heavyInRow_setSite_two hi]
  have hpos : 1 ≤ (p.lightInRow r).card := by
    exact Finset.one_le_card.mpr ⟨i, by simp [hi]⟩
  simp only [rowGrade]
  omega

theorem card_light_after_demote_le_rowGrade
    {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .two) :
    ((setSite p (r, i) .one).lightInRow r).card ≤ rowGrade p r := by
  rw [card_lightInRow_setSite_one hi]
  have hpos : 1 ≤ (p.heavyInRow r).card := by
    exact Finset.one_le_card.mpr ⟨i, by simp [hi]⟩
  simp only [rowGrade]
  omega

/-- The lifted local heavy creation and annihilation matrices. -/
def rUpAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) rPromote

def rDownAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) rDemote

@[simp] theorem rUpAt_transpose (r : Fin m) (i : Fin n) :
    (rUpAt r i).transpose = rDownAt r i := by
  simp [rUpAt, rDownAt, transpose_siteKernel]

@[simp] theorem rDownAt_transpose (r : Fin m) (i : Fin n) :
    (rDownAt r i).transpose = rUpAt r i := by
  simp [rUpAt, rDownAt, transpose_siteKernel]

/-- The paper's heavy analysis leg `A_r`. -/
def AUpMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun σ inp ↦ ∑ i, F.u i inp.1 * rUpAt r i σ inp.2

/-- The paper's adjoint heavy analysis leg `Ã_r`. -/
def ADownMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun σ inp ↦ ∑ i, F.u i inp.1 * rDownAt r i σ inp.2

/-- The paper's heavy synthesis leg `B_r`. -/
def BUpMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out τ ↦ ∑ i, F.u i out.1 * rUpAt r i out.2 τ

/-- External Euclidean fiber at one Fock pattern. -/
def fiber (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) : EVec d :=
  WithLp.toLp 2 (fun k ↦ x (k, p))

@[simp] theorem fiber_apply (x : Fin d × Pattern m n → ℝ)
    (p : Pattern m n) (k : Fin d) : fiber x p k = x (k, p) := rfl

theorem rUpAt_apply (r : Fin m) (i : Fin n) (out inp : Pattern m n) :
    rUpAt r i out inp =
      if out (r, i) = .two ∧ inp = setSite out (r, i) .one then 1 else 0 := by
  simpa [rUpAt, rPromote] using
    siteKernel_ketBra_apply (m := m) (n := n) (r, i) .two .one out inp

theorem rDownAt_apply (r : Fin m) (i : Fin n) (out inp : Pattern m n) :
    rDownAt r i out inp =
      if out (r, i) = .one ∧ inp = setSite out (r, i) .two then 1 else 0 := by
  simpa [rDownAt, rDemote] using
    siteKernel_ketBra_apply (m := m) (n := n) (r, i) .one .two out inp

theorem one_rUp_analysis (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    (∑ inp : Fin d × Pattern m n,
        (F.u i inp.1 * rUpAt r i σ inp.2) * x inp) =
      if σ (r, i) = .two then
        analyze F (fiber x (setSite σ (r, i) .one)) i else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  by_cases hi : σ (r, i) = .two
  · simp only [rUpAt_apply, hi, true_and, if_true]
    simp only [analyze, fiber, PiLp.inner_apply, Real.inner_apply, PiLp.toLp_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp
  · simp [rUpAt_apply, hi]

theorem one_rDown_analysis (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    (∑ inp : Fin d × Pattern m n,
        (F.u i inp.1 * rDownAt r i σ inp.2) * x inp) =
      if σ (r, i) = .one then
        analyze F (fiber x (setSite σ (r, i) .two)) i else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  by_cases hi : σ (r, i) = .one
  · simp only [rDownAt_apply, hi, true_and, if_true]
    simp only [analyze, fiber, PiLp.inner_apply, Real.inner_apply, PiLp.toLp_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp
  · simp [rDownAt_apply, hi]

theorem AUpMatrix_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (σ : Pattern m n) :
    Matrix.mulVec (AUpMatrix F r) x σ =
      ∑ i ∈ σ.heavyInRow r,
        analyze F (fiber x (setSite σ (r, i) .one)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, AUpMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [one_rUp_analysis]
  rw [Pattern.heavyInRow, Finset.sum_filter]

theorem ADownMatrix_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (σ : Pattern m n) :
    Matrix.mulVec (ADownMatrix F r) x σ =
      ∑ i ∈ σ.lightInRow r,
        analyze F (fiber x (setSite σ (r, i) .two)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, ADownMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [one_rDown_analysis]
  rw [Pattern.lightInRow, Finset.sum_filter]

/-- Squared Euclidean energy on the scalar Fock-pattern space. -/
def fockNormSq (y : Pattern m n → ℝ) : ℝ := ∑ p, y p ^ 2

theorem full_normSq_eq_sum_fiber (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq x = ∑ p, ParsevalFrame.normSq (fiber x p) := by
  simp only [FiniteHilbert.normSq, ParsevalFrame.normSq, PiLp.inner_apply,
    Real.inner_apply, fiber, PiLp.toLp_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem fiber_gradeProjection (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fiber (Matrix.mulVec (gradeProjection (d := d) nu) x) p =
      if p.grade = nu then fiber x p else 0 := by
  ext k
  by_cases hp : p.grade = nu <;>
    simp [fiber, gradeProjection_mulVec, hp]

theorem weighted_gradeProjection (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, (p.grade : ℝ) * ParsevalFrame.normSq
      (fiber (Matrix.mulVec (gradeProjection (d := d) nu) x) p)) =
      (nu : ℝ) * FiniteHilbert.normSq
        (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
  rw [full_normSq_eq_sum_fiber]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [fiber_gradeProjection]
  by_cases hp : p.grade = nu
  · subst nu
    simp
  · simp [hp, ParsevalFrame.normSq]

/-- The summed `A_r` energy is bounded by the total occupation-number
quadratic form, on the literal pattern basis. -/
theorem AUp_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, fockNormSq (Matrix.mulVec (AUpMatrix F r) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  classical
  calc
    (∑ r, fockNormSq (Matrix.mulVec (AUpMatrix F r) x)) =
        ∑ r, ∑ σ,
          (∑ i ∈ σ.heavyInRow r,
            analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      simp only [fockNormSq, AUpMatrix_mulVec]
    _ ≤ ∑ r, ∑ σ,
        ((σ.heavyInRow r).card : ℝ) *
          ∑ i ∈ σ.heavyInRow r,
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro σ _
      exact sq_sum_le_card_mul_sum_sq
    _ = ∑ σ, ∑ r,
        ((σ.heavyInRow r).card : ℝ) *
          ∑ i ∈ σ.heavyInRow r,
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.heavyInRow r,
        ((σ.heavyInRow r).card : ℝ) *
          (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ = ∑ z : MarkedSite m n .two,
        ((z.pattern.heavyInRow z.row).card : ℝ) *
          (analyze F
            (fiber x (setSite z.pattern (z.row, z.col) .one)) z.col) ^ 2 := by
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun σ r i ↦ ((σ.heavyInRow r).card : ℝ) *
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .one,
        ((((setSite z.pattern (z.row, z.col) .two).heavyInRow z.row).card : ℕ) : ℝ) *
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .two .one]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ ≤ ∑ z : MarkedSite m n .one,
        (rowGrade z.pattern z.row : ℝ) *
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_heavy_after_promote_le_rowGrade z.state)
        (sq_nonneg _)
    _ = ∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
        (rowGrade p r : ℝ) * (analyze F (fiber x p) i) ^ 2 := by
      symm
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p r i ↦ (rowGrade p r : ℝ) *
            (analyze F (fiber x p) i) ^ 2)
    _ = ∑ p, ∑ r, (rowGrade p r : ℝ) *
        ∑ i ∈ p.lightInRow r, (analyze F (fiber x p) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ ≤ ∑ p, ∑ r, (rowGrade p r : ℝ) *
        ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (subset_analysis F (p.lightInRow r) (fiber x p)) (Nat.cast_nonneg _)
    _ = ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul]
      norm_cast
      rw [sum_rowGrade]

/-- The same occupation-number estimate for the demotion analysis legs
`Ã_r`. -/
theorem ADown_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, fockNormSq (Matrix.mulVec (ADownMatrix F r) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  classical
  calc
    (∑ r, fockNormSq (Matrix.mulVec (ADownMatrix F r) x)) =
        ∑ r, ∑ σ,
          (∑ i ∈ σ.lightInRow r,
            analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 := by
      simp only [fockNormSq, ADownMatrix_mulVec]
    _ ≤ ∑ r, ∑ σ,
        ((σ.lightInRow r).card : ℝ) *
          ∑ i ∈ σ.lightInRow r,
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro σ _
      exact sq_sum_le_card_mul_sum_sq
    _ = ∑ σ, ∑ r,
        ((σ.lightInRow r).card : ℝ) *
          ∑ i ∈ σ.lightInRow r,
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.lightInRow r,
        ((σ.lightInRow r).card : ℝ) *
          (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ = ∑ z : MarkedSite m n .one,
        ((z.pattern.lightInRow z.row).card : ℝ) *
          (analyze F
            (fiber x (setSite z.pattern (z.row, z.col) .two)) z.col) ^ 2 := by
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun σ r i ↦ ((σ.lightInRow r).card : ℝ) *
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .two,
        ((((setSite z.pattern (z.row, z.col) .one).lightInRow z.row).card : ℕ) : ℝ) *
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .one .two]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ ≤ ∑ z : MarkedSite m n .two,
        (rowGrade z.pattern z.row : ℝ) *
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_light_after_demote_le_rowGrade z.state)
        (sq_nonneg _)
    _ = ∑ p, ∑ r, ∑ i ∈ p.heavyInRow r,
        (rowGrade p r : ℝ) * (analyze F (fiber x p) i) ^ 2 := by
      symm
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p r i ↦ (rowGrade p r : ℝ) *
            (analyze F (fiber x p) i) ^ 2)
    _ = ∑ p, ∑ r, (rowGrade p r : ℝ) *
        ∑ i ∈ p.heavyInRow r, (analyze F (fiber x p) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ ≤ ∑ p, ∑ r, (rowGrade p r : ℝ) *
        ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (subset_analysis F (p.heavyInRow r) (fiber x p)) (Nat.cast_nonneg _)
    _ = ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul]
      norm_cast
      rw [sum_rowGrade]

/-- First concrete heavy-leg inequality, restricted to exact total grade. -/
theorem AUp_grade_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, fockNormSq (Matrix.mulVec (AUpMatrix F r)
      (Matrix.mulVec (gradeProjection (d := d) nu) x))) ≤
      (nu : ℝ) * FiniteHilbert.normSq x := by
  calc
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq
        (fiber (Matrix.mulVec (gradeProjection (d := d) nu) x) p) :=
      AUp_energy_le_weighted F _
    _ = (nu : ℝ) * FiniteHilbert.normSq
        (Matrix.mulVec (gradeProjection (d := d) nu) x) :=
      weighted_gradeProjection nu x
    _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left (gradeProjection_normSq_le nu x)
        (Nat.cast_nonneg _)

/-- Second concrete heavy-leg inequality, for the demotion legs. -/
theorem ADown_grade_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, fockNormSq (Matrix.mulVec (ADownMatrix F r)
      (Matrix.mulVec (gradeProjection (d := d) nu) x))) ≤
      (nu : ℝ) * FiniteHilbert.normSq x := by
  calc
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq
        (fiber (Matrix.mulVec (gradeProjection (d := d) nu) x) p) :=
      ADown_energy_le_weighted F _
    _ = (nu : ℝ) * FiniteHilbert.normSq
        (Matrix.mulVec (gradeProjection (d := d) nu) x) :=
      weighted_gradeProjection nu x
    _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left (gradeProjection_normSq_le nu x)
        (Nat.cast_nonneg _)

/-- Row-indexed scalar Fock output space for the block analysis operator. -/
abbrev RowFock (m n : ℕ) := Fin m × Pattern m n

def AUpStack (F : Frame n d) :
    Matrix (RowFock m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ AUpMatrix F out.1 out.2 inp

def ADownStack (F : Frame n d) :
    Matrix (RowFock m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ ADownMatrix F out.1 out.2 inp

def BUpStack (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (RowFock m n) ℝ :=
  fun out inp ↦ BUpMatrix F inp.1 out inp.2

@[simp] theorem BUpStack_transpose (F : Frame n d) :
    (BUpStack (m := m) F).transpose = ADownStack (m := m) F := by
  ext out inp
  simp only [BUpStack, ADownStack, Matrix.transpose_apply]
  simp only [BUpMatrix, ADownMatrix]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
    (rUpAt_transpose out.1 i)
  simpa [Matrix.transpose_apply] using h

theorem rUpAt_sq_zero (r : Fin m) (i : Fin n) :
    rUpAt r i * rUpAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .two
  · simp only [rUpAt_apply, hout, true_and, if_true]
    rw [Finset.sum_eq_single (setSite out (r, i) .one)]
    · simp [setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [rUpAt_apply, hout]

def frameRows (F : Frame n d) : Fin n → Fin d → ℝ :=
  fun i k ↦ F.u i k

def BUpOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out p ↦ F.u i out.1 * rUpAt r i out.2 p

def AUpOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun p inp ↦ F.u i inp.1 * rUpAt r i p inp.2

theorem BUpMatrix_eq_sum_one (F : Frame n d) (r : Fin m) :
    BUpMatrix F r = ∑ i, BUpOne F r i := by
  ext out p
  simp [BUpMatrix, BUpOne, Matrix.sum_apply]

theorem AUpMatrix_eq_sum_one (F : Frame n d) (r : Fin m) :
    AUpMatrix F r = ∑ i, AUpOne F r i := by
  ext p inp
  simp [AUpMatrix, AUpOne, Matrix.sum_apply]

theorem rUpAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    rUpAt r i * rUpAt r j = wordKernel (r, i) (r, j) (.rUp, .rUp) := by
  simpa [rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) rPromote rPromote

theorem BUpOne_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    BUpOne F r i * AUpOne F r j =
      orderedWordTerm (frameRows F) r i j (.rUp, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, BUpOne, AUpOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * rUpAt r i out.2 p) *
        (F.u j inp.1 * rUpAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, rUpAt r i out.2 p * rUpAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.rUp, .rUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rUpAt_mul_rUpAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

theorem BUpOne_mul_AUpOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    BUpOne F r i * AUpOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, BUpOne, AUpOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * rUpAt r i out.2 p) *
        (F.u i inp.1 * rUpAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, rUpAt r i out.2 p * rUpAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rUpAt_sq_zero r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Exact nilpotent row-leg factorization of one physical heavy `+2` row.
The diagonal terms disappear because `R² = 0`, leaving precisely `i ≠ j`. -/
theorem BUpMatrix_mul_AUpMatrix (F : Frame n d) (r : Fin m) :
    BUpMatrix F r * AUpMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (frameRows F) r i j (.rUp, .rUp) := by
  classical
  rw [BUpMatrix_eq_sum_one, AUpMatrix_eq_sum_one, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [BUpOne_mul_AUpOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact BUpOne_mul_AUpOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The named concrete `H₊` is exactly the product of the typed row
synthesis and analysis matrices. -/
theorem Hplus_eq_BUpStack_mul_AUpStack (F : Frame n d) :
    Hplus m (frameRows F) = BUpStack (m := m) F * AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [Hplus, wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, BUpStack, AUpStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg
    (fun M : FullOp d m n ↦ M out inp) (BUpMatrix_mul_AUpMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

theorem AUpMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Pattern m n} {inp : Fin d × Pattern m n}
    (hentry : AUpMatrix F r out inp ≠ 0) :
    (out.grade : ℤ) = (inp.2.grade : ℤ) + 1 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : rUpAt r i out inp.2 ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous rPromote_homogeneous (r, i) hk
  simpa [rUpAt, gradeZ_eq_cast_grade] using hh

theorem ADownMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Pattern m n} {inp : Fin d × Pattern m n}
    (hentry : ADownMatrix F r out inp ≠ 0) :
    (out.grade : ℤ) + 1 = (inp.2.grade : ℤ) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : rDownAt r i out inp.2 ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous rDemote_homogeneous (r, i) hk
  have hz : (out.grade : ℤ) = (inp.2.grade : ℤ) - 1 := by
    simpa [rDownAt, gradeZ_eq_cast_grade, sub_eq_add_neg] using hh
  omega

/-- Orthogonal projection on the middle row/Fock space; the row label does
not contribute to occupation grade. -/
def rowGradeProjection (mu : ℕ) : Matrix (RowFock m n) (RowFock m n) ℝ :=
  Matrix.diagonal fun x ↦ if x.2.grade = mu then 1 else 0

@[simp] theorem rowGradeProjection_transpose (mu : ℕ) :
    (rowGradeProjection (m := m) (n := n) mu).transpose = rowGradeProjection mu := by
  ext out inp
  by_cases h : out = inp
  · subst inp
    simp [rowGradeProjection, Matrix.transpose_apply, Matrix.diagonal_apply]
  · have h' : inp ≠ out := Ne.symm h
    simp [rowGradeProjection, Matrix.transpose_apply, Matrix.diagonal_apply, h, h']

theorem rowGradeProjection_norm_le_one (mu : ℕ) :
    ‖rowGradeProjection (m := m) (n := n) mu‖ ≤ 1 := by
  rw [rowGradeProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro x
  by_cases h : x.2.grade = mu <;> simp [h]

/-- Insertion of the exact middle grade after the `A_r` block column. -/
theorem rowProjection_AUpStack_gradeProjection (F : Frame n d) (nu : ℕ) :
    rowGradeProjection (m := m) (n := n) (nu + 1) * AUpStack (m := m) F *
        gradeProjection (d := d) nu =
      AUpStack (m := m) F * gradeProjection nu := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : AUpStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := AUpMatrix_grade_relation F out.1 hentry
      have hout : out.2.grade = nu + 1 := by
        rw [hin] at hrel
        exact_mod_cast hrel
      simp [hin, hout]
  · simp [hin]

/-- Selecting demotion output grade `mu` forces input grade `mu+1`. -/
theorem rowProjection_ADownStack_input (F : Frame n d) (mu : ℕ) :
    rowGradeProjection (m := m) (n := n) mu * ADownStack (m := m) F *
        gradeProjection (d := d) (mu + 1) =
      rowGradeProjection mu * ADownStack (m := m) F := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hout : out.2.grade = mu
  · by_cases hentry : ADownStack F out inp = 0
    · simp [hout, hentry]
    · have hrel := ADownMatrix_grade_relation F out.1 hentry
      have hin : inp.2.grade = mu + 1 := by
        rw [hout] at hrel
        exact_mod_cast hrel.symm
      simp [hout, hin]
  · simp [hout]

/-- Conversely, fixing the output of an `A_r` leg at grade `k+1` forces its
input to have grade `k`. -/
theorem rowProjection_AUpStack_input (F : Frame n d) (k : ℕ) :
    rowGradeProjection (m := m) (n := n) (k + 1) * AUpStack (m := m) F *
        gradeProjection (d := d) k =
      rowGradeProjection (k + 1) * AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hout : out.2.grade = k + 1
  · by_cases hentry : AUpStack F out inp = 0
    · simp [hout, hentry]
    · have hrel := AUpMatrix_grade_relation F out.1 hentry
      have hin : inp.2.grade = k := by
        rw [hout] at hrel
        push_cast at hrel
        have hz : (inp.2.grade : ℤ) = (k : ℤ) := by omega
        exact_mod_cast hz
      simp [hout, hin]
  · simp [hout]

/-- An input of grade `mu+1` under the demotion analysis column lands exactly
in middle grade `mu`. -/
theorem rowProjection_ADownStack_output (F : Frame n d) (mu : ℕ) :
    rowGradeProjection (m := m) (n := n) mu * ADownStack (m := m) F *
        gradeProjection (d := d) (mu + 1) =
      ADownStack (m := m) F * gradeProjection (d := d) (mu + 1) := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = mu + 1
  · by_cases hentry : ADownStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := ADownMatrix_grade_relation F out.1 hentry
      have hout : out.2.grade = mu := by
        rw [hin] at hrel
        push_cast at hrel
        have hz : (out.2.grade : ℤ) = (mu : ℤ) := by omega
        exact_mod_cast hz
      simp [hin, hout]
  · simp [hin]

theorem rowProjection_zero_AUpStack (F : Frame n d) :
    rowGradeProjection (m := m) (n := n) 0 * AUpStack (m := m) F = 0 := by
  classical
  ext out inp
  simp only [rowGradeProjection, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hout : out.2.grade = 0
  · by_cases hentry : AUpStack F out inp = 0
    · simp [hout, hentry]
    · have hrel := AUpMatrix_grade_relation F out.1 hentry
      rw [hout] at hrel
      have : (0 : ℤ) < (inp.2.grade : ℤ) + 1 := by omega
      omega
  · simp [hout]

theorem ADownStack_gradeProjection_zero (F : Frame n d) :
    ADownStack (m := m) F * gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hin : inp.2.grade = 0
  · by_cases hentry : ADownStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := ADownMatrix_grade_relation F out.1 hentry
      rw [hin] at hrel
      have : (0 : ℤ) ≤ (out.2.grade : ℤ) := by omega
      omega
  · simp [hin]

def coordNormSq {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, x i ^ 2

theorem coordNormSq_toLp {I : Type*} [Fintype I] (x : I → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = coordNormSq x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [coordNormSq]

/-- Generic finite-dimensional conversion from a coordinate energy estimate
to the rectangular matrix L2 operator norm. -/
theorem matrix_norm_le_of_coord_energy
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {A : Matrix I J ℝ} {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ x : J → ℝ,
      coordNormSq (Matrix.mulVec A x) ≤ C ^ 2 * coordNormSq x) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp x))‖ ≤ C * ‖x‖
  have hsq := henergy (WithLp.ofLp x)
  have hout := coordNormSq_toLp (Matrix.mulVec A (WithLp.ofLp x))
  have hin := coordNormSq_toLp (WithLp.ofLp x)
  have hx : ‖x‖ ^ 2 = coordNormSq (WithLp.ofLp x) := by
    simpa using hin
  rw [← hout, ← hx] at hsq
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (WithLp.toLp 2
    (Matrix.mulVec A (WithLp.ofLp x)))]

theorem coordNormSq_AUpStack (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    coordNormSq (Matrix.mulVec (AUpStack F) x) =
      ∑ r, fockNormSq (Matrix.mulVec (AUpMatrix F r) x) := by
  simp only [coordNormSq, fockNormSq, AUpStack, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]

theorem coordNormSq_ADownStack (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    coordNormSq (Matrix.mulVec (ADownStack F) x) =
      ∑ r, fockNormSq (Matrix.mulVec (ADownMatrix F r) x) := by
  simp only [coordNormSq, fockNormSq, ADownStack, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]

/-- Operator form of the first heavy-leg Loewner/energy estimate. -/
theorem AUpStack_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖AUpStack (m := m) F * gradeProjection (d := d) (m := m) nu‖ ≤
      Real.sqrt nu := by
  apply matrix_norm_le_of_coord_energy (Real.sqrt_nonneg _)
  intro x
  rw [← Matrix.mulVec_mulVec, coordNormSq_AUpStack]
  calc
    _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := AUp_grade_energy F nu x
    _ = (Real.sqrt nu) ^ 2 * coordNormSq x := by
      rw [Real.sq_sqrt (Nat.cast_nonneg nu)]
      rfl

/-- Operator form of the second heavy-leg Loewner/energy estimate. -/
theorem ADownStack_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖ADownStack (m := m) F * gradeProjection (d := d) (m := m) nu‖ ≤
      Real.sqrt nu := by
  apply matrix_norm_le_of_coord_energy (Real.sqrt_nonneg _)
  intro x
  rw [← Matrix.mulVec_mulVec, coordNormSq_ADownStack]
  calc
    _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := ADown_grade_energy F nu x
    _ = (Real.sqrt nu) ^ 2 * coordNormSq x := by
      rw [Real.sq_sqrt (Nat.cast_nonneg nu)]
      rfl

@[simp] theorem BUpMatrix_transpose (F : Frame n d) (r : Fin m) :
    (BUpMatrix F r).transpose = ADownMatrix F r := by
  ext σ inp
  simp only [BUpMatrix, ADownMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have h := congrArg (fun K : FockOp m n ↦ K σ inp.2) (rUpAt_transpose r i)
  simpa [Matrix.transpose_apply] using h

theorem l2_opNorm_transpose_real
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℝ) : ‖A.transpose‖ = ‖A‖ := by
  have hct : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [← hct, Matrix.l2_opNorm_conjTranspose]

/-- The row synthesis factor, restricted to middle grade `mu`, has norm at
most `√(mu+1)`.  This is the concrete `B_r B_r†` estimate. -/
theorem BUpStack_rowGradeProjection_norm (F : Frame n d) (mu : ℕ) :
    ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) mu‖ ≤
      Real.sqrt (mu + 1) := by
  let B := BUpStack (m := m) F
  let R := rowGradeProjection (m := m) (n := n) mu
  let A := ADownStack (m := m) F
  let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
  have ht : (B * R).transpose = R * A := by
    simp [B, R, A, Matrix.transpose_mul]
  calc
    ‖B * R‖ = ‖(B * R).transpose‖ := (l2_opNorm_transpose_real (B * R)).symm
    _ = ‖R * A‖ := by rw [ht]
    _ = ‖R * A * P‖ := by
      rw [rowProjection_ADownStack_input (m := m) F mu]
    _ = ‖R * (A * P)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖R‖ * ‖A * P‖ := Matrix.l2_opNorm_mul R (A * P)
    _ ≤ 1 * ‖A * P‖ := by
      exact mul_le_mul_of_nonneg_right (rowGradeProjection_norm_le_one mu)
        (norm_nonneg _)
    _ ≤ 1 * Real.sqrt (mu + 1) := by
      have ha := ADownStack_gradeProjection_norm (m := m) F (mu + 1)
      have ha' : ‖A * P‖ ≤ Real.sqrt ((mu : ℝ) + 1) := by
        simpa [A, P, Nat.cast_add, Nat.cast_one] using ha
      exact mul_le_mul_of_nonneg_left ha' zero_le_one
    _ = Real.sqrt (mu + 1) := one_mul _

theorem Hplus_grade_factor (F : Frame n d) (nu : ℕ) :
    Hplus m (frameRows F) * gradeProjection (d := d) nu =
      (BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (AUpStack (m := m) F * gradeProjection (d := d) nu) := by
  rw [Hplus_eq_BUpStack_mul_AUpStack]
  have hins := rowProjection_AUpStack_gradeProjection (m := m) F nu
  calc
    (BUpStack (m := m) F * AUpStack (m := m) F) * gradeProjection (d := d) nu =
        BUpStack (m := m) F *
          (AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [Matrix.mul_assoc]
    _ = BUpStack (m := m) F *
        (rowGradeProjection (m := m) (n := n) (nu + 1) *
          AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [hins]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sqrt_mul_sqrt_add_two_le (nu : ℕ) :
    Real.sqrt (nu + 2) * Real.sqrt nu ≤ (nu : ℝ) + 1 := by
  have hnu : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  have hnu2 : 0 ≤ (nu : ℝ) + 2 := by positivity
  have hs0 : 0 ≤ Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare :
      (Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ)) ^ 2 ≤
        ((nu : ℝ) + 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnu2, Real.sq_sqrt hnu]
    nlinarith
  nlinarith [sq_nonneg
    (((nu : ℝ) + 1) + Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ))]

/-- Concrete heavy-heavy `+2` component estimate required by the component
table.  No abstract component-bound premise occurs in the statement. -/
theorem Hplus_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hplus m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) + 1 := by
  rw [Hplus_grade_factor]
  calc
    _ ≤
        ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)‖ *
          ‖AUpStack (m := m) F * gradeProjection (d := d) nu‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((nu : ℝ) + 2) * Real.sqrt nu := by
      have hb := BUpStack_rowGradeProjection_norm (m := m) F (nu + 1)
      have hb' :
          ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)‖ ≤
            Real.sqrt ((nu : ℝ) + 2) := by
        convert hb using 1 <;> norm_num <;> ring
      exact mul_le_mul hb' (AUpStack_gradeProjection_norm (m := m) F nu)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ (nu : ℝ) + 1 := sqrt_mul_sqrt_add_two_le nu

theorem Hplus_transpose_eq_Hminus (F : Frame n d) :
    (Hplus m (frameRows F)).transpose = Hminus m (frameRows F) := by
  rw [Hplus, Hminus, wordSum, wordSum,
    DirectionalConcrete.transpose_physicalWordSum]
  rfl

/-- The lowering band is the literal transpose row-leg product. -/
theorem Hminus_eq_AUpStackTranspose_mul_ADownStack (F : Frame n d) :
    Hminus m (frameRows F) =
      (AUpStack (m := m) F).transpose * ADownStack (m := m) F := by
  rw [← Hplus_transpose_eq_Hminus, Hplus_eq_BUpStack_mul_AUpStack,
    Matrix.transpose_mul, BUpStack_transpose]

theorem AUpStackTranspose_rowGradeProjection_norm
    (F : Frame n d) (k : ℕ) :
    ‖(AUpStack (m := m) F).transpose *
        rowGradeProjection (m := m) (n := n) (k + 1)‖ ≤ Real.sqrt k := by
  let A := AUpStack (m := m) F
  let R := rowGradeProjection (m := m) (n := n) (k + 1)
  let P := gradeProjection (d := d) (m := m) (n := n) k
  have ht : (A.transpose * R).transpose = R * A := by
    simp [A, R, Matrix.transpose_mul]
  calc
    ‖A.transpose * R‖ = ‖(A.transpose * R).transpose‖ :=
      (l2_opNorm_transpose_real (A.transpose * R)).symm
    _ = ‖R * A‖ := by rw [ht]
    _ = ‖R * A * P‖ := by
      rw [rowProjection_AUpStack_input (m := m) F k]
    _ = ‖R * (A * P)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖R‖ * ‖A * P‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖A * P‖ := by
      exact mul_le_mul_of_nonneg_right (rowGradeProjection_norm_le_one (k + 1))
        (norm_nonneg _)
    _ ≤ 1 * Real.sqrt k := by
      exact mul_le_mul_of_nonneg_left
        (AUpStack_gradeProjection_norm (m := m) F k) zero_le_one
    _ = Real.sqrt k := one_mul _

theorem Hminus_grade_factor_add_two (F : Frame n d) (k : ℕ) :
    Hminus m (frameRows F) * gradeProjection (d := d) (k + 2) =
      ((AUpStack (m := m) F).transpose *
        rowGradeProjection (m := m) (n := n) (k + 1)) *
      (ADownStack (m := m) F * gradeProjection (d := d) (k + 2)) := by
  rw [Hminus_eq_AUpStackTranspose_mul_ADownStack]
  have hout := rowProjection_ADownStack_output (m := m) F (k + 1)
  have hout' :
      rowGradeProjection (m := m) (n := n) (k + 1) *
          ADownStack (m := m) F * gradeProjection (d := d) (k + 2) =
        ADownStack (m := m) F * gradeProjection (d := d) (k + 2) := by
    convert hout using 1 <;> omega
  calc
    ((AUpStack (m := m) F).transpose * ADownStack (m := m) F) *
        gradeProjection (d := d) (k + 2) =
      (AUpStack (m := m) F).transpose *
        (ADownStack (m := m) F * gradeProjection (d := d) (k + 2)) := by
      rw [Matrix.mul_assoc]
    _ = (AUpStack (m := m) F).transpose *
        (rowGradeProjection (m := m) (n := n) (k + 1) *
          ADownStack (m := m) F * gradeProjection (d := d) (k + 2)) := by
      rw [hout']
    _ = _ := by simp only [Matrix.mul_assoc]

theorem Hminus_gradeProjection_zero (F : Frame n d) :
    Hminus m (frameRows F) * gradeProjection (d := d) 0 = 0 := by
  rw [Hminus_eq_AUpStackTranspose_mul_ADownStack, Matrix.mul_assoc,
    ADownStack_gradeProjection_zero, Matrix.mul_zero]

theorem Hminus_gradeProjection_one (F : Frame n d) :
    Hminus m (frameRows F) * gradeProjection (d := d) 1 = 0 := by
  rw [Hminus_eq_AUpStackTranspose_mul_ADownStack]
  have hout := rowProjection_ADownStack_output (m := m) F 0
  have hout' :
      rowGradeProjection (m := m) (n := n) 0 * ADownStack (m := m) F *
          gradeProjection (d := d) 1 =
        ADownStack (m := m) F * gradeProjection (d := d) 1 := by
    convert hout using 1 <;> norm_num
  have hz : (AUpStack (m := m) F).transpose *
      rowGradeProjection (m := m) (n := n) 0 = 0 := by
    have h := congrArg Matrix.transpose (rowProjection_zero_AUpStack (m := m) F)
    simpa [Matrix.transpose_mul] using h
  calc
    ((AUpStack (m := m) F).transpose * ADownStack (m := m) F) *
        gradeProjection (d := d) 1 =
      (AUpStack (m := m) F).transpose *
        (ADownStack (m := m) F * gradeProjection (d := d) 1) := by
      rw [Matrix.mul_assoc]
    _ = (AUpStack (m := m) F).transpose *
        (rowGradeProjection (m := m) (n := n) 0 * ADownStack (m := m) F *
          gradeProjection (d := d) 1) := by rw [hout']
    _ = ((AUpStack (m := m) F).transpose *
        rowGradeProjection (m := m) (n := n) 0) *
          (ADownStack (m := m) F * gradeProjection (d := d) 1) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz, Matrix.zero_mul]

/-- Concrete heavy-heavy `-2` estimate in the uniform form used by the
component table. -/
theorem Hminus_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hminus m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) + 1 := by
  rcases nu with (_ | _ | k)
  · rw [Hminus_gradeProjection_zero]
    norm_num
  · rw [Hminus_gradeProjection_one]
    norm_num
  · rw [Hminus_grade_factor_add_two]
    calc
      _ ≤
          ‖(AUpStack (m := m) F).transpose *
            rowGradeProjection (m := m) (n := n) (k + 1)‖ *
          ‖ADownStack (m := m) F * gradeProjection (d := d) (k + 2)‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ Real.sqrt k * Real.sqrt (k + 2) := by
        have hd := ADownStack_gradeProjection_norm (m := m) F (k + 2)
        have hd' :
            ‖ADownStack (m := m) F * gradeProjection (d := d) (k + 2)‖ ≤
              Real.sqrt ((k : ℝ) + 2) := by
          convert hd using 1 <;> norm_num <;> ring
        exact mul_le_mul
          (AUpStackTranspose_rowGradeProjection_norm (m := m) F k)
          hd'
          (norm_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ (k : ℝ) + 1 := by
        simpa [mul_comm] using sqrt_mul_sqrt_add_two_le k
      _ ≤ ((k + 2 : ℕ) : ℝ) + 1 := by norm_num

def ADownOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun p inp ↦ F.u i inp.1 * rDownAt r i p inp.2

theorem ADownMatrix_eq_sum_one (F : Frame n d) (r : Fin m) :
    ADownMatrix F r = ∑ i, ADownOne F r i := by
  ext p inp
  simp [ADownMatrix, ADownOne, Matrix.sum_apply]

theorem rDownAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    rDownAt r i * rUpAt r j = wordKernel (r, i) (r, j) (.rDown, .rUp) := by
  simpa [rDownAt, rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) rDemote rPromote

theorem rUpAt_mul_rDownAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    rUpAt r i * rDownAt r j = wordKernel (r, i) (r, j) (.rUp, .rDown) := by
  simpa [rDownAt, rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) rPromote rDemote

theorem AUpOne_transpose_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    (AUpOne F r i).transpose * AUpOne F r j =
      orderedWordTerm (frameRows F) r i j (.rDown, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, AUpOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * rUpAt r i p out.2) *
        (F.u j inp.1 * rUpAt r j p inp.2)) =
      (F.u i out.1 * F.u j inp.1) *
        ∑ p, rDownAt r i out.2 p * rUpAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have ht := congrArg (fun K : FockOp m n ↦ K out.2 p)
        (rUpAt_transpose r i)
      simp only [Matrix.transpose_apply] at ht
      rw [← ht]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.rDown, .rUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rDownAt_mul_rUpAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

theorem ADownOne_transpose_mul_ADownOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    (ADownOne F r i).transpose * ADownOne F r j =
      orderedWordTerm (frameRows F) r i j (.rUp, .rDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ADownOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * rDownAt r i p out.2) *
        (F.u j inp.1 * rDownAt r j p inp.2)) =
      (F.u i out.1 * F.u j inp.1) *
        ∑ p, rUpAt r i out.2 p * rDownAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have ht := congrArg (fun K : FockOp m n ↦ K out.2 p)
        (rDownAt_transpose r i)
      simp only [Matrix.transpose_apply] at ht
      rw [← ht]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.rUp, .rDown) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rUpAt_mul_rDownAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

def DUp (F : Frame n d) : FullOp d m n :=
  ∑ r, ∑ i, (AUpOne F r i).transpose * AUpOne F r i

def DDown (F : Frame n d) : FullOp d m n :=
  ∑ r, ∑ i, (ADownOne F r i).transpose * ADownOne F r i

theorem AUpMatrix_gram_row (F : Frame n d) (r : Fin m) :
    (AUpMatrix F r).transpose * AUpMatrix F r =
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (frameRows F) r i j (.rDown, .rUp)) +
      ∑ i, (AUpOne F r i).transpose * AUpOne F r i := by
  classical
  rw [AUpMatrix_eq_sum_one, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  calc
    (∑ i, ∑ j, (AUpOne F r i).transpose * AUpOne F r j) =
      ∑ i, ((∑ j ∈ Finset.univ.erase i,
        (AUpOne F r i).transpose * AUpOne F r j) +
          (AUpOne F r i).transpose * AUpOne F r i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i,
        (AUpOne F r i).transpose * AUpOne F r j) +
        ∑ i, (AUpOne F r i).transpose * AUpOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact AUpOne_transpose_mul_AUpOne_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

theorem ADownMatrix_gram_row (F : Frame n d) (r : Fin m) :
    (ADownMatrix F r).transpose * ADownMatrix F r =
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (frameRows F) r i j (.rUp, .rDown)) +
      ∑ i, (ADownOne F r i).transpose * ADownOne F r i := by
  classical
  rw [ADownMatrix_eq_sum_one, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  calc
    (∑ i, ∑ j, (ADownOne F r i).transpose * ADownOne F r j) =
      ∑ i, ((∑ j ∈ Finset.univ.erase i,
        (ADownOne F r i).transpose * ADownOne F r j) +
          (ADownOne F r i).transpose * ADownOne F r i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i,
        (ADownOne F r i).transpose * ADownOne F r j) +
        ∑ i, (ADownOne F r i).transpose * ADownOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact ADownOne_transpose_mul_ADownOne_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

theorem AUpStack_gram (F : Frame n d) :
    (AUpStack (m := m) F).transpose * AUpStack (m := m) F =
      wordSum m (frameRows F) .rDown .rUp + DUp (m := m) F := by
  classical
  calc
    (AUpStack (m := m) F).transpose * AUpStack (m := m) F =
        ∑ r, (AUpMatrix F r).transpose * AUpMatrix F r := by
      ext out inp
      simp only [Matrix.mul_apply, Matrix.transpose_apply, AUpStack,
        Matrix.sum_apply]
      rw [Fintype.sum_prod_type]
    _ = ∑ r, ((∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rDown, .rUp)) +
        ∑ i, (AUpOne F r i).transpose * AUpOne F r i) := by
      apply Finset.sum_congr rfl
      intro r _
      exact AUpMatrix_gram_row F r
    _ = (∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rDown, .rUp)) +
        ∑ r, ∑ i, (AUpOne F r i).transpose * AUpOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = wordSum m (frameRows F) .rDown .rUp + DUp (m := m) F := by
      rfl

theorem ADownStack_gram (F : Frame n d) :
    (ADownStack (m := m) F).transpose * ADownStack (m := m) F =
      wordSum m (frameRows F) .rUp .rDown + DDown (m := m) F := by
  classical
  calc
    (ADownStack (m := m) F).transpose * ADownStack (m := m) F =
        ∑ r, (ADownMatrix F r).transpose * ADownMatrix F r := by
      ext out inp
      simp only [Matrix.mul_apply, Matrix.transpose_apply, ADownStack,
        Matrix.sum_apply]
      rw [Fintype.sum_prod_type]
    _ = ∑ r, ((∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rUp, .rDown)) +
        ∑ i, (ADownOne F r i).transpose * ADownOne F r i) := by
      apply Finset.sum_congr rfl
      intro r _
      exact ADownMatrix_gram_row F r
    _ = (∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rUp, .rDown)) +
        ∑ r, ∑ i, (ADownOne F r i).transpose * ADownOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = wordSum m (frameRows F) .rUp .rDown + DDown (m := m) F := by
      rfl

/-- Exact concrete factorization of the named grade-preserving heavy band,
including the actual same-site correction. -/
theorem Hzero_gram_sub_diagonal (F : Frame n d) :
    Hzero m (frameRows F) =
      (AUpStack (m := m) F).transpose * AUpStack (m := m) F +
      (ADownStack (m := m) F).transpose * ADownStack (m := m) F -
      (DUp (m := m) F + DDown (m := m) F) := by
  rw [AUpStack_gram, ADownStack_gram]
  unfold Hzero
  abel

theorem AUpOne_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    Matrix.mulVec (AUpOne F r i) x σ =
      if σ (r, i) = .two then
        analyze F (fiber x (setSite σ (r, i) .one)) i else 0 := by
  simp only [Matrix.mulVec, dotProduct, AUpOne]
  exact one_rUp_analysis F x r i σ

theorem ADownOne_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    Matrix.mulVec (ADownOne F r i) x σ =
      if σ (r, i) = .one then
        analyze F (fiber x (setSite σ (r, i) .two)) i else 0 := by
  simp only [Matrix.mulVec, dotProduct, ADownOne]
  exact one_rDown_analysis F x r i σ

theorem subset_analysis_le_card_mul (F : Frame n d) (S : Finset (Fin n))
    (v : EVec d) :
    (∑ i ∈ S, (analyze F v i) ^ 2) ≤
      (S.card : ℝ) * ParsevalFrame.normSq v := by
  calc
    (∑ i ∈ S, (analyze F v i) ^ 2) ≤
        ∑ i ∈ S, ParsevalFrame.normSq v := by
      apply Finset.sum_le_sum
      intro i hi
      have h := subset_analysis F {i} v
      simpa using h
    _ = (S.card : ℝ) * ParsevalFrame.normSq v := by simp

/-- Exact same-site creation energy, bounded by the occupation number. -/
theorem DUp_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  classical
  calc
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) =
        ∑ r, ∑ i, ∑ σ,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      simp only [fockNormSq, AUpOne_mulVec]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ (r, i) = .two <;> simp [h]
    _ = ∑ r, ∑ σ, ∑ i,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.heavyInRow r,
          (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Pattern.heavyInRow, Finset.sum_filter]
    _ = ∑ z : MarkedSite m n .two,
          (analyze F (fiber x
            (setSite z.pattern (z.row, z.col) .one)) z.col) ^ 2 := by
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p r i ↦ (analyze F (fiber x (setSite p (r, i) .one)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .one,
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .two .one]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ = ∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
          (analyze F (fiber x p) i) ^ 2 := by
      symm
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)
    _ ≤ ∑ p, ∑ r, ((p.lightInRow r).card : ℝ) *
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      exact subset_analysis_le_card_mul F (p.lightInRow r) (fiber x p)
    _ = ∑ p, (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul, ← Nat.cast_sum,
        ← Pattern.card_light_eq_sum_card_lightInRow]
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast p.card_light_le_grade)
        real_inner_self_nonneg

/-- Exact same-site demotion energy, with the same occupation bound. -/
theorem DDown_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  classical
  calc
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) =
        ∑ r, ∑ i, ∑ σ,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      simp only [fockNormSq, ADownOne_mulVec]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ (r, i) = .one <;> simp [h]
    _ = ∑ r, ∑ σ, ∑ i,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.lightInRow r,
          (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Pattern.lightInRow, Finset.sum_filter]
    _ = ∑ z : MarkedSite m n .one,
          (analyze F (fiber x
            (setSite z.pattern (z.row, z.col) .two)) z.col) ^ 2 := by
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p r i ↦ (analyze F (fiber x (setSite p (r, i) .two)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .two,
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .one .two]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ = ∑ p, ∑ r, ∑ i ∈ p.heavyInRow r,
          (analyze F (fiber x p) i) ^ 2 := by
      symm
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)
    _ ≤ ∑ p, ∑ r, ((p.heavyInRow r).card : ℝ) *
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      exact subset_analysis_le_card_mul F (p.heavyInRow r) (fiber x p)
    _ = ∑ p, (p.heavy.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul, ← Nat.cast_sum,
        ← Pattern.card_heavy_eq_sum_card_heavyInRow]
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      have hcard : p.heavy.card ≤ p.grade := by
        have htwo := p.two_mul_card_heavy_le_grade
        omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        real_inner_self_nonneg

theorem DUp_energy_eq_light (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) =
      ∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
        (analyze F (fiber x p) i) ^ 2 := by
  classical
  calc
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) =
        ∑ r, ∑ i, ∑ σ,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      simp only [fockNormSq, AUpOne_mulVec]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ (r, i) = .two <;> simp [h]
    _ = ∑ r, ∑ σ, ∑ i,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.heavyInRow r,
          (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Pattern.heavyInRow, Finset.sum_filter]
    _ = ∑ z : MarkedSite m n .two,
          (analyze F (fiber x
            (setSite z.pattern (z.row, z.col) .one)) z.col) ^ 2 := by
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p r i ↦ (analyze F (fiber x (setSite p (r, i) .one)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .one,
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .two .one]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ = _ := by
      symm
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)

theorem DDown_energy_eq_heavy (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) =
      ∑ p, ∑ r, ∑ i ∈ p.heavyInRow r,
        (analyze F (fiber x p) i) ^ 2 := by
  classical
  calc
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) =
        ∑ r, ∑ i, ∑ σ,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      simp only [fockNormSq, ADownOne_mulVec]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ (r, i) = .one <;> simp [h]
    _ = ∑ r, ∑ σ, ∑ i,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.lightInRow r,
          (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Pattern.lightInRow, Finset.sum_filter]
    _ = ∑ z : MarkedSite m n .one,
          (analyze F (fiber x
            (setSite z.pattern (z.row, z.col) .two)) z.col) ^ 2 := by
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p r i ↦ (analyze F (fiber x (setSite p (r, i) .two)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .two,
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .one .two]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ = _ := by
      symm
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)

theorem Dcombined_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) +
      (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  rw [DUp_energy_eq_light, DDown_energy_eq_heavy, ← Finset.sum_add_distrib]
  calc
    (∑ p, ((∑ r, ∑ i ∈ p.lightInRow r,
          (analyze F (fiber x p) i) ^ 2) +
        (∑ r, ∑ i ∈ p.heavyInRow r,
          (analyze F (fiber x p) i) ^ 2))) ≤
      ∑ p, (((p.light.card + p.heavy.card : ℕ) : ℝ) *
        ParsevalFrame.normSq (fiber x p)) := by
      apply Finset.sum_le_sum
      intro p _
      calc
        _ ≤ (∑ r, ((p.lightInRow r).card : ℝ) *
              ParsevalFrame.normSq (fiber x p)) +
            ∑ r, ((p.heavyInRow r).card : ℝ) *
              ParsevalFrame.normSq (fiber x p) := by
          exact add_le_add
            (Finset.sum_le_sum fun r _ ↦
              subset_analysis_le_card_mul F (p.lightInRow r) (fiber x p))
            (Finset.sum_le_sum fun r _ ↦
              subset_analysis_le_card_mul F (p.heavyInRow r) (fiber x p))
        _ = ((p.light.card + p.heavy.card : ℕ) : ℝ) *
            ParsevalFrame.normSq (fiber x p) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,
            ← Nat.cast_sum, ← Pattern.card_light_eq_sum_card_lightInRow,
            ← Pattern.card_heavy_eq_sum_card_heavyInRow]
          push_cast
          ring
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      have hc : p.light.card + p.heavy.card ≤ p.grade := by
        rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy]
        omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
        real_inner_self_nonneg

/-- Real quadratic form of a concrete finite matrix. -/
def quadratic {I : Type*} [Fintype I] (M : Matrix I I ℝ) (x : I → ℝ) : ℝ :=
  dotProduct (Matrix.mulVec M x) x

theorem quadratic_gram
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (A : Matrix I J ℝ) (x : J → ℝ) :
    quadratic (A.transpose * A) x =
      coordNormSq (Matrix.mulVec A x) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec]
  calc
    dotProduct (Matrix.mulVec A.transpose (Matrix.mulVec A x)) x =
        dotProduct x (Matrix.mulVec A.transpose (Matrix.mulVec A x)) :=
      dotProduct_comm _ _
    _ = dotProduct (Matrix.mulVec A x) (Matrix.mulVec A x) :=
      Matrix.dotProduct_transpose_mulVec A x (Matrix.mulVec A x)
    _ = coordNormSq (Matrix.mulVec A x) := by
      simp [coordNormSq, dotProduct, pow_two]

theorem quadratic_DUp (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (DUp (m := m) F) x =
      ∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x) := by
  calc
    quadratic (DUp (m := m) F) x =
        ∑ r, ∑ i,
          quadratic ((AUpOne F r i).transpose * AUpOne F r i) x := by
      simp only [quadratic, DUp, Matrix.sum_mulVec, sum_dotProduct]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quadratic_gram]
      rfl

theorem quadratic_DDown (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (DDown (m := m) F) x =
      ∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x) := by
  calc
    quadratic (DDown (m := m) F) x =
        ∑ r, ∑ i,
          quadratic ((ADownOne F r i).transpose * ADownOne F r i) x := by
      simp only [quadratic, DDown, Matrix.sum_mulVec, sum_dotProduct]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quadratic_gram]
      rfl

theorem quadratic_Hzero (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (Hzero m (frameRows F)) x =
      coordNormSq (Matrix.mulVec (AUpStack (m := m) F) x) +
      coordNormSq (Matrix.mulVec (ADownStack (m := m) F) x) -
      (quadratic (DUp (m := m) F) x + quadratic (DDown (m := m) F) x) := by
  rw [Hzero_gram_sub_diagonal]
  calc
    quadratic
          ((AUpStack (m := m) F).transpose * AUpStack F +
            (ADownStack (m := m) F).transpose * ADownStack F -
            (DUp F + DDown F)) x =
        quadratic
            ((AUpStack (m := m) F).transpose * AUpStack F +
              (ADownStack (m := m) F).transpose * ADownStack F) x -
          quadratic (DUp F + DDown F) x := by
      simp [quadratic, Matrix.add_mulVec, Matrix.sub_mulVec,
        add_dotProduct, sub_dotProduct]
    _ =
        (quadratic ((AUpStack (m := m) F).transpose * AUpStack F) x +
          quadratic ((ADownStack (m := m) F).transpose * ADownStack F) x) -
        (quadratic (DUp F) x + quadratic (DDown F) x) := by
      simp [quadratic, Matrix.add_mulVec, add_dotProduct]
    _ = _ := by
      rw [quadratic_gram, quadratic_gram]

theorem quadratic_gradeConj (M : FullOp d m n) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (gradeProjection (d := d) nu * M * gradeProjection nu) x =
      quadratic M (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h := Matrix.dotProduct_transpose_mulVec
    (gradeProjection (d := d) (m := m) (n := n) nu)
    x (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))
  rw [gradeProjection_transpose] at h
  calc
    dotProduct
          (Matrix.mulVec (gradeProjection (d := d) nu)
            (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))) x =
        dotProduct x
          (Matrix.mulVec (gradeProjection (d := d) nu)
            (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))) :=
      dotProduct_comm _ _
    _ = dotProduct
          (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
      simpa only using h

theorem Hzero_transpose (F : Frame n d) :
    (Hzero m (frameRows F)).transpose = Hzero m (frameRows F) := by
  unfold Hzero wordSum
  rw [Matrix.transpose_add,
    DirectionalConcrete.transpose_physicalWordSum,
    DirectionalConcrete.transpose_physicalWordSum]
  rfl

theorem Hzero_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0 (Hzero m (frameRows F)) := by
  apply FiniteHilbert.homogeneous_add
  · simpa [Hzero, wordSum, Word.degree, Leg.degree] using
      DirectionalConcrete.physicalWordSum_homogeneous
        (m := m) (frameRows F) (.rUp, .rDown)
  · simpa [Hzero, wordSum, Word.degree, Leg.degree] using
      DirectionalConcrete.physicalWordSum_homogeneous
        (m := m) (frameRows F) (.rDown, .rUp)

/-- The grade-zero heavy band preserves every exact-grade subspace. -/
theorem Hzero_grade_factor (F : Frame n d) (nu : ℕ) :
    gradeProjection (d := d) nu * Hzero m (frameRows F) * gradeProjection nu =
      Hzero m (frameRows F) * gradeProjection nu := by
  apply FiniteHilbert.output_projection_of_homogeneous
    (Hzero_homogeneous (m := m) F) nu nu
  norm_num

theorem coordNormSq_nonneg {I : Type*} [Fintype I] (x : I → ℝ) :
    0 ≤ coordNormSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem fockNormSq_nonneg (x : Pattern m n → ℝ) :
    0 ≤ fockNormSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Sharp quadratic-form estimate for the concrete grade-zero heavy band,
after restriction to one exact total grade. -/
theorem Hzero_gradeConj_quadratic_abs_le (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    |quadratic
      (gradeProjection (d := d) nu * Hzero m (frameRows F) *
        gradeProjection nu) x| ≤
      2 * (nu : ℝ) * FiniteHilbert.normSq x := by
  let P := gradeProjection (d := d) (m := m) (n := n) nu
  let y := Matrix.mulVec P x
  have hUp :
      coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) ≤
        (nu : ℝ) * FiniteHilbert.normSq x := by
    rw [coordNormSq_AUpStack]
    simpa only [P, y] using
      AUp_grade_energy (m := m) F nu x
  have hDown :
      coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) ≤
        (nu : ℝ) * FiniteHilbert.normSq x := by
    rw [coordNormSq_ADownStack]
    simpa only [P, y] using
      ADown_grade_energy (m := m) F nu x
  have hDiag :
      quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y ≤
        (nu : ℝ) * FiniteHilbert.normSq x := by
    calc
      quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y =
          (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) y)) +
          (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) y)) := by
        rw [quadratic_DUp, quadratic_DDown]
      _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber y p) :=
        Dcombined_energy_le_weighted F y
      _ = (nu : ℝ) * FiniteHilbert.normSq y := by
        simpa [P, y] using weighted_gradeProjection (d := d) (m := m) (n := n) nu x
      _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := by
        exact mul_le_mul_of_nonneg_left
          (gradeProjection_normSq_le nu x) (Nat.cast_nonneg _)
  have hDiag0 :
      0 ≤ quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y := by
    rw [quadratic_DUp, quadratic_DDown]
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ fockNormSq_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ fockNormSq_nonneg _)
  have hUp0 :
      0 ≤ coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) :=
    coordNormSq_nonneg _
  have hDown0 :
      0 ≤ coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) :=
    coordNormSq_nonneg _
  have hNorm0 : 0 ≤ FiniteHilbert.normSq x := FiniteHilbert.normSq_nonneg x
  have hNu0 : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  rw [quadratic_gradeConj, quadratic_Hzero, abs_le]
  change
    -(2 * (nu : ℝ) * FiniteHilbert.normSq x) ≤
          coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) +
            coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) -
            (quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y) ∧
      coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) +
            coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) -
            (quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y) ≤
        2 * (nu : ℝ) * FiniteHilbert.normSq x
  constructor <;> nlinarith

theorem quadraticForm_eq_quadratic (M : FullOp d m n)
    (x : EuclideanSpace ℝ (Fin d × Pattern m n)) :
    MatrixTail.quadraticForm M x = quadratic M (WithLp.ofLp x) := by
  simp [MatrixTail.quadraticForm, quadratic, PiLp.inner_apply,
    Real.inner_apply, dotProduct, mul_comm]

theorem Hzero_gradeConj_isHermitian (F : Frame n d) (nu : ℕ) :
    (gradeProjection (d := d) nu * Hzero m (frameRows F) *
      gradeProjection nu).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, gradeProjection_transpose,
    Hzero_transpose, Matrix.mul_assoc]

/-- Concrete heavy-heavy grade-zero component estimate required by the
component table. -/
theorem Hzero_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hzero m (frameRows F) * gradeProjection (d := d) nu‖ ≤
      2 * (nu : ℝ) := by
  rw [← Hzero_grade_factor]
  apply (MatrixTail.opNorm_le_iff_quadraticForm _
    (Hzero_gradeConj_isHermitian (m := m) F nu) (2 * (nu : ℝ)) (by positivity)).2
  intro x
  rw [quadraticForm_eq_quadratic]
  have h := Hzero_gradeConj_quadratic_abs_le (m := m) F nu (WithLp.ofLp x)
  have hx : FiniteHilbert.normSq (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    symm
    simpa using FiniteHilbert.norm_toLp_sq (d := d) (m := m) (n := n)
      (WithLp.ofLp x)
  rwa [hx] at h

/-- Exact L2-norm scaling for the nested normalized heavy-heavy coefficient
used verbatim in the concrete band assembly. -/
theorem norm_normalized_heavy_term_eq {s b : ℕ}
    (A : FullOp d m n) (P : FullOp d m n) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 • A)) * P‖ =
      (Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ))) * ‖A * P‖ := by
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
      0 ≤ (1 : ℝ) / (((s * b : ℕ) : ℝ))),
    abs_of_nonneg (sq_nonneg _)]
  ring

/-- Normalized concrete heavy-heavy `+2` estimate in exactly the nested
scalar shape consumed by `ConcreteBandAssembly`. -/
theorem norm_normalized_Hplus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hplus (s * b) (frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  rw [norm_normalized_heavy_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ‖Hplus (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left
        (Hplus_gradeProjection_norm (m := s * b) F nu)
        BandCoefficientBounds.rho_sq_div_stack_nonneg
    _ ≤ (1 / (s : ℝ)) * ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right
        (BandCoefficientBounds.rho_sq_div_stack_le_inv_s hs hb) (by positivity)
    _ = BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
      simp [BandEnvelope.cTerm]
      ring

/-- Normalized concrete heavy-heavy grade-zero estimate in exactly the nested
scalar shape consumed by `ConcreteBandAssembly`. -/
theorem norm_normalized_Hzero_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hzero (s * b) (frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      2 * BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  rw [norm_normalized_heavy_term_eq]
  have hraw :
      ‖Hzero (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
        2 * ((nu : ℝ) + 1) := by
    calc
      _ ≤ 2 * (nu : ℝ) := Hzero_gradeProjection_norm (m := s * b) F nu
      _ ≤ 2 * ((nu : ℝ) + 1) := by linarith
  calc
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ‖Hzero (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        (2 * ((nu : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left hraw
        BandCoefficientBounds.rho_sq_div_stack_nonneg
    _ ≤ (1 / (s : ℝ)) * (2 * ((nu : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_right
        (BandCoefficientBounds.rho_sq_div_stack_le_inv_s hs hb) (by positivity)
    _ = 2 * BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
      simp [BandEnvelope.cTerm]
      ring

/-- Normalized concrete heavy-heavy `-2` estimate in exactly the nested
scalar shape consumed by `ConcreteBandAssembly`. -/
theorem norm_normalized_Hminus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hminus (s * b) (frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  rw [norm_normalized_heavy_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ‖Hminus (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left
        (Hminus_gradeProjection_norm (m := s * b) F nu)
        BandCoefficientBounds.rho_sq_div_stack_nonneg
    _ ≤ (1 / (s : ℝ)) * ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right
        (BandCoefficientBounds.rho_sq_div_stack_le_inv_s hs hb) (by positivity)
    _ = BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
      simp [BandEnvelope.cTerm]
      ring

end

end SparseFock.HeavyBandsConcrete
