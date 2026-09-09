import SparseFockFormal.FiniteHilbert
import SparseFockFormal.ParsevalFrame
import SparseFockFormal.LightSectorAbstract
import SparseFockFormal.MatrixTail
import Mathlib.Tactic

/-!
# Concrete shared-leg light operator

This module realizes the operators `C_r` and `G-hat` from the light-sector
argument as literal finite matrices on the external Euclidean leg and the
three-level pattern basis.  It also records the exact fixed-heavy/fixed-light
blocks and develops the column-Gram contraction used by every off-diagonal
particle cross map.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace SparseFock.LightSectorConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert

noncomputable section

variable {d m n : ℕ}

/-- The annihilation operator `P_(r,i)` on the literal pattern basis. -/
def pAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) pDestroy

/-- The creation operator `P†_(r,i)` on the literal pattern basis. -/
def pDagAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) pCreate

/-- The rectangular matrix `C_r = Σ_i u_i ⊗ P†_(r,i)`. -/
def CMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out inp ↦ ∑ i, F.u i out.1 * pDagAt r i out.2 inp

/-- The concrete positive shared-leg operator `G-hat = Σ_r C_r C_rᵀ`. -/
def ghat (F : Frame n d) : FullOp d m n :=
  ∑ r, CMatrix F r * (CMatrix F r).transpose

@[simp] theorem CMatrix_transpose_apply (F : Frame n d) (r : Fin m)
    (p : Pattern m n) (out : Fin d × Pattern m n) :
    (CMatrix F r).transpose p out =
      ∑ i, F.u i out.1 * pAt r i p out.2 := by
  simp only [Matrix.transpose_apply, CMatrix, pAt, pDagAt]
  apply Finset.sum_congr rfl
  intro i _hi
  have h := congrFun (congrFun (transpose_siteKernel (r, i) pCreate) p) out.2
  simp only [Matrix.transpose_apply, transpose_pCreate] at h
  rw [h]

/-- Entrywise expansion of `G-hat` as the displayed `Σ U_ij ⊗ P†_i P_j`.
The same-site terms are retained; no hollow-pair convention is used here. -/
theorem ghat_apply (F : Frame n d)
    (out inp : Fin d × Pattern m n) :
    ghat (m := m) F out inp =
      ∑ r, ∑ i, ∑ j,
        (F.u i out.1 * F.u j inp.1) *
          (pDagAt r i * pAt r j) out.2 inp.2 := by
  classical
  simp only [ghat, Matrix.sum_apply, Matrix.mul_apply, CMatrix,
    CMatrix_transpose_apply]
  apply Finset.sum_congr rfl
  intro r _hr
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [pDagAt, pAt]
  apply Finset.sum_congr rfl
  intro mid _hmid
  ring

@[simp] theorem ghat_transpose (F : Frame n d) :
    (ghat (m := m) F).transpose = ghat F := by
  rw [ghat]
  simp only [Matrix.transpose_sum, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- A pattern lies in the block with fixed heavy set `T` and exactly `ell`
light sites. -/
def InBlock (T : Finset (Site m n)) (ell : ℕ) (p : Pattern m n) : Prop :=
  p.heavy = T ∧ p.light.card = ell

instance instDecidableInBlock (T : Finset (Site m n)) (ell : ℕ)
    (p : Pattern m n) : Decidable (InBlock T ell p) := by
  unfold InBlock
  infer_instance

/-- The literal diagonal projection onto a fixed-heavy/fixed-light block. -/
def blockProjection (T : Finset (Site m n)) (ell : ℕ) : FullOp d m n :=
  by
    classical
    exact Matrix.diagonal fun x ↦ if InBlock T ell x.2 then 1 else 0

@[simp] theorem blockProjection_apply (T : Finset (Site m n)) (ell : ℕ)
    (out inp : Fin d × Pattern m n) :
    blockProjection (d := d) T ell out inp =
      if out = inp ∧ InBlock T ell out.2 then 1 else 0 := by
  classical
  by_cases h : out = inp
  · subst inp
    by_cases hb : InBlock T ell out.2 <;>
      simp [blockProjection, Matrix.diagonal, hb]
  · simp [blockProjection, Matrix.diagonal, h]

@[simp] theorem blockProjection_transpose (T : Finset (Site m n)) (ell : ℕ) :
    (blockProjection (d := d) T ell).transpose = blockProjection T ell := by
  ext out inp
  simp only [Matrix.transpose_apply, blockProjection_apply]
  by_cases h : out = inp
  · subst inp
    simp
  · simp [h, Ne.symm h]

@[simp] theorem blockProjection_mul_self (T : Finset (Site m n)) (ell : ℕ) :
    blockProjection (d := d) T ell * blockProjection T ell =
      blockProjection T ell := by
  classical
  simp [blockProjection, Matrix.diagonal_mul_diagonal]

/-- Coordinate energy on the actual external-pattern Euclidean space. -/
def energy (x : Fin d × Pattern m n → ℝ) : ℝ :=
  ∑ a, x a ^ 2

/-- Quadratic form of a literal full matrix. -/
def quadratic (A : FullOp d m n) (x : Fin d × Pattern m n → ℝ) : ℝ :=
  ∑ a, x a * A.mulVec x a

/-- The column-space Gram matrix `U Uᵀ` on the `n` column coordinates. -/
def columnGram (F : Frame n d) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ inner ℝ (F.u i) (F.u j)

/-- Application of the column Gram matrix, kept as an explicit finite sum. -/
def columnGramApply (F : Frame n d) (x : EVec n) : EVec n :=
  WithLp.toLp 2 fun i ↦ ∑ j, columnGram F i j * x j

@[simp] theorem columnGramApply_apply (F : Frame n d) (x : EVec n) (i : Fin n) :
    columnGramApply F x i = ∑ j, columnGram F i j * x j := rfl

/-- `U Uᵀ` is analysis after synthesis. -/
theorem columnGramApply_eq_analyze_synthesize (F : Frame n d) (x : EVec n)
    (i : Fin n) :
    columnGramApply F x i =
      analyze F (synthesize F Finset.univ (fun j ↦ x j)) i := by
  simp only [columnGramApply_apply, columnGram, analyze, synthesize,
    PiLp.inner_apply, Real.inner_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The cross-map column register `U Uᵀ` is an actual Euclidean contraction.
This proves, rather than assumes, the analytic input `‖P_(l←k)‖ ≤ 1`. -/
theorem columnGram_energy_le (F : Frame n d) (x : EVec n) :
    ParsevalFrame.normSq (columnGramApply F x) ≤
      ParsevalFrame.normSq x := by
  let y : EVec d := synthesize F Finset.univ (fun j ↦ x j)
  have hanalysis : ParsevalFrame.normSq (columnGramApply F x) =
      ∑ i, (analyze F y i) ^ 2 := by
    simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [columnGramApply_eq_analyze_synthesize]
    simp [y, pow_two]
  calc
    ParsevalFrame.normSq (columnGramApply F x) =
        ∑ i, (analyze F y i) ^ 2 := hanalysis
    _ = ParsevalFrame.normSq y := analysis_energy_eq F y
    _ ≤ ∑ j ∈ Finset.univ, |x j| ^ 2 := subset_synthesis F Finset.univ (fun j ↦ x j)
    _ = ParsevalFrame.normSq x := by
      rw [ParsevalFrame.normSq_eq_norm_sq, EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs]

/-- Quadratic two-vector form of the concrete cross-map contraction. -/
theorem two_columnGram_pairing_le (F : Frame n d) (x y : EVec n) :
    2 * inner ℝ (columnGramApply F x) y ≤
      ParsevalFrame.normSq x + ParsevalFrame.normSq y := by
  have hcs : inner ℝ (columnGramApply F x) y ≤
      ‖columnGramApply F x‖ * ‖y‖ := real_inner_le_norm _ _
  have hcontractSq := columnGram_energy_le F x
  rw [ParsevalFrame.normSq_eq_norm_sq,
    ParsevalFrame.normSq_eq_norm_sq] at hcontractSq ⊢
  have hcontract : ‖columnGramApply F x‖ ≤ ‖x‖ := by
    nlinarith [norm_nonneg (columnGramApply F x), norm_nonneg x]
  have hmul : ‖columnGramApply F x‖ * ‖y‖ ≤ ‖x‖ * ‖y‖ :=
    mul_le_mul_of_nonneg_right hcontract (norm_nonneg y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-! ## The labelled one-particle shared leg -/

/-- Coordinate form of trace Parseval. -/
theorem sum_frame_coordinate_sq_eq_dim (F : Frame n d) :
    (∑ a, ∑ i, F.u i a * F.u i a) = (d : ℝ) := by
  have hdiag (a : Fin d) : ∑ i, F.u i a * F.u i a = 1 := by
    have h := congrFun (congrFun F.parseval a) a
    simpa [Matrix.sum_apply, ParsevalFrame.outer] using h
  simp_rw [hdiag]
  simp

/-- Trace Parseval: the total squared length of all frame rows is exactly `d`. -/
theorem sum_frame_normSq_eq_dim (F : Frame n d) :
    (∑ i, ParsevalFrame.normSq (F.u i)) = (d : ℝ) := by
  calc
    (∑ i, ParsevalFrame.normSq (F.u i)) =
        ∑ i, ∑ a, F.u i a * F.u i a := by
      simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply]
    _ = ∑ a, ∑ i, F.u i a * F.u i a := Finset.sum_comm
    _ = (d : ℝ) := sum_frame_coordinate_sq_eq_dim F

/-- One shared vector `w_r = Σ_i u_i ⊗ e_r ⊗ e_i`, in literal
finite Euclidean coordinates. -/
def sharedVector (F : Frame n d) (r : Fin m) :
    EuclideanSpace ℝ (Fin d × Site m n) :=
  WithLp.toLp 2 fun z ↦ if z.2.1 = r then F.u z.2.2 z.1 else 0

@[simp] theorem sharedVector_apply (F : Frame n d) (r : Fin m)
    (a : Fin d) (s : Site m n) :
    sharedVector F r (a, s) = if s.1 = r then F.u s.2 a else 0 := rfl

@[simp] theorem sharedVector_apply_index (F : Frame n d) (r : Fin m)
    (z : Fin d × Site m n) :
    sharedVector F r z =
      if z.2.1 = r then F.u z.2.2 z.1 else 0 := rfl

/-- Different row-shared vectors are orthogonal, while each has squared norm
exactly `d`. -/
theorem sharedVector_inner (F : Frame n d) (r q : Fin m) :
    inner ℝ (sharedVector F r) (sharedVector F q) =
      if r = q then (d : ℝ) else 0 := by
  simp only [PiLp.inner_apply, Real.inner_apply, sharedVector_apply_index]
  change (∑ z : Fin d × Site m n,
    (if z.2.1 = r then F.u z.2.2 z.1 else 0) *
      (if z.2.1 = q then F.u z.2.2 z.1 else 0)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  by_cases hrq : r = q
  · subst q
    simp
    exact sum_frame_coordinate_sq_eq_dim F
  · simp [hrq, Ne.symm hrq]

theorem sharedVector_normSq (F : Frame n d) (r : Fin m) :
    inner ℝ (sharedVector F r) (sharedVector F r) = (d : ℝ) := by
  simpa using sharedVector_inner F r r

/-- One literal rank-one matrix `|w_r><w_r|`. -/
def sharedRankOne (F : Frame n d) (r : Fin m) :
    Matrix (Fin d × Site m n) (Fin d × Site m n) ℝ :=
  fun out inp ↦ sharedVector F r out * sharedVector F r inp

/-- The literal one-particle positive matrix `Q = Σ_r |w_r><w_r|`. -/
def sharedQ (F : Frame n d) :
    Matrix (Fin d × Site m n) (Fin d × Site m n) ℝ :=
  ∑ r, sharedRankOne F r

theorem sharedQ_apply (F : Frame n d)
    (out inp : Fin d × Site m n) :
    sharedQ F out inp =
      if out.2.1 = inp.2.1 then
        F.u out.2.2 out.1 * F.u inp.2.2 inp.1
      else 0 := by
  classical
  simp only [sharedQ, sharedRankOne, Matrix.sum_apply,
    sharedVector_apply_index]
  by_cases hrow : out.2.1 = inp.2.1
  · rw [if_pos hrow]
    simp [hrow]
  · rw [if_neg hrow]
    apply Finset.sum_eq_zero
    intro r _hr
    by_cases hout : out.2.1 = r
    · have hin : inp.2.1 ≠ r := by
        intro heq
        exact hrow (hout.trans heq.symm)
      simp [hout, hin]
    · simp [hout]

/-! ## Labelled-particle realization -/

abbrev LabelledIndex (d m n ell : ℕ) :=
  Fin d × (Fin ell → Site m n)

abbrev OtherParticle (ell : ℕ) (k : Fin ell) :=
  {j : Fin ell // j ≠ k}

abbrev ParticleDomainIndex (m n ell : ℕ) (k : Fin ell) :=
  Fin m × (OtherParticle ell k → Site m n)

/-- Remove particle slot `k`, retaining its row in the extra row register. -/
def domainOfWord {ell : ℕ} (k : Fin ell) (w : Fin ell → Site m n) :
    ParticleDomainIndex m n ell k :=
  ((w k).1, fun j ↦ w j.1)

theorem domainOfWord_eq_iff {ell : ℕ} (k : Fin ell)
    (w v : Fin ell → Site m n) :
    domainOfWord k w = domainOfWord k v ↔
      (w k).1 = (v k).1 ∧ ∀ j, j ≠ k → w j = v j := by
  constructor
  · intro h
    constructor
    · exact congrArg
        (fun z : ParticleDomainIndex m n ell k ↦ z.1) h
    · intro j hj
      have hfun := congrArg
        (fun z : ParticleDomainIndex m n ell k ↦ z.2) h
      exact congrFun hfun ⟨j, hj⟩
  · rintro ⟨hrow, hoff⟩
    apply Prod.ext
    · exact hrow
    · funext j
      exact hoff j.1 j.2

/-- Reinsert a column coordinate into the omitted particle slot. -/
def wordOfDomain {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n) :
    Fin ell → Site m n :=
  fun j ↦ if h : j = k then (z.1, i) else z.2 ⟨j, h⟩

@[simp] theorem wordOfDomain_at {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n) :
    wordOfDomain k z i k = (z.1, i) := by
  simp [wordOfDomain]

theorem wordOfDomain_off {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n)
    (j : Fin ell) (hjk : j ≠ k) :
    wordOfDomain k z i j = z.2 ⟨j, hjk⟩ := by
  simp [wordOfDomain, hjk]

@[simp] theorem domainOfWord_wordOfDomain {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n) :
    domainOfWord k (wordOfDomain k z i) = z := by
  apply Prod.ext
  · simp [domainOfWord]
  · funext j
    simp [domainOfWord, wordOfDomain, j.2]

@[simp] theorem wordOfDomain_domainOfWord {ell : ℕ} (k : Fin ell)
    (w : Fin ell → Site m n) :
    wordOfDomain k (domainOfWord k w) (w k).2 = w := by
  funext j
  by_cases hjk : j = k
  · subst j
    simp [domainOfWord]
  · simp [wordOfDomain, domainOfWord, hjk]

/-- `H_ell` is exactly domain data, the omitted column, and the external
coordinate.  This equivalence is used to evaluate all finite sums without a
dimension-counting assumption. -/
def labelledIndexEquiv (k : Fin ell) :
    LabelledIndex d m n ell ≃
      (ParticleDomainIndex m n ell k × Fin n × Fin d) where
  toFun out := (domainOfWord k out.2, (out.2 k).2, out.1)
  invFun z := (z.2.2, wordOfDomain k z.1 z.2.1)
  left_inv out := by
    apply Prod.ext
    · rfl
    · exact wordOfDomain_domainOfWord k out.2
  right_inv z := by
    rcases z with ⟨domain, i, a⟩
    simp

/-- The insertion matrix `V_k` from the exact typed particle domain into the
labelled shared-leg space. -/
def VMatrix (F : Frame n d) (k : Fin ell) :
    Matrix (LabelledIndex d m n ell) (ParticleDomainIndex m n ell k) ℝ :=
  fun out z ↦
    if z = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0

/-- `Q_k = V_k V_kᵀ`, written as a literal labelled-coordinate matrix. -/
def qSlot (F : Frame n d) (k : Fin ell) :
    Matrix (LabelledIndex d m n ell) (LabelledIndex d m n ell) ℝ :=
  fun out inp ↦
    if domainOfWord k out.2 = domainOfWord k inp.2 then
      F.u (out.2 k).2 out.1 * F.u (inp.2 k).2 inp.1
    else 0

def relabelSlots (pi : Equiv.Perm (Fin ell))
    (out : LabelledIndex d m n ell) : LabelledIndex d m n ell :=
  (out.1, fun k ↦ out.2 (pi k))

theorem qSlot_relabelSlots (F : Frame n d) (k : Fin ell)
    (pi : Equiv.Perm (Fin ell))
    (out inp : LabelledIndex d m n ell) :
    qSlot F k (relabelSlots pi out) (relabelSlots pi inp) =
      qSlot F (pi k) out inp := by
  classical
  have hdomain :
      domainOfWord k (relabelSlots pi out).2 =
          domainOfWord k (relabelSlots pi inp).2 ↔
        domainOfWord (pi k) out.2 = domainOfWord (pi k) inp.2 := by
    rw [domainOfWord_eq_iff, domainOfWord_eq_iff]
    constructor
    · rintro ⟨hrow, hoff⟩
      refine ⟨hrow, ?_⟩
      intro j hj
      have hj' : pi.symm j ≠ k := by
        intro heq
        apply hj
        simpa using congrArg pi heq
      simpa [relabelSlots] using hoff (pi.symm j) hj'
    · rintro ⟨hrow, hoff⟩
      refine ⟨hrow, ?_⟩
      intro j hj
      have hpij : pi j ≠ pi k := fun h ↦ hj (pi.injective h)
      simpa [relabelSlots] using hoff (pi j) hpij
  simp only [qSlot]
  rw [if_congr hdomain rfl rfl]
  rfl

theorem VMatrix_mul_transpose (F : Frame n d) (k : Fin ell) :
    VMatrix (m := m) F k * (VMatrix (m := m) F k).transpose =
      qSlot (m := m) F k := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VMatrix, qSlot]
  by_cases hdom : domainOfWord k out.2 = domainOfWord k inp.2
  · rw [if_pos hdom]
    rw [hdom]
    simp
  · rw [if_neg hdom]
    apply Finset.sum_eq_zero
    intro z _hz
    by_cases hzout : z = domainOfWord k out.2
    · have hzinp : z ≠ domainOfWord k inp.2 := by
        intro heq
        exact hdom (hzout.symm.trans heq)
      rw [if_pos hzout, if_neg hzinp]
      simp
    · rw [if_neg hzout]
      simp

/-- Exact diagonal block `V_kᵀ V_k = d I`, evaluated in coordinates. -/
theorem transpose_VMatrix_mul_apply (F : Frame n d) (k : Fin ell)
    (z z' : ParticleDomainIndex m n ell k) :
    ((VMatrix (m := m) F k).transpose * VMatrix (m := m) F k) z z' =
      if z = z' then (d : ℝ) else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VMatrix]
  by_cases hzz : z = z'
  · subst z'
    rw [if_pos rfl]
    let f : LabelledIndex d m n ell → ℝ := fun out ↦
      (if z = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0) *
        (if z = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0)
    calc
      (∑ out : LabelledIndex d m n ell,
        (if z = domainOfWord k out.2 then
          F.u (out.2 k).2 out.1 else 0) *
        (if z = domainOfWord k out.2 then
          F.u (out.2 k).2 out.1 else 0)) = ∑ out, f out := rfl
      _ = ∑ t : ParticleDomainIndex m n ell k × Fin n × Fin d,
          f ((labelledIndexEquiv (d := d) k).symm t) :=
        ((labelledIndexEquiv (d := d) k).symm.sum_comp f).symm
      _ = ∑ i : Fin n, ∑ a : Fin d, F.u i a * F.u i a := by
        simp only [f, labelledIndexEquiv, Equiv.coe_fn_symm_mk,
          domainOfWord_wordOfDomain, wordOfDomain_at]
        rw [Fintype.sum_prod_type]
        simp
        rw [Fintype.sum_prod_type]
      _ = (d : ℝ) := by
        rw [Finset.sum_comm]
        exact sum_frame_coordinate_sq_eq_dim F
  · rw [if_neg hzz]
    apply Finset.sum_eq_zero
    intro out _hout
    by_cases hz : z = domainOfWord k out.2
    · have hz' : z' ≠ domainOfWord k out.2 := by
        intro heq
        exact hzz (hz.trans heq.symm)
      simp [hz, hz']
    · simp [hz]

theorem transpose_VMatrix_mul (F : Frame n d) (k : Fin ell) :
    (VMatrix (m := m) F k).transpose * VMatrix (m := m) F k =
      (d : ℝ) • (1 : Matrix (ParticleDomainIndex m n ell k)
        (ParticleDomainIndex m n ell k) ℝ) := by
  classical
  ext z z'
  rw [transpose_VMatrix_mul_apply F k z z']
  by_cases hzz : z = z'
  · subst z'
    simp
  · simp [hzz]

/-! ### Explicit typing of the off-diagonal cross maps -/

abbrev RestParticle (ell : ℕ) (k l : Fin ell) :=
  {j : Fin ell // j ≠ k ∧ j ≠ l}

abbrev CrossFiberIndex (m n ell : ℕ) (k l : Fin ell) :=
  (Fin m × Fin m) × (RestParticle ell k l → Site m n)

theorem sum_prod3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A × B × C → ℝ) :
    (∑ t, f t) = ∑ a, ∑ b, ∑ c, f (a, b, c) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Fintype.sum_prod_type]

/-- Coordinates on `D_k`: extra row of `k`, row and column of particle `l`,
and all remaining spectator particles. -/
def domainKToFiber (k l : Fin ell) (hkl : k ≠ l)
    (z : ParticleDomainIndex m n ell k) :
    CrossFiberIndex m n ell k l × Fin n :=
  (((z.1, (z.2 ⟨l, Ne.symm hkl⟩).1),
      fun j ↦ z.2 ⟨j.1, j.2.1⟩),
    (z.2 ⟨l, Ne.symm hkl⟩).2)

def fiberToDomainK (k l : Fin ell) (hkl : k ≠ l)
    (z : CrossFiberIndex m n ell k l × Fin n) :
    ParticleDomainIndex m n ell k :=
  (z.1.1.1, fun j ↦
    if hjl : j.1 = l then (z.1.1.2, z.2)
    else z.1.2 ⟨j.1, j.2, hjl⟩)

def domainKEquiv (k l : Fin ell) (hkl : k ≠ l) :
    ParticleDomainIndex m n ell k ≃
      (CrossFiberIndex m n ell k l × Fin n) where
  toFun := domainKToFiber k l hkl
  invFun := fiberToDomainK k l hkl
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      by_cases hjl : j.1 = l
      · subst l
        simp [fiberToDomainK, domainKToFiber]
      · simp [fiberToDomainK, domainKToFiber, hjl]
  right_inv z := by
    rcases z with ⟨⟨⟨r, s⟩, rest⟩, i⟩
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> simp [domainKToFiber, fiberToDomainK, hkl]
      · funext j
        simp [domainKToFiber, fiberToDomainK, j.2.2]
    · simp [domainKToFiber, fiberToDomainK, hkl]

@[simp] theorem domainKToFiber_fiberToDomainK (k l : Fin ell)
    (hkl : k ≠ l) (z : CrossFiberIndex m n ell k l × Fin n) :
    domainKToFiber k l hkl (fiberToDomainK k l hkl z) = z :=
  (domainKEquiv k l hkl).apply_symm_apply z

/-- Coordinates on `D_l`, ordered in the same cross-fiber convention:
particle-`k` row, extra row of `l`, remaining spectators, particle-`k` column. -/
def domainLToFiber (k l : Fin ell) (hkl : k ≠ l)
    (z : ParticleDomainIndex m n ell l) :
    CrossFiberIndex m n ell k l × Fin n :=
  ((((z.2 ⟨k, hkl⟩).1, z.1),
      fun j ↦ z.2 ⟨j.1, j.2.2⟩),
    (z.2 ⟨k, hkl⟩).2)

def fiberToDomainL (k l : Fin ell) (hkl : k ≠ l)
    (z : CrossFiberIndex m n ell k l × Fin n) :
    ParticleDomainIndex m n ell l :=
  (z.1.1.2, fun j ↦
    if hjk : j.1 = k then (z.1.1.1, z.2)
    else z.1.2 ⟨j.1, hjk, j.2⟩)

def domainLEquiv (k l : Fin ell) (hkl : k ≠ l) :
    ParticleDomainIndex m n ell l ≃
      (CrossFiberIndex m n ell k l × Fin n) where
  toFun := domainLToFiber k l hkl
  invFun := fiberToDomainL k l hkl
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      by_cases hjk : j.1 = k
      · subst k
        simp [fiberToDomainL, domainLToFiber]
      · simp [fiberToDomainL, domainLToFiber, hjk]
  right_inv z := by
    rcases z with ⟨⟨⟨r, s⟩, rest⟩, i⟩
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> simp [domainLToFiber, fiberToDomainL, hkl]
      · funext j
        simp [domainLToFiber, fiberToDomainL, j.2.1]
    · simp [domainLToFiber, fiberToDomainL, hkl]

@[simp] theorem domainLToFiber_fiberToDomainL (k l : Fin ell)
    (hkl : k ≠ l) (z : CrossFiberIndex m n ell k l × Fin n) :
    domainLToFiber k l hkl (fiberToDomainL k l hkl z) = z :=
  (domainLEquiv k l hkl).apply_symm_apply z

/-- The explicitly typed cross-map matrix.  It is a row-register permutation,
a copy of the concrete column Gram matrix, and identity on all spectators. -/
def crossMatrix (F : Frame n d) (k l : Fin ell) (hkl : k ≠ l) :
    Matrix (ParticleDomainIndex m n ell k)
      (ParticleDomainIndex m n ell l) ℝ :=
  fun zk zl ↦
    let xk := domainKToFiber k l hkl zk
    let xl := domainLToFiber k l hkl zl
    if xk.1 = xl.1 then columnGram F xk.2 xl.2 else 0

/-- Squared coordinate energy on any finite real coordinate space. -/
def coordinateEnergy {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, x i ^ 2

theorem normSq_eq_coordinateEnergy (x : EVec n) :
    ParsevalFrame.normSq x = coordinateEnergy (fun i ↦ x i) := by
  rw [ParsevalFrame.normSq_eq_norm_sq, EuclideanSpace.norm_sq_eq]
  simp [coordinateEnergy, Real.norm_eq_abs, pow_two]

/-- One column-register slice of a vector on `D_l`. -/
def domainLSlice (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ)
    (fiber : CrossFiberIndex m n ell k l) : EVec n :=
  WithLp.toLp 2 fun j ↦ y (fiberToDomainL k l hkl (fiber, j))

@[simp] theorem domainLSlice_apply (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ)
    (fiber : CrossFiberIndex m n ell k l) (j : Fin n) :
    domainLSlice k l hkl y fiber j =
      y (fiberToDomainL k l hkl (fiber, j)) := rfl

/-- Pointwise, the typed cross map is exactly `U Uᵀ` on one column slice. -/
theorem crossMatrix_mulVec_fiber (F : Frame n d)
    (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ)
    (fiber : CrossFiberIndex m n ell k l) (i : Fin n) :
    (crossMatrix F k l hkl).mulVec y
        (fiberToDomainK k l hkl (fiber, i)) =
      columnGramApply F (domainLSlice k l hkl y fiber) i := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  let f : ParticleDomainIndex m n ell l → ℝ := fun zl ↦
    crossMatrix F k l hkl (fiberToDomainK k l hkl (fiber, i)) zl * y zl
  calc
    (∑ zl, crossMatrix F k l hkl
        (fiberToDomainK k l hkl (fiber, i)) zl * y zl) = ∑ zl, f zl := rfl
    _ = ∑ t : CrossFiberIndex m n ell k l × Fin n,
        f ((domainLEquiv k l hkl).symm t) :=
      ((domainLEquiv k l hkl).symm.sum_comp f).symm
    _ = ∑ j : Fin n, columnGram F i j *
        y (fiberToDomainL k l hkl (fiber, j)) := by
      simp only [f, crossMatrix, Equiv.coe_fn_symm_mk,
        domainLEquiv, domainKToFiber_fiberToDomainK,
        domainLToFiber_fiberToDomainL]
      rw [Fintype.sum_prod_type]
      simp
    _ = columnGramApply F (domainLSlice k l hkl y fiber) i := by
      rfl

/-- The fully typed off-diagonal matrix is a contraction in literal coordinate
energy.  Row transfer and all spectator coordinates are accounted for by the
two proved equivalences above. -/
theorem crossMatrix_energy_le (F : Frame n d)
    (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ) :
    coordinateEnergy ((crossMatrix F k l hkl).mulVec y) ≤
      coordinateEnergy y := by
  classical
  let outEnergy : ParticleDomainIndex m n ell k → ℝ := fun zk ↦
    ((crossMatrix F k l hkl).mulVec y zk) ^ 2
  let inEnergy : ParticleDomainIndex m n ell l → ℝ := fun zl ↦ y zl ^ 2
  calc
    coordinateEnergy ((crossMatrix F k l hkl).mulVec y) =
        ∑ zk, outEnergy zk := rfl
    _ = ∑ t : CrossFiberIndex m n ell k l × Fin n,
        outEnergy ((domainKEquiv k l hkl).symm t) :=
      ((domainKEquiv k l hkl).symm.sum_comp outEnergy).symm
    _ = ∑ fiber : CrossFiberIndex m n ell k l,
        ∑ i : Fin n,
          (columnGramApply F (domainLSlice k l hkl y fiber) i) ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro fiber _hfiber
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [outEnergy, domainKEquiv, Equiv.coe_fn_symm_mk]
      rw [crossMatrix_mulVec_fiber]
    _ ≤ ∑ fiber : CrossFiberIndex m n ell k l,
        ∑ j : Fin n, (domainLSlice k l hkl y fiber j) ^ 2 := by
      apply Finset.sum_le_sum
      intro fiber _hfiber
      have h := columnGram_energy_le F (domainLSlice k l hkl y fiber)
      rw [normSq_eq_coordinateEnergy, normSq_eq_coordinateEnergy] at h
      exact h
    _ = ∑ fiber : CrossFiberIndex m n ell k l, ∑ j : Fin n,
        inEnergy (fiberToDomainL k l hkl (fiber, j)) := by rfl
    _ = ∑ t : CrossFiberIndex m n ell k l × Fin n,
        inEnergy ((domainLEquiv k l hkl).symm t) := by
      exact (Fintype.sum_prod_type (fun t :
        CrossFiberIndex m n ell k l × Fin n ↦
          inEnergy ((domainLEquiv k l hkl).symm t))).symm
    _ = ∑ zl, inEnergy zl :=
      (domainLEquiv k l hkl).symm.sum_comp inEnergy
    _ = coordinateEnergy y := rfl

/-- Reconstruct a labelled word from a cross fiber and the two distinguished
column coordinates: `j` at particle `k` and `i` at particle `l`. -/
def wordOfCross (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    Fin ell → Site m n :=
  fun t ↦ if htk : t = k then (fiber.1.1, j)
    else if htl : t = l then (fiber.1.2, i)
    else fiber.2 ⟨t, htk, htl⟩

@[simp] theorem wordOfCross_at_k (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    wordOfCross k l hkl fiber i j k = (fiber.1.1, j) := by
  simp [wordOfCross]

@[simp] theorem wordOfCross_at_l (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    wordOfCross k l hkl fiber i j l = (fiber.1.2, i) := by
  simp [wordOfCross, hkl, Ne.symm hkl]

theorem wordOfCross_off (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n)
    (t : Fin ell) (htk : t ≠ k) (htl : t ≠ l) :
    wordOfCross k l hkl fiber i j t = fiber.2 ⟨t, htk, htl⟩ := by
  simp [wordOfCross, htk, htl]

/-- Canonical decomposition of the labelled shared-leg space for a pair of
distinct particle labels. -/
def labelledCrossEquiv (k l : Fin ell) (hkl : k ≠ l) :
    LabelledIndex d m n ell ≃
      (CrossFiberIndex m n ell k l × Fin n × Fin n × Fin d) where
  toFun out :=
    ((((out.2 k).1, (out.2 l).1),
        fun t ↦ out.2 t.1),
      (out.2 l).2, (out.2 k).2, out.1)
  invFun z :=
    (z.2.2.2, wordOfCross k l hkl z.1 z.2.1 z.2.2.1)
  left_inv out := by
    apply Prod.ext
    · rfl
    · funext t
      by_cases htk : t = k
      · subst t
        simp
      · by_cases htl : t = l
        · subst t
          simp [hkl, Ne.symm hkl]
        · simp [wordOfCross, htk, htl]
  right_inv z := by
    rcases z with ⟨⟨⟨r, s⟩, rest⟩, i, j, a⟩
    simp only
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> simp [wordOfCross, hkl, Ne.symm hkl]
      · funext t
        simp [wordOfCross, t.2.1, t.2.2]
    · apply Prod.ext
      · simp [wordOfCross, hkl, Ne.symm hkl]
      · apply Prod.ext <;> simp [wordOfCross, hkl, Ne.symm hkl]

@[simp] theorem domainKToFiber_domainOf_crossWord
    (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    domainKToFiber k l hkl (domainOfWord k (wordOfCross k l hkl fiber i j)) =
      (fiber, i) := by
  rw [← domainKToFiber_fiberToDomainK k l hkl (fiber, i)]
  congr 1
  apply Prod.ext
  · simp [domainOfWord, fiberToDomainK, wordOfCross, hkl, Ne.symm hkl]
  · funext t
    by_cases htl : t.1 = l
    · subst l
      simp [domainOfWord, fiberToDomainK, wordOfCross, hkl, Ne.symm hkl]
    · simp [domainOfWord, fiberToDomainK, wordOfCross, t.2, htl,
        hkl, Ne.symm hkl]

@[simp] theorem domainLToFiber_domainOf_crossWord
    (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    domainLToFiber k l hkl (domainOfWord l (wordOfCross k l hkl fiber i j)) =
      (fiber, j) := by
  rw [← domainLToFiber_fiberToDomainL k l hkl (fiber, j)]
  congr 1
  apply Prod.ext
  · simp [domainOfWord, fiberToDomainL, wordOfCross, hkl, Ne.symm hkl]
  · funext t
    by_cases htk : t.1 = k
    · subst k
      simp [domainOfWord, fiberToDomainL, wordOfCross, hkl, Ne.symm hkl]
    · simp [domainOfWord, fiberToDomainL, wordOfCross, t.2, htk,
        hkl, Ne.symm hkl]

theorem eq_domainOf_crossWord_k_iff
    (k l : Fin ell) (hkl : k ≠ l)
    (zk : ParticleDomainIndex m n ell k)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    zk = domainOfWord k (wordOfCross k l hkl fiber i j) ↔
      domainKToFiber k l hkl zk = (fiber, i) := by
  constructor
  · intro h
    rw [h]
    exact domainKToFiber_domainOf_crossWord k l hkl fiber i j
  · intro h
    apply (domainKEquiv k l hkl).injective
    change domainKToFiber k l hkl zk =
      domainKToFiber k l hkl
        (domainOfWord k (wordOfCross k l hkl fiber i j))
    simpa using h

theorem eq_domainOf_crossWord_l_iff
    (k l : Fin ell) (hkl : k ≠ l)
    (zl : ParticleDomainIndex m n ell l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    zl = domainOfWord l (wordOfCross k l hkl fiber i j) ↔
      domainLToFiber k l hkl zl = (fiber, j) := by
  constructor
  · intro h
    rw [h]
    exact domainLToFiber_domainOf_crossWord k l hkl fiber i j
  · intro h
    apply (domainLEquiv k l hkl).injective
    change domainLToFiber k l hkl zl =
      domainLToFiber k l hkl
        (domainOfWord l (wordOfCross k l hkl fiber i j))
    simpa using h

set_option maxHeartbeats 1000000 in
/-- Direct substitution into the literal insertion matrices gives exactly the
typed row-transfer/column-projection cross map. -/
theorem transpose_VMatrix_mul_cross (F : Frame n d)
    (k l : Fin ell) (hkl : k ≠ l) :
    (VMatrix (m := m) F k).transpose * VMatrix (m := m) F l =
      crossMatrix F k l hkl := by
  classical
  ext zk zl
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VMatrix]
  let f : LabelledIndex d m n ell → ℝ := fun out ↦
    (if zk = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0) *
      (if zl = domainOfWord l out.2 then F.u (out.2 l).2 out.1 else 0)
  let xk := domainKToFiber k l hkl zk
  let xl := domainLToFiber k l hkl zl
  change (∑ out, f out) = if xk.1 = xl.1 then columnGram F xk.2 xl.2 else 0
  calc
    (∑ out, f out) =
        ∑ t : CrossFiberIndex m n ell k l × Fin n × Fin n × Fin d,
          f ((labelledCrossEquiv k l hkl).symm t) :=
      ((labelledCrossEquiv k l hkl).symm.sum_comp f).symm
    _ = if xk.1 = xl.1 then columnGram F xk.2 xl.2 else 0 := by
      simp only [f, xk, xl, labelledCrossEquiv, Equiv.coe_fn_symm_mk,
        wordOfCross_at_k, wordOfCross_at_l,
        eq_domainOf_crossWord_k_iff, eq_domainOf_crossWord_l_iff]
      rw [Fintype.sum_prod_type]
      simp_rw [sum_prod3]
      rcases hxk : domainKToFiber k l hkl zk with ⟨fk, ik⟩
      rcases hxl : domainLToFiber k l hkl zl with ⟨fl, jl⟩
      by_cases hf : fk = fl
      · subst fl
        simp [hxk, hxl, columnGram, PiLp.inner_apply, ite_and, eq_comm]
      · simp [hxk, hxl, hf, ite_and, eq_comm]

/-! ### The concrete `d + ell - 1` block-Gram estimate -/

/-- A genuinely dependent direct-sum vector: its `k`th component lives in
the exact domain `D_k`. -/
abbrev DomainFamily (m n ell : ℕ) :=
  (k : Fin ell) → ParticleDomainIndex m n ell k → ℝ

def componentEnergy (z : DomainFamily m n ell) (k : Fin ell) : ℝ :=
  coordinateEnergy (z k)

def crossPairing (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) : ℝ :=
  ∑ a, z k a * (crossMatrix F k l hkl).mulVec (z l) a

/-- `2ab ≤ a²+b²`, summed over the exact typed cross map, followed by
the already-proved `U Uᵀ` contraction. -/
theorem two_crossPairing_le (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) :
    2 * crossPairing F z k l hkl ≤
      componentEnergy z k + componentEnergy z l := by
  let w : ParticleDomainIndex m n ell k → ℝ :=
    (crossMatrix F k l hkl).mulVec (z l)
  have hpoint (a : ParticleDomainIndex m n ell k) :
      2 * z k a * w a ≤ (z k a) ^ 2 + (w a) ^ 2 := by
    nlinarith [sq_nonneg (z k a - w a)]
  have hsum :
      2 * crossPairing F z k l hkl ≤
        componentEnergy z k + coordinateEnergy w := by
    calc
      2 * crossPairing F z k l hkl = ∑ a, 2 * z k a * w a := by
        simp only [crossPairing, w, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ ≤ ∑ a, ((z k a) ^ 2 + (w a) ^ 2) :=
        Finset.sum_le_sum fun a _ha ↦ hpoint a
      _ = componentEnergy z k + coordinateEnergy w := by
        simp [componentEnergy, coordinateEnergy, Finset.sum_add_distrib]
  have hcontract : coordinateEnergy w ≤ componentEnergy z l := by
    exact crossMatrix_energy_le F k l hkl (z l)
  linarith

theorem crossPairing_le_half (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) :
    crossPairing F z k l hkl ≤
      (componentEnergy z k + componentEnergy z l) / 2 := by
  linarith [two_crossPairing_le F z k l hkl]

def crossPairingTotal (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) : ℝ :=
  if hkl : k ≠ l then crossPairing F z k l hkl else 0

theorem crossPairingTotal_le_half (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) :
    crossPairingTotal F z k l ≤
      (componentEnergy z k + componentEnergy z l) / 2 := by
  simp only [crossPairingTotal, dif_pos hkl]
  exact crossPairing_le_half F z k l hkl

/-- The literal quadratic form of the dependent block matrix whose diagonal
blocks are `V_kᵀV_k=dI` and whose off-diagonal blocks are the proved concrete
cross matrices. -/
def sharedLegGramQuadratic (F : Frame n d) (z : DomainFamily m n ell) : ℝ :=
  (d : ℝ) * ∑ k, componentEnergy z k +
    ∑ k, ∑ l ∈ Finset.univ.erase k,
      crossPairingTotal F z k l

/-- Concrete finite-coordinate block-Gram bound.  There is no assumed
cross-map estimate: every cross term invokes `crossMatrix_energy_le`, already
proved from Parseval above. -/
theorem sharedLegGramQuadratic_le (F : Frame n d) (z : DomainFamily m n ell)
    (hell : 1 ≤ ell) :
    sharedLegGramQuadratic F z ≤
      ((d : ℝ) + (ell : ℝ) - 1) * ∑ k, componentEnergy z k := by
  have hcross :
      (∑ k, ∑ l ∈ Finset.univ.erase k,
        crossPairingTotal F z k l) ≤
        ((ell : ℝ) - 1) * ∑ k, componentEnergy z k := by
    apply LightSectorAbstract.offDiagonal_sum_le hell
    intro k l hkl
    exact crossPairingTotal_le_half F z k l hkl
  unfold sharedLegGramQuadratic
  calc
    (d : ℝ) * ∑ k, componentEnergy z k +
        ∑ k, ∑ l ∈ Finset.univ.erase k,
          crossPairingTotal F z k l ≤
      (d : ℝ) * ∑ k, componentEnergy z k +
        ((ell : ℝ) - 1) * ∑ k, componentEnergy z k :=
      add_le_add_right hcross _
    _ = ((d : ℝ) + (ell : ℝ) - 1) *
        ∑ k, componentEnergy z k := by ring

/-! ### Actual rectangular synthesis matrix and its two Gram matrices -/

/-- Quadratic form for an arbitrary literal finite square matrix. -/
def coordinateQuadratic {I : Type*} [Fintype I]
    (A : Matrix I I ℝ) (x : I → ℝ) : ℝ :=
  ∑ i, x i * A.mulVec x i

/-- Elementary rectangular Gram identity in exact finite coordinates. -/
theorem coordinateEnergy_mulVec_eq_gram
    {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) (x : J → ℝ) :
    coordinateEnergy (A.mulVec x) =
      coordinateQuadratic (A.transpose * A) x := by
  simp only [coordinateEnergy, coordinateQuadratic, pow_two]
  change (A.mulVec x) ⬝ᵥ (A.mulVec x) =
    x ⬝ᵥ (A.transpose * A).mulVec x
  rw [← Matrix.mulVec_mulVec]
  calc
    A.mulVec x ⬝ᵥ A.mulVec x = Matrix.vecMul (A.mulVec x) A ⬝ᵥ x :=
      Matrix.dotProduct_mulVec (A.mulVec x) A x
    _ = A.transpose.mulVec (A.mulVec x) ⬝ᵥ x := by
      have h := Matrix.vecMul_transpose A.transpose (A.mulVec x)
      simpa using congrArg (fun y ↦ y ⬝ᵥ x) h
    _ = x ⬝ᵥ A.transpose.mulVec (A.mulVec x) := dotProduct_comm _ _

abbrev AllDomainIndex (m n ell : ℕ) :=
  Sigma (ParticleDomainIndex m n ell)

/-- The row operator `V(z_1,…,z_ell)=Σ_k V_k z_k` as one literal
rectangular matrix. -/
def VAllMatrix (F : Frame n d) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (AllDomainIndex m n ell) ℝ :=
  fun out z ↦ VMatrix F z.1 out z.2

def sigmaToFamily (z : AllDomainIndex m n ell → ℝ) :
    DomainFamily m n ell :=
  fun k a ↦ z ⟨k, a⟩

/-- Total energy of a sigma-indexed direct-sum vector is the sum of its exact
dependent component energies. -/
theorem coordinateEnergy_sigma (z : AllDomainIndex m n ell → ℝ) :
    coordinateEnergy z = ∑ k, componentEnergy (sigmaToFamily z) k := by
  simp only [coordinateEnergy, componentEnergy, sigmaToFamily]
  rw [Fintype.sum_sigma]

/-- The `(k,l)` block pairing in the literal Gram matrix `VᵀV`. -/
def blockGramPairing (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (k l : Fin ell) : ℝ :=
  ∑ a, z ⟨k, a⟩ *
    (((VMatrix F k).transpose * VMatrix F l).mulVec
      (fun b ↦ z ⟨l, b⟩) a)

/-- Expanding the sigma indices in the combined synthesis Gram matrix gives
the sum of its literal typed blocks. -/
theorem coordinateQuadratic_VAll_gram_eq_sum_blocks
    (F : Frame n d) (ell : ℕ) (z : AllDomainIndex m n ell → ℝ) :
    coordinateQuadratic
        ((VAllMatrix (m := m) F ell).transpose * VAllMatrix F ell) z =
      ∑ k, ∑ l, blockGramPairing F ell z k l := by
  classical
  simp only [coordinateQuadratic, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.transpose_apply, VAllMatrix,
    blockGramPairing]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _hk
  simp_rw [Fintype.sum_sigma]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A diagonal block contributes exactly `d` times its component energy. -/
theorem blockGramPairing_self (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (k : Fin ell) :
    blockGramPairing F ell z k k =
      (d : ℝ) * componentEnergy (sigmaToFamily z) k := by
  classical
  rw [blockGramPairing, transpose_VMatrix_mul]
  simp [componentEnergy, sigmaToFamily, coordinateEnergy,
    Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- An off-diagonal literal Gram block is exactly the concrete cross pairing. -/
theorem blockGramPairing_cross (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (k l : Fin ell) (hkl : k ≠ l) :
    blockGramPairing F ell z k l =
      crossPairing F (sigmaToFamily z) k l hkl := by
  rw [blockGramPairing, transpose_VMatrix_mul_cross F k l hkl]
  rfl

/-- The full literal Gram quadratic is exactly the previously estimated
shared-leg block form. -/
theorem sum_blockGramPairing_eq_sharedLeg (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) :
    (∑ k, ∑ l, blockGramPairing F ell z k l) =
      sharedLegGramQuadratic F (sigmaToFamily z) := by
  classical
  have hrow (k : Fin ell) :
      (∑ l, blockGramPairing F ell z k l) =
        (d : ℝ) * componentEnergy (sigmaToFamily z) k +
          ∑ l ∈ Finset.univ.erase k,
            crossPairingTotal F (sigmaToFamily z) k l := by
    calc
      (∑ l, blockGramPairing F ell z k l) =
          (∑ l ∈ Finset.univ.erase k, blockGramPairing F ell z k l) +
            blockGramPairing F ell z k k :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ k)).symm
      _ = blockGramPairing F ell z k k +
          ∑ l ∈ Finset.univ.erase k, blockGramPairing F ell z k l :=
        add_comm _ _
      _ = (d : ℝ) * componentEnergy (sigmaToFamily z) k +
          ∑ l ∈ Finset.univ.erase k,
            crossPairingTotal F (sigmaToFamily z) k l := by
        rw [blockGramPairing_self]
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
        have hkl : k ≠ l := Ne.symm hlk
        rw [blockGramPairing_cross F ell z k l hkl]
        simp [crossPairingTotal, hkl]
  simp_rw [hrow]
  unfold sharedLegGramQuadratic
  rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem coordinateQuadratic_VAll_gram_eq_sharedLeg
    (F : Frame n d) (ell : ℕ) (z : AllDomainIndex m n ell → ℝ) :
    coordinateQuadratic
        ((VAllMatrix (m := m) F ell).transpose * VAllMatrix F ell) z =
      sharedLegGramQuadratic F (sigmaToFamily z) := by
  rw [coordinateQuadratic_VAll_gram_eq_sum_blocks,
    sum_blockGramPairing_eq_sharedLeg]

/-- The combined concrete synthesis map obeys the exact `d + ell - 1`
Euclidean energy bound. -/
theorem VAllMatrix_energy_le (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (hell : 1 ≤ ell) :
    coordinateEnergy ((VAllMatrix (m := m) F ell).mulVec z) ≤
      ((d : ℝ) + (ell : ℝ) - 1) * coordinateEnergy z := by
  rw [coordinateEnergy_mulVec_eq_gram,
    coordinateQuadratic_VAll_gram_eq_sharedLeg,
    coordinateEnergy_sigma]
  exact sharedLegGramQuadratic_le F (sigmaToFamily z) hell

theorem coordinateEnergy_nonneg {I : Type*} [Fintype I] (x : I → ℝ) :
    0 ≤ coordinateEnergy x := by
  exact Finset.sum_nonneg fun i _hi ↦ sq_nonneg (x i)

/-- Finite-coordinate Cauchy--Schwarz in the exact normalization used here. -/
theorem coordinate_dot_sq_le {I : Type*} [Fintype I]
    (x y : I → ℝ) :
    (∑ i, x i * y i) ^ 2 ≤ coordinateEnergy x * coordinateEnergy y := by
  simpa [coordinateEnergy] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) x y)

/-- A synthesis energy bound implies the same one-sided quadratic bound for
its positive row Gram matrix.  The cancellation is proved directly from
finite-coordinate Cauchy--Schwarz. -/
theorem gramQuadratic_le_of_energy_le
    {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ z : J → ℝ,
      coordinateEnergy (A.mulVec z) ≤ c * coordinateEnergy z)
    (x : I → ℝ) :
    coordinateQuadratic (A * A.transpose) x ≤
      c * coordinateEnergy x := by
  let z : J → ℝ := A.transpose.mulVec x
  have hgram : coordinateEnergy z = coordinateQuadratic (A * A.transpose) x := by
    simpa [z] using coordinateEnergy_mulVec_eq_gram A.transpose x
  have hinner : coordinateEnergy z = ∑ i, x i * A.mulVec z i := by
    calc
      coordinateEnergy z = coordinateQuadratic (A * A.transpose) x := hgram
      _ = ∑ i, x i * A.mulVec z i := by
        simp only [coordinateQuadratic]
        rw [Matrix.mulVec_mulVec]
  have hcs : coordinateEnergy z ^ 2 ≤
      coordinateEnergy x * coordinateEnergy (A.mulVec z) := by
    rw [hinner]
    exact coordinate_dot_sq_le x (A.mulVec z)
  have hmul : coordinateEnergy x * coordinateEnergy (A.mulVec z) ≤
      coordinateEnergy x * (c * coordinateEnergy z) :=
    mul_le_mul_of_nonneg_left (hA z) (coordinateEnergy_nonneg x)
  have hchain : coordinateEnergy z ^ 2 ≤
      coordinateEnergy x * (c * coordinateEnergy z) := hcs.trans hmul
  have hznonneg := coordinateEnergy_nonneg z
  have hbound : coordinateEnergy z ≤ c * coordinateEnergy x := by
    by_cases hz : coordinateEnergy z = 0
    · rw [hz]
      exact mul_nonneg hc (coordinateEnergy_nonneg x)
    · have hzpos : 0 < coordinateEnergy z := lt_of_le_of_ne hznonneg (Ne.symm hz)
      nlinarith
  rw [← hgram]
  exact hbound

/-- Coordinate and Euclidean-space presentations of a real matrix quadratic
form agree exactly. -/
theorem quadraticForm_toLp_eq_coordinateQuadratic
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (x : I → ℝ) :
    MatrixTail.quadraticForm A (WithLp.toLp 2 x) =
      coordinateQuadratic A x := by
  rw [MatrixTail.quadraticForm, real_inner_comm,
    Matrix.inner_toEuclideanCLM]
  rfl

/-- The labelled-particle operator `Σ_k Q_k`. -/
def labelledG (F : Frame n d) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (LabelledIndex d m n ell) ℝ :=
  ∑ k, qSlot F k

theorem labelledG_relabelSlots (F : Frame n d) (ell : ℕ)
    (pi : Equiv.Perm (Fin ell))
    (out inp : LabelledIndex d m n ell) :
    labelledG F ell (relabelSlots pi out) (relabelSlots pi inp) =
      labelledG F ell out inp := by
  classical
  simp only [labelledG, Matrix.sum_apply, qSlot_relabelSlots]
  exact Equiv.sum_comp pi (fun k ↦ qSlot F k out inp)

@[simp] theorem qSlot_transpose (F : Frame n d) (k : Fin ell) :
    (qSlot (m := m) F k).transpose = qSlot F k := by
  ext out inp
  simp only [Matrix.transpose_apply, qSlot]
  by_cases hdom : domainOfWord k out.2 = domainOfWord k inp.2
  · rw [if_pos hdom.symm, if_pos hdom]
    ring
  · have hrev : domainOfWord k inp.2 ≠ domainOfWord k out.2 :=
      fun h ↦ hdom h.symm
    rw [if_neg hrev, if_neg hdom]

@[simp] theorem labelledG_transpose (F : Frame n d) (ell : ℕ) :
    (labelledG (m := m) F ell).transpose = labelledG F ell := by
  rw [labelledG, Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  exact qSlot_transpose (m := m) F k

/-- The labelled operator is literally `V Vᵀ`, not just spectrally
equivalent to it. -/
theorem VAllMatrix_mul_transpose (F : Frame n d) (ell : ℕ) :
    VAllMatrix (m := m) F ell * (VAllMatrix F ell).transpose =
      labelledG F ell := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VAllMatrix,
    labelledG, Matrix.sum_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _hk
  have h := congrFun (congrFun (VMatrix_mul_transpose (m := m) F k) out) inp
  simpa [Matrix.mul_apply] using h

theorem labelledG_isHermitian (F : Frame n d) (ell : ℕ) :
    (labelledG (m := m) F ell).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (labelledG (m := m) F ell).transpose = labelledG F ell
  exact labelledG_transpose F ell

/-- Positivity of the labelled shared-leg matrix, in literal coordinates. -/
theorem labelledG_coordinateQuadratic_nonneg (F : Frame n d) (ell : ℕ)
    (x : LabelledIndex d m n ell → ℝ) :
    0 ≤ coordinateQuadratic (labelledG F ell) x := by
  rw [← VAllMatrix_mul_transpose]
  have hgram :
      coordinateEnergy
          ((VAllMatrix (m := m) F ell).transpose.mulVec x) =
        coordinateQuadratic
          (VAllMatrix (m := m) F ell *
            (VAllMatrix (m := m) F ell).transpose) x := by
    simpa using coordinateEnergy_mulVec_eq_gram
      (VAllMatrix (m := m) F ell).transpose x
  rw [← hgram]
  exact coordinateEnergy_nonneg _

/-- The concrete labelled-particle Gram operator obeys the sharp light-sector
constant `d + ell - 1` as an actual coordinate quadratic-form estimate. -/
theorem labelledG_coordinateQuadratic_le (F : Frame n d) (ell : ℕ)
    (x : LabelledIndex d m n ell → ℝ) (hell : 1 ≤ ell) :
    coordinateQuadratic (labelledG F ell) x ≤
      ((d : ℝ) + (ell : ℝ) - 1) * coordinateEnergy x := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : 0 ≤ (d : ℝ) + (ell : ℝ) - 1 := by
    linarith
  rw [← VAllMatrix_mul_transpose]
  exact gramQuadratic_le_of_energy_le
    (VAllMatrix (m := m) F ell)
    ((d : ℝ) + (ell : ℝ) - 1) hc
    (fun z ↦ VAllMatrix_energy_le F ell z hell) x

/-- The same estimate stated on the genuine Euclidean space. -/
theorem labelledG_quadraticForm_le (F : Frame n d) (ell : ℕ)
    (x : EuclideanSpace ℝ (LabelledIndex d m n ell)) (hell : 1 ≤ ell) :
    MatrixTail.quadraticForm (labelledG F ell) x ≤
      ((d : ℝ) + (ell : ℝ) - 1) * ‖x‖ ^ 2 := by
  have h := labelledG_coordinateQuadratic_le F ell (WithLp.ofLp x) hell
  rw [← quadraticForm_toLp_eq_coordinateQuadratic] at h
  have hxnorm : coordinateEnergy (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [coordinateEnergy, Real.norm_eq_abs, pow_two]
  rw [hxnorm] at h
  simpa using h

theorem labelledG_quadraticForm_nonneg (F : Frame n d) (ell : ℕ)
    (x : EuclideanSpace ℝ (LabelledIndex d m n ell)) :
    0 ≤ MatrixTail.quadraticForm (labelledG F ell) x := by
  have h := labelledG_coordinateQuadratic_nonneg F ell (WithLp.ofLp x)
  rw [← quadraticForm_toLp_eq_coordinateQuadratic] at h
  simpa using h

/-- Final L2 operator-norm form of the concrete labelled shared-leg bound. -/
theorem labelledG_norm_le (F : Frame n d) (ell : ℕ) (hell : 1 ≤ ell) :
    ‖labelledG (m := m) F ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : 0 ≤ (d : ℝ) + (ell : ℝ) - 1 := by
    linarith
  apply (MatrixTail.opNorm_le_iff_quadraticForm
    (labelledG (m := m) F ell) (labelledG_isHermitian F ell)
    ((d : ℝ) + (ell : ℝ) - 1) hc).2
  intro x
  rw [abs_of_nonneg (labelledG_quadraticForm_nonneg F ell x)]
  exact labelledG_quadraticForm_le F ell x hell

/-- Grade-envelope form: whenever a nonzero light count `ell` occurs inside
total grade `nu`, the labelled shared-leg operator is bounded by `d + nu`. -/
theorem labelledG_norm_le_grade (F : Frame n d) (ell nu : ℕ)
    (hell : 1 ≤ ell) (hle : ell ≤ nu) :
    ‖labelledG (m := m) F ell‖ ≤ (d : ℝ) + (nu : ℝ) := by
  calc
    ‖labelledG (m := m) F ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 :=
      labelledG_norm_le F ell hell
    _ ≤ (d : ℝ) + (nu : ℝ) := by
      have hleR : (ell : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hle
      linarith

/-! ### Concrete hard-core block coordinates -/

abbrev BlockPattern (T : Finset (Site m n)) (ell : ℕ) :=
  {p : Pattern m n // InBlock T ell p}

abbrev BlockIndex (d : ℕ) (T : Finset (Site m n)) (ell : ℕ) :=
  Fin d × BlockPattern T ell

/-- A fixed enumeration of the exact light support of a block pattern. -/
def lightSupportEquiv (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) : Fin ell ≃ p.1.light :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact p.2.2)).symm

def canonicalLightWord (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (k : Fin ell) : Site m n :=
  (lightSupportEquiv T ell p k).1

@[simp] theorem canonicalLightWord_mem (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (k : Fin ell) :
    canonicalLightWord T ell p k ∈ p.1.light :=
  (lightSupportEquiv T ell p k).2

theorem canonicalLightWord_injective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) :
    Function.Injective (canonicalLightWord T ell p) := by
  intro k l h
  exact (lightSupportEquiv T ell p).injective (Subtype.ext h)

theorem canonicalLightWord_surjective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (s : Site m n) :
    s ∈ p.1.light ↔ ∃ k, canonicalLightWord T ell p k = s := by
  constructor
  · intro hs
    obtain ⟨k, hk⟩ := (lightSupportEquiv T ell p).surjective ⟨s, hs⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rintro ⟨k, rfl⟩
    exact canonicalLightWord_mem T ell p k

/-- Every ordering of the light support gives one hard-core tensor word. -/
def permutedLightWord (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) :
    Fin ell → Site m n :=
  fun k ↦ canonicalLightWord T ell p (pi k)

@[simp] theorem permutedLightWord_refl (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (k : Fin ell) :
    permutedLightWord T ell p (Equiv.refl (Fin ell)) k =
      canonicalLightWord T ell p k := rfl

@[simp] theorem permutedLightWord_refl_fun
    (T : Finset (Site m n)) (ell : ℕ) (p : BlockPattern T ell) :
    permutedLightWord T ell p (Equiv.refl (Fin ell)) =
      canonicalLightWord T ell p := rfl

theorem permutedLightWord_injective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) :
    Function.Injective (permutedLightWord T ell p pi) :=
  (canonicalLightWord_injective T ell p).comp pi.injective

@[simp] theorem permutedLightWord_mem (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) (k : Fin ell) :
    permutedLightWord T ell p pi k ∈ p.1.light :=
  canonicalLightWord_mem T ell p (pi k)

theorem permutedLightWord_surjective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) (s : Site m n) :
    s ∈ p.1.light ↔ ∃ k, permutedLightWord T ell p pi k = s := by
  rw [canonicalLightWord_surjective T ell p s]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨pi.symm k, ?_⟩
    simpa [permutedLightWord, hk]
  · rintro ⟨k, hk⟩
    exact ⟨pi k, hk⟩

/-- The unique slot permutation represented by any injective enumeration of
the exact light support. -/
noncomputable def permutationOfLightWord
    (T : Finset (Site m n)) (ell : ℕ) (p : BlockPattern T ell)
    (w : Fin ell → Site m n)
    (hmem : ∀ k, w k ∈ p.1.light) (hinj : Function.Injective w) :
    Equiv.Perm (Fin ell) := by
  let f : Fin ell → p.1.light := fun k ↦ ⟨w k, hmem k⟩
  have hfInj : Function.Injective f := by
    intro k l h
    exact hinj (congrArg Subtype.val h)
  have hcard : Fintype.card (Fin ell) = Fintype.card p.1.light := by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact p.2.2.symm
  let e : Fin ell ≃ p.1.light :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfInj, hcard⟩)
  exact e.trans (lightSupportEquiv T ell p).symm

@[simp] theorem permutedLightWord_permutationOfLightWord
    (T : Finset (Site m n)) (ell : ℕ) (p : BlockPattern T ell)
    (w : Fin ell → Site m n)
    (hmem : ∀ k, w k ∈ p.1.light) (hinj : Function.Injective w) :
    permutedLightWord T ell p
      (permutationOfLightWord T ell p w hmem hinj) = w := by
  funext k
  simp [permutedLightWord, permutationOfLightWord, canonicalLightWord]

/-- A pattern is determined by its light and heavy supports. -/
theorem pattern_eq_of_light_heavy_eq {p q : Pattern m n}
    (hlight : p.light = q.light) (hheavy : p.heavy = q.heavy) : p = q := by
  funext s
  have hL : (p s = .one) ↔ (q s = .one) := by
    rw [← Pattern.mem_light, ← Pattern.mem_light, hlight]
  have hH : (p s = .two) ↔ (q s = .two) := by
    rw [← Pattern.mem_heavy, ← Pattern.mem_heavy, hheavy]
  cases hp : p s <;> cases hq : q s <;> simp_all

/-- Equality of two enumerated hard-core words recovers the underlying block
pattern and the permutation separately. -/
theorem permutedLightWord_eq_iff
    (T : Finset (Site m n)) (ell : ℕ)
    (p q : BlockPattern T ell)
    (pi sigma : Equiv.Perm (Fin ell)) :
    permutedLightWord T ell p pi = permutedLightWord T ell q sigma ↔
      p = q ∧ pi = sigma := by
  constructor
  · intro hword
    have hlight : p.1.light = q.1.light := by
      ext s
      rw [canonicalLightWord_surjective T ell p s,
        canonicalLightWord_surjective T ell q s]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨sigma (pi.symm k), ?_⟩
        have hkword := congrFun hword (pi.symm k)
        simpa [permutedLightWord, hk] using hkword.symm
      · rintro ⟨k, hk⟩
        refine ⟨pi (sigma.symm k), ?_⟩
        have hkword := congrFun hword (sigma.symm k)
        simpa [permutedLightWord, hk] using hkword
    have hpqVal : p.1 = q.1 :=
      pattern_eq_of_light_heavy_eq hlight (p.2.1.trans q.2.1.symm)
    have hpq : p = q := Subtype.ext hpqVal
    subst q
    have hpi : pi = sigma := by
      apply Equiv.ext
      intro k
      exact canonicalLightWord_injective T ell p
        (congrFun hword k)
    exact ⟨rfl, hpi⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Include the external coordinate and an ordered light support in the
literal labelled-particle basis. -/
def blockLabel (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell) (pi : Equiv.Perm (Fin ell)) :
    LabelledIndex d m n ell :=
  (x.1, permutedLightWord T ell x.2 pi)

@[simp] theorem relabelSlots_blockLabel
    (T : Finset (Site m n)) (ell : ℕ)
    (rho pi : Equiv.Perm (Fin ell)) (x : BlockIndex d T ell) :
    relabelSlots rho (blockLabel T ell x pi) =
      blockLabel T ell x (rho.trans pi) := by
  rfl

theorem blockLabel_eq_iff (T : Finset (Site m n)) (ell : ℕ)
    (x y : BlockIndex d T ell) (pi sigma : Equiv.Perm (Fin ell)) :
    blockLabel T ell x pi = blockLabel T ell y sigma ↔
      x = y ∧ pi = sigma := by
  constructor
  · intro h
    have ha : x.1 = y.1 :=
      congrArg (fun z : LabelledIndex d m n ell ↦ z.1) h
    have hw : permutedLightWord T ell x.2 pi =
        permutedLightWord T ell y.2 sigma :=
      congrArg (fun z : LabelledIndex d m n ell ↦ z.2) h
    obtain ⟨hp, hpi⟩ := (permutedLightWord_eq_iff T ell x.2 y.2 pi sigma).mp hw
    exact ⟨Prod.ext ha hp, hpi⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def permutationCount (ell : ℕ) : ℕ :=
  Fintype.card (Equiv.Perm (Fin ell))

theorem permutationCount_pos (ell : ℕ) : 0 < permutationCount ell := by
  exact Fintype.card_pos

def relativePermEquiv (pi : Equiv.Perm (Fin ell)) :
    Equiv.Perm (Fin ell) ≃ Equiv.Perm (Fin ell) where
  toFun sigma := pi.symm.trans sigma
  invFun tau := pi.trans tau
  left_inv sigma := by
    apply Equiv.ext
    intro k
    simp
  right_inv tau := by
    apply Equiv.ext
    intro k
    simp

theorem labelledG_blockLabel_relative
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x y : BlockIndex d T ell)
    (pi sigma : Equiv.Perm (Fin ell)) :
    labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma) =
      labelledG F ell
        (blockLabel T ell x (Equiv.refl (Fin ell)))
        (blockLabel T ell y (pi.symm.trans sigma)) := by
  calc
    labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma) =
        labelledG F ell
          (relabelSlots pi.symm (blockLabel T ell x pi))
          (relabelSlots pi.symm (blockLabel T ell y sigma)) :=
      (labelledG_relabelSlots F ell pi.symm _ _).symm
    _ = _ := by simp

theorem sum_sum_labelledG_blockLabel
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x y : BlockIndex d T ell) :
    (∑ pi, ∑ sigma,
      labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma)) =
      (permutationCount ell : ℝ) *
        ∑ tau, labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y tau) := by
  calc
    (∑ pi : Equiv.Perm (Fin ell), ∑ sigma : Equiv.Perm (Fin ell),
      labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma)) =
        ∑ pi : Equiv.Perm (Fin ell), ∑ sigma : Equiv.Perm (Fin ell), labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y (pi.symm.trans sigma)) := by
      apply Finset.sum_congr rfl
      intro pi _hpi
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      exact labelledG_blockLabel_relative F T ell x y pi sigma
    _ = ∑ pi : Equiv.Perm (Fin ell), ∑ tau : Equiv.Perm (Fin ell), labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y tau) := by
      apply Finset.sum_congr rfl
      intro pi _hpi
      exact Equiv.sum_comp (relativePermEquiv pi)
        (fun tau ↦ labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y tau))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        permutationCount]

def coordinateDelta {I : Type*} [DecidableEq I] (x y : I) : ℝ :=
  if x = y then 1 else 0

theorem sum_coordinateDelta_mul_coordinateDelta
    {I : Type*} [Fintype I] [DecidableEq I] (x y : I) :
    (∑ z, coordinateDelta z x * coordinateDelta z y) =
      coordinateDelta x y := by
  by_cases hxy : x = y
  · subst y
    simp [coordinateDelta]
  · simp [coordinateDelta, hxy, Ne.symm hxy]

/-- The unnormalized symmetrization matrix: a block basis vector is sent to
the sum of all labelled orderings of its exact light support. -/
def hardCoreLift (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (BlockIndex d T ell) ℝ :=
  fun out x ↦ ∑ pi : Equiv.Perm (Fin ell),
    coordinateDelta out (blockLabel T ell x pi)

/-- Distinct block vectors have disjoint labelled orbits, and every orbit has
exactly `permutationCount ell` elements. -/
theorem hardCoreLift_transpose_mul (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreLift (d := d) T ell).transpose * hardCoreLift T ell =
      (permutationCount ell : ℝ) •
        (1 : Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hardCoreLift]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ out, ∑ pi, ∑ sigma,
        coordinateDelta out (blockLabel T ell x pi) *
          coordinateDelta out (blockLabel T ell y sigma)) =
      ∑ pi, ∑ sigma, ∑ out,
        coordinateDelta out (blockLabel T ell x pi) *
          coordinateDelta out (blockLabel T ell y sigma) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro pi _hpi
        rw [Finset.sum_comm]
    _ = ∑ pi, ∑ sigma,
        coordinateDelta (blockLabel T ell x pi)
          (blockLabel T ell y sigma) := by
      simp_rw [sum_coordinateDelta_mul_coordinateDelta]
    _ = ((permutationCount ell : ℝ) •
        (1 : Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ)) x y := by
      by_cases hxy : x = y
      · subst y
        simp [coordinateDelta, blockLabel_eq_iff, permutationCount]
      · simp [coordinateDelta, blockLabel_eq_iff, hxy,
          permutationCount, Matrix.one_apply]

theorem sum_comm_four
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _hc
      calc
        (∑ a, ∑ b, ∑ d, f a b c d) =
            ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_comm]
        _ = ∑ d, ∑ a, ∑ b, f a b c d := by
          rw [Finset.sum_comm]

theorem hardCoreLift_compression_apply
    (T : Finset (Site m n)) (ell : ℕ)
    (A : Matrix (LabelledIndex d m n ell) (LabelledIndex d m n ell) ℝ)
    (x y : BlockIndex d T ell) :
    ((hardCoreLift (d := d) T ell).transpose * A *
      hardCoreLift (d := d) T ell) x y =
      ∑ pi, ∑ sigma, A (blockLabel T ell x pi) (blockLabel T ell y sigma) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hardCoreLift]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [sum_comm_four]
  apply Finset.sum_congr rfl
  intro pi _hpi
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  simp [coordinateDelta]

/-- The normalized hard-core symmetrization from the exact Fock block into
the distinct-site symmetric subspace of the labelled tensor space. -/
def hardCoreEmbedding (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (BlockIndex d T ell) ℝ :=
  (1 / Real.sqrt (permutationCount ell : ℝ)) • hardCoreLift T ell

/-- The normalization is exact: the hard-core embedding is an isometry. -/
theorem hardCoreEmbedding_transpose_mul
    (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreEmbedding (d := d) T ell).transpose *
        hardCoreEmbedding (d := d) T ell =
      (1 : Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ) := by
  classical
  have hNnat : 0 < permutationCount ell := permutationCount_pos ell
  have hN : (0 : ℝ) < (permutationCount ell : ℝ) := by exact_mod_cast hNnat
  have hsqrt : Real.sqrt (permutationCount ell : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hN)
  have hscalar :
      (1 / Real.sqrt (permutationCount ell : ℝ)) *
          (1 / Real.sqrt (permutationCount ell : ℝ)) *
            (permutationCount ell : ℝ) = 1 := by
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt hN.le]
  rw [hardCoreEmbedding, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, hardCoreLift_transpose_mul]
  rw [smul_smul, smul_smul, hscalar, one_smul]

/-- Exact pullback identity for a finite matrix quadratic form. -/
theorem coordinateQuadratic_compression
    {I J : Type*} [Fintype I] [Fintype J]
    (E : Matrix I J ℝ) (A : Matrix I I ℝ) (x : J → ℝ) :
    coordinateQuadratic (E.transpose * A * E) x =
      coordinateQuadratic A (E.mulVec x) := by
  simp only [coordinateQuadratic]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change x ⬝ᵥ E.transpose.mulVec (A.mulVec (E.mulVec x)) =
    E.mulVec x ⬝ᵥ A.mulVec (E.mulVec x)
  calc
    x ⬝ᵥ E.transpose.mulVec (A.mulVec (E.mulVec x)) =
        E.transpose.mulVec (A.mulVec (E.mulVec x)) ⬝ᵥ x :=
      dotProduct_comm _ _
    _ = Matrix.vecMul (A.mulVec (E.mulVec x)) E ⬝ᵥ x := by
      have h := Matrix.vecMul_transpose E.transpose (A.mulVec (E.mulVec x))
      simpa using congrArg (fun y ↦ y ⬝ᵥ x) h.symm
    _ = A.mulVec (E.mulVec x) ⬝ᵥ E.mulVec x :=
      (Matrix.dotProduct_mulVec (A.mulVec (E.mulVec x)) E x).symm
    _ = E.mulVec x ⬝ᵥ A.mulVec (E.mulVec x) := dotProduct_comm _ _

theorem hardCoreEmbedding_energy (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell → ℝ) :
    coordinateEnergy ((hardCoreEmbedding (d := d) T ell).mulVec x) =
      coordinateEnergy x := by
  rw [coordinateEnergy_mulVec_eq_gram,
    hardCoreEmbedding_transpose_mul]
  simp [coordinateQuadratic, coordinateEnergy, Matrix.mulVec,
    dotProduct, Matrix.one_apply, pow_two]

/-- The literal normalized hard-core compression of the labelled shared-leg
matrix. -/
def hardCoreCompressedG (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ :=
  (hardCoreEmbedding (d := d) T ell).transpose * labelledG F ell *
    hardCoreEmbedding T ell

@[simp] theorem hardCoreCompressedG_transpose
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreCompressedG F T ell).transpose = hardCoreCompressedG F T ell := by
  simp [hardCoreCompressedG, Matrix.transpose_mul, Matrix.mul_assoc]

theorem hardCoreCompressedG_coordinateQuadratic_nonneg
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell → ℝ) :
    0 ≤ coordinateQuadratic (hardCoreCompressedG F T ell) x := by
  rw [hardCoreCompressedG, coordinateQuadratic_compression]
  exact labelledG_coordinateQuadratic_nonneg F ell _

/-- Sharp concrete bound on the explicitly normalized hard-core
compression. -/
theorem hardCoreCompressedG_coordinateQuadratic_le
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell → ℝ) (hell : 1 ≤ ell) :
    coordinateQuadratic (hardCoreCompressedG F T ell) x ≤
      ((d : ℝ) + (ell : ℝ) - 1) * coordinateEnergy x := by
  rw [hardCoreCompressedG, coordinateQuadratic_compression,
    ← hardCoreEmbedding_energy T ell x]
  exact labelledG_coordinateQuadratic_le F ell _ hell

theorem hardCoreCompressedG_isHermitian
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreCompressedG F T ell).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact hardCoreCompressedG_transpose F T ell

/-- L2 operator-norm form of the sharp concrete hard-core compression bound. -/
theorem hardCoreCompressedG_norm_le
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) (hell : 1 ≤ ell) :
    ‖hardCoreCompressedG F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : 0 ≤ (d : ℝ) + (ell : ℝ) - 1 := by linarith
  apply (MatrixTail.opNorm_le_iff_quadraticForm
    (hardCoreCompressedG F T ell)
    (hardCoreCompressedG_isHermitian F T ell)
    ((d : ℝ) + (ell : ℝ) - 1) hc).2
  intro x
  have hupper := hardCoreCompressedG_coordinateQuadratic_le F T ell
    (WithLp.ofLp x) hell
  have hnonneg := hardCoreCompressedG_coordinateQuadratic_nonneg F T ell
    (WithLp.ofLp x)
  rw [← quadraticForm_toLp_eq_coordinateQuadratic] at hupper hnonneg
  have hxnorm : coordinateEnergy (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [coordinateEnergy, Real.norm_eq_abs, pow_two]
  rw [hxnorm] at hupper
  simpa [abs_of_nonneg (by simpa using hnonneg)] using hupper

theorem hardCoreCompressedG_norm_le_grade
    (F : Frame n d) (T : Finset (Site m n)) (ell nu : ℕ)
    (hell : 1 ≤ ell) (hle : ell ≤ nu) :
    ‖hardCoreCompressedG F T ell‖ ≤ (d : ℝ) + (nu : ℝ) := by
  calc
    ‖hardCoreCompressedG F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 :=
      hardCoreCompressedG_norm_le F T ell hell
    _ ≤ (d : ℝ) + (nu : ℝ) := by
      have hleR : (ell : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hle
      linarith

/-- The literal Pattern-level `G-hat` submatrix on one fixed-heavy,
fixed-light block. -/
def ghatBlock (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ :=
  fun out inp ↦ ghat F (out.1, out.2.1) (inp.1, inp.2.1)

theorem eq_update_iff (s : Site m n) (v : Level)
    (out inp : Pattern m n) :
    out = Function.update inp s v ↔
      out s = v ∧ agreesOutsideSite s out inp := by
  constructor
  · rintro rfl
    constructor
    · simp
    · intro x hx
      simp [Function.update, hx]
  · rintro ⟨hs, hoff⟩
    funext x
    by_cases hx : x = s
    · subst x
      simp [hs]
    · simp [Function.update, hx, hoff x hx]

theorem pAt_apply_characterization (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) :
    pAt r i out inp =
      if inp (r, i) = .one ∧
          out = Function.update inp (r, i) .zero then 1 else 0 := by
  classical
  by_cases hoff : agreesOutsideSite (r, i) out inp
  · by_cases hout : out (r, i) = .zero
    · by_cases hin : inp (r, i) = .one
      · have heq : out = Function.update inp (r, i) .zero :=
          (eq_update_iff (r, i) .zero out inp).2 ⟨hout, hoff⟩
        have hoffUpdate : agreesOutsideSite (r, i)
            (Function.update inp (r, i) .zero) inp :=
          (eq_update_iff (r, i) .zero
            (Function.update inp (r, i) .zero) inp).1 rfl |>.2
        simp [pAt, siteKernel, pDestroy, ketBra, hoff, hout, hin, heq,
          hoffUpdate]
      · simp [pAt, siteKernel, pDestroy, ketBra, hoff, hout, hin]
    · have hne : out ≠ Function.update inp (r, i) .zero := by
        intro heq
        apply hout
        simp [heq]
      simp [pAt, siteKernel, pDestroy, ketBra, hoff, hout, hne]
  · have hne : out ≠ Function.update inp (r, i) .zero := by
      intro heq
      apply hoff
      exact (eq_update_iff (r, i) .zero out inp).1 heq |>.2
    simp [pAt, siteKernel, pDestroy, ketBra, hoff, hne]

theorem pDagAt_apply_characterization (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) :
    pDagAt r i out inp =
      if inp (r, i) = .zero ∧
          out = Function.update inp (r, i) .one then 1 else 0 := by
  classical
  by_cases hoff : agreesOutsideSite (r, i) out inp
  · by_cases hout : out (r, i) = .one
    · by_cases hin : inp (r, i) = .zero
      · have heq : out = Function.update inp (r, i) .one :=
          (eq_update_iff (r, i) .one out inp).2 ⟨hout, hoff⟩
        have hoffUpdate : agreesOutsideSite (r, i)
            (Function.update inp (r, i) .one) inp :=
          (eq_update_iff (r, i) .one
            (Function.update inp (r, i) .one) inp).1 rfl |>.2
        simp [pDagAt, siteKernel, pCreate, ketBra, hoff, hout, hin, heq,
          hoffUpdate]
      · simp [pDagAt, siteKernel, pCreate, ketBra, hoff, hout, hin]
    · have hne : out ≠ Function.update inp (r, i) .one := by
        intro heq
        apply hout
        simp [heq]
      simp [pDagAt, siteKernel, pCreate, ketBra, hoff, hout, hne]
  · have hne : out ≠ Function.update inp (r, i) .one := by
      intro heq
      apply hoff
      exact (eq_update_iff (r, i) .one out inp).1 heq |>.2
    simp [pDagAt, siteKernel, pCreate, ketBra, hoff, hne]

def lightMove (inp : Pattern m n) (source target : Site m n) : Pattern m n :=
  Function.update (Function.update inp source .zero) target .one

theorem update_source_zero_apply_eq_zero_iff
    (inp : Pattern m n) (source target : Site m n) :
    Function.update inp source .zero target = .zero ↔
      target = source ∨ inp target = .zero := by
  by_cases h : target = source
  · subst target
    simp
  · simp [Function.update, h]

theorem pDagAt_mul_pAt_apply (r : Fin m) (i j : Fin n)
    (out inp : Pattern m n) :
    (pDagAt r i * pAt r j) out inp =
      if inp (r, j) = .one ∧
          ((r, i) = (r, j) ∨ inp (r, i) = .zero) ∧
          out = lightMove inp (r, j) (r, i) then 1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [pDagAt_apply_characterization, pAt_apply_characterization]
  by_cases hsource : inp (r, j) = .one
  · simp only [hsource, true_and]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq']
    simp [update_source_zero_apply_eq_zero_iff, lightMove]
  · simp [hsource]

theorem heavy_lightMove_of_legal (inp : Pattern m n) (source target : Site m n)
    (hsource : inp source = .one)
    (havailable : target = source ∨ inp target = .zero) :
    (lightMove inp source target).heavy = inp.heavy := by
  classical
  ext x
  simp only [Pattern.mem_heavy]
  by_cases hxt : x = target
  · subst x
    have htNotTwo : inp target ≠ .two := by
      intro htwo
      rcases havailable with hts | htzero
      · subst target
        exact Level.noConfusion (hsource.symm.trans htwo)
      · exact Level.noConfusion (htzero.symm.trans htwo)
    simp [lightMove, htNotTwo]
  · by_cases hxs : x = source
    · subst x
      simp [lightMove, Function.update, hxt, hsource]
    · simp [lightMove, Function.update, hxt, hxs]

theorem light_lightMove_of_legal (inp : Pattern m n) (source target : Site m n)
    (hsource : inp source = .one)
    (havailable : target = source ∨ inp target = .zero) :
    (lightMove inp source target).light = insert target (inp.light.erase source) := by
  classical
  ext x
  simp only [Pattern.mem_light, Finset.mem_insert, Finset.mem_erase]
  by_cases hxt : x = target
  · subst x
    simp [lightMove]
  · by_cases hxs : x = source
    · subst x
      simp [lightMove, Function.update, hxt]
    · simp [lightMove, Function.update, hxt, hxs]

theorem card_light_lightMove_of_legal
    (inp : Pattern m n) (source target : Site m n)
    (hsource : inp source = .one)
    (havailable : target = source ∨ inp target = .zero) :
    (lightMove inp source target).light.card = inp.light.card := by
  classical
  rw [light_lightMove_of_legal inp source target hsource havailable]
  have hsMem : source ∈ inp.light := Pattern.mem_light.mpr hsource
  rcases havailable with rfl | htarget
  · simp [hsMem]
  · have htNotMem : target ∉ inp.light := by
      simp [Pattern.mem_light, htarget]
    rw [Finset.card_insert_of_notMem (by simp [htNotMem]),
      Finset.card_erase_of_mem hsMem]
    have hcardpos : 0 < inp.light.card := Finset.card_pos.mpr ⟨source, hsMem⟩
    omega

/-- `G-hat` has no matrix entries between distinct fixed-heavy/fixed-light
blocks. -/
theorem ghat_apply_eq_zero_of_block_ne
    (F : Frame n d) (out inp : Fin d × Pattern m n)
    (hne : out.2.heavy ≠ inp.2.heavy ∨
      out.2.light.card ≠ inp.2.light.card) :
    ghat (m := m) F out inp = 0 := by
  classical
  rw [ghat_apply]
  apply Finset.sum_eq_zero
  intro r _hr
  apply Finset.sum_eq_zero
  intro i _hi
  apply Finset.sum_eq_zero
  intro j _hj
  rw [pDagAt_mul_pAt_apply]
  by_cases hlegal : inp.2 (r, j) = .one ∧
      ((r, i) = (r, j) ∨ inp.2 (r, i) = .zero) ∧
      out.2 = lightMove inp.2 (r, j) (r, i)
  · rcases hlegal with ⟨hsource, havailable, hmove⟩
    have hheavy : out.2.heavy = inp.2.heavy := by
      rw [hmove]
      exact heavy_lightMove_of_legal inp.2 (r, j) (r, i)
        hsource havailable
    have hlight : out.2.light.card = inp.2.light.card := by
      rw [hmove]
      exact card_light_lightMove_of_legal inp.2 (r, j) (r, i)
        hsource havailable
    exact False.elim (hne.elim (fun h ↦ h hheavy) (fun h ↦ h hlight))
  · rw [if_neg hlegal]
    ring

/-- A matching labelled spectator configuration is exactly a legal hard-core
light move on the underlying Pattern block.  This is the pointwise
combinatorial content of the bosonic compression. -/
theorem lightMove_legal_of_domain_eq
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell)
    (pi sigma : Equiv.Perm (Fin ell)) (k : Fin ell)
    (hdom : domainOfWord k (permutedLightWord T ell out pi) =
      domainOfWord k (permutedLightWord T ell inp sigma)) :
    let O := permutedLightWord T ell out pi
    let I := permutedLightWord T ell inp sigma
    inp.1 (I k) = .one ∧
      (O k = I k ∨ inp.1 (O k) = .zero) ∧
      out.1 = lightMove inp.1 (I k) (O k) := by
  classical
  let O := permutedLightWord T ell out pi
  let I := permutedLightWord T ell inp sigma
  have hmatch := (domainOfWord_eq_iff k O I).1 hdom
  have hrow : (O k).1 = (I k).1 := hmatch.1
  have hoff : ∀ l, l ≠ k → O l = I l := hmatch.2
  have htone : out.1 (O k) = .one := by
    apply Pattern.mem_light.mp
    exact permutedLightWord_mem T ell out pi k
  have hsone : inp.1 (I k) = .one := by
    apply Pattern.mem_light.mp
    exact permutedLightWord_mem T ell inp sigma k
  have hheavy : out.1.heavy = inp.1.heavy := out.2.1.trans inp.2.1.symm
  by_cases hsame : O k = I k
  · have hword : O = I := by
      funext l
      by_cases hlk : l = k
      · subst l
        exact hsame
      · exact hoff l hlk
    have houtinp : out = inp :=
      (permutedLightWord_eq_iff T ell out inp pi sigma).1 hword |>.1
    have hmove : lightMove inp.1 (I k) (O k) = inp.1 := by
      rw [hsame]
      funext x
      by_cases hx : x = I k
      · subst x
        simp [lightMove, hsone]
      · simp [lightMove, Function.update, hx]
    exact ⟨hsone, Or.inl hsame,
      congrArg Subtype.val houtinp |>.trans hmove.symm⟩
  · have htNotOne : inp.1 (O k) ≠ .one := by
      intro htInp
      have htMem : O k ∈ inp.1.light := Pattern.mem_light.mpr htInp
      obtain ⟨l, hl⟩ :=
        (permutedLightWord_surjective T ell inp sigma (O k)).1 htMem
      have hlk : l ≠ k := by
        intro hlk
        subst l
        exact hsame hl.symm
      have hOl : O l = O k := (hoff l hlk).trans hl
      exact hlk ((permutedLightWord_injective T ell out pi) hOl)
    have htNotTwo : inp.1 (O k) ≠ .two := by
      intro htInp
      have htMem : O k ∈ inp.1.heavy := Pattern.mem_heavy.mpr htInp
      have htOutMem : O k ∈ out.1.heavy := by simpa [hheavy] using htMem
      have htOut := Pattern.mem_heavy.mp htOutMem
      exact Level.noConfusion (htone.symm.trans htOut)
    have htzero : inp.1 (O k) = .zero := by
      cases h : inp.1 (O k) with
      | zero => rfl
      | one => exact False.elim (htNotOne h)
      | two => exact False.elim (htNotTwo h)
    have hsNotOne : out.1 (I k) ≠ .one := by
      intro hsOut
      have hsMem : I k ∈ out.1.light := Pattern.mem_light.mpr hsOut
      obtain ⟨l, hl⟩ :=
        (permutedLightWord_surjective T ell out pi (I k)).1 hsMem
      have hlk : l ≠ k := by
        intro hlk
        subst l
        exact hsame hl
      have hIl : I l = I k := (hoff l hlk).symm.trans hl
      exact hlk ((permutedLightWord_injective T ell inp sigma) hIl)
    have hsNotTwo : out.1 (I k) ≠ .two := by
      intro hsOut
      have hsMem : I k ∈ out.1.heavy := Pattern.mem_heavy.mpr hsOut
      have hsInpMem : I k ∈ inp.1.heavy := by simpa [hheavy] using hsMem
      have hsInp := Pattern.mem_heavy.mp hsInpMem
      exact Level.noConfusion (hsone.symm.trans hsInp)
    have hszero : out.1 (I k) = .zero := by
      cases h : out.1 (I k) with
      | zero => rfl
      | one => exact False.elim (hsNotOne h)
      | two => exact False.elim (hsNotTwo h)
    have houtMove : out.1 = lightMove inp.1 (I k) (O k) := by
      funext x
      by_cases hxt : x = O k
      · subst x
        simp [lightMove, htone]
      · by_cases hxs : x = I k
        · subst x
          simp [lightMove, Function.update, Ne.symm hsame, hszero]
        · have hone : out.1 x = .one ↔ inp.1 x = .one := by
            constructor
            · intro hxOut
              have hxMem : x ∈ out.1.light := Pattern.mem_light.mpr hxOut
              obtain ⟨l, hl⟩ :=
                (permutedLightWord_surjective T ell out pi x).1 hxMem
              have hlk : l ≠ k := by
                intro hlk
                subst l
                exact hxt hl.symm
              have : I l = x := (hoff l hlk).symm.trans hl
              exact Pattern.mem_light.mp
                ((permutedLightWord_surjective T ell inp sigma x).2 ⟨l, this⟩)
            · intro hxInp
              have hxMem : x ∈ inp.1.light := Pattern.mem_light.mpr hxInp
              obtain ⟨l, hl⟩ :=
                (permutedLightWord_surjective T ell inp sigma x).1 hxMem
              have hlk : l ≠ k := by
                intro hlk
                subst l
                exact hxs hl.symm
              have : O l = x := (hoff l hlk).trans hl
              exact Pattern.mem_light.mp
                ((permutedLightWord_surjective T ell out pi x).2 ⟨l, this⟩)
          have htwo : out.1 x = .two ↔ inp.1 x = .two := by
            rw [← Pattern.mem_heavy, ← Pattern.mem_heavy, hheavy]
          have hval : out.1 x = inp.1 x := by
            cases ho : out.1 x <;> cases hi : inp.1 x <;> simp_all
          simpa [lightMove, Function.update, hxt, hxs] using hval
    exact ⟨hsone, Or.inr htzero, houtMove⟩

/-- Conversely, every legal Pattern-level move admits the unique labelled
ordering whose spectators coincide with the canonical output ordering. -/
theorem exists_permutation_of_legal_move
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (k : Fin ell)
    (r : Fin m) (i j : Fin n)
    (htarget : canonicalLightWord T ell out k = (r, i))
    (hsource : inp.1 (r, j) = .one)
    (havailable : (r, i) = (r, j) ∨ inp.1 (r, i) = .zero)
    (hmove : out.1 = lightMove inp.1 (r, j) (r, i)) :
    ∃ tau : Equiv.Perm (Fin ell),
      domainOfWord k (canonicalLightWord T ell out) =
          domainOfWord k (permutedLightWord T ell inp tau) ∧
        permutedLightWord T ell inp tau k = (r, j) := by
  classical
  let O := canonicalLightWord T ell out
  let source : Site m n := (r, j)
  let target : Site m n := (r, i)
  let w : Fin ell → Site m n := Function.update O k source
  have hOinj : Function.Injective O :=
    canonicalLightWord_injective T ell out
  have htargetO : O k = target := by simpa [O, target] using htarget
  have hsMem : source ∈ inp.1.light := by
    exact Pattern.mem_light.mpr hsource
  have hOffTarget (l : Fin ell) (hlk : l ≠ k) : O l ≠ target := by
    intro hlt
    apply hlk
    apply hOinj
    exact hlt.trans htargetO.symm
  have hsOutZero : target ≠ source → out.1 source = .zero := by
    intro hne
    change out.1 source = .zero
    rw [hmove]
    change lightMove inp.1 source target source = .zero
    simp [lightMove, Function.update, Ne.symm hne]
  have hOffSource (l : Fin ell) (hlk : l ≠ k) : O l ≠ source := by
    intro hls
    by_cases hts : target = source
    · exact hOffTarget l hlk (hls.trans hts.symm)
    · have hOlOne : out.1 (O l) = .one := by
        apply Pattern.mem_light.mp
        exact canonicalLightWord_mem T ell out l
      have : out.1 source = .one := by simpa [hls] using hOlOne
      exact Level.noConfusion (this.symm.trans (hsOutZero hts))
  have hmem : ∀ l, w l ∈ inp.1.light := by
    intro l
    by_cases hlk : l = k
    · subst l
      simpa [w, source] using hsMem
    · have hOlOne : out.1 (O l) = .one := by
        apply Pattern.mem_light.mp
        exact canonicalLightWord_mem T ell out l
      have hInpOne : inp.1 (O l) = .one := by
        rw [hmove] at hOlOne
        change lightMove inp.1 source target (O l) = .one at hOlOne
        simpa [lightMove, Function.update, hOffTarget l hlk,
          hOffSource l hlk] using hOlOne
      apply Pattern.mem_light.mpr
      simpa [w, Function.update, hlk] using hInpOne
  have hinj : Function.Injective w := by
    intro a b hab
    by_cases ha : a = k
    · subst a
      by_cases hb : b = k
      · exact hb.symm
      · exfalso
        apply hOffSource b hb
        simpa [w, Function.update, hb] using hab.symm
    · by_cases hb : b = k
      · subst b
        exfalso
        apply hOffSource a ha
        simpa [w, Function.update, ha] using hab
      · apply hOinj
        simpa [w, Function.update, ha, hb] using hab
  let tau := permutationOfLightWord T ell inp w hmem hinj
  have hword : permutedLightWord T ell inp tau = w := by
    exact permutedLightWord_permutationOfLightWord T ell inp w hmem hinj
  refine ⟨tau, ?_, ?_⟩
  · rw [hword]
    apply (domainOfWord_eq_iff k _ _).2
    constructor
    · simp [w, O, source, target, htargetO]
    · intro l hlk
      change O l = w l
      simp [w, hlk]
  · rw [hword]
    simp [w, source]

abbrev OrbitRaw (ell : ℕ) := Fin ell × Equiv.Perm (Fin ell)
abbrev MoveRaw (m n : ℕ) := Fin m × (Fin n × Fin n)

def OrbitCompatible (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (z : OrbitRaw ell) : Prop :=
  domainOfWord z.1 (canonicalLightWord T ell out) =
    domainOfWord z.1 (permutedLightWord T ell inp z.2)

instance instDecidableOrbitCompatible (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (z : OrbitRaw ell) :
    Decidable (OrbitCompatible T ell out inp z) := Classical.propDecidable _

def LegalLightMove (out inp : Pattern m n) (z : MoveRaw m n) : Prop :=
  inp (z.1, z.2.2) = .one ∧
    ((z.1, z.2.1) = (z.1, z.2.2) ∨ inp (z.1, z.2.1) = .zero) ∧
    out = lightMove inp (z.1, z.2.2) (z.1, z.2.1)

instance instDecidableLegalLightMove (out inp : Pattern m n) (z : MoveRaw m n) :
    Decidable (LegalLightMove out inp z) := Classical.propDecidable _

/-- Forget labels from one compatible omitted-slot configuration, retaining
the target and source columns of the induced Pattern move. -/
def orbitToLegalMove (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell)
    (z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z}) :
    {z : MoveRaw m n // LegalLightMove out.1 inp.1 z} := by
  let k := z.1.1
  let tau := z.1.2
  let target := canonicalLightWord T ell out k
  let source := permutedLightWord T ell inp tau k
  have hdom : domainOfWord k (canonicalLightWord T ell out) =
      domainOfWord k (permutedLightWord T ell inp tau) := z.2
  have hlegal := lightMove_legal_of_domain_eq T ell out inp
    (Equiv.refl (Fin ell)) tau k (by simpa using hdom)
  have hrow : target.1 = source.1 :=
    (domainOfWord_eq_iff k _ _).1 hdom |>.1
  have hsourceSite : (target.1, source.2) = source := Prod.ext hrow rfl
  refine ⟨(target.1, (target.2, source.2)), ?_⟩
  simpa [LegalLightMove, target, source, hsourceSite] using hlegal

theorem orbitToLegalMove_injective
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) :
    Function.Injective (orbitToLegalMove T ell out inp) := by
  intro x y hxy
  apply Subtype.ext
  rcases x with ⟨⟨kx, taux⟩, hx⟩
  rcases y with ⟨⟨ky, tauy⟩, hy⟩
  have hval := congrArg Subtype.val hxy
  change
    ((canonicalLightWord T ell out kx).1,
      ((canonicalLightWord T ell out kx).2,
        (permutedLightWord T ell inp taux kx).2)) =
    ((canonicalLightWord T ell out ky).1,
      ((canonicalLightWord T ell out ky).2,
        (permutedLightWord T ell inp tauy ky).2)) at hval
  have htarget : canonicalLightWord T ell out kx =
      canonicalLightWord T ell out ky := by
    have hr := congrArg (fun z : MoveRaw m n ↦ z.1) hval
    have hi := congrArg (fun z : MoveRaw m n ↦ z.2.1) hval
    exact Prod.ext hr hi
  have hk : kx = ky :=
    (canonicalLightWord_injective T ell out) htarget
  subst ky
  have hsource : permutedLightWord T ell inp taux kx =
      permutedLightWord T ell inp tauy kx := by
    have hj := congrArg (fun z : MoveRaw m n ↦ z.2.2) hval
    have hrowx := (domainOfWord_eq_iff kx _ _).1 hx |>.1
    have hrowy := (domainOfWord_eq_iff kx _ _).1 hy |>.1
    exact Prod.ext (hrowx.symm.trans hrowy) hj
  have hword : permutedLightWord T ell inp taux =
      permutedLightWord T ell inp tauy := by
    funext l
    by_cases hl : l = kx
    · subst l
      exact hsource
    · exact ((domainOfWord_eq_iff kx _ _).1 hx |>.2 l hl).symm.trans
        ((domainOfWord_eq_iff kx _ _).1 hy |>.2 l hl)
  have htau : taux = tauy :=
    (permutedLightWord_eq_iff T ell inp inp taux tauy).1 hword |>.2
  subst tauy
  rfl

theorem orbitToLegalMove_surjective
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) :
    Function.Surjective (orbitToLegalMove T ell out inp) := by
  intro y
  rcases y with ⟨⟨r, i, j⟩, hy⟩
  have hsource := hy.1
  have havailable := hy.2.1
  have hmove := hy.2.2
  have htone : out.1 (r, i) = .one := by
    rw [hmove]
    simp [lightMove]
  have htMem : (r, i) ∈ out.1.light := Pattern.mem_light.mpr htone
  obtain ⟨k, hk⟩ :=
    (canonicalLightWord_surjective T ell out (r, i)).1 htMem
  obtain ⟨tau, hdom, hsrc⟩ := exists_permutation_of_legal_move
    T ell out inp k r i j hk hsource havailable hmove
  let x : {z : OrbitRaw ell // OrbitCompatible T ell out inp z} :=
    ⟨(k, tau), hdom⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change
    ((canonicalLightWord T ell out k).1,
      ((canonicalLightWord T ell out k).2,
        (permutedLightWord T ell inp tau k).2)) = (r, (i, j))
  simp [hk, hsrc]

/-- Weighted finite-sum form of the exact orbit/legal-move bijection.  The
weights depend only on the target and source columns, as in the frame Gram
entry. -/
theorem orbit_legal_weighted_sum
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (a b : Fin n → ℝ) :
    (∑ k, ∑ tau,
      if OrbitCompatible T ell out inp (k, tau) then
        a (canonicalLightWord T ell out k).2 *
          b (permutedLightWord T ell inp tau k).2
      else 0) =
    ∑ r, ∑ i, ∑ j,
      if LegalLightMove out.1 inp.1 (r, (i, j)) then a i * b j else 0 := by
  classical
  let orbitSet : Finset (OrbitRaw ell) :=
    Finset.univ.filter (OrbitCompatible T ell out inp)
  let moveSet : Finset (MoveRaw m n) :=
    Finset.univ.filter (LegalLightMove out.1 inp.1)
  let e : {z : OrbitRaw ell // OrbitCompatible T ell out inp z} ≃
      {z : MoveRaw m n // LegalLightMove out.1 inp.1 z} :=
    Equiv.ofBijective (orbitToLegalMove T ell out inp)
      ⟨orbitToLegalMove_injective T ell out inp,
        orbitToLegalMove_surjective T ell out inp⟩
  have horbitSubtype :
      (∑ z : OrbitRaw ell,
        if OrbitCompatible T ell out inp z then
          a (canonicalLightWord T ell out z.1).2 *
            b (permutedLightWord T ell inp z.2 z.1).2
        else 0) =
      ∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
        a (canonicalLightWord T ell out z.1.1).2 *
          b (permutedLightWord T ell inp z.1.2 z.1.1).2 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype orbitSet (by simp [orbitSet])
      (fun z : OrbitRaw ell ↦
        a (canonicalLightWord T ell out z.1).2 *
          b (permutedLightWord T ell inp z.2 z.1).2)
  have hmoveSubtype :
      (∑ z : MoveRaw m n,
        if LegalLightMove out.1 inp.1 z then a z.2.1 * b z.2.2 else 0) =
      ∑ z : {z : MoveRaw m n // LegalLightMove out.1 inp.1 z},
        a z.1.2.1 * b z.1.2.2 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype moveSet (by simp [moveSet])
      (fun z : MoveRaw m n ↦ a z.2.1 * b z.2.2)
  have hequiv :
      (∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
        a (canonicalLightWord T ell out z.1.1).2 *
          b (permutedLightWord T ell inp z.1.2 z.1.1).2) =
      ∑ z : {z : MoveRaw m n // LegalLightMove out.1 inp.1 z},
        a z.1.2.1 * b z.1.2.2 := by
    have h := Equiv.sum_comp e
      (fun z : {z : MoveRaw m n // LegalLightMove out.1 inp.1 z} ↦
        a z.1.2.1 * b z.1.2.2)
    calc
      (∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
        a (canonicalLightWord T ell out z.1.1).2 *
          b (permutedLightWord T ell inp z.1.2 z.1.1).2) =
          ∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
            a (e z).1.2.1 * b (e z).1.2.2 := by
              apply Finset.sum_congr rfl
              intro z _hz
              rfl
      _ = _ := h
  calc
    (∑ k, ∑ tau,
      if OrbitCompatible T ell out inp (k, tau) then
        a (canonicalLightWord T ell out k).2 *
          b (permutedLightWord T ell inp tau k).2 else 0) =
        ∑ z : OrbitRaw ell,
          if OrbitCompatible T ell out inp z then
            a (canonicalLightWord T ell out z.1).2 *
              b (permutedLightWord T ell inp z.2 z.1).2 else 0 := by
          rw [Fintype.sum_prod_type]
    _ = _ := horbitSubtype
    _ = _ := hequiv
    _ = (∑ z : MoveRaw m n,
          if LegalLightMove out.1 inp.1 z then a z.2.1 * b z.2.2 else 0) :=
      hmoveSubtype.symm
    _ = ∑ r, ∑ i, ∑ j,
        if LegalLightMove out.1 inp.1 (r, (i, j)) then a i * b j else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Fintype.sum_prod_type]

set_option maxHeartbeats 1000000 in
theorem orbit_sum_labelledG_eq_ghatBlock
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockIndex d T ell) :
    (∑ tau : Equiv.Perm (Fin ell), labelledG F ell
      (blockLabel T ell out (Equiv.refl (Fin ell)))
      (blockLabel T ell inp tau)) = ghatBlock F T ell out inp := by
  classical
  rw [ghatBlock, ghat_apply]
  simp only [labelledG, Matrix.sum_apply, qSlot, blockLabel,
    permutedLightWord, Equiv.refl_apply]
  rw [Finset.sum_comm]
  simp_rw [pDagAt_mul_pAt_apply]
  have h := orbit_legal_weighted_sum T ell out.2 inp.2
    (fun i ↦ F.u i out.1) (fun j ↦ F.u j inp.1)
  convert h using 1 <;>
    simp [OrbitCompatible, LegalLightMove, permutedLightWord, mul_ite]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro tau _htau
  by_cases hp : domainOfWord k (canonicalLightWord T ell out.2) =
      domainOfWord k (permutedLightWord T ell inp.2 tau)
  · simp only [hp, if_pos]
  · simp only [hp, if_neg]

/-- The unnormalized symmetrization produces exactly one factorial copy of
the literal fixed-heavy/fixed-light `G-hat` block. -/
theorem hardCoreLift_labelledG_compression
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreLift (d := d) T ell).transpose * labelledG F ell *
        hardCoreLift T ell =
      (permutationCount ell : ℝ) • ghatBlock F T ell := by
  ext out inp
  rw [hardCoreLift_compression_apply,
    sum_sum_labelledG_blockLabel,
    orbit_sum_labelledG_eq_ghatBlock]
  rfl

/-- Exact concrete compression identity: normalized hard-core
symmetrization of the labelled Gram matrix is the actual Pattern/Fock
`G-hat` block, with no relaxation or comparison premise. -/
theorem hardCoreCompressedG_eq_ghatBlock
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    hardCoreCompressedG F T ell = ghatBlock F T ell := by
  have hNnat : 0 < permutationCount ell := permutationCount_pos ell
  have hN : (0 : ℝ) < (permutationCount ell : ℝ) := by exact_mod_cast hNnat
  have hsqrt : Real.sqrt (permutationCount ell : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hN)
  have hscalar :
      (1 / Real.sqrt (permutationCount ell : ℝ)) *
          (1 / Real.sqrt (permutationCount ell : ℝ)) *
            (permutationCount ell : ℝ) = 1 := by
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt hN.le]
  rw [hardCoreCompressedG, hardCoreEmbedding, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    hardCoreLift_labelledG_compression]
  rw [smul_smul, smul_smul, hscalar, one_smul]

/-- Sharp Euclidean operator norm of the actual fixed-heavy/fixed-light
Pattern block. -/
theorem ghatBlock_norm_le
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) (hell : 1 ≤ ell) :
    ‖ghatBlock F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 := by
  rw [← hardCoreCompressedG_eq_ghatBlock F T ell]
  exact hardCoreCompressedG_norm_le F T ell hell

theorem ghatBlock_norm_le_grade
    (F : Frame n d) (T : Finset (Site m n)) (ell nu : ℕ)
    (hell : 1 ≤ ell) (hle : ell ≤ nu) :
    ‖ghatBlock F T ell‖ ≤ (d : ℝ) + (nu : ℝ) - 1 := by
  calc
    ‖ghatBlock F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 :=
      ghatBlock_norm_le F T ell hell
    _ ≤ (d : ℝ) + (nu : ℝ) - 1 := by
      have hleR : (ell : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hle
      linarith

/-! ### Finite direct sum of the concrete Pattern blocks -/

abbrev LightCount (m n : ℕ) := Fin (Fintype.card (Site m n) + 1)

abbrev FockBlockKey (m n : ℕ) := Finset (Site m n) × LightCount m n

def patternLightCount (p : Pattern m n) : LightCount m n :=
  ⟨p.light.card, Nat.lt_succ_of_le (Finset.card_le_univ p.light)⟩

def patternBlockKey (p : Pattern m n) : FockBlockKey m n :=
  (p.heavy, patternLightCount p)

def fullKeyFiberEquiv (q : FockBlockKey m n) :
    {x : Fin d × Pattern m n // patternBlockKey x.2 = q} ≃
      BlockIndex d q.1 q.2.1 where
  toFun x :=
    (x.1.1, ⟨x.1.2,
      congrArg Prod.fst x.2,
      congrArg (fun z : FockBlockKey m n ↦ z.2.1) x.2⟩)
  invFun z :=
    ⟨(z.1, z.2.1), by
      apply Prod.ext
      · exact z.2.2.1
      · apply Fin.ext
        exact z.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

/-- Every full external/Fock coordinate belongs to one and only one finite
fixed-heavy/fixed-light block. -/
def fullIndexBlockEquiv :
    (Fin d × Pattern m n) ≃
      Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1 :=
  (Equiv.sigmaFiberEquiv
    (fun x : Fin d × Pattern m n ↦ patternBlockKey x.2)).symm.trans
      (Equiv.sigmaCongrRight fun q ↦ fullKeyFiberEquiv (d := d) q)

@[simp] theorem fullIndexBlockEquiv_symm_apply
    (q : FockBlockKey m n) (z : BlockIndex d q.1 q.2.1) :
    (fullIndexBlockEquiv (d := d) (m := m) (n := n)).symm ⟨q, z⟩ =
      (z.1, z.2.1) := rfl

def blockFiber (x : Fin d × Pattern m n → ℝ) (q : FockBlockKey m n) :
    BlockIndex d q.1 q.2.1 → ℝ :=
  fun z ↦ x (z.1, z.2.1)

theorem normSq_eq_sum_blockFiber (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq x =
      ∑ q : FockBlockKey m n, coordinateEnergy (blockFiber x q) := by
  classical
  have h := Equiv.sum_comp (fullIndexBlockEquiv (d := d) (m := m) (n := n))
    (fun z : Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1 ↦
      x ((fullIndexBlockEquiv (d := d) (m := m) (n := n)).symm z) ^ 2)
  rw [Fintype.sum_sigma] at h
  simpa [FiniteHilbert.normSq, coordinateEnergy, blockFiber] using h

def blockGrade (q : FockBlockKey m n) : ℕ := q.2.1 + 2 * q.1.card

theorem grade_eq_blockGrade {q : FockBlockKey m n}
    (p : BlockPattern q.1 q.2.1) : p.1.grade = blockGrade q := by
  rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy]
  simp [blockGrade, p.2.1, p.2.2]

theorem ghat_mul_gradeProjection_apply
    (F : Frame n d) (nu : ℕ)
    (out inp : Fin d × Pattern m n) :
    (ghat (m := m) F *
      gradeProjection (d := d) (m := m) (n := n) nu) out inp =
      if inp.2.grade = nu then ghat (m := m) F out inp else 0 := by
  classical
  rw [gradeProjection, Matrix.mul_diagonal]
  by_cases h : inp.2.grade = nu <;> simp [h]

theorem ghat_apply_eq_zero_of_key_ne
    (F : Frame n d) {q q' : FockBlockKey m n}
    (out : BlockIndex d q.1 q.2.1)
    (inp : BlockIndex d q'.1 q'.2.1) (hne : q ≠ q') :
    ghat (m := m) F (out.1, out.2.1) (inp.1, inp.2.1) = 0 := by
  apply ghat_apply_eq_zero_of_block_ne
  by_contra hsame
  push_neg at hsame
  apply hne
  apply Prod.ext
  · exact out.2.2.1.symm.trans (hsame.1.trans inp.2.2.1)
  · apply Fin.ext
    exact out.2.2.2.symm.trans (hsame.2.trans inp.2.2.2)

set_option maxHeartbeats 1000000 in
theorem blockFiber_ghat_gradeProjection_mulVec
    (F : Frame n d) (nu : ℕ) (x : Fin d × Pattern m n → ℝ)
    (q : FockBlockKey m n) :
    blockFiber
      (Matrix.mulVec
        (ghat (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) x) q =
      if blockGrade q = nu then
        Matrix.mulVec (ghatBlock F q.1 q.2.1) (blockFiber x q)
      else 0 := by
  classical
  funext out
  let e := fullIndexBlockEquiv (d := d) (m := m) (n := n)
  let A := ghat (m := m) F *
    gradeProjection (d := d) (m := m) (n := n) nu
  change Matrix.mulVec A x (out.1, out.2.1) = _
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ inp : Fin d × Pattern m n,
      A (out.1, out.2.1) inp * x inp) =
        ∑ z : Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1,
          A (out.1, out.2.1) (e.symm z) * x (e.symm z) := by
            have h := Equiv.sum_comp e
              (fun z : Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1 ↦
                A (out.1, out.2.1) (e.symm z) * x (e.symm z))
            simpa using h
    _ = ∑ q' : FockBlockKey m n,
          ∑ inp : BlockIndex d q'.1 q'.2.1,
            A (out.1, out.2.1) (inp.1, inp.2.1) *
              x (inp.1, inp.2.1) := by
          rw [Fintype.sum_sigma]
          rfl
    _ = ∑ inp : BlockIndex d q.1 q.2.1,
            A (out.1, out.2.1) (inp.1, inp.2.1) *
            x (inp.1, inp.2.1) := by
          apply Finset.sum_eq_single q
          · intro q' _hq' hq'ne
            apply Finset.sum_eq_zero
            intro inp _hinp
            change
              (ghat (m := m) F *
                gradeProjection (d := d) (m := m) (n := n) nu)
                  (out.1, out.2.1) (inp.1, inp.2.1) *
                x (inp.1, inp.2.1) = 0
            rw [ghat_mul_gradeProjection_apply]
            by_cases hg : inp.2.1.grade = nu
            · rw [if_pos hg, ghat_apply_eq_zero_of_key_ne F out inp
                (Ne.symm hq'ne)]
              simp
            · simp [hg]
          · intro hq
            exact False.elim (hq (Finset.mem_univ q))
    _ = ∑ inp : BlockIndex d q.1 q.2.1,
          (if blockGrade q = nu then ghatBlock F q.1 q.2.1 out inp else 0) *
            blockFiber x q inp := by
          apply Finset.sum_congr rfl
          intro inp _hinp
          rw [show A (out.1, out.2.1) (inp.1, inp.2.1) =
              if inp.2.1.grade = nu then
                ghat (m := m) F (out.1, out.2.1) (inp.1, inp.2.1)
              else 0 by
                exact ghat_mul_gradeProjection_apply F nu _ _]
          rw [grade_eq_blockGrade inp.2]
          rfl
    _ = (if blockGrade q = nu then
          ∑ inp, ghatBlock F q.1 q.2.1 out inp * blockFiber x q inp
        else 0) := by
          by_cases hg : blockGrade q = nu <;> simp [hg]
    _ = (if blockGrade q = nu then
          Matrix.mulVec (ghatBlock F q.1 q.2.1) (blockFiber x q)
        else 0) out := by
          by_cases hg : blockGrade q = nu <;>
            simp [hg, Matrix.mulVec, dotProduct]

theorem ghatBlock_zero_light
    (F : Frame n d) (T : Finset (Site m n)) :
    ghatBlock F T 0 = 0 := by
  ext out inp
  rw [← orbit_sum_labelledG_eq_ghatBlock F T 0 out inp]
  simp [labelledG]

theorem coordinateEnergy_mulVec_le_of_norm_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (z : I → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) :
    coordinateEnergy (A.mulVec z) ≤ C ^ 2 * coordinateEnergy z := by
  let zE : EuclideanSpace ℝ I := WithLp.toLp 2 z
  let yE : EuclideanSpace ℝ I :=
    (EuclideanSpace.equiv I ℝ).symm (Matrix.mulVec A zE)
  have hop : ‖yE‖ ≤ ‖A‖ * ‖zE‖ := by
    simpa [yE] using Matrix.l2_opNorm_mulVec A zE
  have hopC : ‖yE‖ ≤ C * ‖zE‖ :=
    hop.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg zE))
  have hz : ‖zE‖ ^ 2 = coordinateEnergy z := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [zE, coordinateEnergy]
  have hy : ‖yE‖ ^ 2 = coordinateEnergy (A.mulVec z) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [yE, zE, coordinateEnergy, Matrix.mulVec]
  calc
    coordinateEnergy (A.mulVec z) = ‖yE‖ ^ 2 := hy.symm
    _ ≤ (C * ‖zE‖) ^ 2 := by
      nlinarith [norm_nonneg yE, mul_nonneg hC (norm_nonneg zE)]
    _ = C ^ 2 * coordinateEnergy z := by rw [mul_pow, hz]

set_option maxHeartbeats 1000000 in
theorem ghat_gradeProjection_normSq_le
    (F : Frame n d) (nu : ℕ) (hnu : 1 ≤ nu)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
        (Matrix.mulVec
          (ghat (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu) x) ≤
      ((d : ℝ) + (nu : ℝ) - 1) ^ 2 * FiniteHilbert.normSq x := by
  classical
  let C : ℝ := (d : ℝ) + (nu : ℝ) - 1
  have hnuR : (1 : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hnu
  have hC : 0 ≤ C := by
    dsimp [C]
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  rw [normSq_eq_sum_blockFiber, normSq_eq_sum_blockFiber]
  calc
    (∑ q : FockBlockKey m n,
      coordinateEnergy
        (blockFiber
          (Matrix.mulVec
            (ghat (m := m) F *
              gradeProjection (d := d) (m := m) (n := n) nu) x) q)) =
        ∑ q : FockBlockKey m n,
          if blockGrade q = nu then
            coordinateEnergy
              (Matrix.mulVec (ghatBlock F q.1 q.2.1) (blockFiber x q))
          else 0 := by
            apply Finset.sum_congr rfl
            intro q _hq
            rw [blockFiber_ghat_gradeProjection_mulVec]
            by_cases hg : blockGrade q = nu <;>
              simp [hg, coordinateEnergy]
    _ ≤ ∑ q : FockBlockKey m n, C ^ 2 * coordinateEnergy (blockFiber x q) := by
      apply Finset.sum_le_sum
      intro q _hq
      by_cases hg : blockGrade q = nu
      · rw [if_pos hg]
        by_cases hell : q.2.1 = 0
        · have hzero : ghatBlock F q.1 q.2.1 = 0 := by
            rw [hell]
            exact ghatBlock_zero_light F q.1
          rw [hzero]
          have hnonneg := mul_nonneg (sq_nonneg C)
            (coordinateEnergy_nonneg (blockFiber x q))
          simpa [coordinateEnergy] using hnonneg
        · have hellPos : 1 ≤ q.2.1 := Nat.one_le_iff_ne_zero.mpr hell
          have hellLe : q.2.1 ≤ nu := by
            dsimp [blockGrade] at hg
            omega
          exact coordinateEnergy_mulVec_le_of_norm_le
            (ghatBlock F q.1 q.2.1) (blockFiber x q) C hC
            (by
              simpa [C] using
                ghatBlock_norm_le_grade F q.1 q.2.1 nu hellPos hellLe)
      · rw [if_neg hg]
        exact mul_nonneg (sq_nonneg C) (coordinateEnergy_nonneg (blockFiber x q))
    _ = C ^ 2 * ∑ q : FockBlockKey m n, coordinateEnergy (blockFiber x q) := by
      rw [Finset.mul_sum]
    _ = ((d : ℝ) + (nu : ℝ) - 1) ^ 2 *
        ∑ q : FockBlockKey m n, coordinateEnergy (blockFiber x q) := rfl

/-- Sharp positive-grade Euclidean operator bound on the actual Pattern/Fock
operator. -/
theorem ghat_gradeProjection_norm_le
    (F : Frame n d) (nu : ℕ) (hnu : 1 ≤ nu) :
    ‖ghat (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (d : ℝ) + (nu : ℝ) - 1 := by
  have hnuR : (1 : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hnu
  have hC : 0 ≤ (d : ℝ) + (nu : ℝ) - 1 := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  exact FiniteHilbert.norm_le_of_normSq_mulVec_le hC
    (ghat_gradeProjection_normSq_le F nu hnu)

theorem ghat_apply_eq_zero_of_input_light_card_zero
    (F : Frame n d) (out inp : Fin d × Pattern m n)
    (hzero : inp.2.light.card = 0) :
    ghat (m := m) F out inp = 0 := by
  classical
  rw [ghat_apply]
  apply Finset.sum_eq_zero
  intro r _hr
  apply Finset.sum_eq_zero
  intro i _hi
  apply Finset.sum_eq_zero
  intro j _hj
  rw [pDagAt_mul_pAt_apply]
  have hnot : ¬(inp.2 (r, j) = .one ∧
      ((r, i) = (r, j) ∨ inp.2 (r, i) = .zero) ∧
      out.2 = lightMove inp.2 (r, j) (r, i)) := by
    intro hlegal
    have hmem : (r, j) ∈ inp.2.light := Pattern.mem_light.mpr hlegal.1
    have hpos : 0 < inp.2.light.card := Finset.card_pos.mpr ⟨(r, j), hmem⟩
    omega
  rw [if_neg hnot]
  ring

theorem ghat_apply_eq_zero_of_grade_ne
    (F : Frame n d) (out inp : Fin d × Pattern m n)
    (hne : out.2.grade ≠ inp.2.grade) :
    ghat (m := m) F out inp = 0 := by
  apply ghat_apply_eq_zero_of_block_ne
  by_contra hblock
  simp only [not_or, not_ne_iff] at hblock
  apply hne
  rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy,
    Pattern.grade_eq_card_light_add_two_mul_card_heavy,
    hblock.1, hblock.2]

theorem gradeProjection_mul_ghat_apply
    (F : Frame n d) (nu : ℕ)
    (out inp : Fin d × Pattern m n) :
    (gradeProjection (d := d) (m := m) (n := n) nu *
      ghat (m := m) F) out inp =
      if out.2.grade = nu then ghat F out inp else 0 := by
  classical
  rw [gradeProjection, Matrix.diagonal_mul]
  by_cases h : out.2.grade = nu <;> simp [h]

/-- `G-hat` preserves every exact total grade, so it commutes with the actual
orthogonal grade projection. -/
theorem gradeProjection_mul_ghat_eq_ghat_mul_gradeProjection
    (F : Frame n d) (nu : ℕ) :
    gradeProjection (d := d) (m := m) (n := n) nu * ghat F =
      ghat F * gradeProjection nu := by
  ext out inp
  rw [gradeProjection_mul_ghat_apply, ghat_mul_gradeProjection_apply]
  by_cases hout : out.2.grade = nu
  · by_cases hinp : inp.2.grade = nu
    · simp [hout, hinp]
    · have hne : out.2.grade ≠ inp.2.grade := by
        intro h
        exact hinp (h.symm.trans hout)
      simp [hout, hinp, ghat_apply_eq_zero_of_grade_ne F out inp hne]
  · by_cases hinp : inp.2.grade = nu
    · have hne : out.2.grade ≠ inp.2.grade := by
        intro h
        exact hout (h.trans hinp)
      simp [hout, hinp, ghat_apply_eq_zero_of_grade_ne F out inp hne]
    · simp [hout, hinp]

@[simp] theorem ghat_gradeProjection_transpose
    (F : Frame n d) (nu : ℕ) :
    (ghat (m := m) F *
      gradeProjection (d := d) (m := m) (n := n) nu).transpose =
      ghat F * gradeProjection nu := by
  rw [Matrix.transpose_mul, gradeProjection_transpose, ghat_transpose,
    gradeProjection_mul_ghat_eq_ghat_mul_gradeProjection]

theorem ghat_gradeProjection_isHermitian
    (F : Frame n d) (nu : ℕ) :
    (ghat (m := m) F *
      gradeProjection (d := d) (m := m) (n := n) nu).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact ghat_gradeProjection_transpose F nu

/-- The exact grade-zero restriction vanishes: `G-hat` always annihilates one
light site before recreating one. -/
theorem ghat_gradeProjection_zero
    (F : Frame n d) :
    ghat (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  ext out inp
  rw [ghat_mul_gradeProjection_apply]
  by_cases hg : inp.2.grade = 0
  · rw [if_pos hg]
    apply ghat_apply_eq_zero_of_input_light_card_zero
    rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy] at hg
    omega
  · simp [hg]

/-- All-grade envelope used by downstream C-stack estimates. -/
theorem ghat_gradeProjection_norm_le_all
    (F : Frame n d) (nu : ℕ) :
    ‖ghat (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (d : ℝ) + (nu : ℝ) := by
  by_cases hnu : nu = 0
  · subst nu
    rw [ghat_gradeProjection_zero]
    simp
  · have hnuPos : 1 ≤ nu := Nat.one_le_iff_ne_zero.mpr hnu
    calc
      ‖ghat (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
          (d : ℝ) + (nu : ℝ) - 1 :=
        ghat_gradeProjection_norm_le F nu hnuPos
      _ ≤ (d : ℝ) + (nu : ℝ) := by linarith

@[simp] theorem ghatBlock_transpose
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (ghatBlock F T ell).transpose = ghatBlock F T ell := by
  ext out inp
  have h := congrFun (congrFun (ghat_transpose (m := m) F)
    (out.1, out.2.1)) (inp.1, inp.2.1)
  simpa [ghatBlock, Matrix.transpose_apply] using h

theorem ghatBlock_isHermitian
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (ghatBlock F T ell).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact ghatBlock_transpose F T ell

/-! ## The zero-light block -/

/-- Literal coordinate support in one fixed-heavy/fixed-light block. -/
def SupportedOnBlock (T : Finset (Site m n)) (ell : ℕ)
    (x : Fin d × Pattern m n → ℝ) : Prop :=
  ∀ a, ¬ InBlock T ell a.2 → x a = 0

theorem pAt_ne_zero_input_one (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) (h : pAt r i out inp ≠ 0) :
    inp (r, i) = .one := by
  classical
  simp only [pAt, siteKernel] at h
  by_cases hoff : agreesOutsideSite (r, i) out inp
  · simp only [hoff, if_pos, pDestroy, ketBra] at h
    by_contra hne
    simp [hne] at h
  · simp [hoff] at h

theorem no_light_site_of_block_zero {T : Finset (Site m n)}
    {p : Pattern m n} (hp : InBlock T 0 p) (s : Site m n) :
    p s ≠ .one := by
  intro hs
  have hempty : p.light = ∅ := Finset.card_eq_zero.mp hp.2
  have : s ∈ p.light := by simp [hs]
  simpa [hempty] using this

/-- Every annihilation map kills a vector supported on a zero-light block. -/
theorem Ctranspose_mulVec_eq_zero_of_zeroLight
    (F : Frame n d) (T : Finset (Site m n))
    (x : Fin d × Pattern m n → ℝ) (hx : SupportedOnBlock T 0 x)
    (r : Fin m) :
    (CMatrix F r).transpose.mulVec x = 0 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, CMatrix_transpose_apply,
    Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro out _hout
  by_cases hb : InBlock T 0 out.2
  · apply mul_eq_zero.mpr
    left
    apply Finset.sum_eq_zero
    intro i _hi
    apply mul_eq_zero.mpr
    right
    by_contra hne
    exact no_light_site_of_block_zero hb (r, i)
      (pAt_ne_zero_input_one r i p out.2 hne)
  · rw [hx out hb, mul_zero]

/-- The concrete `G-hat` quadratic form is identically zero on the block with
no light sites, including all same-site terms. -/
theorem ghat_mulVec_eq_zero_of_zeroLight
    (F : Frame n d) (T : Finset (Site m n))
    (x : Fin d × Pattern m n → ℝ) (hx : SupportedOnBlock T 0 x) :
    (ghat (m := m) F).mulVec x = 0 := by
  rw [ghat, Matrix.sum_mulVec]
  funext out
  simp only [Finset.sum_apply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro r _hr
  rw [← Matrix.mulVec_mulVec]
  rw [Ctranspose_mulVec_eq_zero_of_zeroLight F T x hx r]
  simp

theorem ghat_quadratic_eq_zero_of_zeroLight
    (F : Frame n d) (T : Finset (Site m n))
    (x : Fin d × Pattern m n → ℝ) (hx : SupportedOnBlock T 0 x) :
    quadratic (ghat (m := m) F) x = 0 := by
  rw [quadratic, ghat_mulVec_eq_zero_of_zeroLight F T x hx]
  simp

end

end SparseFock.LightSectorConcrete
