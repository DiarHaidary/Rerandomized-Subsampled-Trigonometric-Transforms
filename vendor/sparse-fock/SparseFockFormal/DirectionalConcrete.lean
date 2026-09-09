import SparseFockFormal.NamedBands
import SparseFockFormal.FiniteHilbert
import SparseFockFormal.DirectionalBounds
import SparseFockFormal.ParsevalFrame
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Concrete directional row-local estimates

This file realizes the three marked-pattern arguments from the paper on the
literal finite pattern basis.  All sums are over finite types and the norm is
the Euclidean L2 operator norm from `FiniteHilbert`.
-/

namespace SparseFock

namespace DirectionalConcrete

open ParsevalFrame LocalOperator BandInventory FiniteOperator ExternalOperator
  GlobalBands NamedBands FiniteHilbert
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Forget only the Euclidean wrapper on the vectors of a Parseval frame. -/
def frameRows (F : Frame n d) : Fin n → Fin d → ℝ :=
  fun i k ↦ F.u i k

@[simp] theorem frameRows_apply (F : Frame n d) (i : Fin n) (k : Fin d) :
    frameRows F i k = F.u i k := rfl

/-- Update two distinct sites of a pattern.  The second update is written
last; all uses below prove the sites distinct. -/
def setPair (p : Pattern m n) (s : Site m n) (a : Level)
    (t : Site m n) (b : Level) : Pattern m n :=
  Function.update (Function.update p s a) t b

@[simp] theorem setPair_apply_left (p : Pattern m n) {s t : Site m n}
    (hst : s ≠ t) (a b : Level) :
    setPair p s a t b s = a := by
  simp [setPair, hst]

@[simp] theorem setPair_apply_right (p : Pattern m n) (s t : Site m n)
    (a b : Level) :
    setPair p s a t b t = b := by
  simp [setPair]

theorem setPair_apply_of_ne (p : Pattern m n) {s t x : Site m n}
    (hxs : x ≠ s) (hxt : x ≠ t) (a b : Level) :
    setPair p s a t b x = p x := by
  simp [setPair, hxs, hxt]

theorem agreesOutsidePair_setPair (p : Pattern m n) (s t : Site m n)
    (a b : Level) :
    agreesOutsidePair s t p (setPair p s a t b) := by
  intro x hxs hxt
  symm
  exact setPair_apply_of_ne p hxs hxt a b

/-- Outside-pair agreement plus the two local values determines the input
pattern uniquely. -/
theorem eq_setPair_iff {out inp : Pattern m n} {s t : Site m n}
    (hst : s ≠ t) (a b : Level) :
    inp = setPair out s a t b ↔
      agreesOutsidePair s t out inp ∧ inp s = a ∧ inp t = b := by
  constructor
  · rintro rfl
    exact ⟨agreesOutsidePair_setPair out s t a b,
      setPair_apply_left out hst a b, setPair_apply_right out s t a b⟩
  · rintro ⟨hout, hs, ht⟩
    funext x
    by_cases hxs : x = s
    · subst x
      simpa [setPair_apply_left out hst a b] using hs
    · by_cases hxt : x = t
      · subst x
        simpa using ht
      · rw [setPair_apply_of_ne out hxs hxt]
        exact (hout x hxs hxt).symm

/-- Exact matrix entry of a lifted pair of local rank-one transitions. -/
theorem pairKernel_ketBra_apply {s t : Site m n} (hst : s ≠ t)
    (os is ot it : Level) (out inp : Pattern m n) :
    pairKernel s t (ketBra os is) (ketBra ot it) out inp =
      if out s = os ∧ out t = ot ∧ inp = setPair out s is t it then 1 else 0 := by
  classical
  simp only [pairKernel, ketBra]
  by_cases hoff : agreesOutsidePair s t out inp
  · rw [if_pos hoff]
    by_cases hos : out s = os
    · by_cases hot : out t = ot
      · simp only [hos, hot, true_and]
        have heqiff : inp = setPair out s is t it ↔ inp s = is ∧ inp t = it := by
          rw [eq_setPair_iff hst]
          simp [hoff]
        by_cases his : inp s = is
        · by_cases hit : inp t = it
          · have heq := heqiff.mpr ⟨his, hit⟩
            rw [if_pos his, if_pos hit, if_pos heq]
            norm_num
          · have hne : inp ≠ setPair out s is t it := by
              intro heq
              exact hit (heqiff.mp heq).2
            simp [his, hit, hne]
        · have hne : inp ≠ setPair out s is t it := by
            intro heq
            exact his (heqiff.mp heq).1
          simp [his, hne]
      · simp [hos, hot]
    · simp [hos]
  · rw [if_neg hoff]
    have hne : inp ≠ setPair out s is t it := by
      intro h
      apply hoff
      rw [h]
      exact agreesOutsidePair_setPair out s t is it
    simp [hne]

/-- The transpose light hop `H'` from the paper. -/
def Hprime (m : ℕ) (u : Fin n → Fin d → ℝ) : FullOp d m n :=
  wordSum m u .pDown .pUp

/-- Swapping both ordered indices does not change a sum over `i ≠ j`. -/
theorem sum_ordered_swap {A : Type*} [AddCommMonoid A]
    (f : Fin n → Fin n → A) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f j i) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  classical
  have expand (g : Fin n → Fin n → A) :
      (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) =
        ∑ i, ∑ j, if j ≠ i then g i j else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  rw [expand (fun i j ↦ f j i), expand f, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [hij, Ne.symm]

/-- Transposition of a physical word sum is its ordered adjoint word sum. -/
theorem transpose_physicalWordSum (u : Fin n → Fin d → ℝ) (w : Word) :
    (physicalWordSum m u w).transpose =
      physicalWordSum m u w.orderedAdjoint := by
  classical
  ext out inp
  simp only [Matrix.transpose_apply, physicalWordSum, Matrix.sum_apply]
  have hterm (r : Fin m) (i j : Fin n) :
      orderedWordTerm u r i j w inp out =
        orderedWordTerm u r j i w.orderedAdjoint out inp := by
    have h := congrArg
      (fun M : FullOp d m n ↦ M out inp)
      (transpose_orderedWordTerm u r i j w)
    simpa [Matrix.transpose_apply] using h
  simp_rw [hterm]
  apply Finset.sum_congr rfl
  intro r _
  exact sum_ordered_swap
    (fun i j ↦ orderedWordTerm u r i j w.orderedAdjoint out inp)

/-- Ordered-index relabeling makes the transpose light hop symmetric. -/
theorem Hprime_transpose (u : Fin n → Fin d → ℝ) :
    (Hprime m u).transpose = Hprime m u := by
  rw [Hprime, wordSum, transpose_physicalWordSum]
  rfl

theorem yPlus_wordKernel_apply {r : Fin m} {i j : Fin n} (hij : i ≠ j)
    (out inp : Pattern m n) :
    wordKernel (r, i) (r, j) (.rUp, .pUp) out inp =
      if out (r, i) = .two ∧ out (r, j) = .one ∧
          inp = setPair out (r, i) .one (r, j) .zero then 1 else 0 := by
  have hsite : (r, i) ≠ (r, j) := by
    intro h
    exact hij (congrArg Prod.snd h)
  simpa [wordKernel, Leg.op, rPromote, pCreate] using
    pairKernel_ketBra_apply hsite .two .one .one .zero out inp

theorem yZero_wordKernel_apply {r : Fin m} {i j : Fin n} (hij : i ≠ j)
    (out inp : Pattern m n) :
    wordKernel (r, i) (r, j) (.rDown, .pUp) out inp =
      if out (r, i) = .one ∧ out (r, j) = .one ∧
          inp = setPair out (r, i) .two (r, j) .zero then 1 else 0 := by
  have hsite : (r, i) ≠ (r, j) := by
    intro h
    exact hij (congrArg Prod.snd h)
  simpa [wordKernel, Leg.op, rDemote, pCreate] using
    pairKernel_ketBra_apply hsite .one .two .one .zero out inp

theorem hprime_wordKernel_apply {r : Fin m} {i j : Fin n} (hij : i ≠ j)
    (out inp : Pattern m n) :
    wordKernel (r, i) (r, j) (.pDown, .pUp) out inp =
      if out (r, i) = .zero ∧ out (r, j) = .one ∧
          inp = setPair out (r, i) .one (r, j) .zero then 1 else 0 := by
  have hsite : (r, i) ≠ (r, j) := by
    intro h
    exact hij (congrArg Prod.snd h)
  simpa [wordKernel, Leg.op, pDestroy, pCreate] using
    pairKernel_ketBra_apply hsite .zero .one .one .zero out inp

/-- One ordered `Y₊` word has exactly the marked-pattern coefficient claimed
in the paper. -/
theorem orderedYplus_mulVec (u : Fin n → Fin d → ℝ)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (orderedWordTerm u r i j (.rUp, .pUp)) x (k, σ) =
      if σ (r, i) = .two ∧ σ (r, j) = .one then
        ∑ l, u i k * u j l *
          x (l, setPair σ (r, i) .one (r, j) .zero)
      else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [orderedWordTerm, externalTensor, ExternalOperator.outer]
  simp_rw [yPlus_wordKernel_apply hij]
  by_cases hout : σ (r, i) = .two ∧ σ (r, j) = .one
  · simp [hout]
  · have hz (τ : Pattern m n) :
        ¬(σ (r, i) = .two ∧ σ (r, j) = .one ∧
          τ = setPair σ (r, i) .one (r, j) .zero) := by
      intro h
      exact hout ⟨h.1, h.2.1⟩
    simp [hz, hout]

/-- One ordered `Y₀` word has exactly its marked-pattern coefficient. -/
theorem orderedYzero_mulVec (u : Fin n → Fin d → ℝ)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (orderedWordTerm u r i j (.rDown, .pUp)) x (k, σ) =
      if σ (r, i) = .one ∧ σ (r, j) = .one then
        ∑ l, u i k * u j l *
          x (l, setPair σ (r, i) .two (r, j) .zero)
      else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [orderedWordTerm, externalTensor, ExternalOperator.outer]
  simp_rw [yZero_wordKernel_apply hij]
  by_cases hout : σ (r, i) = .one ∧ σ (r, j) = .one
  · simp [hout]
  · have hz (τ : Pattern m n) :
        ¬(σ (r, i) = .one ∧ σ (r, j) = .one ∧
          τ = setPair σ (r, i) .two (r, j) .zero) := by
      intro h
      exact hout ⟨h.1, h.2.1⟩
    simp [hz, hout]

/-- One ordered transpose-light-hop word has exactly its marked coefficient. -/
theorem orderedHprime_mulVec (u : Fin n → Fin d → ℝ)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (orderedWordTerm u r i j (.pDown, .pUp)) x (k, σ) =
      if σ (r, i) = .zero ∧ σ (r, j) = .one then
        ∑ l, u i k * u j l *
          x (l, setPair σ (r, i) .one (r, j) .zero)
      else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [orderedWordTerm, externalTensor, ExternalOperator.outer]
  simp_rw [hprime_wordKernel_apply hij]
  by_cases hout : σ (r, i) = .zero ∧ σ (r, j) = .one
  · simp [hout]
  · have hz (τ : Pattern m n) :
        ¬(σ (r, i) = .zero ∧ σ (r, j) = .one ∧
          τ = setPair σ (r, i) .one (r, j) .zero) := by
      intro h
      exact hout ⟨h.1, h.2.1⟩
    simp [hz, hout]

/-- Ordered distinct pairs whose two output levels are different are exactly
the product of the two corresponding row-local occupation sets. -/
theorem sum_distinct_level_pairs (σ : Pattern m n) (r : Fin m)
    {a b : Level} (hab : a ≠ b) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        if σ (r, i) = a ∧ σ (r, j) = b then f i j else 0) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ σ (r, i) = a),
        ∑ j ∈ Finset.univ.filter (fun j ↦ σ (r, j) = b), f i j := by
  classical
  have hexpand (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = a ∧ σ (r, j) = b then f i j else 0) =
        ∑ j, if j ≠ i then
          (if σ (r, i) = a ∧ σ (r, j) = b then f i j else 0) else 0 := by
    rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  rw [show (∑ i ∈ Finset.univ.filter (fun i ↦ σ (r, i) = a),
        ∑ j ∈ Finset.univ.filter (fun j ↦ σ (r, j) = b), f i j) =
      ∑ i, if σ (r, i) = a then
        (∑ j, if σ (r, j) = b then f i j else 0) else 0 by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [Finset.sum_filter]]
  simp_rw [hexpand]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ (r, i) = a
  · simp only [hi, true_and, if_true]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : σ (r, j) = b
    · have hji : j ≠ i := by
        intro h
        subst j
        exact hab (hi.symm.trans hj)
      simp [hj, hji]
    · simp [hj]
  · simp [hi]

/-- When both local levels are the same, the ordered-pair restriction is the
erase of the marked source from the same row-local set. -/
theorem sum_same_level_pairs (σ : Pattern m n) (r : Fin m)
    (a : Level) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        if σ (r, i) = a ∧ σ (r, j) = a then f i j else 0) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ σ (r, i) = a),
        ∑ j ∈ (Finset.univ.filter (fun j ↦ σ (r, j) = a)).erase i, f i j := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ (r, i) = a
  · simp only [hi, true_and, if_true]
    rw [← Finset.filter_erase, Finset.sum_filter]
  · simp [hi]

/-- Exact coefficient formula for the concrete named `Y₊` matrix. -/
theorem Yplus_mulVec_coeff (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yplus m (frameRows F)) x (k, σ) =
      ∑ r, ∑ a ∈ σ.heavyInRow r, ∑ c ∈ σ.lightInRow r,
        ∑ l, F.u a k * F.u c l *
          x (l, setPair σ (r, a) .one (r, c) .zero) := by
  classical
  simp only [Yplus, wordSum, physicalWordSum, Matrix.sum_mulVec,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        Matrix.mulVec (orderedWordTerm (frameRows F) r i j (.rUp, .pUp)) x (k, σ)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = .two ∧ σ (r, j) = .one then
            ∑ l, F.u i k * F.u j l *
              x (l, setPair σ (r, i) .one (r, j) .zero)
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact orderedYplus_mulVec (frameRows F) x r
        (Ne.symm (Finset.mem_erase.mp hj).1) k σ
    _ = ∑ a ∈ σ.heavyInRow r, ∑ c ∈ σ.lightInRow r,
          ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero) := by
      simpa only [Pattern.heavyInRow, Pattern.lightInRow] using
        sum_distinct_level_pairs σ r (a := .two) (b := .one) (by decide)
          (fun a c ↦ ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero))

/-- Exact coefficient formula for the concrete named `Y₀` matrix. -/
theorem Yzero_mulVec_coeff (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yzero m (frameRows F)) x (k, σ) =
      ∑ r, ∑ a ∈ σ.lightInRow r,
        ∑ c ∈ (σ.lightInRow r).erase a,
          ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .two (r, c) .zero) := by
  classical
  simp only [Yzero, wordSum, physicalWordSum, Matrix.sum_mulVec,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        Matrix.mulVec (orderedWordTerm (frameRows F) r i j (.rDown, .pUp)) x (k, σ)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = .one ∧ σ (r, j) = .one then
            ∑ l, F.u i k * F.u j l *
              x (l, setPair σ (r, i) .two (r, j) .zero)
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact orderedYzero_mulVec (frameRows F) x r
        (Ne.symm (Finset.mem_erase.mp hj).1) k σ
    _ = ∑ a ∈ σ.lightInRow r,
          ∑ c ∈ (σ.lightInRow r).erase a,
            ∑ l, F.u a k * F.u c l *
              x (l, setPair σ (r, a) .two (r, c) .zero) := by
      simpa only [Pattern.lightInRow] using
        sum_same_level_pairs σ r .one
          (fun a c ↦ ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .two (r, c) .zero))

/-- Exact coefficient formula for the transpose light hop `H'`. -/
theorem Hprime_mulVec_coeff (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Hprime m (frameRows F)) x (k, σ) =
      ∑ r, ∑ a ∈ σ.freshInRow r, ∑ c ∈ σ.lightInRow r,
        ∑ l, F.u a k * F.u c l *
          x (l, setPair σ (r, a) .one (r, c) .zero) := by
  classical
  simp only [Hprime, wordSum, physicalWordSum, Matrix.sum_mulVec,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        Matrix.mulVec (orderedWordTerm (frameRows F) r i j (.pDown, .pUp)) x (k, σ)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = .zero ∧ σ (r, j) = .one then
            ∑ l, F.u i k * F.u j l *
              x (l, setPair σ (r, i) .one (r, j) .zero)
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact orderedHprime_mulVec (frameRows F) x r
        (Ne.symm (Finset.mem_erase.mp hj).1) k σ
    _ = ∑ a ∈ σ.freshInRow r, ∑ c ∈ σ.lightInRow r,
          ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero) := by
      simpa only [Pattern.freshInRow, Pattern.lightInRow] using
        sum_distinct_level_pairs σ r (a := .zero) (b := .one) (by decide)
          (fun a c ↦ ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero))

/-- External coefficient vector attached to one pattern. -/
def fiber (x : Fin d × Pattern m n → ℝ) (τ : Pattern m n) : EVec d :=
  WithLp.toLp 2 (fun k ↦ x (k, τ))

@[simp] theorem fiber_apply (x : Fin d × Pattern m n → ℝ)
    (τ : Pattern m n) (k : Fin d) : fiber x τ k = x (k, τ) := rfl

/-- The scalar `u_cᵀ x_τ`. -/
def contract (F : Frame n d) (c : Fin n)
    (x : Fin d × Pattern m n → ℝ) (τ : Pattern m n) : ℝ :=
  ∑ l, F.u c l * x (l, τ)

theorem contract_eq_analyze (F : Frame n d) (c : Fin n)
    (x : Fin d × Pattern m n → ℝ) (τ : Pattern m n) :
    contract F c x τ = analyze F (fiber x τ) c := by
  simp only [contract, analyze, PiLp.inner_apply, Real.inner_apply, fiber_apply]

/-- The marked output vector `z⁺_{σ,r,c}`. -/
def yPlusMarked (F : Frame n d) (x : Fin d × Pattern m n → ℝ)
    (σ : Pattern m n) (r : Fin m) (c : Fin n) : EVec d :=
  synthesize F (σ.heavyInRow r) (fun a ↦
    contract F c x (setPair σ (r, a) .one (r, c) .zero))

/-- The marked output vector `z⁰_{σ,r,c}`. -/
def yZeroMarked (F : Frame n d) (x : Fin d × Pattern m n → ℝ)
    (σ : Pattern m n) (r : Fin m) (c : Fin n) : EVec d :=
  synthesize F ((σ.lightInRow r).erase c) (fun a ↦
    contract F c x (setPair σ (r, a) .two (r, c) .zero))

/-- The marked output vector `z'_{σ,r,c}`. -/
def hprimeMarked (F : Frame n d) (x : Fin d × Pattern m n → ℝ)
    (σ : Pattern m n) (r : Fin m) (c : Fin n) : EVec d :=
  synthesize F (σ.freshInRow r) (fun a ↦
    contract F c x (setPair σ (r, a) .one (r, c) .zero))

@[simp] theorem yPlusMarked_apply (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) (k : Fin d) :
    yPlusMarked F x σ r c k =
      ∑ a ∈ σ.heavyInRow r, F.u a k *
        contract F c x (setPair σ (r, a) .one (r, c) .zero) := by
  simp [yPlusMarked, synthesize, mul_comm]

@[simp] theorem yZeroMarked_apply (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) (k : Fin d) :
    yZeroMarked F x σ r c k =
      ∑ a ∈ (σ.lightInRow r).erase c, F.u a k *
        contract F c x (setPair σ (r, a) .two (r, c) .zero) := by
  simp [yZeroMarked, synthesize, mul_comm]

@[simp] theorem hprimeMarked_apply (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) (k : Fin d) :
    hprimeMarked F x σ r c k =
      ∑ a ∈ σ.freshInRow r, F.u a k *
        contract F c x (setPair σ (r, a) .one (r, c) .zero) := by
  simp [hprimeMarked, synthesize, mul_comm]

/-- Reversing the two marked indices in an ordered sum over a single finite
set preserves multiplicity exactly. -/
theorem sum_erase_comm {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → α → ℝ) :
    (∑ a ∈ s, ∑ c ∈ s.erase a, f a c) =
      ∑ c ∈ s, ∑ a ∈ s.erase c, f a c := by
  classical
  have hexpand (g : α → α → ℝ) :
      (∑ a ∈ s, ∑ c ∈ s.erase a, g a c) =
        ∑ a ∈ s, ∑ c ∈ s, if c ≠ a then g a c else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.filter_ne' s a, Finset.sum_filter]
  rw [hexpand f, hexpand (fun c a ↦ f a c)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  by_cases h : c = a <;> simp [h, Ne.symm]

/-- Paper equation `(Yplus-coeff)` on the actual finite pattern basis. -/
theorem Yplus_mulVec_marked (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yplus m (frameRows F)) x (k, σ) =
      ∑ r, ∑ c ∈ σ.lightInRow r, yPlusMarked F x σ r c k := by
  rw [Yplus_mulVec_coeff]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [yPlusMarked_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [contract]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Paper equation `(Yzero-coeff)` on the actual finite pattern basis. -/
theorem Yzero_mulVec_marked (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yzero m (frameRows F)) x (k, σ) =
      ∑ r, ∑ c ∈ σ.lightInRow r, yZeroMarked F x σ r c k := by
  rw [Yzero_mulVec_coeff]
  apply Finset.sum_congr rfl
  intro r _
  rw [sum_erase_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [yZeroMarked_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [contract]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Paper equation `(Hprime-coeff)` on the actual finite pattern basis. -/
theorem Hprime_mulVec_marked (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Hprime m (frameRows F)) x (k, σ) =
      ∑ r, ∑ c ∈ σ.lightInRow r, hprimeMarked F x σ r c k := by
  rw [Hprime_mulVec_coeff]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hprimeMarked_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [contract]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem yPlusMarked_normSq_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) :
    ParsevalFrame.normSq (yPlusMarked F x σ r c) ≤
      ∑ a ∈ σ.heavyInRow r,
        (contract F c x (setPair σ (r, a) .one (r, c) .zero)) ^ 2 := by
  calc
    ParsevalFrame.normSq (yPlusMarked F x σ r c) ≤
        ∑ a ∈ σ.heavyInRow r,
          |contract F c x (setPair σ (r, a) .one (r, c) .zero)| ^ 2 := by
      exact subset_synthesis F (σ.heavyInRow r)
        (fun a ↦ contract F c x (setPair σ (r, a) .one (r, c) .zero))
    _ = _ := by simp only [sq_abs]

theorem yZeroMarked_normSq_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) :
    ParsevalFrame.normSq (yZeroMarked F x σ r c) ≤
      ∑ a ∈ (σ.lightInRow r).erase c,
        (contract F c x (setPair σ (r, a) .two (r, c) .zero)) ^ 2 := by
  calc
    ParsevalFrame.normSq (yZeroMarked F x σ r c) ≤
        ∑ a ∈ (σ.lightInRow r).erase c,
          |contract F c x (setPair σ (r, a) .two (r, c) .zero)| ^ 2 := by
      exact subset_synthesis F ((σ.lightInRow r).erase c)
        (fun a ↦ contract F c x (setPair σ (r, a) .two (r, c) .zero))
    _ = _ := by simp only [sq_abs]

theorem hprimeMarked_normSq_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) :
    ParsevalFrame.normSq (hprimeMarked F x σ r c) ≤
      ∑ a ∈ σ.freshInRow r,
        (contract F c x (setPair σ (r, a) .one (r, c) .zero)) ^ 2 := by
  calc
    ParsevalFrame.normSq (hprimeMarked F x σ r c) ≤
        ∑ a ∈ σ.freshInRow r,
          |contract F c x (setPair σ (r, a) .one (r, c) .zero)| ^ 2 := by
      exact subset_synthesis F (σ.freshInRow r)
        (fun a ↦ contract F c x (setPair σ (r, a) .one (r, c) .zero))
    _ = _ := by simp only [sq_abs]

/-- The nested row/light sum is exactly a sum over the global light-site set. -/
theorem sum_rows_light_eq_sum_light (σ : Pattern m n)
    {A : Type*} [AddCommMonoid A] (f : Site m n → A) :
    (∑ r, ∑ c ∈ σ.lightInRow r, f (r, c)) =
      ∑ s ∈ σ.light, f s := by
  classical
  simp only [Pattern.lightInRow, Pattern.light, Finset.sum_filter]
  rw [Fintype.sum_prod_type]

/-- Finite-family Cauchy--Schwarz in the exact Euclidean coordinate model. -/
theorem normSq_sum_le_card {α : Type*} [DecidableEq α]
    (s : Finset α) (z : α → EVec d) :
    ParsevalFrame.normSq (∑ a ∈ s, z a) ≤
      (s.card : ℝ) * ∑ a ∈ s, ParsevalFrame.normSq (z a) := by
  simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply,
    WithLp.ofLp_sum, Finset.sum_apply]
  calc
    (∑ k, (∑ a ∈ s, z a k) * ∑ a ∈ s, z a k) =
        ∑ k, (∑ a ∈ s, z a k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ∑ k, (s.card : ℝ) * ∑ a ∈ s, (z a k) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ a ∈ s, ∑ k, z a k * z a k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The fiber of a full coordinate vector at one Fock pattern. -/
def fullFiber (v : Fin d × Pattern m n → ℝ) (σ : Pattern m n) : EVec d :=
  WithLp.toLp 2 (fun k ↦ v (k, σ))

theorem full_normSq_eq_sum_fiber (v : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq v =
      ∑ σ, ParsevalFrame.normSq (fullFiber v σ) := by
  simp only [FiniteHilbert.normSq, ParsevalFrame.normSq, PiLp.inner_apply,
    Real.inner_apply, fullFiber]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem Yplus_fullFiber (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n) :
    fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) σ =
      ∑ s ∈ σ.light, yPlusMarked F x σ s.1 s.2 := by
  ext k
  rw [show fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) σ k =
      Matrix.mulVec (Yplus m (frameRows F)) x (k, σ) by rfl]
  rw [Yplus_mulVec_marked]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
    sum_rows_light_eq_sum_light σ
      (fun s ↦ yPlusMarked F x σ s.1 s.2 k)

theorem Yzero_fullFiber (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n) :
    fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) σ =
      ∑ s ∈ σ.light, yZeroMarked F x σ s.1 s.2 := by
  ext k
  rw [show fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) σ k =
      Matrix.mulVec (Yzero m (frameRows F)) x (k, σ) by rfl]
  rw [Yzero_mulVec_marked]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
    sum_rows_light_eq_sum_light σ
      (fun s ↦ yZeroMarked F x σ s.1 s.2 k)

theorem Hprime_fullFiber (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n) :
    fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) σ =
      ∑ s ∈ σ.light, hprimeMarked F x σ s.1 s.2 := by
  ext k
  rw [show fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) σ k =
      Matrix.mulVec (Hprime m (frameRows F)) x (k, σ) by rfl]
  rw [Hprime_mulVec_marked]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
    sum_rows_light_eq_sum_light σ
      (fun s ↦ hprimeMarked F x σ s.1 s.2 k)

/-- A pattern with an ordered pair of distinct marked columns in one row and
prescribed local output states. -/
structure RowMark (m n : ℕ) (a b : Level) where
  pattern : Pattern m n
  row : Fin m
  left : Fin n
  right : Fin n
  ne : left ≠ right
  left_state : pattern (row, left) = a
  right_state : pattern (row, right) = b
  deriving DecidableEq, Fintype

/-- The columns in one row carrying a prescribed local state.  This generic
version lets the marked-tuple arguments treat fresh, light, and heavy sites
uniformly. -/
def levelInRow (p : Pattern m n) (r : Fin m) (a : Level) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ p (r, i) = a

@[simp] theorem mem_levelInRow {p : Pattern m n} {r : Fin m}
    {a : Level} {i : Fin n} :
    i ∈ levelInRow p r a ↔ p (r, i) = a := by
  simp [levelInRow]

@[simp] theorem levelInRow_zero (p : Pattern m n) (r : Fin m) :
    levelInRow p r .zero = p.freshInRow r := by
  ext i
  simp [levelInRow, Pattern.freshInRow]

@[simp] theorem levelInRow_one (p : Pattern m n) (r : Fin m) :
    levelInRow p r .one = p.lightInRow r := by
  ext i
  simp [levelInRow, Pattern.lightInRow]

@[simp] theorem levelInRow_two (p : Pattern m n) (r : Fin m) :
    levelInRow p r .two = p.heavyInRow r := by
  ext i
  simp [levelInRow, Pattern.heavyInRow]

/-- Nested sigma-type presentation of the same marked data. -/
abbrev NestedRowMark (m n : ℕ) (a b : Level) :=
  Σ p : Pattern m n, Σ r : Fin m,
    Σ i : {i : Fin n // p (r, i) = a},
      {j : Fin n // j ≠ i.1 ∧ p (r, j) = b}

/-- A `RowMark` is precisely a pattern, row, first state-constrained column,
and a distinct second state-constrained column. -/
def rowMarkNestedEquiv (a b : Level) :
    RowMark m n a b ≃ NestedRowMark m n a b where
  toFun z := ⟨z.pattern, z.row, ⟨z.left, z.left_state⟩,
    ⟨z.right, z.ne.symm, z.right_state⟩⟩
  invFun z :=
    { pattern := z.1
      row := z.2.1
      left := z.2.2.1.1
      right := z.2.2.2.1
      ne := z.2.2.2.2.1.symm
      left_state := z.2.2.1.2
      right_state := z.2.2.2.2.2 }
  left_inv z := by
    cases z
    rfl
  right_inv z := by
    rcases z with ⟨p, r, i, j⟩
    rfl

theorem sum_subtype_eq_filter {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (g : α → ℝ) :
    (∑ x : {x // p x}, g x.1) = ∑ x ∈ Finset.univ.filter p, g x := by
  symm
  exact Finset.sum_subtype (Finset.univ.filter p) (by simp) g

/-- Expands a sum over marked patterns into the paper's row-local nested
sum.  The `erase` is exactly the ordered distinctness condition. -/
theorem sum_rowMark_eq_nested (a b : Level)
    (g : Pattern m n → Fin m → Fin n → Fin n → ℝ) :
    (∑ z : RowMark m n a b, g z.pattern z.row z.left z.right) =
      ∑ p, ∑ r, ∑ i ∈ levelInRow p r a,
        ∑ j ∈ (levelInRow p r b).erase i, g p r i j := by
  rw [Fintype.sum_equiv (rowMarkNestedEquiv (m := m) (n := n) a b)
    (fun z ↦ g z.pattern z.row z.left z.right)
    (fun z ↦ g z.1 z.2.1 z.2.2.1.1 z.2.2.2.1) (by intro z; rfl)]
  simp_rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [sum_subtype_eq_filter]
  rw [sum_subtype_eq_filter (fun i : Fin n ↦ p (r, i) = a)
    (fun i ↦ ∑ j ∈ Finset.univ.filter
      (fun j : Fin n ↦ j ≠ i ∧ p (r, j) = b), g p r i j)]
  change (∑ i ∈ levelInRow p r a,
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin n ↦ j ≠ i ∧ p (r, j) = b), g p r i j) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Finset.univ.filter
      (fun j : Fin n ↦ j ≠ i ∧ p (r, j) = b) =
      (levelInRow p r b).erase i by
    ext j
    simp [levelInRow]]

@[ext]
theorem rowMark_ext {x y : RowMark m n a b}
    (hpattern : x.pattern = y.pattern)
    (hrow : x.row = y.row) (hleft : x.left = y.left)
    (hright : x.right = y.right) : x = y := by
  cases x with
  | mk xp xr xl xright xne xleftState xrightState =>
    cases y with
    | mk yp yr yl yright yne yleftState yrightState =>
      dsimp at hpattern hrow hleft hright
      subst yp
      subst yr
      subst yl
      subst yright
      rfl

theorem setPair_restore (p : Pattern m n) {s t : Site m n}
    (hst : s ≠ t) {oa ob ia ib : Level}
    (hs : p s = oa) (ht : p t = ob) :
    setPair (setPair p s ia t ib) s oa t ob = p := by
  funext x
  by_cases hxs : x = s
  · subst x
    simpa [setPair_apply_left _ hst] using hs.symm
  · by_cases hxt : x = t
    · subst x
      simpa using ht.symm
    · rw [setPair_apply_of_ne _ hxs hxt,
        setPair_apply_of_ne _ hxs hxt]

/-- The marked-pattern update is an actual finite equivalence; its inverse
restores the two output states. -/
def rowMarkTransition (oa ob ia ib : Level) :
    RowMark m n oa ob ≃ RowMark m n ia ib where
  toFun z :=
    { pattern := setPair z.pattern (z.row, z.left) ia (z.row, z.right) ib
      row := z.row
      left := z.left
      right := z.right
      ne := z.ne
      left_state := setPair_apply_left z.pattern
        (by intro h; exact z.ne (congrArg Prod.snd h)) ia ib
      right_state := setPair_apply_right z.pattern _ _ ia ib }
  invFun z :=
    { pattern := setPair z.pattern (z.row, z.left) oa (z.row, z.right) ob
      row := z.row
      left := z.left
      right := z.right
      ne := z.ne
      left_state := setPair_apply_left z.pattern
        (by intro h; exact z.ne (congrArg Prod.snd h)) oa ob
      right_state := setPair_apply_right z.pattern _ _ oa ob }
  left_inv z := by
    cases z with
    | mk p r a c hne ha hc =>
      have hp := setPair_restore p
        (by intro h; exact hne (congrArg Prod.snd h))
        (oa := oa) (ob := ob) (ia := ia) (ib := ib) ha hc
      simp only
      apply rowMark_ext
      · exact hp
      · rfl
      · rfl
      · rfl
  right_inv z := by
    cases z with
    | mk p r a c hne ha hc =>
      have hp := setPair_restore p
        (by intro h; exact hne (congrArg Prod.snd h))
        (oa := ia) (ob := ib) (ia := oa) (ib := ob) ha hc
      simp only
      apply rowMark_ext
      · exact hp
      · rfl
      · rfl
      · rfl

/-- Exact multiplicity-one reindexing of any scalar observable along a marked
transition. -/
theorem sum_rowMarkTransition (oa ob ia ib : Level)
    (f : RowMark m n ia ib → ℝ) :
    (∑ z : RowMark m n oa ob, f (rowMarkTransition oa ob ia ib z)) =
      ∑ z : RowMark m n ia ib, f z := by
  exact Equiv.sum_comp (rowMarkTransition oa ob ia ib) f

@[simp] theorem rowMarkTransition_pattern (oa ob ia ib : Level)
    (z : RowMark m n oa ob) :
    (rowMarkTransition oa ob ia ib z).pattern =
      setPair z.pattern (z.row, z.left) ia (z.row, z.right) ib := rfl

@[simp] theorem rowMarkTransition_right (oa ob ia ib : Level)
    (z : RowMark m n oa ob) :
    (rowMarkTransition oa ob ia ib z).right = z.right := rfl

/-- Exact coefficient-square reindexing for `Y₊`; no tuple is dropped or
duplicated. -/
theorem Yplus_marked_reindex (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ z : RowMark m n .two .one,
      (contract F z.right x
        (setPair z.pattern (z.row, z.left) .one
          (z.row, z.right) .zero)) ^ 2) =
      ∑ z : RowMark m n .one .zero,
        (contract F z.right x z.pattern) ^ 2 := by
  simpa only [rowMarkTransition_pattern, rowMarkTransition_right] using
    sum_rowMarkTransition (m := m) (n := n) .two .one .one .zero
      (fun z ↦ (contract F z.right x z.pattern) ^ 2)

/-- Exact coefficient-square reindexing for `Y₀`. -/
theorem Yzero_marked_reindex (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ z : RowMark m n .one .one,
      (contract F z.right x
        (setPair z.pattern (z.row, z.left) .two
          (z.row, z.right) .zero)) ^ 2) =
      ∑ z : RowMark m n .two .zero,
        (contract F z.right x z.pattern) ^ 2 := by
  simpa only [rowMarkTransition_pattern, rowMarkTransition_right] using
    sum_rowMarkTransition (m := m) (n := n) .one .one .two .zero
      (fun z ↦ (contract F z.right x z.pattern) ^ 2)

/-- Exact coefficient-square reindexing for the transpose light hop. -/
theorem Hprime_marked_reindex (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ z : RowMark m n .zero .one,
      (contract F z.right x
        (setPair z.pattern (z.row, z.left) .one
          (z.row, z.right) .zero)) ^ 2) =
      ∑ z : RowMark m n .one .zero,
        (contract F z.right x z.pattern) ^ 2 := by
  simpa only [rowMarkTransition_pattern, rowMarkTransition_right] using
    sum_rowMarkTransition (m := m) (n := n) .zero .one .one .zero
      (fun z ↦ (contract F z.right x z.pattern) ^ 2)

/-- A concrete full coordinate vector is supported on one exact occupation
grade. -/
def SupportedAtGrade (nu : ℕ) (x : Fin d × Pattern m n → ℝ) : Prop :=
  ∀ k p, p.grade ≠ nu → x (k, p) = 0

theorem gradeProjection_supported (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    SupportedAtGrade nu
      (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
  intro k p hp
  rw [gradeProjection_mulVec]
  simp [hp]

theorem fiber_eq_zero_of_not_grade {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    {p : Pattern m n} (hp : p.grade ≠ nu) :
    fiber x p = 0 := by
  ext k
  exact hx k p hp

theorem contract_eq_zero_of_not_grade {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (F : Frame n d) (c : Fin n) {p : Pattern m n}
    (hp : p.grade ≠ nu) :
    contract F c x p = 0 := by
  rw [contract_eq_analyze, fiber_eq_zero_of_not_grade hx hp]
  simp [analyze]

/-- A sum of all ordered realizations of one word has the word's exact grade
shift. -/
theorem physicalWordSum_homogeneous (u : Fin n → Fin d → ℝ) (w : Word) :
    ExternalOperator.Homogeneous w.degree (physicalWordSum m u w) := by
  intro out inp hnonzero
  classical
  simp only [physicalWordSum, Matrix.sum_apply] at hnonzero
  by_contra hgrade
  apply hnonzero
  apply Finset.sum_eq_zero
  intro r _
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  by_contra hterm
  exact hgrade
    (orderedWordTerm_homogeneous u r
      (Ne.symm (Finset.mem_erase.mp hj).1) w hterm)

theorem Yplus_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 2 (Yplus m (frameRows F)) := by
  simpa [Yplus, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.rUp, .pUp)

theorem Yzero_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0 (Yzero m (frameRows F)) := by
  simpa [Yzero, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.rDown, .pUp)

theorem Hprime_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0 (Hprime m (frameRows F)) := by
  simpa [Hprime, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.pDown, .pUp)

/-- Homogeneity plus exact input support makes every incompatible output fiber
identically zero. -/
theorem fullFiber_mulVec_eq_zero_of_grade {delta : ℤ}
    {A : FullOp d m n} (hA : ExternalOperator.Homogeneous delta A)
    {nu : ℕ} {x : Fin d × Pattern m n → ℝ}
    (hx : SupportedAtGrade nu x) (p : Pattern m n)
    (hp : (p.grade : ℤ) ≠ (nu : ℤ) + delta) :
    fullFiber (Matrix.mulVec A x) p = 0 := by
  ext k
  simp only [fullFiber, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro inp _
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : A (k, p) inp = 0
    · simp [hentry]
    · have hrel := homogeneous_grade_relation hA hentry
      exfalso
      apply hp
      simpa [hin] using hrel
  · simp [hx inp.1 inp.2 hin]

/-- Coefficient energy indexed by actual finite marked patterns. -/
def markedEnergy (a b : Level) (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) : ℝ :=
  ∑ z : RowMark m n a b, (contract F z.right x z.pattern) ^ 2

theorem markedEnergy_eq_nested (a b : Level) (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    markedEnergy a b F x =
      ∑ p, ∑ r, ∑ i ∈ levelInRow p r a,
        ∑ j ∈ (levelInRow p r b).erase i,
          (contract F j x p) ^ 2 := by
  exact sum_rowMark_eq_nested a b
    (fun p _ _ j ↦ (contract F j x p) ^ 2)

/-- For a fixed input pattern, fresh-site Parseval is paid once per marked
light site. -/
theorem light_fresh_energy_at_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    (∑ r, ∑ a ∈ p.lightInRow r,
      ∑ c ∈ p.freshInRow r |>.erase a,
        (contract F c x p) ^ 2) ≤
      (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  calc
    (∑ r, ∑ a ∈ p.lightInRow r,
        ∑ c ∈ p.freshInRow r |>.erase a,
          (contract F c x p) ^ 2) ≤
        ∑ r, ∑ a ∈ p.lightInRow r,
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro a _
      simpa only [contract_eq_analyze] using
        subset_analysis F ((p.freshInRow r).erase a) (fiber x p)
    _ = (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      norm_cast
      rw [← Pattern.card_light_eq_sum_card_lightInRow]

/-- For a fixed input pattern, fresh-site Parseval is paid once per marked
heavy site. -/
theorem heavy_fresh_energy_at_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    (∑ r, ∑ a ∈ p.heavyInRow r,
      ∑ c ∈ p.freshInRow r |>.erase a,
        (contract F c x p) ^ 2) ≤
      (p.heavy.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  calc
    (∑ r, ∑ a ∈ p.heavyInRow r,
        ∑ c ∈ p.freshInRow r |>.erase a,
          (contract F c x p) ^ 2) ≤
        ∑ r, ∑ a ∈ p.heavyInRow r,
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro a _
      simpa only [contract_eq_analyze] using
        subset_analysis F ((p.freshInRow r).erase a) (fiber x p)
    _ = (p.heavy.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      norm_cast
      rw [← Pattern.card_heavy_eq_sum_card_heavyInRow]

/-- Fully concrete input-side resummation for light marks. -/
theorem markedEnergy_one_zero_le (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    markedEnergy .one .zero F x ≤
      (nu : ℝ) * FiniteHilbert.normSq x := by
  rw [markedEnergy_eq_nested]
  simp only [levelInRow_one, levelInRow_zero]
  calc
    (∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
        ∑ j ∈ (p.freshInRow r).erase i,
          contract F j x p ^ 2) ≤
        ∑ p, (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.grade = nu
      · calc
          (∑ r, ∑ i ∈ p.lightInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) :=
                light_fresh_energy_at_le F x p
          _ ≤ (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast (hp ▸ p.card_light_le_grade)
            · exact real_inner_self_nonneg
      · have hfiber : fiber x p = 0 := fiber_eq_zero_of_not_grade hx hp
        calc
          (∑ r, ∑ i ∈ p.lightInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) :=
                light_fresh_energy_at_le F x p
          _ = 0 := by simp [hfiber, ParsevalFrame.normSq]
          _ = (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            simp [hfiber, ParsevalFrame.normSq]
    _ = (nu : ℝ) * FiniteHilbert.normSq x := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [fiber, fullFiber] using (full_normSq_eq_sum_fiber x).symm

/-- Fully concrete input-side resummation for heavy marks, with the factor two
kept denominator-free. -/
theorem two_mul_markedEnergy_two_zero_le (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    2 * markedEnergy .two .zero F x ≤
      (nu : ℝ) * FiniteHilbert.normSq x := by
  rw [markedEnergy_eq_nested]
  simp only [levelInRow_two, levelInRow_zero]
  calc
    2 * (∑ p, ∑ r, ∑ i ∈ p.heavyInRow r,
        ∑ j ∈ (p.freshInRow r).erase i,
          contract F j x p ^ 2) =
        ∑ p, 2 * (∑ r, ∑ i ∈ p.heavyInRow r,
          ∑ j ∈ (p.freshInRow r).erase i,
            contract F j x p ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p, (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.grade = nu
      · have hlocal := heavy_fresh_energy_at_le F x p
        have hcountNat : 2 * p.heavy.card ≤ nu := by
          simpa [hp] using p.two_mul_card_heavy_le_grade
        have hcount : (2 : ℝ) * (p.heavy.card : ℝ) ≤ (nu : ℝ) := by
          exact_mod_cast hcountNat
        calc
          2 * (∑ r, ∑ i ∈ p.heavyInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              2 * ((p.heavy.card : ℝ) *
                ParsevalFrame.normSq (fiber x p)) := by linarith
          _ = ((2 : ℝ) * (p.heavy.card : ℝ)) *
                ParsevalFrame.normSq (fiber x p) := by ring
          _ ≤ (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            exact mul_le_mul_of_nonneg_right hcount real_inner_self_nonneg
      · have hfiber : fiber x p = 0 := fiber_eq_zero_of_not_grade hx hp
        have hlocal := heavy_fresh_energy_at_le F x p
        calc
          2 * (∑ r, ∑ i ∈ p.heavyInRow r,
              ∑ j ∈ (p.freshInRow r).erase i,
                contract F j x p ^ 2) ≤
              2 * ((p.heavy.card : ℝ) *
                ParsevalFrame.normSq (fiber x p)) := by linarith
          _ = 0 := by simp [hfiber, ParsevalFrame.normSq]
          _ = (nu : ℝ) * ParsevalFrame.normSq (fiber x p) := by
            simp [hfiber, ParsevalFrame.normSq]
    _ = (nu : ℝ) * FiniteHilbert.normSq x := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [fiber, fullFiber] using (full_normSq_eq_sum_fiber x).symm

/-- The row-local coefficient squares after `Y₊` synthesis are exactly the
finite marked-output sum. -/
theorem Yplus_output_coeff_energy_eq (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ∑ a ∈ p.heavyInRow r,
        (contract F c x
          (setPair p (r, a) .one (r, c) .zero)) ^ 2) =
      ∑ z : RowMark m n .two .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := by
  rw [sum_rowMark_eq_nested (m := m) (n := n) .two .one
    (fun p r a c ↦ (contract F c x
      (setPair p (r, a) .one (r, c) .zero)) ^ 2)]
  simp only [levelInRow_two, levelInRow_one]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hnot : a ∉ p.lightInRow r := by
    intro hlight
    have haTwo : p (r, a) = .two := by simpa using ha
    have haOne : p (r, a) = .one := by simpa using hlight
    simp_all
  rw [Finset.erase_eq_self.mpr hnot]

/-- The corresponding exact marked-output identity for `Y₀`. -/
theorem Yzero_output_coeff_energy_eq (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ∑ a ∈ (p.lightInRow r).erase c,
        (contract F c x
          (setPair p (r, a) .two (r, c) .zero)) ^ 2) =
      ∑ z : RowMark m n .one .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .two
            (z.row, z.right) .zero)) ^ 2 := by
  rw [sum_rowMark_eq_nested (m := m) (n := n) .one .one
    (fun p r a c ↦ (contract F c x
      (setPair p (r, a) .two (r, c) .zero)) ^ 2)]
  simp only [levelInRow_one]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  exact sum_erase_comm (p.lightInRow r)
    (fun a c ↦ (contract F c x
      (setPair p (r, a) .two (r, c) .zero)) ^ 2) |>.symm

/-- The corresponding exact marked-output identity for the transpose hop. -/
theorem Hprime_output_coeff_energy_eq (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ∑ a ∈ p.freshInRow r,
        (contract F c x
          (setPair p (r, a) .one (r, c) .zero)) ^ 2) =
      ∑ z : RowMark m n .zero .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := by
  rw [sum_rowMark_eq_nested (m := m) (n := n) .zero .one
    (fun p r a c ↦ (contract F c x
      (setPair p (r, a) .one (r, c) .zero)) ^ 2)]
  simp only [levelInRow_zero, levelInRow_one]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hnot : a ∉ p.lightInRow r := by
    intro hlight
    have haZero : p (r, a) = .zero := by simpa using ha
    have haOne : p (r, a) = .one := by simpa using hlight
    simp_all
  rw [Finset.erase_eq_self.mpr hnot]

theorem Yplus_marked_synthesis_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ParsevalFrame.normSq (yPlusMarked F x p r c)) ≤
      markedEnergy .one .zero F x := by
  calc
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yPlusMarked F x p r c)) ≤
        ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ∑ a ∈ p.heavyInRow r,
            (contract F c x
              (setPair p (r, a) .one (r, c) .zero)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro c _
      exact yPlusMarked_normSq_le F x p r c
    _ = ∑ z : RowMark m n .two .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := Yplus_output_coeff_energy_eq F x
    _ = markedEnergy .one .zero F x := Yplus_marked_reindex F x

theorem Yzero_marked_synthesis_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ParsevalFrame.normSq (yZeroMarked F x p r c)) ≤
      markedEnergy .two .zero F x := by
  calc
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yZeroMarked F x p r c)) ≤
        ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ∑ a ∈ (p.lightInRow r).erase c,
            (contract F c x
              (setPair p (r, a) .two (r, c) .zero)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro c _
      exact yZeroMarked_normSq_le F x p r c
    _ = ∑ z : RowMark m n .one .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .two
            (z.row, z.right) .zero)) ^ 2 := Yzero_output_coeff_energy_eq F x
    _ = markedEnergy .two .zero F x := Yzero_marked_reindex F x

theorem Hprime_marked_synthesis_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ParsevalFrame.normSq (hprimeMarked F x p r c)) ≤
      markedEnergy .one .zero F x := by
  calc
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (hprimeMarked F x p r c)) ≤
        ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ∑ a ∈ p.freshInRow r,
            (contract F c x
              (setPair p (r, a) .one (r, c) .zero)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro c _
      exact hprimeMarked_normSq_le F x p r c
    _ = ∑ z : RowMark m n .zero .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := Hprime_output_coeff_energy_eq F x
    _ = markedEnergy .one .zero F x := Hprime_marked_reindex F x

theorem Yplus_output_fiber_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (p : Pattern m n) :
    ParsevalFrame.normSq
      (fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) p) ≤
      (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yPlusMarked F x p r c) := by
  by_cases hp : p.grade = nu + 2
  · by_cases hheavy : p.heavy.Nonempty
    · have hcardNat : p.light.card ≤ nu := by
        have hformula := p.grade_eq_card_light_add_two_mul_card_heavy
        have hone : 1 ≤ p.heavy.card := Finset.one_le_card.mpr hheavy
        omega
      have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
        exact_mod_cast hcardNat
      rw [Yplus_fullFiber]
      calc
        ParsevalFrame.normSq
            (∑ s ∈ p.light, yPlusMarked F x p s.1 s.2) ≤
            (p.light.card : ℝ) * ∑ s ∈ p.light,
              ParsevalFrame.normSq (yPlusMarked F x p s.1 s.2) :=
          normSq_sum_le_card p.light
            (fun s ↦ yPlusMarked F x p s.1 s.2)
        _ = (p.light.card : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
              ParsevalFrame.normSq (yPlusMarked F x p r c) := by
          rw [← sum_rows_light_eq_sum_light p
            (fun s ↦ ParsevalFrame.normSq (yPlusMarked F x p s.1 s.2))]
        _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
              ParsevalFrame.normSq (yPlusMarked F x p r c) := by
          apply mul_le_mul_of_nonneg_right hcard
          exact Finset.sum_nonneg fun r _ ↦
            Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg
    · have hempty : p.heavy = ∅ := Finset.not_nonempty_iff_eq_empty.mp hheavy
      have hrow (r : Fin m) : p.heavyInRow r = ∅ := by
        ext a
        constructor
        · intro ha
          have hsite : (r, a) ∈ p.heavy := by simpa using ha
          simp [hempty] at hsite
        · simp
      have hzero (r : Fin m) (c : Fin n) :
          ParsevalFrame.normSq (yPlusMarked F x p r c) = 0 := by
        have hle := yPlusMarked_normSq_le F x p r c
        rw [hrow] at hle
        simp only [Finset.sum_empty] at hle
        exact le_antisymm hle real_inner_self_nonneg
      rw [Yplus_fullFiber]
      calc
        ParsevalFrame.normSq
            (∑ s ∈ p.light, yPlusMarked F x p s.1 s.2) ≤
            (p.light.card : ℝ) * ∑ s ∈ p.light,
              ParsevalFrame.normSq (yPlusMarked F x p s.1 s.2) :=
          normSq_sum_le_card p.light
            (fun s ↦ yPlusMarked F x p s.1 s.2)
        _ = 0 := by simp [hzero]
        _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
              ParsevalFrame.normSq (yPlusMarked F x p r c) := by
          exact mul_nonneg (Nat.cast_nonneg nu)
            (Finset.sum_nonneg fun r _ ↦
              Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
  · have hpInt : (p.grade : ℤ) ≠ (nu : ℤ) + 2 := by
      intro h
      apply hp
      exact_mod_cast h
    have hz := fullFiber_mulVec_eq_zero_of_grade
      (Yplus_homogeneous (m := m) F) hx p hpInt
    rw [hz]
    have hrhs : 0 ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yPlusMarked F x p r c) :=
      mul_nonneg (Nat.cast_nonneg nu)
        (Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
    simpa [ParsevalFrame.normSq] using hrhs

theorem Yzero_output_fiber_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (p : Pattern m n) :
    ParsevalFrame.normSq
      (fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) p) ≤
      (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yZeroMarked F x p r c) := by
  by_cases hp : p.grade = nu
  · have hcardNat : p.light.card ≤ nu := by
      simpa [hp] using p.card_light_le_grade
    have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
      exact_mod_cast hcardNat
    rw [Yzero_fullFiber]
    calc
      ParsevalFrame.normSq
          (∑ s ∈ p.light, yZeroMarked F x p s.1 s.2) ≤
          (p.light.card : ℝ) * ∑ s ∈ p.light,
            ParsevalFrame.normSq (yZeroMarked F x p s.1 s.2) :=
        normSq_sum_le_card p.light
          (fun s ↦ yZeroMarked F x p s.1 s.2)
      _ = (p.light.card : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (yZeroMarked F x p r c) := by
        rw [← sum_rows_light_eq_sum_light p
          (fun s ↦ ParsevalFrame.normSq (yZeroMarked F x p s.1 s.2))]
      _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (yZeroMarked F x p r c) := by
        apply mul_le_mul_of_nonneg_right hcard
        exact Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg
  · have hpInt : (p.grade : ℤ) ≠ (nu : ℤ) + 0 := by
      intro h
      apply hp
      have h' : (p.grade : ℤ) = (nu : ℤ) := by simpa using h
      exact_mod_cast h'
    have hz := fullFiber_mulVec_eq_zero_of_grade
      (Yzero_homogeneous (m := m) F) hx p hpInt
    rw [hz]
    have hrhs : 0 ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yZeroMarked F x p r c) :=
      mul_nonneg (Nat.cast_nonneg nu)
        (Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
    simpa [ParsevalFrame.normSq] using hrhs

theorem Hprime_output_fiber_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (p : Pattern m n) :
    ParsevalFrame.normSq
      (fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) p) ≤
      (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (hprimeMarked F x p r c) := by
  by_cases hp : p.grade = nu
  · have hcardNat : p.light.card ≤ nu := by
      simpa [hp] using p.card_light_le_grade
    have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
      exact_mod_cast hcardNat
    rw [Hprime_fullFiber]
    calc
      ParsevalFrame.normSq
          (∑ s ∈ p.light, hprimeMarked F x p s.1 s.2) ≤
          (p.light.card : ℝ) * ∑ s ∈ p.light,
            ParsevalFrame.normSq (hprimeMarked F x p s.1 s.2) :=
        normSq_sum_le_card p.light
          (fun s ↦ hprimeMarked F x p s.1 s.2)
      _ = (p.light.card : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (hprimeMarked F x p r c) := by
        rw [← sum_rows_light_eq_sum_light p
          (fun s ↦ ParsevalFrame.normSq (hprimeMarked F x p s.1 s.2))]
      _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (hprimeMarked F x p r c) := by
        apply mul_le_mul_of_nonneg_right hcard
        exact Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg
  · have hpInt : (p.grade : ℤ) ≠ (nu : ℤ) + 0 := by
      intro h
      apply hp
      have h' : (p.grade : ℤ) = (nu : ℤ) := by simpa using h
      exact_mod_cast h'
    have hz := fullFiber_mulVec_eq_zero_of_grade
      (Hprime_homogeneous (m := m) F) hx p hpInt
    rw [hz]
    have hrhs : 0 ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (hprimeMarked F x p r c) :=
      mul_nonneg (Nat.cast_nonneg nu)
        (Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
    simpa [ParsevalFrame.normSq] using hrhs

theorem Yplus_output_energy_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Yplus m (frameRows F)) x) ≤
      (nu : ℝ) * markedEnergy .one .zero F x := by
  rw [full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) p)) ≤
        ∑ p, (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yPlusMarked F x p r c) := by
      exact Finset.sum_le_sum fun p _ ↦ Yplus_output_fiber_le_marked F hx p
    _ = (nu : ℝ) * ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yPlusMarked F x p r c) := by
      rw [Finset.mul_sum]
    _ ≤ (nu : ℝ) * markedEnergy .one .zero F x := by
      exact mul_le_mul_of_nonneg_left
        (Yplus_marked_synthesis_energy_le F x) (Nat.cast_nonneg nu)

theorem Yzero_output_energy_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Yzero m (frameRows F)) x) ≤
      (nu : ℝ) * markedEnergy .two .zero F x := by
  rw [full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) p)) ≤
        ∑ p, (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yZeroMarked F x p r c) := by
      exact Finset.sum_le_sum fun p _ ↦ Yzero_output_fiber_le_marked F hx p
    _ = (nu : ℝ) * ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yZeroMarked F x p r c) := by
      rw [Finset.mul_sum]
    _ ≤ (nu : ℝ) * markedEnergy .two .zero F x := by
      exact mul_le_mul_of_nonneg_left
        (Yzero_marked_synthesis_energy_le F x) (Nat.cast_nonneg nu)

theorem Hprime_output_energy_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Hprime m (frameRows F)) x) ≤
      (nu : ℝ) * markedEnergy .one .zero F x := by
  rw [full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) p)) ≤
        ∑ p, (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (hprimeMarked F x p r c) := by
      exact Finset.sum_le_sum fun p _ ↦ Hprime_output_fiber_le_marked F hx p
    _ = (nu : ℝ) * ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (hprimeMarked F x p r c) := by
      rw [Finset.mul_sum]
    _ ≤ (nu : ℝ) * markedEnergy .one .zero F x := by
      exact mul_le_mul_of_nonneg_left
        (Hprime_marked_synthesis_energy_le F x) (Nat.cast_nonneg nu)

/-- Sharp squared-energy estimate for `Y₊` on an exactly supported vector. -/
theorem Yplus_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Yplus m (frameRows F)) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  exact DirectionalBounds.directional_energy_sq_bound
    (Nat.cast_nonneg nu) (FiniteHilbert.normSq_nonneg x)
    (Yplus_output_energy_le_marked F hx)
    (markedEnergy_one_zero_le F hx)

/-- Sharp denominator-free squared-energy estimate for `Y₀` on an exactly
supported vector. -/
theorem Yzero_two_mul_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    2 * FiniteHilbert.normSq
      (Matrix.mulVec (Yzero m (frameRows F)) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  exact DirectionalBounds.directional_energy_half_sq_bound
    (Nat.cast_nonneg nu) (Yzero_output_energy_le_marked F hx)
    (two_mul_markedEnergy_two_zero_le F hx)

/-- Sharp squared-energy estimate for the transpose light hop on an exactly
supported vector. -/
theorem Hprime_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Hprime m (frameRows F)) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  exact DirectionalBounds.directional_energy_sq_bound
    (Nat.cast_nonneg nu) (FiniteHilbert.normSq_nonneg x)
    (Hprime_output_energy_le_marked F hx)
    (markedEnergy_one_zero_le F hx)

/-- Coordinate energy of the genuine restricted `Y₊` matrix. -/
theorem Yplus_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
      (Matrix.mulVec
        (Yplus m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  have h := Yplus_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    FiniteHilbert.normSq
        (Matrix.mulVec
          (Yplus m (frameRows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Denominator-free coordinate energy of the genuine restricted `Y₀`
matrix. -/
theorem Yzero_restricted_two_mul_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    2 * FiniteHilbert.normSq
      (Matrix.mulVec
        (Yzero m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  have h := Yzero_two_mul_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    2 * FiniteHilbert.normSq
        (Matrix.mulVec
          (Yzero m (frameRows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Coordinate energy of the genuine restricted transpose-hop matrix. -/
theorem Hprime_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
      (Matrix.mulVec
        (Hprime m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  have h := Hprime_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    FiniteHilbert.normSq
        (Matrix.mulVec
          (Hprime m (frameRows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

theorem Yzero_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
      (Matrix.mulVec
        (Yzero m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      ((nu : ℝ) / Real.sqrt 2) ^ 2 * FiniteHilbert.normSq x := by
  have htwo := Yzero_restricted_two_mul_energy (m := m) F nu x
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hconstant : ((nu : ℝ) / Real.sqrt 2) ^ 2 =
      (nu : ℝ) ^ 2 / 2 := by
    rw [div_pow, hsqrt]
  rw [hconstant]
  nlinarith [FiniteHilbert.normSq_nonneg
    (Matrix.mulVec
      (Yzero m (frameRows F) * gradeProjection (d := d) nu) x)]

/-- The first directional row-local bound from the paper, as an actual L2
matrix operator norm. -/
theorem norm_Yplus_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Yplus m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (Yplus_restricted_energy (m := m) F nu)

/-- The second directional row-local bound, including the sharp `sqrt 2`
denominator. -/
theorem norm_Yzero_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Yzero m (frameRows F) * gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / Real.sqrt 2 := by
  exact norm_le_of_normSq_mulVec_le
    (div_nonneg (Nat.cast_nonneg nu) (Real.sqrt_nonneg 2))
    (Yzero_restricted_energy (m := m) F nu)

/-- The transpose light-hop directional row-local bound, as an actual L2
matrix operator norm. -/
theorem norm_Hprime_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Hprime m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (Hprime_restricted_energy (m := m) F nu)

end

end DirectionalConcrete

end SparseFock
