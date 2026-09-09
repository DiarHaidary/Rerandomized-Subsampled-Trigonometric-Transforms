import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Exact finite-time compression.  The power needed in an even vacuum
moment is q, because the moment is the squared norm of the q-step orbit. -/

namespace SRHT.Cutoff

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- An orbit retained through time q is unchanged by compression at every
step.  No global invariance of the cutoff space is required. -/
theorem compression_pow_apply
    (M P : H →ₗ[ℝ] H) (v : H) (q : ℕ)
    (hretain : ∀ j ≤ q, P ((M ^ j) v) = (M ^ j) v) :
    ((P * M * P) ^ q) v = (M ^ q) v := by
  have h : ∀ j ≤ q, ((P * M * P) ^ j) v = (M ^ j) v := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hjq : j ≤ q := by omega
      rw [pow_succ', Module.End.mul_apply, ih hjq]
      simp only [Module.End.mul_apply]
      rw [hretain j hjq]
      simpa only [pow_succ', Module.End.mul_apply] using hretain (j + 1) hj
  exact h q le_rfl

/-- Reachability in nested cutoff spaces supplies the retention hypotheses. -/
theorem compression_pow_apply_of_filtration
    (M P : H →ₗ[ℝ] H) (V : ℕ → Submodule ℝ H) (v : H) (q : ℕ)
    (hv : v ∈ V 0)
    (hstep : ∀ j < q, ∀ x ∈ V j, M x ∈ V (j + 1))
    (hfix : ∀ j ≤ q, ∀ x ∈ V j, P x = x) :
    ((P * M * P) ^ q) v = (M ^ q) v := by
  apply compression_pow_apply
  intro j hj
  apply hfix j hj
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hstep j (by omega) _ (ih (by omega))

section Norm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Squared q-step norms, and consequently even vacuum moments, are exactly
unchanged by cutoff. -/
theorem compression_pow_norm_sq
    (M P : E →L[ℝ] E) (v : E) (q : ℕ)
    (hretain : ∀ j ≤ q, P ((M ^ j) v) = (M ^ j) v) :
    ‖((P * M * P) ^ q) v‖ ^ 2 = ‖(M ^ q) v‖ ^ 2 := by
  have h := compression_pow_apply M.toLinearMap P.toLinearMap v q
    (by simpa only [← ContinuousLinearMap.toLinearMap_pow,
      ContinuousLinearMap.coe_coe] using hretain)
  have heq : ((P * M * P) ^ q) v = (M ^ q) v := by
    simpa only [← ContinuousLinearMap.toLinearMap_mul,
      ← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe] using h
  rw [heq]

/-- The summed squared-orbit form used for a matrix-valued vacuum moment. -/
theorem compression_vacuum_moment {ι : Type*} [Fintype ι]
    (M P : E →L[ℝ] E) (v : ι → E) (q : ℕ)
    (hretain : ∀ i j, j ≤ q → P ((M ^ j) (v i)) = (M ^ j) (v i)) :
    (∑ i, ‖((P * M * P) ^ q) (v i)‖ ^ 2) =
      ∑ i, ‖(M ^ q) (v i)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  exact compression_pow_norm_sq M P (v i) q (hretain i)

end Norm

section Matrix

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate projection onto a finite set of allowed basis states. -/
def supportProjection (D : Finset ι) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => if i ∈ D then 1 else 0

@[simp] theorem supportProjection_mulVec (D : Finset ι) (v : ι → ℝ) (i : ι) :
    (supportProjection D *ᵥ v) i = if i ∈ D then v i else 0 := by
  simp [supportProjection, Matrix.mulVec_diagonal]

theorem supportProjection_fix (D : Finset ι) (v : ι → ℝ)
    (hv : ∀ i, i ∉ D → v i = 0) : supportProjection D *ᵥ v = v := by
  funext i
  rw [supportProjection_mulVec]
  split_ifs with hi
  · rfl
  · exact (hv i hi).symm

/-- Coordinate support moves only along nonzero matrix entries. -/
theorem mulVec_supported (M : Matrix ι ι ℝ) (D E : Finset ι) (v : ι → ℝ)
    (hv : ∀ j, j ∉ D → v j = 0)
    (hstep : ∀ i j, j ∈ D → M i j ≠ 0 → i ∈ E) :
    ∀ i, i ∉ E → (M *ᵥ v) i = 0 := by
  intro i hi
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j ∈ D
  · have hm : M i j = 0 := by
      by_contra hm
      exact hi (hstep i j hj hm)
    simp [hm]
  · simp [hv j hj]

/-- Actual matrix powers are preserved by compression on a retained orbit. -/
theorem matrix_compression_pow_mulVec
    (M P : Matrix ι ι ℝ) (v : ι → ℝ) (q : ℕ)
    (hretain : ∀ j ≤ q, P *ᵥ ((M ^ j) *ᵥ v) = (M ^ j) *ᵥ v) :
    ((P * M * P) ^ q) *ᵥ v = (M ^ q) *ᵥ v := by
  have h : ∀ j ≤ q, ((P * M * P) ^ j) *ᵥ v = (M ^ j) *ᵥ v := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hjq : j ≤ q := by omega
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih hjq]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hretain j hjq]
      simpa only [pow_succ', ← Matrix.mulVec_mulVec] using hretain (j + 1) hj
  exact h q le_rfl

/-- Exact q-step cutoff identity with fully explicit finite coordinate
support hypotheses.  The one-step hypothesis is an entrywise bandwidth
condition, not a hypothesis about powers or moments. -/
theorem matrix_cutoff_pow_of_reachability
    (M : Matrix ι ι ℝ) (D : ℕ → Finset ι) (v : ι → ℝ) (q : ℕ)
    (hv : ∀ i, i ∉ D 0 → v i = 0)
    (hstep : ∀ j < q, ∀ a b, b ∈ D j → M a b ≠ 0 → a ∈ D (j + 1))
    (hmono : ∀ j ≤ q, D j ⊆ D q) :
    ((supportProjection (D q) * M * supportProjection (D q)) ^ q) *ᵥ v =
      (M ^ q) *ᵥ v := by
  apply matrix_compression_pow_mulVec
  intro j hj
  apply supportProjection_fix
  have hs : ∀ i, i ∉ D j → ((M ^ j) *ᵥ v) i = 0 := by
    induction j with
    | zero => simpa using hv
    | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact mulVec_supported M (D j) (D (j + 1)) _ (ih (by omega))
        (hstep j (by omega))
  intro i hi
  exact hs i (fun hm => hi (hmono j hj hm))

/-- The exact even-moment quantity is a sum of squared q-step orbit norms.
Consequently the q-step cutoff, rather than a 2q-step cutoff, suffices. -/
theorem matrix_cutoff_vacuum_energy {κ : Type*} [Fintype κ]
    (M : Matrix ι ι ℝ) (D : ℕ → Finset ι) (v : κ → ι → ℝ) (q : ℕ)
    (hv : ∀ k i, i ∉ D 0 → v k i = 0)
    (hstep : ∀ j < q, ∀ a b, b ∈ D j → M a b ≠ 0 → a ∈ D (j + 1))
    (hmono : ∀ j ≤ q, D j ⊆ D q) :
    (∑ k, ∑ i, (((supportProjection (D q) * M * supportProjection (D q)) ^ q) *ᵥ v k) i ^ 2) =
      ∑ k, ∑ i, ((M ^ q) *ᵥ v k) i ^ 2 := by
  apply Finset.sum_congr rfl
  intro k _
  rw [matrix_cutoff_pow_of_reachability M D (v k) q (hv k) hstep hmono]

end Matrix
end SRHT.Cutoff
