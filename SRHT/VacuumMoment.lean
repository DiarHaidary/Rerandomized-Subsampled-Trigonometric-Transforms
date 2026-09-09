import SRHT.MatrixRepresentation
import SRHT.Cutoff

/-! Finite vacuum moments and exact reachable-state compression. -/
namespace SRHT.VacuumMoment
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open SparseFock.FiniteL2 SRHT.HardCore Matrix

variable {J : Type*} [Fintype J] [DecidableEq J]

def unitVector (j : J) : J → ℝ := fun i => if i=j then 1 else 0

@[simp] theorem energy_unitVector (j : J) : energy (unitVector j) = 1 := by
  simp [energy,unitVector]

@[simp] theorem mulVec_unitVector (M : Matrix J J ℝ) (j i : J) :
    (M *ᵥ unitVector j) i = M i j := by
  simp [Matrix.mulVec,dotProduct,unitVector]

theorem even_diagonal_energy (M : Matrix J J ℝ) (hM : M.transpose=M)
    (q : ℕ) (j : J) : (M^(2*q)) j j = energy ((M^q) *ᵥ unitVector j) := by
  have hp : (M^q).transpose=M^q := by rw [Matrix.transpose_pow,hM]
  have hpow : M^(2*q) = (M^q).transpose*(M^q) := by
    rw [hp, ← pow_add]
    congr 1
    omega
  rw [hpow]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,energy,mulVec_unitVector,pow_two]

theorem energy_power_unit_le (M : Matrix J J ℝ) (q : ℕ) (j : J)
    {K : ℝ} (hK : 0 ≤ K) (hM : ‖M‖ ≤ K) :
    energy ((M^q) *ᵥ unitVector j) ≤ K^(2*q) := by
  letI : Nonempty J := ⟨j⟩
  have hpow : ‖M^q‖ ≤ K^q := (norm_pow_le M q).trans (pow_le_pow_left₀ (norm_nonneg _) hM q)
  calc
    _ ≤ ‖M^q‖^2 := by simpa using matrix_energy_le_norm (M^q) (unitVector j)
    _ ≤ (K^q)^2 := pow_le_pow_left₀ (norm_nonneg _) hpow 2
    _ = K^(2*q) := by rw [← pow_mul]; congr 1; omega

theorem compressed_energy_bound (M : Matrix J J ℝ) (D : ℕ → Finset J)
    (q : ℕ) (j : J) (hj : j ∈ D 0)
    (hstep : ∀ r < q, ∀ a b, b ∈ D r → M a b ≠ 0 → a ∈ D (r+1))
    (hmono : ∀ r ≤ q, D r ⊆ D q)
    {K : ℝ} (hK : 0 ≤ K)
    (hnorm : ‖Cutoff.supportProjection (D q)*M*Cutoff.supportProjection (D q)‖ ≤ K) :
    energy ((M^q) *ᵥ unitVector j) ≤ K^(2*q) := by
  have hv : ∀ i, i ∉ D 0 → unitVector j i=0 := by
    intro i hi
    have hne : i≠j := by intro he; exact hi (he.symm ▸ hj)
    simp [unitVector,hne]
  rw [← Cutoff.matrix_cutoff_pow_of_reachability M D (unitVector j) q hv hstep hmono]
  exact energy_power_unit_le _ q j hK hnorm

theorem moment_le_of_compressed_norm
    {Ω I A : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A]
    (B : WeightedONBasis Ω I) (M : Ω → Matrix A A ℝ)
    (hM : ∀ x, (M x).transpose=M x) (D : ℕ → Finset (A × I))
    (q : ℕ) (hv : ∀ a : A, (a,B.vacuum) ∈ D 0)
    (hstep : ∀ r < q, ∀ a b, b ∈ D r → B.matrixMulOp M a b ≠ 0 → a ∈ D (r+1))
    (hmono : ∀ r ≤ q, D r ⊆ D q)
    {K : ℝ} (hK : 0 ≤ K)
    (hnorm : ‖Cutoff.supportProjection (D q)*B.matrixMulOp M*Cutoff.supportProjection (D q)‖ ≤ K) :
    B.expect (fun x => Matrix.trace (M x^(2*q))) ≤ (Fintype.card A : ℝ)*K^(2*q) := by
  rw [← B.matrix_vacuum_moment]
  calc
    _ = ∑ a : A, energy ((B.matrixMulOp M^q) *ᵥ unitVector (a,B.vacuum)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact even_diagonal_energy _ (MatrixRepresentation.matrixMulOp_symmetric B M hM) q _
    _ ≤ ∑ _ : A, K^(2*q) := by
      apply Finset.sum_le_sum
      intro a _
      exact compressed_energy_bound _ D q _ (hv a) hstep hmono hK hnorm
    _ = _ := by simp

end
end SRHT.VacuumMoment
