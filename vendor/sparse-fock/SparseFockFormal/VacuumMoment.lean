import SparseFockFormal.ProductFock
import SparseFockFormal.ExternalOperators
import SparseFockFormal.ParsevalFrame
import Mathlib.Tactic

namespace SparseFock

namespace VacuumMoment

open scoped BigOperators
open FiniteL2 FiniteOperator ExternalOperator ParsevalFrame ProductFock

noncomputable section

/-- The normalized iid-coordinate Gram error
`m⁻¹ Σ_r Σ_{i≠j} eta_{ri} eta_{rj} u_i u_jᵀ`. -/
def iidGramError {m n d : ℕ} (b : ℕ) (F : Frame n d)
    (omega : Configuration m n) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (m : ℝ)) •
    ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
      (etaCoordinate b (r, i) omega * etaCoordinate b (r, j) omega) •
        ParsevalFrame.outer (F.u i) (F.u j)

theorem iidGramError_apply {m n d : ℕ} (b : ℕ) (F : Frame n d)
    (omega : Configuration m n) (a c : Fin d) :
    iidGramError b F omega a c = (1 / (m : ℝ)) *
      ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
        etaCoordinate b (r, i) omega * etaCoordinate b (r, j) omega *
          F.u i a * F.u j c := by
  simp only [iidGramError, Matrix.smul_apply, Matrix.sum_apply,
    ParsevalFrame.outer_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Matrix-valued multiplication by the random Gram error in the concrete
product polynomial basis. -/
def multiplicationOperator {m n d : ℕ} (b : ℕ) (hb : 1 < b) (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (Fin d × Pattern m n) ℝ :=
  (weightedONBasis b hb m n).matrixMulOp (iidGramError b F)

/-- The exact vacuum-moment identity, for every natural power `k`. -/
theorem vacuum_moment_identity {m n d b : ℕ} (hb : 1 < b) (F : Frame n d)
    (k : ℕ) :
    (∑ a : Fin d,
      (multiplicationOperator b hb F ^ k)
        (a, vacuumPattern m n) (a, vacuumPattern m n)) =
      (iidLaw b hb m n).expect
        (fun omega ↦ Matrix.trace ((iidGramError b F omega) ^ k)) := by
  simpa [multiplicationOperator, weightedONBasis,
    FiniteL2.WeightedONBasis.expect, FiniteLaw.expect] using
      (weightedONBasis b hb m n).matrix_vacuum_moment (iidGramError b F) k

section MatrixMulOpLinearity

variable {Omega I A K : Type*}
  [Fintype Omega] [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype K]

theorem matrixMulOp_smul (B : WeightedONBasis Omega I) (c : ℝ)
    (M : Omega → Matrix A A ℝ) :
    B.matrixMulOp (fun omega ↦ c • M omega) = c • B.matrixMulOp M := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  ring

theorem matrixMulOp_fintype_sum (B : WeightedONBasis Omega I)
    (M : K → Omega → Matrix A A ℝ) :
    B.matrixMulOp (fun omega ↦ ∑ k, M k omega) =
      ∑ k, B.matrixMulOp (M k) := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.sum_apply, Finset.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem matrixMulOp_finset_sum (B : WeightedONBasis Omega I)
    (S : Finset K) (M : K → Omega → Matrix A A ℝ) :
    B.matrixMulOp (fun omega ↦ ∑ k ∈ S, M k omega) =
      ∑ k ∈ S, B.matrixMulOp (M k) := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.sum_apply, Finset.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end MatrixMulOpLinearity

/-- A scalar observable multiplying a fixed external matrix becomes the
external tensor product with its scalar multiplication matrix. -/
theorem matrixMulOp_scalar_external {m n d b : ℕ} (hb : 1 < b)
    (a : Configuration m n → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (weightedONBasis b hb m n).matrixMulOp (fun omega ↦ a omega • M) =
      externalTensor M ((weightedONBasis b hb m n).mulOp a) := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.mulOp,
    WeightedONBasis.coeff, externalTensor, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  ring

/-- The concrete deterministic Fock operator obtained by lifting the local
Jacobi multiplication matrices at the two distinct sites. -/
def globalJacobiOperator {m n d : ℕ} (b : ℕ) (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (Fin d × Pattern m n) ℝ :=
  let J := LocalOperator.jacobi (Real.sqrt ((b : ℝ) - 1))
  (1 / (m : ℝ)) •
    ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
      externalTensor (ParsevalFrame.outer (F.u i) (F.u j))
        (siteKernel (r, i) J * siteKernel (r, j) J)

/-- The matrix-valued multiplication operator is exactly the explicit global
sum of external rank-one terms tensored with the two lifted Jacobi matrices. -/
theorem multiplicationOperator_eq_globalJacobi {m n d b : ℕ} (hb : 1 < b)
    (F : Frame n d) :
    multiplicationOperator (m := m) b hb F = globalJacobiOperator (m := m) b F := by
  let B := weightedONBasis b hb m n
  let J := LocalOperator.jacobi (Real.sqrt ((b : ℝ) - 1))
  change B.matrixMulOp (iidGramError b F) = _
  rw [show iidGramError b F = fun omega ↦ (1 / (m : ℝ)) •
      ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
        (etaCoordinate b (r, i) omega * etaCoordinate b (r, j) omega) •
          ParsevalFrame.outer (F.u i) (F.u j) from rfl]
  rw [matrixMulOp_smul]
  rw [matrixMulOp_fintype_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [matrixMulOp_fintype_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [matrixMulOp_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixMulOp_scalar_external]
  rw [ProductFock.mulOp_etaCoordinate_mul hb (r, i) (r, j)]

end

end VacuumMoment

end SparseFock
