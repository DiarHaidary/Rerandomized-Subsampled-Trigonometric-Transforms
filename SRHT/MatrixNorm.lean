import SRHT.HardCore
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace SRHT.MatrixNorm
open HardCore
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

variable {I J K I' J' K' : Type*}
  [Fintype I] [Fintype J] [Fintype K]
  [Fintype I'] [Fintype J'] [Fintype K']
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [DecidableEq I'] [DecidableEq J'] [DecidableEq K']

theorem submatrix_equiv_mulVec (A : Matrix I J ℝ)
    (e : I' ≃ I) (f : J' ≃ J) (v : J' → ℝ) (i : I') :
    (A.submatrix e f).mulVec v i =
      A.mulVec (fun j => v (f.symm j)) (e i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  simpa using f.sum_comp (fun j => A (e i) j * v (f.symm j))

theorem submatrix_equiv_norm_le (A : Matrix I J ℝ)
    (e : I' ≃ I) (f : J' ≃ J) : ‖A.submatrix e f‖ ≤ ‖A‖ := by
  apply matrix_norm_le_of_energy _ _ (norm_nonneg _)
  intro v
  have hout : energy ((A.submatrix e f).mulVec v) =
      energy (A.mulVec (fun j => v (f.symm j))) := by
    simp only [energy, submatrix_equiv_mulVec]
    exact e.sum_comp (fun i => (A.mulVec (fun j => v (f.symm j))) i ^ 2)
  have hin : energy (fun j => v (f.symm j)) = energy v := by
    exact f.symm.sum_comp (fun j => v j ^ 2)
  rw [hout]
  calc
    _ ≤ ‖A‖ ^ 2 * energy (fun j => v (f.symm j)) :=
      matrix_energy_le_norm A _
    _ = _ := by rw [hin]

theorem submatrix_equiv_norm (A : Matrix I J ℝ)
    (e : I' ≃ I) (f : J' ≃ J) : ‖A.submatrix e f‖ = ‖A‖ := by
  apply le_antisymm (submatrix_equiv_norm_le A e f)
  have h := submatrix_equiv_norm_le (A.submatrix e f) e.symm f.symm
  simpa [Matrix.submatrix_submatrix] using h

def amplifyLeft (A : Matrix I J ℝ) : Matrix (K × I) (K × J) ℝ :=
  fun out inp => if out.1 = inp.1 then A out.2 inp.2 else 0

theorem amplifyLeft_norm_le (A : Matrix I J ℝ) :
    ‖amplifyLeft (K := K) A‖ ≤ ‖A‖ := by
  have heq : amplifyLeft (K := K) A =
      (amplifyRight (K := K) A).submatrix (Equiv.prodComm K I) (Equiv.prodComm K J) := by
    ext out inp
    simp [amplifyLeft, amplifyRight]
  rw [heq, submatrix_equiv_norm]
  exact amplifyRight_norm_le A

theorem kronecker_factor (A : Matrix I J ℝ) (B : Matrix K K' ℝ) :
    Matrix.kronecker A B =
      amplifyRight (K := K) A * amplifyLeft (K := J) B := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp [Matrix.kronecker, Matrix.kroneckerMap, Matrix.mul_apply,
    amplifyRight, amplifyLeft, Fintype.sum_prod_type]

theorem kronecker_norm_le (A : Matrix I J ℝ) (B : Matrix K K' ℝ) :
    ‖Matrix.kronecker A B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [kronecker_factor]
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul (amplifyRight_norm_le A) (amplifyLeft_norm_le B)
      (norm_nonneg _) (norm_nonneg _))

end
end SRHT.MatrixNorm
