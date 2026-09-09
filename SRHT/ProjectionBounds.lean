import SRHT.Cutoff
import SRHT.MatrixNorm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace SRHT.ProjectionBounds
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix Cutoff
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

@[simp] theorem projection_transpose (D : Finset I) :
    (supportProjection D).transpose = supportProjection D := diagonal_transpose _

@[simp] theorem projection_sq (D : Finset I) : supportProjection D * supportProjection D =
    supportProjection D := by
  simp only [supportProjection,diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem projection_norm_le_one (D : Finset I) : ‖supportProjection D‖ ≤ 1 := by
  rw [supportProjection,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro i
  split_ifs <;> norm_num

theorem sandwich_norm_le (P : Matrix I J ℝ) (A : Matrix I I ℝ)
    (hP : ‖P‖ ≤ 1) : ‖P.transpose*A*P‖ ≤ ‖A‖ := by
  have ht : ‖P.transpose‖ ≤ 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.l2_opNorm_conjTranspose]
    exact hP
  calc
    _ ≤ (‖P.transpose‖*‖A‖)*‖P‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖A‖)*1 := by gcongr
    _ = _ := by ring

theorem projection_sandwich_norm_le (D : Finset I) (A : Matrix I I ℝ) :
    ‖supportProjection D*A*supportProjection D‖ ≤ ‖A‖ := by
  simpa using sandwich_norm_le (supportProjection D) A (projection_norm_le_one D)

theorem projection_positive (D : Finset I) : (supportProjection D).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (supportProjection D)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem sandwich_positive (D : Finset I) (A : Matrix I I ℝ) (hA : A.PosSemidef) :
    (supportProjection D*A*supportProjection D).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same (supportProjection D)

theorem projection_apply (D : Finset I) (i j : I) :
    supportProjection D i j = if i=j ∧ i∈D then 1 else 0 := by
  by_cases h : i=j <;> simp [supportProjection,Matrix.diagonal_apply,h]

theorem sandwich_apply (D : Finset I) (A : Matrix I I ℝ) (i j : I) :
    (supportProjection D*A*supportProjection D) i j =
      if i∈D ∧ j∈D then A i j else 0 := by
  simp only [supportProjection,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hi : i∈D <;> by_cases hj : j∈D <;> simp [hi,hj]

theorem sandwich_sum {K : Type*} [Fintype K] (P : Matrix I I ℝ)
    (A : K → Matrix I I ℝ) :
    ∑ k, P*A k*P = P*(∑ k, A k)*P := by
  simp only [Matrix.mul_sum,Matrix.sum_mul]

theorem sandwich_finset_sum {K : Type*} (T : Finset K) (P : Matrix I I ℝ)
    (A : K → Matrix I I ℝ) :
    ∑ k ∈ T, P*A k*P = P*(∑ k ∈ T, A k)*P := by
  simp only [Matrix.mul_sum,Matrix.sum_mul]

end
end SRHT.ProjectionBounds
