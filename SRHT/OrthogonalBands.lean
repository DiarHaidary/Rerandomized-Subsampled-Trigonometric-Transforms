import SRHT.MatrixNorm

namespace SRHT.OrthogonalBands
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
variable {B I J : Type*} [Fintype B] [DecidableEq B]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem transpose_mul_zero (A C : Matrix I J ℝ)
    (h : ∀ i j l, A i j*C i l=0) : A.transpose*C=0 := by
  ext j l
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.zero_apply]
  exact Finset.sum_eq_zero (fun i _ => h i j l)

theorem gram_sum (A : B → Matrix I J ℝ)
    (h : ∀ b c, b≠c → (A b).transpose*A c=0) :
    (∑ b, A b).transpose*(∑ b, A b) = ∑ b, (A b).transpose*A b := by
  rw [Matrix.transpose_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_single b
  · intro c _ hc
    exact h b c hc.symm
  · simp

theorem norm_sum_sq_le (A : B → Matrix I J ℝ)
    (h : ∀ b c, b≠c → (A b).transpose*A c=0) :
    ‖∑ b, A b‖^2 ≤ ∑ b, ‖A b‖^2 := by
  have he (M : Matrix I J ℝ) : ‖M.transpose*M‖=‖M‖^2 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self M
  rw [← he,gram_sum A h]
  calc
    _ ≤ ∑ b, ‖(A b).transpose*A b‖ := norm_sum_le _ _
    _ = _ := by simp_rw [he]

theorem norm_sum_sq_le_of_disjoint_support (A : B → Matrix I J ℝ)
    (h : ∀ b c, b≠c → ∀ i j l, A b i j*A c i l=0) :
    ‖∑ b, A b‖^2 ≤ ∑ b, ‖A b‖^2 :=
  norm_sum_sq_le A (fun b c hbc => transpose_mul_zero _ _ (h b c hbc))

end
end SRHT.OrthogonalBands
