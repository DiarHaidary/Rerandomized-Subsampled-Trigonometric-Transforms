import SRHT.SmallRowsNormalBound

/-! Finite row collection and orthogonal block assembly for the small-row theorem. -/
namespace SRHT.SmallRows
open SRHT.HardCore SRHT.MatrixNorm
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {R I J K : Type*} [Fintype R] [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq R] [DecidableEq I] [DecidableEq J] [DecidableEq K]

def rowCollection (A : R→Matrix I J ℝ) : Matrix (R×I) J ℝ :=
  fun out inp=>A out.1 out.2 inp

theorem rowCollection_gram (A : R→Matrix I J ℝ) :
    (rowCollection A).transpose * rowCollection A = ∑ r, (A r).transpose*A r := by
  ext i j
  simp only [rowCollection,Matrix.mul_apply,Matrix.transpose_apply,Matrix.sum_apply,Fintype.sum_prod_type]

theorem rowCollection_mul (A : R→Matrix I J ℝ) (B : Matrix J K ℝ) :
    rowCollection A * B = rowCollection (fun r=>A r*B) := by
  ext i j
  simp only [rowCollection,Matrix.mul_apply]

theorem norm_sq_eq_columnGram (A : Matrix I J ℝ) : ‖A‖^2=‖A.transpose*A‖ := by
  have h:=Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  simpa only [pow_two] using h.symm

theorem rowCollection_norm_sq_le (A : R→Matrix I J ℝ) (c : ℝ)
    (hA : ∀ r, ‖A r‖^2≤c) : ‖rowCollection A‖^2≤(Fintype.card R:ℝ)*c := by
  rw [norm_sq_eq_columnGram,rowCollection_gram]
  calc
    _ ≤ ∑ r, ‖(A r).transpose*A r‖ := norm_sum_le _ _
    _ = ∑ r, ‖A r‖^2 := by simp_rw [← norm_sq_eq_columnGram]
    _ ≤ ∑ _r:R, c := Finset.sum_le_sum (fun r _=>hA r)
    _ = (Fintype.card R:ℝ)*c := by simp

theorem transpose_product_zero (A B : Matrix I J ℝ) (h : A.transpose*B=0) :
    B.transpose*A=0 := by
  have ht:=congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using ht

/-- Square norms add subadditively when all output channels are mutually orthogonal. -/
theorem four_block_norm_sq_le (A B C D : Matrix I J ℝ)
    (hAB : A.transpose*B=0) (hAC : A.transpose*C=0) (hAD : A.transpose*D=0)
    (hBC : B.transpose*C=0) (hBD : B.transpose*D=0) (hCD : C.transpose*D=0) :
    ‖A+B+C+D‖^2 ≤ ‖A‖^2+‖B‖^2+‖C‖^2+‖D‖^2 := by
  have heq : (A+B+C+D).transpose*(A+B+C+D)=
      A.transpose*A+B.transpose*B+C.transpose*C+D.transpose*D := by
    simp only [Matrix.transpose_add,Matrix.add_mul,Matrix.mul_add,hAB,hAC,hAD,hBC,hBD,hCD,
      transpose_product_zero A B hAB,transpose_product_zero A C hAC,
      transpose_product_zero A D hAD,transpose_product_zero B C hBC,
      transpose_product_zero B D hBD,transpose_product_zero C D hCD,add_zero,zero_add]
  rw [norm_sq_eq_columnGram,heq]
  have h1:=norm_add_le (A.transpose*A) (B.transpose*B)
  have h2:=norm_add_le (A.transpose*A+B.transpose*B) (C.transpose*C)
  have h3:=norm_add_le (A.transpose*A+B.transpose*B+C.transpose*C) (D.transpose*D)
  simp_rw [← norm_sq_eq_columnGram] at h1 h2 h3
  linarith

end
end SRHT.SmallRows

