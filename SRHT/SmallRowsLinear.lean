import SRHT.SmallRowsE
import SRHT.Model
import SRHT.MatrixNorm

/-! The three coefficient flattenings of an actual two-sign Walsh row. -/
namespace SRHT.SmallRows
open SRHT.HardCore SRHT.MatrixNorm
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {k : ℕ} {D : Type*} [Fintype D] [DecidableEq D]

def raisingCoefficient (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ) :
    Matrix (WalshIndex k × WalshIndex k) D ℝ :=
  fun out b => U out.1 b * walshMatrix k (j+out.1) out.2

theorem raisingCoefficient_gram (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ) :
    (raisingCoefficient j U).transpose * raisingCoefficient j U = U.transpose*U := by
  classical
  ext b c
  simp only [raisingCoefficient,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ a, (U i b * walshMatrix k (j+i) a) * (U i c * walshMatrix k (j+i) a)) =
        (U i b*U i c) * ∑ a, walshMatrix k (j+i) a * walshMatrix k (j+i) a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [walsh_row_inner]; simp

theorem raisingCoefficient_norm (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ) :
    ‖raisingCoefficient j U‖=‖U‖ := by
  have hf := Matrix.l2_opNorm_conjTranspose_mul_self (raisingCoefficient j U)
  have hu := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,raisingCoefficient_gram] at hf
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hu
  have hn1:=norm_nonneg (raisingCoefficient j U)
  have hn2:=norm_nonneg U
  nlinarith

def mixedCoefficient (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ) :
    Matrix (WalshIndex k) (D × WalshIndex k) ℝ :=
  fun i inp => U i inp.1 * walshMatrix k (j+i) inp.2

theorem mixedCoefficient_gram (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ) :
    mixedCoefficient j U * (mixedCoefficient j U).transpose =
      Matrix.diagonal (rowLeverage U) := by
  classical
  ext i l
  simp only [mixedCoefficient,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type]
  have he : (∑ b, ∑ a,
      (U i b*walshMatrix k (j+i) a)*(U l b*walshMatrix k (j+l) a)) =
      (∑ b, U i b*U l b) * (∑ a, walshMatrix k (j+i) a*walshMatrix k (j+l) a) := by
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he,walsh_row_inner]
  by_cases hi : i=l
  · subst l
    simp only [ite_true,mul_one,Matrix.diagonal_apply_eq,rowLeverage]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · have hj : j+i≠j+l := fun h=>hi (add_left_cancel h)
    simp [hi,hj,Matrix.diagonal_apply]

theorem mixedCoefficient_norm_sq_le (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ)
    (mu : ℝ) (hmu : 0≤mu) (hell : ∀ i, rowLeverage U i≤mu) :
    ‖mixedCoefficient j U‖^2≤mu := by
  classical
  have hf := Matrix.l2_opNorm_conjTranspose_mul_self (mixedCoefficient j U).transpose
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose,
    mixedCoefficient_gram,Matrix.l2_opNorm_diagonal] at hf
  have ht : ‖(mixedCoefficient j U).transpose‖=‖mixedCoefficient j U‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (mixedCoefficient j U)
  have hd : ‖rowLeverage U‖≤mu := by
    apply (pi_norm_le_iff_of_nonneg hmu).2
    intro i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (rowLeverage_nonneg U i)] using hell i
  rw [ht] at hf
  nlinarith

def diagonalRowCoefficient (U : Matrix (WalshIndex k) D ℝ) :
    Matrix (WalshIndex k) (D × WalshIndex k) ℝ :=
  fun i inp => if i=inp.2 then U i inp.1 else 0

theorem diagonalRowCoefficient_gram (U : Matrix (WalshIndex k) D ℝ) :
    diagonalRowCoefficient U * (diagonalRowCoefficient U).transpose = Matrix.diagonal (rowLeverage U) := by
  classical
  ext i l
  simp only [diagonalRowCoefficient,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    ite_mul,mul_ite,zero_mul,mul_zero,Fintype.sum_ite_eq]
  by_cases h : i=l
  · subst l
    simp only [ite_true,Matrix.diagonal_apply_eq,rowLeverage]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp [h,Ne.symm h,Matrix.diagonal_apply]

def reversedMixedCoefficient (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ) :
    Matrix (WalshIndex k) (D × WalshIndex k) ℝ :=
  fun a inp => U inp.2 inp.1 * walshMatrix k (j+inp.2) a

def shiftedWalsh (j : WalshIndex k) : Matrix (WalshIndex k) (WalshIndex k) ℝ :=
  fun a i => walshMatrix k (j+i) a

theorem reversedMixedCoefficient_factor (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ) :
    reversedMixedCoefficient j U = shiftedWalsh j * diagonalRowCoefficient U := by
  classical
  ext a inp
  simp [reversedMixedCoefficient,shiftedWalsh,diagonalRowCoefficient,Matrix.mul_apply,mul_comm]

theorem shiftedWalsh_gram (j : WalshIndex k) : (shiftedWalsh j).transpose * shiftedWalsh j=1 := by
  classical
  ext i l
  simp only [shiftedWalsh,Matrix.mul_apply,Matrix.transpose_apply,walsh_row_inner,
    Matrix.one_apply,add_left_cancel_iff]

theorem diagonalRowCoefficient_norm_sq_le (U : Matrix (WalshIndex k) D ℝ)
    (mu : ℝ) (hmu : 0≤mu) (hell : ∀ i, rowLeverage U i≤mu) :
    ‖diagonalRowCoefficient U‖^2≤mu := by
  have hf := Matrix.l2_opNorm_conjTranspose_mul_self (diagonalRowCoefficient U).transpose
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose,
    diagonalRowCoefficient_gram,Matrix.l2_opNorm_diagonal] at hf
  have ht : ‖(diagonalRowCoefficient U).transpose‖=‖diagonalRowCoefficient U‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (diagonalRowCoefficient U)
  have hd : ‖rowLeverage U‖≤mu := by
    apply (pi_norm_le_iff_of_nonneg hmu).2
    intro i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (rowLeverage_nonneg U i)] using hell i
  rw [ht] at hf
  nlinarith

theorem reversedMixedCoefficient_norm_sq_le (j : WalshIndex k) (U : Matrix (WalshIndex k) D ℝ)
    (mu : ℝ) (hmu : 0≤mu) (hell : ∀ i, rowLeverage U i≤mu) :
    ‖reversedMixedCoefficient j U‖^2≤mu := by
  have hW := isometry_norm_le_one (shiftedWalsh j) (shiftedWalsh_gram j)
  have hnorm : ‖reversedMixedCoefficient j U‖≤‖diagonalRowCoefficient U‖ := by
    rw [reversedMixedCoefficient_factor]
    exact (Matrix.l2_opNorm_mul _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right hW (norm_nonneg (diagonalRowCoefficient U)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (diagonalRowCoefficient_norm_sq_le U mu hmu hell)

end
end SRHT.SmallRows
