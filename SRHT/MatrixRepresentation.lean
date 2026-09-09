import SparseFockFormal.FiniteL2
import SRHT.MatrixNorm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! Exact finite multiplication representations, including positivity. -/
namespace SRHT.MatrixRepresentation
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open SparseFock.FiniteL2

variable {Ω I A C D : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
variable [Fintype A] [Fintype C] [Fintype D]
variable [DecidableEq A] [DecidableEq C] [DecidableEq D]

def rect (B : WeightedONBasis Ω I) (M : Ω → Matrix A C ℝ) :
    Matrix (A × I) (C × I) ℝ :=
  fun out inp => B.coeff out.2 (fun x => M x out.1 inp.1 * B.basis inp.2 x)

theorem rect_square (B : WeightedONBasis Ω I) (M : Ω → Matrix A A ℝ) :
    rect B M = B.matrixMulOp M := rfl

theorem rect_transpose (B : WeightedONBasis Ω I) (M : Ω → Matrix A C ℝ) :
    (rect B M).transpose = rect B (fun x => (M x).transpose) := by
  ext a c
  simp only [rect, Matrix.transpose_apply, WeightedONBasis.coeff]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem rect_mul (B : WeightedONBasis Ω I)
    (M : Ω → Matrix A C ℝ) (N : Ω → Matrix C D ℝ) :
    rect B M * rect B N = rect B (fun x => M x * N x) := by
  ext out inp
  rcases out with ⟨a,i⟩
  rcases inp with ⟨c,j⟩
  rw [Matrix.mul_apply]
  simp only [rect, Fintype.sum_prod_type, Matrix.mul_apply]
  have hfun : (fun x => (∑ b, M x a b * N x b c) * B.basis j x) =
      (fun x => ∑ b, (M x a b * N x b c) * B.basis j x) := by
    funext x
    rw [Finset.sum_mul]
  rw [hfun, B.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ k, B.coeff i (fun x => M x a b * B.basis k x) *
      B.coeff k (fun x => N x b c * B.basis j x)) =
        ∑ k, B.coeff k (fun x => N x b c * B.basis j x) *
          B.coeff i (fun x => M x a b * B.basis k x) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = B.coeff i (fun x => M x a b *
          ∑ k, B.coeff k (fun y => N y b c * B.basis j y) * B.basis k x) := by
            symm
            exact B.coeff_mul_sum i _ _
    _ = B.coeff i (fun x => M x a b * (N x b c * B.basis j x)) := by
            congr 1
            funext x
            rw [← B.reconstruct (fun y => N y b c * B.basis j y) x]
    _ = B.coeff i (fun x => (M x a b * N x b c) * B.basis j x) := by
            congr 2
            funext x
            ring

theorem rect_gram (B : WeightedONBasis Ω I) (W : Ω → Matrix A C ℝ) :
    (rect B W).transpose * rect B W =
      B.matrixMulOp (fun x => (W x).transpose * W x) := by
  rw [rect_transpose, rect_mul, rect_square]

theorem matrixMulOp_sum {J : Type*} [Fintype J]
    (B : WeightedONBasis Ω I) (M : J → Ω → Matrix A A ℝ) :
    B.matrixMulOp (fun x => ∑ j, M j x) = ∑ j, B.matrixMulOp (M j) := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem matrixMulOp_smul (B : WeightedONBasis Ω I)
    (M : Ω → Matrix A A ℝ) (r : ℝ) :
    B.matrixMulOp (fun x => r • M x) = r • B.matrixMulOp M := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrixMulOp_sub (B : WeightedONBasis Ω I)
    (M N : Ω → Matrix A A ℝ) :
    B.matrixMulOp (fun x => M x - N x) = B.matrixMulOp M - B.matrixMulOp N := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]

def evaluation (B : WeightedONBasis Ω I) (x : Ω) : Matrix A (A × I) ℝ :=
  fun a b => if a = b.1 then B.basis b.2 x else 0

theorem evaluation_sandwich (B : WeightedONBasis Ω I)
    (M : Matrix A A ℝ) (x : Ω) (a b : A × I) :
    (((evaluation B x).transpose * M * evaluation B x) : Matrix (A × I) (A × I) ℝ) a b =
      B.basis a.2 x * M a.1 b.1 * B.basis b.2 x := by
  simp [Matrix.mul_apply, evaluation, Matrix.transpose_apply]

theorem matrixMulOp_as_sum (B : WeightedONBasis Ω I) (M : Ω → Matrix A A ℝ) :
    B.matrixMulOp M = ∑ x, B.weight x •
      ((evaluation B x).transpose * M x * evaluation B x) := by
  ext a b
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, evaluation_sandwich]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrixMulOp_positive (B : WeightedONBasis Ω I) (M : Ω → Matrix A A ℝ)
    (hM : ∀ x, (M x).PosSemidef) : (B.matrixMulOp M).PosSemidef := by
  rw [matrixMulOp_as_sum]
  apply Matrix.posSemidef_sum
  intro x _
  apply Matrix.PosSemidef.smul _ (B.weight_nonneg x)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hM x).conjTranspose_mul_mul_same (evaluation B x)

theorem matrixMulOp_symmetric (B : WeightedONBasis Ω I) (M : Ω → Matrix A A ℝ)
    (hM : ∀ x, (M x).transpose = M x) : (B.matrixMulOp M).transpose = B.matrixMulOp M := by
  change (rect B M).transpose = rect B M
  rw [rect_transpose]
  congr 1
  funext x
  exact hM x

end
end SRHT.MatrixRepresentation
