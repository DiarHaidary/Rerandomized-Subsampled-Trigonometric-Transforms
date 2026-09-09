import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace SparseFock

namespace FiniteL2

open scoped BigOperators

variable (Omega I : Type*) [Fintype Omega] [Fintype I]

/-- A completely explicit orthonormal basis of a finite weighted real `L₂`
space.  `reconstruction` records completeness, not merely orthonormality. -/
structure WeightedONBasis where
  weight : Omega → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  sum_weight : ∑ x, weight x = 1
  basis : I → Omega → ℝ
  orthonormal_same : ∀ i,
    (∑ x, weight x * basis i x * basis i x) = 1
  orthonormal_ne : ∀ i j, i ≠ j →
    (∑ x, weight x * basis i x * basis j x) = 0
  reconstruction : ∀ (f : Omega → ℝ) (x : Omega),
    f x = ∑ i, (∑ y, weight y * basis i y * f y) * basis i x
  vacuum : I
  vacuum_eq_one : ∀ x, basis vacuum x = 1

variable {Omega I} [DecidableEq I]

namespace WeightedONBasis

variable (B : WeightedONBasis Omega I)

noncomputable def expect (f : Omega → ℝ) : ℝ :=
  ∑ x, B.weight x * f x

noncomputable def coeff (i : I) (f : Omega → ℝ) : ℝ :=
  ∑ x, B.weight x * B.basis i x * f x

theorem coeff_basis (i j : I) :
    B.coeff i (B.basis j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simpa [coeff, mul_assoc] using B.orthonormal_same i
  · simp only [h, ↓reduceIte]
    simpa [coeff, mul_assoc] using B.orthonormal_ne i j h

theorem reconstruct (f : Omega → ℝ) (x : Omega) :
    f x = ∑ i, B.coeff i f * B.basis i x := by
  simpa [coeff] using B.reconstruction f x

theorem expect_one : B.expect (fun _ => 1) = 1 := by
  simpa [expect] using B.sum_weight

theorem coeff_mul_sum (i : I) (a : Omega → ℝ) (c : I → ℝ) :
    B.coeff i (fun x => a x * ∑ j, c j * B.basis j x) =
      ∑ j, c j * B.coeff i (fun x => a x * B.basis j x) := by
  simp only [coeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem coeff_sum {K : Type*} [Fintype K] (i : I) (f : K → Omega → ℝ) :
    B.coeff i (fun x => ∑ k, f k x) = ∑ k, B.coeff i (f k) := by
  simp only [coeff, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Matrix of multiplication by a scalar observable in the finite ON basis. -/
noncomputable def mulOp (a : Omega → ℝ) : Matrix I I ℝ :=
  fun i j => B.coeff i (fun x => a x * B.basis j x)

theorem mulOp_one : B.mulOp (fun _ => 1) = 1 := by
  classical
  ext i j
  simp [mulOp, coeff_basis, Matrix.one_apply]

theorem mulOp_mul (a b : Omega → ℝ) :
    B.mulOp a * B.mulOp b = B.mulOp (fun x => a x * b x) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [mulOp]
  calc
    (∑ k, B.coeff i (fun x => a x * B.basis k x) *
        B.coeff k (fun x => b x * B.basis j x)) =
        ∑ k, B.coeff k (fun x => b x * B.basis j x) *
          B.coeff i (fun x => a x * B.basis k x) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = B.coeff i (fun x => a x *
          ∑ k, B.coeff k (fun y => b y * B.basis j y) * B.basis k x) := by
            symm
            exact B.coeff_mul_sum i a
              (fun k => B.coeff k (fun y => b y * B.basis j y))
    _ = B.coeff i (fun x => a x * (b x * B.basis j x)) := by
            congr 1
            funext x
            rw [← B.reconstruct (fun y => b y * B.basis j y) x]
    _ = B.coeff i (fun x => (a x * b x) * B.basis j x) := by
            congr 2
            funext x
            ring

theorem mulOp_pow (a : Omega → ℝ) (k : ℕ) :
    B.mulOp a ^ k = B.mulOp (fun x => a x ^ k) := by
  classical
  induction k with
  | zero => exact B.mulOp_one.symm
  | succ k ih =>
      rw [pow_succ, ih, B.mulOp_mul]
      congr 1

theorem vacuum_mulOp (a : Omega → ℝ) :
    B.mulOp a B.vacuum B.vacuum = B.expect a := by
  simp [mulOp, coeff, expect, B.vacuum_eq_one]

theorem vacuum_moment (a : Omega → ℝ) (k : ℕ) :
    (B.mulOp a ^ k) B.vacuum B.vacuum = B.expect (fun x => a x ^ k) := by
  rw [B.mulOp_pow]
  exact B.vacuum_mulOp _

section MatrixValued

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Matrix-valued multiplication operator.  Its basis is the external matrix
index paired with the finite `L₂` basis index. -/
noncomputable def matrixMulOp (M : Omega → Matrix A A ℝ) :
    Matrix (A × I) (A × I) ℝ :=
  fun out inp =>
    B.coeff out.2 (fun x => M x out.1 inp.1 * B.basis inp.2 x)

theorem matrixMulOp_one :
    B.matrixMulOp (fun _ => (1 : Matrix A A ℝ)) = 1 := by
  classical
  ext out inp
  rcases out with ⟨a, i⟩
  rcases inp with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simp [matrixMulOp, Matrix.one_apply, B.coeff_basis]
  · simp [matrixMulOp, coeff, Matrix.one_apply, hab]

theorem matrixMulOp_mul (M N : Omega → Matrix A A ℝ) :
    B.matrixMulOp M * B.matrixMulOp N =
      B.matrixMulOp (fun x => M x * N x) := by
  classical
  ext out inp
  rcases out with ⟨a, i⟩
  rcases inp with ⟨c, j⟩
  rw [Matrix.mul_apply]
  simp only [matrixMulOp, Fintype.sum_prod_type, Matrix.mul_apply]
  change (∑ b, ∑ k,
      B.coeff i (fun x => M x a b * B.basis k x) *
        B.coeff k (fun x => N x b c * B.basis j x)) =
    B.coeff i (fun x => (∑ b, M x a b * N x b c) * B.basis j x)
  have hfun :
      (fun x => (∑ b, M x a b * N x b c) * B.basis j x) =
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
            exact B.coeff_mul_sum i (fun x => M x a b)
              (fun k => B.coeff k (fun y => N y b c * B.basis j y))
    _ = B.coeff i (fun x => M x a b * (N x b c * B.basis j x)) := by
            congr 1
            funext x
            rw [← B.reconstruct (fun y => N y b c * B.basis j y) x]
    _ = B.coeff i (fun x => (M x a b * N x b c) * B.basis j x) := by
            congr 2
            funext x
            ring

theorem matrixMulOp_pow (M : Omega → Matrix A A ℝ) (k : ℕ) :
    B.matrixMulOp M ^ k = B.matrixMulOp (fun x => M x ^ k) := by
  classical
  induction k with
  | zero => exact (B.matrixMulOp_one (A := A)).symm
  | succ k ih =>
      rw [pow_succ, ih, B.matrixMulOp_mul]
      congr 1

theorem matrix_vacuum_moment (M : Omega → Matrix A A ℝ) (k : ℕ) :
    (∑ a, (B.matrixMulOp M ^ k) (a, B.vacuum) (a, B.vacuum)) =
      B.expect (fun x => Matrix.trace (M x ^ k)) := by
  rw [B.matrixMulOp_pow]
  simp only [matrixMulOp, coeff, B.vacuum_eq_one, mul_one, expect, Matrix.trace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  simp

end MatrixValued

end WeightedONBasis

end FiniteL2

end SparseFock
