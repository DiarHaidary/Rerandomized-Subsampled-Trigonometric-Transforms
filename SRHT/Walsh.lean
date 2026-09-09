import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! Concrete normalized Walsh matrices on the elementary abelian group `(ZMod 2)^k`. -/

open scoped BigOperators Matrix

namespace SRHT

noncomputable section

/-- The row and column group for a Walsh transform of order `2^k`. -/
abbrev WalshIndex (k : ℕ) := Fin k → ZMod 2

@[simp] theorem walshIndex_card (k : ℕ) : Fintype.card (WalshIndex k) = 2 ^ k := by
  simp [WalshIndex]

/-- The real sign associated with a bit. -/
def bitSign (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

@[simp] theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]
@[simp] theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  have cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  rcases cases a with rfl | rfl <;> rcases cases b with rfl | rfl <;>
    simp [bitSign, hone]

@[simp] theorem bitSign_sq (a : ZMod 2) : bitSign a ^ 2 = 1 := by
  unfold bitSign
  split <;> norm_num

@[simp] theorem bitSign_mul_self (a : ZMod 2) : bitSign a * bitSign a = 1 := by
  simpa only [pow_two] using bitSign_sq a

theorem bitSign_sum_mul (a : ZMod 2) :
    (∑ b : ZMod 2, bitSign (a * b)) = if a = 0 then 2 else 0 := by
  have cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases cases a with rfl | rfl
  · simp [bitSign]
  · rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide]
    norm_num [bitSign]

/-- The unnormalized real Walsh character. -/
def walshChar {k : ℕ} (a b : WalshIndex k) : ℝ :=
  ∏ i, bitSign (a i * b i)

theorem walshChar_comm {k : ℕ} (a b : WalshIndex k) :
    walshChar a b = walshChar b a := by
  simp [walshChar, mul_comm]

@[simp] theorem walshChar_zero_left {k : ℕ} (b : WalshIndex k) :
    walshChar 0 b = 1 := by simp [walshChar]

@[simp] theorem walshChar_zero_right {k : ℕ} (a : WalshIndex k) :
    walshChar a 0 = 1 := by simp [walshChar]

theorem walshChar_add_left {k : ℕ} (a b c : WalshIndex k) :
    walshChar (a + b) c = walshChar a c * walshChar b c := by
  simp only [walshChar, Pi.add_apply, add_mul, bitSign_add, Finset.prod_mul_distrib]

theorem walshChar_add_right {k : ℕ} (a b c : WalshIndex k) :
    walshChar a (b + c) = walshChar a b * walshChar a c := by
  simp only [walshChar, Pi.add_apply, mul_add, bitSign_add, Finset.prod_mul_distrib]

@[simp] theorem walshChar_sq {k : ℕ} (a b : WalshIndex k) : walshChar a b ^ 2 = 1 := by
  simp [walshChar, ← Finset.prod_pow]

@[simp] theorem walshChar_mul_self {k : ℕ} (a b : WalshIndex k) :
    walshChar a b * walshChar a b = 1 := by
  simpa only [pow_two] using walshChar_sq a b

@[simp] theorem walshIndex_add_self {k : ℕ} (a : WalshIndex k) : a + a = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (a i)

theorem walshIndex_add_eq_zero_iff {k : ℕ} (a b : WalshIndex k) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun z : WalshIndex k => z + b) h
    simpa only [add_assoc, walshIndex_add_self, add_zero, zero_add] using this
  · rintro rfl
    exact walshIndex_add_self a

theorem walshChar_sum {k : ℕ} (a : WalshIndex k) :
    (∑ b, walshChar a b) = if a = 0 then (Fintype.card (WalshIndex k) : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha]
    unfold walshChar
    change (∑ b : Fin k → ZMod 2, ∏ i : Fin k, bitSign (a i * b i)) = 0
    rw [← Fintype.prod_sum (fun i : Fin k => fun b : ZMod 2 => bitSign (a i * b))]
    simp_rw [bitSign_sum_mul]
    have hex : ∃ i, a i ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem walshChar_orthogonal {k : ℕ} (a b : WalshIndex k) :
    (∑ j, walshChar a j * walshChar b j) =
      if a = b then (Fintype.card (WalshIndex k) : ℝ) else 0 := by
  simp_rw [← walshChar_add_left]
  rw [walshChar_sum]
  simp only [walshIndex_add_eq_zero_iff]

/-- The normalized symmetric Walsh-Hadamard matrix. -/
def walshMatrix (k : ℕ) : Matrix (WalshIndex k) (WalshIndex k) ℝ :=
  fun a b => (Real.sqrt (Fintype.card (WalshIndex k) : ℝ))⁻¹ * walshChar a b

theorem walshMatrix_apply (k : ℕ) (a b : WalshIndex k) :
    walshMatrix k a b = (Real.sqrt (2 ^ k : ℝ))⁻¹ * walshChar a b := by
  simp [walshMatrix]

@[simp] theorem walshMatrix_transpose (k : ℕ) : (walshMatrix k)ᵀ = walshMatrix k := by
  ext a b
  exact congrArg ((Real.sqrt (Fintype.card (WalshIndex k) : ℝ))⁻¹ * ·)
    (walshChar_comm b a)

theorem walshMatrix_mul_self (k : ℕ) : walshMatrix k * walshMatrix k = 1 := by
  classical
  have hn : (0 : ℝ) < Fintype.card (WalshIndex k) := by
    exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card (WalshIndex k) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hn)
  ext a b
  simp only [Matrix.mul_apply, walshMatrix, Matrix.one_apply]
  conv_lhs => arg 2; ext j; rw [walshChar_comm j b]
  have hsum :
      (∑ j, (Real.sqrt (Fintype.card (WalshIndex k) : ℝ))⁻¹ * walshChar a j *
        ((Real.sqrt (Fintype.card (WalshIndex k) : ℝ))⁻¹ * walshChar b j)) =
      (Real.sqrt (Fintype.card (WalshIndex k) : ℝ))⁻¹ ^ 2 *
        (∑ j, walshChar a j * walshChar b j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, walshChar_orthogonal]
  split_ifs with hab
  · have hs2 := Real.sq_sqrt hn.le
    field_simp
    exact hs2.symm
  · simp

@[simp] theorem walshMatrix_transpose_mul (k : ℕ) :
    (walshMatrix k)ᵀ * walshMatrix k = 1 := by
  rw [walshMatrix_transpose, walshMatrix_mul_self]

@[simp] theorem walshMatrix_mul_transpose (k : ℕ) :
    walshMatrix k * (walshMatrix k)ᵀ = 1 := by
  rw [walshMatrix_transpose, walshMatrix_mul_self]

/-- Scalar row orthogonality, useful without matrix multiplication notation. -/
theorem walshMatrix_orthogonal {k : ℕ} (a b : WalshIndex k) :
    (∑ j, walshMatrix k a j * walshMatrix k b j) = if a = b then 1 else 0 := by
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
    congrArg (fun A : Matrix (WalshIndex k) (WalshIndex k) ℝ => A a b)
      (walshMatrix_mul_transpose k)

theorem walshChar_mul_matrix {k : ℕ} (a b j : WalshIndex k) :
    walshChar a j * walshMatrix k b j = walshMatrix k (a + b) j := by
  simp only [walshMatrix, walshChar_add_left]
  ring

end

end SRHT
