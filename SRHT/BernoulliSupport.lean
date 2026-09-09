import SRHT.BernoulliVariance
import Mathlib.Data.Finset.Powerset

namespace SRHT.BernoulliSupport
open SparseFock BinaryBasis BernoulliVariance
open scoped BigOperators
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def support (x : I → ZMod 2) : Finset I := Finset.univ.filter (fun i => x i ≠ 0)
def bitsOf (S : Finset I) (i : I) : ZMod 2 := if i ∈ S then 1 else 0

@[simp] theorem mem_support (x : I → ZMod 2) (i : I) :
    i ∈ support x ↔ x i ≠ 0 := by simp [support]

@[simp] theorem support_bitsOf (S : Finset I) : support (bitsOf S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [bitsOf, h]

@[simp] theorem bitsOf_support (x : I → ZMod 2) : bitsOf (support x) = x := by
  funext i
  rcases bit_cases (x i) with h | h <;> simp [bitsOf, h]

def supportEquiv : (I → ZMod 2) ≃ Finset I where
  toFun := support
  invFun := bitsOf
  left_inv := bitsOf_support
  right_inv := support_bitsOf

def law (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (Finset I) where
  weight S := (iidLaw p hp hp1).weight (bitsOf S)
  weight_nonneg S := (iidLaw p hp hp1).weight_nonneg _
  sum_weight := by
    calc
      _ = ∑ x : I → ZMod 2, (iidLaw p hp hp1).weight x :=
        supportEquiv.symm.sum_comp _
      _ = 1 := (iidLaw p hp hp1).sum_weight

theorem expect_law (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : Finset I → ℝ) :
    (law (I := I) p hp hp1).expect f =
      (iidLaw p hp hp1).expect (fun x => f (support x)) := by
  unfold FiniteLaw.expect
  have h := supportEquiv.sum_comp
    (fun S => (iidLaw p hp hp1).weight (bitsOf S) * f S)
  simpa [law, supportEquiv] using h.symm

theorem bitsOf_map (π : Equiv.Perm I) (S : Finset I) (i : I) :
    bitsOf (S.map π.toEmbedding) i = bitsOf S (π.symm i) := by
  simp [bitsOf]

theorem law_exchangeable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (π : Equiv.Perm I) (S : Finset I) :
    (law p hp hp1).weight (S.map π.toEmbedding) = (law p hp hp1).weight S := by
  change (∏ i, mass p (bitsOf (S.map π.toEmbedding) i)) =
    ∏ i, mass p (bitsOf S i)
  simp_rw [bitsOf_map]
  exact π.symm.prod_comp (fun i => mass p (bitsOf S i))

theorem count_eq_card_support (x : I → ZMod 2) :
    count x = ((support x).card : ℝ) := by
  simp [count, support, bitValue, Finset.card_filter, Nat.cast_sum]

theorem mean_centered_support (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (law (I := I) p hp hp1).expect
      (fun S => (S.card : ℝ) - (Fintype.card I : ℝ)*p) = 0 := by
  rw [expect_law]
  simp_rw [← count_eq_card_support]
  exact centered_count_mean hp hp1

theorem variance_support (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (law (I := I) p hp hp1).expect
      (fun S => ((S.card : ℝ) - (Fintype.card I : ℝ)*p)^2) =
      (Fintype.card I : ℝ)*p*(1-p) := by
  rw [expect_law]
  simp_rw [← count_eq_card_support]
  exact centered_count_variance hp hp1

theorem support_deviation_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (law (I := I) p hp hp1).expect
      (fun S => max ((S.card : ℝ)-(Fintype.card I : ℝ)*p) 0)^2 ≤
      ((Fintype.card I : ℝ)*p*(1-p))/4 := by
  have h := positivePart_sq_le_quarter_variance (law (I := I) p hp hp1)
    (fun S => (S.card : ℝ)-(Fintype.card I : ℝ)*p)
    (mean_centered_support p hp hp1)
  rwa [variance_support] at h

end
end SRHT.BernoulliSupport
