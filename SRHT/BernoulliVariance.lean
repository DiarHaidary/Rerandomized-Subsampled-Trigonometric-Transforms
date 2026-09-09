import SRHT.BinaryBasis
import Mathlib.Tactic

namespace SRHT.BernoulliVariance
open SparseFock
open BinaryBasis
open scoped BigOperators
noncomputable section

theorem expect_sum {Ω J : Type*} [Fintype Ω] [Fintype J]
    (μ : FiniteLaw Ω) (f : J → Ω → ℝ) :
    μ.expect (fun ω => ∑ j, f j ω) = ∑ j, μ.expect (f j) := by
  simp_rw [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem sq_expect_le_expect_sq {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect f ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) := by
  have h := μ.expect_nonneg (fun ω => sq_nonneg (f ω - μ.expect f))
  have heq : μ.expect (fun ω => (f ω - μ.expect f)^2) =
      μ.expect (fun ω => f ω^2) - μ.expect f^2 := by
    calc
      _ = μ.expect (fun ω => f ω^2 - 2 * μ.expect f * f ω + μ.expect f^2) := by
        apply μ.expect_congr
        intro ω
        ring
      _ = _ := by
        rw [μ.expect_add, μ.expect_sub, μ.expect_smul, μ.expect_const]
        ring
  rw [heq] at h
  linarith

theorem positivePart_sq_le_quarter_variance {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) (hmean : μ.expect f = 0) :
    μ.expect (fun ω => max (f ω) 0)^2 ≤ μ.expect (fun ω => f ω^2)/4 := by
  have heq : 2 * μ.expect (fun ω => max (f ω) 0) =
      μ.expect (fun ω => |f ω|) := by
    calc
      _ = μ.expect (fun ω => 2 * max (f ω) 0) := (μ.expect_smul _ _).symm
      _ = μ.expect (fun ω => |f ω| + f ω) := by
        apply μ.expect_congr
        intro ω
        by_cases h : 0 ≤ f ω
        · rw [max_eq_left h, abs_of_nonneg h]; ring
        · rw [max_eq_right (le_of_not_ge h), abs_of_neg (lt_of_not_ge h)]; ring
      _ = _ := by rw [μ.expect_add, hmean, add_zero]
  have h := sq_expect_le_expect_sq μ (fun ω => |f ω|)
  simp only [sq_abs] at h
  rw [← heq] at h
  nlinarith

variable {I : Type*} [Fintype I] [DecidableEq I]

def iidLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (I → ZMod 2) :=
  FiniteLaw.independentProduct (fun _ => BinaryBasis.law p hp hp1)

def count (x : I → ZMod 2) : ℝ := ∑ i, bitValue (x i)

theorem local_mean {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (BinaryBasis.law p hp hp1).expect (fun z => bitValue z - p) = 0 := by
  simp [BinaryBasis.law, FiniteLaw.expect, mass, bitValue]
  ring

theorem local_variance {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (BinaryBasis.law p hp hp1).expect (fun z => (bitValue z - p)^2) = p*(1-p) := by
  simp [BinaryBasis.law, FiniteLaw.expect, mass, bitValue]
  ring

theorem centered_count_eq (p : ℝ) (x : I → ZMod 2) :
    count x - (Fintype.card I : ℝ)*p = ∑ i, (bitValue (x i) - p) := by
  simp [count, Finset.sum_sub_distrib]

theorem centered_count_mean {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (iidLaw (I := I) p hp hp1).expect
      (fun x => count x - (Fintype.card I : ℝ)*p) = 0 := by
  simp_rw [centered_count_eq]
  rw [expect_sum]
  have h (i : I) : (iidLaw p hp hp1).expect (fun x => bitValue (x i)-p) = 0 := by
    rw [iidLaw, FiniteLaw.expect_independentProduct_apply
      (fun _ : I => BinaryBasis.law p hp hp1) i (fun z => bitValue z-p)]
    exact local_mean hp hp1
  simp_rw [h]
  simp

theorem coordinate_covariance {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (i j : I) :
    (iidLaw p hp hp1).expect (fun x => (bitValue (x i)-p)*(bitValue (x j)-p)) =
      if i = j then p*(1-p) else 0 := by
  by_cases h : i = j
  · subst j
    simp only [if_true, ← pow_two]
    rw [iidLaw, FiniteLaw.expect_independentProduct_apply
      (fun _ : I => BinaryBasis.law p hp hp1) i (fun z => (bitValue z-p)^2)]
    exact local_variance hp hp1
  · rw [if_neg h]
    have hf := FiniteLaw.expect_independentProduct_factorizes_on
      (fun _ : I => BinaryBasis.law p hp hp1) {i,j}
      (fun _ z => bitValue z-p)
    simpa [Finset.prod_insert, h, local_mean hp hp1, iidLaw] using hf

theorem centered_count_variance {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (iidLaw (I := I) p hp hp1).expect
      (fun x => (count x - (Fintype.card I : ℝ)*p)^2) =
      (Fintype.card I : ℝ)*p*(1-p) := by
  have heq (x : I → ZMod 2) :
      (count x - (Fintype.card I : ℝ)*p)^2 =
        ∑ i, ∑ j, (bitValue (x i)-p)*(bitValue (x j)-p) := by
    rw [centered_count_eq, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [heq, expect_sum, coordinate_covariance hp hp1]
  simp
  ring

/-- The retention coefficient in the finite nested coupling is uniformly
bounded below, including M=1 and M=n-1. -/
theorem retention_lower {n M : ℕ} (hM : 0 < M) (hMn : M < n)
    {a : ℝ} (ha : 0 ≤ a)
    (ha2 : a^2 ≤ ((M : ℝ)*((n : ℝ)-M)/n)/4) :
    (1/4 : ℝ) ≤ 1 - a / ((M : ℝ)*((n : ℝ)-M)/n) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hgap : (1 : ℝ) ≤ (n : ℝ)-M := by
    have h : (M : ℝ)+1 ≤ n := by exact_mod_cast hMn
    linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  let v : ℝ := (M : ℝ)*((n : ℝ)-M)/n
  have hv : (1/2 : ℝ) ≤ v := by
    apply (le_div_iff₀ hn0).mpr
    have hprod := mul_nonneg (sub_nonneg.mpr hM1) (sub_nonneg.mpr hgap)
    nlinarith
  have hv0 : 0 < v := by linarith
  have hav : a ≤ 3*v/4 := by
    change a^2 ≤ v/4 at ha2
    nlinarith [sq_nonneg (v-1/2)]
  change 1/4 ≤ 1 - a/v
  have hdiv : a/v ≤ 3/4 := (div_le_iff₀ hv0).mpr (by linarith)
  linarith

end
end SRHT.BernoulliVariance
