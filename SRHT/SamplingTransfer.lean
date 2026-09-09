import SRHT.SamplingConditional
import SparseFockFormal.TracePowerConvexity
import SparseFockFormal.MatrixTail
import Mathlib.Tactic

namespace SRHT.Sampling
open SparseFock SparseFock.SparseIIDTransfer SparseFock.TracePowerConvexity
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def excess (μ : FiniteLaw (Finset J)) (M : ℕ) : ℝ :=
  μ.expect (fun B => max ((B.card : ℝ) - M) 0)

def retention (μ : FiniteLaw (Finset J)) (M : ℕ) : ℝ :=
  1 - excess μ M * (Fintype.card J : ℝ) /
    ((M : ℝ) * ((Fintype.card J : ℝ) - M))

theorem deficit_eq_excess (μ : FiniteLaw (Finset J)) (M : ℕ)
    (hmean : μ.expect (fun B => (B.card : ℝ) - M) = 0) :
    μ.expect (fun B => max ((M : ℝ) - B.card) 0) = excess μ M := by
  have he (B : Finset J) : max ((M : ℝ) - B.card) 0 =
      max ((B.card : ℝ) - M) 0 - ((B.card : ℝ) - M) := by
    by_cases h : (M : ℝ) ≤ B.card
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
      ring
    · have hh := le_of_lt (lt_of_not_ge h)
      rw [max_eq_left (sub_nonneg.mpr hh), max_eq_right (sub_nonpos.mpr hh)]
      ring
  simp_rw [he]
  rw [μ.expect_sub, hmean, sub_zero]
  rfl

theorem conditional_coefficient (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM0 : 0 < M) (hMn : M < Fintype.card J)
    (hmean : μ.expect (fun B => (B.card : ℝ) - M) = 0)
    (T : Exact J M) (j : J) :
    ((Fintype.card J : ℝ) / M) * inclusion μ hMn.le T j - 1 =
      retention μ M * (((Fintype.card J : ℝ) / M) * site T.val j - 1) := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hnm : ((Fintype.card J : ℝ) - M) ≠ 0 := by
    have hh : (M : ℝ) < Fintype.card J := by exact_mod_cast hMn
    linarith
  by_cases hj : j ∈ T.val
  · rw [inclusion_inside μ hμ hMn.le hM0 T j hj, deficit_eq_excess μ M hmean]
    simp only [site, hj, ite_true, mul_one, retention]
    field_simp
    <;> ring
  · rw [inclusion_outside μ hμ hMn.le hMn T j hj]
    simp only [site, hj, ite_false, mul_zero, zero_sub, retention, excess]
    field_simp
    <;> ring

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The centered sampled sum, on the actual vector space containing the
effects.  For matrix effects summing to I, this is the sampled Gram error. -/
def centeredSum (α : ℝ) (A : J → E) (B : Finset J) : E :=
  ∑ j, (α * site B j - 1) • A j

theorem centeredSum_eq (α : ℝ) (A : J → E) (B : Finset J) :
    centeredSum α A B = α • (∑ j ∈ B, A j) - ∑ j, A j := by
  simp only [centeredSum, sub_smul, one_smul, Finset.sum_sub_distrib,
    mul_smul, site]
  congr 1
  rw [Finset.smul_sum]
  simp

/-- The exact finite conditional barycenter.  It is proved from the explicit
nested coupling and same-region inclusion probabilities. -/
theorem conditional_barycenter (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM0 : 0 < M) (hMn : M < Fintype.card J)
    (hmean : μ.expect (fun B => (B.card : ℝ) - M) = 0)
    (A : J → E) (T : Exact J M) :
    barycenter (conditionalLaw μ hMn.le T) (centeredSum ((Fintype.card J : ℝ) / M) A) =
      retention μ M • centeredSum ((Fintype.card J : ℝ) / M) A T.val := by
  simp only [barycenter, centeredSum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_smul]
  congr 1
  have he :
      (∑ B, (conditionalLaw μ hMn.le T).weight B *
        (((Fintype.card J : ℝ) / M) * site B j - 1)) =
      ((Fintype.card J : ℝ) / M) * inclusion μ hMn.le T j - 1 := by
    change (conditionalLaw μ hMn.le T).expect
      (fun B => ((Fintype.card J : ℝ) / M) * site B j - 1) = _
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_smul, FiniteLaw.expect_const]
    rfl
  rw [he]
  exact conditional_coefficient μ hμ hM0 hMn hmean T j

/-- Jensen transfer for any convex functional on the effect vector space. -/
theorem centeredSum_convex_transfer (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM0 : 0 < M) (hMn : M < Fintype.card J)
    (hmean : μ.expect (fun B => (B.card : ℝ) - M) = 0)
    (A : J → E) (Φ : E → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) :
    (∑ T : Exact J M, (1 / (Fintype.card (Exact J M) : ℝ)) *
      Φ (retention μ M • centeredSum ((Fintype.card J : ℝ) / M) A T.val)) ≤
      μ.expect (fun B => Φ (centeredSum ((Fintype.card J : ℝ) / M) A B)) := by
  calc
    _ ≤ ∑ T : Exact J M, (1 / (Fintype.card (Exact J M) : ℝ)) *
        (conditionalLaw μ hMn.le T).expect
          (fun B => Φ (centeredSum ((Fintype.card J : ℝ) / M) A B)) := by
      apply Finset.sum_le_sum
      intro T _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← conditional_barycenter μ hμ hM0 hMn hmean A T]
      exact finite_jensen _ _ Φ hΦ
    _ = _ := by
      simp only [FiniteLaw.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B _
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, conditionalLaw_mixture μ hμ hMn.le]

section TraceMoment

variable {d : ℕ}

theorem traceEvenPower_smul (q : ℕ) (c : ℝ) (X : SymmetricMatrix d) :
    traceEvenPower q (c • X) = c ^ (2*q) * traceEvenPower q X := by
  simp only [traceEvenPower, Submodule.coe_smul_of_tower, smul_pow, Matrix.trace_smul,
    smul_eq_mul]

theorem traceEvenPower_nonneg (q : ℕ) (X : SymmetricMatrix d) :
    0 ≤ traceEvenPower q X := by
  apply MatrixTail.trace_even_pow_nonneg
  have hx : (X : Matrix (Fin d) (Fin d) ℝ).transpose = X := X.property
  change (X : Matrix (Fin d) (Fin d) ℝ).conjTranspose = X
  ext i j
  simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using
    congrFun (congrFun hx i) j

def fixedMoment (M q : ℕ) (A : J → SymmetricMatrix d) : ℝ :=
  ∑ T : Exact J M, (1 / (Fintype.card (Exact J M) : ℝ)) *
    traceEvenPower q (centeredSum ((Fintype.card J : ℝ) / M) A T.val)

def supportMoment (μ : FiniteLaw (Finset J)) (M q : ℕ) (A : J → SymmetricMatrix d) : ℝ :=
  μ.expect (fun B => traceEvenPower q (centeredSum ((Fintype.card J : ℝ) / M) A B))

theorem fixedMoment_nonneg (M q : ℕ) (A : J → SymmetricMatrix d) :
    0 ≤ fixedMoment M q A :=
  Finset.sum_nonneg fun T _ => mul_nonneg (by positivity) (traceEvenPower_nonneg q _)

/-- Exact scaled trace-moment transfer, valid for any exchangeable support
law of mean size M and arbitrary noncommuting symmetric matrix effects. -/
theorem scaled_trace_moment_transfer (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM0 : 0 < M) (hMn : M < Fintype.card J)
    (hmean : μ.expect (fun B => (B.card : ℝ) - M) = 0)
    (q : ℕ) (A : J → SymmetricMatrix d) :
    retention μ M ^ (2*q) * fixedMoment M q A ≤ supportMoment μ M q A := by
  have h := centeredSum_convex_transfer μ hμ hM0 hMn hmean A
    (traceEvenPower q) (convexOn_traceEvenPower d q)
  simp_rw [traceEvenPower_smul] at h
  simpa only [fixedMoment, supportMoment, Finset.mul_sum, mul_left_comm,
    mul_assoc] using h

/-- A retention of at least one quarter costs at most 4^(2q) in the
unnormalized even trace moment. -/
theorem trace_moment_transfer (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM0 : 0 < M) (hMn : M < Fintype.card J)
    (hmean : μ.expect (fun B => (B.card : ℝ) - M) = 0)
    (hc : (1/4 : ℝ) ≤ retention μ M) (q : ℕ) (A : J → SymmetricMatrix d) :
    fixedMoment M q A ≤ (4 : ℝ) ^ (2*q) * supportMoment μ M q A := by
  have hscaled := scaled_trace_moment_transfer μ hμ hM0 hMn hmean q A
  have hc4 : 1 ≤ 4 * retention μ M := by linarith
  have hpow : 1 ≤ (4 : ℝ) ^ (2*q) * retention μ M ^ (2*q) := by
    simpa only [one_pow, mul_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hc4 (2*q)
  calc
    fixedMoment M q A = 1 * fixedMoment M q A := by ring
    _ ≤ ((4 : ℝ) ^ (2*q) * retention μ M ^ (2*q)) * fixedMoment M q A :=
      mul_le_mul_of_nonneg_right hpow (fixedMoment_nonneg M q A)
    _ = (4 : ℝ) ^ (2*q) * (retention μ M ^ (2*q) * fixedMoment M q A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (by positivity)

end TraceMoment

end
end SRHT.Sampling
