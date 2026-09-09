import SRHT.SamplingCoupling
import Mathlib.Tactic

namespace SRHT.Sampling
open SparseFock
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def conditionalLaw (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T : Exact J M) : FiniteLaw (Finset J) where
  weight B := (Fintype.card (Exact J M) : ℝ) * (jointLaw μ hM).weight (B,T)
  weight_nonneg B := mul_nonneg (by positivity) ((jointLaw μ hM).weight_nonneg _)
  sum_weight := by
    letI := exact_nonempty hM
    rw [← Finset.mul_sum]
    change (Fintype.card (Exact J M) : ℝ) * targetMarginal μ hM T = 1
    rw [targetMarginal_uniform]
    field_simp

theorem conditionalLaw_invariant (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (σ : Equiv.Perm J) (B : Finset J) (T : Exact J M) :
    (conditionalLaw μ hM (actExact σ T)).weight (σ.finsetCongr B) =
      (conditionalLaw μ hM T).weight B := by
  simp only [conditionalLaw, jointLaw_invariant]

theorem conditionalLaw_mixture (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM : M ≤ Fintype.card J) (B : Finset J) :
    (∑ T : Exact J M, (1 / (Fintype.card (Exact J M) : ℝ)) *
      (conditionalLaw μ hM T).weight B) = μ.weight B := by
  letI := exact_nonempty hM
  have hN : (Fintype.card (Exact J M) : ℝ) ≠ 0 := by positivity
  simp only [conditionalLaw]
  simp_rw [← mul_assoc, one_div_mul_cancel hN, one_mul]
  exact joint_first_marginal μ hμ hM B

def fiberMoment (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (f : Finset J → ℝ) (T : Exact J M) : ℝ :=
  ∑ B, (jointLaw μ hM).weight (B,T) * f B

theorem fiberMoment_invariant (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (f : Finset J → ℝ)
    (hf : ∀ (σ : Equiv.Perm J) B, f (σ.finsetCongr B) = f B)
    (σ : Equiv.Perm J) (T : Exact J M) :
    fiberMoment μ hM f (actExact σ T) = fiberMoment μ hM f T := by
  unfold fiberMoment
  rw [← σ.finsetCongr.sum_comp (fun B => (jointLaw μ hM).weight (B,actExact σ T) * f B)]
  simp_rw [jointLaw_invariant, hf]

theorem conditionalLaw_expect_invariant_function (μ : FiniteLaw (Finset J))
    (hμ : Exchangeable μ) {M : ℕ} (hM : M ≤ Fintype.card J)
    (f : Finset J → ℝ) (hf : ∀ (σ : Equiv.Perm J) B, f (σ.finsetCongr B) = f B)
    (T : Exact J M) : (conditionalLaw μ hM T).expect f = μ.expect f := by
  have hconst (U : Exact J M) : fiberMoment μ hM f U = fiberMoment μ hM f T := by
    obtain ⟨σ, hσ⟩ := exact_transitive T U
    rw [← hσ, fiberMoment_invariant μ hM f hf]
  calc
    _ = (Fintype.card (Exact J M) : ℝ) * fiberMoment μ hM f T := by
      simp only [FiniteLaw.expect, conditionalLaw, fiberMoment, mul_assoc, Finset.mul_sum]
    _ = ∑ _U : Exact J M, fiberMoment μ hM f T := by simp
    _ = ∑ U : Exact J M, fiberMoment μ hM f U := by simp_rw [hconst]
    _ = μ.expect f := by
      simp only [fiberMoment, FiniteLaw.expect]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, joint_first_marginal μ hμ hM]

theorem conditionalLaw_expect_card_function (μ : FiniteLaw (Finset J))
    (hμ : Exchangeable μ) {M : ℕ} (hM : M ≤ Fintype.card J)
    (f : ℕ → ℝ) (T : Exact J M) :
    (conditionalLaw μ hM T).expect (fun B => f B.card) = μ.expect (fun B => f B.card) :=
  conditionalLaw_expect_invariant_function μ hμ hM _
    (by intro σ B; simp) T

def site (B : Finset J) (j : J) : ℝ := if j ∈ B then 1 else 0

def inclusion (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T : Exact J M) (j : J) : ℝ :=
  (conditionalLaw μ hM T).expect (fun B => site B j)

theorem inclusion_invariant (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (σ : Equiv.Perm J) (T : Exact J M) (j : J) :
    inclusion μ hM (actExact σ T) (σ j) = inclusion μ hM T j := by
  unfold inclusion FiniteLaw.expect
  rw [← σ.finsetCongr.sum_comp (fun B => (conditionalLaw μ hM (actExact σ T)).weight B * site B (σ j))]
  simp_rw [conditionalLaw_invariant]
  simp [site, Finset.mem_map_equiv]

theorem actExact_swap_fixed {M : ℕ} (T : Exact J M) (i j : J)
    (hij : i ∈ T.val ↔ j ∈ T.val) : actExact (Equiv.swap i j) T = T := by
  apply Subtype.ext
  ext k
  simp only [actExact, Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hki : k = i
  · subst k
    simpa using hij.symm
  · by_cases hkj : k = j
    · subst k
      simpa using hij
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem inclusion_same_region (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T : Exact J M) (i j : J)
    (hij : i ∈ T.val ↔ j ∈ T.val) : inclusion μ hM T i = inclusion μ hM T j := by
  have h := inclusion_invariant μ hM (Equiv.swap i j) T i
  rw [actExact_swap_fixed T i j hij, Equiv.swap_apply_left] at h
  exact h.symm

theorem conditionalLaw_zero_of_not_nested (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (B : Finset J) (T : Exact J M)
    (h : ¬ (B ⊆ T.val ∨ T.val ⊆ B)) : (conditionalLaw μ hM T).weight B = 0 := by
  simp only [conditionalLaw, jointLaw_zero_of_not_nested μ hM B T h, mul_zero]

theorem sum_site (B T : Finset J) :
    (∑ j ∈ T, site B j) = ((T ∩ B).card : ℝ) := by
  simp [site, ← Finset.sum_filter, Finset.filter_mem_eq_inter]

theorem sum_missing (B T : Finset J) :
    (∑ j ∈ T, (1 - site B j)) = ((T \ B).card : ℝ) := by
  have h (j : J) : 1 - site B j = if j ∉ B then 1 else 0 := by
    by_cases hj : j ∈ B <;> simp [site, hj]
  simp_rw [h]
  simpa only [Finset.sdiff_eq_filter] using
    (Finset.sum_boole (R := ℝ) (fun j => j ∉ B) T)

theorem expect_finset_sum {α K : Type*} [Fintype α]
    (μ : FiniteLaw α) (S : Finset K) (f : K → α → ℝ) :
    μ.expect (fun a => ∑ k ∈ S, f k a) = ∑ k ∈ S, μ.expect (f k) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem weighted_missing_eq (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T : Exact J M) (B : Finset J) :
    (conditionalLaw μ hM T).weight B * ((T.val \ B).card : ℝ) =
      (conditionalLaw μ hM T).weight B * max ((M : ℝ) - B.card) 0 := by
  by_cases hn : B ⊆ T.val ∨ T.val ⊆ B
  · congr 1
    rcases hn with h | h
    · have hc : B.card ≤ M := (Finset.card_le_card h).trans_eq T.property
      have hcr : (B.card : ℝ) ≤ M := by exact_mod_cast hc
      rw [Finset.card_sdiff_of_subset h, T.property, Nat.cast_sub hc,
        max_eq_left (sub_nonneg.mpr hcr)]
    · have hc : M ≤ B.card := T.property ▸ Finset.card_le_card h
      have hcr : (M : ℝ) ≤ B.card := by exact_mod_cast hc
      simp [Finset.sdiff_eq_empty_iff_subset.mpr h, max_eq_right (sub_nonpos.mpr hcr)]
  · rw [conditionalLaw_zero_of_not_nested μ hM B T hn]
    simp

theorem weighted_excess_eq (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T : Exact J M) (B : Finset J) :
    (conditionalLaw μ hM T).weight B * ((B \ T.val).card : ℝ) =
      (conditionalLaw μ hM T).weight B * max ((B.card : ℝ) - M) 0 := by
  by_cases hn : B ⊆ T.val ∨ T.val ⊆ B
  · congr 1
    rcases hn with h | h
    · have hc : B.card ≤ M := (Finset.card_le_card h).trans_eq T.property
      have hcr : (B.card : ℝ) ≤ M := by exact_mod_cast hc
      simp [Finset.sdiff_eq_empty_iff_subset.mpr h, max_eq_right (sub_nonpos.mpr hcr)]
    · have hc : M ≤ B.card := T.property ▸ Finset.card_le_card h
      have hcr : (M : ℝ) ≤ B.card := by exact_mod_cast hc
      rw [Finset.card_sdiff_of_subset h, T.property, Nat.cast_sub hc,
        max_eq_left (sub_nonneg.mpr hcr)]
  · rw [conditionalLaw_zero_of_not_nested μ hM B T hn]
    simp

theorem inclusion_inside_mul (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM : M ≤ Fintype.card J) (T : Exact J M) (i : J) (hi : i ∈ T.val) :
    (M : ℝ) * (1 - inclusion μ hM T i) =
      μ.expect (fun B => max ((M : ℝ) - B.card) 0) := by
  calc
    _ = ∑ j ∈ T.val, (1 - inclusion μ hM T j) := by
      have he (j : J) (hj : j ∈ T.val) : inclusion μ hM T j = inclusion μ hM T i :=
        inclusion_same_region μ hM T j i (iff_of_true hj hi)
      symm
      calc
        _ = ∑ _j ∈ T.val, (1 - inclusion μ hM T i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [he j hj]
        _ = _ := by simp [T.property]; ring
    _ = (conditionalLaw μ hM T).expect (fun B => ∑ j ∈ T.val, (1 - site B j)) := by
      rw [expect_finset_sum]
      simp [FiniteLaw.expect_sub, inclusion]
    _ = (conditionalLaw μ hM T).expect (fun B => ((T.val \ B).card : ℝ)) := by
      simp_rw [sum_missing]
    _ = (conditionalLaw μ hM T).expect (fun B => max ((M : ℝ) - B.card) 0) := by
      apply Finset.sum_congr rfl
      intro B _
      exact weighted_missing_eq μ hM T B
    _ = _ := conditionalLaw_expect_card_function μ hμ hM
      (fun k : ℕ => max ((M : ℝ) - k) 0) T

theorem inclusion_outside_mul (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM : M ≤ Fintype.card J) (T : Exact J M) (i : J) (hi : i ∉ T.val) :
    ((Fintype.card J : ℝ) - M) * inclusion μ hM T i =
      μ.expect (fun B => max ((B.card : ℝ) - M) 0) := by
  have hcard : (T.valᶜ.card : ℝ) = (Fintype.card J : ℝ) - M := by
    rw [Finset.card_compl, T.property, Nat.cast_sub hM]
  calc
    _ = ∑ j ∈ T.valᶜ, inclusion μ hM T j := by
      have he (j : J) (hj : j ∈ T.valᶜ) : inclusion μ hM T j = inclusion μ hM T i :=
        inclusion_same_region μ hM T j i (iff_of_false (Finset.mem_compl.mp hj) hi)
      rw [Finset.sum_congr rfl he]
      simp [hcard]
    _ = (conditionalLaw μ hM T).expect (fun B => ∑ j ∈ T.valᶜ, site B j) := by
      rw [expect_finset_sum]
      rfl
    _ = (conditionalLaw μ hM T).expect (fun B => ((B \ T.val).card : ℝ)) := by
      apply FiniteLaw.expect_congr
      intro B
      rw [sum_site]
      have he : T.valᶜ ∩ B = B \ T.val := by
        ext j
        simp [and_comm]
      rw [he]
    _ = (conditionalLaw μ hM T).expect (fun B => max ((B.card : ℝ) - M) 0) := by
      apply Finset.sum_congr rfl
      intro B _
      exact weighted_excess_eq μ hM T B
    _ = _ := conditionalLaw_expect_card_function μ hμ hM
      (fun k : ℕ => max ((k : ℝ) - M) 0) T

theorem inclusion_inside (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM : M ≤ Fintype.card J) (hM0 : 0 < M)
    (T : Exact J M) (i : J) (hi : i ∈ T.val) :
    inclusion μ hM T i = 1 -
      μ.expect (fun B => max ((M : ℝ) - B.card) 0) / M := by
  have h := inclusion_inside_mul μ hμ hM T i hi
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
  apply (eq_sub_iff_add_eq).2
  field_simp
  nlinarith

theorem inclusion_outside (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM : M ≤ Fintype.card J) (hMn : M < Fintype.card J)
    (T : Exact J M) (i : J) (hi : i ∉ T.val) :
    inclusion μ hM T i =
      μ.expect (fun B => max ((B.card : ℝ) - M) 0) / ((Fintype.card J : ℝ) - M) := by
  have h := inclusion_outside_mul μ hμ hM T i hi
  have hpos : 0 < (Fintype.card J : ℝ) - M := by exact_mod_cast Nat.sub_pos_of_lt hMn
  exact (eq_div_iff hpos.ne').2 (by nlinarith)

end
end SRHT.Sampling
