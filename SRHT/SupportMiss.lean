import SRHT.Model
import SRHT.SamplingCoupling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact support-missing probabilities for uniform fixed-size row samples. -/
namespace SRHT.SupportMiss
noncomputable section
open SparseFock
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

def missLaw {M : ℕ} (hM : M ≤ Fintype.card J) : FiniteLaw (Sampling.Exact J M) := by
  letI := Sampling.exact_nonempty hM
  exact SRHT.uniformLaw (Sampling.Exact J M)

def exactEquivPowerset (M : ℕ) :
    Sampling.Exact J M ≃ ((Finset.univ : Finset J).powersetCard M) where
  toFun T := ⟨T.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, T.property⟩⟩
  invFun T := ⟨T.val, (Finset.mem_powersetCard.mp T.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq J] in
theorem exact_card (M : ℕ) : Fintype.card (Sampling.Exact J M) =
    (Fintype.card J).choose M := by
  rw [Fintype.card_congr (exactEquivPowerset (J:=J) M), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ]

def missEquivPowerset (M : ℕ) (K : Finset J) :
    {T : Sampling.Exact J M // Disjoint T.val K} ≃ (Kᶜ.powersetCard M) where
  toFun T := ⟨T.val.val, Finset.mem_powersetCard.mpr ⟨by
    intro j hj
    exact Finset.mem_compl.mpr (fun hk => Finset.disjoint_left.mp T.property hj hk),
    T.val.property⟩⟩
  invFun T := ⟨⟨T.val, (Finset.mem_powersetCard.mp T.property).2⟩,
    Finset.disjoint_left.mpr (fun j hj hk =>
      Finset.mem_compl.mp ((Finset.mem_powersetCard.mp T.property).1 hj) hk)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem miss_card (M : ℕ) (K : Finset J) :
    Fintype.card {T : Sampling.Exact J M // Disjoint T.val K} =
      (Fintype.card J - K.card).choose M := by
  rw [Fintype.card_congr (missEquivPowerset M K), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_compl]

theorem uniform_prob_card {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [DecidablePred fun a => a ∈ s] : (SRHT.uniformLaw α).prob s =
      (Fintype.card {a // a ∈ s} : ℝ) / Fintype.card α := by
  classical
  simp only [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator,
    SRHT.uniformLaw_weight, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp [Fintype.card_subtype, div_eq_mul_inv]

def missRatio (n L M : ℕ) : ℝ :=
  ((n-L).choose M : ℝ) / (n.choose M : ℝ)

theorem miss_probability {M : ℕ} (hM : M ≤ Fintype.card J) (K : Finset J) :
    (missLaw hM).prob {T | Disjoint T.val K} =
      missRatio (Fintype.card J) K.card M := by
  let := Sampling.exact_nonempty hM
  rw [missLaw, uniform_prob_card]
  change (Fintype.card {T : Sampling.Exact J M // Disjoint T.val K} : ℝ) /
    Fintype.card (Sampling.Exact J M) = _
  rw [miss_card, exact_card]
  rfl

theorem uniformRowLaw_miss_probability {k M : ℕ} (hM : M ≤ 2^k)
    (K : Finset (WalshIndex k)) :
    (uniformRowLaw hM).prob {T | Disjoint T.val K} = missRatio (2^k) K.card M := by
  let := rowSet_nonempty hM
  rw [uniformRowLaw, uniform_prob_card]
  change (Fintype.card {T : Sampling.Exact (WalshIndex k) M // Disjoint T.val K} : ℝ) /
    Fintype.card (Sampling.Exact (WalshIndex k) M) = _
  rw [miss_card, exact_card, walshIndex_card]
  rfl

theorem missRatio_symm {n L M : ℕ} (hL : L≤n) (hM : M≤n-L) :
    missRatio n L M = ((n-M).choose L : ℝ) / (n.choose L : ℝ) := by
  have hMn : M≤n := hM.trans (Nat.sub_le _ _)
  have hLM : L≤n-M := by omega
  have hsub : n-L-M = n-M-L := by omega
  have hf (a : ℕ) : (a.factorial : ℝ) ≠ 0 := by positivity
  unfold missRatio
  rw [Nat.cast_choose ℝ hM, Nat.cast_choose ℝ hMn,
    Nat.cast_choose ℝ hLM, Nat.cast_choose ℝ hL, hsub]
  field_simp

theorem choose_ratio_descFactorial (a n L : ℕ) :
    (a.choose L : ℝ)/(n.choose L : ℝ) =
      (a.descFactorial L : ℝ)/(n.descFactorial L : ℝ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (L.factorial : ℝ) ≠ 0 := by positivity
  exact (mul_div_mul_left _ _ hf).symm

theorem missRatio_product {n L M : ℕ} (hL : L≤n) (hM : M≤n-L) :
    missRatio n L M = ∏ j ∈ Finset.range L, (1-(M:ℝ)/(n-j:ℕ)) := by
  rw [missRatio_symm hL hM, choose_ratio_descFactorial,
    Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hjL : j<L := Finset.mem_range.mp hj
  have hjn : j<n := hjL.trans_le hL
  have hjnm : j≤n-M := by omega
  have hMn : M≤n := by omega
  have hnj : (n-j:ℕ) ≠ 0 := by omega
  rw [Nat.cast_sub hjnm, Nat.cast_sub hMn]
  have hcast : (n-j:ℕ) = (n:ℝ)-j := by rw [Nat.cast_sub hjn.le]
  have hn0 : ((n-j:ℕ):ℝ) ≠ 0 := by exact_mod_cast hnj
  rw [div_eq_iff hn0]
  field_simp
  rw [hcast]
  ring

theorem missRatio_lower {n L M : ℕ} (hL : L≤n) (hM : M≤n-L) :
    (1-(M:ℝ)/(n-L+1:ℕ))^L ≤ missRatio n L M := by
  have hd : (0:ℝ)<(n-L+1:ℕ) := by positivity
  have hmd : (M:ℝ)≤(n-L+1:ℕ) := by exact_mod_cast (show M≤n-L+1 by omega)
  have hb : 0≤1-(M:ℝ)/(n-L+1:ℕ) := by
    have hdiv := (div_le_one hd).mpr hmd
    linarith
  rw [missRatio_product hL hM]
  calc
    _ = ∏ _j ∈ Finset.range L, (1-(M:ℝ)/(n-L+1:ℕ)) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun _ _ => hb)
      intro j hj
      have hjL : j<L := Finset.mem_range.mp hj
      have hden : ((n-L+1:ℕ):ℝ)≤(n-j:ℕ) := by
        exact_mod_cast (show n-L+1≤n-j by omega)
      have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg M) hd hden
      linarith

theorem missRatio_nonneg (n L M : ℕ) : 0≤missRatio n L M := by
  unfold missRatio
  positivity

theorem miss_probability_lower {M : ℕ} (hM : M≤Fintype.card J) (K : Finset J)
    (havoid : M≤Fintype.card J-K.card) :
    (1-(M:ℝ)/(Fintype.card J-K.card+1:ℕ))^K.card ≤
      (missLaw hM).prob {T | Disjoint T.val K} := by
  rw [miss_probability]
  exact missRatio_lower (Finset.card_le_univ K) havoid

theorem uniformRowLaw_miss_probability_lower {k M : ℕ} (hM : M≤2^k)
    (K : Finset (WalshIndex k)) (havoid : M≤2^k-K.card) :
    (1-(M:ℝ)/(2^k-K.card+1:ℕ))^K.card ≤
      (uniformRowLaw hM).prob {T | Disjoint T.val K} := by
  rw [uniformRowLaw_miss_probability]
  exact missRatio_lower (by simpa using Finset.card_le_univ K) havoid

/-- The finite necessary row count, including the automatic large-row branch.
The conclusion remains valid without requiring the confidence term to be positive. -/
theorem necessary_rows {n L M t : ℕ} (hL0 : 0<L) (hL : L≤n)
    {δ : ℝ} (hδ : 0≤δ)
    (hfailure : (1/2:ℝ)^(t*L) * missRatio n L M ≤ δ) :
    ((n-L+1:ℕ):ℝ) * (1-(2:ℝ)^t * δ^(1/(L:ℝ))) ≤ M := by
  have hd : (0:ℝ)<(n-L+1:ℕ) := by positivity
  have hroot : 0≤δ^(1/(L:ℝ)) := Real.rpow_nonneg hδ _
  have htwo : 0≤(2:ℝ)^t := by positivity
  by_cases hM : M≤n-L
  · have hbase : 0≤1-(M:ℝ)/(n-L+1:ℕ) := by
      have hm : (M:ℝ)≤(n-L+1:ℕ) := by exact_mod_cast (show M≤n-L+1 by omega)
      have hh := (div_le_one hd).mpr hm
      linarith
    have hpow : (((1/2:ℝ)^t) * (1-(M:ℝ)/(n-L+1:ℕ)))^L ≤ δ := by
      rw [mul_pow, ← pow_mul]
      exact (mul_le_mul_of_nonneg_left (missRatio_lower hL hM) (by positivity)).trans hfailure
    have hrootpow : (δ^(1/(L:ℝ)))^L = δ := by
      simpa only [one_div] using Real.rpow_inv_natCast_pow hδ hL0.ne'
    rw [← hrootpow] at hpow
    have hlin := le_of_pow_le_pow_left₀ hL0.ne' hroot hpow
    have hscale : (2:ℝ)^t * (1/2:ℝ)^t = 1 := by rw [← mul_pow]; norm_num
    have hh := mul_le_mul_of_nonneg_left hlin htwo
    rw [← mul_assoc, hscale, one_mul] at hh
    have hmdiv : (M:ℝ)/(n-L+1:ℕ) * (n-L+1:ℕ) = M := div_mul_cancel₀ _ hd.ne'
    nlinarith [mul_le_mul_of_nonneg_right hh hd.le]
  · have hm : ((n-L+1:ℕ):ℝ)≤M := by exact_mod_cast (show n-L+1≤M by omega)
    have hnonneg := mul_nonneg htwo hroot
    have hprod := mul_nonneg hd.le hnonneg
    nlinarith

theorem necessary_rows_of_failure_bound {n L M t : ℕ} (hL0 : 0<L) (hL : L≤n)
    {δ failure : ℝ} (hδ : 0≤δ)
    (hlower : (1/2:ℝ)^(t*L) * missRatio n L M ≤ failure)
    (hupper : failure≤δ) :
    ((n-L+1:ℕ):ℝ) * (1-(2:ℝ)^t * δ^(1/(L:ℝ))) ≤ M :=
  necessary_rows hL0 hL hδ (hlower.trans hupper)

/-- At two rounds and confidence `δ=2^(-4L)`, at least three quarters of
`n-L+1` rows are necessary. -/
theorem two_round_three_quarters {n L M : ℕ} (hL0 : 0<L) (hL : L≤n)
    (hfailure : (1/2:ℝ)^(2*L) * missRatio n L M ≤ (1/2:ℝ)^(4*L)) :
    (3/4:ℝ) * (n-L+1:ℕ) ≤ M := by
  have hh := necessary_rows (t:=2) hL0 hL (by positivity) hfailure
  have hroot : ((1/2:ℝ)^(4*L))^(1/(L:ℝ)) = (1/16:ℝ) := by
    rw [pow_mul]
    have h := Real.pow_rpow_inv_natCast (x:=((1/2:ℝ)^4)) (by positivity) hL0.ne'
    simpa only [one_div] using h.trans (show (1/2:ℝ)^4 = 1/16 by norm_num)
  rw [hroot] at hh
  norm_num at hh ⊢
  linarith

end
end SRHT.SupportMiss
