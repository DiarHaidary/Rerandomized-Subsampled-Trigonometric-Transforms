import SRHT.SupportMiss
import SRHT.Parameters

/-! A scalar, quantified high-confidence obstruction.  The support-miss lower
bound for a fixed number of sign rounds exceeds any proposed universal row
bound proportional to `ε⁻² (1 + log (1/δ))` along an unbounded dyadic sequence.
The probability interpretation of the support-miss lower bound is separate. -/
namespace SRHT.ConfidenceObstruction
noncomputable section

def exponentialConfidence (a : ℝ) (L : ℕ) : ℝ := Real.exp (-(a*(L:ℝ)))

theorem exponentialConfidence_pos (a : ℝ) (L : ℕ) :
    0 < exponentialConfidence a L := Real.exp_pos _

theorem exponentialConfidence_root (a : ℝ) {L : ℕ} (hL : 0<L) :
    (exponentialConfidence a L)^(1/(L:ℝ)) = Real.exp (-a) := by
  unfold exponentialConfidence
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

theorem log_inverse_exponentialConfidence (a : ℝ) (L : ℕ) :
    Real.log (1/exponentialConfidence a L) = a*(L:ℝ) := by
  simp [exponentialConfidence, one_div, Real.log_inv, Real.log_exp]

theorem support_fraction_pos {t : ℕ} {a : ℝ}
    (ha : (t:ℝ)*Real.log 2 < a) :
    0 < 1-(2:ℝ)^t*Real.exp (-a) := by
  have heq : Real.exp ((t:ℝ)*Real.log 2) = (2:ℝ)^t := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hp : (2:ℝ)^t*Real.exp (-a) < 1 := by
    rw [← heq, ← Real.exp_add]
    apply Real.exp_lt_one_iff.mpr
    linarith
  linarith

/-- Dyadic side lengths exceed any prescribed threshold, with arbitrarily
large exponents. -/
theorem exists_dyadic_gt (x : ℝ) (k₀ : ℕ) :
    ∃ k : ℕ, k₀≤k ∧ 1≤k ∧ x<(2:ℝ)^k := by
  obtain ⟨N,hN⟩ := exists_nat_gt x
  let k := max k₀ (N+1)
  have hNk : N<k := by dsimp [k]; omega
  have hkp : k<2^k := Nat.lt_two_pow_self
  refine ⟨k, le_max_left _ _, ?_, ?_⟩
  · omega
  · have hh : (N:ℝ)<(2:ℝ)^k := by exact_mod_cast hNk.trans hkp
    exact hN.trans hh

theorem exponentialConfidence_lt_half {a : ℝ} {L : ℕ}
    (hlarge : Real.log 2 < a*(L:ℝ)) :
    exponentialConfidence a L < 1/2 := by
  have hh : Real.exp (-(a*(L:ℝ))) < Real.exp (-Real.log 2) :=
    Real.exp_lt_exp.mpr (neg_lt_neg hlarge)
  norm_num [Real.exp_neg, Real.exp_log] at hh
  simpa only [exponentialConfidence, Real.exp_neg] using hh

/-- A quadratic support requirement eventually exceeds every fixed multiple
of the logarithmic row budget, including along arbitrarily large dyadic sizes. -/
theorem exists_dyadic_scalar_gap (C ε a : ℝ) (t k₀ : ℕ)
    (hε : 0<ε) (ha : (t:ℝ)*Real.log 2<a) :
    ∃ k : ℕ, k₀≤k ∧ 1≤k ∧
      exponentialConfidence a (2^k)<1/2 ∧
      C/ε^2 * (1+Real.log (1/exponentialConfidence a (2^k))) <
        (((2^k)^2-2^k+1:ℕ):ℝ) * (1-(2:ℝ)^t*Real.exp (-a)) := by
  let η := 1-(2:ℝ)^t*Real.exp (-a)
  let K := |C|/ε^2
  have hη : 0<η := support_fraction_pos ha
  have hK : 0≤K := by dsimp [K]; positivity
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0<a := lt_of_le_of_lt
    (mul_nonneg (Nat.cast_nonneg t) hlog2.le) ha
  obtain ⟨k,hk₀,hk,hlarge⟩ := exists_dyadic_gt
    (max 2 (max (2*K*(1+a)/η) (Real.log 2/a))) k₀
  let L : ℕ := 2^k
  have hlarge' : max 2 (max (2*K*(1+a)/η) (Real.log 2/a)) < (L:ℝ) := by
    simpa only [L, Nat.cast_pow, Nat.cast_ofNat] using hlarge
  have hL2 : (2:ℝ)<L := lt_of_le_of_lt (le_max_left _ _) hlarge'
  have hmain : 2*K*(1+a)/η < (L:ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlarge'
  have hconf : Real.log 2/a < (L:ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlarge'
  have hconfidence : exponentialConfidence a L<1/2 :=
    exponentialConfidence_lt_half (by
      have hh := (div_lt_iff₀ ha0).mp hconf
      nlinarith)
  have hL0 : (0:ℝ)<L := by linarith
  have hLnat : 1≤L := by exact_mod_cast (show (1:ℝ)≤L by linarith)
  have hLsq : L≤L^2 := by nlinarith
  have hcast : ((L^2-L+1:ℕ):ℝ) = (L:ℝ)^2-L+1 := by
    rw [Nat.cast_add, Nat.cast_sub hLsq, Nat.cast_pow, Nat.cast_one]
  have hquadratic : (L:ℝ)^2/2 ≤ (L:ℝ)^2-L+1 := by nlinarith [sq_nonneg ((L:ℝ)-1)]
  have hthreshold : 2*K*(1+a) < (L:ℝ)*η := (div_lt_iff₀ hη).mp hmain
  have hscale := mul_lt_mul_of_pos_right hthreshold hL0
  have hbudget : K*(1+a*(L:ℝ)) ≤ K*(1+a)*(L:ℝ) := by
    have hh := mul_nonneg hK (show 0≤(L:ℝ)-1 by linarith)
    nlinarith
  have hquadscale := mul_le_mul_of_nonneg_right hquadratic hη.le
  have hCle : C/ε^2 ≤ K := by
    exact div_le_div_of_nonneg_right (le_abs_self C) (sq_nonneg ε)
  have hbudgetC := mul_le_mul_of_nonneg_right hCle
    (show 0≤1+a*(L:ℝ) by positivity)
  refine ⟨k,hk₀,hk,hconfidence,?_⟩
  change C/ε^2 * (1+Real.log (1/exponentialConfidence a L)) <
    ((L^2-L+1:ℕ):ℝ)*η
  rw [log_inverse_exponentialConfidence, hcast]
  nlinarith

/-- No natural row count below the proposed logarithmic budget can meet the
finite necessary-row inequality at the resulting dyadic dimension. -/
theorem exists_dyadic_no_logarithmic_rows (C ε a : ℝ) (t k₀ : ℕ)
    (hε : 0<ε) (ha : (t:ℝ)*Real.log 2<a) :
    ∃ k : ℕ, k₀≤k ∧ 1≤k ∧
      0<exponentialConfidence a (2^k) ∧
      exponentialConfidence a (2^k)<1/2 ∧
      ∀ M : ℕ,
        (M:ℝ)≤C/ε^2*(1+Real.log (1/exponentialConfidence a (2^k))) →
        ¬ (((2^k)^2-2^k+1:ℕ):ℝ) *
          (1-(2:ℝ)^t*(exponentialConfidence a (2^k))^(1/((2^k:ℕ):ℝ))) ≤ M := by
  obtain ⟨k,hk₀,hk,hconf,hgap⟩ := exists_dyadic_scalar_gap C ε a t k₀ hε ha
  refine ⟨k,hk₀,hk,exponentialConfidence_pos _ _,hconf,?_⟩
  intro M hM hnecess
  rw [exponentialConfidence_root a (L:=2^k) (by positivity)] at hnecess
  exact (not_lt_of_ge (hnecess.trans hM)) hgap

/-- The exact support-miss lower bound is strictly larger than the requested
failure probability for every row count within the proposed logarithmic budget.
This theorem is scalar; a probability lower bound composes with it directly. -/
theorem exists_dyadic_support_failure (C ε a : ℝ) (t k₀ : ℕ)
    (hε : 0<ε) (ha : (t:ℝ)*Real.log 2<a) :
    ∃ k : ℕ, k₀≤k ∧ 1≤k ∧
      0<exponentialConfidence a (2^k) ∧
      exponentialConfidence a (2^k)<1/2 ∧
      ∀ M : ℕ,
        (M:ℝ)≤C/ε^2*(1+Real.log (1/exponentialConfidence a (2^k))) →
        exponentialConfidence a (2^k) <
          (1/2:ℝ)^(t*2^k) * SupportMiss.missRatio ((2^k)^2) (2^k) M := by
  obtain ⟨k,hk₀,hk,hδ,hδhalf,hnot⟩ :=
    exists_dyadic_no_logarithmic_rows C ε a t k₀ hε ha
  refine ⟨k,hk₀,hk,hδ,hδhalf,?_⟩
  intro M hM
  by_contra hbad
  have hL : 2^k≤(2^k)^2 := by
    have hh0 : 0<(2:ℕ)^k := by positivity
    have hh : 1≤(2:ℕ)^k := hh0
    nlinarith
  exact hnot M hM (SupportMiss.necessary_rows (by positivity) hL hδ.le
    (le_of_not_gt hbad))

end
end SRHT.ConfidenceObstruction
