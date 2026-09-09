import SRHT.LinearDimension

/-! Explicit dimension-linear and cubic-logarithmic confidence bounds for the
actual row count.  All constants are universal, including their dependence on
the requested failure probability. -/
namespace SRHT
noncomputable section

theorem ceil_logb_four_cube_le {x : ℝ} (hx : 1 ≤ x) :
    (⌈Real.logb 4 x⌉₊ : ℝ)^3 ≤ 4*x := by
  have hlog := Real.logb_nonneg (by norm_num : (1:ℝ)<4) hx
  have hceil := Nat.ceil_lt_add_one hlog
  have hp := Real.rpow_lt_rpow_of_exponent_lt
    (by norm_num : (1:ℝ)<4) hceil
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith : 0<x),
    Real.rpow_one] at hp
  have hc := cube_le_four_pow ⌈Real.logb 4 x⌉₊
  nlinarith

theorem log_inverse_failure_ge_half {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1/2) :
    1/2 ≤ Real.log (1/δ) := by
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hinv : (2:ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hmono := Real.log_le_log (by norm_num : (0:ℝ)<2) hinv
  norm_num at hlog2
  linarith

theorem ceil_confidence_log_le {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1/2) :
    (⌈Real.logb 4 (4/δ)⌉₊ : ℝ) ≤ 5*Real.log (1/δ) := by
  have hell := log_inverse_failure_ge_half hδ hδ1
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hlog2
  have hlog4eq : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num
  have hlog4 : 1 ≤ Real.log 4 := by rw [hlog4eq]; linarith
  have hlog4pos : 0 < Real.log 4 := by linarith
  have hratio : 1 ≤ (4:ℝ)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hceil := Nat.ceil_lt_add_one
    (Real.logb_nonneg (by norm_num : (1:ℝ)<4) hratio)
  have hlog : Real.logb 4 (4/δ) = 1+Real.log (1/δ)/Real.log 4 := by
    rw [show (4:ℝ)/δ = 4*(1/δ) by ring, Real.logb,
      Real.log_mul (by norm_num) (by positivity : (1:ℝ)/δ ≠ 0), add_div,
      div_self hlog4pos.ne']
  have hdiv : Real.log (1/δ)/Real.log 4 ≤ Real.log (1/δ) := by
    apply (div_le_iff₀ hlog4pos).mpr
    nlinarith
  rw [hlog] at hceil
  rw [hlog]
  linarith

theorem failureOrder_le_split_logs {d : ℕ} {δ : ℝ}
    (hd : 1≤d) (hδ : 0<δ) :
    failureOrder d δ ≤ ⌈Real.logb 4 (d:ℝ)⌉₊ + ⌈Real.logb 4 (4/δ)⌉₊ := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  unfold failureOrder
  rw [show 4*(d:ℝ)/δ = (d:ℝ)*(4/δ) by ring,
    Real.logb_mul hd0.ne' (by positivity : (4:ℝ)/δ ≠ 0)]
  exact Nat.ceil_add_le _ _

theorem failureOrder_cube_log_bound {d : ℕ} {δ : ℝ}
    (hd : 1≤d) (hδ : 0<δ) (hδ1 : δ<1/2) :
    (failureOrder d δ:ℝ)^3 ≤ 16*(d:ℝ)+500*(Real.log (1/δ))^3 := by
  let a : ℝ := ⌈Real.logb 4 (d:ℝ)⌉₊
  let b : ℝ := ⌈Real.logb 4 (4/δ)⌉₊
  have ha : 0≤a := by positivity
  have hb : 0≤b := by positivity
  have hsplit : (failureOrder d δ:ℝ) ≤ a+b := by
    have hh := Nat.cast_le (α:=ℝ).mpr (failureOrder_le_split_logs hd hδ)
    simpa only [Nat.cast_add] using hh
  have hcuba : a^3 ≤ 4*(d:ℝ) :=
    ceil_logb_four_cube_le (by exact_mod_cast hd)
  have hblog : b ≤ 5*Real.log (1/δ) := ceil_confidence_log_le hδ hδ1
  have hcubb : b^3 ≤ 125*(Real.log (1/δ))^3 := by
    have hh : b^3 ≤ (5*Real.log (1/δ))^3 := by gcongr
    nlinarith [hh]
  have hc : (failureOrder d δ:ℝ)^3 ≤ (a+b)^3 := by gcongr
  have hdiff : 0 ≤ (a-b)^2*(a+b) := mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith

theorem effectiveDimension_log_bound {d : ℕ} {δ : ℝ}
    (hd : 1≤d) (hδ : 0<δ) (hδ1 : δ<1/2) :
    (effectiveDimension d (failureOrder d δ):ℝ) ≤
      13500*((d:ℝ)+(Real.log (1/δ))^3) := by
  have hc := failureOrder_cube_log_bound hd hδ hδ1
  unfold effectiveDimension
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) d]

theorem rowCount_log_confidence {n d : ℕ} {ε δ : ℝ}
    (hd : 1≤d) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ<1/2) :
    (rowCount n d ε δ:ℝ) ≤
      110592001*((d:ℝ)+(Real.log (1/δ))^3)/ε^2 := by
  have hD := effectiveDimension_log_bound hd hδ hδ1
  have he2 : 0<ε^2 := sq_pos_of_pos hε
  have hsize : (rowCount n d ε δ:ℝ) ≤
      ⌈8192*(effectiveDimension d (failureOrder d δ):ℝ)/ε^2⌉₊ := by
    unfold rowCount
    exact Nat.cast_le.mpr (min_le_right _ _)
  have hceil := Nat.ceil_lt_add_one (show
    0≤8192*(effectiveDimension d (failureOrder d δ):ℝ)/ε^2 by positivity)
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have hell : 0≤Real.log (1/δ) := le_trans (by norm_num)
    (log_inverse_failure_ge_half hδ hδ1)
  have hell3 : 0≤(Real.log (1/δ))^3 := by positivity
  have heSq : ε^2≤1 := by nlinarith
  apply (le_div_iff₀ he2).mpr
  have hs := (lt_div_iff₀ he2).mp (show
    (rowCount n d ε δ:ℝ)-1 <
      8192*(effectiveDimension d (failureOrder d δ):ℝ)/ε^2 by linarith)
  nlinarith

/-- The explicit row count has the claimed cubic logarithmic confidence
dependence, with its ambient-dimension cap retained. -/
theorem rowCount_log_confidence_capped {n d : ℕ} {ε δ : ℝ}
    (hd : 1≤d) (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1/2) :
    (rowCount n d ε δ:ℝ) ≤ min (n:ℝ)
      (110592001*((d:ℝ)+(Real.log (1/δ))^3)/ε^2) := by
  exact le_min (by exact_mod_cast rowCount_le n d ε δ)
    (rowCount_log_confidence hd hε hε1.le hδ hδ1)

end
end SRHT
