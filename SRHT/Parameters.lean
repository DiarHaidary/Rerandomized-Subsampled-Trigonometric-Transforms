import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! The explicit finite constants of the SRHT draft. -/
namespace SRHT
noncomputable section

def failureOrder (d : ℕ) (δ : ℝ) : ℕ :=
  ⌈Real.logb 4 (4 * (d : ℝ) / δ)⌉₊

def effectiveDimension (d q : ℕ) : ℕ := d + 27 * q ^ 3

def rowCount (n d : ℕ) (ε δ : ℝ) : ℕ :=
  min n ⌈8192 * (effectiveDimension d (failureOrder d δ) : ℝ) / ε ^ 2⌉₊

def momentEnvelope (D m : ℝ) : ℝ :=
  6 * Real.sqrt (D / m) + 9 * D / m

theorem failureOrder_log_lower (d : ℕ) (δ : ℝ) :
    Real.logb 4 (4 * (d : ℝ) / δ) ≤ (failureOrder d δ : ℝ) :=
  Nat.le_ceil _

theorem ratio_le_four_pow_failureOrder {d : ℕ} {δ : ℝ}
    (hd : 1 ≤ d) (hδ : 0 < δ) :
    4 * (d : ℝ) / δ ≤ (4 : ℝ) ^ failureOrder d δ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hx : 0 < 4 * (d : ℝ) / δ := by positivity
  have h := (Real.logb_le_iff_le_rpow (b := (4 : ℝ)) (by norm_num) hx).mp
    (failureOrder_log_lower d δ)
  simpa [Real.rpow_natCast] using h

theorem failure_mass_le {d : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) :
    (d : ℝ) * (1 / 2 : ℝ) ^ (2 * failureOrder d δ) ≤ δ / 4 := by
  have hp := ratio_le_four_pow_failureOrder hd hδ
  have hpos : 0 < (4 : ℝ) ^ failureOrder d δ := by positivity
  have hmul : 4 * (d : ℝ) ≤ (4 : ℝ) ^ failureOrder d δ * δ :=
    (div_le_iff₀ hδ).mp hp
  have heq : (1 / 2 : ℝ) ^ (2 * failureOrder d δ) =
      1 / (4 : ℝ) ^ failureOrder d δ := by
    rw [pow_mul, ← one_div_pow]
    norm_num
  rw [heq, mul_one_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem rowCount_le (n d : ℕ) (ε δ : ℝ) : rowCount n d ε δ ≤ n :=
  min_le_left _ _

theorem rowCount_lower_of_lt {n d : ℕ} {ε δ : ℝ}
    (h : rowCount n d ε δ < n) :
    8192 * (effectiveDimension d (failureOrder d δ) : ℝ) / ε ^ 2 ≤
      (rowCount n d ε δ : ℝ) := by
  have hn : ⌈8192 * (effectiveDimension d (failureOrder d δ) : ℝ) / ε ^ 2⌉₊ < n := by
    simpa only [rowCount, min_lt_iff, lt_self_iff_false, false_or] using h
  rw [rowCount, min_eq_right hn.le]
  exact Nat.le_ceil _

theorem envelope_nonneg {D m : ℝ} (hD : 0 ≤ D) (hm : 0 < m) :
    0 ≤ momentEnvelope D m := by
  unfold momentEnvelope
  positivity

theorem envelope_le_half {D m a : ℝ}
    (hD : 0 ≤ D) (hm : 0 < m) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hsize : 256 * D / a ^ 2 ≤ m) :
    momentEnvelope D m ≤ a / 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha0
  have hsize' : 256 * D ≤ m * a ^ 2 := (div_le_iff₀ ha2).mp hsize
  have hratio : D / m ≤ a ^ 2 / 256 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have hsqrt : Real.sqrt (D / m) ≤ a / 16 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  have ha_sq : a ^ 2 ≤ a := by nlinarith
  unfold momentEnvelope
  have hlast : 9 * D / m = 9 * (D / m) := by ring
  rw [hlast]
  nlinarith

theorem amplified_envelope_le_half {D m ε : ℝ}
    (hD : 0 ≤ D) (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : 8192*D/ε^2 ≤ m) : 4*momentEnvelope D m ≤ ε/2 := by
  have he2 : 0<ε^2 := sq_pos_of_pos hε
  have hs : 8192*D ≤ m*ε^2 := (div_le_iff₀ he2).mp hsize
  have hr : D/m ≤ ε^2/8192 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have hsq : Real.sqrt (D/m) ≤ ε/64 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [sq_nonneg ε]
  have he : ε^2 ≤ ε := by nlinarith
  unfold momentEnvelope
  have hdiv : 9*D/m=9*(D/m) := by ring
  rw [hdiv]
  nlinarith

theorem failureOrder_pos {d : ℕ} {δ : ℝ} (hd : 1≤d) (hδ : 0<δ) (hδ1 : δ<1/2) :
    0 < failureOrder d δ := by
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have hr : 1 < 4*(d:ℝ)/δ := (lt_div_iff₀ hδ).mpr (by linarith)
  have hp : 0 < Real.logb 4 (4*(d:ℝ)/δ) := Real.logb_pos (by norm_num) hr
  have hn := failureOrder_log_lower d δ
  have hnat : (0:ℝ)<failureOrder d δ := hp.trans_le hn
  exact_mod_cast hnat

theorem rowCount_pos {n d : ℕ} {ε δ : ℝ} (hn : 0<n) (hd : 1≤d) (hε : 0<ε) :
    0 < rowCount n d ε δ := by
  apply lt_min hn
  apply Nat.ceil_pos.mpr
  have hD : (0:ℝ)<effectiveDimension d (failureOrder d δ) := by
    have h : 0<effectiveDimension d (failureOrder d δ) := by unfold effectiveDimension; omega
    exact_mod_cast h
  positivity

theorem logb_four_eq (x : ℝ) : Real.logb 4 x = Real.log x/(2*Real.log 2) := by
  rw [Real.logb,show (4:ℝ)=2^2 by norm_num,Real.log_pow]
  norm_num

theorem failureOrder_original (d : ℕ) (δ : ℝ) :
    failureOrder d δ = ⌈Real.log (4*(d:ℝ)/δ)/(2*Real.log 2)⌉₊ := by
  unfold failureOrder
  rw [logb_four_eq]

theorem selector_envelope_le {L p : ℝ} (hL : 0≤L) (hp : 0<p) (hp1 : p<1) :
    2*Real.sqrt ((1-p)/p)*Real.sqrt L+|(1-2*p)/p| *L ≤
      2*Real.sqrt (L/p)+L/p := by
  have hab : |(1-2*p)/p| ≤ 1/p := by
    rw [abs_div,abs_of_pos hp]
    apply div_le_div_of_nonneg_right _ hp.le
    apply abs_le.mpr
    constructor <;> linarith
  have hsig : Real.sqrt ((1-p)/p)*Real.sqrt L ≤ Real.sqrt (L/p) := by
    rw [← Real.sqrt_mul (by positivity : 0≤(1-p)/p)]
    apply Real.sqrt_le_sqrt
    have he : ((1-p)/p)*L = (1-p)*(L/p) := by ring
    rw [he]
    have hratio : 0≤L/p := div_nonneg hL hp.le
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hab hL
  have he : (1/p)*L=L/p := by ring
  rw [he] at hlast
  linarith

theorem bernoulli_envelope_le {D n m : ℝ}
    (hD : 0≤D) (hn : 0<n) (hm : 0<m) (hmn : m<n) :
    2*Real.sqrt ((1-m/n)/(m/n))*Real.sqrt (9*D/n)+
      |(1-2*(m/n))/(m/n)| *(9*D/n) ≤ momentEnvelope D m := by
  have hp : 0<m/n := div_pos hm hn
  have hp1 : m/n<1 := (div_lt_one hn).mpr hmn
  have h := selector_envelope_le (L:=9*D/n) (by positivity) hp hp1
  have he : (9*D/n)/(m/n)=9*(D/m) := by field_simp
  rw [he] at h
  have hs : Real.sqrt (9*(D/m)) = 3*Real.sqrt (D/m) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤9)]
    norm_num
  rw [hs] at h
  unfold momentEnvelope
  convert h using 1 <;> ring

end
end SRHT
