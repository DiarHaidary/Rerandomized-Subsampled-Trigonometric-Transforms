import SRHT.Parameters

/-! An explicit dimension-linear consequence for every fixed failure probability. -/
namespace SRHT
noncomputable section

theorem cube_le_four_pow (q : ℕ) : (q:ℝ)^3 ≤ (4:ℝ)^q := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    by_cases hq : q≤1
    · interval_cases q <;> norm_num
    · have hqR : (2:ℝ)≤q := by exact_mod_cast (show 2≤q by omega)
      have hprod : 0 ≤ ((q:ℝ)-2)*(3*(q:ℝ)^2+3*q+3) :=
        mul_nonneg (by linarith) (by positivity)
      rw [pow_succ (4:ℝ) q,Nat.cast_succ]
      nlinarith

theorem four_pow_failureOrder_lt {d : ℕ} {δ : ℝ}
    (hd : 1≤d) (hδ : 0<δ) (hδ1 : δ<1/2) :
    (4:ℝ)^failureOrder d δ < 16*(d:ℝ)/δ := by
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have hx : 0 < 4*(d:ℝ)/δ := by positivity
  have hr : 1 < 4*(d:ℝ)/δ := (lt_div_iff₀ hδ).mpr (by linarith)
  have hlog : 0≤Real.logb 4 (4*(d:ℝ)/δ) := (Real.logb_pos (by norm_num) hr).le
  have hceil := Nat.ceil_lt_add_one hlog
  change (failureOrder d δ:ℝ) < Real.logb 4 (4*(d:ℝ)/δ)+1 at hceil
  have hpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<4) hceil
  rw [Real.rpow_natCast,Real.rpow_add (by norm_num),Real.rpow_logb (by norm_num) (by norm_num) hx,
    Real.rpow_one] at hpow
  convert hpow using 1 <;> ring

theorem effectiveDimension_linear {d : ℕ} {δ : ℝ}
    (hd : 1≤d) (hδ : 0<δ) (hδ1 : δ<1/2) :
    (effectiveDimension d (failureOrder d δ):ℝ) ≤ (1+432/δ)*(d:ℝ) := by
  have hc := cube_le_four_pow (failureOrder d δ)
  have hp := four_pow_failureOrder_lt hd hδ hδ1
  have he : (1+432/δ)*(d:ℝ) = (d:ℝ)+27*(16*d/δ) := by ring
  rw [he]
  unfold effectiveDimension
  push_cast
  linarith

theorem rowCount_dimension_linear {n d : ℕ} {ε δ : ℝ}
    (hd : 1≤d) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ<1/2) :
    (rowCount n d ε δ : ℝ) ≤ (8192*(1+432/δ)+1)*(d:ℝ)/ε^2 := by
  have hD := effectiveDimension_linear hd hδ hδ1
  have he2 : 0<ε^2 := sq_pos_of_pos hε
  have hsize : (rowCount n d ε δ:ℝ) ≤
      ⌈8192*(effectiveDimension d (failureOrder d δ):ℝ)/ε^2⌉₊ := by
    unfold rowCount
    exact Nat.cast_le.mpr (min_le_right _ _)
  have hceil := Nat.ceil_lt_add_one (show 0≤8192*(effectiveDimension d (failureOrder d δ):ℝ)/ε^2 by positivity)
  have hdR : (1:ℝ)≤d := by exact_mod_cast hd
  have heSq : ε^2≤1 := by nlinarith
  apply (le_div_iff₀ he2).mpr
  have hs := (lt_div_iff₀ he2).mp (show
      (rowCount n d ε δ:ℝ)-1 < 8192*(effectiveDimension d (failureOrder d δ):ℝ)/ε^2 by linarith)
  nlinarith

end
end SRHT
