import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Canonical v1.4 paper parameters

This module formalizes the scalar constants, base-two failure order, and integer
rounding used in lines 1430--1498 of the canonical v1.4 sparse-Fock report.
It is independent of the conditional operator/probability interfaces.
-/

namespace SparseFock

namespace PaperParameters

/-- The convex-order constant `(1 - exp (-1))⁻¹`. -/
noncomputable def cStar : ℝ := (1 - Real.exp (-1))⁻¹

/-- The common band constant `3 + sqrt 2`. -/
noncomputable def Cband : ℝ := 3 + Real.sqrt 2

/-- The global parameter constant `90 * cStar²`. -/
noncomputable def L : ℝ := 90 * cStar ^ 2

/-- The paper's base-two failure order. -/
noncomputable def failureOrder (d : ℕ) (delta : ℝ) : ℕ :=
  max 1 ⌈Real.logb 2 ((d : ℝ) / delta)⌉₊

/-- `D_q = d + 2q + 1`. -/
def Dq (d q : ℕ) : ℕ := d + 2 * q + 1

/-- Rounded sparsity `ceil (L(2q+1)/epsilon)`. -/
noncomputable def roundedS (q : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈L * ((2 * q + 1 : ℕ) : ℝ) / epsilon⌉₊

/-- The unrounded row target `L² D_q / epsilon²`. -/
noncomputable def M0 (d q : ℕ) (epsilon : ℝ) : ℝ :=
  L ^ 2 * (Dq d q : ℝ) / epsilon ^ 2

/-- Rounded stack height `ceil (M0/s)`. -/
noncomputable def roundedB (d q : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈M0 d q epsilon / roundedS q epsilon⌉₊

/-- Rounded row count, exactly divisible by the sparsity. -/
noncomputable def roundedM (d q : ℕ) (epsilon : ℝ) : ℕ :=
  roundedS q epsilon * roundedB d q epsilon

/-- The uniform band envelope evaluated at grade at most `2q`. -/
noncomputable def betaEnvelope (d q : ℕ) (m s : ℝ) : ℝ :=
  Cband * (Real.sqrt ((Dq d q : ℝ) / m) +
    (Dq d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s)

/-- The Markov moment base after the convex-order factor `cStar²`. -/
noncomputable def roundedMomentBase (d q : ℕ) (epsilon : ℝ) : ℝ :=
  3 * cStar ^ 2 *
    betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon

@[simp] theorem roundedM_eq_s_mul_b (d q : ℕ) (epsilon : ℝ) :
    roundedM d q epsilon = roundedS q epsilon * roundedB d q epsilon := rfl

theorem expGap_pos : 0 < 1 - Real.exp (-1) := by
  linarith [Real.exp_neg_one_lt_half]

theorem expGap_lt_one : 1 - Real.exp (-1) < 1 := by
  linarith [Real.exp_pos (-1)]

theorem cStar_pos : 0 < cStar := by
  exact inv_pos.mpr expGap_pos

theorem one_lt_cStar : 1 < cStar := by
  rw [cStar]
  exact (one_lt_inv₀ expGap_pos).2 expGap_lt_one

/-- Certified decimal bound from the paper: `cStar < 1.582`. -/
theorem cStar_lt_1582 : cStar < (791 : ℝ) / 500 := by
  rw [cStar, inv_lt_iff_one_lt_mul₀ expGap_pos]
  nlinarith [Real.exp_neg_one_lt_d9]

theorem L_pos : 0 < L := by
  rw [L]
  exact mul_pos (by norm_num) (sq_pos_of_pos cStar_pos)

theorem ninety_lt_L : (90 : ℝ) < L := by
  have hsq : (1 : ℝ) < cStar ^ 2 := by
    nlinarith [one_lt_cStar, cStar_pos]
  rw [L]
  nlinarith

/-- Certified global-constant bound from the paper: `L < 226`. -/
theorem L_lt_226 : L < (226 : ℝ) := by
  have hsq : cStar ^ 2 < ((791 : ℝ) / 500) ^ 2 := by
    simpa [pow_two] using
      mul_self_lt_mul_self cStar_pos.le cStar_lt_1582
  rw [L]
  nlinarith

theorem sqrt_two_lt_142 : Real.sqrt 2 < (71 : ℝ) / 50 := by
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 71 / 50)).2 (by norm_num)

/-- The numerical moment base in the v1.4 report. -/
theorem Cband_div_ten_lt_442 : Cband / 10 < (221 : ℝ) / 500 := by
  rw [Cband]
  nlinarith [sqrt_two_lt_142]

theorem Cband_div_ten_lt_half : Cband / 10 < (1 : ℝ) / 2 := by
  exact Cband_div_ten_lt_442.trans (by norm_num)

theorem Cband_pos : 0 < Cband := by
  rw [Cband]
  positivity

theorem betaEnvelope_nonneg {d q : ℕ} {m s : ℝ}
    (hm : 0 < m) (hs : 0 < s) :
    0 ≤ betaEnvelope d q m s := by
  rw [betaEnvelope]
  exact mul_nonneg Cband_pos.le <| add_nonneg
    (add_nonneg (Real.sqrt_nonneg _)
      (div_nonneg (by positivity) hm.le))
    (div_nonneg (by positivity) hs.le)

theorem one_le_failureOrder (d : ℕ) (delta : ℝ) :
    1 ≤ failureOrder d delta := by
  exact Nat.le_max_left _ _

theorem log2_ratio_le_failureOrder (d : ℕ) (delta : ℝ) :
    Real.logb 2 ((d : ℝ) / delta) ≤ (failureOrder d delta : ℝ) := by
  calc
    Real.logb 2 ((d : ℝ) / delta) ≤
        (⌈Real.logb 2 ((d : ℝ) / delta)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (failureOrder d delta : ℕ) := by
      exact_mod_cast Nat.le_max_right 1 ⌈Real.logb 2 ((d : ℝ) / delta)⌉₊

/-- The base-two ceiling gives `d/delta ≤ 2^q`. -/
theorem ratio_le_two_pow_failureOrder
    {d : ℕ} {delta : ℝ} (hd : 1 ≤ d) (hdelta : 0 < delta) :
    (d : ℝ) / delta ≤ (2 : ℝ) ^ failureOrder d delta := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast Nat.zero_lt_of_lt hd
  have hratio : 0 < (d : ℝ) / delta := div_pos hdReal hdelta
  have hlog := log2_ratio_le_failureOrder d delta
  have hrpow :=
    (Real.logb_le_iff_le_rpow (b := (2 : ℝ)) (by norm_num) hratio).mp hlog
  simpa [Real.rpow_natCast] using hrpow

/-- Equivalently, `2⁻q ≤ delta/d`. -/
theorem half_pow_failureOrder_le
    {d : ℕ} {delta : ℝ} (hd : 1 ≤ d) (hdelta : 0 < delta) :
    ((1 : ℝ) / 2) ^ failureOrder d delta ≤ delta / d := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast Nat.zero_lt_of_lt hd
  have hratio : 0 < (d : ℝ) / delta := div_pos hdReal hdelta
  have hinv := one_div_le_one_div_of_le hratio
    (ratio_le_two_pow_failureOrder hd hdelta)
  calc
    ((1 : ℝ) / 2) ^ failureOrder d delta =
        1 / ((2 : ℝ) ^ failureOrder d delta) := by
      rw [one_div_pow]
    _ ≤ 1 / ((d : ℝ) / delta) := hinv
    _ = delta / d := by field_simp

/-- The failure-order arithmetic in lines 1457--1464. -/
theorem four_pow_failureOrder_le
    {d : ℕ} {delta : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (d : ℝ) * ((1 : ℝ) / 4) ^ failureOrder d delta ≤ delta := by
  let q := failureOrder d delta
  have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdPos : (0 : ℝ) < d := zero_lt_one.trans_le hdReal
  have hhalf : ((1 : ℝ) / 2) ^ q ≤ delta / d := by
    simpa [q] using half_pow_failureOrder_le hd hdelta0
  have hhalf0 : 0 ≤ ((1 : ℝ) / 2) ^ q := by positivity
  have hsq : (((1 : ℝ) / 2) ^ q) ^ 2 ≤ (delta / d) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hhalf0 hhalf
  have hfour : ((1 : ℝ) / 4) ^ q = (((1 : ℝ) / 2) ^ q) ^ 2 := by
    rw [show ((1 : ℝ) / 4) = ((1 : ℝ) / 2) * ((1 : ℝ) / 2) by norm_num]
    simp [mul_pow, pow_two]
  have hfirst : (d : ℝ) * ((1 : ℝ) / 4) ^ q ≤ delta ^ 2 / d := by
    rw [hfour]
    calc
      (d : ℝ) * (((1 : ℝ) / 2) ^ q) ^ 2 ≤
          (d : ℝ) * (delta / d) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hdPos.le
      _ = delta ^ 2 / d := by field_simp
  have hdeltaD : delta ≤ (d : ℝ) := hdelta1.trans hdReal
  have hmul : delta * delta ≤ delta * (d : ℝ) :=
    mul_le_mul_of_nonneg_left hdeltaD hdelta0.le
  have hsecond : delta ^ 2 / (d : ℝ) ≤ delta := by
    apply (div_le_iff₀ hdPos).2
    simpa [pow_two] using hmul
  exact hfirst.trans hsecond

@[simp] theorem cast_Dq (d q : ℕ) :
    (Dq d q : ℝ) = (d : ℝ) + 2 * (q : ℝ) + 1 := by
  simp [Dq]

theorem q_le_Dq (d q : ℕ) : q ≤ Dq d q := by
  simp [Dq]
  omega

theorem Dq_le_two_mul_add {d q : ℕ} (hd : 1 ≤ d) :
    Dq d q ≤ 2 * (d + q) := by
  simp [Dq]
  omega

theorem roundedS_lower (q : ℕ) (epsilon : ℝ) :
    L * ((2 * q + 1 : ℕ) : ℝ) / epsilon ≤ (roundedS q epsilon : ℝ) := by
  simpa [roundedS] using
    (Nat.le_ceil (L * ((2 * q + 1 : ℕ) : ℝ) / epsilon))

theorem roundedS_pos {q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < roundedS q epsilon := by
  have htarget : 0 < L * ((2 * q + 1 : ℕ) : ℝ) / epsilon := by
    exact div_pos (mul_pos L_pos (by positivity)) hepsilon
  have hcast : (0 : ℝ) < roundedS q epsilon :=
    htarget.trans_le (roundedS_lower q epsilon)
  exact_mod_cast hcast

theorem roundedS_lt_add_one {q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (roundedS q epsilon : ℝ) <
      L * ((2 * q + 1 : ℕ) : ℝ) / epsilon + 1 := by
  have htarget : 0 ≤ L * ((2 * q + 1 : ℕ) : ℝ) / epsilon := by
    exact (div_pos (mul_pos L_pos (by positivity)) hepsilon).le
  simpa [roundedS] using Nat.ceil_lt_add_one htarget

/-- The intermediate sparsity estimate used in line 1474 of the report. -/
theorem roundedS_lt_six_L_mul_q_div
    {q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedS q epsilon : ℝ) < 6 * L * (q : ℝ) / epsilon := by
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hcount : (((2 * q + 1 : ℕ) : ℝ)) ≤ 3 * (q : ℝ) := by
    push_cast
    linarith
  have hA :
      L * ((2 * q + 1 : ℕ) : ℝ) / epsilon ≤
        3 * L * (q : ℝ) / epsilon := by
    apply (div_le_div_iff_of_pos_right hepsilon0).2
    have := mul_le_mul_of_nonneg_left hcount L_pos.le
    nlinarith
  have hL : (1 : ℝ) ≤ L := by nlinarith [ninety_lt_L]
  have hLq : (1 : ℝ) ≤ L * (q : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ L * (q : ℝ) := mul_le_mul hL hqReal (by norm_num) L_pos.le
  have hunit : (1 : ℝ) ≤ 3 * L * (q : ℝ) / epsilon := by
    apply (le_div_iff₀ hepsilon0).2
    nlinarith
  calc
    (roundedS q epsilon : ℝ) <
        L * ((2 * q + 1 : ℕ) : ℝ) / epsilon + 1 :=
      roundedS_lt_add_one hepsilon0
    _ ≤ 3 * L * (q : ℝ) / epsilon +
        (3 * L * (q : ℝ) / epsilon) := add_le_add hA hunit
    _ = 6 * L * (q : ℝ) / epsilon := by ring

/-- Certified explicit sparsity bound from line 1475: `s < 1356 q / epsilon`. -/
theorem roundedS_lt_1356
    {q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedS q epsilon : ℝ) < 1356 * (q : ℝ) / epsilon := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hcoefficient : 6 * L < (1356 : ℝ) := by
    nlinarith [L_lt_226]
  have hnumerator : 6 * L * (q : ℝ) < 1356 * (q : ℝ) := by
    exact mul_lt_mul_of_pos_right hcoefficient hqPos
  exact (roundedS_lt_six_L_mul_q_div hq hepsilon0 hepsilon1).trans
    ((div_lt_div_iff_of_pos_right hepsilon0).2 hnumerator)

theorem M0_pos {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < M0 d q epsilon := by
  have hDqNat : 0 < Dq d q := by simp [Dq]
  have hDq : (0 : ℝ) < (Dq d q : ℕ) := by exact_mod_cast hDqNat
  rw [M0]
  exact div_pos (mul_pos (sq_pos_of_pos L_pos) hDq)
    (sq_pos_of_pos hepsilon)

theorem roundedB_lower (d q : ℕ) (epsilon : ℝ) :
    M0 d q epsilon / (roundedS q epsilon : ℝ) ≤
      (roundedB d q epsilon : ℝ) := by
  simpa [roundedB] using
    (Nat.le_ceil (M0 d q epsilon / (roundedS q epsilon : ℝ)))

/-- The first scale condition in line 1432: the rounded row count is at least `M0`. -/
theorem roundedM_lower
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    M0 d q epsilon ≤ (roundedM d q epsilon : ℝ) := by
  let s := roundedS q epsilon
  have hsNat : 0 < s := roundedS_pos hepsilon
  have hs : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hb : M0 d q epsilon / (s : ℝ) ≤ (roundedB d q epsilon : ℝ) := by
    simpa [s] using roundedB_lower d q epsilon
  calc
    M0 d q epsilon = (s : ℝ) * (M0 d q epsilon / (s : ℝ)) := by
      field_simp
    _ ≤ (s : ℝ) * (roundedB d q epsilon : ℝ) :=
      mul_le_mul_of_nonneg_left hb hs.le
    _ = (roundedM d q epsilon : ℕ) := by simp [roundedM, s]

/-- The first scale condition in the literal form displayed in line 1432. -/
theorem roundedM_scale_condition
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    L ^ 2 * (Dq d q : ℝ) / epsilon ^ 2 ≤
      (roundedM d q epsilon : ℝ) := by
  simpa [M0] using roundedM_lower (d := d) (q := q) hepsilon

/-- The exact ceiling estimate `m < M0 + s`. -/
theorem roundedM_lt_M0_add_s
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (roundedM d q epsilon : ℝ) <
      M0 d q epsilon + roundedS q epsilon := by
  let s := roundedS q epsilon
  have hsNat : 0 < s := roundedS_pos hepsilon
  have hs : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hquot : 0 ≤ M0 d q epsilon / (s : ℝ) := by
    exact (div_pos (M0_pos hepsilon) hs).le
  have hb : (roundedB d q epsilon : ℝ) <
      M0 d q epsilon / (s : ℝ) + 1 := by
    simpa [roundedB, s] using Nat.ceil_lt_add_one hquot
  calc
    (roundedM d q epsilon : ℝ) =
        (s : ℝ) * (roundedB d q epsilon : ℝ) := by simp [roundedM, s]
    _ < (s : ℝ) * (M0 d q epsilon / (s : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hb hs
    _ = M0 d q epsilon + s := by field_simp

/-- A coarse comparison showing that the rounded sparsity is below `M0`. -/
theorem roundedS_lt_M0
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedS q epsilon : ℝ) < M0 d q epsilon := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqDq : (q : ℝ) ≤ (Dq d q : ℕ) := by
    exact_mod_cast q_le_Dq d q
  have hsmall : 6 * (q : ℝ) * epsilon < L * (Dq d q : ℕ) := by
    calc
      6 * (q : ℝ) * epsilon ≤ 6 * (q : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hepsilon1
          (by positivity : (0 : ℝ) ≤ 6 * (q : ℝ))
      _ < L * (q : ℝ) := by
        exact mul_lt_mul_of_pos_right (by nlinarith [ninety_lt_L]) hqPos
      _ ≤ L * (Dq d q : ℕ) := mul_le_mul_of_nonneg_left hqDq L_pos.le
  have hcore : 6 * L * (q : ℝ) * epsilon <
      L ^ 2 * (Dq d q : ℕ) := by
    calc
      6 * L * (q : ℝ) * epsilon = L * (6 * (q : ℝ) * epsilon) := by ring
      _ < L * (L * (Dq d q : ℕ)) := mul_lt_mul_of_pos_left hsmall L_pos
      _ = L ^ 2 * (Dq d q : ℕ) := by ring
  have hscaled : 6 * L * (q : ℝ) / epsilon < M0 d q epsilon := by
    rw [M0]
    apply (div_lt_div_iff₀ hepsilon0 (sq_pos_of_pos hepsilon0)).2
    have hmul := mul_lt_mul_of_pos_right hcore hepsilon0
    nlinarith [sq_nonneg epsilon]
  exact (roundedS_lt_six_L_mul_q_div hq hepsilon0 hepsilon1).trans hscaled

/-- The main rounded parameters always have at least two rows per stack. -/
theorem two_le_roundedB
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    2 ≤ roundedB d q epsilon := by
  have hsNat : 0 < roundedS q epsilon := roundedS_pos hepsilon0
  have hs : (0 : ℝ) < roundedS q epsilon := by exact_mod_cast hsNat
  have hsM : (roundedS q epsilon : ℝ) < M0 d q epsilon :=
    roundedS_lt_M0 hq hepsilon0 hepsilon1
  have hratio : (1 : ℝ) < M0 d q epsilon / roundedS q epsilon := by
    apply (lt_div_iff₀ hs).2
    simpa using hsM
  have hbCast : (1 : ℝ) < roundedB d q epsilon :=
    hratio.trans_le (roundedB_lower d q epsilon)
  exact_mod_cast hbCast

theorem two_le_main_roundedB
    {d : ℕ} {delta epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    2 ≤ roundedB d (failureOrder d delta) epsilon :=
  two_le_roundedB (one_le_failureOrder d delta) hepsilon0 hepsilon1

/-- The paper's `m < 2 M0` rounding estimate. -/
theorem roundedM_lt_two_M0
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedM d q epsilon : ℝ) < 2 * M0 d q epsilon := by
  have hm := roundedM_lt_M0_add_s (d := d) (q := q) hepsilon0
  have hs := roundedS_lt_M0 (d := d) hq hepsilon0 hepsilon1
  linarith

theorem roundedM_lt_three_M0
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedM d q epsilon : ℝ) < 3 * M0 d q epsilon := by
  exact (roundedM_lt_two_M0 hq hepsilon0 hepsilon1).trans
    (by nlinarith [M0_pos (d := d) (q := q) hepsilon0])

/-- The numerical upper bound for `3 M0` used in lines 1492--1498. -/
theorem three_M0_lt_306456
    {d q : ℕ} {epsilon : ℝ}
    (hd : 1 ≤ d) (hepsilon : 0 < epsilon) :
    3 * M0 d q epsilon <
      306456 * ((d : ℝ) + q) / epsilon ^ 2 := by
  have hDqNat : Dq d q ≤ 2 * (d + q) := Dq_le_two_mul_add hd
  have hDq : (Dq d q : ℝ) ≤ 2 * ((d : ℝ) + q) := by
    exact_mod_cast hDqNat
  have hDqPosNat : 0 < Dq d q := by simp [Dq]
  have hDqPos : (0 : ℝ) < (Dq d q : ℕ) := by exact_mod_cast hDqPosNat
  have hLsq : L ^ 2 < (226 : ℝ) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self L_pos.le L_lt_226
  have hnum : 3 * (L ^ 2 * (Dq d q : ℕ)) <
      306456 * ((d : ℝ) + q) := by
    calc
      3 * (L ^ 2 * (Dq d q : ℕ)) <
          3 * ((226 : ℝ) ^ 2 * (Dq d q : ℕ)) := by
        exact mul_lt_mul_of_pos_left
          (mul_lt_mul_of_pos_right hLsq hDqPos) (by norm_num)
      _ ≤ 3 * ((226 : ℝ) ^ 2 * (2 * ((d : ℝ) + q))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hDq (by positivity)) (by norm_num)
      _ = 306456 * ((d : ℝ) + q) := by ring
  calc
    3 * M0 d q epsilon =
        (3 * (L ^ 2 * (Dq d q : ℕ))) / epsilon ^ 2 := by
      rw [M0]
      ring
    _ < (306456 * ((d : ℝ) + q)) / epsilon ^ 2 :=
      (div_lt_div_iff_of_pos_right (sq_pos_of_pos hepsilon)).2 hnum
    _ = 306456 * ((d : ℝ) + q) / epsilon ^ 2 := rfl

/-- Certified explicit row bound from line 1497. -/
theorem roundedM_lt_306456
    {d q : ℕ} {epsilon : ℝ}
    (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedM d q epsilon : ℝ) <
      306456 * ((d : ℝ) + q) / epsilon ^ 2 :=
  (roundedM_lt_three_M0 hq hepsilon0 hepsilon1).trans
    (three_M0_lt_306456 hd hepsilon0)

/-- Scalar parameter substitution behind lines 1437--1446. -/
theorem betaEnvelope_le_three_Cband
    {d q : ℕ} {m s epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hm : 0 < m) (hs : 0 < s)
    (hmScale : L ^ 2 * (Dq d q : ℝ) ≤ epsilon ^ 2 * m)
    (hsScale : L * ((2 * q + 1 : ℕ) : ℝ) ≤ epsilon * s) :
    betaEnvelope d q m s ≤ 3 * Cband * epsilon / L := by
  have hL1 : (1 : ℝ) ≤ L := by nlinarith [ninety_lt_L]
  have hepsilonL : epsilon ≤ L := hepsilon1.trans hL1
  have hdense : (Dq d q : ℝ) / m ≤ epsilon ^ 2 / L ^ 2 := by
    apply (div_le_div_iff₀ hm (sq_pos_of_pos L_pos)).2
    nlinarith
  have ht0 : 0 ≤ epsilon / L := (div_pos hepsilon0 L_pos).le
  have ht1 : epsilon / L ≤ 1 := (div_le_one L_pos).2 hepsilonL
  have hlinear : (Dq d q : ℝ) / m ≤ epsilon / L := by
    calc
      (Dq d q : ℝ) / m ≤ epsilon ^ 2 / L ^ 2 := hdense
      _ = (epsilon / L) ^ 2 := by field_simp
      _ ≤ epsilon / L := by nlinarith [sq_nonneg (epsilon / L)]
  have hroot : Real.sqrt ((Dq d q : ℝ) / m) ≤ epsilon / L := by
    rw [Real.sqrt_le_iff]
    exact ⟨ht0, by simpa [div_pow] using hdense⟩
  have hsparse : ((2 * q + 1 : ℕ) : ℝ) / s ≤ epsilon / L := by
    apply (div_le_div_iff₀ hs L_pos).2
    nlinarith
  rw [betaEnvelope]
  have hsum : Real.sqrt ((Dq d q : ℝ) / m) +
      (Dq d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s ≤
        3 * (epsilon / L) := by linarith
  calc
    Cband * (Real.sqrt ((Dq d q : ℝ) / m) +
        (Dq d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s) ≤
        Cband * (3 * (epsilon / L)) :=
      mul_le_mul_of_nonneg_left hsum Cband_pos.le
    _ = 3 * Cband * epsilon / L := by ring

/-- The rounded parameters satisfy the exact beta-envelope substitution. -/
theorem rounded_betaEnvelope_le
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) ≤
      3 * Cband * epsilon / L := by
  have hsNat : 0 < roundedS q epsilon := roundedS_pos hepsilon0
  have hs : (0 : ℝ) < roundedS q epsilon := by exact_mod_cast hsNat
  have hmLower := roundedM_lower (d := d) (q := q) hepsilon0
  have hm : (0 : ℝ) < roundedM d q epsilon :=
    (M0_pos hepsilon0).trans_le hmLower
  have hmScale : L ^ 2 * (Dq d q : ℝ) ≤
      epsilon ^ 2 * (roundedM d q epsilon : ℝ) := by
    have hraw := (div_le_iff₀ (sq_pos_of_pos hepsilon0)).mp
      (by simpa [M0] using hmLower)
    simpa [mul_comm] using hraw
  have hsScale : L * ((2 * q + 1 : ℕ) : ℝ) ≤
      epsilon * (roundedS q epsilon : ℝ) := by
    have hraw := (div_le_iff₀ hepsilon0).mp
      (roundedS_lower q epsilon)
    simpa [mul_comm] using hraw
  exact betaEnvelope_le_three_Cband hepsilon0 hepsilon1 hm hs hmScale hsScale

/-- After convex-order scaling, the rounded envelope has base below
`(3 + sqrt 2)/10`, hence below `0.442` and `1/2`. -/
theorem rounded_moment_base_lt_442
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * cStar ^ 2 *
        betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon <
      (221 : ℝ) / 500 := by
  have hbeta := rounded_betaEnvelope_le (d := d) (q := q) hepsilon0 hepsilon1
  have hscaled :
      3 * cStar ^ 2 *
          betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon ≤
        Cband / 10 := by
    calc
      3 * cStar ^ 2 *
          betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon ≤
          3 * cStar ^ 2 * (3 * Cband * epsilon / L) / epsilon := by
        apply (div_le_div_iff_of_pos_right hepsilon0).2
        exact mul_le_mul_of_nonneg_left hbeta (by positivity)
      _ = Cband / 10 := by
        rw [L]
        field_simp [ne_of_gt cStar_pos, ne_of_gt hepsilon0]
        ring
  exact hscaled.trans_lt Cband_div_ten_lt_442

theorem rounded_moment_base_lt_half
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * cStar ^ 2 *
        betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon <
      (1 : ℝ) / 2 :=
  (rounded_moment_base_lt_442 hepsilon0 hepsilon1).trans (by norm_num)

theorem roundedMomentBase_lt_442
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    roundedMomentBase d q epsilon < (221 : ℝ) / 500 := by
  simpa [roundedMomentBase] using
    rounded_moment_base_lt_442 (d := d) (q := q) hepsilon0 hepsilon1

theorem roundedMomentBase_lt_half
    {d q : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    roundedMomentBase d q epsilon < (1 : ℝ) / 2 := by
  simpa [roundedMomentBase] using
    rounded_moment_base_lt_half (d := d) (q := q) hepsilon0 hepsilon1

theorem roundedMomentBase_nonneg
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 ≤ roundedMomentBase d q epsilon := by
  have hsNat : 0 < roundedS q epsilon := roundedS_pos hepsilon
  have hs : (0 : ℝ) < roundedS q epsilon := by exact_mod_cast hsNat
  have hmLower := roundedM_lower (d := d) (q := q) hepsilon
  have hm : (0 : ℝ) < roundedM d q epsilon :=
    (M0_pos hepsilon).trans_le hmLower
  have hDq : (0 : ℝ) ≤ (Dq d q : ℕ) := by positivity
  have hcount : (0 : ℝ) ≤ ((2 * q + 1 : ℕ) : ℕ) := by positivity
  have hbeta : 0 ≤ betaEnvelope d q (roundedM d q epsilon)
      (roundedS q epsilon) := by
    rw [betaEnvelope]
    exact mul_nonneg Cband_pos.le <| add_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (div_nonneg hDq hm.le))
      (div_nonneg hcount hs.le)
  rw [roundedMomentBase]
  exact div_nonneg (mul_nonneg (by positivity) hbeta) hepsilon.le

/-- The complete scalar failure arithmetic for the rounded v1.4 parameters.
The remaining probabilistic task is to prove that the actual failure
probability is bounded by this scalar expression. -/
theorem rounded_scalar_failure_le_delta
    {d : ℕ} {delta epsilon : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (d : ℝ) *
        (roundedMomentBase d (failureOrder d delta) epsilon) ^
          (2 * failureOrder d delta) ≤ delta := by
  let q := failureOrder d delta
  let rho := roundedMomentBase d q epsilon
  have hrho0 : 0 ≤ rho := by
    simpa [rho, q] using
      roundedMomentBase_nonneg (d := d) (q := failureOrder d delta) hepsilon0
  have hrho : rho ≤ (1 : ℝ) / 2 := by
    exact (roundedMomentBase_lt_half (d := d) (q := q) hepsilon0 hepsilon1).le
  have hpow : rho ^ (2 * q) ≤ ((1 : ℝ) / 2) ^ (2 * q) :=
    pow_le_pow_left₀ hrho0 hrho _
  have hhalfFour : ((1 : ℝ) / 2) ^ (2 * q) = ((1 : ℝ) / 4) ^ q := by
    rw [pow_mul]
    norm_num
  calc
    (d : ℝ) *
        (roundedMomentBase d (failureOrder d delta) epsilon) ^
          (2 * failureOrder d delta) = (d : ℝ) * rho ^ (2 * q) := by
      simp [rho, q]
    _ ≤ (d : ℝ) * (((1 : ℝ) / 2) ^ (2 * q)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (d : ℝ) * ((1 : ℝ) / 4) ^ q := by rw [hhalfFour]
    _ ≤ delta := by
      simpa [q] using four_pow_failureOrder_le hd hdelta0 hdelta1

/-- Canonical scale conditions and explicit dimensions, specialized to the
base-two failure order selected by the paper. -/
theorem main_parameter_package
    {d : ℕ} {delta epsilon : ℝ}
    (hd : 1 ≤ d) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    L * ((2 * failureOrder d delta + 1 : ℕ) : ℝ) / epsilon ≤
        (roundedS (failureOrder d delta) epsilon : ℝ) ∧
    M0 d (failureOrder d delta) epsilon ≤
        (roundedM d (failureOrder d delta) epsilon : ℝ) ∧
    (roundedS (failureOrder d delta) epsilon : ℝ) <
        1356 * (failureOrder d delta : ℝ) / epsilon ∧
    (roundedM d (failureOrder d delta) epsilon : ℝ) <
        306456 * ((d : ℝ) + failureOrder d delta) / epsilon ^ 2 ∧
    2 ≤ roundedB d (failureOrder d delta) epsilon := by
  let q := failureOrder d delta
  have hq : 1 ≤ q := one_le_failureOrder d delta
  exact ⟨roundedS_lower q epsilon,
    roundedM_lower hepsilon0,
    roundedS_lt_1356 hq hepsilon0 hepsilon1,
    roundedM_lt_306456 hd hq hepsilon0 hepsilon1,
    two_le_roundedB hq hepsilon0 hepsilon1⟩

end PaperParameters

end SparseFock
