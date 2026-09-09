import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic
import SparseFockFormal.LadderEndgame

/-!
# Conditional probabilistic and parameter endgame

This file proves the measure-theoretic Markov inequality needed by the moment
method, its scalar cancellation step, the `q`/failure arithmetic, and integer
rounding at the constants in the candidate assembly.

The moment-transfer theorem is intentionally conditional.  Its hypotheses
`hconvex` and `hladder` are the numerical inequalities that would have to be
supplied by the unformalized convex-order and operator/Fock arguments.
-/

open scoped ENNReal

namespace SparseFock

namespace ProbabilisticEndgame

open MeasureTheory

/-- Markov's inequality applied directly to the `2q`-th power of an
`ℝ≥0∞`-valued random variable. -/
theorem markov_even_power
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ≥0∞) (hX : AEMeasurable X μ) (threshold : ℝ≥0∞) (q : ℕ) :
    threshold ^ (2 * q) * μ {ω | threshold ^ (2 * q) ≤ X ω ^ (2 * q)} ≤
      ∫⁻ ω, X ω ^ (2 * q) ∂μ := by
  exact mul_meas_ge_le_lintegral₀ (hX.pow_const (2 * q)) (threshold ^ (2 * q))

/-- The scalar cancellation step after Markov and a `2q`-moment estimate. -/
theorem markov_scalar_cancel
    {q : ℕ} {ε failure moment d rho : ℝ}
    (hε : 0 < ε)
    (hmarkov : ε ^ (2 * q) * failure ≤ moment)
    (hmoment : moment ≤ d * (rho * ε) ^ (2 * q)) :
    failure ≤ d * rho ^ (2 * q) := by
  apply (mul_le_mul_iff_left₀ (pow_pos hε (2 * q))).mp
  calc
    failure * ε ^ (2 * q) = ε ^ (2 * q) * failure := by ring
    _ ≤ moment := hmarkov
    _ ≤ d * (rho * ε) ^ (2 * q) := hmoment
    _ = (d * rho ^ (2 * q)) * ε ^ (2 * q) := by
      rw [mul_pow]
      ring

/-- Conditional composition of convex-order moment transfer and the scalar
three-band ladder moment estimate.

`hconvex` and `hladder` expose, rather than assume implicitly, the two
unformalized operator/probability inputs. -/
theorem conditional_moment_transfer
    {q : ℕ} {sourceMoment iidMoment c d beta rho ε : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hbeta : 0 ≤ beta)
    (hconvex : sourceMoment ≤ c ^ (4 * q) * iidMoment)
    (hladder : iidMoment ≤ d * (3 * beta) ^ (2 * q))
    (hscale : 3 * c ^ 2 * beta ≤ rho * ε) :
    sourceMoment ≤ d * (rho * ε) ^ (2 * q) := by
  have hcPow : c ^ (4 * q) = (c ^ 2) ^ (2 * q) := by
    calc
      c ^ (4 * q) = c ^ (2 * (2 * q)) := by
        congr 1
        omega
      _ = (c ^ 2) ^ (2 * q) := by rw [pow_mul]
  have hcombined :
      c ^ (4 * q) * (d * (3 * beta) ^ (2 * q)) =
        d * (3 * c ^ 2 * beta) ^ (2 * q) := by
    rw [hcPow]
    calc
      (c ^ 2) ^ (2 * q) * (d * (3 * beta) ^ (2 * q)) =
          d * ((c ^ 2) ^ (2 * q) * (3 * beta) ^ (2 * q)) := by ring
      _ = d * ((c ^ 2 * (3 * beta)) ^ (2 * q)) := by
        congr 1
        exact (mul_pow (c ^ 2) (3 * beta) (2 * q)).symm
      _ = d * (3 * c ^ 2 * beta) ^ (2 * q) := by
        congr 1
        ring
  calc
    sourceMoment ≤ c ^ (4 * q) * iidMoment := hconvex
    _ ≤ c ^ (4 * q) * (d * (3 * beta) ^ (2 * q)) := by
      exact mul_le_mul_of_nonneg_left hladder (pow_nonneg hc _)
    _ = d * (3 * c ^ 2 * beta) ^ (2 * q) := hcombined
    _ ≤ d * (rho * ε) ^ (2 * q) := by
      apply mul_le_mul_of_nonneg_left _ hd
      exact pow_le_pow_left₀ (by positivity) hscale _

/-- The integer moment order used by the candidate SparseStack assembly. -/
noncomputable def failureOrder (d δ : ℝ) : ℕ := max 1 ⌈Real.log (d / δ)⌉₊

theorem one_le_failureOrder (d δ : ℝ) : 1 ≤ failureOrder d δ := by
  exact Nat.le_max_left _ _

theorem log_ratio_le_failureOrder (d δ : ℝ) :
    Real.log (d / δ) ≤ (failureOrder d δ : ℝ) := by
  calc
    Real.log (d / δ) ≤ (⌈Real.log (d / δ)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (failureOrder d δ : ℕ) := by
      exact_mod_cast Nat.le_max_right 1 ⌈Real.log (d / δ)⌉₊

/-- The logarithmic failure arithmetic, in a slightly stronger `e^{-q}` form. -/
theorem exp_failure_bound
    {d δ q : ℝ}
    (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hq : Real.log (d / δ) ≤ q) :
    d * Real.exp (-2 * q) ≤ δ := by
  have hratio : 0 < d / δ := div_pos (lt_of_lt_of_le zero_lt_one hd) hδ0
  have hratioOne : 1 < d / δ := by
    rw [one_lt_div hδ0]
    exact hδ1.trans_le hd
  have hq0 : 0 ≤ q := by
    exact (Real.log_pos hratioOne).le.trans hq
  have hexp : d / δ ≤ Real.exp q := by
    calc
      d / δ = Real.exp (Real.log (d / δ)) := (Real.exp_log hratio).symm
      _ ≤ Real.exp q := Real.exp_le_exp.mpr hq
  have hdle : d ≤ δ * Real.exp q := by
    have := (div_le_iff₀ hδ0).mp hexp
    simpa [mul_comm] using this
  have hminus : Real.exp (-2 * q) ≤ Real.exp (-q) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    d * Real.exp (-2 * q) ≤ d * Real.exp (-q) :=
      mul_le_mul_of_nonneg_left hminus (le_trans zero_le_one hd)
    _ ≤ (δ * Real.exp q) * Real.exp (-q) :=
      mul_le_mul_of_nonneg_right hdle (Real.exp_pos _).le
    _ = δ := by
      rw [mul_assoc, ← Real.exp_add]
      simp

/-- If a moment base is at most `e⁻¹`, the chosen integer moment order drives
the scalar failure term below `δ`. -/
theorem failureOrder_power_bound
    {d δ rho : ℝ}
    (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hrho0 : 0 ≤ rho) (hrho : rho ≤ Real.exp (-1)) :
    d * rho ^ (2 * failureOrder d δ) ≤ δ := by
  let q := failureOrder d δ
  have hpow : rho ^ (2 * q) ≤ Real.exp (-1) ^ (2 * q) :=
    pow_le_pow_left₀ hrho0 hrho _
  calc
    d * rho ^ (2 * q) ≤ d * Real.exp (-1) ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hpow (le_trans zero_le_one hd)
    _ = d * Real.exp (-2 * (q : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    _ ≤ δ := exp_failure_bound hd hδ0 hδ1 (log_ratio_le_failureOrder d δ)

/-- Complete scalar/probabilistic endgame, conditional on the convex-order,
ladder-moment, and Markov inequalities displayed as hypotheses. -/
theorem conditional_final_failure
    {d δ ε c beta normMoment sourceMoment iidMoment failure : ℝ}
    (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hc : 0 ≤ c) (hbeta : 0 ≤ beta)
    (hconvex : sourceMoment ≤
      c ^ (4 * failureOrder d δ) * iidMoment)
    (hladder : iidMoment ≤
      d * (3 * beta) ^ (2 * failureOrder d δ))
    (hmarkov : ε ^ (2 * failureOrder d δ) * failure ≤ normMoment)
    (hnormTrace : normMoment ≤ sourceMoment)
    (hscale : 3 * c ^ 2 * beta ≤ Real.exp (-1) * ε) :
    failure ≤ δ := by
  have hmoment : sourceMoment ≤
      d * (Real.exp (-1) * ε) ^ (2 * failureOrder d δ) :=
    conditional_moment_transfer hc (le_trans zero_le_one hd) hbeta hconvex hladder hscale
  have hfailure : failure ≤
      d * Real.exp (-1) ^ (2 * failureOrder d δ) :=
    markov_scalar_cancel hε (hmarkov.trans hnormTrace) hmoment
  exact hfailure.trans <|
    failureOrder_power_bound hd hδ0 hδ1 (Real.exp_pos _).le le_rfl

/-- The exact decimal/rational comparison used in the candidate endgame. -/
theorem assembly_failure_base_le_exp_neg_one :
    (81 : ℝ) / 500 ≤ Real.exp (-1) := by
  exact (by norm_num : (81 : ℝ) / 500 ≤ 0.36787944116).trans
    Real.exp_neg_one_gt_d9.le

/-- Arithmetic for `c² ≤ 2.51` and `beta ≤ 0.0215 ε`: the final moment
base is at most `0.162 ε`. -/
theorem assembly_scale_bound
    {c beta ε : ℝ}
    (hε : 0 ≤ ε) (hbeta0 : 0 ≤ beta)
    (hc : c ^ 2 ≤ (251 : ℝ) / 100)
    (hbeta : beta ≤ (43 : ℝ) / 2000 * ε) :
    3 * c ^ 2 * beta ≤ (81 : ℝ) / 500 * ε := by
  calc
    3 * c ^ 2 * beta ≤ 3 * ((251 : ℝ) / 100) * beta := by
      nlinarith [mul_nonneg hbeta0 (sq_nonneg c)]
    _ ≤ 3 * ((251 : ℝ) / 100) * ((43 : ℝ) / 2000 * ε) := by
      exact mul_le_mul_of_nonneg_left hbeta (by norm_num)
    _ ≤ (81 : ℝ) / 500 * ε := by nlinarith

/-- Substitution of the candidate choices `K₁ = 250000`, `K₂ = 1000` into
the assembled band envelope.  The only non-arithmetic input is `hband`, the
displayed bound on `beta`. -/
theorem candidate_beta_parameter_bound
    {d q m s ε beta : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hm : 0 < m) (hs : 0 < s)
    (hmScale : 250000 * (d + q) ≤ ε ^ 2 * m)
    (hsScale : 1000 * q ≤ ε * s)
    (hband : beta ≤ Real.sqrt (3 * (d + q) / m) +
      6 * (d + q) / m + 18 * q / s) :
    beta ≤ (43 : ℝ) / 2000 * ε := by
  have hdense : (d + q) / m ≤ ε ^ 2 / 250000 := by
    apply (div_le_iff₀ hm).2
    nlinarith
  have hsparse : q / s ≤ ε / 1000 := by
    apply (div_le_iff₀ hs).2
    nlinarith
  have hεsq : ε ^ 2 ≤ ε := by nlinarith [sq_nonneg ε]
  have hlinear : 6 * (d + q) / m ≤ (6 : ℝ) / 250000 * ε := by
    have := mul_le_mul_of_nonneg_left hdense (by norm_num : (0 : ℝ) ≤ 6)
    calc
      6 * (d + q) / m = 6 * ((d + q) / m) := by ring
      _ ≤ 6 * (ε ^ 2 / 250000) := this
      _ = (6 : ℝ) / 250000 * ε ^ 2 := by ring
      _ ≤ (6 : ℝ) / 250000 * ε :=
        mul_le_mul_of_nonneg_left hεsq (by norm_num)
  have hsparseTerm : 18 * q / s ≤ (18 : ℝ) / 1000 * ε := by
    have := mul_le_mul_of_nonneg_left hsparse (by norm_num : (0 : ℝ) ≤ 18)
    calc
      18 * q / s = 18 * (q / s) := by ring
      _ ≤ 18 * (ε / 1000) := this
      _ = (18 : ℝ) / 1000 * ε := by ring
  have hrootSq : 3 * (d + q) / m ≤ ((26 : ℝ) / 7500 * ε) ^ 2 := by
    have hthree := mul_le_mul_of_nonneg_left hdense (by norm_num : (0 : ℝ) ≤ 3)
    have hcoefficient : (3 : ℝ) / 250000 ≤ ((26 : ℝ) / 7500) ^ 2 := by
      norm_num
    have hscaled := mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg ε)
    calc
      3 * (d + q) / m = 3 * ((d + q) / m) := by ring
      _ ≤ 3 * (ε ^ 2 / 250000) := hthree
      _ = (3 : ℝ) / 250000 * ε ^ 2 := by ring
      _ ≤ ((26 : ℝ) / 7500) ^ 2 * ε ^ 2 := hscaled
      _ = ((26 : ℝ) / 7500 * ε) ^ 2 := by ring
  have hroot : Real.sqrt (3 * (d + q) / m) ≤ (26 : ℝ) / 7500 * ε := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hrootSq⟩
  nlinarith

/-- The conditional endgame with the numerical constants from the candidate
assembly.  The operator/probability inputs remain the four displayed moment
hypotheses. -/
theorem conditional_final_failure_numeric
    {d δ ε c beta normMoment sourceMoment iidMoment failure : ℝ}
    (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hc0 : 0 ≤ c) (hbeta0 : 0 ≤ beta)
    (hc2 : c ^ 2 ≤ (251 : ℝ) / 100)
    (hconvex : sourceMoment ≤
      c ^ (4 * failureOrder d δ) * iidMoment)
    (hladder : iidMoment ≤
      d * (3 * beta) ^ (2 * failureOrder d δ))
    (hmarkov : ε ^ (2 * failureOrder d δ) * failure ≤ normMoment)
    (hnormTrace : normMoment ≤ sourceMoment)
    (hbeta : beta ≤ (43 : ℝ) / 2000 * ε) :
    failure ≤ δ := by
  have hbase : 3 * c ^ 2 * beta ≤ Real.exp (-1) * ε := by
    calc
      3 * c ^ 2 * beta ≤ (81 : ℝ) / 500 * ε :=
        assembly_scale_bound hε.le hbeta0 hc2 hbeta
      _ ≤ Real.exp (-1) * ε :=
        mul_le_mul_of_nonneg_right assembly_failure_base_le_exp_neg_one hε.le
  exact conditional_final_failure hd hδ0 hδ1 hε hc0 hbeta0
    hconvex hladder hmarkov hnormTrace hbase

/-- Lower and factor-two upper bounds for a nonnegative natural ceiling. -/
theorem natCeil_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  constructor
  · exact Nat.le_ceil x
  · exact (Nat.ceil_lt_add_one (by linarith)).le.trans (by linarith)

/-- Rounded sparsity. -/
noncomputable def roundedS (q : ℕ) (ε : ℝ) : ℕ := ⌈1000 * (q : ℝ) / ε⌉₊

/-- Rounded stack count after rounding the sparsity. -/
noncomputable def roundedB (d q : ℕ) (ε : ℝ) : ℕ :=
  ⌈250000 * ((d : ℝ) + q) / (ε ^ 2 * roundedS q ε)⌉₊

/-- Rounded row count, divisible by the rounded sparsity. -/
noncomputable def roundedM (d q : ℕ) (ε : ℝ) : ℕ := roundedS q ε * roundedB d q ε

theorem roundedS_bounds
    {q : ℕ} {ε : ℝ} (hq : 1 ≤ q) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    1000 * (q : ℝ) / ε ≤ (roundedS q ε : ℝ) ∧
      (roundedS q ε : ℝ) ≤ 2000 * (q : ℝ) / ε := by
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx : 1 ≤ 1000 * (q : ℝ) / ε := by
    apply (le_div_iff₀ hε0).2
    nlinarith
  have hb := natCeil_bounds hx
  constructor
  · simpa [roundedS] using hb.1
  · calc
      (roundedS q ε : ℝ) ≤ 2 * (1000 * (q : ℝ) / ε) := by
        simpa [roundedS] using hb.2
      _ = 2000 * (q : ℝ) / ε := by ring

theorem roundedS_pos
    {q : ℕ} {ε : ℝ} (hq : 1 ≤ q) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < roundedS q ε := by
  have hs := (roundedS_bounds hq hε0 hε1).1
  have : (0 : ℝ) < roundedS q ε :=
    (div_pos (mul_pos (by norm_num) (by exact_mod_cast Nat.zero_lt_of_lt hq)) hε0).trans_le hs
  exact_mod_cast this

/-- Exact lower row bound and the rounded upper row bound from the candidate
parameter choice. -/
theorem roundedM_bounds
    {d q : ℕ} {ε : ℝ}
    (hd : 1 ≤ d) (hq : 1 ≤ q) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    250000 * ((d : ℝ) + q) / ε ^ 2 ≤ (roundedM d q ε : ℝ) ∧
      (roundedM d q ε : ℝ) ≤
        252000 * ((d : ℝ) + q) / ε ^ 2 := by
  let s := roundedS q ε
  let target := 250000 * ((d : ℝ) + q) / ε ^ 2
  have hsNat : 0 < s := roundedS_pos hq hε0 hε1
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hdq : (0 : ℝ) < (d : ℝ) + q := by positivity
  have htarget : 0 < target := by
    dsimp [target]
    positivity
  have hquot : target / (s : ℝ) =
      250000 * ((d : ℝ) + q) / (ε ^ 2 * s) := by
    dsimp [target]
    field_simp
  have hbLower : target / (s : ℝ) ≤ (roundedB d q ε : ℝ) := by
    rw [hquot]
    simpa [roundedB, s] using
      (Nat.le_ceil (250000 * ((d : ℝ) + q) / (ε ^ 2 * s)))
  have hbUpper : (roundedB d q ε : ℝ) ≤ target / (s : ℝ) + 1 := by
    have := (Nat.ceil_lt_add_one (le_of_lt (div_pos htarget hsReal))).le
    rw [hquot]
    simpa [roundedB, s] using
      (Nat.ceil_lt_add_one (le_of_lt (by positivity :
        0 < 250000 * ((d : ℝ) + q) / (ε ^ 2 * s)))).le
  have hmLower : target ≤ (roundedM d q ε : ℝ) := by
    calc
      target = (s : ℝ) * (target / (s : ℝ)) := by field_simp
      _ ≤ (s : ℝ) * (roundedB d q ε : ℝ) :=
        mul_le_mul_of_nonneg_left hbLower hsReal.le
      _ = (roundedM d q ε : ℕ) := by simp [roundedM, s]
  have hmUpper : (roundedM d q ε : ℝ) ≤ target + s := by
    calc
      (roundedM d q ε : ℝ) = (s : ℝ) * (roundedB d q ε : ℝ) := by simp [roundedM, s]
      _ ≤ (s : ℝ) * (target / (s : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hbUpper hsReal.le
      _ = target + s := by field_simp
  have hsUpper : (s : ℝ) ≤ 2000 * (q : ℝ) / ε := by
    simpa [s] using (roundedS_bounds hq hε0 hε1).2
  have hsAbsorb : 2000 * (q : ℝ) / ε ≤
      2000 * ((d : ℝ) + q) / ε ^ 2 := by
    have hdReal : (0 : ℝ) ≤ d := by positivity
    have hqReal : (0 : ℝ) ≤ q := by positivity
    have hqeps : (q : ℝ) * ε ≤ (d : ℝ) + q := by
      have hmul := mul_le_mul_of_nonneg_left hε1 hqReal
      nlinarith
    have hqeps' := mul_le_mul_of_nonneg_right hqeps hε0.le
    apply (div_le_div_iff₀ hε0 (sq_pos_of_pos hε0)).2
    nlinarith
  constructor
  · simpa [target] using hmLower
  · calc
      (roundedM d q ε : ℝ) ≤ target + s := hmUpper
      _ ≤ target + 2000 * ((d : ℝ) + q) / ε ^ 2 :=
        by simpa [add_comm] using add_le_add_left (hsUpper.trans hsAbsorb) target
      _ = 252000 * ((d : ℝ) + q) / ε ^ 2 := by
        dsimp [target]
        ring

/-- The rounded parameters simultaneously meet the lower theorem hypotheses
and retain the claimed constant-factor upper bounds. -/
theorem rounded_parameter_package
    {d q : ℕ} {ε : ℝ}
    (hd : 1 ≤ d) (hq : 1 ≤ q) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    1000 * (q : ℝ) / ε ≤ (roundedS q ε : ℝ) ∧
    (roundedS q ε : ℝ) ≤ 2000 * (q : ℝ) / ε ∧
    250000 * ((d : ℝ) + q) / ε ^ 2 ≤ (roundedM d q ε : ℝ) ∧
    (roundedM d q ε : ℝ) ≤ 252000 * ((d : ℝ) + q) / ε ^ 2 ∧
    roundedM d q ε = roundedS q ε * roundedB d q ε := by
  exact ⟨(roundedS_bounds hq hε0 hε1).1,
    (roundedS_bounds hq hε0 hε1).2,
    (roundedM_bounds hd hq hε0 hε1).1,
    (roundedM_bounds hd hq hε0 hε1).2,
    rfl⟩

end ProbabilisticEndgame

end SparseFock


