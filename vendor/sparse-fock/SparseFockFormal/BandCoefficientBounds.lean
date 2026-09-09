import SparseFockFormal.ScalarBounds
import SparseFockFormal.TernaryJacobi
import Mathlib.Tactic

/-!
# Scalar coefficient bounds for normalized sparse-Fock bands

These are the denominator-cleared inequalities used when `m = s * b` and
the heavy Jacobi coefficient is `sqrt (b - 1)`.
-/

namespace SparseFock.BandCoefficientBounds

noncomputable section

/-- The square of the heavy coefficient, divided by the stack height, is at
most `1 / s`. -/
theorem rho_sq_div_stack_le_inv_s {s b : ℕ} (hs : 0 < s) (hb : 1 < b) :
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) ≤ 1 / (s : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbR : (0 : ℝ) < b := by positivity
  rw [TernaryJacobi.sq_sqrt_b_sub_one hb, Nat.cast_mul]
  apply (div_le_div_iff₀ (mul_pos hsR hbR) hsR).2
  nlinarith

/-- The unsquared heavy coefficient, divided by the stack height, is also at
most `1 / s`. -/
theorem rho_div_stack_le_inv_s {s b : ℕ} (hs : 0 < s) (hb : 1 < b) :
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) ≤ 1 / (s : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbR : (0 : ℝ) < b := by positivity
  have hrho0 : 0 ≤ Real.sqrt ((b : ℝ) - 1) := Real.sqrt_nonneg _
  have hrhoSq := TernaryJacobi.sq_sqrt_b_sub_one hb
  have hrhoLe : Real.sqrt ((b : ℝ) - 1) ≤ (b : ℝ) := by
    have hbTwo : (2 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  rw [Nat.cast_mul]
  apply (div_le_div_iff₀ (mul_pos hsR hbR) hsR).2
  nlinarith

theorem rho_div_stack_nonneg {s b : ℕ} :
    0 ≤ Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) := by
  positivity

theorem rho_sq_div_stack_nonneg {s b : ℕ} :
    0 ≤ Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) := by
  positivity

/-- The exact AM--GM absorption used for the `X_+` mixed band. -/
theorem mixed_plus_absorb {s b d nu : ℕ} (hs : 0 < s) (hb : 1 < b) :
    (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1))) ≤
      (1 / 2 : ℝ) *
        (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbR : (0 : ℝ) < b := by positivity
  have hmR : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
  have hnu : (0 : ℝ) ≤ nu := by positivity
  have hD : (0 : ℝ) ≤ (d : ℝ) + nu + 1 := by positivity
  have hh : (0 : ℝ) ≤ (b : ℝ) - 1 := by
    have hbOne : (1 : ℝ) ≤ b := by exact_mod_cast (Nat.le_of_lt hb)
    linarith
  have hsqrtMul :
      Real.sqrt ((b : ℝ) - 1) *
          Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) =
        Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
          Real.sqrt ((d : ℝ) + nu + 1) := by
    rw [Real.sqrt_mul hnu]
    rw [Real.sqrt_mul hh]
    ring
  have hamgm := ScalarBounds.mixed_product_into_envelope
    (show 0 ≤ ((b : ℝ) - 1) * (nu : ℝ) by positivity) hD
  have hheavy :
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) ≤
        (nu : ℝ) / s := by
    have hcoef := rho_sq_div_stack_le_inv_s hs hb
    rw [TernaryJacobi.sq_sqrt_b_sub_one hb] at hcoef
    have hmul := mul_le_mul_of_nonneg_right hcoef hnu
    calc
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) =
          (((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * (nu : ℝ) := by ring
      _ ≤ (1 / (s : ℝ)) * (nu : ℝ) := hmul
      _ = (nu : ℝ) / s := by ring
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) =
        (Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
          Real.sqrt ((d : ℝ) + nu + 1)) / (((s * b : ℕ) : ℝ)) := by
      rw [← hsqrtMul]
      ring
    _ ≤ ((((b : ℝ) - 1) * (nu : ℝ)) + ((d : ℝ) + nu + 1)) /
        2 / (((s * b : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_right hamgm hmR.le
    _ ≤ (1 / 2 : ℝ) *
        (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
      have hsum := add_le_add_right hheavy
        (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)))
      calc
        ((((b : ℝ) - 1) * (nu : ℝ)) + ((d : ℝ) + nu + 1)) /
            2 / (((s * b : ℕ) : ℝ)) =
            (1 / 2 : ℝ) *
              (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
                (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ))) := by
          ring
        _ ≤ (1 / 2 : ℝ) *
            (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
              (nu : ℝ) / s) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- The two `X₀` orientations are absorbed by one dense term and one sparse
term, exactly as in the grade-zero mixed row of the paper. -/
theorem mixed_zero_absorb {s b d nu : ℕ} (hs : 0 < s) (hb : 1 < b) :
    2 * (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu))) ≤
      ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s := by
  have hmR : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
  have hnu : (0 : ℝ) ≤ nu := by positivity
  have hD : (0 : ℝ) ≤ (d : ℝ) + nu := by positivity
  have hh : (0 : ℝ) ≤ (b : ℝ) - 1 := by
    have hbOne : (1 : ℝ) ≤ b := by exact_mod_cast (Nat.le_of_lt hb)
    linarith
  have hsqrtMul :
      Real.sqrt ((b : ℝ) - 1) *
          Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) =
        Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
          Real.sqrt ((d : ℝ) + nu) := by
    rw [Real.sqrt_mul hnu]
    rw [Real.sqrt_mul hh]
    ring
  have hamgm := ScalarBounds.mixed_product_into_envelope
    (show 0 ≤ ((b : ℝ) - 1) * (nu : ℝ) by positivity) hD
  have hcoef := rho_sq_div_stack_le_inv_s hs hb
  rw [TernaryJacobi.sq_sqrt_b_sub_one hb] at hcoef
  have hheavy :
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) ≤
        (nu : ℝ) / s := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hnu
    calc
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) =
          (((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * (nu : ℝ) := by ring
      _ ≤ (1 / (s : ℝ)) * (nu : ℝ) := hmul
      _ = (nu : ℝ) / s := by ring
  calc
    2 * (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu))) =
        (2 / (((s * b : ℕ) : ℝ)) *
          (Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
            Real.sqrt ((d : ℝ) + nu))) := by
      rw [← hsqrtMul]
      ring
    _ ≤ (2 / (((s * b : ℕ) : ℝ)) *
        ((((b : ℝ) - 1) * (nu : ℝ) + ((d : ℝ) + nu)) / 2)) :=
      mul_le_mul_of_nonneg_left hamgm (by positivity)
    _ = (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) +
        ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) := by ring
    _ ≤ ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s := by
      linarith

/-- A directional bound `rho * nu / (s*b)` is absorbed by `nu / s`. -/
theorem directional_absorb {s b nu : ℕ} (hs : 0 < s) (hb : 1 < b) :
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) ≤
      (nu : ℝ) / s := by
  have hcoef := rho_div_stack_le_inv_s hs hb
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) ≤
        (1 / (s : ℝ)) * (nu : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ = (nu : ℝ) / s := by ring

end

end SparseFock.BandCoefficientBounds
