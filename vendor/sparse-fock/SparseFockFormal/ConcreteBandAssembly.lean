import SparseFockFormal.ConcreteLadder
import SparseFockFormal.NamedBands
import SparseFockFormal.BandEnvelope
import Mathlib.Tactic

/-!
# Exact assembly of the three concrete band estimates

This file contains only algebra and norm inequalities.  It rewrites each
normalized physical band into the named light--light, light--heavy, and
heavy--heavy pieces, and combines component estimates with the scalar
envelope proved in `BandEnvelope`.
-/

namespace SparseFock.ConcreteBandAssembly

open scoped Matrix.Norms.L2Operator
open ParsevalFrame BandInventory GlobalBands NamedBands ExternalOperator
open ConcreteLadder FiniteHilbert BandEnvelope

noncomputable section

variable {d m n b : ℕ}

private theorem norm_three_le (A B C : FullOp d m n) :
    ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
  calc
    ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
    _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by
      gcongr
      exact norm_add_le _ _

private theorem normalizedBand_plus_mul_projection
    (F : Frame n d) (nu : ℕ) :
    normalizedBand m F b .plus * gradeProjection (d := d) nu =
      ((1 / (m : ℝ)) • Lplus m (fun i a ↦ F.u i a)) * gradeProjection nu +
      ((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xplus m (fun i a ↦ F.u i a) + Yplus m (fun i a ↦ F.u i a)))) *
            gradeProjection nu +
      ((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 • Hplus m (fun i a ↦ F.u i a))) *
          gradeProjection nu := by
  rw [normalizedBand, band_plus_named]
  simp only [smul_add, add_mul]

private theorem normalizedBand_zero_mul_projection
    (F : Frame n d) (nu : ℕ) :
    normalizedBand m F b .zero * gradeProjection (d := d) nu =
      ((1 / (m : ℝ)) • Lzero m (fun i a ↦ F.u i a)) * gradeProjection nu +
      ((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xzero m (fun i a ↦ F.u i a) + XzeroAdj m (fun i a ↦ F.u i a) +
            Yzero m (fun i a ↦ F.u i a) + YzeroAdj m (fun i a ↦ F.u i a)))) *
              gradeProjection nu +
      ((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 • Hzero m (fun i a ↦ F.u i a))) *
          gradeProjection nu := by
  rw [normalizedBand, band_zero_named]
  simp only [smul_add, add_mul]

private theorem normalizedBand_minus_mul_projection
    (F : Frame n d) (nu : ℕ) :
    normalizedBand m F b .minus * gradeProjection (d := d) nu =
      ((1 / (m : ℝ)) • Lminus m (fun i a ↦ F.u i a)) * gradeProjection nu +
      ((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) •
          (XplusAdj m (fun i a ↦ F.u i a) +
            YplusAdj m (fun i a ↦ F.u i a)))) * gradeProjection nu +
      ((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 • Hminus m (fun i a ↦ F.u i a))) *
          gradeProjection nu := by
  rw [normalizedBand, band_minus_named]
  simp only [smul_add, add_mul]

/-- Exact operator-level assembly for the positive band. -/
theorem plus_band_envelope_of_components
    (F : Frame n d) (nu : ℕ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hlight :
      ‖((1 / (m : ℝ)) • Lplus m (fun i x ↦ F.u i x)) *
        gradeProjection (d := d) nu‖ ≤ a + bTerm d nu m)
    (hmixed :
      ‖((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xplus m (fun i x ↦ F.u i x) + Yplus m (fun i x ↦ F.u i x)))) *
            gradeProjection (d := d) nu‖ ≤ bTerm d nu m + (3 / 2 : ℝ) * c)
    (hheavy :
      ‖((1 / (m : ℝ)) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 • Hplus m (fun i x ↦ F.u i x))) *
          gradeProjection (d := d) nu‖ ≤ c)
    (hbTerm : 0 ≤ bTerm d nu m) :
    ‖normalizedBand m F b .plus * gradeProjection (d := d) nu‖ ≤
      PaperParameters.Cband * (a + bTerm d nu m + c) := by
  rw [normalizedBand_plus_mul_projection]
  calc
    _ ≤
        ‖((1 / (m : ℝ)) • Lplus m (fun i x ↦ F.u i x)) * gradeProjection nu‖ +
        ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) •
          (Xplus m (fun i x ↦ F.u i x) + Yplus m (fun i x ↦ F.u i x)))) *
            gradeProjection nu‖ +
        ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hplus m (fun i x ↦ F.u i x))) * gradeProjection nu‖ := norm_three_le _ _ _
    _ ≤ (a + bTerm d nu m) +
        (bTerm d nu m + (3 / 2 : ℝ) * c) + c := by linarith
    _ = a + 2 * bTerm d nu m + (5 / 2 : ℝ) * c := by ring
    _ ≤ PaperParameters.Cband * (a + bTerm d nu m + c) :=
      plus_row_envelope ha hbTerm hc

/-- Exact operator-level assembly for the grade-preserving band. -/
theorem zero_band_envelope_of_components
    (F : Frame n d) (nu : ℕ) {c : ℝ}
    (hc : 0 ≤ c)
    (hlight :
      ‖((1 / (m : ℝ)) • Lzero m (fun i x ↦ F.u i x)) *
        gradeProjection (d := d) nu‖ ≤ 3 * bTerm d nu m)
    (hmixed :
      ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) •
        (Xzero m (fun i x ↦ F.u i x) + XzeroAdj m (fun i x ↦ F.u i x) +
          Yzero m (fun i x ↦ F.u i x) + YzeroAdj m (fun i x ↦ F.u i x)))) *
            gradeProjection (d := d) nu‖ ≤
        bTerm d nu m + (1 + Real.sqrt 2) * c)
    (hheavy :
      ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) ^ 2 •
        Hzero m (fun i x ↦ F.u i x))) * gradeProjection (d := d) nu‖ ≤ 2 * c)
    (hbTerm : 0 ≤ bTerm d nu m) (ha : 0 ≤ aTerm d nu m) :
    ‖normalizedBand m F b .zero * gradeProjection (d := d) nu‖ ≤
      PaperParameters.Cband * (aTerm d nu m + bTerm d nu m + c) := by
  rw [normalizedBand_zero_mul_projection]
  calc
    _ ≤
        ‖((1 / (m : ℝ)) • Lzero m (fun i x ↦ F.u i x)) * gradeProjection nu‖ +
        ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) •
          (Xzero m (fun i x ↦ F.u i x) + XzeroAdj m (fun i x ↦ F.u i x) +
            Yzero m (fun i x ↦ F.u i x) + YzeroAdj m (fun i x ↦ F.u i x)))) *
              gradeProjection nu‖ +
        ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hzero m (fun i x ↦ F.u i x))) * gradeProjection nu‖ := norm_three_le _ _ _
    _ ≤ 3 * bTerm d nu m +
        (bTerm d nu m + (1 + Real.sqrt 2) * c) + 2 * c := by linarith
    _ = 4 * bTerm d nu m + (3 + Real.sqrt 2) * c := by ring
    _ ≤ PaperParameters.Cband * (aTerm d nu m + bTerm d nu m + c) :=
      zero_row_envelope ha hbTerm hc

/-- Exact operator-level assembly for the negative band. -/
theorem minus_band_envelope_of_components
    (F : Frame n d) (nu : ℕ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hlight :
      ‖((1 / (m : ℝ)) • Lminus m (fun i x ↦ F.u i x)) *
        gradeProjection (d := d) nu‖ ≤ a + bTerm d nu m)
    (hmixed :
      ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) •
        (XplusAdj m (fun i x ↦ F.u i x) + YplusAdj m (fun i x ↦ F.u i x)))) *
          gradeProjection (d := d) nu‖ ≤ bTerm d nu m + (3 / 2 : ℝ) * c)
    (hheavy :
      ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) ^ 2 •
        Hminus m (fun i x ↦ F.u i x))) * gradeProjection (d := d) nu‖ ≤ c)
    (hbTerm : 0 ≤ bTerm d nu m) :
    ‖normalizedBand m F b .minus * gradeProjection (d := d) nu‖ ≤
      PaperParameters.Cband * (a + bTerm d nu m + c) := by
  rw [normalizedBand_minus_mul_projection]
  calc
    _ ≤
        ‖((1 / (m : ℝ)) • Lminus m (fun i x ↦ F.u i x)) * gradeProjection nu‖ +
        ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) •
          (XplusAdj m (fun i x ↦ F.u i x) + YplusAdj m (fun i x ↦ F.u i x)))) *
            gradeProjection nu‖ +
        ‖((1 / (m : ℝ)) • (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hminus m (fun i x ↦ F.u i x))) * gradeProjection nu‖ := norm_three_le _ _ _
    _ ≤ (a + bTerm d nu m) +
        (bTerm d nu m + (3 / 2 : ℝ) * c) + c := by linarith
    _ = a + 2 * bTerm d nu m + (5 / 2 : ℝ) * c := by ring
    _ ≤ PaperParameters.Cband * (a + bTerm d nu m + c) :=
      plus_row_envelope ha hbTerm hc

end

end SparseFock.ConcreteBandAssembly
