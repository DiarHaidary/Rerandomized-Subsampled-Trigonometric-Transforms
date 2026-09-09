import SparseFockFormal.DirectionalConcrete
import SparseFockFormal.BandCoefficientBounds
import Mathlib.Tactic

/-!
# Normalized directional mixed-band estimates

This module transports the concrete directional estimates to the named
adjoint operators and then inserts the exact normalization
`sqrt (b - 1) / (s*b)` used by the sparse-stack model.
-/

namespace SparseFock

namespace DirectionalNormalized

open ParsevalFrame BandInventory GlobalBands NamedBands ExternalOperator
  FiniteHilbert DirectionalConcrete BandCoefficientBounds
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d m n : ℕ}

theorem l2_norm_transpose (A : FullOp d m n) : ‖A.transpose‖ = ‖A‖ := by
  have h : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose]
  rw [← h]
  exact Matrix.l2_opNorm_conjTranspose A

/-- The paper's named `Y₊†` is literally the matrix transpose of `Y₊`. -/
@[simp] theorem transpose_Yplus (u : Fin n → Fin d → ℝ) :
    (Yplus m u).transpose = YplusAdj m u := by
  simpa [Yplus, YplusAdj, wordSum, Word.orderedAdjoint, Leg.adjoint] using
    transpose_physicalWordSum (m := m) u (.rUp, .pUp)

@[simp] theorem transpose_YplusAdj (u : Fin n → Fin d → ℝ) :
    (YplusAdj m u).transpose = Yplus m u := by
  rw [← transpose_Yplus (m := m) u, Matrix.transpose_transpose]

/-- The paper's named `Y₀†` is literally the matrix transpose of `Y₀`. -/
@[simp] theorem transpose_Yzero (u : Fin n → Fin d → ℝ) :
    (Yzero m u).transpose = YzeroAdj m u := by
  simpa [Yzero, YzeroAdj, wordSum, Word.orderedAdjoint, Leg.adjoint] using
    transpose_physicalWordSum (m := m) u (.rDown, .pUp)

@[simp] theorem transpose_YzeroAdj (u : Fin n → Fin d → ℝ) :
    (YzeroAdj m u).transpose = Yzero m u := by
  rw [← transpose_Yzero (m := m) u, Matrix.transpose_transpose]

theorem YplusAdj_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous (-2) (YplusAdj m (frameRows F)) := by
  simpa [YplusAdj, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.pDown, .rDown)

theorem YzeroAdj_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0 (YzeroAdj m (frameRows F)) := by
  simpa [YzeroAdj, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (frameRows F) (.pDown, .rUp)

/-- A homogeneous matrix intertwines the two compatible exact-grade
projections.  This is stronger than merely inserting an output projection
after an already restricted operator. -/
theorem gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
    {delta : ℤ} {A : FullOp d m n}
    (hA : ExternalOperator.Homogeneous delta A) (mu nu : ℕ)
    (hcompatible : (mu : ℤ) = (nu : ℤ) + delta) :
    gradeProjection (d := d) mu * A = A * gradeProjection nu := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hentry : A out inp = 0
  · simp [hentry]
  · have hrel := homogeneous_grade_relation hA hentry
    have hiff : out.2.grade = mu ↔ inp.2.grade = nu := by
      constructor
      · intro hout
        have hinInt : (inp.2.grade : ℤ) = (nu : ℤ) := by
          rw [hout] at hrel
          omega
        exact_mod_cast hinInt
      · intro hin
        have houtInt : (out.2.grade : ℤ) = (mu : ℤ) := by
          rw [hin] at hrel
          omega
        exact_mod_cast houtInt
    by_cases hout : out.2.grade = mu
    · simp [hout, hiff.mp hout]
    · have hin : inp.2.grade ≠ nu := fun h ↦ hout (hiff.mpr h)
      simp [hout, hin]

/-- Exact shifted adjoint bound: on grade `nu+2`, `Y₊†` has the same norm as
`Y₊` on grade `nu`. -/
theorem norm_YplusAdj_restricted_add_two_le (F : Frame n d) (nu : ℕ) :
    ‖YplusAdj m (frameRows F) * gradeProjection (d := d) (nu + 2)‖ ≤
      (nu : ℝ) := by
  calc
    ‖YplusAdj m (frameRows F) * gradeProjection (d := d) (nu + 2)‖ =
        ‖(YplusAdj m (frameRows F) *
          gradeProjection (d := d) (nu + 2)).transpose‖ := by
      exact (l2_norm_transpose
        (YplusAdj m (frameRows F) *
          gradeProjection (d := d) (nu + 2))).symm
    _ = ‖gradeProjection (d := d) (nu + 2) *
          Yplus m (frameRows F)‖ := by
      rw [Matrix.transpose_mul, transpose_YplusAdj,
        gradeProjection_transpose]
    _ = ‖Yplus m (frameRows F) * gradeProjection (d := d) nu‖ := by
      rw [gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Yplus_homogeneous (m := m) F) (nu + 2) nu (by norm_num)]
    _ ≤ (nu : ℝ) := norm_Yplus_restricted_le (m := m) F nu

/-- Uniform same-grade notation for the adjoint bound.  The two bottom grades
vanish; above them the exact shifted estimate is even smaller than `nu`. -/
theorem norm_YplusAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖YplusAdj m (frameRows F) * gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) := by
  by_cases hnu : 2 ≤ nu
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnu
    have h := norm_YplusAdj_restricted_add_two_le (m := m) F k
    calc
      ‖YplusAdj m (frameRows F) * gradeProjection (d := d) (2 + k)‖ =
          ‖YplusAdj m (frameRows F) * gradeProjection (d := d) (k + 2)‖ := by
        rw [Nat.add_comm]
      _ ≤ (k : ℝ) := h
      _ ≤ ((2 + k : ℕ) : ℝ) := by
        exact_mod_cast (show k ≤ 2 + k by omega)
  · have himpossible : ∀ mu : ℕ,
        (mu : ℤ) ≠ (nu : ℤ) + (-2) := by
      intro mu hmu
      have hnuLt : nu < 2 := Nat.lt_of_not_ge hnu
      have hmuNonneg : (0 : ℤ) ≤ (mu : ℤ) := by positivity
      omega
    have hz := input_grade_vanishes_of_no_output
      (YplusAdj_homogeneous (m := m) F) nu himpossible
    rw [hz]
    simp

/-- Since `Y₀` preserves grade, transpose invariance gives exactly the same
restricted norm for its named adjoint. -/
theorem norm_YzeroAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖YzeroAdj m (frameRows F) * gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / Real.sqrt 2 := by
  calc
    ‖YzeroAdj m (frameRows F) * gradeProjection (d := d) nu‖ =
        ‖(YzeroAdj m (frameRows F) *
          gradeProjection (d := d) nu).transpose‖ := by
      exact (l2_norm_transpose
        (YzeroAdj m (frameRows F) *
          gradeProjection (d := d) nu)).symm
    _ = ‖gradeProjection (d := d) nu * Yzero m (frameRows F)‖ := by
      rw [Matrix.transpose_mul, transpose_YzeroAdj,
        gradeProjection_transpose]
    _ = ‖Yzero m (frameRows F) * gradeProjection (d := d) nu‖ := by
      rw [gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Yzero_homogeneous (m := m) F) nu nu (by norm_num)]
    _ ≤ (nu : ℝ) / Real.sqrt 2 := norm_Yzero_restricted_le (m := m) F nu

/-- Exact L2-norm scaling for the normalized heavy-light coefficient. -/
theorem norm_normalized_directional_term_eq {s b : ℕ}
    (A : FullOp d m n) (P : FullOp d m n) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • A)) * P‖ =
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * ‖A * P‖ := by
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
      0 ≤ (1 : ℝ) / (((s * b : ℕ) : ℝ))),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Normalized `Y₊` contribution at exactly the paper constant `nu/s`. -/
theorem norm_normalized_Yplus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • Yplus (s * b) (frameRows F))) *
          gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / s := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖Yplus (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (DirectionalConcrete.norm_Yplus_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ ≤ (nu : ℝ) / s := directional_absorb hs hb

/-- Normalized `Y₊†` contribution, with the same uniform paper constant. -/
theorem norm_normalized_YplusAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • YplusAdj (s * b) (frameRows F))) *
          gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / s := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖YplusAdj (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (norm_YplusAdj_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ ≤ (nu : ℝ) / s := directional_absorb hs hb

/-- Each normalized `Y₀` orientation contributes at most
`(nu/s)/sqrt 2`. -/
theorem norm_normalized_Yzero_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • Yzero (s * b) (frameRows F))) *
          gradeProjection (d := d) nu‖ ≤
      ((nu : ℝ) / s) / Real.sqrt 2 := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖Yzero (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          ((nu : ℝ) / Real.sqrt 2) := by
      exact mul_le_mul_of_nonneg_left
        (DirectionalConcrete.norm_Yzero_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ = (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          (nu : ℝ)) / Real.sqrt 2 := by ring
    _ ≤ ((nu : ℝ) / s) / Real.sqrt 2 := by
      exact div_le_div_of_nonneg_right (directional_absorb hs hb)
        (Real.sqrt_nonneg 2)

/-- The named normalized `Y₀†` orientation has the identical constant. -/
theorem norm_normalized_YzeroAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • YzeroAdj (s * b) (frameRows F))) *
          gradeProjection (d := d) nu‖ ≤
      ((nu : ℝ) / s) / Real.sqrt 2 := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖YzeroAdj (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          ((nu : ℝ) / Real.sqrt 2) := by
      exact mul_le_mul_of_nonneg_left
        (norm_YzeroAdj_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ = (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          (nu : ℝ)) / Real.sqrt 2 := by ring
    _ ≤ ((nu : ℝ) / s) / Real.sqrt 2 := by
      exact div_le_div_of_nonneg_right (directional_absorb hs hb)
        (Real.sqrt_nonneg 2)

/-- The two grade-preserving `Y` orientations together contribute exactly the
paper's `sqrt 2 * nu/s` allowance. -/
theorem norm_normalized_Yzero_pair_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Yzero (s * b) (frameRows F) +
            YzeroAdj (s * b) (frameRows F)))) *
          gradeProjection (d := d) nu‖ ≤
      Real.sqrt 2 * ((nu : ℝ) / s) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Yzero (s * b) (frameRows F) +
              YzeroAdj (s * b) (frameRows F)))) *
            gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • Yzero (s * b) (frameRows F))) *
            gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • YzeroAdj (s * b) (frameRows F))) *
            gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • Yzero (s * b) (frameRows F))) *
            gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • YzeroAdj (s * b) (frameRows F))) *
            gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ 2 * (((nu : ℝ) / s) / Real.sqrt 2) := by
      have h₁ := norm_normalized_Yzero_restricted_le F s b nu hs hb
      have h₂ := norm_normalized_YzeroAdj_restricted_le F s b nu hs hb
      linarith
    _ = Real.sqrt 2 * ((nu : ℝ) / s) := by
      have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      field_simp [ne_of_gt hsqrtPos]
      nlinarith

end

end DirectionalNormalized

end SparseFock
