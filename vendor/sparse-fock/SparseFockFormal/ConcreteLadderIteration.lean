import SparseFockFormal.ConcreteLadder
import Mathlib.Tactic

/-!
# Concrete finite ladder iteration

The three grade bands are actual finite Euclidean matrices.  This file
expands their powers into ordered words, inserts the exact grade projections,
and proves the closed vacuum-word estimate used by the moment method.
-/

namespace SparseFock.ConcreteLadderIteration

open scoped BigOperators Matrix.Norms.L2Operator
open ParsevalFrame BandInventory ExternalOperator FiniteHilbert ConcreteLadder

noncomputable section

variable {m n d b : ℕ}

/-- A word stored in application order: its head acts first (at the right end
of the corresponding matrix product). -/
def BandWord : ℕ → Type
  | 0 => Fin 1
  | N + 1 => Shift × BandWord N

instance bandWordFintype (N : ℕ) : Fintype (BandWord N) := by
  induction N with
  | zero => simp [BandWord]; infer_instance
  | succ N _ih => simp [BandWord]; infer_instance

instance bandWordDecidableEq (N : ℕ) : DecidableEq (BandWord N) := by
  induction N with
  | zero => simp [BandWord]; infer_instance
  | succ N _ih => simp [BandWord]; infer_instance

@[simp] theorem card_shift : Fintype.card Shift = 3 := by decide

@[simp] theorem card_bandWord (N : ℕ) : Fintype.card (BandWord N) = 3 ^ N := by
  induction N with
  | zero => simp [BandWord]
  | succ N ih => simp [BandWord, ih, pow_succ, mul_comm]

/-- Ordered matrix product of one band word. -/
def wordOperator (B : Shift → FullOp d m n) :
    {N : ℕ} → BandWord N → FullOp d m n
  | 0, _ => 1
  | _ + 1, w => wordOperator B w.2 * B w.1

/-- The exact (partial) grade walk followed by a band word. -/
def walkGradeFrom : {N : ℕ} → ℕ → BandWord N → Option ℕ
  | 0, nu, _ => some nu
  | _ + 1, nu, w =>
      (nextGrade w.1 nu).bind fun mu => walkGradeFrom mu w.2

/-- Expanding a power of the three-band sum gives precisely the sum of all
ordered band words. -/
theorem sum_wordOperator_eq_pow (B : Shift → FullOp d m n) (N : ℕ) :
    (∑ w : BandWord N, wordOperator B w) = (∑ delta : Shift, B delta) ^ N := by
  induction N with
  | zero =>
      change (∑ _w : Fin 1, (1 : FullOp d m n)) = 1
      have hU : (Finset.univ : Finset (Fin 1)) = {0} := by
        ext w
        fin_cases w
        simp
      rw [hU]
      simp
  | succ N ih =>
      rw [show (∑ w : BandWord (N + 1), wordOperator B w) =
          ∑ delta : Shift, ∑ w : BandWord N, wordOperator B w * B delta by
        simp [BandWord, wordOperator, Fintype.sum_prod_type]]
      simp_rw [← Finset.sum_mul]
      rw [← Finset.mul_sum, ih, pow_succ]

theorem nextGrade_forward_le {delta : Shift} {nu mu : ℕ}
    (h : nextGrade delta nu = some mu) : mu ≤ nu + 2 := by
  cases delta with
  | plus => simp [nextGrade] at h; omega
  | zero => simp [nextGrade] at h; omega
  | minus =>
      simp only [nextGrade] at h
      split at h
      · simp at h; omega
      · simp at h

theorem nextGrade_backward_le {delta : Shift} {nu mu : ℕ}
    (h : nextGrade delta nu = some mu) : nu ≤ mu + 2 := by
  cases delta with
  | plus => simp [nextGrade] at h; omega
  | zero => simp [nextGrade] at h; omega
  | minus =>
      simp only [nextGrade] at h
      split at h
      · simp at h; omega
      · simp at h

/-- If a remaining word can return grade `nu` to the vacuum, then `nu` is at
most twice the number of remaining factors. -/
theorem startGrade_le_twice_length_of_walk_to_zero
    {N nu : ℕ} (w : BandWord N)
    (h : walkGradeFrom nu w = some 0) : nu ≤ 2 * N := by
  induction N generalizing nu with
  | zero =>
      simpa [BandWord, walkGradeFrom] using Option.some.inj h
  | succ N ih =>
      rcases w with ⟨delta, w⟩
      simp only [walkGradeFrom] at h
      cases hnext : nextGrade delta nu with
      | none => simp [hnext] at h
      | some mu =>
          simp only [hnext, Option.bind_some] at h
          have hmu : mu ≤ 2 * N := ih w h
          have hback : nu ≤ mu + 2 := nextGrade_backward_le hnext
          omega

/-- A word which does not return the input grade to grade zero has zero
vacuum-output block. -/
theorem projected_word_eq_zero_of_walk_ne_zero
    (F : Frame n d) (B : Shift → FullOp d m n)
    (hhom : ∀ delta, ExternalOperator.Homogeneous delta.degree (B delta))
    {N nu : ℕ} (w : BandWord N)
    (hwalk : walkGradeFrom nu w ≠ some 0) :
    gradeProjection (d := d) 0 * wordOperator B w * gradeProjection nu = 0 := by
  induction N generalizing nu with
  | zero =>
      have hnu : nu ≠ 0 := by
        intro h
        subst nu
        exact hwalk rfl
      simpa [BandWord, wordOperator] using
        (FiniteHilbert.gradeProjection_mul_gradeProjection
          (d := d) (m := m) (n := n) (Ne.symm hnu))
  | succ N ih =>
      rcases w with ⟨delta, w⟩
      cases hnext : nextGrade delta nu with
      | none =>
          have hz : B delta * gradeProjection (d := d) nu = 0 := by
            apply FiniteHilbert.input_grade_vanishes_of_no_output (hhom delta) nu
            exact nextGrade_none_impossible hnext
          change gradeProjection (d := d) 0 *
            (wordOperator B w * B delta) * gradeProjection nu = 0
          calc
            gradeProjection (d := d) 0 *
                (wordOperator B w * B delta) * gradeProjection nu =
                gradeProjection (d := d) 0 * wordOperator B w *
                  (B delta * gradeProjection nu) := by noncomm_ring
            _ = 0 := by rw [hz, mul_zero]
      | some mu =>
          have hrest : walkGradeFrom mu w ≠ some 0 := by
            simpa [walkGradeFrom, hnext] using hwalk
          have ihz := ih w hrest
          have hins : gradeProjection (d := d) mu * B delta * gradeProjection nu =
              B delta * gradeProjection nu := by
            apply FiniteHilbert.output_projection_of_homogeneous (hhom delta)
            exact nextGrade_compatible hnext
          change gradeProjection (d := d) 0 *
            (wordOperator B w * B delta) * gradeProjection nu = 0
          calc
            gradeProjection (d := d) 0 *
                  (wordOperator B w * B delta) * gradeProjection nu =
                gradeProjection (d := d) 0 * wordOperator B w *
                  (B delta * gradeProjection nu) := by noncomm_ring
            _ = gradeProjection (d := d) 0 * wordOperator B w *
                  (gradeProjection mu * B delta * gradeProjection nu) := by
                    rw [hins]
            _ =
                (gradeProjection (d := d) 0 * wordOperator B w *
                  gradeProjection mu) * (B delta * gradeProjection nu) := by
                    noncomm_ring
            _ = 0 := by rw [ihz, zero_mul]

/-- Every closed word of length `2q`, restricted from and to the vacuum
grade, has norm at most `beta^(2q)` whenever all bands up to grade `2q` obey
the common bound. -/
theorem closed_projected_word_norm_le
    (F : Frame n d) (B : Shift → FullOp d m n)
    (hhom : ∀ delta, ExternalOperator.Homogeneous delta.degree (B delta))
    {q t N nu : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ delta nu, nu ≤ 2 * q →
      ‖B delta * gradeProjection (d := d) nu‖ ≤ beta)
    (w : BandWord N) (hlen : t + N = 2 * q)
    (hstart : nu ≤ 2 * t)
    (hwalk : walkGradeFrom nu w = some 0) :
    ‖gradeProjection (d := d) 0 * wordOperator B w * gradeProjection nu‖ ≤
      beta ^ N := by
  induction N generalizing t nu with
  | zero =>
      have hnu : nu = 0 := by
        simpa [BandWord, walkGradeFrom] using Option.some.inj hwalk
      subst nu
      simpa [BandWord, wordOperator] using
        (FiniteHilbert.gradeProjection_norm_le_one
          (d := d) (m := m) (n := n) 0)
  | succ N ih =>
      rcases w with ⟨delta, w⟩
      cases hnext : nextGrade delta nu with
      | none => simp [walkGradeFrom, hnext] at hwalk
      | some mu =>
          have hrest : walkGradeFrom mu w = some 0 := by
            simpa [walkGradeFrom, hnext] using hwalk
          have hnuBack : nu ≤ 2 * (N + 1) :=
            startGrade_le_twice_length_of_walk_to_zero ⟨delta, w⟩ hwalk
          have hnuQ : nu ≤ 2 * q := by
            by_cases htq : t ≤ q
            · exact hstart.trans (by omega)
            · omega
          have hmuStart : mu ≤ 2 * (t + 1) := by
            have := nextGrade_forward_le hnext
            omega
          have hlen' : (t + 1) + N = 2 * q := by omega
          have ihbound := ih (t := t + 1) (nu := mu) w hlen' hmuStart hrest
          have hstep := hband delta nu hnuQ
          have hins : gradeProjection (d := d) mu * B delta * gradeProjection nu =
              B delta * gradeProjection nu := by
            apply FiniteHilbert.output_projection_of_homogeneous (hhom delta)
            exact nextGrade_compatible hnext
          change ‖gradeProjection (d := d) 0 *
            (wordOperator B w * B delta) * gradeProjection nu‖ ≤ beta ^ (N + 1)
          calc
            ‖gradeProjection (d := d) 0 *
                (wordOperator B w * B delta) * gradeProjection nu‖ =
                ‖gradeProjection (d := d) 0 * wordOperator B w *
                  (B delta * gradeProjection nu)‖ := by
                    congr 1
                    noncomm_ring
            _ = ‖gradeProjection (d := d) 0 * wordOperator B w *
                  (gradeProjection mu * B delta * gradeProjection nu)‖ := by
                    rw [hins]
            _ =
                ‖(gradeProjection (d := d) 0 * wordOperator B w *
                    gradeProjection mu) * (B delta * gradeProjection nu)‖ := by
                  congr 1
                  noncomm_ring
            _ ≤ ‖gradeProjection (d := d) 0 * wordOperator B w *
                    gradeProjection mu‖ * ‖B delta * gradeProjection nu‖ :=
              norm_mul_le _ _
            _ ≤ beta ^ N * beta := by
              exact mul_le_mul ihbound hstep (norm_nonneg _) (pow_nonneg hbeta _)
            _ = beta ^ (N + 1) := by rw [pow_succ]

/-- Uniform projected-word bound, including invalid and nonclosed words. -/
theorem projected_word_norm_le
    (F : Frame n d) (B : Shift → FullOp d m n)
    (hhom : ∀ delta, ExternalOperator.Homogeneous delta.degree (B delta))
    {q : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ delta nu, nu ≤ 2 * q →
      ‖B delta * gradeProjection (d := d) nu‖ ≤ beta)
    (w : BandWord (2 * q)) :
    ‖gradeProjection (d := d) 0 * wordOperator B w * gradeProjection 0‖ ≤
      beta ^ (2 * q) := by
  by_cases hwalk : walkGradeFrom 0 w = some 0
  · exact closed_projected_word_norm_le F B hhom hbeta hband w
      (t := 0) (by omega) (by omega) hwalk
  · rw [projected_word_eq_zero_of_walk_ne_zero F B hhom w hwalk, norm_zero]
    exact pow_nonneg hbeta _

/-- Summing all `3^(2q)` words gives the concrete projected-power norm
estimate. -/
theorem projected_power_norm_le
    (F : Frame n d) (B : Shift → FullOp d m n)
    (hhom : ∀ delta, ExternalOperator.Homogeneous delta.degree (B delta))
    {q : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ delta nu, nu ≤ 2 * q →
      ‖B delta * gradeProjection (d := d) nu‖ ≤ beta) :
    ‖gradeProjection (d := d) 0 * (∑ delta : Shift, B delta) ^ (2 * q) *
        gradeProjection 0‖ ≤ (3 * beta) ^ (2 * q) := by
  have hexpand :
      gradeProjection (d := d) 0 * (∑ delta : Shift, B delta) ^ (2 * q) *
          gradeProjection 0 =
        ∑ w : BandWord (2 * q),
          gradeProjection (d := d) 0 * wordOperator B w * gradeProjection 0 := by
    rw [← sum_wordOperator_eq_pow]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [hexpand]
  calc
    ‖∑ w : BandWord (2 * q),
        gradeProjection (d := d) 0 * wordOperator B w * gradeProjection 0‖ ≤
        ∑ w : BandWord (2 * q),
          ‖gradeProjection (d := d) 0 * wordOperator B w * gradeProjection 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w : BandWord (2 * q), beta ^ (2 * q) := by
      exact Finset.sum_le_sum fun w _ ↦
        projected_word_norm_le F B hhom hbeta hband w
    _ = (3 * beta) ^ (2 * q) := by
      simp [mul_pow]

/-- A single entry is bounded by the Euclidean L2 operator norm. -/
theorem abs_entry_le_l2_opNorm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (i j : I) : |A i j| ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ I := EuclideanSpace.single j 1
  let y : EuclideanSpace ℝ I :=
    (EuclideanSpace.equiv I ℝ).symm (Matrix.mulVec A e)
  have hcoord : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ ‖A‖ * ‖e‖ := by
    simpa [y] using Matrix.l2_opNorm_mulVec A e
  calc
    |A i j| = ‖y i‖ := by
      simp [y, e, Matrix.mulVec, Real.norm_eq_abs]
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖A‖ * ‖e‖ := hop
    _ = ‖A‖ := by simp [e]

/-- The projected-power norm estimate controls the sum of the `d` vacuum
diagonal matrix elements. -/
theorem vacuum_diagonal_sum_le
    (F : Frame n d) (B : Shift → FullOp d m n)
    (hhom : ∀ delta, ExternalOperator.Homogeneous delta.degree (B delta))
    {q : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ delta nu, nu ≤ 2 * q →
      ‖B delta * gradeProjection (d := d) nu‖ ≤ beta) :
    (∑ a : Fin d,
      ((∑ delta : Shift, B delta) ^ (2 * q))
        (a, ProductFock.vacuumPattern m n)
        (a, ProductFock.vacuumPattern m n)) ≤
      (d : ℝ) * (3 * beta) ^ (2 * q) := by
  let T : FullOp d m n := ∑ delta : Shift, B delta
  let A : FullOp d m n :=
    gradeProjection (d := d) 0 * T ^ (2 * q) * gradeProjection 0
  have hA : ‖A‖ ≤ (3 * beta) ^ (2 * q) := by
    simpa [A, T] using projected_power_norm_le F B hhom hbeta hband
  have hdiag (a : Fin d) :
      (T ^ (2 * q)) (a, ProductFock.vacuumPattern m n)
          (a, ProductFock.vacuumPattern m n) =
        A (a, ProductFock.vacuumPattern m n)
          (a, ProductFock.vacuumPattern m n) := by
    simp [A, gradeProjection, Matrix.diagonal_mul, Matrix.mul_diagonal,
      ConcreteLadder.vacuumPattern_grade]
  calc
    (∑ a : Fin d,
      ((∑ delta : Shift, B delta) ^ (2 * q))
        (a, ProductFock.vacuumPattern m n)
        (a, ProductFock.vacuumPattern m n)) =
        ∑ a : Fin d, (T ^ (2 * q))
          (a, ProductFock.vacuumPattern m n)
          (a, ProductFock.vacuumPattern m n) := by rfl
    _ ≤ ∑ _a : Fin d, (3 * beta) ^ (2 * q) := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [hdiag]
      calc
        A (a, ProductFock.vacuumPattern m n)
            (a, ProductFock.vacuumPattern m n) ≤
            |A (a, ProductFock.vacuumPattern m n)
              (a, ProductFock.vacuumPattern m n)| := le_abs_self _
        _ ≤ ‖A‖ := abs_entry_le_l2_opNorm A _ _
        _ ≤ (3 * beta) ^ (2 * q) := hA
    _ = (d : ℝ) * (3 * beta) ^ (2 * q) := by simp

/-- Concrete iid trace-moment estimate from actual restricted band bounds. -/
theorem iid_trace_moment_le_of_band_bounds
    (hb : 1 < b) (F : Frame n d) {q : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hband : ∀ delta nu, nu ≤ 2 * q →
      ‖normalizedBand m F b delta * gradeProjection (d := d) nu‖ ≤ beta) :
    (ProductFock.iidLaw b hb m n).expect
        (fun omega ↦ Matrix.trace ((VacuumMoment.iidGramError b F omega) ^
          (2 * q))) ≤
      (d : ℝ) * (3 * beta) ^ (2 * q) := by
  rw [← ConcreteLadder.vacuum_moment_identity_bands hb F (2 * q)]
  exact vacuum_diagonal_sum_le F (normalizedBand m F b)
    (fun delta ↦ normalizedBand_homogeneous F b delta) hbeta hband

end

end SparseFock.ConcreteLadderIteration
