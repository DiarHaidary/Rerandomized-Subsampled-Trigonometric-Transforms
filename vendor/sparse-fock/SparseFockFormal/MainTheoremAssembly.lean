import SparseFockFormal.ConcreteMomentEndgame
import SparseFockFormal.SparseStackModel
import Mathlib.Tactic

/-!
# Assembly record for the explicit SparseStack theorem

This module packages every displayed conclusion of the main theorem: the
literal operator-norm tail, its equivalent vector OSE success event, the exact
column sparsity, the rounded parameter lower bounds, and the strict explicit
size bounds.  The assembly theorem still accepts the concrete band envelope;
the final module supplies it from the operator estimates.
-/

namespace SparseFock.MainTheoremAssembly

open scoped Matrix.Norms.L2Operator
open ParsevalFrame SparseStackModel SparseStackDistribution
open PaperParameters ConcreteLadder FiniteHilbert

noncomputable section

theorem canonicalS_pos {d : ℕ} {delta eps : ℝ} (heps : 0 < eps) :
    0 < roundedS (failureOrder d delta) eps :=
  roundedS_pos heps

theorem canonicalB_pos {d : ℕ} {delta eps : ℝ}
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    0 < roundedB d (failureOrder d delta) eps := by
  have h := two_le_main_roundedB (d := d) (delta := delta) heps0 heps1
  omega

/-- Every mathematical conclusion asserted in TeX Theorem 1.1 for a fixed
Parseval frame. -/
structure MainConclusions {n d : ℕ} (delta eps : ℝ) (F : Frame n d)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) : Prop where
  operatorFailure :
    (rawSampleLaw (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
      {z | eps < ‖gramError F (toSample z)‖} ≤ delta
  oseSuccess :
    1 - delta ≤
      (rawSampleLaw (roundedS (failureOrder d delta) eps)
          (roundedB d (failureOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
        {z | MatrixTail.IsSparseStackOSE F (toSample z) eps}
  exactColumnSparsity :
    ∀ (z : RawSample (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n) (i : Fin n),
      Fintype.card
        {r : Fin (roundedS (failureOrder d delta) eps) ×
            Fin (roundedB d (failureOrder d delta) eps) //
          stackMatrix (toSample z) r i ≠ 0} =
        roundedS (failureOrder d delta) eps
  qAtLeastOne : 1 ≤ failureOrder d delta
  sparsityLower :
    L * ((2 * failureOrder d delta + 1 : ℕ) : ℝ) / eps ≤
      (roundedS (failureOrder d delta) eps : ℝ)
  rowsLower :
    M0 d (failureOrder d delta) eps ≤
      (roundedM d (failureOrder d delta) eps : ℝ)
  sparsityStrict :
    (roundedS (failureOrder d delta) eps : ℝ) <
      1356 * (failureOrder d delta : ℝ) / eps
  rowsStrict :
    (roundedM d (failureOrder d delta) eps : ℝ) <
      306456 * ((d : ℝ) + failureOrder d delta) / eps ^ 2
  bAtLeastTwo : 2 ≤ roundedB d (failureOrder d delta) eps
  rowsFactor :
    roundedM d (failureOrder d delta) eps =
      roundedS (failureOrder d delta) eps *
        roundedB d (failureOrder d delta) eps

/-- All non-operator parts of the main theorem are automatic once the actual
uniform concrete band estimate is supplied. -/
theorem main_conclusions_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * failureOrder d delta →
      ‖normalizedBand (roundedM d (failureOrder d delta) eps) F
          (roundedB d (failureOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        betaEnvelope d (failureOrder d delta)
          (roundedM d (failureOrder d delta) eps)
          (roundedS (failureOrder d delta) eps)) :
    MainConclusions delta eps F heps0 heps1 := by
  have hparams := main_parameter_package
    (d := d) (delta := delta) hd heps0 heps1
  rcases hparams with ⟨hsLower, hmLower, hsStrict, hmStrict, hbTwo⟩
  refine
    { operatorFailure :=
        ConcreteMomentEndgame.rounded_operator_norm_failure_le_delta_of_band_bounds
          hd hdelta0 hdelta1 heps0 heps1 F hband
      oseSuccess :=
        ConcreteMomentEndgame.rounded_success_probability_of_band_bounds
          hd hdelta0 hdelta1 heps0 heps1 F hband
      exactColumnSparsity := ?_
      qAtLeastOne := one_le_failureOrder d delta
      sparsityLower := hsLower
      rowsLower := hmLower
      sparsityStrict := hsStrict
      rowsStrict := hmStrict
      bAtLeastTwo := hbTwo
      rowsFactor := roundedM_eq_s_mul_b d (failureOrder d delta) eps }
  intro z i
  exact exactly_s_nonzeros_per_column (toSample z)
    (canonicalS_pos (d := d) (delta := delta) heps0) i

end

end SparseFock.MainTheoremAssembly
