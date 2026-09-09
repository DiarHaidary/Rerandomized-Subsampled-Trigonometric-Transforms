import SparseFockFormal.ConcreteBandEnvelope
import SparseFockFormal.MainTheoremAssembly
import SparseFockFormal.IndependentFrameAssembly
import SparseFockFormal.MatrixFrameBridge
import Mathlib.Tactic

/-!
# Explicit fully independent SparseStack theorem

This is the hypothesis-free endpoint corresponding to TeX Theorem 1.1.  It
is stated first for the exact Parseval-frame model used in the proof and then
for a literal matrix `U` with `Uᵀ U = I`.
-/

namespace SparseFock.MainTheorem

open scoped Matrix.Norms.L2Operator
open ParsevalFrame SparseStackModel SparseStackDistribution
open PaperParameters ConcreteLadder FiniteHilbert
open MainTheoremAssembly ConcreteBandEnvelope MatrixFrameBridge

noncomputable section

/-- The paper's concrete band proposition, specialized to its rounded integer
parameters.  This is the last operator input formerly present in the
conditional endgame. -/
theorem rounded_band_bound
    {n d : ℕ} {delta eps : ℝ}
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (shift : BandInventory.Shift) (nu : ℕ)
    (hnu : nu ≤ 2 * failureOrder d delta) :
    ‖normalizedBand (roundedM d (failureOrder d delta) eps) F
          (roundedB d (failureOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
      betaEnvelope d (failureOrder d delta)
        (roundedM d (failureOrder d delta) eps)
        (roundedS (failureOrder d delta) eps) := by
  have hs : 0 < roundedS (failureOrder d delta) eps := roundedS_pos heps0
  have hbTwo : 2 ≤ roundedB d (failureOrder d delta) eps :=
    two_le_main_roundedB (d := d) (delta := delta) heps0 heps1
  have hb : 1 < roundedB d (failureOrder d delta) eps := by omega
  rw [roundedM_eq_s_mul_b]
  exact concrete_band_bound_le_beta F
    (roundedS (failureOrder d delta) eps)
    (roundedB d (failureOrder d delta) eps)
    (failureOrder d delta) nu hs hb hnu shift

/-- Hypothesis-free fixed-frame form of the full theorem. -/
theorem fully_independent_sparseStack
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d) :
    MainConclusions delta eps F heps0 heps1 := by
  apply main_conclusions_of_band_bounds hd hdelta0 hdelta1 heps0 heps1 F
  intro shift nu hnu
  exact rounded_band_bound heps0 heps1 F shift nu hnu

/-- Literal matrix-vector version of the OSE event in the displayed theorem. -/
def IsMatrixSparseStackOSE {s b n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ) (Z : Sample s b n) (eps : ℝ) : Prop :=
  ∀ x : EVec d,
    (1 - eps) * ‖x‖ ^ 2 ≤
        ‖MatrixTail.applyRectMatrix (stackMatrix Z * U) x‖ ^ 2 ∧
      ‖MatrixTail.applyRectMatrix (stackMatrix Z * U) x‖ ^ 2 ≤
        (1 + eps) * ‖x‖ ^ 2

/-- Every conclusion of TeX Theorem 1.1 in the source matrix notation. -/
structure MatrixMainConclusions {n d : ℕ} (delta eps : ℝ)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) : Prop where
  operatorFailure :
    (rawSampleLaw (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
      {z | eps <
        ‖U.transpose * (sketchGram (toSample z) * U) - 1‖} ≤ delta
  oseSuccess :
    1 - delta ≤
      (rawSampleLaw (roundedS (failureOrder d delta) eps)
          (roundedB d (failureOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
        {z | IsMatrixSparseStackOSE U (toSample z) eps}
  exactColumnSparsity :
    ∀ (z : RawSample (roundedS (failureOrder d delta) eps)
        (roundedB d (failureOrder d delta) eps) n) (i : Fin n),
      Fintype.card
        {r : Fin (roundedS (failureOrder d delta) eps) ×
            Fin (roundedB d (failureOrder d delta) eps) //
          stackMatrix (toSample z) r i ≠ 0} =
        roundedS (failureOrder d delta) eps
  qAtLeastOne : 1 ≤ failureOrder d delta
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

/-- Literal matrix form of the explicit theorem. -/
theorem fully_independent_sparseStack_matrix
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    MatrixMainConclusions delta eps U heps0 heps1 := by
  let F := frameOfMatrix U hU
  have hmain : MainConclusions delta eps F heps0 heps1 :=
    fully_independent_sparseStack hd hdelta0 hdelta1 heps0 heps1 F
  refine
    { operatorFailure := ?_
      oseSuccess := ?_
      exactColumnSparsity := hmain.exactColumnSparsity
      qAtLeastOne := hmain.qAtLeastOne
      sparsityStrict := hmain.sparsityStrict
      rowsStrict := hmain.rowsStrict
      bAtLeastTwo := hmain.bAtLeastTwo
      rowsFactor := hmain.rowsFactor }
  · simpa [F] using hmain.operatorFailure
  · simpa [F, IsMatrixSparseStackOSE, MatrixTail.IsSparseStackOSE] using
      hmain.oseSuccess

/-- Conditioning corollary for an arbitrary finite law of frames independent
of the fully independent SparseStack sample. -/
theorem fully_independent_sparseStack_independent_frame
    {Omega : Type*} [Fintype Omega]
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (frameLaw : FiniteLaw Omega) (frames : Omega → Frame n d) :
    1 - delta ≤
      (FiniteLaw.product frameLaw
        (rawSampleLaw (roundedS (failureOrder d delta) eps)
          (roundedB d (failureOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1))).prob
        {outcome | MatrixTail.IsSparseStackOSE (frames outcome.1)
          (toSample outcome.2) eps} := by
  apply IndependentFrameAssembly.independent_frame_ose_success_of_band_bounds
    hd hdelta0 hdelta1 heps0 heps1 frameLaw frames
  intro omega shift nu hnu
  exact rounded_band_bound heps0 heps1 (frames omega) shift nu hnu

end

end SparseFock.MainTheorem
