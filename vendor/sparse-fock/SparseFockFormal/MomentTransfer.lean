import SparseFockFormal.DistributionBridges
import SparseFockFormal.TracePowerConvexity
import Mathlib.Tactic

/-!
# Exact trace-moment transfer identities

This file contains the algebraic and distributional equalities needed to pass
from the finite sparse-selector model to the iid product-Fock model.  It does
not assume the analytic moment estimate.
-/

namespace SparseFock.MomentTransfer

open scoped BigOperators InnerProductSpace Matrix
open ParsevalFrame SparseStackModel SparseStackDistribution
open SparseIIDCoupling SparseIIDTransfer SparseIIDUnconditional
open ProductFock VacuumMoment DistributionBridges
open TracePowerConvexity

noncomputable section

variable {s b n d : ℕ}

/-- Trace of a matrix power is homogeneous of the corresponding degree. -/
theorem trace_pow_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    ((r • A) ^ k).trace = r ^ k * (A ^ k).trace := by
  rw [smul_pow]
  exact Matrix.trace_smul (r ^ k) (A ^ k)

/-- Scaling both iid vectors by `c_b` scales the `2q`-trace moment by
`c_b^(4q)`. -/
theorem scaledIIDVectorError_trace_even (F : Frame n d)
    (y : YArray b s n) (q : ℕ) :
    ((scaledIIDVectorError F y) ^ (2 * q)).trace =
      cB b ^ (4 * q) * ((iidVectorError F y) ^ (2 * q)).trace := by
  rw [scaledIIDVectorError_eq_smul, trace_pow_smul]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

/-- The sparse-selector trace moment is literally the raw SparseStack trace
moment under the identical finite law. -/
theorem selector_trace_moment_eq_raw (hs : 0 < s) (hb : 0 < b)
    (F : Frame n d) (q : ℕ) :
    (selectorArrayLaw hb s n).expect
        (fun x ↦ ((sparseVectorError F x) ^ (2 * q)).trace) =
      (rawSampleLaw s b n hb).expect
        (fun ω ↦ ((gramError F (toSample ω)) ^ (2 * q)).trace) := by
  rw [selectorArrayLaw_eq_rawSampleLaw]
  apply (rawSampleLaw s b n hb).expect_congr
  intro x
  rw [sparseVectorError_eq_gramError hs]

/-- The unscaled iid-vector trace moment is exactly the product-Fock trace
moment after the proved finite-coordinate flattening. -/
theorem iid_trace_moment_eq_product (hs : 0 < s) (hb : 1 < b)
    (F : Frame n d) (q : ℕ) :
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((iidVectorError F y) ^ (2 * q)).trace) =
      (iidLaw b hb (s * b) n).expect
        (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) := by
  calc
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((iidVectorError F y) ^ (2 * q)).trace) =
        (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ ((iidGramError b F (flattenY y)) ^ (2 * q)).trace) := by
      apply (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect_congr
      intro y
      rw [iidVectorError_eq_flattened_iidGramError hs hb]
    _ = (iidLaw b hb (s * b) n).expect
        (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) :=
      iidArrayLaw_expect_flatten_eq_iidLaw_expect
        (s := s) (n := n) hb
        (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace)

/-- Full algebraic factor in the iid side of the convex-order transfer. -/
theorem scaled_iid_trace_moment_eq_product (hs : 0 < s) (hb : 1 < b)
    (F : Frame n d) (q : ℕ) :
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) =
      cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) := by
  calc
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) =
        (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ cB b ^ (4 * q) *
            ((iidVectorError F y) ^ (2 * q)).trace) := by
      apply (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect_congr
      intro y
      exact scaledIIDVectorError_trace_even F y q
    _ = cB b ^ (4 * q) *
        (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ ((iidVectorError F y) ^ (2 * q)).trace) := by
      exact FiniteLaw.expect_smul _ _ _
    _ = cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) := by
      rw [iid_trace_moment_eq_product hs hb F q]

/-- The proved convexity of the even trace power instantiates the full
unconditional sparse--iid convex order. -/
theorem unconditional_trace_moment_order (hb : 0 < b)
    (F : Frame n d) (q : ℕ) :
    (selectorArrayLaw hb s n).expect
        (fun x ↦ ((sparseVectorError F x) ^ (2 * q)).trace) ≤
      (iidArrayLaw hb s n).expect
        (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) := by
  simpa [TracePowerConvexity.traceEvenPower, sparseSymmetricError,
    scaledIIDSymmetricError] using
      (SparseIIDUnconditional.unconditional_convex_order hb F
        (TracePowerConvexity.traceEvenPower (d := d) q)
        (TracePowerConvexity.convexOn_traceEvenPower d q))

/-- Exact distribution-level convex-moment bridge from the literal raw
SparseStack law to the product-Fock iid law. -/
theorem raw_trace_moment_le_scaled_product (hs : 0 < s) (hb : 1 < b)
    (F : Frame n d) (q : ℕ) :
    (rawSampleLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
        (fun z ↦ ((gramError F (toSample z)) ^ (2 * q)).trace) ≤
      cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega ↦ ((iidGramError b F omega) ^ (2 * q)).trace) := by
  calc
    (rawSampleLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
        (fun z ↦ ((gramError F (toSample z)) ^ (2 * q)).trace) =
        (selectorArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun x ↦ ((sparseVectorError F x) ^ (2 * q)).trace) :=
      (selector_trace_moment_eq_raw hs (lt_trans Nat.zero_lt_one hb) F q).symm
    _ ≤ (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) :=
      unconditional_trace_moment_order (lt_trans Nat.zero_lt_one hb) F q
    _ = cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega ↦ ((iidGramError b F omega) ^ (2 * q)).trace) :=
      scaled_iid_trace_moment_eq_product hs hb F q

end

end SparseFock.MomentTransfer
