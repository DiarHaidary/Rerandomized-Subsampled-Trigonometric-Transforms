import SRHT.MatrixNormTransport
import SRHT.BernoulliRepresentation
import SRHT.SignCompression
import SRHT.SelectorRepresentation
import SRHT.SmallRowsFinal
import SRHT.Parameters
import SRHT.SamplingBernoulli

namespace SRHT.BernoulliMoment
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix Cutoff ProjectionBounds TwoSignRepresentation BernoulliRepresentation

variable {k d : ℕ}
local instance rowDecidableEq : DecidableEq (G k) := Fintype.decidablePiFintype

theorem compressed_matrix_eq (U : Matrix (G k) (Fin d) ℝ)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ) :
    supportProjection (reachable k d q) *
        (BernoulliRepresentation.basis k p hp hp1).matrixMulOp (error U p) *
          supportProjection (reachable k d q) =
      (SelectorRepresentation.bernoulliMatrix (SignCompression.effect U q) q
        (Real.sqrt ((1-p)/p)) ((1-2*p)/p)).submatrix
          (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm := by
  classical
  have hA : ∀ j, (SignCompression.effect U q j).transpose = SignCompression.effect U q j := by
    intro j
    have hh := (SignCompression.effect_positive U q j).isHermitian
    change (SignCompression.effect U q j).conjTranspose = SignCompression.effect U q j at hh
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  rw [← SelectorRepresentation.compress_fullBernoulli _ hA]
  ext out inp
  rw [sandwich_apply,multiplication_eq]
  simp only [Matrix.submatrix_apply,Equiv.prodAssoc_symm_apply,
    SelectorRepresentation.selectorCutoff_compression_entry]
  by_cases ho : out.2.1.1.card ≤ 2*q ∧ out.2.1.2.card ≤ 2*q <;>
    by_cases hi : inp.2.1.1.card ≤ 2*q ∧ inp.2.1.2.card ≤ 2*q <;>
    by_cases hs : out.2.2.card ≤ q <;> by_cases ht : inp.2.2.card ≤ q
  all_goals simp [reachable,SelectorRepresentation.fullBernoulli,operator,selector,
    Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap,SignCompression.effect_entry,
    SignCompression.support,ho,hi,hs,ht]

set_option maxHeartbeats 200000 in
theorem moment_le_of_subset_bound (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ)
    {L : ℝ} (hL : 0≤L)
    (hsub : ∀ T : Finset (G k), T.card≤q → ‖∑ j∈T, SignCompression.effect U q j‖≤L) :
    (BernoulliRepresentation.basis k p hp hp1).expect
      (fun x => Matrix.trace (error U p x ^ (2*q))) ≤
      (d:ℝ)*(2*Real.sqrt ((1-p)/p)*Real.sqrt L+|(1-2*p)/p| *L)^(2*q) := by
  let K := 2*Real.sqrt ((1-p)/p)*Real.sqrt L+|(1-2*p)/p| *L
  have hK : 0≤K := by dsimp [K]; positivity
  suffices hh : (BernoulliRepresentation.basis k p hp hp1).expect
      (fun x => Matrix.trace (error U p x ^ (2*q))) ≤
      (Fintype.card (Fin d):ℝ)*K^(2*q) by
    simpa only [Fintype.card_fin] using hh
  refine VacuumMoment.moment_le_of_compressed_norm
    (BernoulliRepresentation.basis k p hp hp1) (error U p) (error_symmetric U p)
    (reachable k d) q ?_ ?_ ?_ hK ?_
  · intro a
    simp only [BernoulliRepresentation.basis_vacuum]
    exact vacuum_reachable a
  · intro r hr out inp hi h
    exact multiplication_reachable U p hp hp1 r out inp hi h
  · intro r hr
    exact reachable_mono hr
  · have he := congrArg (fun A : Matrix (Fin d × (SmallRows.SignPair (G k) × Finset (G k)))
          (Fin d × (SmallRows.SignPair (G k) × Finset (G k))) ℝ => ‖A‖)
        (compressed_matrix_eq U p hp hp1 q)
    rw [MatrixNorm.submatrix_equiv_norm] at he
    rw [MatrixNormTransport.square_addCommGroup_norm_instance_eq_ring_norm] at he
    have hh := SelectorRepresentation.norm_bernoulliMatrix_le_of_sum_norm
      (SignCompression.effect U q) (SignCompression.effect_positive U q)
      (SignCompression.effect_sum_norm U q hU) q hL hsub
      (Real.sqrt ((1-p)/p)) ((1-2*p)/p)
    exact he.trans_le (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using hh)

/-- Complete moment bound for the literal two-round Walsh Gram error, with
all occupation, positivity, reachability, and small-row estimates discharged. -/
theorem moment_bound (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (q : ℕ) (hq : 1≤q) {M : ℕ} (hM : 0<M) (hMn : M<2^k) :
    (BernoulliRepresentation.basis k (Sampling.rate (G k) M)
      (Sampling.rate_pos hM (by simpa using hMn))
      (Sampling.rate_lt_one hM (by simpa using hMn))).expect
        (fun x => Matrix.trace (error U (Sampling.rate (G k) M) x ^ (2*q))) ≤
      (d:ℝ)*momentEnvelope (effectiveDimension d q) M ^ (2*q) := by
  let n : ℝ := Fintype.card (G k)
  let D : ℝ := effectiveDimension d q
  let L : ℝ := 9*D/n
  have hn : 0<n := by dsimp [n]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hL : 0≤L := by dsimp [L]; positivity
  have hmR : (0:ℝ)<M := by exact_mod_cast hM
  have hmnR : (M:ℝ)<n := by
    dsimp [n]
    exact_mod_cast (show M<Fintype.card (G k) by simpa using hMn)
  have hsub : ∀ T : Finset (G k), T.card≤q → ‖∑ j∈T,SignCompression.effect U q j‖≤L := by
    intro T hT
    have hh := SmallRows.sign_cutoff_small_rows_norm_le U hU q hq T hT
    convert hh using 1
    dsimp [L,D,n,effectiveDimension]
    push_cast
    ring
  have hb := moment_le_of_subset_bound U hU (Sampling.rate (G k) M)
    (Sampling.rate_pos hM (by simpa using hMn))
    (Sampling.rate_lt_one hM (by simpa using hMn)) q hL hsub
  have he := bernoulli_envelope_le hD hn hmR hmnR
  calc
    _ ≤ _ := hb
    _ ≤ (d:ℝ)*momentEnvelope D M^(2*q) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply pow_le_pow_left₀ (by dsimp [L]; positivity)
      exact he

end
end SRHT.BernoulliMoment

