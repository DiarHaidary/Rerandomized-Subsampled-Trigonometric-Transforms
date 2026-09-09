import SRHT.ActualMomentTransfer
import SRHT.Parameters

/-! The exact finite-law matrix tail and vector OSE endpoints. -/
namespace SRHT.FixedSizeTail
noncomputable section
open SparseFock SparseFock.FiniteLocalMoments SparseFock.MatrixTail
open ActualMomentTransfer TwoSignRepresentation
open scoped BigOperators Matrix.Norms.L2Operator
variable {k d M : ℕ}

def IsOSE (U : Matrix (G k) (Fin d) ℝ) (x y : SignAssignment k)
    (T : Finset (G k)) (ε : ℝ) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin d),
    (1-ε)*‖v‖^2 ≤ ‖applyRectMatrix (sampledFrame U x y T) v‖^2 ∧
    ‖applyRectMatrix (sampledFrame U x y T) v‖^2 ≤ (1+ε)*‖v‖^2

theorem sampledGram_isHermitian (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) (T : Finset (G k)) : (sampledGram U x y T).IsHermitian := by
  rw [← sampledFrame_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self (sampledFrame U x y T)).isHermitian

theorem gram_norm_iff_ose (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) (T : Finset (G k)) (ε : ℝ) (hε : 0≤ε) :
    ‖sampledGram U x y T-1‖≤ε ↔ IsOSE U x y T ε := by
  rw [gramError_norm_le_iff_isGramOSE _ (sampledGram_isHermitian U x y T) ε hε]
  unfold IsGramOSE IsOSE
  simp only [← sampledFrame_gram,quadraticForm_transpose_mul_self]

theorem matrix_tail (U : Matrix (G k) (Fin d) ℝ) (hM : M≤2^k)
    (μx μy : FiniteLaw (SignAssignment k)) (q : ℕ) (hq : 0<q)
    (ε : ℝ) (hε : 0<ε) :
    (μx.product (μy.product (uniformRowLaw hM))).prob
      {z | ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} ≤
    (μx.product (μy.product (uniformRowLaw hM))).expect
      (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) / ε^(2*q) := by
  let A := fun z : SignAssignment k × (SignAssignment k × RowSet k M) =>
    sampledGram U z.1 z.2.1 z.2.2.val-1
  have hA : ∀ z, (A z).IsHermitian := fun z =>
    (sampledGram_isHermitian U z.1 z.2.1 z.2.2.val).sub Matrix.isHermitian_one
  exact matrix_markov_tail (μx.product (μy.product (uniformRowLaw hM))) A hA q hq ε hε

theorem failure_le_tail (U : Matrix (G k) (Fin d) ℝ) (hM : M≤2^k)
    (μx μy : FiniteLaw (SignAssignment k)) (ε : ℝ) (hε : 0≤ε) :
    (μx.product (μy.product (uniformRowLaw hM))).prob
      {z | ¬ IsOSE U z.1 z.2.1 z.2.2.val ε} ≤
    (μx.product (μy.product (uniformRowLaw hM))).prob
      {z | ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} := by
  apply FiniteLaw.prob_mono
  intro z hz
  by_contra hn
  exact hz ((gram_norm_iff_ose U z.1 z.2.1 z.2.2.val ε hε).mp (not_le.mp hn).le)

/-- A supplied literal Bernoulli moment estimate transfers to the concrete
fixed-size distribution, including separately limited independent signs. -/
theorem moment_of_bernoulli_bound (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hM0 : 0<M) (hMn : M<2^k) (q : ℕ)
    (μx μy : FiniteLaw (SignAssignment k))
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*q)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*q)))
    (K : ℝ)
    (hBern : (BernoulliRepresentation.basis k (Sampling.rate (G k) M)
      (Sampling.rate_pos hM0 (by simpa using hMn))
      (Sampling.rate_lt_one hM0 (by simpa using hMn))).expect
      (fun z => Matrix.trace (BernoulliRepresentation.error U (Sampling.rate (G k) M) z ^ (2*q))) ≤
        (d:ℝ)*K^(2*q)) :
    (μx.product (μy.product (uniformRowLaw hMn.le))).expect
      (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) ≤
      (d:ℝ)*(4*K)^(2*q) := by
  rw [fixed_sign_moment_match_min U hMn.le q hx hy]
  calc
    _ ≤ (4:ℝ)^(2*q) * _ := fixed_to_bernoulli U hU hM0 hMn q
    _ ≤ (4:ℝ)^(2*q) * ((d:ℝ)*K^(2*q)) :=
      mul_le_mul_of_nonneg_left hBern (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem tail_of_moment_bound (U : Matrix (G k) (Fin d) ℝ) (hM : M≤2^k)
    (μx μy : FiniteLaw (SignAssignment k)) (q : ℕ) (hq : 0<q)
    (ε K : ℝ) (hε : 0<ε) (hK : 0≤K) (hhalf : K≤ε/2)
    (hmoment : (μx.product (μy.product (uniformRowLaw hM))).expect
      (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) ≤
      (d:ℝ)*K^(2*q)) :
    (μx.product (μy.product (uniformRowLaw hM))).prob
      {z | ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} ≤ (d:ℝ)*(1/2:ℝ)^(2*q) := by
  calc
    _ ≤ _ := matrix_tail U hM μx μy q hq ε hε
    _ ≤ ((d:ℝ)*K^(2*q))/ε^(2*q) :=
      div_le_div_of_nonneg_right hmoment (by positivity)
    _ = (d:ℝ)*(K/ε)^(2*q) := by rw [div_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply pow_le_pow_left₀ (div_nonneg hK hε.le)
      exact (div_le_iff₀ hε).mpr (by linarith)

theorem success_of_tail (U : Matrix (G k) (Fin d) ℝ) (hM : M≤2^k)
    (μx μy : FiniteLaw (SignAssignment k)) (ε δ : ℝ) (hε : 0≤ε)
    (htail : (μx.product (μy.product (uniformRowLaw hM))).prob
      {z | ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} ≤δ) :
    1-δ ≤ (μx.product (μy.product (uniformRowLaw hM))).prob
      {z | IsOSE U z.1 z.2.1 z.2.2.val ε} := by
  have hh := (failure_le_tail U hM μx μy ε hε).trans htail
  have hc := FiniteLaw.prob_compl (μx.product (μy.product (uniformRowLaw hM)))
    {z | IsOSE U z.1 z.2.1 z.2.2.val ε}
  have hh' : 1-(μx.product (μy.product (uniformRowLaw hM))).prob
      {z | IsOSE U z.1 z.2.1 z.2.2.val ε} ≤δ := by
    rw [← hc]
    exact hh
  linarith

/-- The explicit 8192-row constant yields the claimed failure level from
the literal Bernoulli envelope. This is the statistical assembly step. -/
theorem failure_of_bernoulli_bound (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hd : 1≤d) (hM0 : 0<M) (hMn : M<2^k)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ<1/2)
    (μx μy : FiniteLaw (SignAssignment k))
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hsize : 8192*(effectiveDimension d (failureOrder d δ):ℝ)/ε^2 ≤ M)
    (hBern : (BernoulliRepresentation.basis k (Sampling.rate (G k) M)
      (Sampling.rate_pos hM0 (by simpa using hMn))
      (Sampling.rate_lt_one hM0 (by simpa using hMn))).expect
      (fun z => Matrix.trace (BernoulliRepresentation.error U (Sampling.rate (G k) M) z ^ (2*failureOrder d δ))) ≤
        (d:ℝ)*(momentEnvelope (effectiveDimension d (failureOrder d δ)) M)^(2*failureOrder d δ)) :
    (μx.product (μy.product (uniformRowLaw hMn.le))).prob
      {z | ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} ≤ δ/4 := by
  have hMreal : (0:ℝ)<M := by exact_mod_cast hM0
  have hD : (0:ℝ)≤effectiveDimension d (failureOrder d δ) := Nat.cast_nonneg _
  have hK := envelope_nonneg hD hMreal
  have hh := amplified_envelope_le_half hD hMreal hε hε1 hsize
  exact (tail_of_moment_bound U hMn.le μx μy (failureOrder d δ)
    (failureOrder_pos hd hδ hδ1) ε
    (4*momentEnvelope (effectiveDimension d (failureOrder d δ)) M) hε (by positivity) hh
    (moment_of_bernoulli_bound U hU hM0 hMn (failureOrder d δ) μx μy hx hy _ hBern)).trans
      (failure_mass_le hd hδ)

theorem full_rows_ose (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (x y : SignAssignment k) (T : RowSet k (2^k)) (ε : ℝ) (hε : 0≤ε) :
    IsOSE U x y T.val ε := by
  apply (gram_norm_iff_ose U x y T.val ε hε).mp
  rw [sampledGram_full U hU]
  simpa using hε

theorem full_rows_success (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (μx μy : FiniteLaw (SignAssignment k)) (ε : ℝ) (hε : 0≤ε) :
    (μx.product (μy.product (uniformRowLaw (le_refl (2^k))))).prob
      {z | IsOSE U z.1 z.2.1 z.2.2.val ε} = 1 := by
  have he : {z : SignAssignment k × (SignAssignment k × RowSet k (2^k)) |
      IsOSE U z.1 z.2.1 z.2.2.val ε} = Set.univ := by
    ext z
    simp [full_rows_ose U hU z.1 z.2.1 z.2.2 ε hε]
  rw [he,FiniteLaw.prob_univ]

/-- Norm-tail assembly for the prescribed row count, with the exact full-row
branch included before any division by the Bernoulli sampling variance. -/
theorem rowCount_norm_failure_of_bernoulli_bound (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hd : 1≤d)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ<1/2)
    (μx μy : FiniteLaw (SignAssignment k))
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hBern : ∀ (hM0 : 0<rowCount (2^k) d ε δ) (hMn : rowCount (2^k) d ε δ<2^k),
      (BernoulliRepresentation.basis k (Sampling.rate (G k) (rowCount (2^k) d ε δ))
        (Sampling.rate_pos hM0 (by simpa using hMn))
        (Sampling.rate_lt_one hM0 (by simpa using hMn))).expect
        (fun z => Matrix.trace (BernoulliRepresentation.error U
          (Sampling.rate (G k) (rowCount (2^k) d ε δ)) z ^ (2*failureOrder d δ))) ≤
          (d:ℝ)*(momentEnvelope (effectiveDimension d (failureOrder d δ))
            (rowCount (2^k) d ε δ))^(2*failureOrder d δ)) :
    (μx.product (μy.product (uniformRowLaw (rowCount_le (2^k) d ε δ)))).prob
      {z | ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} ≤δ := by
  by_cases hfull : rowCount (2^k) d ε δ=2^k
  · have he : {z : SignAssignment k × (SignAssignment k × RowSet k (rowCount (2^k) d ε δ)) |
        ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      have hT : z.2.2.val=Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa using z.2.2.property.trans hfull
      rw [hT,sampledGram_univ U hU]
      simpa using (not_le.mpr hε)
    rw [he,FiniteLaw.prob_empty]
    exact hδ.le
  · have hMn : rowCount (2^k) d ε δ<2^k :=
      lt_of_le_of_ne (rowCount_le _ _ _ _) hfull
    have hM0 := rowCount_pos (n:=2^k) (δ:=δ) (by positivity) hd hε
    exact (failure_of_bernoulli_bound U hU hd hM0 hMn ε δ hε hε1 hδ hδ1 μx μy
      hx hy (rowCount_lower_of_lt hMn) (hBern hM0 hMn)).trans (by linarith)

/-- Assembly for the prescribed row count. The Bernoulli estimate is supplied
only in the proper-sampling branch; full sampling is an exact isometry. -/
theorem rowCount_success_of_bernoulli_bound (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hd : 1≤d)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδ1 : δ<1/2)
    (μx μy : FiniteLaw (SignAssignment k))
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hBern : ∀ (hM0 : 0<rowCount (2^k) d ε δ) (hMn : rowCount (2^k) d ε δ<2^k),
      (BernoulliRepresentation.basis k (Sampling.rate (G k) (rowCount (2^k) d ε δ))
        (Sampling.rate_pos hM0 (by simpa using hMn))
        (Sampling.rate_lt_one hM0 (by simpa using hMn))).expect
        (fun z => Matrix.trace (BernoulliRepresentation.error U
          (Sampling.rate (G k) (rowCount (2^k) d ε δ)) z ^ (2*failureOrder d δ))) ≤
          (d:ℝ)*(momentEnvelope (effectiveDimension d (failureOrder d δ))
            (rowCount (2^k) d ε δ))^(2*failureOrder d δ)) :
    1-δ ≤ (μx.product (μy.product (uniformRowLaw (rowCount_le (2^k) d ε δ)))).prob
      {z | IsOSE U z.1 z.2.1 z.2.2.val ε} := by
  exact success_of_tail U (rowCount_le (2^k) d ε δ) μx μy ε δ hε.le
    (rowCount_norm_failure_of_bernoulli_bound U hU hd ε δ hε hε1 hδ hδ1 μx μy hx hy hBern)

end
end SRHT.FixedSizeTail
