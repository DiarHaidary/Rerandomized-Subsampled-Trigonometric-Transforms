import SRHT.SamplingBernoulli
import SRHT.BernoulliRepresentation
import SRHT.LimitedIndependence

/-! Distributional bridges for the literal two-round sampled Gram matrix. -/
namespace SRHT.ActualMomentTransfer
noncomputable section
open SparseFock SparseFock.SparseIIDTransfer SparseFock.TracePowerConvexity
open SparseFock.FiniteLocalMoments TwoSignRepresentation
open scoped BigOperators Matrix.Norms.L2Operator
variable {k d M : ℕ}

def symmetricEffect (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) (j : G k) : SymmetricMatrix d :=
  ⟨rowEffect U j (x,y), by
    change (rowEffect U j (x,y)).transpose = rowEffect U j (x,y)
    ext a b
    exact mul_comm _ _⟩

theorem rowEffect_sum_one (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (x y : SignAssignment k) :
    (∑ j, rowEffect U j (x,y)) = 1 := by
  convert transformedFrame_transpose_mul U hU x y using 1
  ext a b
  simp [Matrix.sum_apply,rowEffect,Matrix.mul_apply,Matrix.transpose_apply]

theorem centeredSum_coe (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) (α : ℝ) (T : Finset (G k)) :
    ((Sampling.centeredSum α (symmetricEffect U x y) T : SymmetricMatrix d) : Matrix (Fin d) (Fin d) ℝ) =
      ∑ j, (α*Sampling.site T j-1) • rowEffect U j (x,y) := by
  simp [Sampling.centeredSum,symmetricEffect]

theorem centeredSum_sampledGram (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (x y : SignAssignment k) (T : RowSet k M) :
    ((Sampling.centeredSum ((Fintype.card (G k):ℝ)/M)
      (symmetricEffect U x y) T.val : SymmetricMatrix d) : Matrix (Fin d) (Fin d) ℝ) =
      sampledGram U x y T.val - 1 := by
  rw [Sampling.centeredSum_eq]
  simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, Submodule.coe_sum,
    symmetricEffect]
  rw [rowEffect_sum_one U hU]
  congr 1
  ext a b
  simp [sampledGram,Matrix.smul_apply,Matrix.sum_apply,rowEffect,T.property]

theorem fixedMoment_eq (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (x y : SignAssignment k) (hM : M≤2^k) (q : ℕ) :
    Sampling.fixedMoment M q (symmetricEffect U x y) =
      (uniformRowLaw hM).expect (fun T => Matrix.trace ((sampledGram U x y T.val-1)^(2*q))) := by
  unfold Sampling.fixedMoment FiniteLaw.expect
  change (∑ T : RowSet k M, (1/(Fintype.card (RowSet k M):ℝ)) *
    traceEvenPower q (Sampling.centeredSum ((Fintype.card (G k):ℝ)/M)
      (symmetricEffect U x y) T.val)) = _
  apply Finset.sum_congr rfl
  intro T _
  rw [uniformRowLaw_weight]
  simp only [one_div,traceEvenPower,centeredSum_sampledGram U hU x y]

theorem site_support (z : G k → ZMod 2) (j : G k) :
    Sampling.site (BernoulliSupport.support z) j = BinaryBasis.bitValue (z j) := by
  simp [Sampling.site,BernoulliSupport.support,BinaryBasis.bitValue]

theorem supportMoment_eq (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) (hM0 : 0<M) (hMn : M<Fintype.card (G k)) (q : ℕ) :
    Sampling.supportMoment (Sampling.rateLaw hM0 hMn) M q (symmetricEffect U x y) =
      (BernoulliVariance.iidLaw (Sampling.rate (G k) M)
        (Sampling.rate_pos hM0 hMn).le (Sampling.rate_lt_one hM0 hMn).le).expect
        (fun z => Matrix.trace (BernoulliRepresentation.error U (Sampling.rate (G k) M) ((x,y),z) ^ (2*q))) := by
  unfold Sampling.supportMoment Sampling.rateLaw
  rw [BernoulliSupport.expect_law]
  apply FiniteLaw.expect_congr
  intro z
  unfold traceEvenPower
  congr 2
  rw [centeredSum_coe]
  unfold BernoulliRepresentation.error
  apply Finset.sum_congr rfl
  intro j _
  rw [site_support]
  congr 1
  simp only [Sampling.rate,div_div_eq_mul_div]
  ring

theorem bernoulli_basis_expect (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (f : ((SignAssignment k × SignAssignment k) × SignAssignment k) → ℝ) :
    (BernoulliRepresentation.basis k p hp hp1).expect f =
      (signLaw k).expect (fun x => (signLaw k).expect (fun y =>
        (BernoulliVariance.iidLaw p hp.le hp1.le).expect (fun z => f ((x,y),z)))) := by
  have hB : ProductBasis.lawOfBasis (BernoulliRepresentation.basis k p hp hp1) =
      ((signLaw k).product (signLaw k)).product (BernoulliVariance.iidLaw p hp.le hp1.le) := by
    apply OccupationBasis.law_ext
    funext x
    have hs := congrArg (fun μ => μ.weight x.1) (TwoSignRepresentation.basis_law (k:=k))
    have hz := congrArg (fun μ => μ.weight x.2) (OccupationBasis.bernoulli_law (G:=G k) p hp hp1)
    change _ * _ = _ * _
    exact congrArg₂ (· * ·) hs hz
  change (ProductBasis.lawOfBasis (BernoulliRepresentation.basis k p hp hp1)).expect f = _
  rw [hB]
  simp_rw [FiniteLaw.product_expect_eq_iterated]

/-- Literal uniform distinct-row sampling is bounded by the independent
Bernoulli moment of the exact Gram multiplication operator. -/
theorem fixed_to_bernoulli (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hM0 : 0<M) (hMn : M<2^k) (q : ℕ) :
    (sketchLaw hMn.le).expect (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) ≤
      (4:ℝ)^(2*q) *
        (BernoulliRepresentation.basis k (Sampling.rate (G k) M)
          (Sampling.rate_pos hM0 (by simpa using hMn))
          (Sampling.rate_lt_one hM0 (by simpa using hMn))).expect
          (fun z => Matrix.trace (BernoulliRepresentation.error U (Sampling.rate (G k) M) z ^ (2*q))) := by
  rw [bernoulli_basis_expect]
  unfold sketchLaw
  simp_rw [FiniteLaw.product_expect_eq_iterated]
  rw [← FiniteLaw.expect_smul]
  apply FiniteLaw.expect_mono
  intro x
  rw [← FiniteLaw.expect_smul]
  apply FiniteLaw.expect_mono
  intro y
  rw [← fixedMoment_eq U hU x y hMn.le]
  have h := Sampling.bernoulli_trace_moment_transfer hM0 (show M<Fintype.card (G k) by simpa using hMn)
    q (symmetricEffect U x y)
  rw [supportMoment_eq] at h
  exact h

theorem polynomial_eq_frame (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) :
    twoRoundPolynomial (walshMatrix k) bitSign U x y = transformedFrame U x y := rfl

theorem weightedError_frame (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) (c : G k → ℝ) :
    weightedGramError (transformedFrame U x y) c =
      (∑ j, c j • rowEffect U j (x,y)) - 1 := by
  unfold weightedGramError
  congr 1
  ext a b
  simp only [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.transpose_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,rowEffect]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weightedError_sampledGram (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) (T : Finset (G k)) :
    weightedGramError (twoRoundPolynomial (walshMatrix k) bitSign U x y)
      (fun j => ((Fintype.card (G k):ℝ)/T.card)*Sampling.site T j) =
      sampledGram U x y T - 1 := by
  rw [polynomial_eq_frame,weightedError_frame]
  congr 1
  ext a b
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,rowEffect]
  change (∑ j, (((Fintype.card (G k):ℝ)/T.card)*Sampling.site T j)*
    (transformedFrame U x y j a*transformedFrame U x y j b)) = _
  simp [Sampling.site,sampledGram,Finset.mul_sum,ite_mul,mul_assoc]

theorem sampled_trace_local_x (U : Matrix (G k) (Fin d) ℝ)
    (y : SignAssignment k) (T : Finset (G k)) (q : ℕ) :
    HasLocalDegree (4*q) (fun x => Matrix.trace ((sampledGram U x y T-1)^(2*q))) := by
  simpa only [weightedError_sampledGram] using traceGram_degree_x (walshMatrix k) bitSign U y
    (fun j => ((Fintype.card (G k):ℝ)/T.card)*Sampling.site T j) q

theorem sampled_trace_local_y (U : Matrix (G k) (Fin d) ℝ)
    (x : SignAssignment k) (T : Finset (G k)) (q : ℕ) :
    HasLocalDegree (4*q) (fun y => Matrix.trace ((sampledGram U x y T-1)^(2*q))) := by
  simpa only [weightedError_sampledGram] using traceGram_degree_y (walshMatrix k) bitSign U x
    (fun j => ((Fintype.card (G k):ℝ)/T.card)*Sampling.site T j) q

/-- Exact 4q-coordinate moment matching for each independent sign family,
with the actual uniform sample of distinct rows retained. -/
theorem fixed_sign_moment_match (U : Matrix (G k) (Fin d) ℝ)
    (hM : M≤2^k) (q : ℕ) {μx μy : FiniteLaw (SignAssignment k)}
    (hx : MatchesUpTo μx (signLaw k) (4*q))
    (hy : MatchesUpTo μy (signLaw k) (4*q)) :
    (μx.product (μy.product (uniformRowLaw hM))).expect
      (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) =
    (sketchLaw hM).expect
      (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) := by
  unfold sketchLaw
  simp_rw [FiniteLaw.product_expect_eq_iterated]
  calc
    _ = μx.expect (fun x => (signLaw k).expect (fun y =>
      (uniformRowLaw hM).expect (fun T => Matrix.trace ((sampledGram U x y T.val-1)^(2*q))))) := by
      apply μx.expect_congr
      intro x
      exact (localDegree_expect (uniformRowLaw hM) _
        (fun T => sampled_trace_local_y U x T.val q)).expect_eq_of_matchesUpTo hy
    _ = _ := (localDegree_expect (signLaw k) _ (fun y =>
      localDegree_expect (uniformRowLaw hM) _
        (fun T => sampled_trace_local_x U y T.val q))).expect_eq_of_matchesUpTo hx

theorem fixed_sign_moment_match_min (U : Matrix (G k) (Fin d) ℝ)
    (hM : M≤2^k) (q : ℕ) {μx μy : FiniteLaw (SignAssignment k)}
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*q)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*q))) :
    (μx.product (μy.product (uniformRowLaw hM))).expect
      (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) =
    (sketchLaw hM).expect
      (fun z => Matrix.trace ((sampledGram U z.1 z.2.1 z.2.2.val-1)^(2*q))) :=
  fixed_sign_moment_match U hM q
    (matchesUpTo_of_min_card (by simpa using hx)) (matchesUpTo_of_min_card (by simpa using hy))

theorem bernoulli_error_weightedGram (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (p : ℝ) (x y z : SignAssignment k) :
    weightedGramError (twoRoundPolynomial (walshMatrix k) bitSign U x y)
      (fun j => BinaryBasis.bitValue (z j)/p) =
      BernoulliRepresentation.error U p ((x,y),z) := by
  rw [polynomial_eq_frame,weightedError_frame]
  unfold BernoulliRepresentation.error
  simp only [sub_smul,one_smul,Finset.sum_sub_distrib,rowEffect_sum_one U hU]

/-- Full literal three-family moment matching. In particular, independent
Bernoulli selectors may themselves be replaced by 2q-wise matching selectors. -/
theorem bernoulli_moment_match_min (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ)
    {μx μy μz : FiniteLaw (SignAssignment k)}
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*q)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*q)))
    (hz : MatchesUpTo μz (BernoulliVariance.iidLaw p hp.le hp1.le) (min (2^k) (2*q))) :
    (μx.product (μy.product μz)).expect
      (fun z => Matrix.trace (BernoulliRepresentation.error U p ((z.1,z.2.1),z.2.2)^(2*q))) =
    (BernoulliRepresentation.basis k p hp hp1).expect
      (fun z => Matrix.trace (BernoulliRepresentation.error U p z ^(2*q))) := by
  have hh := twoRound_trace_moment_match (walshMatrix k) bitSign
    (fun z => BinaryBasis.bitValue z/p) U q
    (matchesUpTo_of_min_card (by simpa using hx))
    (matchesUpTo_of_min_card (by simpa using hy))
    (matchesUpTo_of_min_card (by simpa using hz))
  simp only [bernoulli_error_weightedGram U hU] at hh
  rw [bernoulli_basis_expect]
  simpa only [FiniteLaw.product_expect_eq_iterated] using hh

end
end SRHT.ActualMomentTransfer
