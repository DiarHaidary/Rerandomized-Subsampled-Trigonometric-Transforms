import SRHT.BernoulliMoment
import SRHT.ActualMomentTransfer

/-! The full scope of report Theorem 2: arbitrary real Bernoulli rate,
independent or limited-independent families, and the finite tail (9.2). -/
namespace SRHT.BernoulliGeneral
noncomputable section
open SparseFock SparseFock.FiniteLocalMoments SparseFock.MatrixTail
open TwoSignRepresentation
open scoped BigOperators Matrix.Norms.L2Operator
variable {k d : ℕ}
local instance rowDecidableEq : DecidableEq (G k) := Fintype.decidablePiFintype

/-- The literal mutually independent sign/sign/Bernoulli product law. -/
def law (k : ℕ) (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    FiniteLaw (SignAssignment k × (SignAssignment k × SignAssignment k)) :=
  (signLaw k).product ((signLaw k).product (BernoulliVariance.iidLaw p hp.le hp1.le))

/-- The real quantity m=p*2^k is the actual expected selector count. -/
theorem expected_rows (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (law k p hp hp1).expect (fun z => BernoulliVariance.count z.2.2) = p*(2^k:ℝ) := by
  have hm := BernoulliVariance.centered_count_mean (I:=G k) hp.le hp1.le
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_const] at hm
  have hc : (BernoulliVariance.iidLaw (I:=G k) p hp.le hp1.le).expect BernoulliVariance.count =
      (Fintype.card (G k):ℝ)*p := by linarith
  simp only [law,FiniteLaw.product_expect_eq_iterated,hc,FiniteLaw.expect_const]
  simp [mul_comm]

/-- The actual centered row Gram, with the product-law association convention. -/
def gramError (U : Matrix (G k) (Fin d) ℝ) (p : ℝ)
    (z : SignAssignment k × (SignAssignment k × SignAssignment k)) : Matrix (Fin d) (Fin d) ℝ :=
  BernoulliRepresentation.error U p ((z.1,z.2.1),z.2.2)

theorem gramError_eq_weightedGram (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (p : ℝ) (z) :
    gramError U p z = weightedGramError (transformedFrame U z.1 z.2.1)
      (fun j => BinaryBasis.bitValue (z.2.2 j)/p) := by
  exact (ActualMomentTransfer.bernoulli_error_weightedGram U hU p z.1 z.2.1 z.2.2).symm

theorem gramError_isHermitian (U : Matrix (G k) (Fin d) ℝ) (p : ℝ) (z) :
    (gramError U p z).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact BernoulliRepresentation.error_symmetric U p ((z.1,z.2.1),z.2.2)

/-- Theorem 2 in the occupation-basis law, for every real 0<p<1.
The expected number p*2^k of rows need not be an integer. -/
theorem moment_bound_basis (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ) (hq : 1≤q) :
    (BernoulliRepresentation.basis k p hp hp1).expect
      (fun z => Matrix.trace (BernoulliRepresentation.error U p z ^ (2*q))) ≤
      (d:ℝ)*momentEnvelope (effectiveDimension d q) (p*(2^k:ℝ)) ^ (2*q) := by
  let n : ℝ := Fintype.card (G k)
  let D : ℝ := effectiveDimension d q
  let L : ℝ := 9*D/n
  have hn : 0<n := by dsimp [n]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hL : 0≤L := by dsimp [L]; positivity
  have hsub : ∀ T : Finset (G k), T.card≤q → ‖∑ j∈T,SignCompression.effect U q j‖≤L := by
    intro T hT
    have hh := SmallRows.sign_cutoff_small_rows_norm_le U hU q hq T hT
    convert hh using 1
    dsimp [L,D,n,effectiveDimension]
    push_cast
    ring
  have hb := BernoulliMoment.moment_le_of_subset_bound U hU p hp hp1 q hL hsub
  have hmn : p*n<n := by nlinarith
  have he := bernoulli_envelope_le hD hn (mul_pos hp hn) hmn
  have hpn : p*n/n=p := mul_div_cancel_right₀ p (ne_of_gt hn)
  rw [hpn] at he
  have hnval : n=(2^k:ℝ) := by simp [n]
  calc
    _ ≤ _ := hb
    _ ≤ (d:ℝ)*momentEnvelope D (p*n)^(2*q) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply pow_le_pow_left₀ (by dsimp [L]; positivity)
      exact he
    _ = _ := by rw [hnval]

theorem law_expect (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (f : ((SignAssignment k × SignAssignment k) × SignAssignment k) → ℝ) :
    (law k p hp hp1).expect (fun z => f ((z.1,z.2.1),z.2.2)) =
      (BernoulliRepresentation.basis k p hp hp1).expect f := by
  rw [ActualMomentTransfer.bernoulli_basis_expect]
  simp only [law,FiniteLaw.product_expect_eq_iterated]

/-- Report Theorem 2 under the actual fully independent finite product law. -/
theorem moment_bound (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ) (hq : 1≤q) :
    (law k p hp hp1).expect (fun z => Matrix.trace (gramError U p z ^ (2*q))) ≤
      (d:ℝ)*momentEnvelope (effectiveDimension d q) (p*(2^k:ℝ)) ^ (2*q) := by
  unfold gramError
  rw [law_expect p hp hp1 (fun z => Matrix.trace (BernoulliRepresentation.error U p z ^ (2*q)))]
  exact moment_bound_basis U hU p hp hp1 q hq

/-- The full limited-independence inequality in Theorem 2. Only the stated
coordinate marginals are matched; mutual independence is the product law. -/
theorem moment_bound_limited (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ) (hq : 1≤q)
    {μx μy μz : FiniteLaw (SignAssignment k)}
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*q)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*q)))
    (hz : MatchesUpTo μz (BernoulliVariance.iidLaw p hp.le hp1.le) (min (2^k) (2*q))) :
    (μx.product (μy.product μz)).expect (fun z => Matrix.trace (gramError U p z ^ (2*q))) ≤
      (d:ℝ)*momentEnvelope (effectiveDimension d q) (p*(2^k:ℝ)) ^ (2*q) := by
  unfold gramError
  rw [ActualMomentTransfer.bernoulli_moment_match_min U hU p hp hp1 q hx hy hz]
  exact moment_bound_basis U hU p hp hp1 q hq

/-- The first inequality of (9.2), with the full Theorem 2 envelope substituted.
It holds for the limited-independent law as well as the fully independent one. -/
theorem tail_ratio_limited (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ) (hq : 1≤q)
    {μx μy μz : FiniteLaw (SignAssignment k)}
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*q)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*q)))
    (hz : MatchesUpTo μz (BernoulliVariance.iidLaw p hp.le hp1.le) (min (2^k) (2*q)))
    (a : ℝ) (ha : 0<a) :
    (μx.product (μy.product μz)).prob {z | a≤‖gramError U p z‖} ≤
      ((d:ℝ)*momentEnvelope (effectiveDimension d q) (p*(2^k:ℝ)) ^ (2*q))/a^(2*q) := by
  calc
    _ ≤ _ := matrix_markov_tail (μx.product (μy.product μz)) (gramError U p)
      (gramError_isHermitian U p) q hq a ha
    _ ≤ _ := div_le_div_of_nonneg_right
      (moment_bound_limited U hU p hp hp1 q hq hx hy hz) (by positivity)

/-- Equation (9.2), in the stronger form with a weak norm threshold.
Here m=p*2^k is real, and the three matching laws are mutually independent. -/
theorem tail_bound_limited (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ) (hq : 1≤q)
    {μx μy μz : FiniteLaw (SignAssignment k)}
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*q)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*q)))
    (hz : MatchesUpTo μz (BernoulliVariance.iidLaw p hp.le hp1.le) (min (2^k) (2*q)))
    (a : ℝ) (ha : 0<a) (ha1 : a<1)
    (hsize : 256*(effectiveDimension d q:ℝ)/a^2 ≤ p*(2^k:ℝ)) :
    (μx.product (μy.product μz)).prob {z | a≤‖gramError U p z‖} ≤
      (d:ℝ)*(1/2:ℝ)^(2*q) := by
  have hm : 0<p*(2^k:ℝ) := by positivity
  have hD : (0:ℝ)≤effectiveDimension d q := Nat.cast_nonneg _
  have hK := envelope_nonneg hD hm
  have hh := envelope_le_half hD hm ha ha1.le hsize
  calc
    _ ≤ _ := tail_ratio_limited U hU p hp hp1 q hq hx hy hz a ha
    _ = (d:ℝ)*(momentEnvelope (effectiveDimension d q) (p*(2^k:ℝ))/a)^(2*q) := by
      rw [div_pow]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply pow_le_pow_left₀ (div_nonneg hK ha.le)
      exact (div_le_iff₀ ha).mpr (by linarith)

/-- Equation (9.2) for the literal fully independent Bernoulli sketch. -/
theorem tail_bound (U : Matrix (G k) (Fin d) ℝ) (hU : U.transpose*U=1)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (q : ℕ) (hq : 1≤q)
    (a : ℝ) (ha : 0<a) (ha1 : a<1)
    (hsize : 256*(effectiveDimension d q:ℝ)/a^2 ≤ p*(2^k:ℝ)) :
    (law k p hp hp1).prob {z | a≤‖gramError U p z‖} ≤
      (d:ℝ)*(1/2:ℝ)^(2*q) :=
  tail_bound_limited U hU p hp hp1 q hq
    (matchesUpTo_refl _ _) (matchesUpTo_refl _ _) (matchesUpTo_refl _ _) a ha ha1 hsize

/-- The rate-one endpoint has identically zero centered error when every
selector is one; no limiting argument or variance division is needed. -/
theorem full_selectors_error_zero (U : Matrix (G k) (Fin d) ℝ)
    (x y : SignAssignment k) : gramError U 1 (x,y,fun _ => 1) = 0 := by
  simp [gramError,BernoulliRepresentation.error,BinaryBasis.bitValue]

end
end SRHT.BernoulliGeneral
