import SRHT.BernoulliMoment
import SRHT.FixedSizeTail

/-! The complete fixed-size two-round SRHT theorem for literal Walsh matrices.
The three random families are independent by construction of their product law;
each sign family need only match the uniform law on min(n,4q) coordinates. -/
namespace SRHT
noncomputable section
open SparseFock SparseFock.FiniteLocalMoments FixedSizeTail
open scoped BigOperators Matrix.Norms.L2Operator
variable {k d : ℕ}

/-- The actual two-round Walsh sketch, with the explicit prescribed row count,
is an oblivious subspace embedding. There are no assumed moment estimates or
operator bounds: orthonormal columns and the stated limited independence suffice. -/
theorem two_round_srht_ose (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hd : 1≤d) (hdn : d≤2^k)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1/2)
    (μx μy : FiniteLaw (SignAssignment k))
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*failureOrder d δ))) :
    1-δ ≤ (μx.product (μy.product (uniformRowLaw (rowCount_le (2^k) d ε δ)))).prob
      {z | IsOSE U z.1 z.2.1 z.2.2.val ε} := by
  apply rowCount_success_of_bernoulli_bound U hU hd ε δ hε hε1.le hδ hδ1 μx μy hx hy
  intro hM0 hMn
  exact BernoulliMoment.moment_bound U hU (failureOrder d δ)
    (failureOrder_pos hd hδ hδ1) hM0 hMn

/-- The corresponding concrete operator-norm failure bound. The proper-sampling
branch in fact has mass at most δ/4, while sampling all rows has zero error. -/
theorem two_round_srht_norm_failure (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hd : 1≤d) (hdn : d≤2^k)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1/2)
    (μx μy : FiniteLaw (SignAssignment k))
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4*failureOrder d δ)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4*failureOrder d δ))) :
    (μx.product (μy.product (uniformRowLaw (rowCount_le (2^k) d ε δ)))).prob
      {z | ε≤‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} ≤δ := by
  apply rowCount_norm_failure_of_bernoulli_bound U hU hd ε δ hε hε1.le hδ hδ1 μx μy hx hy
  intro hM0 hMn
  exact BernoulliMoment.moment_bound U hU (failureOrder d δ)
    (failureOrder_pos hd hδ hδ1) hM0 hMn

/-- Fully independent signs are a special case of the theorem. -/
theorem two_round_srht_ose_independent (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (hd : 1≤d) (hdn : d≤2^k)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1/2) :
    1-δ ≤ (sketchLaw (rowCount_le (2^k) d ε δ)).prob
      {z | IsOSE U z.1 z.2.1 z.2.2.val ε} :=
  two_round_srht_ose U hU hd hdn ε δ hε hε1 hδ hδ1 (signLaw k) (signLaw k)
    (matchesUpTo_refl _ _) (matchesUpTo_refl _ _)

end
end SRHT
