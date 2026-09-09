import SRHT.Main
import SRHT.LogConfidence

/-! The embedding theorem and the report's joint dimension/confidence row order
in one public statement. -/
namespace SRHT
noncomputable section
open SparseFock SparseFock.FiniteLocalMoments FixedSizeTail

theorem two_round_srht_ose_log_confidence {k d : ℕ}
    (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (hU : U.transpose * U = 1) (hd : 1 ≤ d) (hdn : d ≤ 2^k)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1/2)
    (μx μy : FiniteLaw (SignAssignment k))
    (hx : MatchesUpTo μx (signLaw k) (min (2^k) (4 * failureOrder d δ)))
    (hy : MatchesUpTo μy (signLaw k) (min (2^k) (4 * failureOrder d δ))) :
    (rowCount (2^k) d ε δ : ℝ) ≤
        min (2^k : ℝ) (110592001 * ((d:ℝ) + Real.log (1/δ)^3) / ε^2) ∧
    1 - δ ≤ (μx.product (μy.product (uniformRowLaw (rowCount_le (2^k) d ε δ)))).prob
      {z | IsOSE U z.1 z.2.1 z.2.2.val ε} := by
  exact ⟨by simpa using rowCount_log_confidence_capped (n:=2^k) hd hε hε1 hδ hδ1,
    two_round_srht_ose U hU hd hdn ε δ hε hε1 hδ hδ1 μx μy hx hy⟩

end
end SRHT
