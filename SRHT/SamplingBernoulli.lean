import SRHT.SamplingTransfer
import SRHT.BernoulliSupport
import Mathlib.Tactic

/-! Complete fixed-size/Bernoulli moment comparison for arbitrary real
symmetric effects, with no divisibility requirement on the row count. -/

namespace SRHT.Sampling
open SparseFock SparseFock.SparseIIDTransfer
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def rate (J : Type*) [Fintype J] (M : ℕ) : ℝ := (M : ℝ) / Fintype.card J

theorem rate_pos {M : ℕ} (hM : 0 < M) (hMn : M < Fintype.card J) : 0 < rate J M := by
  apply div_pos
  · exact_mod_cast hM
  · exact_mod_cast (show 0 < Fintype.card J by omega)

theorem rate_lt_one {M : ℕ} (hM : 0 < M) (hMn : M < Fintype.card J) : rate J M < 1 := by
  apply (div_lt_one (by exact_mod_cast (show 0 < Fintype.card J by omega))).2
  exact_mod_cast hMn

def rateLaw {M : ℕ} (hM : 0 < M) (hMn : M < Fintype.card J) : FiniteLaw (Finset J) :=
  BernoulliSupport.law (rate J M) (rate_pos hM hMn).le (rate_lt_one hM hMn).le

theorem rateLaw_exchangeable {M : ℕ} (hM : 0 < M) (hMn : M < Fintype.card J) :
    Exchangeable (rateLaw hM hMn) := by
  intro π B
  exact BernoulliSupport.law_exchangeable _ _ _ π B

theorem card_mul_rate {M : ℕ} (hM : 0 < M) (hMn : M < Fintype.card J) :
    (Fintype.card J : ℝ) * rate J M = M := by
  have hn : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card J ≠ 0 by omega)
  unfold rate
  field_simp

theorem rateLaw_mean {M : ℕ} (hM : 0 < M) (hMn : M < Fintype.card J) :
    (rateLaw hM hMn).expect (fun B => (B.card : ℝ) - M) = 0 := by
  have h := BernoulliSupport.mean_centered_support (I := J) (rate J M)
    (rate_pos hM hMn).le (rate_lt_one hM hMn).le
  rw [card_mul_rate hM hMn] at h
  exact h

theorem rateLaw_retention {M : ℕ} (hM : 0 < M) (hMn : M < Fintype.card J) :
    (1/4 : ℝ) ≤ retention (rateLaw hM hMn) M := by
  have ha : 0 ≤ excess (rateLaw hM hMn) M :=
    (rateLaw hM hMn).expect_nonneg (fun B => le_max_right _ _)
  have hb := BernoulliSupport.support_deviation_bound (I := J) (rate J M)
    (rate_pos hM hMn).le (rate_lt_one hM hMn).le
  rw [card_mul_rate hM hMn] at hb
  have hvar : (M : ℝ) * (1 - rate J M) =
      (M : ℝ) * ((Fintype.card J : ℝ) - M) / Fintype.card J := by
    have hn : (Fintype.card J : ℝ) ≠ 0 := by
      exact_mod_cast (show Fintype.card J ≠ 0 by omega)
    unfold rate
    field_simp
  rw [hvar] at hb
  have hh := BernoulliVariance.retention_lower hM hMn ha hb
  simpa only [retention, div_div_eq_mul_div] using hh

/-- Uniform sampling of M distinct rows has even trace moments at most
4^(2q) times independent Bernoulli sampling with rate M/n.  The matrices
may be noncommuting; symmetry is the only matrix hypothesis. -/
theorem bernoulli_trace_moment_transfer {M d : ℕ}
    (hM : 0 < M) (hMn : M < Fintype.card J) (q : ℕ)
    (A : J → SymmetricMatrix d) :
    fixedMoment M q A ≤ (4 : ℝ) ^ (2*q) * supportMoment (rateLaw hM hMn) M q A :=
  trace_moment_transfer (rateLaw hM hMn) (rateLaw_exchangeable hM hMn) hM hMn
    (rateLaw_mean hM hMn) (rateLaw_retention hM hMn) q A

end
end SRHT.Sampling
