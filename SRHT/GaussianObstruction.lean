import SRHT.ConfidenceObstruction
import SRHT.AlignmentObstruction

/-! Appendix A.3 for the actual distribution of independent sign layers and
uniform distinct row sampling.  A fixed number of Walsh/sign rounds cannot
satisfy a universal `C ε⁻² (1 + log (1/δ))` row bound at every confidence level. -/
namespace SRHT.GaussianObstruction
noncomputable section
open ConfidenceObstruction

/-- Along arbitrarily large dyadic sizes, every permissible row count within
the proposed logarithmic budget has actual lower-tail failure probability
strictly above the requested confidence. -/
theorem exists_dyadic_failure (C ε a : ℝ) (t k₀ : ℕ)
    (hε : 0<ε) (hε1 : ε<1) (ha : (t:ℝ)*Real.log 2<a) :
    ∃ k : ℕ, k₀≤k ∧ 1≤k ∧
      0<exponentialConfidence a (2^k) ∧
      exponentialConfidence a (2^k)<1/2 ∧
      ∀ (M : ℕ) (hM : M≤(2^k)^2),
        (M:ℝ)≤C/ε^2*(1+Real.log (1/exponentialConfidence a (2^k))) →
        exponentialConfidence a (2^k) <
          AlignmentObstruction.failureProbability k t hM ε := by
  obtain ⟨k,hk₀,hk,hδ,hδhalf,hbad⟩ :=
    exists_dyadic_support_failure C ε a t k₀ hε ha
  refine ⟨k,hk₀,hk,hδ,hδhalf,?_⟩
  intro M hM hbudget
  exact (hbad M hbudget).trans_le
    (AlignmentObstruction.failure_lower k t hM ε hε1)

/-- No universal constant works for all dimensions and confidence levels,
even for the single explicit unit-vector family in `Alignment`.  The statement
allows the proposed scheme to choose its row count separately at every input
dimension and confidence, and already enforces the ambient-dimension cap. -/
theorem no_universal_logarithmic_budget (t : ℕ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε<1) :
    ¬ ∃ C : ℝ, ∀ k : ℕ, 1≤k → ∀ δ : ℝ, 0<δ → δ<1/2 →
      ∃ (M : ℕ) (hM : M≤(2^k)^2),
        (M:ℝ)≤C/ε^2*(1+Real.log (1/δ)) ∧
        AlignmentObstruction.failureProbability k t hM ε ≤ δ := by
  intro ⟨C,hC⟩
  let a : ℝ := ((t:ℝ)+1)*Real.log 2
  have ha : (t:ℝ)*Real.log 2<a := by
    dsimp [a]
    have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
    nlinarith
  obtain ⟨k,_hk₀,hk,hδ,hδhalf,hbad⟩ :=
    exists_dyadic_failure C ε a t 1 hε hε1 ha
  obtain ⟨M,hM,hbudget,hfailure⟩ :=
    hC k hk (exponentialConfidence a (2^k)) hδ hδhalf
  exact (not_lt_of_ge hfailure) (hbad M hM hbudget)

end
end SRHT.GaussianObstruction
