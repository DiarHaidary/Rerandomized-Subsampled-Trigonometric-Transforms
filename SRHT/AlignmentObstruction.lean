import SRHT.Alignment
import SRHT.SupportMiss

/-! The actual alternating-support SRHT failure event and necessary row count. -/
namespace SRHT.AlignmentObstruction
noncomputable section
open SparseFock Alignment SupportMiss
open scoped BigOperators

@[simp] theorem site_card (k : ℕ) : Fintype.card (Site k) = (2^k)^2 := by
  simp [Site, pow_two]

def law (k t : ℕ) {M : ℕ} (hM : M≤(2^k)^2) :
    FiniteLaw (Layers k t × Sampling.Exact (Site k) M) :=
  (layersLaw k t).product (missLaw (by simpa only [site_card] using hM))

/-- The failure event for the literal unit input and actual sampled vector. -/
def failureEvent (k t M : ℕ) (ε : ℝ) : Set (Layers k t × Sampling.Exact (Site k) M) :=
  {z | sampleEnergy (evolve k t z.1) z.2.val < 1-ε}

def failureProbability (k t : ℕ) {M : ℕ} (hM : M≤(2^k)^2) (ε : ℝ) : ℝ :=
  (law k t hM).prob (failureEvent k t M ε)

theorem product_prob_rectangle {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (A : Set α) (B : Set β) :
    (μ.product ν).prob {z | z.1∈A ∧ z.2∈B} = μ.prob A * ν.prob B := by
  classical
  rw [FiniteLaw.product_prob_eq_iterated]
  have hsec (a : α) : ν.prob {b | (a,b)∈{z : α×β | z.1∈A ∧ z.2∈B}} =
      ν.prob B * FiniteLaw.indicator A a := by
    by_cases ha : a∈A
    · simp [ha,FiniteLaw.indicator]
    · simp [ha,FiniteLaw.indicator,FiniteLaw.prob_empty]
  simp_rw [hsec]
  rw [FiniteLaw.expect_smul]
  change ν.prob B * μ.prob A = μ.prob A * ν.prob B
  ring

/-- Appendix A.2: fully independent sign layers can preserve an L-point
support, which the independent uniform row sample then misses. -/
theorem failure_lower (k t : ℕ) {M : ℕ} (hM : M≤(2^k)^2)
    (ε : ℝ) (hε : ε<1) :
    (1/2:ℝ)^(t*2^k) * missRatio ((2^k)^2) (2^k) M ≤
      failureProbability k t hM ε := by
  classical
  let K := support (alternating k t)
  let hMc : M≤Fintype.card (Site k) := by simpa only [site_card] using hM
  have hprob := product_prob_rectangle (layersLaw k t) (missLaw hMc)
    (aligned k t) {T | Disjoint T.val K}
  rw [aligned_probability,miss_probability] at hprob
  have hK : K.card=2^k := alternating_support_card k t
  rw [site_card,hK] at hprob
  calc
    _ = (law k t hM).prob {z | z.1∈aligned k t ∧ Disjoint z.2.val K} := hprob.symm
    _ ≤ _ := by
      apply FiniteLaw.prob_mono
      intro z hz
      change sampleEnergy (evolve k t z.1) z.2.val < 1-ε
      rw [evolve_of_aligned k t z.1 hz.1,
        sampleEnergy_eq_zero_of_disjoint _ _ hz.2]
      linarith

/-- Appendix A.4 as a theorem about the actual transform distribution.
The only performance premise is the claimed failure probability bound. -/
theorem necessary_rows (k t : ℕ) {M : ℕ} (hM : M≤(2^k)^2)
    (ε δ : ℝ) (hε : ε<1) (hδ : 0≤δ)
    (hfailure : failureProbability k t hM ε ≤ δ) :
    (((2^k)^2-2^k+1:ℕ):ℝ) * (1-(2:ℝ)^t * δ^(1/(2^k:ℝ))) ≤ M := by
  have hL0 : 0<2^k := by positivity
  have hL : 2^k≤(2^k)^2 := by
    have h := Nat.one_le_pow k 2 (by decide)
    nlinarith
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using SupportMiss.necessary_rows_of_failure_bound hL0 hL hδ
    (failure_lower k t hM ε hε) hfailure

/-- The actual two-round obstruction at δ=2^(-4L). -/
theorem two_round_three_quarters (k : ℕ) {M : ℕ} (hM : M≤(2^k)^2)
    (ε : ℝ) (hε : ε<1)
    (hfailure : failureProbability k 2 hM ε ≤ (1/2:ℝ)^(4*2^k)) :
    (3/4:ℝ) * ((2^k)^2-2^k+1:ℕ) ≤ M := by
  have hL0 : 0<2^k := by positivity
  have hL : 2^k≤(2^k)^2 := by
    have h := Nat.one_le_pow k 2 (by decide)
    nlinarith
  exact SupportMiss.two_round_three_quarters hL0 hL
    ((failure_lower k 2 hM ε hε).trans hfailure)

end
end SRHT.AlignmentObstruction
