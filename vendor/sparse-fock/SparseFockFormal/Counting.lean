import SparseFockFormal.Pattern

namespace SparseFock

namespace Counting

/-- Occupation-count product used in Claim A (`Y₊`). -/
theorem claimA_count {ν outputLight inputLight : ℕ}
    (hout : outputLight ≤ ν + 2) (hin : inputLight ≤ ν) :
    outputLight * inputLight ≤ ν * (ν + 2) := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul hout hin

/-- Occupation-count product used in Claim B (`Y₀`), without division by two. -/
theorem claimB_count {ν outputLight inputHeavy : ℕ}
    (hout : outputLight ≤ ν) (hin : 2 * inputHeavy ≤ ν) :
    2 * (outputLight * inputHeavy) ≤ ν * ν := by
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul hout hin

/-- Occupation-count product used in Claim C (transpose light hop). -/
theorem claimC_count {ν outputLight inputLight : ℕ}
    (hout : outputLight ≤ ν) (hin : inputLight ≤ ν) :
    outputLight * inputLight ≤ ν * ν := by
  exact Nat.mul_le_mul hout hin

theorem pattern_claimA_input_count {m n ν : ℕ} (p : Pattern m n)
    (hgrade : p.grade = ν) : p.light.card ≤ ν := by
  simpa [hgrade] using p.card_light_le_grade

theorem pattern_claimB_input_count {m n ν : ℕ} (p : Pattern m n)
    (hgrade : p.grade = ν) : 2 * p.heavy.card ≤ ν := by
  simpa [hgrade] using p.two_mul_card_heavy_le_grade

/-- Claim A's two occupation factors, specialized to input/output patterns. -/
theorem pattern_claimA_count {m n ν : ℕ} (input output : Pattern m n)
    (hin : input.grade = ν) (hout : output.grade = ν + 2) :
    output.light.card * input.light.card ≤ ν * (ν + 2) := by
  apply claimA_count
  · simpa [hout] using output.card_light_le_grade
  · simpa [hin] using input.card_light_le_grade

/-- Claim B's two occupation factors, specialized to grade-`ν` patterns. -/
theorem pattern_claimB_count {m n ν : ℕ} (input output : Pattern m n)
    (hin : input.grade = ν) (hout : output.grade = ν) :
    2 * (output.light.card * input.heavy.card) ≤ ν * ν := by
  apply claimB_count
  · simpa [hout] using output.card_light_le_grade
  · simpa [hin] using input.two_mul_card_heavy_le_grade

/-- Claim C's two light-occupation factors, specialized to grade-`ν` patterns. -/
theorem pattern_claimC_count {m n ν : ℕ} (input output : Pattern m n)
    (hin : input.grade = ν) (hout : output.grade = ν) :
    output.light.card * input.light.card ≤ ν * ν := by
  apply claimC_count
  · simpa [hout] using output.card_light_le_grade
  · simpa [hin] using input.card_light_le_grade

end Counting

end SparseFock


