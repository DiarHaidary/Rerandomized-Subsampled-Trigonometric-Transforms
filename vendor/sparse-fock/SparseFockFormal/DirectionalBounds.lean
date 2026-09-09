import SparseFockFormal.Pattern
import Mathlib.Tactic

namespace SparseFock

namespace DirectionalBounds

open scoped BigOperators

/-- The occupation profile retained by the directional norm arguments.  This
is a count-level abstraction; it does not assert that a site move is valid. -/
structure Profile where
  light : ℕ
  heavy : ℕ
  deriving DecidableEq, Repr

namespace Profile

def grade (p : Profile) : ℕ := p.light + 2 * p.heavy

/-- Count transformation for `Y₊`: one light is promoted and one fresh site is
created, so the light count is unchanged and the heavy count increases by one. -/
def yPlus (p : Profile) : Profile :=
  { light := p.light, heavy := p.heavy + 1 }

/-- Count transformation for `Y₀`: one heavy is demoted and one fresh light is
created, producing two additional light particles and one fewer heavy particle.
The theorem using this definition explicitly assumes `1 ≤ p.heavy`. -/
def yZero (p : Profile) : Profile :=
  { light := p.light + 2, heavy := p.heavy - 1 }

/-- A transpose light hop only moves a light particle. -/
def lightHop (p : Profile) : Profile := p

@[simp] theorem yPlus_light (p : Profile) : p.yPlus.light = p.light := rfl

@[simp] theorem yPlus_heavy (p : Profile) : p.yPlus.heavy = p.heavy + 1 := rfl

@[simp] theorem yPlus_grade (p : Profile) : p.yPlus.grade = p.grade + 2 := by
  simp [yPlus, grade]
  omega

@[simp] theorem yZero_light (p : Profile) : p.yZero.light = p.light + 2 := rfl

@[simp] theorem yZero_heavy (p : Profile) : p.yZero.heavy = p.heavy - 1 := rfl

theorem yZero_grade (p : Profile) (hheavy : 1 ≤ p.heavy) :
    p.yZero.grade = p.grade := by
  simp [yZero, grade]
  omega

@[simp] theorem lightHop_grade (p : Profile) : p.lightHop.grade = p.grade := rfl

@[simp] theorem lightHop_light (p : Profile) : p.lightHop.light = p.light := rfl

theorem light_le_grade (p : Profile) : p.light ≤ p.grade := by
  simp [grade]

theorem two_mul_heavy_le_grade (p : Profile) : 2 * p.heavy ≤ p.grade := by
  simp [grade]

end Profile

/-- Extract the count profile of a concrete finite sparse-Fock pattern. -/
def profile {m n : ℕ} (p : Pattern m n) : Profile :=
  { light := p.light.card, heavy := p.heavy.card }

@[simp] theorem profile_light {m n : ℕ} (p : Pattern m n) :
    (profile p).light = p.light.card := rfl

@[simp] theorem profile_heavy {m n : ℕ} (p : Pattern m n) :
    (profile p).heavy = p.heavy.card := rfl

theorem profile_grade {m n : ℕ} (p : Pattern m n) :
    (profile p).grade = p.grade := by
  simp [profile, Profile.grade, Pattern.grade_eq_card_light_add_two_mul_card_heavy]

/-- The total number of row-local light indices is bounded by the grade. -/
theorem sum_card_lightInRow_le_grade {m n : ℕ} (p : Pattern m n) :
    (∑ r, (p.lightInRow r).card) ≤ p.grade := by
  rw [← Pattern.card_light_eq_sum_card_lightInRow]
  exact p.card_light_le_grade

/-- Twice the total number of row-local heavy indices is bounded by the grade. -/
theorem two_mul_sum_card_heavyInRow_le_grade {m n : ℕ} (p : Pattern m n) :
    2 * (∑ r, (p.heavyInRow r).card) ≤ p.grade := by
  rw [← Pattern.card_heavy_eq_sum_card_heavyInRow]
  exact p.two_mul_card_heavy_le_grade

/-- Any row-indexed family injected into the light sites has total multiplicity
at most the grade.  This is the exact combinatorial premise used after the
row-local Gram/Parseval resummation. -/
theorem rowLocal_light_multiplicity_le_grade {m n : ℕ}
    (p : Pattern m n) (multiplicity : Fin m → ℕ)
    (hlocal : ∀ r, multiplicity r ≤ (p.lightInRow r).card) :
    (∑ r, multiplicity r) ≤ p.grade := by
  calc
    (∑ r, multiplicity r) ≤ ∑ r, (p.lightInRow r).card := by
      apply Finset.sum_le_sum
      intro r _
      exact hlocal r
    _ ≤ p.grade := sum_card_lightInRow_le_grade p

/-- Any row-indexed family injected into the heavy sites has doubled total
multiplicity at most the grade. -/
theorem two_mul_rowLocal_heavy_multiplicity_le_grade {m n : ℕ}
    (p : Pattern m n) (multiplicity : Fin m → ℕ)
    (hlocal : ∀ r, multiplicity r ≤ (p.heavyInRow r).card) :
    2 * (∑ r, multiplicity r) ≤ p.grade := by
  have hsum : (∑ r, multiplicity r) ≤ ∑ r, (p.heavyInRow r).card := by
    apply Finset.sum_le_sum
    intro r _
    exact hlocal r
  exact le_trans (Nat.mul_le_mul_left 2 hsum)
    (two_mul_sum_card_heavyInRow_le_grade p)

/-- Sharp count consequence for `Y₊`: unlike the coarser grade-only bound,
the move preserves the light count, so both occupation factors are at most `ν`. -/
theorem yPlus_count_sharp {ν : ℕ} (input : Profile)
    (hgrade : input.grade = ν) :
    input.yPlus.light * input.light ≤ ν * ν := by
  rw [Profile.yPlus_light]
  have hle : input.light ≤ ν := by
    simpa [hgrade] using input.light_le_grade
  exact Nat.mul_le_mul hle hle

/-- Denominator-cleared occupation product for `Y₀`. -/
theorem yZero_count {ν : ℕ} (input : Profile) (hheavy : 1 ≤ input.heavy)
    (hgrade : input.grade = ν) :
    2 * (input.yZero.light * input.heavy) ≤ ν * ν := by
  have houtGrade : input.yZero.grade = ν := by
    rw [input.yZero_grade hheavy, hgrade]
  have hout : input.yZero.light ≤ ν := by
    simpa [houtGrade] using input.yZero.light_le_grade
  have hin : 2 * input.heavy ≤ ν := by
    simpa [hgrade] using input.two_mul_heavy_le_grade
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul hout hin

/-- Occupation product for the transpose light hop. -/
theorem lightHop_count {ν : ℕ} (input : Profile)
    (hgrade : input.grade = ν) :
    input.lightHop.light * input.light ≤ ν * ν := by
  rw [Profile.lightHop_light]
  have hle : input.light ≤ ν := by
    simpa [hgrade] using input.light_le_grade
  exact Nat.mul_le_mul hle hle

/-- Abstract energy closure for `Y₊` and the transpose hop.

`hOutputCS` is the output-side Cauchy--Schwarz/row-Gram estimate and
`hInputParseval` is the reindexed input-side fresh-Parseval estimate.  They are
named hypotheses because this module does not define the Hilbert-space operators. -/
theorem directional_energy_sq_bound
    {ν inputEnergy reindexedEnergy outputEnergy : ℝ}
    (hν : 0 ≤ ν) (_hinput : 0 ≤ inputEnergy)
    (hOutputCS : outputEnergy ≤ ν * reindexedEnergy)
    (hInputParseval : reindexedEnergy ≤ ν * inputEnergy) :
    outputEnergy ≤ ν ^ 2 * inputEnergy := by
  calc
    outputEnergy ≤ ν * reindexedEnergy := hOutputCS
    _ ≤ ν * (ν * inputEnergy) := by
      exact mul_le_mul_of_nonneg_left hInputParseval hν
    _ = ν ^ 2 * inputEnergy := by ring

/-- Abstract denominator-cleared energy closure for `Y₀`.

The second premise records that twice the reindexed heavy contribution is at
most `ν` times the input energy. -/
theorem directional_energy_half_sq_bound
    {ν inputEnergy reindexedEnergy outputEnergy : ℝ}
    (hν : 0 ≤ ν)
    (hOutputCS : outputEnergy ≤ ν * reindexedEnergy)
    (hInputHeavy : 2 * reindexedEnergy ≤ ν * inputEnergy) :
    2 * outputEnergy ≤ ν ^ 2 * inputEnergy := by
  calc
    2 * outputEnergy ≤ 2 * (ν * reindexedEnergy) := by linarith
    _ = ν * (2 * reindexedEnergy) := by ring
    _ ≤ ν * (ν * inputEnergy) := by
      exact mul_le_mul_of_nonneg_left hInputHeavy hν
    _ = ν ^ 2 * inputEnergy := by ring

end DirectionalBounds

end SparseFock


