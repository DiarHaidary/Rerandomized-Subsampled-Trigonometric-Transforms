import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Elementary probability on finite types

This file supplies a small, explicit probability foundation for the finite
random objects in the sparse-Fock argument.  A `FiniteLaw α` is a nonnegative
real weight on the finite type `α` whose total mass is one.  Expectations and
event probabilities are finite sums, so none of the results below hide
measurability, integrability, or independence hypotheses.

The main construction is `FiniteLaw.independentProduct`.  Its outcome is a
function `x : ι → α`, and its mass is the literal product of the coordinate
masses.  The coordinate marginal, separated-observable factorization, and
cylinder-event factorization theorems therefore give genuine mutual
independence of the coordinates.
-/

open scoped BigOperators

namespace SparseFock

noncomputable section

/-- A probability law on a finite type, represented by explicit real weights. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  /-- Probability mass of an outcome. -/
  weight : α → ℝ
  /-- Every outcome has nonnegative mass. -/
  weight_nonneg : ∀ x, 0 ≤ weight x
  /-- The total mass is one. -/
  sum_weight : ∑ x, weight x = 1

namespace FiniteLaw

variable {α β ι κ : Type*}

section Basic

variable [Fintype α]

/-- The expectation of a real-valued observable under a finite law. -/
def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

/-- The real indicator of a set. -/
def indicator (s : Set α) (x : α) : ℝ :=
  by
    classical
    exact if x ∈ s then 1 else 0

/-- Probability of an event, defined as the expectation of its indicator. -/
def prob (μ : FiniteLaw α) (s : Set α) : ℝ :=
  μ.expect (indicator s)

@[simp] theorem expect_zero (μ : FiniteLaw α) :
    μ.expect (fun _ => 0) = 0 := by
  simp [expect]

@[simp] theorem expect_one (μ : FiniteLaw α) :
    μ.expect (fun _ => 1) = 1 := by
  simpa [expect] using μ.sum_weight

@[simp] theorem expect_const (μ : FiniteLaw α) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  calc
    μ.expect (fun _ => c) = (∑ x, μ.weight x) * c := by
      simp_rw [expect, Finset.sum_mul]
    _ = c := by rw [μ.sum_weight, one_mul]

theorem expect_add (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x + g x) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_neg (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect (fun x => -f x) = -μ.expect f := by
  simp [expect]

theorem expect_smul (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

theorem expect_congr (μ : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ x, f x = g x) : μ.expect f = μ.expect g := by
  apply Finset.sum_congr rfl
  intro x _hx
  rw [h x]

theorem expect_nonneg (μ : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg fun x _hx => mul_nonneg (μ.weight_nonneg x) (hf x)

theorem expect_mono (μ : FiniteLaw α) {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro x _hx
  exact mul_le_mul_of_nonneg_left (hfg x) (μ.weight_nonneg x)

theorem abs_expect_le_expect_abs (μ : FiniteLaw α) (f : α → ℝ) :
    |μ.expect f| ≤ μ.expect (fun x => |f x|) := by
  calc
    |μ.expect f| = |∑ x, μ.weight x * f x| := rfl
    _ ≤ ∑ x, |μ.weight x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = μ.expect (fun x => |f x|) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [abs_mul, abs_of_nonneg (μ.weight_nonneg x)]

@[simp] theorem prob_empty (μ : FiniteLaw α) : μ.prob ∅ = 0 := by
  classical
  calc
    μ.prob ∅ = μ.expect (fun _ => 0) := by
      rw [prob]
      apply μ.expect_congr
      intro x
      unfold indicator
      simp
    _ = 0 := μ.expect_zero

@[simp] theorem prob_univ (μ : FiniteLaw α) : μ.prob Set.univ = 1 := by
  classical
  calc
    μ.prob Set.univ = μ.expect (fun _ => 1) := by
      rw [prob]
      apply μ.expect_congr
      intro x
      unfold indicator
      simp
    _ = 1 := μ.expect_one

theorem prob_nonneg (μ : FiniteLaw α) (s : Set α) : 0 ≤ μ.prob s := by
  classical
  apply μ.expect_nonneg
  intro x
  unfold indicator
  split <;> norm_num

theorem prob_le_one (μ : FiniteLaw α) (s : Set α) : μ.prob s ≤ 1 := by
  classical
  calc
    μ.prob s ≤ μ.expect (fun _ => 1) := by
      apply μ.expect_mono
      intro x
      unfold indicator
      split <;> norm_num
    _ = 1 := μ.expect_one

theorem prob_mem_Icc (μ : FiniteLaw α) (s : Set α) : μ.prob s ∈ Set.Icc 0 1 :=
  ⟨μ.prob_nonneg s, μ.prob_le_one s⟩

theorem prob_mono (μ : FiniteLaw α) {s t : Set α} (hst : s ⊆ t) :
    μ.prob s ≤ μ.prob t := by
  classical
  apply μ.expect_mono
  intro x
  by_cases hx : x ∈ s
  · have hxt : x ∈ t := hst hx
    simp [indicator, hx, hxt]
  · unfold indicator
    simp only [hx, ↓reduceIte]
    split <;> norm_num

theorem prob_compl (μ : FiniteLaw α) (s : Set α) :
    μ.prob sᶜ = 1 - μ.prob s := by
  classical
  calc
    μ.prob sᶜ = μ.expect (fun x => 1 - indicator s x) := by
      rw [prob]
      apply μ.expect_congr
      intro x
      by_cases hx : x ∈ s <;> simp [indicator, hx]
    _ = μ.expect (fun _ => 1) - μ.expect (indicator s) := μ.expect_sub _ _
    _ = 1 - μ.prob s := by rw [μ.expect_one]; rfl

theorem prob_singleton [DecidableEq α] (μ : FiniteLaw α) (a : α) :
    μ.prob {a} = μ.weight a := by
  classical
  simp [prob, expect, indicator]

/-- Finite Markov inequality in multiplication form. -/
theorem markov_mul (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (threshold : ℝ) :
    threshold * μ.prob {x | threshold ≤ f x} ≤ μ.expect f := by
  classical
  rw [prob, expect, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hlarge : threshold ≤ f x
  · simp [indicator, hlarge]
    calc
      threshold * μ.weight x = μ.weight x * threshold := by ring
      _ ≤ μ.weight x * f x :=
        mul_le_mul_of_nonneg_left hlarge (μ.weight_nonneg x)
  · simp [indicator, hlarge]
    exact mul_nonneg (μ.weight_nonneg x) (hf x)

/-- Standard divided form of finite Markov's inequality. -/
theorem markov (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    μ.prob {x | threshold ≤ f x} ≤ μ.expect f / threshold := by
  apply (le_div_iff₀ hthreshold).2
  simpa [mul_comm] using μ.markov_mul hf threshold

end Basic

section IndependentProduct

variable [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Product law with independent coordinates.  The joint mass is definitionally
the product of the individual coordinate masses. -/
def independentProduct (μ : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  weight x := ∏ i, (μ i).weight (x i)
  weight_nonneg x := Finset.prod_nonneg fun i _hi => (μ i).weight_nonneg (x i)
  sum_weight := by
    rw [← Fintype.prod_sum]
    simp only [(μ _).sum_weight, Finset.prod_const_one]

@[simp] theorem independentProduct_weight (μ : ι → FiniteLaw α) (x : ι → α) :
    (independentProduct μ).weight x = ∏ i, (μ i).weight (x i) := rfl

/-- Exact factorization of the expectation of arbitrary separated coordinate
observables.  This is the principal independence theorem. -/
theorem expect_independentProduct_factorizes
    (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independentProduct μ).expect (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).expect (f i) := by
  calc
    (independentProduct μ).expect (fun x => ∏ i, f i (x i)) =
        ∑ x : ι → α, ∏ i, ((μ i).weight (x i) * f i (x i)) := by
      rw [expect]
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [independentProduct_weight, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a, ((μ i).weight a * f i a) := by
      exact (Fintype.prod_sum
        (fun i a => (μ i).weight a * f i a)).symm
    _ = ∏ i, (μ i).expect (f i) := by
      simp only [expect]

/-- Factorization remains exact when observables are attached only to a subset
of coordinates. -/
theorem expect_independentProduct_factorizes_on
    (μ : ι → FiniteLaw α) (s : Finset ι) (f : ι → α → ℝ) :
    (independentProduct μ).expect (fun x => ∏ i ∈ s, f i (x i)) =
      ∏ i ∈ s, (μ i).expect (f i) := by
  let g : ι → α → ℝ := fun i a => if i ∈ s then f i a else 1
  have hgpoint (x : ι → α) :
      (∏ i, g i (x i)) = ∏ i ∈ s, f i (x i) := by
    simp [g]
  have hgexpect (i : ι) :
      (μ i).expect (g i) = if i ∈ s then (μ i).expect (f i) else 1 := by
    by_cases hi : i ∈ s
    · simp [g, hi]
    · simp [g, hi]
  calc
    (independentProduct μ).expect (fun x => ∏ i ∈ s, f i (x i)) =
        (independentProduct μ).expect (fun x => ∏ i, g i (x i)) := by
      apply (independentProduct μ).expect_congr
      intro x
      exact (hgpoint x).symm
    _ = ∏ i, (μ i).expect (g i) :=
      expect_independentProduct_factorizes μ g
    _ = ∏ i ∈ s, (μ i).expect (f i) := by
      simp_rw [hgexpect]
      simp

/-- Every coordinate of the product law has its prescribed expectation. -/
theorem expect_independentProduct_apply
    (μ : ι → FiniteLaw α) (i : ι) (f : α → ℝ) :
    (independentProduct μ).expect (fun x => f (x i)) = (μ i).expect f := by
  have h := expect_independentProduct_factorizes_on μ {i} (fun _ => f)
  simpa using h

/-- Every coordinate event has its prescribed marginal probability. -/
theorem prob_independentProduct_apply
    (μ : ι → FiniteLaw α) (i : ι) (s : Set α) :
    (independentProduct μ).prob {x | x i ∈ s} = (μ i).prob s := by
  classical
  calc
    (independentProduct μ).prob {x | x i ∈ s} =
        (independentProduct μ).expect (fun x => indicator s (x i)) := by
      rw [prob]
      apply (independentProduct μ).expect_congr
      intro x
      simp [indicator]
    _ = (μ i).expect (indicator s) :=
      expect_independentProduct_apply μ i (indicator s)
    _ = (μ i).prob s := rfl

/-- In particular, the one-coordinate mass of the product law is the original
coordinate mass. -/
theorem prob_independentProduct_eq
    [DecidableEq α] (μ : ι → FiniteLaw α) (i : ι) (a : α) :
    (independentProduct μ).prob {x | x i = a} = (μ i).weight a := by
  calc
    (independentProduct μ).prob {x | x i = a} =
        (μ i).prob {a} := by
      simpa only [Set.mem_singleton_iff] using
        prob_independentProduct_apply μ i ({a} : Set α)
    _ = (μ i).weight a := prob_singleton (μ i) a

/-- The cylinder event determined by one event at each coordinate. -/
def cylinder (s : ι → Set α) : Set (ι → α) :=
  {x | ∀ i, x i ∈ s i}

omit [DecidableEq ι] [Fintype α] in
theorem indicator_cylinder (s : ι → Set α) (x : ι → α) :
    indicator (cylinder s) x = ∏ i, indicator (s i) (x i) := by
  classical
  by_cases hall : ∀ i, x i ∈ s i
  · simp [indicator, cylinder, hall]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hleft : x ∉ cylinder s := by
      intro hx
      exact hi (hx i)
    rw [indicator]
    simp only [hleft, ↓reduceIte]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [indicator, hi]

/-- Exact factorization of all finite coordinate-cylinder events.  This is the
event-level statement of mutual independence. -/
theorem prob_independentProduct_cylinder
    (μ : ι → FiniteLaw α) (s : ι → Set α) :
    (independentProduct μ).prob (cylinder s) = ∏ i, (μ i).prob (s i) := by
  calc
    (independentProduct μ).prob (cylinder s) =
        (independentProduct μ).expect
          (fun x => ∏ i, indicator (s i) (x i)) := by
      rw [prob]
      apply (independentProduct μ).expect_congr
      intro x
      exact indicator_cylinder s x
    _ = ∏ i, (μ i).expect (indicator (s i)) :=
      expect_independentProduct_factorizes μ (fun i => indicator (s i))
    _ = ∏ i, (μ i).prob (s i) := by
      simp only [prob]

end IndependentProduct

end FiniteLaw

end

end SparseFock
