import SparseFockFormal.FiniteProbability
import Mathlib.Tactic

/-!
# Finite local moments and bounded interaction degree

This module gives a distribution-level formulation of limited independence
which is independent of any particular random-matrix model.

`MatchesUpTo mu nu k` says that `mu` and `nu` have the same expectation for
every real observable which depends on at most `k` named coordinates.  On a
finite alphabet this is exactly equality of all marginals of order at most
`k` (indicators of point cylinders recover the marginal masses, and finite
linear combinations recover arbitrary observables).

`HasLocalDegree k f` is the additive span of observables which each depend on
at most `k` coordinates.  Unlike the support of `f` itself, this interaction
degree behaves additively under products.  Consequently `k`-wise marginal
matching transfers expectations of every observable of local degree at most
`k`.  These elementary facts are the bookkeeping layer used by the
SparseStack limited-independence theorem.
-/

open scoped BigOperators

namespace SparseFock

namespace FiniteLocalMoments

noncomputable section

variable {ι α : Type*}

/-- A function on a coordinate product depends only on the coordinates in
`S` when changing every coordinate outside `S` leaves its value unchanged. -/
def DependsOn [DecidableEq ι] (S : Finset ι) (f : (ι → α) → ℝ) : Prop :=
  ∀ x y, (∀ i, i ∈ S → x i = y i) → f x = f y

/-- Exact agreement of all finite marginals through order `k`, stated in its
equivalent observable form.  The premise quantifies over *every* local
observable, not over a distinguished target moment. -/
def MatchesUpTo [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ ν : FiniteLaw (ι → α)) (k : ℕ) : Prop :=
  ∀ (S : Finset ι), S.card ≤ k →
    ∀ f : (ι → α) → ℝ, DependsOn S f → μ.expect f = ν.expect f

theorem matchesUpTo_refl [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : FiniteLaw (ι → α)) (k : ℕ) : MatchesUpTo μ μ k := by
  intro S hS f hf
  rfl

theorem matchesUpTo_mono [Fintype ι] [DecidableEq ι] [Fintype α]
    {μ ν : FiniteLaw (ι → α)} {k l : ℕ}
    (h : MatchesUpTo μ ν l) (hkl : k ≤ l) : MatchesUpTo μ ν k := by
  intro S hS f hf
  exact h S (hS.trans hkl) f hf

/-- Equality of local marginals implies equality of every cylinder-event
probability involving at most `k` coordinates.  This makes the connection to
the usual event-level definition of `k`-wise independence explicit. -/
theorem prob_cylinder_eq_of_matchesUpTo
    [Fintype ι] [DecidableEq ι] [Fintype α]
    {μ ν : FiniteLaw (ι → α)} {k : ℕ}
    (h : MatchesUpTo μ ν k) (S : Finset ι) (hS : S.card ≤ k)
    (a : ι → α) :
    μ.prob {x | ∀ i ∈ S, x i = a i} =
      ν.prob {x | ∀ i ∈ S, x i = a i} := by
  let event : Set (ι → α) := {x | ∀ i ∈ S, x i = a i}
  have hdep : DependsOn S (FiniteLaw.indicator event) := by
    intro x y hxy
    have hmem : x ∈ event ↔ y ∈ event := by
      constructor
      · intro hx i hi
        rw [← hxy i hi]
        exact hx i hi
      · intro hy i hi
        rw [hxy i hi]
        exact hy i hi
    simp only [FiniteLaw.indicator]
    split <;> split <;> simp_all
  simpa [FiniteLaw.prob, event] using
    h S hS (FiniteLaw.indicator event) hdep

/-- The additive span of observables with coordinate support of size at most
`k`.  The explicit constructors are convenient for exact finite-sum proofs. -/
inductive HasLocalDegree [DecidableEq ι] (k : ℕ) : ((ι → α) → ℝ) → Prop
  | atom (S : Finset ι) (f : (ι → α) → ℝ)
      (card_le : S.card ≤ k) (depends : DependsOn S f) : HasLocalDegree k f
  | zero : HasLocalDegree k (fun _ => 0)
  | add {f g : (ι → α) → ℝ} :
      HasLocalDegree k f → HasLocalDegree k g →
        HasLocalDegree k (fun x => f x + g x)
  | smul (c : ℝ) {f : (ι → α) → ℝ} :
      HasLocalDegree k f → HasLocalDegree k (fun x => c * f x)

namespace HasLocalDegree

variable [DecidableEq ι]

theorem congr {k : ℕ} {f g : (ι → α) → ℝ}
    (hf : HasLocalDegree k f) (hfg : f = g) : HasLocalDegree k g := by
  subst g
  exact hf

theorem constant (k : ℕ) (c : ℝ) :
    HasLocalDegree (ι := ι) (α := α) k (fun _ => c) := by
  apply atom ∅ (fun _ => c)
  · simp
  · intro x y hxy
    rfl

theorem neg {k : ℕ} {f : (ι → α) → ℝ}
    (hf : HasLocalDegree k f) :
    HasLocalDegree k (fun x => -f x) := by
  simpa using smul (-1) hf

theorem sub {k : ℕ} {f g : (ι → α) → ℝ}
    (hf : HasLocalDegree k f) (hg : HasLocalDegree k g) :
    HasLocalDegree k (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using add hf (neg hg)

theorem mono {k l : ℕ} {f : (ι → α) → ℝ}
    (hf : HasLocalDegree k f) (hkl : k ≤ l) : HasLocalDegree l f := by
  induction hf with
  | atom S f hcard hdep =>
      exact atom S f (hcard.trans hkl) hdep
  | zero => exact zero
  | add hf hg ihf ihg => exact add ihf ihg
  | smul c hf ih => exact smul c ih

theorem sum_finset {β : Type*} {k : ℕ} (T : Finset β)
    (f : β → (ι → α) → ℝ)
    (hf : ∀ t ∈ T, HasLocalDegree k (f t)) :
    HasLocalDegree k (fun x => ∑ t ∈ T, f t x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using (zero : HasLocalDegree k (fun _ : ι → α => 0))
  | @insert t T ht ih =>
      have hhead := hf t (Finset.mem_insert_self t T)
      have htail : ∀ u ∈ T, HasLocalDegree k (f u) := by
        intro u hu
        exact hf u (Finset.mem_insert_of_mem hu)
      simpa [Finset.sum_insert ht] using add hhead (ih htail)

theorem sum_fintype {β : Type*} [Fintype β] {k : ℕ}
    (f : β → (ι → α) → ℝ)
    (hf : ∀ t, HasLocalDegree k (f t)) :
    HasLocalDegree k (fun x => ∑ t, f t x) := by
  classical
  simpa using sum_finset (Finset.univ : Finset β) f
    (fun t _ht => hf t)

private theorem mul_local_left {k l : ℕ} (S : Finset ι)
    (f : (ι → α) → ℝ) (hcard : S.card ≤ k) (hdep : DependsOn S f)
    {g : (ι → α) → ℝ} (hg : HasLocalDegree l g) :
    HasLocalDegree (k + l) (fun x => f x * g x) := by
  induction hg with
  | atom T g hT hgd =>
      apply atom (S ∪ T) (fun x => f x * g x)
      · calc
          (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le S T
          _ ≤ k + l := Nat.add_le_add hcard hT
      · intro x y hxy
        have hfxy : f x = f y := hdep x y (fun i hi => hxy i (Finset.mem_union_left T hi))
        have hgxy : g x = g y := hgd x y (fun i hi => hxy i (Finset.mem_union_right S hi))
        change f x * g x = f y * g y
        rw [hfxy, hgxy]
  | zero =>
      simpa using (zero : HasLocalDegree (k + l) (fun _ : ι → α => 0))
  | add hg₁ hg₂ ih₁ ih₂ =>
      simpa [mul_add] using add ih₁ ih₂
  | smul c hg ih =>
      have hscaled := smul c ih
      convert hscaled using 1
      funext x
      ring

/-- Interaction degrees add under pointwise multiplication.  This is the
finite-coordinate analogue of the elementary fact that degrees add when
polynomials are multiplied. -/
theorem mul {k l : ℕ} {f g : (ι → α) → ℝ}
    (hf : HasLocalDegree k f) (hg : HasLocalDegree l g) :
    HasLocalDegree (k + l) (fun x => f x * g x) := by
  induction hf with
  | atom S f hS hfd => exact mul_local_left S f hS hfd hg
  | zero =>
      simpa using (zero : HasLocalDegree (k + l) (fun _ : ι → α => 0))
  | add hf₁ hf₂ ih₁ ih₂ =>
      simpa [add_mul] using add ih₁ ih₂
  | smul c hf ih =>
      have hscaled := smul c ih
      convert hscaled using 1
      funext x
      ring

/-- Marginal matching transfers expectations of all observables of bounded
local interaction degree. -/
theorem expect_eq_of_matchesUpTo [Fintype ι] [Fintype α]
    {μ ν : FiniteLaw (ι → α)} {k : ℕ} {f : (ι → α) → ℝ}
    (hmatch : MatchesUpTo μ ν k) (hf : HasLocalDegree k f) :
    μ.expect f = ν.expect f := by
  induction hf with
  | atom S f hcard hdep => exact hmatch S hcard f hdep
  | zero => simp
  | add hf hg ihf ihg =>
      rw [μ.expect_add, ν.expect_add, ihf, ihg]
  | smul c hf ih =>
      rw [μ.expect_smul, ν.expect_smul, ih]

end HasLocalDegree

end

end FiniteLocalMoments

end SparseFock
