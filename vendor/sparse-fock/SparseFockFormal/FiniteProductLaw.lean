import SparseFockFormal.FiniteProbability
import Mathlib.Tactic

/-!
# Binary products of explicit finite probability laws

The core finite-probability module builds iid coordinate products.  This file
adds the heterogeneous product needed to state independence of a random frame
and the SparseStack sketch literally.
-/

namespace SparseFock

open scoped BigOperators

namespace FiniteLaw

noncomputable section

variable {alpha beta : Type*} [Fintype alpha] [Fintype beta]

/-- The literal independent product of two finite laws, possibly on different
finite types. -/
def product (mu : FiniteLaw alpha) (nu : FiniteLaw beta) :
    FiniteLaw (alpha × beta) where
  weight x := mu.weight x.1 * nu.weight x.2
  weight_nonneg x := mul_nonneg (mu.weight_nonneg x.1) (nu.weight_nonneg x.2)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [nu.sum_weight]
    simpa using mu.sum_weight

@[simp] theorem product_weight (mu : FiniteLaw alpha) (nu : FiniteLaw beta)
    (a : alpha) (b : beta) :
    (product mu nu).weight (a, b) = mu.weight a * nu.weight b := rfl

/-- Fubini's identity for the explicit product weights. -/
theorem product_expect_eq_iterated (mu : FiniteLaw alpha) (nu : FiniteLaw beta)
    (f : alpha × beta → ℝ) :
    (product mu nu).expect f =
      mu.expect (fun a ↦ nu.expect (fun b ↦ f (a, b))) := by
  rw [expect, expect, Fintype.sum_prod_type]
  simp only [product_weight]
  simp_rw [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Event form of heterogeneous Fubini. -/
theorem product_prob_eq_iterated (mu : FiniteLaw alpha) (nu : FiniteLaw beta)
    (event : Set (alpha × beta)) :
    (product mu nu).prob event =
      mu.expect (fun a ↦ nu.prob {b | (a, b) ∈ event}) := by
  rw [prob, product_expect_eq_iterated]
  apply expect_congr
  intro a
  rw [prob]
  apply expect_congr
  intro b
  rfl

/-- Uniform conditional upper bounds pass to an independent product law. -/
theorem product_prob_le {mu : FiniteLaw alpha} {nu : FiniteLaw beta}
    {event : Set (alpha × beta)} {delta : ℝ}
    (h : ∀ a, nu.prob {b | (a, b) ∈ event} ≤ delta) :
    (product mu nu).prob event ≤ delta := by
  rw [product_prob_eq_iterated]
  calc
    mu.expect (fun a ↦ nu.prob {b | (a, b) ∈ event}) ≤
        mu.expect (fun _ ↦ delta) := expect_mono mu h
    _ = delta := expect_const mu delta

/-- Uniform conditional success lower bounds pass to an independent product
law. -/
theorem le_product_prob {mu : FiniteLaw alpha} {nu : FiniteLaw beta}
    {event : Set (alpha × beta)} {p : ℝ}
    (h : ∀ a, p ≤ nu.prob {b | (a, b) ∈ event}) :
    p ≤ (product mu nu).prob event := by
  rw [product_prob_eq_iterated]
  calc
    p = mu.expect (fun _ ↦ p) := (expect_const mu p).symm
    _ ≤ mu.expect (fun a ↦ nu.prob {b | (a, b) ∈ event}) := expect_mono mu h

end

end FiniteLaw

end SparseFock
