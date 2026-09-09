import SparseFockFormal.FiniteProbability
import Mathlib.Tactic

namespace SRHT.Sampling
open SparseFock
open scoped BigOperators
noncomputable section

def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := 1 / (Fintype.card α : ℝ)
  weight_nonneg _ := by positivity
  sum_weight := by
    have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [h]

def mapLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : FiniteLaw α) (f : α → β) : FiniteLaw β where
  weight y := ∑ x, if f x = y then μ.weight x else 0
  weight_nonneg y := Finset.sum_nonneg fun x _ => by
    split_ifs <;> simp [μ.weight_nonneg]
  sum_weight := by
    rw [Finset.sum_comm]
    simpa using μ.sum_weight

theorem mapLaw_expect {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (mapLaw μ f).expect g = μ.expect (fun x => g (f x)) := by
  classical
  simp only [FiniteLaw.expect, mapLaw]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

def productLaw {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  weight z := μ.weight z.1 * ν.weight z.2
  weight_nonneg z := mul_nonneg (μ.weight_nonneg _) (ν.weight_nonneg _)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.sum_weight, mul_one]
    exact μ.sum_weight

theorem uniformLaw_weight_pos {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    0 < (uniformLaw α).weight a := by
  change 0 < 1 / (Fintype.card α : ℝ)
  positivity

theorem uniformLaw_invariant {α : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (a : α) : (uniformLaw α).weight (e a) = (uniformLaw α).weight a := rfl

theorem mapLaw_invariant {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : FiniteLaw α) (f : α → β) (e : α ≃ α) (g : β ≃ β)
    (hμ : ∀ a, μ.weight (e a) = μ.weight a)
    (hf : ∀ a, f (e a) = g (f a)) (b : β) :
    (mapLaw μ f).weight (g b) = (mapLaw μ f).weight b := by
  change (∑ a, if f a = g b then μ.weight a else 0) = _
  rw [← e.sum_comp (fun a => if f a = g b then μ.weight a else 0)]
  simp_rw [hf, hμ, g.injective.eq_iff]
  rfl

theorem mapLaw_expect_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : FiniteLaw α) (e : α ≃ β) (b : β) :
    (mapLaw μ e).weight b = μ.weight (e.symm b) := by
  simp only [mapLaw]
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ ha
    have hh : e a ≠ b := by
      intro h
      apply ha
      exact e.injective (h.trans (e.apply_symm_apply b).symm)
    simp [hh]
  · simp

end
end SRHT.Sampling
