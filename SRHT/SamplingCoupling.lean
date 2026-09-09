import SRHT.SamplingFinite
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! A literal finite fill/thin coupling, obtained by randomizing a nested
deterministic pair with a uniform permutation. -/

namespace SRHT.Sampling
open SparseFock
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev Exact (J : Type*) [Fintype J] (M : ℕ) := {T : Finset J // T.card = M}

theorem exact_nonempty {M : ℕ} (hM : M ≤ Fintype.card J) : Nonempty (Exact J M) := by
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset J))
    (by simpa using hM)
  exact ⟨T, hT⟩

theorem exists_nested_target {M : ℕ} (hM : M ≤ Fintype.card J) (B : Finset J) :
    ∃ T : Exact J M, (T.val ⊆ B ∨ B ⊆ T.val) := by
  by_cases h : M ≤ B.card
  · obtain ⟨T, hTB, hT⟩ := Finset.exists_subset_card_eq h
    exact ⟨⟨T, hT⟩, Or.inl hTB⟩
  · obtain ⟨T, hBT, hT⟩ := Finset.exists_superset_card_eq (le_of_lt (Nat.lt_of_not_ge h)) hM
    exact ⟨⟨T, hT⟩, Or.inr hBT⟩

def target {M : ℕ} (hM : M ≤ Fintype.card J) (B : Finset J) : Exact J M :=
  Classical.choose (exists_nested_target hM B)

theorem target_nested {M : ℕ} (hM : M ≤ Fintype.card J) (B : Finset J) :
    (target hM B).val ⊆ B ∨ B ⊆ (target hM B).val :=
  Classical.choose_spec (exists_nested_target hM B)

def actExact {M : ℕ} (π : Equiv.Perm J) (T : Exact J M) : Exact J M :=
  ⟨T.val.map π.toEmbedding, by simpa using T.property⟩

def actExactEquiv {M : ℕ} (π : Equiv.Perm J) : Exact J M ≃ Exact J M where
  toFun := actExact π
  invFun := actExact π.symm
  left_inv T := by
    apply Subtype.ext
    simp [actExact, Finset.map_map]
  right_inv T := by
    apply Subtype.ext
    simp [actExact, Finset.map_map]

theorem exact_transitive {M : ℕ} (T U : Exact J M) :
    ∃ π : Equiv.Perm J, actExact π T = U := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq T.val U.val
    (T.property.trans U.property.symm)
  exact ⟨π, Subtype.ext hπ⟩

def sourceLaw (μ : FiniteLaw (Finset J)) : FiniteLaw (Finset J × Equiv.Perm J) :=
  productLaw μ (uniformLaw (Equiv.Perm J))

def outcome {M : ℕ} (hM : M ≤ Fintype.card J)
    (z : Finset J × Equiv.Perm J) : Finset J × Exact J M :=
  (z.2.finsetCongr z.1, actExact z.2 (target hM z.1))

def jointLaw (μ : FiniteLaw (Finset J)) {M : ℕ} (hM : M ≤ Fintype.card J) :
    FiniteLaw (Finset J × Exact J M) := mapLaw (sourceLaw μ) (outcome hM)

def sourceAct (σ : Equiv.Perm J) :
    (Finset J × Equiv.Perm J) ≃ (Finset J × Equiv.Perm J) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.mulLeft σ)

def pairAct {M : ℕ} (σ : Equiv.Perm J) :
    (Finset J × Exact J M) ≃ (Finset J × Exact J M) :=
  Equiv.prodCongr σ.finsetCongr (actExactEquiv σ)

theorem outcome_act {M : ℕ} (hM : M ≤ Fintype.card J)
    (σ : Equiv.Perm J) (z : Finset J × Equiv.Perm J) :
    outcome hM (sourceAct σ z) = pairAct σ (outcome hM z) := by
  apply Prod.ext
  · ext j
    simp [outcome, sourceAct, pairAct, Finset.mem_map_equiv]
    rfl
  · apply Subtype.ext
    ext j
    simp [outcome, sourceAct, pairAct, actExactEquiv, actExact, Finset.mem_map_equiv]
    rfl

theorem jointLaw_invariant (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (σ : Equiv.Perm J) (B : Finset J) (T : Exact J M) :
    (jointLaw μ hM).weight (σ.finsetCongr B, actExact σ T) =
      (jointLaw μ hM).weight (B,T) := by
  exact mapLaw_invariant (sourceLaw μ) (outcome hM) (sourceAct σ) (pairAct σ)
    (fun z => rfl) (outcome_act hM σ) (B,T)

def Exchangeable (μ : FiniteLaw (Finset J)) : Prop :=
  ∀ (π : Equiv.Perm J) (B : Finset J), μ.weight (π.finsetCongr B) = μ.weight B

theorem joint_first_marginal (μ : FiniteLaw (Finset J)) (hμ : Exchangeable μ)
    {M : ℕ} (hM : M ≤ Fintype.card J) (B : Finset J) :
    (∑ T : Exact J M, (jointLaw μ hM).weight (B,T)) = μ.weight B := by
  classical
  change (∑ T, ∑ z, if outcome hM z = (B,T) then (sourceLaw μ).weight z else 0) = _
  rw [Finset.sum_comm]
  have hinner (z : Finset J × Equiv.Perm J) :
      (∑ T : Exact J M, if outcome hM z = (B,T) then (sourceLaw μ).weight z else 0) =
        if z.2.finsetCongr z.1 = B then (sourceLaw μ).weight z else 0 := by
    simp only [outcome, Prod.mk.injEq]
    by_cases hz : z.2.finsetCongr z.1 = B
    · simp only [hz, true_and, ite_true]
      simp
    · simp only [hz, false_and, ite_false, Finset.sum_const_zero]
  simp_rw [hinner]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hp (π : Equiv.Perm J) :
      (∑ b : Finset J, if π.finsetCongr b = B then (sourceLaw μ).weight (b,π) else 0) =
        μ.weight B * (uniformLaw (Equiv.Perm J)).weight π := by
    rw [Finset.sum_eq_single (π.finsetCongr.symm B)]
    · simp only [Equiv.apply_symm_apply, ite_true, sourceLaw, productLaw]
      rw [← hμ π (π.finsetCongr.symm B), Equiv.apply_symm_apply]
    · intro b _ hb
      have hh : π.finsetCongr b ≠ B := by
        intro h
        apply hb
        exact π.finsetCongr.injective (h.trans (π.finsetCongr.apply_symm_apply B).symm)
      exact if_neg hh
    · simp
  simp_rw [hp]
  rw [← Finset.mul_sum, (uniformLaw (Equiv.Perm J)).sum_weight, mul_one]

def targetMarginal (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T : Exact J M) : ℝ :=
  ∑ B, (jointLaw μ hM).weight (B,T)

theorem targetMarginal_invariant (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (σ : Equiv.Perm J) (T : Exact J M) :
    targetMarginal μ hM (actExact σ T) = targetMarginal μ hM T := by
  unfold targetMarginal
  rw [← σ.finsetCongr.sum_comp (fun B => (jointLaw μ hM).weight (B,actExact σ T))]
  simp_rw [jointLaw_invariant]

theorem targetMarginal_constant (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T U : Exact J M) :
    targetMarginal μ hM T = targetMarginal μ hM U := by
  obtain ⟨σ, hσ⟩ := exact_transitive T U
  rw [← hσ, targetMarginal_invariant]

theorem targetMarginal_sum (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) : ∑ T, targetMarginal μ hM T = 1 := by
  unfold targetMarginal
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact (jointLaw μ hM).sum_weight

theorem targetMarginal_uniform (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (T : Exact J M) :
    targetMarginal μ hM T = 1 / (Fintype.card (Exact J M) : ℝ) := by
  letI := exact_nonempty hM
  have hsum : (Fintype.card (Exact J M) : ℝ) * targetMarginal μ hM T = 1 := by
    calc
      _ = ∑ _U : Exact J M, targetMarginal μ hM T := by simp
      _ = ∑ U : Exact J M, targetMarginal μ hM U := by
        apply Finset.sum_congr rfl
        intro U _
        exact targetMarginal_constant μ hM T U
      _ = 1 := targetMarginal_sum μ hM
  apply (eq_div_iff (by positivity : (Fintype.card (Exact J M) : ℝ) ≠ 0)).2
  nlinarith

theorem outcome_nested {M : ℕ} (hM : M ≤ Fintype.card J)
    (z : Finset J × Equiv.Perm J) :
    (outcome hM z).1 ⊆ (outcome hM z).2.val ∨
      (outcome hM z).2.val ⊆ (outcome hM z).1 := by
  rcases target_nested hM z.1 with h | h
  · right
    exact Finset.map_subset_map.mpr h
  · left
    exact Finset.map_subset_map.mpr h

theorem jointLaw_zero_of_not_nested (μ : FiniteLaw (Finset J)) {M : ℕ}
    (hM : M ≤ Fintype.card J) (B : Finset J) (T : Exact J M)
    (h : ¬ (B ⊆ T.val ∨ T.val ⊆ B)) : (jointLaw μ hM).weight (B,T) = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  change (if outcome hM z = (B,T) then _ else _) = 0
  split_ifs with hz
  · have hh := outcome_nested hM z
    rw [hz] at hh
    exact (h hh).elim
  · rfl

end
end SRHT.Sampling
