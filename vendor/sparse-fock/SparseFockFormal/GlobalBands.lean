import SparseFockFormal.ExternalOperators

/-!
# Concrete global sparse--Fock bands

This module forms the actual sums over rows and ordered distinct column pairs.
It then groups all sixteen local Jacobi products into the nine
shift/heaviness cells from `BandInventory`.  Thus the decomposition here is an
equality of concrete finite matrices, not an abstract band interface.
-/

namespace SparseFock.GlobalBands

open BandInventory LocalOperator FiniteOperator ExternalOperator

noncomputable section

variable {d m n : ℕ}

theorem sum_leg {A : Type*} [AddCommMonoid A] (f : Leg → A) :
    ∑ a, f a = f .pUp + f .pDown + f .rUp + f .rDown := by
  rw [show (Finset.univ : Finset Leg) = {.pUp, .pDown, .rUp, .rDown} by decide]
  simp [add_assoc]

theorem sum_shift {A : Type*} [AddCommMonoid A] (f : Shift → A) :
    ∑ δ, f δ = f .plus + f .zero + f .minus := by
  rw [show (Finset.univ : Finset Shift) = {.plus, .zero, .minus} by decide]
  simp [add_assoc]

theorem sum_heaviness {A : Type*} [AddCommMonoid A] (f : Heaviness → A) :
    ∑ h, f h = f .lightLight + f .lightHeavy + f .heavyHeavy := by
  rw [show (Finset.univ : Finset Heaviness) =
    {.lightLight, .lightHeavy, .heavyHeavy} by decide]
  simp [add_assoc]

/-- The four oriented legs, with one factor of `ρ` for every heavy leg,
sum to the local Jacobi multiplication matrix. -/
theorem jacobi_eq_weighted_legs (ρ : ℝ) :
    jacobi ρ = ∑ a : Leg, ρ ^ a.heavy • a.op := by
  ext out inp
  cases out <;> cases inp <;>
    simp [sum_leg, jacobi, Leg.op, Leg.heavy, pCreate, pDestroy,
      rPromote, rDemote, ketBra]

/-- At two distinct physical sites, the product of the two Jacobi matrices is
exactly the weighted sum of all sixteen oriented words. -/
theorem pairKernel_jacobi_eq_all_words
    (ρ : ℝ) (s t : Site m n) :
    pairKernel s t (jacobi ρ) (jacobi ρ) =
      ∑ w : Word, ρ ^ w.heavy • wordKernel s t w := by
  classical
  ext out inp
  by_cases hoff : agreesOutsidePair s t out inp
  · simp only [pairKernel, wordKernel, hoff, if_pos, Matrix.sum_apply,
      Matrix.smul_apply, Fintype.sum_prod_type, sum_leg, Word.heavy,
      Matrix.add_apply, Leg.heavy]
    cases hos : out s <;> cases his : inp s <;>
      cases hot : out t <;> cases hit : inp t <;>
      simp [jacobi, Leg.op, pCreate, pDestroy, rPromote, rDemote, ketBra,
        hos, his, hot, hit] <;> ring
  · simp [pairKernel, wordKernel, hoff, Fintype.sum_prod_type, sum_leg]

/-- One ordered physical Jacobi-pair term. -/
def orderedJacobiTerm
    (u : Fin n → Fin d → ℝ) (ρ : ℝ)
    (r : Fin m) (i j : Fin n) : FullOp d m n :=
  externalTensor (outer (u i) (u j))
    (pairKernel (r, i) (r, j) (jacobi ρ) (jacobi ρ))

theorem orderedJacobiTerm_eq_all_words
    (u : Fin n → Fin d → ℝ) (ρ : ℝ)
    (r : Fin m) (i j : Fin n) :
    orderedJacobiTerm u ρ r i j =
      ∑ w : Word, ρ ^ w.heavy • orderedWordTerm u r i j w := by
  classical
  ext out inp
  rw [orderedJacobiTerm, pairKernel_jacobi_eq_all_words]
  simp only [externalTensor, orderedWordTerm, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The full unnormalised operator: actual rows and actual ordered `i ≠ j`
pairs only. -/
def rawMultiplication
    (m : ℕ) (u : Fin n → Fin d → ℝ) (ρ : ℝ) : FullOp d m n :=
  ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i, orderedJacobiTerm u ρ r i j

/-- The physical sum associated with one oriented local word. -/
def physicalWordSum
    (m : ℕ) (u : Fin n → Fin d → ℝ) (w : Word) : FullOp d m n :=
  ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i, orderedWordTerm u r i j w

/-- Fubini plus scalar distributivity for the four finite indices used by a
physical word sum. -/
theorem sum_ordered_pairs_comm {A : Type*} [AddCommMonoid A] [Module ℝ A]
    (c : Word → ℝ) (f : Fin m → Fin n → Fin n → Word → A) :
    (∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ w, c w • f r i j w) =
      ∑ w, c w • (∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i, f r i j w) := by
  classical
  have hj (r : Fin m) (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, ∑ w, c w • f r i j w) =
        ∑ w, c w • (∑ j ∈ Finset.univ.erase i, f r i j w) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.smul_sum]
  have hi (r : Fin m) :
      (∑ i, ∑ j ∈ Finset.univ.erase i, ∑ w, c w • f r i j w) =
        ∑ w, c w • (∑ i, ∑ j ∈ Finset.univ.erase i, f r i j w) := by
    simp_rw [hj r]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.smul_sum]
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.smul_sum]

theorem rawMultiplication_eq_all_words
    (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    rawMultiplication m u ρ =
      ∑ w : Word, ρ ^ w.heavy • physicalWordSum m u w := by
  classical
  unfold rawMultiplication physicalWordSum
  simp_rw [orderedJacobiTerm_eq_all_words]
  exact sum_ordered_pairs_comm (m := m) (n := n)
    (fun w ↦ ρ ^ w.heavy) (fun r i j w ↦ orderedWordTerm u r i j w)

/-- One concrete cell in the `3 × 3` inventory. -/
def cell
    (m : ℕ) (u : Fin n → Fin d → ℝ) (ρ : ℝ)
    (δ : Shift) (h : Heaviness) : FullOp d m n :=
  ∑ w ∈ wordsIn δ h, ρ ^ w.heavy • physicalWordSum m u w

/-- A global grade band, still split internally into its three exact
heaviness cells. -/
def band
    (m : ℕ) (u : Fin n → Fin d → ℝ) (ρ : ℝ) (δ : Shift) : FullOp d m n :=
  ∑ h : Heaviness, cell m u ρ δ h

/-- Pure finite partition identity: every one of the sixteen words occurs in
exactly one inventory cell. -/
theorem sum_all_cells {A : Type*} [AddCommMonoid A] (f : Word → A) :
    (∑ δ : Shift, ∑ h : Heaviness, ∑ w ∈ wordsIn δ h, f w) =
      ∑ w : Word, f w := by
  classical
  rw [sum_shift]
  simp only [sum_heaviness]
  simp only [wordsIn, Finset.sum_filter, Fintype.sum_prod_type, sum_leg]
  simp [Word.shift, Word.heaviness]
  abel

/-- The concrete Jacobi-pair operator is the sum of its `+2`, `0`, and `-2`
bands. -/
theorem rawMultiplication_eq_sum_bands
    (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    rawMultiplication m u ρ = ∑ δ : Shift, band m u ρ δ := by
  rw [rawMultiplication_eq_all_words]
  symm
  exact sum_all_cells (fun w ↦ ρ ^ w.heavy • physicalWordSum m u w)

/-- An unweighted named family, useful for matching the paper's `L`, mixed,
and `H` notation. -/
def family
    (m : ℕ) (u : Fin n → Fin d → ℝ) (δ : Shift) (h : Heaviness) :
    FullOp d m n :=
  ∑ w ∈ wordsIn δ h, physicalWordSum m u w

theorem cell_lightLight
    (u : Fin n → Fin d → ℝ) (ρ : ℝ) (δ : Shift) :
    cell m u ρ δ .lightLight = family m u δ .lightLight := by
  apply Finset.sum_congr rfl
  intro w hw
  have hh : w.heavy = 0 := by
    have hcell : w.heaviness = .lightLight :=
      ((mem_wordsIn w δ .lightLight).mp hw).2
    rw [Word.heavy_eq_heaviness]
    rw [hcell]
  simp [hh]

theorem cell_lightHeavy
    (u : Fin n → Fin d → ℝ) (ρ : ℝ) (δ : Shift) :
    cell m u ρ δ .lightHeavy = ρ • family m u δ .lightHeavy := by
  rw [cell, family, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hh : w.heavy = 1 := by
    have hcell : w.heaviness = .lightHeavy :=
      ((mem_wordsIn w δ .lightHeavy).mp hw).2
    rw [Word.heavy_eq_heaviness]
    rw [hcell]
  simp [hh]

theorem cell_heavyHeavy
    (u : Fin n → Fin d → ℝ) (ρ : ℝ) (δ : Shift) :
    cell m u ρ δ .heavyHeavy = ρ ^ 2 • family m u δ .heavyHeavy := by
  rw [cell, family, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hh : w.heavy = 2 := by
    have hcell : w.heaviness = .heavyHeavy :=
      ((mem_wordsIn w δ .heavyHeavy).mp hw).2
    rw [Word.heavy_eq_heaviness]
    rw [hcell]
  simp [hh]

/-- The exact three-cell formula for every grade band.  Specialising
`ρ = sqrt (b-1)` gives coefficients `1`, `sqrt (b-1)`, and `b-1`. -/
theorem band_eq_three_families
    (u : Fin n → Fin d → ℝ) (ρ : ℝ) (δ : Shift) :
    band m u ρ δ =
      family m u δ .lightLight +
        ρ • family m u δ .lightHeavy +
        ρ ^ 2 • family m u δ .heavyHeavy := by
  rw [band, sum_heaviness, cell_lightLight, cell_lightHeavy, cell_heavyHeavy]

/-- Each concrete band has precisely its advertised grade change. -/
theorem band_homogeneous
    (u : Fin n → Fin d → ℝ) (ρ : ℝ) (δ : Shift) :
    ExternalOperator.Homogeneous δ.degree (band m u ρ δ) := by
  intro out inp hnonzero
  classical
  simp only [band, cell, Matrix.sum_apply, Matrix.smul_apply] at hnonzero
  by_contra hgrade
  have hz : ∀ h : Heaviness, ∀ w ∈ wordsIn δ h,
      (ρ ^ w.heavy • physicalWordSum m u w) out inp = 0 := by
    intro h w hw
    by_cases hc : ρ ^ w.heavy = 0
    · simp [hc]
    · have hshift := (mem_wordsIn w δ h).mp hw |>.1
      rw [Matrix.smul_apply]
      apply mul_eq_zero.mpr
      right
      simp only [physicalWordSum, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro r _
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j hj
      by_contra hterm
      have hom := orderedWordTerm_homogeneous u r
        (Ne.symm (Finset.mem_erase.mp hj).1) w hterm
      rw [Word.degree_eq_shift, hshift] at hom
      exact hgrade hom
  apply hnonzero
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro w hw
  exact hz h w hw

end

end SparseFock.GlobalBands
