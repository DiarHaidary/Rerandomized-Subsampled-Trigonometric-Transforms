import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace SparseFock

namespace LightSectorAbstract

open scoped BigOperators

/-- The sum over all indices other than `i` is the full sum with the `i`th
term removed.  This small identity is used to count every off-diagonal block
exactly `ell - 1` times. -/
theorem sum_erase_univ_eq_sub {ell : ℕ} (energy : Fin ell → ℝ) (i : Fin ell) :
    (∑ j ∈ (Finset.univ.erase i), energy j) = (∑ j, energy j) - energy i := by
  have hi : i ∈ (Finset.univ : Finset (Fin ell)) := Finset.mem_univ i
  rw [← Finset.sum_erase_add _ _ hi]
  ring

/-- The first-index contribution to an ordered off-diagonal sum. -/
theorem sum_offDiagonal_left {ell : ℕ} (hell : 1 ≤ ell)
    (energy : Fin ell → ℝ) :
    (∑ i, ∑ _j ∈ (Finset.univ.erase i), energy i) =
      ((ell : ℝ) - 1) * ∑ i, energy i := by
  have hcard (i : Fin ell) : (Finset.univ.erase i).card = ell - 1 := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  calc
    (∑ i, ∑ _j ∈ (Finset.univ.erase i), energy i) =
        ∑ i, (((ell - 1 : ℕ) : ℝ) * energy i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [hcard i]
    _ = (((ell - 1 : ℕ) : ℝ) * ∑ i, energy i) := by
          rw [Finset.mul_sum]
    _ = ((ell : ℝ) - 1) * ∑ i, energy i := by
          rw [Nat.cast_sub hell]
          norm_num

/-- The second-index contribution to an ordered off-diagonal sum. -/
theorem sum_offDiagonal_right {ell : ℕ} (_hell : 1 ≤ ell)
    (energy : Fin ell → ℝ) :
    (∑ i, ∑ j ∈ (Finset.univ.erase i), energy j) =
      ((ell : ℝ) - 1) * ∑ i, energy i := by
  let total : ℝ := ∑ i, energy i
  calc
    (∑ i, ∑ j ∈ (Finset.univ.erase i), energy j) =
        ∑ i, (total - energy i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact sum_erase_univ_eq_sub energy i
    _ = (ell : ℝ) * total - total := by
          simp [total, Finset.sum_sub_distrib]
    _ = ((ell : ℝ) - 1) * total := by ring
    _ = ((ell : ℝ) - 1) * ∑ i, energy i := by rfl

/-- Pairwise arithmetic behind the block-Gram estimate.

`cross i j` is the scalar contribution of the `(i,j)` block to one fixed
quadratic form, while `energy i` is the squared norm of the `i`th input block.
The premise is exactly the operator Cauchy--Schwarz estimate after
`2ab ≤ a²+b²`; no operator fact is hidden here. -/
theorem offDiagonal_sum_le {ell : ℕ} (hell : 1 ≤ ell)
    (energy : Fin ell → ℝ) (cross : Fin ell → Fin ell → ℝ)
    (hcross : ∀ i j, i ≠ j →
      cross i j ≤ (energy i + energy j) / 2) :
    (∑ i, ∑ j ∈ (Finset.univ.erase i), cross i j) ≤
      ((ell : ℝ) - 1) * ∑ i, energy i := by
  calc
    (∑ i, ∑ j ∈ (Finset.univ.erase i), cross i j) ≤
        ∑ i, ∑ j ∈ (Finset.univ.erase i),
          ((energy i + energy j) / 2) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j hj
            exact hcross i j (Finset.mem_erase.mp hj).1.symm
    _ = ((∑ i, ∑ _j ∈ (Finset.univ.erase i), energy i) +
          (∑ i, ∑ j ∈ (Finset.univ.erase i), energy j)) / 2 := by
            simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]
    _ = ((ell : ℝ) - 1) * ∑ i, energy i := by
          rw [sum_offDiagonal_left hell, sum_offDiagonal_right hell]
          ring

/-- A precise scalar certificate for the shared-leg block-Gram step.

To instantiate this with operators `V_i`, take `energy i = ‖z_i‖²`,
`diagonal i = ⟪z_i, V_i† V_i z_i⟫`, and let `cross i j` be the ordered
off-diagonal quadratic-form contribution.  The three hypotheses below are
exactly the facts that still have to be supplied by an operator formalization:

* `hquadratic`: expansion of the quadratic form into its blocks;
* `hdiag`: `V_i† V_i ≼ d I`;
* `hcross`: the cross-map contraction `‖V_i† V_j‖ ≤ 1` followed by scalar
  Cauchy--Schwarz.

The conclusion is the `d + ell - 1` light-sector constant. -/
theorem blockGram_of_pairwise_certificate {ell : ℕ} (hell : 1 ≤ ell)
    {d quadratic : ℝ}
    (energy diagonal : Fin ell → ℝ)
    (cross : Fin ell → Fin ell → ℝ)
    (hquadratic : quadratic ≤
      (∑ i, diagonal i) +
        ∑ i, ∑ j ∈ (Finset.univ.erase i), cross i j)
    (hdiag : ∀ i, diagonal i ≤ d * energy i)
    (hcross : ∀ i j, i ≠ j →
      cross i j ≤ (energy i + energy j) / 2) :
    quadratic ≤ (d + (ell : ℝ) - 1) * ∑ i, energy i := by
  have hdiagSum : (∑ i, diagonal i) ≤ d * ∑ i, energy i := by
    calc
      (∑ i, diagonal i) ≤ ∑ i, d * energy i := by
        apply Finset.sum_le_sum
        intro i _
        exact hdiag i
      _ = d * ∑ i, energy i := by rw [Finset.mul_sum]
  have hcrossSum := offDiagonal_sum_le hell energy cross hcross
  calc
    quadratic ≤ (∑ i, diagonal i) +
        ∑ i, ∑ j ∈ (Finset.univ.erase i), cross i j := hquadratic
    _ ≤ d * ∑ i, energy i +
        ((ell : ℝ) - 1) * ∑ i, energy i := add_le_add hdiagSum hcrossSum
    _ = (d + (ell : ℝ) - 1) * ∑ i, energy i := by ring

/-- Compression is norm-decreasing at the scalar quadratic-form level.

This theorem intentionally assumes the compression comparison `hard ≤ bosonic`.
In the sparse-Fock proof that premise is supplied by the positive bosonic dilation;
formalizing the Fock-space isometry and positivity is outside this module. -/
theorem compressed_lightSector_bound
    {d ell hard bosonic energy : ℝ}
    (hcompression : hard ≤ bosonic)
    (hbosonic : bosonic ≤ (d + ell - 1) * energy) :
    hard ≤ (d + ell - 1) * energy :=
  hcompression.trans hbosonic

end LightSectorAbstract

end SparseFock


