import SparseFockFormal.VacuumMoment
import SparseFockFormal.GlobalBands
import SparseFockFormal.FiniteHilbert
import Mathlib.Tactic

/-!
# Exact passage from the iid multiplication operator to concrete grade bands

This module closes the algebraic seam between the product-probability
realization in `VacuumMoment` and the physical, distinct-site bands in
`GlobalBands`.  In particular, the global operator in the vacuum moment is
literally the normalized sum of the three concrete bands.
-/

namespace SparseFock.ConcreteLadder

open scoped BigOperators
open ParsevalFrame ProductFock VacuumMoment
open LocalOperator FiniteOperator ExternalOperator GlobalBands
open FiniteHilbert

noncomputable section

variable {m n d b : ℕ}

/-- Kernels lifted at two distinct sites multiply to the simultaneous
two-site kernel. -/
theorem siteKernel_mul_siteKernel_of_ne
    (s t : Site m n) (hst : s ≠ t) (A B : LocalOperator.Op) :
    siteKernel s A * siteKernel t B = pairKernel s t A B := by
  classical
  ext out inp
  by_cases hoff : agreesOutsidePair s t out inp
  · let mid : Pattern m n := Function.update out s (inp s)
    rw [Matrix.mul_apply, Finset.sum_eq_single mid]
    · have hs : agreesOutsideSite s out mid := by
        intro x hxs
        simp [mid, hxs]
      have ht : agreesOutsideSite t mid inp := by
        intro x hxt
        by_cases hxs : x = s
        · subst x
          simp [mid]
        · simp [mid, hxs, hoff x hxs hxt]
      have hmids : mid s = inp s := by simp [mid]
      have hmidt : mid t = out t := by
        simp [mid, Ne.symm hst]
      simp [siteKernel, pairKernel, hoff, hs, ht, hmids, hmidt]
    · intro other _ hother
      by_cases hs : agreesOutsideSite s out other
      · by_cases ht : agreesOutsideSite t other inp
        · have heq : other = mid := by
            funext x
            by_cases hxs : x = s
            · subst x
              have hst' : s ≠ t := hst
              simpa [mid] using ht s hst'
            · have hx := hs x hxs
              simpa [mid, hxs] using hx.symm
          exact (hother heq).elim
        · simp [siteKernel, ht]
      · simp [siteKernel, hs]
    · intro hnot
      exact (hnot (Finset.mem_univ mid)).elim
  · rw [Matrix.mul_apply]
    simp only [pairKernel, hoff, if_false]
    apply (Finset.sum_eq_zero fun mid _ ↦ ?_)
    by_cases hs : agreesOutsideSite s out mid
    · by_cases ht : agreesOutsideSite t mid inp
      · exfalso
        apply hoff
        intro x hxs hxt
        exact (hs x hxs).trans (ht x hxt)
      · simp [siteKernel, pairKernel, hoff, ht]
    · simp [siteKernel, pairKernel, hoff, hs]

/-- At distinct columns in one row, the product appearing in the product-L2
model is exactly the physical pair kernel used by the band inventory. -/
theorem siteJacobiProduct_eq_pairKernel
    (r : Fin m) (i j : Fin n) (hij : i ≠ j) (ρ : ℝ) :
    siteKernel (r, i) (jacobi ρ) * siteKernel (r, j) (jacobi ρ) =
      pairKernel (r, i) (r, j) (jacobi ρ) (jacobi ρ) := by
  apply siteKernel_mul_siteKernel_of_ne
  intro h
  exact hij (congrArg Prod.snd h)

/-- The global Jacobi operator from the exact vacuum moment is the normalized
physical multiplication matrix from `GlobalBands`. -/
theorem globalJacobiOperator_eq_smul_rawMultiplication
    (F : Frame n d) :
    globalJacobiOperator (m := m) b F =
      (1 / (m : ℝ)) • rawMultiplication m (fun i a ↦ F.u i a)
        (Real.sqrt ((b : ℝ) - 1)) := by
  classical
  simp only [globalJacobiOperator]
  unfold rawMultiplication orderedJacobiTerm
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
  rw [siteJacobiProduct_eq_pairKernel r i j hij]
  ext out inp
  rfl

/-- One normalized concrete grade band. -/
def normalizedBand (m : ℕ) (F : Frame n d) (b : ℕ)
    (δ : BandInventory.Shift) : FullOp d m n :=
  (1 / (m : ℝ)) •
    GlobalBands.band m (fun i a ↦ F.u i a)
      (Real.sqrt ((b : ℝ) - 1)) δ

theorem normalizedBand_homogeneous (F : Frame n d) (b : ℕ)
    (δ : BandInventory.Shift) :
  ExternalOperator.Homogeneous δ.degree (normalizedBand m F b δ) := by
  apply FiniteHilbert.homogeneous_smul
  exact GlobalBands.band_homogeneous
    (m := m) (fun i a ↦ F.u i a) (Real.sqrt ((b : ℝ) - 1)) δ

@[simp] theorem vacuumPattern_grade :
    (vacuumPattern m n).grade = 0 := by
  classical
  simp [vacuumPattern, Pattern.grade, Level.weight]

/-- Natural output grade of one band, with `none` for an impossible downward
step from grade zero or one. -/
def nextGrade : BandInventory.Shift → ℕ → Option ℕ
  | .plus, nu => some (nu + 2)
  | .zero, nu => some nu
  | .minus, nu => if 2 ≤ nu then some (nu - 2) else none

theorem nextGrade_compatible {delta : BandInventory.Shift} {nu mu : ℕ}
    (hnext : nextGrade delta nu = some mu) :
    (mu : ℤ) = (nu : ℤ) + delta.degree := by
  cases delta with
  | plus =>
      simp [nextGrade] at hnext
      subst mu
      simp [BandInventory.Shift.degree]
  | zero =>
      simp [nextGrade] at hnext
      subst mu
      simp [BandInventory.Shift.degree]
  | minus =>
      simp only [nextGrade] at hnext
      split at hnext
      case isTrue htwo =>
        simp only [Option.some.injEq] at hnext
        subst mu
        simp [BandInventory.Shift.degree]
        omega
      case isFalse htwo => simp at hnext

theorem nextGrade_none_impossible {delta : BandInventory.Shift} {nu : ℕ}
    (hnext : nextGrade delta nu = none) :
    ∀ mu : ℕ, (mu : ℤ) ≠ (nu : ℤ) + delta.degree := by
  cases delta with
  | plus => simp [nextGrade] at hnext
  | zero => simp [nextGrade] at hnext
  | minus =>
      simp only [nextGrade] at hnext
      split at hnext
      case isTrue htwo => simp at hnext
      case isFalse htwo =>
        intro mu hmu
        simp [BandInventory.Shift.degree] at hmu
        omega

/-- Exact projection insertion for one concrete band step. -/
theorem normalizedBand_output_projection
    (F : Frame n d) (b : ℕ) (delta : BandInventory.Shift)
    (nu mu : ℕ) (hnext : nextGrade delta nu = some mu) :
    gradeProjection (d := d) mu * normalizedBand m F b delta *
        gradeProjection nu =
      normalizedBand m F b delta * gradeProjection nu := by
  apply FiniteHilbert.output_projection_of_homogeneous
    (normalizedBand_homogeneous F b delta)
  exact nextGrade_compatible hnext

/-- An impossible downward band vanishes on the input grade. -/
theorem normalizedBand_vanishes_of_nextGrade_none
    (F : Frame n d) (b : ℕ) (delta : BandInventory.Shift)
    (nu : ℕ) (hnext : nextGrade delta nu = none) :
    normalizedBand m F b delta * gradeProjection (d := d) nu = 0 := by
  apply FiniteHilbert.input_grade_vanishes_of_no_output
    (normalizedBand_homogeneous F b delta) nu
  exact nextGrade_none_impossible hnext

/-- The multiplication operator in the exact iid vacuum moment is literally
the sum of its three normalized physical grade bands. -/
theorem multiplicationOperator_eq_sum_normalizedBands
    (hb : 1 < b) (F : Frame n d) :
    multiplicationOperator (m := m) b hb F =
      ∑ δ : BandInventory.Shift, normalizedBand m F b δ := by
  rw [multiplicationOperator_eq_globalJacobi hb F,
    globalJacobiOperator_eq_smul_rawMultiplication]
  rw [GlobalBands.rawMultiplication_eq_sum_bands]
  simp [normalizedBand, Finset.smul_sum]

/-- Exact vacuum identity with the concrete three-band sum substituted. -/
theorem vacuum_moment_identity_bands
    (hb : 1 < b) (F : Frame n d) (k : ℕ) :
    (∑ a : Fin d,
      ((∑ δ : BandInventory.Shift, normalizedBand m F b δ) ^ k)
        (a, vacuumPattern m n) (a, vacuumPattern m n)) =
      (ProductFock.iidLaw b hb m n).expect
        (fun omega ↦ Matrix.trace ((iidGramError b F omega) ^ k)) := by
  rw [← multiplicationOperator_eq_sum_normalizedBands hb F]
  exact vacuum_moment_identity hb F k

end

end SparseFock.ConcreteLadder
