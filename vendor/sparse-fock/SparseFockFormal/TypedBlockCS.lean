import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Typed block Cauchy--Schwarz

This file proves the operator inequality used at TeX lines 930--989.  The
middle space is the genuine Hilbert direct sum (`PiLp 2`), not a product with
the supremum norm.
-/

open scoped NNReal ENNReal InnerProduct
open WithLp

namespace SparseFock.TypedBlockCS

noncomputable section

variable {R X Y Z : Type*}
variable [Fintype R]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The column operator `x ↦ (a r x)ₙ` into the Hilbert direct sum. -/
def blockAnalysisLinear (a : R → X →L[ℝ] Y) :
    X →ₗ[ℝ] PiLp 2 (fun _ : R ↦ Y) where
  toFun x := toLp 2 (fun r ↦ a r x)
  map_add' x y := by
    ext r
    simp
  map_smul' c x := by
    ext r
    simp

/-- The continuous column operator.  Continuity follows from finite
dimensionality of its domain. -/
def blockAnalysis (a : R → X →L[ℝ] Y) :
    X →L[ℝ] PiLp 2 (fun _ : R ↦ Y) :=
  ⟨blockAnalysisLinear a, (blockAnalysisLinear a).continuous_of_finiteDimensional⟩

@[simp]
theorem blockAnalysis_apply (a : R → X →L[ℝ] Y) (x : X) (r : R) :
    blockAnalysis a x r = a r x :=
  rfl

/-- The row operator `(yₙ) ↦ ∑ r, b r (y r)` from the Hilbert direct sum. -/
def blockSynthesisLinear (b : R → Y →L[ℝ] Z) :
    PiLp 2 (fun _ : R ↦ Y) →ₗ[ℝ] Z where
  toFun y := ∑ r, b r (y r)
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.smul_sum]

/-- The continuous row operator. -/
def blockSynthesis (b : R → Y →L[ℝ] Z) :
    PiLp 2 (fun _ : R ↦ Y) →L[ℝ] Z :=
  ⟨blockSynthesisLinear b,
    (blockSynthesisLinear b).continuous_of_finiteDimensional⟩

@[simp]
theorem blockSynthesis_apply (b : R → Y →L[ℝ] Z)
    (y : PiLp 2 (fun _ : R ↦ Y)) :
    blockSynthesis b y = ∑ r, b r (y r) :=
  rfl

theorem block_comp_eq (a : R → X →L[ℝ] Y) (b : R → Y →L[ℝ] Z) :
    blockSynthesis b ∘L blockAnalysis a = ∑ r, b r ∘L a r := by
  ext x
  change (∑ r, b r (a r x)) = _
  simp

theorem blockAnalysis_adjoint (a : R → X →L[ℝ] Y) :
    (blockAnalysis a)† = blockSynthesis (fun r ↦ (a r)†) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (blockSynthesis (fun r ↦ (a r)†)) (blockAnalysis a)).2
  intro y x
  simp only [blockSynthesis_apply, blockAnalysis_apply, PiLp.inner_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro r _
  exact ContinuousLinearMap.adjoint_inner_left (a r) x (y r)

theorem blockSynthesis_adjoint (b : R → Y →L[ℝ] Z) :
    (blockSynthesis b)† = blockAnalysis (fun r ↦ (b r)†) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (blockAnalysis (fun r ↦ (b r)†)) (blockSynthesis b)).2
  intro z y
  simp only [blockAnalysis_apply, blockSynthesis_apply, PiLp.inner_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact ContinuousLinearMap.adjoint_inner_left (b r) (y r) z

theorem analysis_gram_eq (a : R → X →L[ℝ] Y) :
    (blockAnalysis a)† ∘L blockAnalysis a = ∑ r, (a r)† ∘L a r := by
  rw [blockAnalysis_adjoint]
  exact block_comp_eq a (fun r ↦ (a r)†)

theorem synthesis_cogram_eq (b : R → Y →L[ℝ] Z) :
    blockSynthesis b ∘L (blockSynthesis b)† = ∑ r, b r ∘L (b r)† := by
  rw [blockSynthesis_adjoint]
  exact block_comp_eq (fun r ↦ (b r)†) b

/-- Typed block Cauchy--Schwarz without writing the projections explicitly:
the maps `a r` and `b r` may already contain the domain, middle, and range
projections.  This is the exact row/column-operator inequality. -/
theorem typed_block_cs (a : R → X →L[ℝ] Y) (b : R → Y →L[ℝ] Z) :
    ‖∑ r, b r ∘L a r‖ ^ 2 ≤
      ‖∑ r, (a r)† ∘L a r‖ * ‖∑ r, b r ∘L (b r)†‖ := by
  let A := blockAnalysis a
  let B := blockSynthesis b
  have hcomp : B ∘L A = ∑ r, b r ∘L a r := block_comp_eq a b
  have hA : A† ∘L A = ∑ r, (a r)† ∘L a r := analysis_gram_eq a
  have hB : B ∘L B† = ∑ r, b r ∘L (b r)† := synthesis_cogram_eq b
  have hnorm : ‖B ∘L A‖ ≤ ‖B‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le B A
  calc
    ‖∑ r, b r ∘L a r‖ ^ 2 = ‖B ∘L A‖ ^ 2 := by rw [hcomp]
    _ ≤ (‖B‖ * ‖A‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (‖A‖ * ‖A‖) * (‖B‖ * ‖B‖) := by ring
    _ = ‖A† ∘L A‖ * ‖B ∘L B†‖ := by
      rw [ContinuousLinearMap.norm_adjoint_comp_self]
      have hBadj := ContinuousLinearMap.norm_adjoint_comp_self (B†)
      simp only [ContinuousLinearMap.adjoint_adjoint] at hBadj
      rw [hBadj, LinearIsometryEquiv.norm_map]
    _ = ‖∑ r, (a r)† ∘L a r‖ * ‖∑ r, b r ∘L (b r)†‖ := by rw [hA, hB]

/-- The displayed projection form of TeX equation (typed-block-CS).  The six
hypotheses say exactly that `E`, `F`, and `G` are orthogonal projections:
self-adjoint idempotents on their respective Hilbert spaces. -/
theorem typed_block_cs_with_projections
    (E : X →L[ℝ] X) (F : Y →L[ℝ] Y) (G : Z →L[ℝ] Z)
    (hEadj : E† = E) (hFadj : F† = F) (hGadj : G† = G)
    (hEid : E ∘L E = E) (hFid : F ∘L F = F) (hGid : G ∘L G = G)
    (a : R → X →L[ℝ] Y) (b : R → Y →L[ℝ] Z) :
    ‖G ∘L (∑ r, (b r ∘L F) ∘L a r) ∘L E‖ ^ 2 ≤
      ‖E ∘L (∑ r, ((a r)† ∘L F) ∘L a r) ∘L E‖ *
      ‖G ∘L (∑ r, (b r ∘L F) ∘L (b r)†) ∘L G‖ := by
  let ap : R → X →L[ℝ] Y := fun r ↦ (F ∘L a r) ∘L E
  let bp : R → Y →L[ℝ] Z := fun r ↦ (G ∘L b r) ∘L F
  have hmain := typed_block_cs ap bp
  have hleft :
      ∑ r, bp r ∘L ap r = G ∘L (∑ r, (b r ∘L F) ∘L a r) ∘L E := by
    ext x
    simp only [ap, bp, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    change (F ∘L F) (a r (E x)) = F (a r (E x))
    rw [hFid]
  have hrightA :
      ∑ r, (ap r)† ∘L ap r =
        E ∘L (∑ r, ((a r)† ∘L F) ∘L a r) ∘L E := by
    ext x
    simp only [ap, ContinuousLinearMap.adjoint_comp, hEadj, hFadj,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    change (F ∘L F) (a r (E x)) = F (a r (E x))
    rw [hFid]
  have hrightB :
      ∑ r, bp r ∘L (bp r)† =
        G ∘L (∑ r, (b r ∘L F) ∘L (b r)†) ∘L G := by
    ext z
    simp only [bp, ContinuousLinearMap.adjoint_comp, hGadj, hFadj,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    change (F ∘L F) (((b r)†) (G z)) = F (((b r)†) (G z))
    rw [hFid]
  rw [hleft, hrightA, hrightB] at hmain
  exact hmain

end

end SparseFock.TypedBlockCS
