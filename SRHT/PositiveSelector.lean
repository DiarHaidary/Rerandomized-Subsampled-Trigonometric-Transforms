import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-! Positive hard-core selector creation.  All norms are genuine Hilbert
operator norms; effects need not commute. -/

open scoped BigOperators InnerProduct

namespace SRHT.PositiveSelector
noncomputable section

variable {J H : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

local notation "⟪" x ", " y "⟫" => @inner ℝ H _ x y

/-- The row version of weighted Cauchy--Schwarz.  Its constant is the norm
of the sum of the positive effects, with no number-of-summands loss. -/
theorem positive_row_energy (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive) (T : Finset J) (f : J → H)
    {L : ℝ} (hL : ‖∑ j ∈ T, A j‖ ≤ L) :
    ‖∑ j ∈ T, A j (f j)‖ ^ 2 ≤
      L * ∑ j ∈ T, ⟪f j, A j (f j)⟫ := by
  let g : H := ∑ j ∈ T, A j (f j)
  let E : ℝ := ∑ j ∈ T, ⟪f j, A j (f j)⟫
  let a : ℝ := ∑ j ∈ T, ⟪g, A j g⟫
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => (hA j).inner_nonneg_right _
  have hg : (∑ j ∈ T, ⟪g, A j (f j)⟫) = ‖g‖ ^ 2 := by
    rw [← inner_sum]
    exact real_inner_self_eq_norm_sq _
  have hs : ∀ j, ⟪f j, A j g⟫ = ⟪g, A j (f j)⟫ := by
    intro j
    rw [← (hA j).inner_left_eq_inner_right, real_inner_comm]
  have hquad : ∀ t : ℝ, 0 ≤ a * (t * t) + (-2 * ‖g‖ ^ 2) * t + E := by
    intro t
    have hp := Finset.sum_nonneg (s := T)
      (fun j _ => (hA j).inner_nonneg_right (f j - t • g))
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real, hs] at hp
    simp only [mul_sub] at hp
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul] at hp
    rw [hg] at hp
    dsimp [a, E]
    nlinarith
  have hd := discrim_le_zero hquad
  have ha : a ≤ L * ‖g‖ ^ 2 := by
    have he : a = ⟪g, (∑ j ∈ T, A j) g⟫ := by
      simp [a, inner_sum]
    rw [he]
    calc
      ⟪g, (∑ j ∈ T, A j) g⟫ ≤ ‖g‖ * ‖(∑ j ∈ T, A j) g‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * (‖∑ j ∈ T, A j‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖g‖ * (L * ‖g‖) := by gcongr
      _ = L * ‖g‖ ^ 2 := by ring
  have hprod := mul_le_mul_of_nonneg_right ha hE
  dsimp [discrim] at hd
  change ‖g‖ ^ 2 ≤ L * E
  by_cases hz : ‖g‖ ^ 2 = 0
  · rw [hz]
    exact mul_nonneg ((norm_nonneg _).trans hL) hE
  · have hp : 0 < ‖g‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    nlinarith

/-- Erasing an occupied site is injective on sets containing that site.
Thus an input energy is charged at most once per site. -/
theorem erase_sum_le (j : J) (e : Finset J → ℝ) (he : ∀ S, 0 ≤ e S) :
    (∑ T : Finset J, ∑ k ∈ T, if k = j then e (T.erase j) else 0) ≤ ∑ S, e S := by
  classical
  let D : Finset (Finset J) := Finset.univ.filter (fun T => j ∈ T)
  have hinj : Set.InjOn (fun T : Finset J => T.erase j) D := by
    intro T hT S hS h
    have hjT : j ∈ T := (Finset.mem_filter.mp hT).2
    have hjS : j ∈ S := (Finset.mem_filter.mp hS).2
    have hh := congrArg (insert j) h
    simpa [Finset.insert_erase hjT, Finset.insert_erase hjS] using hh
  calc
    (∑ T : Finset J, ∑ k ∈ T, if k = j then e (T.erase j) else 0) =
        ∑ T ∈ D, e (T.erase j) := by
      simp [D, Finset.sum_filter]
    _ = ∑ S ∈ D.image (fun T => T.erase j), e S := (Finset.sum_image hinj).symm
    _ ≤ ∑ S, e S := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun S _ _ => he S)

/-- The genuine selector Hilbert space, including a zero extension above q. -/
abbrev Space (J H : Type*) [Fintype J] := PiLp 2 (fun _ : Finset J => H)

def creationLinear (A : J → H →L[ℝ] H) (q : ℕ) :
    Space J H →ₗ[ℝ] Space J H where
  toFun f := WithLp.toLp 2 fun T =>
    if T.card ≤ q then ∑ j ∈ T, A j (f (T.erase j)) else 0
  map_add' f g := by
    ext T
    by_cases h : T.card ≤ q <;> simp [h, Finset.sum_add_distrib]
  map_smul' c f := by
    ext T
    by_cases h : T.card ≤ q <;> simp [h, Finset.smul_sum]

def creation (A : J → H →L[ℝ] H) (q : ℕ) :
    Space J H →L[ℝ] Space J H :=
  ⟨creationLinear A q, (creationLinear A q).continuous_of_finiteDimensional⟩

@[simp] theorem creation_apply (A : J → H →L[ℝ] H) (q : ℕ)
    (f : Space J H) (T : Finset J) :
    creation A q f T =
      if T.card ≤ q then ∑ j ∈ T, A j (f (T.erase j)) else 0 := rfl

/-- Full creation energy estimate.  It has no multiplicative dependence on
the selector cutoff q. -/
theorem creation_energy_of_sum_norm (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive)
    (hsum : ‖∑ j, A j‖ ≤ 1)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L)
    (f : Space J H) :
    ‖creation A q f‖ ^ 2 ≤ L * ‖f‖ ^ 2 := by
  classical
  have hpoint (T : Finset J) : ‖creation A q f T‖ ^ 2 ≤
      L * ∑ j ∈ T, ⟪f (T.erase j), A j (f (T.erase j))⟫ := by
    rw [creation_apply]
    split_ifs with h
    · exact positive_row_energy A hA T (fun j => f (T.erase j)) (hsub T h)
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg hL (Finset.sum_nonneg fun j _ => (hA j).inner_nonneg_right _)
  have hreindex :
      (∑ T : Finset J, ∑ j ∈ T, ⟪f (T.erase j), A j (f (T.erase j))⟫) ≤
        ∑ S : Finset J, ‖f S‖ ^ 2 := by
    calc
      _ = ∑ j : J, ∑ T : Finset J,
          ∑ k ∈ T, if k = j then ⟪f (T.erase j), A j (f (T.erase j))⟫ else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro T _
        rw [Finset.sum_comm]
        simp
      _ ≤ ∑ j : J, ∑ S : Finset J, ⟪f S, A j (f S)⟫ := by
        apply Finset.sum_le_sum
        intro j _
        exact erase_sum_le j _ (fun S => (hA j).inner_nonneg_right _)
      _ ≤ ∑ S : Finset J, ‖f S‖ ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro S _
        rw [← inner_sum, ← ContinuousLinearMap.sum_apply]
        calc
          _ ≤ ‖f S‖ * ‖(∑ j, A j) (f S)‖ := real_inner_le_norm _ _
          _ ≤ ‖f S‖ * (‖∑ j, A j‖ * ‖f S‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖f S‖ * (1 * ‖f S‖) := by gcongr
          _ = ‖f S‖ ^ 2 := by ring
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ T : Finset J, L * ∑ j ∈ T, ⟪f (T.erase j), A j (f (T.erase j))⟫ :=
      Finset.sum_le_sum fun T _ => hpoint T
    _ = L * ∑ T : Finset J, ∑ j ∈ T, ⟪f (T.erase j), A j (f (T.erase j))⟫ := by
      rw [Finset.mul_sum]
    _ ≤ L * ∑ S : Finset J, ‖f S‖ ^ 2 := mul_le_mul_of_nonneg_left hreindex hL

theorem creation_energy (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive)
    (hsum : ∑ j, A j = ContinuousLinearMap.id ℝ H)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L)
    (f : Space J H) : ‖creation A q f‖ ^ 2 ≤ L * ‖f‖ ^ 2 := by
  apply creation_energy_of_sum_norm A hA _ q hL hsub f
  rw [hsum]
  exact ContinuousLinearMap.norm_id_le

theorem norm_creation_le_of_sum_norm (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive) (hsum : ‖∑ j, A j‖ ≤ 1)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L) :
    ‖creation A q‖ ≤ Real.sqrt L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  have h := creation_energy_of_sum_norm A hA hsum q hL hsub f
  have hs := Real.sq_sqrt hL
  have hp : 0 ≤ Real.sqrt L * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (creation A q f)]

/-- Dimension-free positive-selector creation bound in the actual L2 norm. -/
theorem norm_creation_le (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive)
    (hsum : ∑ j, A j = ContinuousLinearMap.id ℝ H)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L) :
    ‖creation A q‖ ≤ Real.sqrt L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  have h := creation_energy A hA hsum q hL hsub f
  have hs := Real.sq_sqrt hL
  have hp : 0 ≤ Real.sqrt L * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (creation A q f)]

def occupancyLinear (A : J → H →L[ℝ] H) (q : ℕ) :
    Space J H →ₗ[ℝ] Space J H where
  toFun f := WithLp.toLp 2 fun T =>
    if T.card ≤ q then (∑ j ∈ T, A j) (f T) else 0
  map_add' f g := by
    ext T
    by_cases h : T.card ≤ q <;> simp [h, Finset.sum_add_distrib]
  map_smul' c f := by
    ext T
    by_cases h : T.card ≤ q <;> simp [h]

def occupancy (A : J → H →L[ℝ] H) (q : ℕ) :
    Space J H →L[ℝ] Space J H :=
  ⟨occupancyLinear A q, (occupancyLinear A q).continuous_of_finiteDimensional⟩

@[simp] theorem occupancy_apply (A : J → H →L[ℝ] H) (q : ℕ)
    (f : Space J H) (T : Finset J) :
    occupancy A q f T =
      if T.card ≤ q then (∑ j ∈ T, A j) (f T) else 0 := rfl

theorem norm_occupancy_le (A : J → H →L[ℝ] H) (q : ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L) :
    ‖occupancy A q‖ ≤ L := by
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro f
  have he : ‖occupancy A q f‖ ^ 2 ≤ L ^ 2 * ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T _
    have hp : ‖occupancy A q f T‖ ≤ L * ‖f T‖ := by
      rw [occupancy_apply]
      split_ifs with h
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hsub T h) (norm_nonneg _))
      · simpa using mul_nonneg hL (norm_nonneg (f T))
    nlinarith [norm_nonneg (occupancy A q f T), norm_nonneg (f T)]
  have hp : 0 ≤ L * ‖f‖ := mul_nonneg hL (norm_nonneg _)
  nlinarith [norm_nonneg (occupancy A q f)]

/-- Hard-core annihilation is the Hilbert adjoint of creation. -/
def annihilation (A : J → H →L[ℝ] H) (q : ℕ) :
    Space J H →L[ℝ] Space J H := (creation A q).adjoint

theorem norm_annihilation_le (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive)
    (hsum : ∑ j, A j = ContinuousLinearMap.id ℝ H)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L) :
    ‖annihilation A q‖ ≤ Real.sqrt L := by
  rw [annihilation, LinearIsometryEquiv.norm_map]
  exact norm_creation_le A hA hsum q hL hsub

/-- Compressed centered Bernoulli multiplication in its orthonormal subset
basis.  σ is the creation/annihilation coefficient and τ the occupied-site
diagonal coefficient. -/
def bernoulliOperator (A : J → H →L[ℝ] H) (q : ℕ) (σ τ : ℝ) :
    Space J H →L[ℝ] Space J H :=
  σ • (creation A q + annihilation A q) + τ • occupancy A q

theorem norm_bernoulliOperator_le (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive)
    (hsum : ∑ j, A j = ContinuousLinearMap.id ℝ H)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L)
    (σ τ : ℝ) :
    ‖bernoulliOperator A q σ τ‖ ≤
      2 * |σ| * Real.sqrt L + |τ| * L := by
  have hc := norm_creation_le A hA hsum q hL hsub
  have ha := norm_annihilation_le A hA hsum q hL hsub
  have hn := norm_occupancy_le A q hL hsub
  change ‖σ • (creation A q + annihilation A q) + τ • occupancy A q‖ ≤ _
  calc
    _ ≤ ‖σ • (creation A q + annihilation A q)‖ + ‖τ • occupancy A q‖ :=
      norm_add_le (σ • (creation A q + annihilation A q)) (τ • occupancy A q)
    _ ≤ |σ| * ‖creation A q + annihilation A q‖ + |τ| * ‖occupancy A q‖ := by
      simpa only [Real.norm_eq_abs] using add_le_add
        (ContinuousLinearMap.opNorm_smul_le σ (creation A q + annihilation A q))
        (ContinuousLinearMap.opNorm_smul_le τ (occupancy A q))
    _ ≤ |σ| * (‖creation A q‖ + ‖annihilation A q‖) + |τ| * ‖occupancy A q‖ := by
      gcongr
      exact norm_add_le (creation A q) (annihilation A q)
    _ ≤ |σ| * (Real.sqrt L + Real.sqrt L) + |τ| * L := by gcongr
    _ = _ := by ring

/-- Contraction-sum version, allowing effects obtained by compression to
an ambient sign cutoff. -/
theorem norm_bernoulliOperator_le_of_sum_norm (A : J → H →L[ℝ] H)
    (hA : ∀ j, (A j).IsPositive) (hsum : ‖∑ j, A j‖ ≤ 1)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L)
    (σ τ : ℝ) :
    ‖bernoulliOperator A q σ τ‖ ≤ 2 * |σ| * Real.sqrt L + |τ| * L := by
  have hc := norm_creation_le_of_sum_norm A hA hsum q hL hsub
  have ha : ‖annihilation A q‖ ≤ Real.sqrt L := by
    rw [annihilation, LinearIsometryEquiv.norm_map]
    exact hc
  have hn := norm_occupancy_le A q hL hsub
  change ‖σ • (creation A q + annihilation A q) + τ • occupancy A q‖ ≤ _
  calc
    _ ≤ ‖σ • (creation A q + annihilation A q)‖ + ‖τ • occupancy A q‖ :=
      norm_add_le (σ • (creation A q + annihilation A q)) (τ • occupancy A q)
    _ ≤ |σ| * ‖creation A q + annihilation A q‖ + |τ| * ‖occupancy A q‖ := by
      simpa only [Real.norm_eq_abs] using add_le_add
        (ContinuousLinearMap.opNorm_smul_le σ (creation A q + annihilation A q))
        (ContinuousLinearMap.opNorm_smul_le τ (occupancy A q))
    _ ≤ |σ| * (‖creation A q‖ + ‖annihilation A q‖) + |τ| * ‖occupancy A q‖ := by
      gcongr
      exact norm_add_le (creation A q) (annihilation A q)
    _ ≤ |σ| * (Real.sqrt L + Real.sqrt L) + |τ| * L := by gcongr
    _ = _ := by ring

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped Matrix.Norms.L2Operator

/-- Positive semidefinite matrices give positive operators for the actual
Euclidean Hilbert structure. -/
theorem matrix_effect_positive (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).2
  constructor
  · change star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
    rw [← map_star]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) hA.isHermitian
  · intro x
    rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
    simpa using hA.dotProduct_mulVec_nonneg (WithLp.ofLp x)

/-- Matrix-input form of the complete positive-selector estimate.  The
subset bound and every norm in this statement are L2 operator norms. -/
theorem matrix_norm_bernoulliOperator_le (A : J → Matrix ι ι ℝ)
    (hA : ∀ j, (A j).PosSemidef) (hsum : ∑ j, A j = 1)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L)
    (σ τ : ℝ) :
    ‖bernoulliOperator (fun j => Matrix.toEuclideanCLM (𝕜 := ℝ) (A j)) q σ τ‖ ≤
      2 * |σ| * Real.sqrt L + |τ| * L := by
  apply norm_bernoulliOperator_le _ (fun j => matrix_effect_positive _ (hA j)) _ q hL _ σ τ
  · rw [← map_sum, hsum, map_one]
    rfl
  · intro T hT
    rw [← map_sum, Matrix.l2_opNorm_toEuclideanCLM]
    exact hsub T hT

theorem matrix_norm_bernoulliOperator_le_of_sum_norm (A : J → Matrix ι ι ℝ)
    (hA : ∀ j, (A j).PosSemidef) (hsum : ‖∑ j, A j‖ ≤ 1)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L)
    (σ τ : ℝ) :
    ‖bernoulliOperator (fun j => Matrix.toEuclideanCLM (𝕜 := ℝ) (A j)) q σ τ‖ ≤
      2 * |σ| * Real.sqrt L + |τ| * L := by
  apply norm_bernoulliOperator_le_of_sum_norm _
    (fun j => matrix_effect_positive _ (hA j)) _ q hL _ σ τ
  · rwa [← map_sum, Matrix.l2_opNorm_toEuclideanCLM]
  · intro T hT
    rw [← map_sum, Matrix.l2_opNorm_toEuclideanCLM]
    exact hsub T hT

end Matrix

end
end SRHT.PositiveSelector
