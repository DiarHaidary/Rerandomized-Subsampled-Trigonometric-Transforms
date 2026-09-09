import SRHT.PositiveSelector
import SRHT.HardCore
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Concrete matrix representation of the positive-selector operator.
The matrix index is `ι × Finset J`: the effect coordinate precedes the
selector subset. -/

namespace SRHT.SelectorRepresentation
open SRHT.PositiveSelector
open scoped BigOperators InnerProduct Matrix.Norms.L2Operator
noncomputable section

private theorem starAlgEquiv_map_star {X Y : Type*}
    [Add X] [Mul X] [SMul ℝ X] [Star X]
    [Add Y] [Mul Y] [SMul ℝ Y] [Star Y]
    (e : X ≃⋆ₐ[ℝ] Y) (x : X) : e (star x) = star (e x) := e.map_star' x

variable {J ι : Type*} [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]

def regroup : EuclideanSpace ℝ (ι × Finset J) ≃ₗᵢ[ℝ] Space J (EuclideanSpace ℝ ι) where
  toFun f := WithLp.toLp 2 fun S => WithLp.toLp 2 fun i => f (i,S)
  invFun f := WithLp.toLp 2 fun z => f z.2 z.1
  left_inv f := by ext z; rfl
  right_inv f := by ext S i; rfl
  map_add' f g := by ext S i; rfl
  map_smul' c f := by ext S i; rfl
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [PiLp.norm_sq_eq_of_L2]
    change (∑ S : Finset J, ∑ i : ι, ‖f (i,S)‖ ^ 2) = ∑ z : ι × Finset J, ‖f z‖ ^ 2
    rw [Fintype.sum_prod_type, Finset.sum_comm]

@[simp] theorem regroup_apply (f : EuclideanSpace ℝ (ι × Finset J))
    (S : Finset J) (i : ι) : regroup f S i = f (i,S) := rfl

@[simp] theorem regroup_symm_apply (f : Space J (EuclideanSpace ℝ ι))
    (i : ι) (S : Finset J) : regroup.symm f (i,S) = f S i := rfl

/-- The concrete star algebra isomorphism between selector Hilbert operators
and matrices on the coordinate/subset product basis. -/
def matrixRepresentation :
    (Space J (EuclideanSpace ℝ ι) →L[ℝ] Space J (EuclideanSpace ℝ ι)) ≃⋆ₐ[ℝ]
      Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  regroup.symm.conjStarAlgEquiv.trans (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm

theorem represented_apply (K : Space J (EuclideanSpace ℝ ι) →L[ℝ] Space J (EuclideanSpace ℝ ι))
    (f : EuclideanSpace ℝ (ι × Finset J)) (i : ι) (S : Finset J) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixRepresentation K) f (i,S) =
      K (regroup f) S i := by
  change (Matrix.toEuclideanCLM (𝕜 := ℝ)
    ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (regroup.symm.conjStarAlgEquiv K))) f (i,S) = _
  rw [StarAlgEquiv.apply_symm_apply]
  rfl

theorem norm_matrixRepresentation (K : Space J (EuclideanSpace ℝ ι) →L[ℝ] Space J (EuclideanSpace ℝ ι)) :
    ‖matrixRepresentation K‖ = ‖K‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  change ‖Matrix.toEuclideanCLM (n := ι × Finset J) (𝕜 := ℝ)
    ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (regroup.symm.conjStarAlgEquiv K))‖ = _
  rw [StarAlgEquiv.apply_symm_apply]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖regroup.symm (K (regroup f))‖ ≤ ‖K‖ * ‖f‖
    rw [LinearIsometryEquiv.norm_map]
    simpa only [LinearIsometryEquiv.norm_map] using ContinuousLinearMap.le_opNorm K (regroup f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have h := ContinuousLinearMap.le_opNorm (regroup.symm.conjStarAlgEquiv K) (regroup.symm f)
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.norm_map] using h

/-- Matrix entry obtained by applying the Hilbert operator to one coordinate
of one selector subset. -/
theorem matrixRepresentation_entry
    (K : Space J (EuclideanSpace ℝ ι) →L[ℝ] Space J (EuclideanSpace ℝ ι))
    (a b : ι) (S T : Finset J) :
    matrixRepresentation K (a,S) (b,T) =
      K (regroup (EuclideanSpace.single (b,T) 1)) S a := by
  have h := represented_apply K (EuclideanSpace.single (b,T) 1) a S
  simpa only [Matrix.toEuclideanCLM_toLp, EuclideanSpace.single,
    PiLp.single, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply] using h

def effect (A : J → Matrix ι ι ℝ) (j : J) := Matrix.toEuclideanCLM (𝕜 := ℝ) (A j)

def creationMatrix (A : J → Matrix ι ι ℝ) (q : ℕ) :
    Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  matrixRepresentation (creation (effect A) q)

def annihilationMatrix (A : J → Matrix ι ι ℝ) (q : ℕ) :
    Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  matrixRepresentation (annihilation (effect A) q)

def occupancyMatrix (A : J → Matrix ι ι ℝ) (q : ℕ) :
    Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  matrixRepresentation (occupancy (effect A) q)

def bernoulliMatrix (A : J → Matrix ι ι ℝ) (q : ℕ) (σ τ : ℝ) :
    Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  matrixRepresentation (bernoulliOperator (effect A) q σ τ)

theorem regroup_single (b : ι) (T S : Finset J) :
    regroup (EuclideanSpace.single (b,T) 1) S =
      if S = T then EuclideanSpace.single b 1 else 0 := by
  ext a
  by_cases hST : S = T <;> by_cases hab : a = b
  all_goals simp [regroup_apply, PiLp.single_apply, Prod.mk.injEq, hST, hab]

theorem effect_single (A : J → Matrix ι ι ℝ) (j : J) (a b : ι) :
    effect A j (EuclideanSpace.single b 1) a = A j a b := by
  simp only [effect, EuclideanSpace.single, PiLp.single, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]

theorem creationMatrix_entry (A : J → Matrix ι ι ℝ) (q : ℕ)
    (a b : ι) (S T : Finset J) :
    creationMatrix A q (a,S) (b,T) =
      if S.card ≤ q then ∑ j ∈ S, if S.erase j = T then A j a b else 0 else 0 := by
  rw [creationMatrix, matrixRepresentation_entry, creation_apply]
  split_ifs with hS
  · simp only [WithLp.ofLp_sum, Finset.sum_apply, regroup_single, apply_ite, ite_apply, map_zero,
      effect_single, PiLp.zero_apply, WithLp.ofLp_zero, Pi.zero_apply]
  · rfl

theorem occupancyMatrix_entry (A : J → Matrix ι ι ℝ) (q : ℕ)
    (a b : ι) (S T : Finset J) :
    occupancyMatrix A q (a,S) (b,T) =
      if S.card ≤ q ∧ S = T then ∑ j ∈ S, A j a b else 0 := by
  rw [occupancyMatrix, matrixRepresentation_entry, occupancy_apply]
  by_cases hST : S = T
  · subst T
    by_cases hS : S.card ≤ q
    all_goals simp [hS, regroup_single, WithLp.ofLp_sum, effect_single]
  · by_cases hS : S.card ≤ q
    all_goals simp [hS, hST, regroup_single, WithLp.ofLp_sum, effect_single]

theorem annihilationMatrix_eq_transpose (A : J → Matrix ι ι ℝ) (q : ℕ) :
    annihilationMatrix A q = (creationMatrix A q).transpose := by
  unfold annihilationMatrix annihilation
  rw [← ContinuousLinearMap.star_eq_adjoint]
  rw [starAlgEquiv_map_star]
  ext out inp
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, star_trivial, creationMatrix]

/-- Exact lowering coefficient; without symmetry the effect is transposed,
as required by the Hilbert adjoint. -/
theorem annihilationMatrix_entry (A : J → Matrix ι ι ℝ) (q : ℕ)
    (a b : ι) (S T : Finset J) :
    annihilationMatrix A q (a,S) (b,T) =
      if T.card ≤ q then ∑ j ∈ T, if T.erase j = S then A j b a else 0 else 0 := by
  rw [annihilationMatrix_eq_transpose, Matrix.transpose_apply, creationMatrix_entry]

theorem bernoulliMatrix_decomposition (A : J → Matrix ι ι ℝ) (q : ℕ) (σ τ : ℝ) :
    bernoulliMatrix A q σ τ =
      σ • (creationMatrix A q + (creationMatrix A q).transpose) + τ • occupancyMatrix A q := by
  unfold bernoulliMatrix bernoulliOperator
  rw [map_add, map_smul, map_smul, map_add]
  rw [← creationMatrix, ← annihilationMatrix, ← occupancyMatrix, annihilationMatrix_eq_transpose]

theorem norm_bernoulliMatrix_le_of_sum_norm (A : J → Matrix ι ι ℝ)
    (hA : ∀ j, (A j).PosSemidef) (hsum : ‖∑ j, A j‖ ≤ 1)
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hsub : ∀ T : Finset J, T.card ≤ q → ‖∑ j ∈ T, A j‖ ≤ L)
    (σ τ : ℝ) :
    ‖bernoulliMatrix A q σ τ‖ ≤ 2 * |σ| * Real.sqrt L + |τ| * L := by
  rw [bernoulliMatrix, norm_matrixRepresentation]
  exact matrix_norm_bernoulliOperator_le_of_sum_norm A hA hsum q hL hsub σ τ

def selectorCutoff (q : ℕ) : Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  Matrix.diagonal fun z => if z.2.card ≤ q then 1 else 0

@[simp] theorem selectorCutoff_transpose (q : ℕ) :
    (selectorCutoff (J := J) (ι := ι) q).transpose = selectorCutoff q := by
  simp [selectorCutoff]

theorem selectorCutoff_compression_entry
    (K : Matrix (ι × Finset J) (ι × Finset J) ℝ) (q : ℕ)
    (a b : ι) (S T : Finset J) :
    (selectorCutoff (J := J) (ι := ι) q * K * selectorCutoff (J := J) (ι := ι) q) (a,S) (b,T) =
      if S.card ≤ q ∧ T.card ≤ q then K (a,S) (b,T) else 0 := by
  by_cases hS : S.card ≤ q <;> by_cases hT : T.card ≤ q
  all_goals simp [selectorCutoff, Matrix.mul_diagonal, Matrix.diagonal_mul, hS, hT]

def fullCreation (A : J → Matrix ι ι ℝ) : Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  ∑ j, Matrix.kronecker (A j) (HardCore.create j)

def fullAnnihilation (A : J → Matrix ι ι ℝ) : Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  ∑ j, Matrix.kronecker (A j) (HardCore.annihilate j)

def fullOccupancy (A : J → Matrix ι ι ℝ) : Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  ∑ j, Matrix.kronecker (A j) (HardCore.number j)

def fullBernoulli (A : J → Matrix ι ι ℝ) (σ τ : ℝ) :
    Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  ∑ j, Matrix.kronecker (A j)
    (σ • (HardCore.create j + HardCore.annihilate j) + τ • HardCore.number j)

theorem fullCreation_entry (A : J → Matrix ι ι ℝ)
    (a b : ι) (S T : Finset J) :
    fullCreation A (a,S) (b,T) = ∑ j ∈ S, if S.erase j = T then A j a b else 0 := by
  simp only [fullCreation, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap,
    HardCore.create, mul_ite, mul_one, mul_zero, ite_and]
  rw [← Finset.sum_filter]
  simp [eq_comm]
  rw [Finset.sum_filter]

theorem fullOccupancy_entry (A : J → Matrix ι ι ℝ)
    (a b : ι) (S T : Finset J) :
    fullOccupancy A (a,S) (b,T) = if S = T then ∑ j ∈ S, A j a b else 0 := by
  by_cases h : S = T
  all_goals simp [fullOccupancy, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap,
    HardCore.number_apply, h, ← Finset.sum_filter]

theorem fullCreation_transpose (A : J → Matrix ι ι ℝ)
    (hA : ∀ j, (A j).transpose = A j) :
    (fullCreation A).transpose = fullAnnihilation A := by
  rw [fullCreation, Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro j _
  change Matrix.kronecker (A j).transpose (HardCore.create j).transpose = _
  rw [hA j, HardCore.create_transpose]

theorem fullBernoulli_decomposition (A : J → Matrix ι ι ℝ) (σ τ : ℝ) :
    fullBernoulli A σ τ = σ • (fullCreation A + fullAnnihilation A) + τ • fullOccupancy A := by
  ext ⟨a,S⟩ ⟨b,T⟩
  simp only [fullBernoulli, fullCreation, fullAnnihilation, fullOccupancy, Matrix.sum_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, smul_eq_mul]
  change (∑ j, A j a b * (σ * (HardCore.create j S T + HardCore.annihilate j S T) +
      τ * HardCore.number j S T)) =
    σ * ((∑ j, A j a b * HardCore.create j S T) +
      ∑ j, A j a b * HardCore.annihilate j S T) +
      τ * ∑ j, A j a b * HardCore.number j S T
  have h (j : J) : A j a b * (σ * (HardCore.create j S T + HardCore.annihilate j S T) +
      τ * HardCore.number j S T) =
      σ * (A j a b * HardCore.create j S T) +
      σ * (A j a b * HardCore.annihilate j S T) +
      τ * (A j a b * HardCore.number j S T) := by ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem compress_fullCreation (A : J → Matrix ι ι ℝ) (q : ℕ) :
    selectorCutoff (J := J) (ι := ι) q * fullCreation A * selectorCutoff (J := J) (ι := ι) q = creationMatrix A q := by
  ext ⟨a,S⟩ ⟨b,T⟩
  rw [selectorCutoff_compression_entry, fullCreation_entry, creationMatrix_entry]
  by_cases hS : S.card ≤ q
  · by_cases hT : T.card ≤ q
    · simp [hS, hT]
    · simp only [hS, hT, and_false, ite_false, ite_true]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have he : S.erase j ≠ T := by
        intro he
        apply hT
        rw [← he]
        exact (Finset.card_le_card (Finset.erase_subset j S)).trans hS
      simp [he]
  · simp [hS]

theorem compress_fullOccupancy (A : J → Matrix ι ι ℝ) (q : ℕ) :
    selectorCutoff (J := J) (ι := ι) q * fullOccupancy A * selectorCutoff (J := J) (ι := ι) q = occupancyMatrix A q := by
  ext ⟨a,S⟩ ⟨b,T⟩
  rw [selectorCutoff_compression_entry, fullOccupancy_entry, occupancyMatrix_entry]
  by_cases hST : S = T
  · subst T
    simp
  · simp [hST]

theorem compress_fullAnnihilation (A : J → Matrix ι ι ℝ)
    (hA : ∀ j, (A j).transpose = A j) (q : ℕ) :
    selectorCutoff (J := J) (ι := ι) q * fullAnnihilation A * selectorCutoff (J := J) (ι := ι) q = (creationMatrix A q).transpose := by
  have h := congrArg Matrix.transpose (compress_fullCreation A q)
  simpa only [Matrix.transpose_mul, selectorCutoff_transpose, fullCreation_transpose A hA,
    Matrix.mul_assoc] using h

/-- Exact connection to the literal Kronecker sum of hard-core local
Bernoulli Jacobi matrices, compressed on both sides to selector degree q. -/
theorem compress_fullBernoulli (A : J → Matrix ι ι ℝ)
    (hA : ∀ j, (A j).transpose = A j) (q : ℕ) (σ τ : ℝ) :
    selectorCutoff (J := J) (ι := ι) q * fullBernoulli A σ τ * selectorCutoff (J := J) (ι := ι) q = bernoulliMatrix A q σ τ := by
  rw [fullBernoulli_decomposition, bernoulliMatrix_decomposition]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [compress_fullCreation, compress_fullAnnihilation A hA, compress_fullOccupancy]

end
end SRHT.SelectorRepresentation
