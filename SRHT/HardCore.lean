import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite hard-core subset operators

The matrices in this file are literal matrices on `Finset G`, rather than an
axiomatic creation/annihilation interface. Rows are outputs and columns inputs.
-/

namespace SRHT.HardCore

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G]

abbrev Space (G : Type*) := Finset G
abbrev Op (G : Type*) := Matrix (Finset G) (Finset G) ℝ

/-- Insert one previously absent site. -/
def create (i : G) : Op G := fun S T =>
  if i ∈ S ∧ T = S.erase i then 1 else 0

/-- Remove one occupied site. -/
def annihilate (i : G) : Op G := fun S T =>
  if i ∉ S ∧ T = insert i S then 1 else 0

/-- The projector onto configurations containing a specified site. -/
def number (i : G) : Op G :=
  Matrix.diagonal fun S => if i ∈ S then 1 else 0

/-- The exact occupation-grade projector. -/
def gradeProjection (r : ℕ) : Op G :=
  Matrix.diagonal fun S => if S.card = r then 1 else 0

@[simp] theorem create_mul_apply (i : G) (A : Op G) (S T : Finset G) :
    (create i * A) S T = if i ∈ S then A (S.erase i) T else 0 := by
  classical
  by_cases h : i ∈ S <;> simp [create, Matrix.mul_apply, h]

@[simp] theorem annihilate_mul_apply (i : G) (A : Op G) (S T : Finset G) :
    (annihilate i * A) S T = if i ∉ S then A (insert i S) T else 0 := by
  classical
  by_cases h : i ∈ S <;> simp [annihilate, Matrix.mul_apply, h]

@[simp] theorem create_mulVec (i : G) (v : Finset G → ℝ) (S : Finset G) :
    (create i).mulVec v S = if i ∈ S then v (S.erase i) else 0 := by
  classical
  by_cases h : i ∈ S <;> simp [create, Matrix.mulVec, dotProduct, h]

@[simp] theorem annihilate_mulVec (i : G) (v : Finset G → ℝ) (S : Finset G) :
    (annihilate i).mulVec v S = if i ∉ S then v (insert i S) else 0 := by
  classical
  by_cases h : i ∈ S <;> simp [annihilate, Matrix.mulVec, dotProduct, h]

theorem erase_insert_relation (i : G) (S T : Finset G) :
    (i ∈ T ∧ S = T.erase i) ↔ (i ∉ S ∧ T = insert i S) := by
  constructor
  · rintro ⟨hi, rfl⟩
    simp [Finset.insert_erase hi]
  · rintro ⟨hi, rfl⟩
    simp [hi]

@[simp] theorem create_transpose (i : G) : (create i).transpose = annihilate i := by
  ext S T
  simp only [Matrix.transpose_apply, create, annihilate, erase_insert_relation]

@[simp] theorem annihilate_transpose (i : G) :
    (annihilate i).transpose = create i := by
  rw [← create_transpose, Matrix.transpose_transpose]

@[simp] theorem number_apply (i : G) (S T : Finset G) :
    number i S T = if S = T ∧ i ∈ S then 1 else 0 := by
  classical
  by_cases h : S = T
  · subst T; simp [number, Matrix.diagonal_apply]
  · simp [number, Matrix.diagonal_apply, h]

@[simp] theorem annihilate_create_same (i : G) :
    annihilate i * create i = 1 - number i := by
  classical
  ext S T
  by_cases h : i ∈ S
  · simp [annihilate_mul_apply, h, number_apply, Matrix.one_apply]
  · simp [annihilate_mul_apply, h, create, number_apply, Matrix.one_apply,
      Finset.erase_insert, eq_comm]

@[simp] theorem create_annihilate_same (i : G) :
    create i * annihilate i = number i := by
  classical
  ext S T
  by_cases h : i ∈ S
  · simp [create_mul_apply, h, annihilate, number_apply,
      Finset.insert_erase h, eq_comm]
  · simp [create_mul_apply, h, number_apply]

@[simp] theorem create_square (i : G) : create i * create i = 0 := by
  ext S T
  by_cases h : i ∈ S <;> simp [create_mul_apply, create, h]

@[simp] theorem annihilate_square (i : G) :
    annihilate i * annihilate i = 0 := by
  ext S T
  by_cases h : i ∈ S <;> simp [annihilate_mul_apply, annihilate, h]

theorem annihilate_create_of_ne {i j : G} (hij : i ≠ j) :
    annihilate i * create j = create j * annihilate i := by
  ext S T
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [annihilate_mul_apply, create_mul_apply, create, annihilate,
      hi, hj, hij, hij.symm, Finset.erase_insert_of_ne hij]

/-- The exact hard-core commutator, including the repeated-site correction. -/
theorem annihilate_create (i j : G) :
    annihilate i * create j = create j * annihilate i +
      if i = j then 1 - (2 : ℝ) • number i else 0 := by
  by_cases hij : i = j
  · subst j
    rw [annihilate_create_same, create_annihilate_same]
    simp only [ite_true]
    ext S T
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · simp [hij, annihilate_create_of_ne hij]

theorem create_comm (i j : G) : create i * create j = create j * create i := by
  by_cases hij : i = j
  · subst j; rfl
  have hji : j ≠ i := Ne.symm hij
  ext S T
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [create_mul_apply, create, hi, hj, hij, hji, Finset.erase_right_comm]

theorem annihilate_comm (i j : G) :
    annihilate i * annihilate j = annihilate j * annihilate i := by
  have h := congrArg Matrix.transpose (create_comm i j)
  simpa using h.symm

@[simp] theorem number_square (i : G) : number i * number i = number i := by
  classical
  rw [number, Matrix.diagonal_mul_diagonal]
  congr 1
  funext S
  by_cases h : i ∈ S <;> simp [h]

@[simp] theorem number_transpose (i : G) : (number i).transpose = number i := by
  simp [number]

@[simp] theorem number_norm_le_one (i : G) : ‖number i‖ ≤ 1 := by
  rw [number, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro S
  by_cases h : i ∈ S <;> simp [h]

theorem annihilate_norm_le_one (i : G) : ‖annihilate i‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (annihilate i)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, annihilate_transpose,
    create_annihilate_same] at h
  have hb := number_norm_le_one i
  have hn := norm_nonneg (annihilate i)
  nlinarith

theorem create_norm_le_one (i : G) : ‖create i‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose (create i)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, create_transpose] at h
  rw [← h]
  exact annihilate_norm_le_one i

@[simp] theorem gradeProjection_square (r : ℕ) :
    gradeProjection (G := G) r * gradeProjection r = gradeProjection r := by
  classical
  rw [gradeProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext S
  by_cases h : S.card = r <;> simp [h]

@[simp] theorem gradeProjection_transpose (r : ℕ) :
    (gradeProjection (G := G) r).transpose = gradeProjection r := by
  simp [gradeProjection]

theorem gradeProjection_norm_le_one (r : ℕ) :
    ‖gradeProjection (G := G) r‖ ≤ 1 := by
  rw [gradeProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro S
  by_cases h : S.card = r <;> simp [h]

/-- Annihilation in a real one-particle mode. -/
def annihilateMode (f : G → ℝ) : Op G := ∑ i, f i • annihilate i

/-- Creation in a real one-particle mode. -/
def createMode (f : G → ℝ) : Op G := ∑ i, f i • create i

@[simp] theorem createMode_transpose (f : G → ℝ) :
    (createMode f).transpose = annihilateMode f := by
  simp [createMode, annihilateMode, Matrix.transpose_sum]

@[simp] theorem annihilateMode_transpose (f : G → ℝ) :
    (annihilateMode f).transpose = createMode f := by
  simp [createMode, annihilateMode, Matrix.transpose_sum]

theorem sum_smul_mul_sum_smul (f g : G → ℝ) (A B : G → Op G) :
    (∑ i, f i • A i) * (∑ j, g j • B j) =
      ∑ i, ∑ j, (f i * g j) • (A i * B j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

theorem annihilateMode_createMode (f g : G → ℝ) :
    annihilateMode f * createMode g = createMode g * annihilateMode f +
      (∑ i, f i * g i) • (1 : Op G) -
      (2 : ℝ) • ∑ i, (f i * g i) • number i := by
  classical
  have hmain : (∑ i, ∑ j, (f i * g j) • (create j * annihilate i)) =
      createMode g * annihilateMode f := by
    rw [createMode, annihilateMode, sum_smul_mul_sum_smul, Finset.sum_comm]
    simp only [mul_comm]
  have hdiag :
      (∑ i, ∑ j, (f i * g j) •
        (if i = j then (1 : Op G) - (2 : ℝ) • number i else 0)) =
      ∑ i, (f i * g i) • ((1 : Op G) - (2 : ℝ) • number i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [smul_ite]
  have hlast : (∑ i, (f i * g i) • ((1 : Op G) - (2 : ℝ) • number i)) =
      (∑ i, f i * g i) • (1 : Op G) -
        (2 : ℝ) • ∑ i, (f i * g i) • number i := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [annihilateMode, createMode, sum_smul_mul_sum_smul]
  simp_rw [annihilate_create, smul_add, Finset.sum_add_distrib]
  rw [hmain, hdiag, hlast]
  simp only [createMode, annihilateMode]
  abel

/-- The sum of local occupancies counts occupied sites exactly. -/
theorem sum_number :
    (∑ i : G, number i) = Matrix.diagonal (fun S : Finset G => (S.card : ℝ)) := by
  classical
  ext S T
  by_cases h : S = T
  · subst T
    simp [number, Matrix.diagonal_apply, Matrix.sum_apply]
  · simp [number, Matrix.diagonal_apply, Matrix.sum_apply, h]

theorem sum_number_mul_grade (r : ℕ) :
    (∑ i : G, number i) * gradeProjection r = (r : ℝ) • gradeProjection r := by
  rw [sum_number, gradeProjection, Matrix.diagonal_mul_diagonal]
  ext S T
  by_cases h : S = T
  · subst T
    by_cases hr : S.card = r <;> simp [Matrix.diagonal_apply, hr]
  · simp [Matrix.diagonal_apply, h]

/-- The concrete column collecting every single-site annihilation. -/
def extraction : Matrix (G × Finset G) (Finset G) ℝ :=
  fun out inp => annihilate out.1 out.2 inp

theorem extraction_gram :
    (extraction (G := G)).transpose * extraction = ∑ i : G, number i := by
  classical
  have h : (extraction (G := G)).transpose * extraction =
      ∑ i : G, (annihilate i).transpose * annihilate i := by
    ext S T
    simp only [extraction, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.transpose_apply, Matrix.sum_apply]
  rw [h]
  simp

/-- Restrict the input of extraction to one occupation grade. -/
def gradeExtraction (r : ℕ) : Matrix (G × Finset G) (Finset G) ℝ :=
  extraction * gradeProjection r

theorem gradeExtraction_gram (r : ℕ) :
    (gradeExtraction (G := G) r).transpose * gradeExtraction r =
      (r : ℝ) • gradeProjection r := by
  rw [gradeExtraction, Matrix.transpose_mul, gradeProjection_transpose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc extraction.transpose extraction,
    extraction_gram, sum_number_mul_grade, mul_smul_comm, gradeProjection_square]

theorem gradeExtraction_norm_sq_le (r : ℕ) :
    ‖gradeExtraction (G := G) r‖ ^ 2 ≤ (r : ℝ) := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (gradeExtraction (G := G) r)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, gradeExtraction_gram,
    norm_smul, Real.norm_natCast] at h
  have hp := gradeProjection_norm_le_one (G := G) r
  have hn : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith

section MatrixEnergy

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

def energy {I : Type*} [Fintype I] (v : I → ℝ) : ℝ := ∑ i, v i ^ 2

theorem norm_toLp_sq {I : Type*} [Fintype I] (v : I → ℝ) :
    ‖WithLp.toLp 2 v‖ ^ 2 = energy v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [energy]

/-- Coordinate-energy criterion for a rectangular Euclidean matrix norm. -/
theorem matrix_norm_le_of_energy (A : Matrix I J ℝ) (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ v : J → ℝ, energy (A.mulVec v) ≤ C^2 * energy v) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖ ≤ C * ‖x‖
  have he := henergy (WithLp.ofLp x)
  have hout := norm_toLp_sq (A.mulVec (WithLp.ofLp x))
  have hin : ‖x‖^2 = energy (WithLp.ofLp x) := by
    simpa using norm_toLp_sq (WithLp.ofLp x)
  rw [← hout, ← hin] at he
  have hp : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg x)
  have hn := norm_nonneg (WithLp.toLp 2 (A.mulVec (WithLp.ofLp x)))
  nlinarith

theorem matrix_energy_le_norm (A : Matrix I J ℝ) (v : J → ℝ) :
    energy (A.mulVec v) ≤ ‖A‖^2 * energy v := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  change ‖WithLp.toLp 2 (A.mulVec v)‖ ^ 2 ≤
    (‖A‖ * ‖WithLp.toLp 2 v‖) ^ 2 at hsq
  simpa only [mul_pow, norm_toLp_sq] using hsq

/-- Repeat a rectangular matrix independently on a spectator coordinate. -/
def amplifyRight (A : Matrix I J ℝ) : Matrix (I × K) (J × K) ℝ :=
  fun out inp => if out.2 = inp.2 then A out.1 inp.1 else 0

theorem amplifyRight_mulVec (A : Matrix I J ℝ) (v : J × K → ℝ)
    (i : I) (k : K) :
    (amplifyRight A).mulVec v (i,k) = A.mulVec (fun j => v (j,k)) i := by
  classical
  simp [amplifyRight, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem amplifyRight_norm_le (A : Matrix I J ℝ) :
    ‖amplifyRight (K := K) A‖ ≤ ‖A‖ := by
  apply matrix_norm_le_of_energy _ _ (norm_nonneg A)
  intro v
  calc
    energy ((amplifyRight A).mulVec v) =
        ∑ k : K, energy (A.mulVec (fun j => v (j,k))) := by
          simp only [energy, Fintype.sum_prod_type, amplifyRight_mulVec]
          rw [Finset.sum_comm]
    _ ≤ ∑ k : K, ‖A‖^2 * energy (fun j => v (j,k)) := by
          apply Finset.sum_le_sum
          intro k _
          exact matrix_energy_le_norm A _
    _ = ‖A‖^2 * energy v := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [energy, Fintype.sum_prod_type]
          rw [Finset.sum_comm]

end MatrixEnergy

end
end SRHT.HardCore
