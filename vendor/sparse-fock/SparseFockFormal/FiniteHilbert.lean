import SparseFockFormal.ExternalOperators
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Euclidean realization of the finite sparse--Fock space

The sparse--Fock space used in the paper is finite.  This file equips the
concrete matrix model from `ExternalOperators` with its genuine Euclidean
operator norm and defines the orthogonal projections onto exact total grades.
Nothing in this layer is an abstract operator interface.
-/

namespace SparseFock.FiniteHilbert

open ExternalOperator FiniteOperator
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d m n : ℕ}

/-- The actual Euclidean space indexed by the external coordinate and a
sparse--Fock pattern. -/
abbrev FullSpace (d m n : ℕ) := EuclideanSpace ℝ (Fin d × Pattern m n)

/-- The continuous Euclidean operator represented by a concrete full matrix. -/
def asOperator (A : FullOp d m n) :
    FullSpace d m n →L[ℝ] FullSpace d m n :=
  (Matrix.toEuclideanCLM
    (n := Fin d × Pattern m n) (𝕜 := ℝ)) A

@[simp] theorem asOperator_apply (A : FullOp d m n)
    (x : Fin d × Pattern m n → ℝ) :
    asOperator A (WithLp.toLp 2 x) =
      WithLp.toLp 2 (Matrix.mulVec A x) :=
  rfl

/-- In the L2-operator-norm scope, the matrix norm is definitionally the norm
of its represented Euclidean operator. -/
theorem norm_asOperator (A : FullOp d m n) : ‖asOperator A‖ = ‖A‖ :=
  Matrix.l2_opNorm_toEuclideanCLM A

/-- The integer grade used by homogeneous matrices is the cast of the natural
occupation grade. -/
theorem gradeZ_eq_cast_grade (p : Pattern m n) :
    FiniteOperator.gradeZ p = (p.grade : ℤ) := by
  classical
  simp only [FiniteOperator.gradeZ, LocalOperator.weightZ, Pattern.grade]
  norm_cast

theorem fullGradeZ_eq_cast_grade (x : Fin d × Pattern m n) :
    ExternalOperator.gradeZ x = (x.2.grade : ℤ) :=
  gradeZ_eq_cast_grade x.2

/-- The diagonal orthogonal projection onto total grade `nu`. -/
def gradeProjection (nu : ℕ) : FullOp d m n :=
  Matrix.diagonal fun x ↦ if x.2.grade = nu then 1 else 0

@[simp] theorem gradeProjection_apply (nu : ℕ)
    (out inp : Fin d × Pattern m n) :
    gradeProjection (d := d) nu out inp =
      if out = inp ∧ out.2.grade = nu then 1 else 0 := by
  classical
  by_cases h : out = inp
  · subst inp
    by_cases hg : out.2.grade = nu <;>
      simp [gradeProjection, Matrix.diagonal_apply, hg]
  · simp [gradeProjection, Matrix.diagonal_apply, h]

@[simp] theorem gradeProjection_transpose (nu : ℕ) :
    (gradeProjection (d := d) (m := m) (n := n) nu).transpose =
      gradeProjection nu := by
  ext out inp
  simp only [Matrix.transpose_apply, gradeProjection_apply]
  by_cases hEq : out = inp
  · subst inp
    simp
  · have h' : inp ≠ out := Ne.symm hEq
    simp [hEq, h']

@[simp] theorem gradeProjection_mul_self (nu : ℕ) :
    gradeProjection (d := d) (m := m) (n := n) nu * gradeProjection nu =
      gradeProjection nu := by
  classical
  rw [gradeProjection, Matrix.diagonal_mul_diagonal]
  ext out inp
  by_cases hEq : out = inp
  · subst inp
    by_cases hg : out.2.grade = nu <;> simp [Matrix.diagonal_apply, hg]
  · simp [Matrix.diagonal_apply, hEq]

/-- Every exact-grade projection has Euclidean operator norm at most one. -/
theorem gradeProjection_norm_le_one (nu : ℕ) :
    ‖gradeProjection (d := d) (m := m) (n := n) nu‖ ≤ 1 := by
  rw [gradeProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro x
  by_cases h : x.2.grade = nu <;> simp [h]

@[simp] theorem gradeProjection_mul_gradeProjection
    {mu nu : ℕ} (h : mu ≠ nu) :
    gradeProjection (d := d) (m := m) (n := n) mu * gradeProjection nu = 0 := by
  classical
  rw [gradeProjection, gradeProjection, Matrix.diagonal_mul_diagonal]
  ext out inp
  by_cases hEq : out = inp
  · subst inp
    by_cases hmu : out.2.grade = mu
    · have hnu : out.2.grade ≠ nu := by
        intro hx
        exact h (hmu.symm.trans hx)
      simp [Matrix.diagonal_apply, hmu, hnu, h]
    · simp [Matrix.diagonal_apply, hmu]
  · simp [Matrix.diagonal_apply, hEq]

/-- Multiplication by the grade projection simply keeps coordinates in the
specified grade. -/
theorem gradeProjection_mulVec (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) (a : Fin d × Pattern m n) :
    Matrix.mulVec (gradeProjection (d := d) nu) x a =
      if a.2.grade = nu then x a else 0 := by
  classical
  simp [gradeProjection, Matrix.mulVec_diagonal]

/-- The squared Euclidean norm of an explicitly indexed vector. -/
def normSq (x : Fin d × Pattern m n → ℝ) : ℝ :=
  ∑ a, x a ^ 2

theorem normSq_nonneg (x : Fin d × Pattern m n → ℝ) :
    0 ≤ normSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem norm_toLp_sq (x : Fin d × Pattern m n → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = normSq x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [normSq]

theorem gradeProjection_normSq (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    normSq (Matrix.mulVec (gradeProjection (d := d) nu) x) =
      ∑ a with a.2.grade = nu, x a ^ 2 := by
  classical
  simp only [normSq, gradeProjection_mulVec]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a.2.grade = nu <;> simp [h]

/-- Grade projections are Euclidean contractions, stated in exact coordinate
energy form. -/
theorem gradeProjection_normSq_le (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    normSq (Matrix.mulVec (gradeProjection (d := d) nu) x) ≤ normSq x := by
  rw [gradeProjection_normSq]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun a : Fin d × Pattern m n ↦ a.2.grade = nu)
      Finset.univ) ?_
  intro a _ _
  exact sq_nonneg (x a)

/-- A coordinatewise squared-energy estimate yields the corresponding L2
operator-norm bound for the concrete finite matrix. -/
theorem norm_le_of_normSq_mulVec_le {A : FullOp d m n} {C : ℝ}
    (hC : 0 ≤ C)
    (henergy : ∀ x : Fin d × Pattern m n → ℝ,
      normSq (Matrix.mulVec A x) ≤ C ^ 2 * normSq x) :
    ‖A‖ ≤ C := by
  rw [← norm_asOperator]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp x))‖ ≤ C * ‖x‖
  have hsq := henergy (WithLp.ofLp x)
  have hout := norm_toLp_sq (d := d) (m := m) (n := n)
    (Matrix.mulVec A (WithLp.ofLp x))
  have hin := norm_toLp_sq (d := d) (m := m) (n := n) (WithLp.ofLp x)
  have hx : ‖x‖ ^ 2 = normSq (WithLp.ofLp x) := by
    simpa using hin
  rw [← hout, ← hx] at hsq
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (WithLp.toLp 2
    (Matrix.mulVec A (WithLp.ofLp x)))]

/-- A concrete matrix is grade homogeneous iff every nonzero entry has the
advertised casted occupation shift.  This is a convenient natural-grade form
of `ExternalOperator.Homogeneous`. -/
theorem homogeneous_grade_relation {delta : ℤ} {A : FullOp d m n}
    (hA : ExternalOperator.Homogeneous delta A)
    {out inp : Fin d × Pattern m n} (hentry : A out inp ≠ 0) :
    (out.2.grade : ℤ) = (inp.2.grade : ℤ) + delta := by
  simpa [fullGradeZ_eq_cast_grade] using hA hentry

theorem homogeneous_smul {delta : ℤ} {A : FullOp d m n}
    (hA : ExternalOperator.Homogeneous delta A) (c : ℝ) :
    ExternalOperator.Homogeneous delta (c • A) := by
  intro out inp hentry
  have hAentry : A out inp ≠ 0 := by
    intro hz
    apply hentry
    simp [hz]
  exact hA hAentry

theorem homogeneous_add {delta : ℤ} {A B : FullOp d m n}
    (hA : ExternalOperator.Homogeneous delta A)
    (hB : ExternalOperator.Homogeneous delta B) :
    ExternalOperator.Homogeneous delta (A + B) := by
  intro out inp hentry
  by_cases hAz : A out inp = 0
  · have hBn : B out inp ≠ 0 := by
      intro hBz
      exact hentry (by simp [hAz, hBz])
    exact hB hBn
  · exact hA hAz

/-- If `mu` is the grade forced from input grade `nu` by homogeneity, then
the output-grade projection can be inserted without changing the restricted
operator. -/
theorem output_projection_of_homogeneous {delta : ℤ} {A : FullOp d m n}
    (hA : ExternalOperator.Homogeneous delta A) (mu nu : ℕ)
    (hcompatible : (mu : ℤ) = (nu : ℤ) + delta) :
    gradeProjection (d := d) mu * A * gradeProjection nu =
      A * gradeProjection nu := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : A out inp = 0
    · simp [hin, hentry]
    · have hrel := homogeneous_grade_relation hA hentry
      have houtInt : (out.2.grade : ℤ) = (mu : ℤ) := by
        rw [hrel, hin, ← hcompatible]
      have hout : out.2.grade = mu := by exact_mod_cast houtInt
      simp [hin, hout]
  · simp [hin]

/-- If homogeneity would force a negative or otherwise impossible natural
output grade, the operator vanishes on the stated input grade. -/
theorem input_grade_vanishes_of_no_output {delta : ℤ} {A : FullOp d m n}
    (hA : ExternalOperator.Homogeneous delta A) (nu : ℕ)
    (himpossible : ∀ mu : ℕ, (mu : ℤ) ≠ (nu : ℤ) + delta) :
    A * gradeProjection (d := d) nu = 0 := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : A out inp = 0
    · simp [hin, hentry]
    · have hrel := homogeneous_grade_relation hA hentry
      exfalso
      exact (himpossible out.2.grade (by simpa [hin] using hrel))
  · simp [hin]

/-- Projecting a homogeneous matrix onto an incompatible output grade kills
its action on one fixed input grade. -/
theorem incompatible_grade_block_zero {delta : ℤ} {A : FullOp d m n}
    (hA : ExternalOperator.Homogeneous delta A) (mu nu : ℕ)
    (hincompatible : (mu : ℤ) ≠ (nu : ℤ) + delta) :
    gradeProjection (d := d) mu * A * gradeProjection nu = 0 := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.zero_apply]
  by_cases hout : out.2.grade = mu
  · by_cases hin : inp.2.grade = nu
    · by_cases hentry : A out inp = 0
      · simp [hout, hin, hentry]
      · have hrel := homogeneous_grade_relation hA hentry
        exfalso
        apply hincompatible
        simpa [hout, hin] using hrel
    · simp [hout, hin]
  · simp [hout]

end

end SparseFock.FiniteHilbert
