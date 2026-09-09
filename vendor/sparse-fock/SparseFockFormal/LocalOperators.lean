import SparseFockFormal.Pattern
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace SparseFock

namespace LocalOperator

/-- A real operator on the three local sparse-Fock levels.  Rows are outputs and
columns are inputs. -/
abbrev Op := Matrix Level Level ℝ

/-- The rank-one matrix `|out><inp|`. -/
def ketBra (out inp : Level) : Op := fun i j =>
  if i = out ∧ j = inp then 1 else 0

@[simp] theorem ketBra_apply (out inp i j : Level) :
    ketBra out inp i j = if i = out ∧ j = inp then 1 else 0 := rfl

def pCreate : Op := ketBra .one .zero
def pDestroy : Op := ketBra .zero .one
def rPromote : Op := ketBra .two .one
def rDemote : Op := ketBra .one .two

/-- The three-level Jacobi multiplication matrix with heavy amplitude `ρ`. -/
def jacobi (ρ : ℝ) : Op :=
  pDestroy + pCreate + ρ • (rPromote + rDemote)

@[simp] theorem transpose_ketBra (out inp : Level) :
    (ketBra out inp).transpose = ketBra inp out := by
  ext i j
  simp [ketBra, Matrix.transpose_apply, and_comm]

@[simp] theorem transpose_pCreate : pCreate.transpose = pDestroy := by
  simp [pCreate, pDestroy]

@[simp] theorem transpose_pDestroy : pDestroy.transpose = pCreate := by
  simp [pCreate, pDestroy]

@[simp] theorem transpose_rPromote : rPromote.transpose = rDemote := by
  simp [rPromote, rDemote]

@[simp] theorem transpose_rDemote : rDemote.transpose = rPromote := by
  simp [rPromote, rDemote]

@[simp] theorem transpose_jacobi (ρ : ℝ) : (jacobi ρ).transpose = jacobi ρ := by
  ext i j
  cases i <;> cases j <;>
    simp [jacobi, pCreate, pDestroy, rPromote, rDemote, ketBra,
      Matrix.transpose_apply]

/-- Entrywise verification of the local multiplication matrix. -/
theorem jacobi_apply (ρ : ℝ) (i j : Level) :
    jacobi ρ i j =
      match i, j with
      | .zero, .one => 1
      | .one, .zero => 1
      | .one, .two => ρ
      | .two, .one => ρ
      | _, _ => 0 := by
  cases i <;> cases j <;>
    simp [jacobi, pCreate, pDestroy, rPromote, rDemote, ketBra]

@[simp] theorem pCreate_sq : pCreate * pCreate = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, ketBra, Matrix.mul_apply]

@[simp] theorem rPromote_sq : rPromote * rPromote = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [rPromote, ketBra, Matrix.mul_apply]

/-- The same-site product used by the `C A` factorization vanishes. -/
@[simp] theorem pCreate_mul_rPromote : pCreate * rPromote = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, rPromote, ketBra, Matrix.mul_apply]

/-- The same-site product used by the grade-zero `C Ã` factorization vanishes. -/
@[simp] theorem pCreate_mul_rDemote : pCreate * rDemote = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, rDemote, ketBra, Matrix.mul_apply]

/-- Reversing the first mixed product produces the artificial direct jump. -/
@[simp] theorem rPromote_mul_pCreate :
    rPromote * pCreate = ketBra .two .zero := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, rPromote, ketBra, Matrix.mul_apply]

def weightZ (q : Level) : ℤ := q.weight

/-- A local matrix changes occupation grade by `δ` on its support. -/
def Homogeneous (δ : ℤ) (A : Op) : Prop :=
  ∀ ⦃out inp : Level⦄, A out inp ≠ 0 → weightZ out = weightZ inp + δ

theorem pCreate_homogeneous : Homogeneous 1 pCreate := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [pCreate, ketBra, weightZ, Level.weight] at h ⊢

theorem pDestroy_homogeneous : Homogeneous (-1) pDestroy := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [pDestroy, ketBra, weightZ, Level.weight] at h ⊢

theorem rPromote_homogeneous : Homogeneous 1 rPromote := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [rPromote, ketBra, weightZ, Level.weight] at h ⊢

theorem rDemote_homogeneous : Homogeneous (-1) rDemote := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [rDemote, ketBra, weightZ, Level.weight] at h ⊢

end LocalOperator

end SparseFock


