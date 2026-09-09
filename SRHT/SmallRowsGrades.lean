import SRHT.SmallRowsLift

/-! Exact occupation-grade support for the literal hard-core operators. -/
namespace SRHT.HardCore
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem create_card (i : G) (S T : Finset G) (h : create i S T ≠ 0) :
    S.card=T.card+1 := by
  have he : i∈S ∧ T=S.erase i := by simpa [create] using h
  rw [he.2,Finset.card_erase_of_mem he.1]
  have hp := Finset.card_pos.mpr ⟨i,he.1⟩
  omega

theorem annihilate_card (i : G) (S T : Finset G) (h : annihilate i S T ≠ 0) :
    T.card=S.card+1 := by
  have he : i∉S ∧ T=insert i S := by simpa [annihilate] using h
  rw [he.2,Finset.card_insert_of_notMem he.1]

theorem createMode_card (f : G→ℝ) (S T : Finset G) (h : createMode f S T ≠ 0) :
    S.card=T.card+1 := by
  simp only [createMode,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  apply create_card i
  intro hz
  simp [hz] at hi

theorem annihilateMode_card (f : G→ℝ) (S T : Finset G) (h : annihilateMode f S T ≠ 0) :
    T.card=S.card+1 := by
  simp only [annihilateMode,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  apply annihilate_card i
  intro hz
  simp [hz] at hi

theorem homogeneous_left_projection (A : Op G) (r s : ℕ)
    (hA : ∀ S T, A S T ≠ 0 → T.card=r → S.card=s) :
    gradeProjection s * A * gradeProjection r = A * gradeProjection r := by
  classical
  ext S T
  simp only [gradeProjection,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hr : T.card=r
  · by_cases hz : A S T=0
    · simp [hr,hz]
    · simp [hr,hA S T hz hr]
  · simp [hr]

theorem create_grade (i : G) (r : ℕ) :
    gradeProjection (r+1) * create i * gradeProjection r = create i * gradeProjection r :=
  homogeneous_left_projection _ _ _ (by intro S T h hr; rw [create_card i S T h,hr])

theorem annihilate_grade (i : G) (r : ℕ) :
    gradeProjection r * annihilate i * gradeProjection (r+1) = annihilate i * gradeProjection (r+1) :=
  homogeneous_left_projection _ _ _ (by intro S T h hr; have hc:=annihilate_card i S T h; omega)

theorem createMode_grade (f : G→ℝ) (r : ℕ) :
    gradeProjection (r+1) * createMode f * gradeProjection r = createMode f * gradeProjection r :=
  homogeneous_left_projection _ _ _ (by intro S T h hr; rw [createMode_card f S T h,hr])

theorem annihilateMode_grade (f : G→ℝ) (r : ℕ) :
    gradeProjection r * annihilateMode f * gradeProjection (r+1) = annihilateMode f * gradeProjection (r+1) :=
  homogeneous_left_projection _ _ _ (by intro S T h hr; have hc:=annihilateMode_card f S T h; omega)

theorem annihilate_grade_zero (i : G) : annihilate i * gradeProjection 0 = 0 := by
  classical
  ext S T
  simp only [gradeProjection,Matrix.mul_diagonal,Matrix.zero_apply]
  by_cases hT : T.card=0
  · have hz : annihilate i S T=0 := by
      by_contra hh
      have hc:=annihilate_card i S T hh
      omega
    simp [hz]
  · simp [hT]

theorem annihilateMode_grade_zero (f : G→ℝ) : annihilateMode f * gradeProjection 0 = 0 := by
  classical
  ext S T
  simp only [gradeProjection,Matrix.mul_diagonal,Matrix.zero_apply]
  by_cases hT : T.card=0
  · have hz : annihilateMode f S T=0 := by
      by_contra hh
      have hc:=annihilateMode_card f S T hh
      omega
    simp [hz]
  · simp [hT]

end
end SRHT.HardCore
