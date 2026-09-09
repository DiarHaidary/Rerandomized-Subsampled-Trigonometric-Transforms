import SRHT.GradeCompression
import SRHT.SignCompression
import SRHT.SmallRowsGrades

/-! Exact degree support and the nine-neighbor bound for the actual two-sign frame. -/

namespace SRHT.SmallRowsGrade
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open TwoSignRepresentation GradeCompression

variable {k d : ℕ}

abbrev Index (k d : ℕ) := Fin d × SmallRows.SignPair (WalshIndex k)
abbrev Grades (k : ℕ) := Fin (Fintype.card (WalshIndex k)+1) × Fin (Fintype.card (WalshIndex k)+1)

/-- The actual pair of occupation cardinalities, with their finite bounds. -/
def grade (z : Index k d) : Grades k :=
  (⟨z.2.1.card,Nat.lt_succ_of_le (Finset.card_le_univ _)⟩,
   ⟨z.2.2.card,Nat.lt_succ_of_le (Finset.card_le_univ _)⟩)

theorem flip_card_exact (i : WalshIndex k) (S T : Finset (WalshIndex k))
    (h : flip i S T ≠ 0) : S.card=T.card+1 ∨ T.card=S.card+1 := by
  by_cases hc : HardCore.create i S T=0
  · right
    apply HardCore.annihilate_card i S T
    simpa [TwoSignRepresentation.flip,hc] using h
  · exact Or.inl (HardCore.create_card i S T hc)

theorem liftedFrame_card_exact (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (T : Finset (WalshIndex k)) (out : SmallRows.RowSign T (WalshIndex k))
    (inp : Index k d) (h : liftedFrame U T out inp ≠ 0) :
    (out.2.1.card=inp.2.1.card+1 ∨ inp.2.1.card=out.2.1.card+1) ∧
    (out.2.2.card=inp.2.2.card+1 ∨ inp.2.2.card=out.2.2.card+1) := by
  rw [liftedFrame_apply] at h
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  have hx : flip i out.2.1 inp.2.1 ≠ 0 := by intro hz; simp [hz] at hi
  have hy : flip a out.2.2 inp.2.2 ≠ 0 := by intro hz; simp [hz] at hi
  exact ⟨flip_card_exact i _ _ hx,flip_card_exact a _ _ hy⟩

/-- The Gram has exact even degree steps; a bandwidth inequality alone would not suffice. -/
theorem effectSum_evenStep (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (T : Finset (WalshIndex k)) (out inp : Index k d)
    (h : (∑ j ∈ T,TwoSignRepresentation.effect U j) out inp ≠ 0) :
    pairEvenStep (grade out) (grade inp) := by
  rw [effect_sum_gram,Matrix.mul_apply] at h
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ho : liftedFrame U T a out ≠ 0 := by intro hz; simp [Matrix.transpose_apply,hz] at ha
  have hi : liftedFrame U T a inp ≠ 0 := by intro hz; simp [hz] at ha
  have hs := liftedFrame_card_exact U T a out ho
  have ht := liftedFrame_card_exact U T a inp hi
  change evenStep out.2.1.card inp.2.1.card ∧ evenStep out.2.2.card inp.2.2.card
  unfold evenStep
  constructor <;> omega

theorem grade_projection_eq (a : Grades k) :
    gradeProjection (grade (k:=k) (d:=d)) a =
      SmallRows.rowGradeProjection (R:=Fin d) (G:=WalshIndex k) a.1.val a.2.val := by
  ext out inp
  rw [SmallRows.rowGradeProjection_apply]
  simp only [gradeProjection,Matrix.diagonal_apply]
  by_cases he : out=inp
  · subst inp
    simp [grade,Prod.ext_iff,Fin.ext_iff]
  · simp [he]

def allowed (q : ℕ) (a : Grades k) : Prop := a.1.val≤2*q ∧ a.2.val≤2*q

instance (q : ℕ) : DecidablePred (@allowed k q) := fun a => inferInstanceAs
  (Decidable (a.1.val≤2*q ∧ a.2.val≤2*q))

theorem cutoff_diagonal (q : ℕ) : SignCompression.projection k d q =
    Matrix.diagonal (fun z => if allowed q (grade z) then 1 else 0) := by
  ext out inp
  simp [SignCompression.projection,Cutoff.supportProjection,SignCompression.support,allowed,grade]
  rfl

theorem grade_cutoff_mul (q : ℕ) (a : Grades k) :
    gradeProjection (grade (k:=k) (d:=d)) a * SignCompression.projection k d q =
      if allowed q a then gradeProjection grade a else 0 := by
  rw [cutoff_diagonal,gradeProjection,Matrix.diagonal_mul_diagonal]
  by_cases ha : allowed q a <;> simp only [ha,if_true,if_false]
  all_goals
    ext out inp
    by_cases hai : grade out=a <;> by_cases he : out=inp
    · subst inp; simp [Matrix.diagonal_apply,hai,ha]
    · simp [Matrix.diagonal_apply,he]
    · subst inp; simp [Matrix.diagonal_apply,hai]
    · simp [Matrix.diagonal_apply,he]

theorem cutoff_grade_mul (q : ℕ) (a : Grades k) :
    SignCompression.projection k d q * gradeProjection (grade (k:=k) (d:=d)) a =
      if allowed q a then gradeProjection grade a else 0 := by
  have h := congrArg Matrix.transpose (grade_cutoff_mul (d:=d) q a)
  by_cases ha : allowed q a <;>
    simpa [Matrix.transpose_mul,SignCompression.projection,
      ProjectionBounds.projection_transpose,gradeProjection,ha] using h

theorem cutoff_effect_sum (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (q : ℕ) (T : Finset (WalshIndex k)) :
    (∑ j∈T,SignCompression.effect U q j) =
      SignCompression.projection k d q * (∑ j∈T,TwoSignRepresentation.effect U j) *
        SignCompression.projection k d q :=
  ProjectionBounds.sandwich_finset_sum T _ _

theorem cutoff_effectSum_evenStep (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (q : ℕ) (T : Finset (WalshIndex k)) (out inp : Index k d)
    (h : (∑ j∈T,SignCompression.effect U q j) out inp ≠ 0) :
    pairEvenStep (grade out) (grade inp) := by
  rw [cutoff_effect_sum,SignCompression.projection,ProjectionBounds.sandwich_apply] at h
  split_ifs at h with hs
  · exact effectSum_evenStep U T out inp h
  · exact (h rfl).elim

theorem cutoff_grade_block (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (q : ℕ) (T : Finset (WalshIndex k)) (a : Grades k) :
    gradeProjection grade a * (∑ j∈T,SignCompression.effect U q j) * gradeProjection grade a =
      if allowed q a then
        gradeProjection grade a * (∑ j∈T,TwoSignRepresentation.effect U j) * gradeProjection grade a
      else 0 := by
  rw [cutoff_effect_sum]
  simp only [← Matrix.mul_assoc]
  rw [grade_cutoff_mul]
  by_cases ha : allowed q a
  · simp only [ha,if_true]
    rw [Matrix.mul_assoc _ (SignCompression.projection k d q),cutoff_grade_mul,if_pos ha]
  · simp [ha]

/-- The full cutoff estimate, reducing only the diagonal numerical estimate
to the independently formalized four-block calculation. -/
theorem sign_cutoff_norm_le_of_diagonal (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (q : ℕ) (T : Finset (WalshIndex k)) {L : ℝ} (hL : 0≤L)
    (hdiag : ∀ r s : ℕ, r≤2*q → s≤2*q →
      ‖SmallRows.rowGradeProjection (R:=Fin d) (G:=WalshIndex k) r s *
        (∑ j∈T,TwoSignRepresentation.effect U j) * SmallRows.rowGradeProjection r s‖ ≤ L) :
    ‖∑ j∈T,SignCompression.effect U q j‖ ≤ 9*L := by
  have hpos : (∑ j∈T,SignCompression.effect U q j).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j hj
    exact SignCompression.effect_positive U q j
  apply grade_schur_nine _ hpos (grade (k:=k) (d:=d)) hL
  · intro a b hab
    apply grade_block_zero_of_entries _ _ pairEvenStep _ a b hab
    intro out inp hn
    by_contra hne
    exact hn (cutoff_effectSum_evenStep U q T out inp hne)
  · intro a
    rw [cutoff_grade_block]
    by_cases ha : allowed q a
    · rw [if_pos ha,grade_projection_eq]
      exact hdiag a.1.val a.2.val ha.1 ha.2
    · simpa [ha] using hL

end
end SRHT.SmallRowsGrade
