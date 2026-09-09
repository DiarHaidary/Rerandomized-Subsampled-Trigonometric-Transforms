import SRHT.TwoSignRepresentation
import SRHT.SmallRowsLinearBands
import SRHT.SmallRowsAssembly

namespace SRHT.TwoSignDecomposition
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open HardCore SmallRows TwoSignRepresentation Matrix
variable {k d : ℕ}

theorem walsh_product (j a i : G k) :
    walshMatrix k j a * walshMatrix k a i =
      (Real.sqrt (Fintype.card (G k):ℝ))⁻¹ * walshMatrix k (j+i) a := by
  simp only [walshMatrix,walshChar_add_left]
  rw [walshChar_comm a i]
  ring

theorem liftedFrame_decomposition (U : Matrix (G k) (Fin d) ℝ) (T : Finset (G k)) :
    liftedFrame U T = (Real.sqrt (Fintype.card (G k):ℝ))⁻¹ •
      (rawRaising U T + rawMixedPM U T + rawMixedMP U T + collectedDouble U (walshModes T)) := by
  ext out inp
  rw [liftedFrame_apply,Finset.sum_comm]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,rawRaising,rawMixedPM,rawMixedMP,
    raisingBlock,mixedBlock,raisingCoefficient,mixedCoefficient,collectedDouble,
    annihilateMode,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,walshModes]
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [walsh_product]
  simp only [TwoSignRepresentation.flip,Matrix.add_apply]
  ring

def Signature
    (A : Matrix (RowSign T (G k)) (Fin d × SignPair (G k)) ℝ)
    (r s : ℕ) (dx dy : ℤ) : Prop :=
  ∀ out inp, A out inp≠0 →
    (out.2.1.card:ℤ)=(r:ℤ)+dx ∧ (out.2.2.card:ℤ)=(s:ℤ)+dy

theorem signature_restricted {T : Finset (G k)}
    (A : Matrix (RowSign T (G k)) (Fin d × SignPair (G k)) ℝ)
    (r s : ℕ) (dx dy : ℤ)
    (hA : ∀ out inp, A out inp≠0 →
      (out.2.1.card:ℤ)=(inp.2.1.card:ℤ)+dx ∧ (out.2.2.card:ℤ)=(inp.2.2.card:ℤ)+dy) :
    Signature (A*rowGradeProjection r s) r s dx dy := by
  intro out inp h
  rw [mul_rowGradeProjection_apply] at h
  by_cases hg : inp.2.1.card=r ∧ inp.2.2.card=s
  · rw [if_pos hg] at h
    simpa only [hg.1,hg.2] using hA out inp h
  · simp [hg] at h

theorem signatures_orthogonal {T : Finset (G k)}
    (A B : Matrix (RowSign T (G k)) (Fin d × SignPair (G k)) ℝ)
    (r s : ℕ) (dx dy ex ey : ℤ) (hA : Signature A r s dx dy) (hB : Signature B r s ex ey)
    (hne : dx≠ex ∨ dy≠ey) : A.transpose*B=0 := by
  ext j l
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro out _
  by_cases ha : A out j=0
  · simp [ha]
  by_cases hb : B out l=0
  · simp [hb]
  have h1 := hA out j ha
  have h2 := hB out l hb
  exfalso
  rcases hne with hx|hy <;> omega

theorem four_blocks_norm_sq_le (U : Matrix (G k) (Fin d) ℝ) (T : Finset (G k)) (r s : ℕ) :
    ‖rawRaising U T*rowGradeProjection r s + rawMixedPM U T*rowGradeProjection r s +
      rawMixedMP U T*rowGradeProjection r s + collectedDouble U (walshModes T)*rowGradeProjection r s‖^2 ≤
    ‖rawRaising U T*rowGradeProjection r s‖^2 + ‖rawMixedPM U T*rowGradeProjection r s‖^2 +
      ‖rawMixedMP U T*rowGradeProjection r s‖^2 + ‖collectedDouble U (walshModes T)*rowGradeProjection r s‖^2 := by
  have hA : Signature (rawRaising U T*rowGradeProjection r s) r s 1 1 := by
    apply signature_restricted
    intro out inp h
    have hc := rawRaising_card U T out inp h
    constructor <;> omega
  have hB : Signature (rawMixedPM U T*rowGradeProjection r s) r s 1 (-1) := by
    apply signature_restricted
    intro out inp h
    have hc := rawMixedPM_card U T out inp h
    constructor <;> omega
  have hC : Signature (rawMixedMP U T*rowGradeProjection r s) r s (-1) 1 := by
    apply signature_restricted
    intro out inp h
    have hc := rawMixedMP_card U T out inp h
    constructor <;> omega
  have hD : Signature (collectedDouble U (walshModes T)*rowGradeProjection r s) r s (-1) (-1) := by
    apply signature_restricted
    intro out inp h
    have hc := collectedDouble_card U (walshModes T) out inp h
    constructor <;> omega
  exact four_block_norm_sq_le _ _ _ _
    (signatures_orthogonal _ _ r s _ _ _ _ hA hB (by norm_num))
    (signatures_orthogonal _ _ r s _ _ _ _ hA hC (by norm_num))
    (signatures_orthogonal _ _ r s _ _ _ _ hA hD (by norm_num))
    (signatures_orthogonal _ _ r s _ _ _ _ hB hC (by norm_num))
    (signatures_orthogonal _ _ r s _ _ _ _ hB hD (by norm_num))
    (signatures_orthogonal _ _ r s _ _ _ _ hC hD (by norm_num))

end
end SRHT.TwoSignDecomposition
