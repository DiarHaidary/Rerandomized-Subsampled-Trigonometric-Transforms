import SRHT.TwoSignRepresentation
import SRHT.ProjectionBounds

namespace SRHT.SignCompression
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix Cutoff ProjectionBounds TwoSignRepresentation Classical
variable {k d : ℕ}

def support (k d q : ℕ) : Finset (Fin d × SmallRows.SignPair (G k)) :=
  Finset.univ.filter fun z => z.2.1.card ≤ 2*q ∧ z.2.2.card ≤ 2*q

def projection (k d q : ℕ) : Matrix (Fin d × SmallRows.SignPair (G k))
    (Fin d × SmallRows.SignPair (G k)) ℝ := supportProjection (support k d q)

def effect (U : Matrix (G k) (Fin d) ℝ) (q : ℕ) (j : G k) :
    Matrix (Fin d × SmallRows.SignPair (G k)) (Fin d × SmallRows.SignPair (G k)) ℝ :=
  projection k d q * TwoSignRepresentation.effect U j * projection k d q

theorem effect_positive (U : Matrix (G k) (Fin d) ℝ) (q : ℕ) (j : G k) :
    (effect U q j).PosSemidef :=
  sandwich_positive _ _ (TwoSignRepresentation.effect_positive U j)

theorem effect_sum (U : Matrix (G k) (Fin d) ℝ) (q : ℕ) (hU : U.transpose*U=1) :
    ∑ j, effect U q j = projection k d q := by
  unfold effect
  rw [sandwich_sum,TwoSignRepresentation.effects_sum_one U hU,Matrix.mul_one]
  exact projection_sq _

theorem effect_sum_norm (U : Matrix (G k) (Fin d) ℝ) (q : ℕ) (hU : U.transpose*U=1) :
    ‖∑ j, effect U q j‖ ≤ 1 := by
  rw [effect_sum U q hU]
  exact projection_norm_le_one _

theorem effect_subset_gram (U : Matrix (G k) (Fin d) ℝ) (q : ℕ) (T : Finset (G k)) :
    (∑ j ∈ T, effect U q j) =
      (liftedFrame U T * projection k d q).transpose * (liftedFrame U T * projection k d q) := by
  unfold effect
  rw [sandwich_finset_sum,TwoSignRepresentation.effect_sum_gram,Matrix.transpose_mul]
  simp only [projection,projection_transpose,Matrix.mul_assoc]

theorem effect_subset_norm (U : Matrix (G k) (Fin d) ℝ) (q : ℕ) (T : Finset (G k)) :
    ‖∑ j ∈ T, effect U q j‖ = ‖liftedFrame U T * projection k d q‖^2 := by
  rw [effect_subset_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,pow_two] using
    Matrix.l2_opNorm_conjTranspose_mul_self (liftedFrame U T * projection k d q)

theorem effect_entry (U : Matrix (G k) (Fin d) ℝ) (q : ℕ)
    (j : G k) (out inp : Fin d × SmallRows.SignPair (G k)) :
    effect U q j out inp =
      if out ∈ support k d q ∧ inp ∈ support k d q then
        TwoSignRepresentation.effect U j out inp else 0 := by
  classical
  by_cases ho : out ∈ support k d q <;> by_cases hi : inp ∈ support k d q <;>
    simp [effect,projection,Cutoff.supportProjection,Matrix.diagonal_mul,Matrix.mul_diagonal,ho,hi]

end
end SRHT.SignCompression
