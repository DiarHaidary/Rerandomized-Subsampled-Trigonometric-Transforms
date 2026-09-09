import SRHT.TwoSignDecomposition
import SRHT.SmallRowsAssembly
import SRHT.TwoSignRepresentation
import SRHT.SmallRowsGrade

/-! The actual row-effect matrix and its finite-grade Gram norm. -/
namespace SRHT.SmallRows
open SRHT.HardCore SRHT.MatrixNorm
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {k d : ℕ}

theorem effect_diagonal_norm_eq_liftedFrame (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (T : Finset (WalshIndex k)) (r s : ℕ) :
    ‖rowGradeProjection r s * (∑ j ∈ T, TwoSignRepresentation.effect U j) *
      rowGradeProjection r s‖ =
      ‖TwoSignRepresentation.liftedFrame U T * rowGradeProjection r s‖^2 := by
  rw [TwoSignRepresentation.effect_sum_gram,norm_sq_eq_columnGram,
    Matrix.transpose_mul,rowGradeProjection_transpose]
  simp only [Matrix.mul_assoc]

theorem walsh_normalization_sq (k : ℕ) :
    ((Real.sqrt (Fintype.card (WalshIndex k):ℝ))⁻¹)^2 =
      1/(Fintype.card (WalshIndex k):ℝ) := by
  rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [one_div]

theorem normalized_matrix_norm_sq {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J ℝ) (k : ℕ) :
    ‖(Real.sqrt (Fintype.card (WalshIndex k):ℝ))⁻¹ • A‖^2 =
      ‖A‖^2/(Fintype.card (WalshIndex k):ℝ) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow,walsh_normalization_sq]
  ring

/-- The complete unnormalized four-channel estimate, with no assumed operator bound. -/
theorem raw_four_blocks_norm_sq_le (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (T : Finset (WalshIndex k)) (r s : ℕ) :
    ‖(rawRaising U T+rawMixedPM U T+rawMixedMP U T+collectedDouble U (walshModes T))*
      rowGradeProjection r s‖^2 ≤
      (d:ℝ)+3*(r-1:ℕ)+(r-1:ℕ)*(s-1:ℕ)+T.card*(s-1:ℕ)+
        T.card*((r+1:ℕ)*(s+1:ℕ)+(r+1:ℕ)*s+r*(s+1:ℕ)) := by
  have hA:=rawRaising_norm_sq_le U T r s
  have hB:=rawMixedPM_norm_sq_le U T r s 1 (by norm_num) (rowLeverage_le_one U hU)
  have hC:=rawMixedMP_norm_sq_le U T r s 1 (by norm_num) (rowLeverage_le_one U hU)
  have hD:=collectedDouble_isometry_norm_sq_le_all T U hU r s
  have hu : ‖U‖^2≤1 := by
    have h:=pow_le_pow_left₀ (norm_nonneg U) (isometry_norm_le_one U hU) 2
    simpa using h
  have hA' : ‖rawRaising U T*rowGradeProjection r s‖^2 ≤
      (T.card:ℝ)*(((r:ℝ)+1)*((s:ℝ)+1)) := hA.trans (by
    calc
      _ = ((T.card:ℝ)*((r:ℝ)+1)*((s:ℝ)+1))*‖U‖^2 := by ring
      _ ≤ ((T.card:ℝ)*((r:ℝ)+1)*((s:ℝ)+1))*1 :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      _ = _ := by ring)
  have hsum:=TwoSignDecomposition.four_blocks_norm_sq_le U T r s
  simp only [Matrix.add_mul]
  simp only [Fintype.card_fin] at hD
  push_cast
  nlinarith

/-- The actual finite-grade row-effect estimate. No randomization or operator norm
hypothesis is assumed: the only input-frame hypothesis is `Uᵀ U=I`. -/
theorem effect_diagonal_norm_le (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (q : ℕ) (hq : 1≤q) (T : Finset (WalshIndex k))
    (hT : T.card≤q) (r s : ℕ) (hr : r≤2*q) (hs : s≤2*q) :
    ‖rowGradeProjection r s*(∑ j∈T,TwoSignRepresentation.effect U j)*rowGradeProjection r s‖ ≤
      ((d:ℝ)+27*(q:ℝ)^3)/(Fintype.card (WalshIndex k):ℝ) := by
  rw [effect_diagonal_norm_eq_liftedFrame,TwoSignDecomposition.liftedFrame_decomposition,
    Matrix.smul_mul,normalized_matrix_norm_sq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (raw_four_blocks_norm_sq_le U hU T r s).trans (small_row_cost_le d T.card r s q hq hr hs hT)

/-- The decisive deterministic small-set estimate on the complete low-sign cutoff. -/
theorem sign_cutoff_small_rows_norm_le (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (hU : U.transpose*U=1) (q : ℕ) (hq : 1≤q) (T : Finset (WalshIndex k)) (hT : T.card≤q) :
    ‖∑ j∈T,SignCompression.effect U q j‖ ≤
      9*(((d:ℝ)+27*(q:ℝ)^3)/(Fintype.card (WalshIndex k):ℝ)) := by
  apply SmallRowsGrade.sign_cutoff_norm_le_of_diagonal U q T (by positivity)
  intro r s hr hs
  exact effect_diagonal_norm_le U hU q hq T hT r s hr hs

end
end SRHT.SmallRows

