import SRHT.SmallRows
import SRHT.SmallRowsMixed
import SRHT.MatrixNorm

/-! Actual two-particle occupation lifts and their quantitative grade bounds. -/
namespace SRHT.SmallRows
open SRHT.HardCore SRHT.MatrixNorm
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

variable {G R : Type*} [Fintype G] [DecidableEq G] [Fintype R] [DecidableEq R]

def twoGradeProjection (p q : ℕ) : TwoOp G :=
  Matrix.kronecker (gradeProjection p) (gradeProjection q)

def rowGradeProjection (p q : ℕ) : Matrix (RowSign R G) (RowSign R G) ℝ :=
  amplifyLeft (twoGradeProjection p q)

def extractionShuffle : ((R × G × G) × SignPair G) ≃
    R × ((G × Finset G) × (G × Finset G)) where
  toFun z := (z.1.1, ((z.1.2.1,z.2.1),(z.1.2.2,z.2.2)))
  invFun z := ((z.1,z.2.1.1,z.2.2.1),(z.2.1.2,z.2.2.2))
  left_inv := by rintro ⟨⟨j,i,a⟩,S,Q⟩; rfl
  right_inv := by rintro ⟨j,⟨i,S⟩,a,Q⟩; rfl

def doubleExtraction (p q : ℕ) :
    Matrix ((R × G × G) × SignPair G) (RowSign R G) ℝ :=
  (amplifyLeft (K := R) (Matrix.kronecker (gradeExtraction p) (gradeExtraction q))).submatrix
    extractionShuffle (Equiv.refl _)

theorem doubleExtraction_norm_sq_le (p q : ℕ) :
    ‖doubleExtraction (R := R) (G := G) p q‖ ^ 2 ≤ (p : ℝ) * q := by
  have hd : ‖doubleExtraction (R := R) (G := G) p q‖ ≤
      ‖gradeExtraction (G := G) p‖ * ‖gradeExtraction (G := G) q‖ := by
    unfold doubleExtraction
    rw [submatrix_equiv_norm]
    exact (amplifyLeft_norm_le _).trans (kronecker_norm_le _ _)
  have hdsq := pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [mul_pow] at hdsq
  exact hdsq.trans (mul_le_mul (gradeExtraction_norm_sq_le p)
    (gradeExtraction_norm_sq_le q) (sq_nonneg _) (Nat.cast_nonneg _))

def occupationLift (K : Matrix (R × G × G) (R × G × G) ℝ) (p q : ℕ) :
    Matrix (RowSign R G) (RowSign R G) ℝ :=
  (doubleExtraction p q).transpose * amplifyRight (K := SignPair G) K * doubleExtraction p q

theorem occupationLift_norm_le (K : Matrix (R × G × G) (R × G × G) ℝ) (p q : ℕ) :
    ‖occupationLift K p q‖ ≤ (p : ℝ) * q * ‖K‖ := by
  have ht : ‖(doubleExtraction (R := R) (G := G) p q).transpose‖ =
      ‖doubleExtraction (R := R) (G := G) p q‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (doubleExtraction (R := R) (G := G) p q)
  unfold occupationLift
  calc
    _ ≤ (‖(doubleExtraction (R := R) (G := G) p q).transpose‖ *
          ‖amplifyRight (K := SignPair G) K‖) * ‖doubleExtraction (R := R) (G := G) p q‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ = ‖doubleExtraction (R := R) (G := G) p q‖ ^ 2 *
          ‖amplifyRight (K := SignPair G) K‖ := by rw [ht]; ring
    _ ≤ ((p : ℝ) * q) * ‖K‖ :=
      mul_le_mul (doubleExtraction_norm_sq_le p q) (amplifyRight_norm_le K)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

def rawDoubleExtraction :
    Matrix ((R × G × G) × SignPair G) (RowSign R G) ℝ :=
  (amplifyLeft (K := R) (Matrix.kronecker (extraction (G := G)) (extraction (G := G)))).submatrix
    extractionShuffle (Equiv.refl _)

theorem rawDoubleExtraction_apply (out : (R × G × G) × SignPair G) (inp : RowSign R G) :
    rawDoubleExtraction out inp = if out.1.1 = inp.1 then
      annihilate out.1.2.1 out.2.1 inp.2.1 * annihilate out.1.2.2 out.2.2 inp.2.2 else 0 := rfl

theorem rowGradeProjection_apply (p q : ℕ) (out inp : RowSign R G) :
    rowGradeProjection p q out inp = if out = inp then
      if out.2.1.card = p ∧ out.2.2.card = q then 1 else 0 else 0 := by
  classical
  simp only [rowGradeProjection, amplifyLeft, twoGradeProjection, Matrix.kronecker,
    Matrix.kroneckerMap, gradeProjection, Matrix.diagonal_apply]
  by_cases hj : out.1 = inp.1 <;> by_cases hx : out.2.1 = inp.2.1 <;>
    by_cases hy : out.2.2 = inp.2.2 <;>
    simp [hj,hx,hy,Prod.ext_iff,ite_and] <;> split_ifs <;> rfl

theorem doubleExtraction_eq_raw_mul (p q : ℕ) :
    doubleExtraction (R := R) (G := G) p q =
      rawDoubleExtraction * rowGradeProjection p q := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, rowGradeProjection_apply, mul_ite, mul_zero,
    Fintype.sum_ite_eq']
  simp only [doubleExtraction, Matrix.submatrix_apply, amplifyLeft, Matrix.kronecker,
    Matrix.kroneckerMap, extractionShuffle, Equiv.refl_apply, gradeExtraction,
    Matrix.mul_diagonal, gradeProjection, extraction, rawDoubleExtraction_apply]
  by_cases hj : out.1.1 = inp.1 <;> by_cases hp : inp.2.1.card = p <;>
    by_cases hq : inp.2.2.card = q <;> simp [hj,hp,hq]

theorem rowGradeProjection_transpose (p q : ℕ) :
    (rowGradeProjection (R := R) (G := G) p q).transpose = rowGradeProjection p q := by
  classical
  ext out inp
  simp only [Matrix.transpose_apply,rowGradeProjection_apply]
  by_cases h : out = inp
  · subst inp; rfl
  · simp [h,Ne.symm h]

def rawOccupationLift (K : Matrix (R × G × G) (R × G × G) ℝ) :
    Matrix (RowSign R G) (RowSign R G) ℝ :=
  rawDoubleExtraction.transpose * amplifyRight (K := SignPair G) K * rawDoubleExtraction

theorem occupationLift_eq_compression (K : Matrix (R × G × G) (R × G × G) ℝ) (p q : ℕ) :
    occupationLift K p q = rowGradeProjection p q * rawOccupationLift K * rowGradeProjection p q := by
  unfold occupationLift rawOccupationLift
  rw [doubleExtraction_eq_raw_mul, Matrix.transpose_mul, rowGradeProjection_transpose]
  simp only [Matrix.mul_assoc]

theorem rawOccupationLift_apply (K : Matrix (R × G × G) (R × G × G) ℝ)
    (out inp : RowSign R G) :
    rawOccupationLift K out inp =
      ∑ i, ∑ a, ∑ l, ∑ b, K (out.1,i,a) (inp.1,l,b) *
        (create i * annihilate l) out.2.1 inp.2.1 *
        (create a * annihilate b) out.2.2 inp.2.2 := by
  classical
  simp only [rawOccupationLift,Matrix.mul_apply,Matrix.transpose_apply,
    rawDoubleExtraction_apply,amplifyRight,Fintype.sum_prod_type,
    ite_mul,mul_ite,zero_mul,mul_zero]
  simp only [Prod.mk.injEq, ite_and, Fintype.sum_ite_eq', Fintype.sum_ite_eq, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [← annihilate_transpose]
  simp only [Matrix.transpose_apply]
  let e : (G × G × Finset G × Finset G × G × G) ≃
      (G × G × G × G × Finset G × Finset G) :=
    { toFun := fun ⟨l,b,S,Q,i,a⟩ => ⟨i,a,l,b,Q,S⟩
      invFun := fun ⟨i,a,l,b,Q,S⟩ => ⟨l,b,S,Q,i,a⟩
      left_inv := by rintro ⟨l,b,S,Q,i,a⟩; rfl
      right_inv := by rintro ⟨i,a,l,b,S,Q⟩; rfl }
  have he := Fintype.sum_equiv e
    (fun ⟨l,b,S,Q,i,a⟩ =>
      (annihilate i S out.2.1 * annihilate a Q out.2.2 * K (out.1,i,a) (inp.1,l,b)) *
      (annihilate l S inp.2.1 * annihilate b Q inp.2.2))
    (fun ⟨i,a,l,b,Q,S⟩ =>
      (K (out.1,i,a) (inp.1,l,b) * (annihilate i S out.2.1 * annihilate l S inp.2.1)) *
      (annihilate a Q out.2.2 * annihilate b Q inp.2.2))
    (by rintro ⟨l,b,S,Q,i,a⟩; dsimp [e]; ring)
  simpa only [Fintype.sum_prod_type] using he

theorem mixedTransfer_eq_rawLift {k : ℕ} (T : Finset (WalshIndex k))
    (P : Matrix (WalshIndex k) (WalshIndex k) ℝ) :
    mixedTransfer P (walshModes T) = rawOccupationLift (SmallRowsMixed.kernel T P) := by
  classical
  ext out inp
  rw [rawOccupationLift_apply]
  simp only [mixedTransfer,tensor,walshModes,createMode,annihilateMode]
  simp_rw [sum_smul_mul_sum_smul]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,SmallRowsMixed.kernel]
  simp_rw [Finset.mul_sum]
  let e : ((WalshIndex k) × (WalshIndex k) × (WalshIndex k) × (WalshIndex k)) ≃
      ((WalshIndex k) × (WalshIndex k) × (WalshIndex k) × (WalshIndex k)) :=
    { toFun := fun ⟨l,i,a,b⟩ => ⟨i,a,l,b⟩
      invFun := fun ⟨i,a,l,b⟩ => ⟨l,i,a,b⟩
      left_inv := by rintro ⟨l,i,a,b⟩; rfl
      right_inv := by rintro ⟨i,a,l,b⟩; rfl }
  have he := Fintype.sum_equiv e
    (fun ⟨l,i,a,b⟩ => P l i * ((create i * annihilate l) out.2.1 inp.2.1 *
      ((walshMatrix k (inp.1.1+i) a * walshMatrix k (out.1.1+l) b) *
        (create a * annihilate b) out.2.2 inp.2.2)))
    (fun ⟨i,a,l,b⟩ => (P l i * walshMatrix k (inp.1.1+i) a * walshMatrix k (out.1.1+l) b) *
      (create i * annihilate l) out.2.1 inp.2.1 * (create a * annihilate b) out.2.2 inp.2.2)
    (by rintro ⟨l,i,a,b⟩; dsimp [e]; ring)
  simpa only [Fintype.sum_prod_type] using he

/-- The actual mixed normal-order term costs exactly the two occupied grades. -/
theorem mixedTransfer_compressed_norm_le {k : ℕ} (T : Finset (WalshIndex k))
    (P : Matrix (WalshIndex k) (WalshIndex k) ℝ) (p q : ℕ) :
    ‖rowGradeProjection p q * mixedTransfer P (walshModes T) * rowGradeProjection p q‖ ≤
      (p : ℝ) * q * ‖P‖ := by
  rw [mixedTransfer_eq_rawLift, ← occupationLift_eq_compression]
  exact (occupationLift_norm_le _ p q).trans
    (mul_le_mul_of_nonneg_left (SmallRowsMixed.kernel_norm_le T P)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

end
end SRHT.SmallRows








