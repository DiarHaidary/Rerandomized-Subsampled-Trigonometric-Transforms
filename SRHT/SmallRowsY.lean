import SRHT.SmallRowsX
import SRHT.SmallRowsE
import SRHT.SmallRowsLift

/-! The reflected y-transfer kernel: row analysis, register exchange, and synthesis. -/
namespace SRHT.SmallRowsY
open SRHT.HardCore SRHT.MatrixNorm SRHT.SmallRows
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {k : ℕ}
local notation "G" => WalshIndex k

abbrev KernelIndex (T : Finset G) := (T × G) × Finset G
abbrev AnalysisIndex (T : Finset G) := (G × T × T) × Finset G

def analysis (T : Finset G) : Matrix (AnalysisIndex T) (KernelIndex T) ℝ :=
  fun out inp => if out.2 = inp.2 then
    if out.1.2.1 = inp.1.1 then walshMatrix k (out.1.2.2.1 + out.1.1) inp.1.2 else 0
  else 0

def exchange (T : Finset G) : AnalysisIndex T ≃ AnalysisIndex T where
  toFun z := ((z.1.1,z.1.2.2,z.1.2.1),z.2)
  invFun z := ((z.1.1,z.1.2.2,z.1.2.1),z.2)
  left_inv := by rintro ⟨⟨i,j,l⟩,S⟩; rfl
  right_inv := by rintro ⟨⟨i,j,l⟩,S⟩; rfl

def middle (T : Finset G) (ell : G → ℝ) : Matrix (AnalysisIndex T) (AnalysisIndex T) ℝ :=
  (Matrix.diagonal fun out : AnalysisIndex T => ell out.1.1 * siteSign out.1.1 out.2).submatrix
    (Equiv.refl _) (exchange T)

def kernel (T : Finset G) (ell : G → ℝ) : Matrix (KernelIndex T) (KernelIndex T) ℝ :=
  fun out inp => if out.2 = inp.2 then
    ∑ i, ell i * siteSign i out.2 *
      walshMatrix k (inp.1.1.1+i) out.1.2 * walshMatrix k (out.1.1.1+i) inp.1.2
  else 0

theorem shift_inner (j a b : G) :
    (∑ i, walshMatrix k (j+i) a * walshMatrix k (j+i) b) = if a=b then 1 else 0 := by
  have hs := Equiv.sum_comp (Equiv.addLeft j) (fun i => walshMatrix k i a * walshMatrix k i b)
  have hw := congrArg (fun M : Matrix G G ℝ => M a b) (walshMatrix_transpose_mul k)
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] at hw
  exact hs.trans hw

theorem analysis_gram (T : Finset G) :
    (analysis T).transpose * analysis T = (T.card : ℝ) • (1 : Matrix (KernelIndex T) (KernelIndex T) ℝ) := by
  classical
  ext ⟨⟨j,a⟩,S⟩ ⟨⟨l,b⟩,Q⟩
  simp only [analysis,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    ite_mul,mul_ite,zero_mul,mul_zero,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  simp only [Fintype.sum_ite_eq',Fintype.sum_ite_eq,Finset.sum_ite_irrel,Finset.sum_const_zero]
  by_cases hS : S=Q <;> by_cases hj : j=l
  · subst Q; subst l
    simp only [ite_true]
    rw [Finset.sum_comm]
    simp only [shift_inner,Finset.sum_const,nsmul_eq_mul,Fintype.card_coe]
    simp
  · simp [hj,Ne.symm hj,hS,Prod.ext_iff]
  · simp [hS,Ne.symm hS,Prod.ext_iff]
  · simp [hS,Ne.symm hS,Prod.ext_iff]

theorem analysis_norm_sq_le (T : Finset G) : ‖analysis T‖^2 ≤ (T.card : ℝ) := by
  have hg := Matrix.l2_opNorm_conjTranspose_mul_self (analysis T)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,analysis_gram,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)] at hg
  have hI : ‖(1 : Matrix (KernelIndex T) (KernelIndex T) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun _ => by simp)
  nlinarith

theorem middle_norm_le (T : Finset G) (ell : G → ℝ) (mu : ℝ) (hmu : 0≤mu)
    (hell : ∀ i, ‖ell i‖≤mu) : ‖middle T ell‖≤mu := by
  unfold middle
  rw [submatrix_equiv_norm,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hmu).2
  intro out
  simpa only [norm_mul,siteSign_norm,mul_one] using hell out.1.1

theorem kernel_factorization (T : Finset G) (ell : G → ℝ) :
    kernel T ell = (analysis T).transpose * middle T ell * analysis T := by
  classical
  ext ⟨⟨j,a⟩,S⟩ ⟨⟨l,b⟩,Q⟩
  simp only [kernel,analysis,middle,exchange,Matrix.submatrix_apply,Equiv.refl_apply,Equiv.coe_fn_mk,
    Matrix.mul_apply,Matrix.transpose_apply,Matrix.diagonal_apply,Fintype.sum_prod_type,
    ite_mul,mul_ite,zero_mul,mul_zero]
  simp only [Prod.mk.injEq,ite_and,Fintype.sum_ite_eq',Fintype.sum_ite_eq,
    Finset.sum_ite_irrel,Finset.sum_const_zero]
  by_cases hS : S=Q
  · subst Q
    simp only [ite_true]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ite_mul,zero_mul,Fintype.sum_ite_eq']
    ring
  · simp [hS,Ne.symm hS]

theorem kernel_norm_le (T : Finset G) (ell : G → ℝ) (mu : ℝ) (hmu : 0≤mu)
    (hell : ∀ i, ‖ell i‖≤mu) : ‖kernel T ell‖ ≤ mu * T.card := by
  classical
  letI : Fintype (KernelIndex T) := inferInstance
  letI : Fintype (AnalysisIndex T) := inferInstance
  rw [kernel_factorization]
  have ht : ‖(analysis T).transpose‖=‖analysis T‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (analysis T)
  calc
    _ ≤ (‖(analysis T).transpose‖ * ‖middle T ell‖) * ‖analysis T‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ = ‖analysis T‖^2 * ‖middle T ell‖ := by rw [ht]; ring
    _ ≤ (T.card : ℝ) * mu := mul_le_mul (analysis_norm_sq_le T)
      (middle_norm_le T ell mu hmu hell) (norm_nonneg _) (Nat.cast_nonneg _)
    _ = mu * T.card := by ring

def signExchange (T : Finset G) : RowSign T G ≃ RowSign T G where
  toFun z := (z.1,z.2.2,z.2.1)
  invFun z := (z.1,z.2.2,z.2.1)
  left_inv := by rintro ⟨j,S,Q⟩; rfl
  right_inv := by rintro ⟨j,S,Q⟩; rfl

theorem rowGradeProjection_exchange (T : Finset G) (p q : ℕ) :
    (rowGradeProjection (R:=T) q p).submatrix (signExchange T) (signExchange T) =
      rowGradeProjection p q := by
  classical
  ext out inp
  simp only [Matrix.submatrix_apply,rowGradeProjection_apply,signExchange,Equiv.coe_fn_mk]
  by_cases h : out=inp
  · subst inp
    simp [and_comm]
  · have he : (out.1,out.2.2,out.2.1) ≠ (inp.1,inp.2.2,inp.2.1) := by
      intro hh
      apply h
      exact (signExchange T).injective hh
    simp [h,he]

theorem yTransfer_eq_singleLift (T : Finset G) (P : Matrix G G ℝ) :
    yTransfer P (walshModes T) =
      (rawSingleLift (kernel T (fun i => P i i))).submatrix (signExchange T) (signExchange T) := by
  classical
  ext out inp
  simp only [Matrix.submatrix_apply,rawSingleLift_apply,signExchange,Equiv.coe_fn_mk,
    yTransfer,tensor,localCorrection_entry,walshModes,kernel]
  by_cases hs : out.2.1=inp.2.1
  · simp only [hs,ite_true,and_true,ite_mul,mul_ite,zero_mul,mul_zero,
      Fintype.sum_ite_eq]
    simp only [createMode,annihilateMode]
    simp_rw [sum_smul_mul_sum_smul]
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    let e : (G × G × G) ≃ (G × G × G) :=
      { toFun := fun ⟨i,a,b⟩ => ⟨a,b,i⟩
        invFun := fun ⟨a,b,i⟩ => ⟨i,a,b⟩
        left_inv := by rintro ⟨i,a,b⟩; rfl
        right_inv := by rintro ⟨a,b,i⟩; rfl }
    have he := Fintype.sum_equiv e
      (fun ⟨i,a,b⟩ => P i i * (siteSign i inp.2.1 *
        ((walshMatrix k (inp.1.1+i) a * walshMatrix k (out.1.1+i) b) *
          (create a * annihilate b) out.2.2 inp.2.2)))
      (fun ⟨a,b,i⟩ =>
        (P i i * siteSign i inp.2.1 * walshMatrix k (inp.1.1+i) a *
          walshMatrix k (out.1.1+i) b) * (create a * annihilate b) out.2.2 inp.2.2)
      (by rintro ⟨i,a,b⟩; dsimp [e]; ring)
    simpa only [Fintype.sum_prod_type,walshModes] using he
  · simp [hs]

/-- The actual y-transfer term costs only its occupied y-grade and the selected row count. -/
theorem yTransfer_compressed_norm_le (T : Finset G) (P : Matrix G G ℝ)
    (mu : ℝ) (hmu : 0≤mu) (hell : ∀ i, ‖P i i‖≤mu) (p q : ℕ) :
    ‖rowGradeProjection p q * yTransfer P (walshModes T) * rowGradeProjection p q‖ ≤
      mu * T.card * q := by
  classical
  have he : rowGradeProjection p q * yTransfer P (walshModes T) * rowGradeProjection p q =
      (singleLift (kernel T (fun i => P i i)) q p).submatrix (signExchange T) (signExchange T) := by
    rw [singleLift_eq_compression,yTransfer_eq_singleLift,
      ← rowGradeProjection_exchange T p q]
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rw [he,submatrix_equiv_norm]
  calc
    _ ≤ (q : ℝ) * ‖kernel T (fun i => P i i)‖ := singleLift_norm_le _ q p
    _ ≤ (q : ℝ) * (mu*T.card) :=
      mul_le_mul_of_nonneg_left (kernel_norm_le T _ mu hmu hell) (Nat.cast_nonneg _)
    _ = mu*T.card*q := by ring

end
end SRHT.SmallRowsY




