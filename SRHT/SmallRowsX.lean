import SRHT.SmallRowsE
import SRHT.SmallRowsLift
import SRHT.MatrixNorm
import SRHT.Model

/-! Exact one-particle contractions for the X and F normal-order terms. -/

namespace SRHT.SmallRows
open SRHT.HardCore SRHT.MatrixNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section

section WalshKernel

variable {k : ℕ}
local notation "G" => WalshIndex k

/-- Fourier analysis in the row register, with a character twist at the x-site. -/
def xAnalysis (T : Finset G) :
    Matrix ((G × Finset G) × G) ((T × G) × Finset G) ℝ :=
  fun out inp => if inp.2=out.1.2 then if inp.1.2=out.2 then
    walshChar out.2 out.1.1 * walshMatrix k inp.1.1.val out.1.1 else 0 else 0

theorem xAnalysis_gram (T : Finset G) : (xAnalysis T)ᵀ * xAnalysis T = 1 := by
  classical
  ext ⟨⟨j,i⟩,S⟩ ⟨⟨l,b⟩,Q⟩
  simp only [xAnalysis, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    ite_mul, mul_ite, zero_mul, mul_zero]
  by_cases hS : S=Q <;> by_cases hi : i=b
  · subst Q
    subst b
    have ht (a : G) :
        walshChar i a * walshMatrix k j.val a * (walshChar i a * walshMatrix k l.val a) =
        walshMatrix k j.val a * walshMatrix k l.val a := by
      calc
        _ = walshChar i a ^ 2 * (walshMatrix k j.val a * walshMatrix k l.val a) := by ring
        _ = _ := by rw [walshChar_sq]; ring
    simp [ht, walshMatrix_orthogonal, Matrix.one_apply]
  · simp [hS,hi,Matrix.one_apply]
  · simp [hS,hi,Matrix.one_apply]
  · simp [hS,hi,Matrix.one_apply]

theorem xAnalysis_norm_le_one (T : Finset G) : ‖xAnalysis T‖ ≤ 1 :=
  isometry_norm_le_one (xAnalysis T) (xAnalysis_gram T)

def xMiddle (P : Matrix G G ℝ) (h : G → Finset G → ℝ) :
    Matrix ((G × Finset G) × G) ((G × Finset G) × G) ℝ :=
  Matrix.diagonal (fun out => h out.1.1 out.1.2) * amplifyLeft Pᵀ

theorem xMiddle_apply (P : Matrix G G ℝ) (h : G → Finset G → ℝ)
    (out inp : (G × Finset G) × G) :
    xMiddle P h out inp = if out.1=inp.1 then h out.1.1 out.1.2 * P inp.2 out.2 else 0 := by
  simp [xMiddle,Matrix.diagonal_mul,amplifyLeft,Matrix.transpose_apply]

theorem xMiddle_norm_le (P : Matrix G G ℝ) (h : G → Finset G → ℝ)
    (C : ℝ) (hC : 0≤C) (hh : ∀ a S, ‖h a S‖≤C) : ‖xMiddle P h‖ ≤ C * ‖P‖ := by
  have hd : ‖Matrix.diagonal (fun out : (G × Finset G) × G => h out.1.1 out.1.2)‖ ≤ C := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hC).2 (fun out => hh _ _)
  have ht : ‖Pᵀ‖=‖P‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose P
  unfold xMiddle
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hd ((amplifyLeft_norm_le Pᵀ).trans_eq ht) (norm_nonneg _) hC)

def xKernel (T : Finset G) (P : Matrix G G ℝ) (h : G → Finset G → ℝ) :
    Matrix ((T × G) × Finset G) ((T × G) × Finset G) ℝ :=
  (xAnalysis T)ᵀ * xMiddle P h * xAnalysis T

theorem xKernel_norm_le (T : Finset G) (P : Matrix G G ℝ) (h : G → Finset G → ℝ)
    (C : ℝ) (hC : 0≤C) (hh : ∀ a S, ‖h a S‖≤C) : ‖xKernel T P h‖ ≤ C * ‖P‖ := by
  have hb := xAnalysis_norm_le_one T
  have ht : ‖(xAnalysis T)ᵀ‖≤1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose (xAnalysis T)).trans_le hb
  have hm := xMiddle_norm_le P h C hC hh
  unfold xKernel
  calc
    _ ≤ (‖(xAnalysis T)ᵀ‖ * ‖xMiddle P h‖) * ‖xAnalysis T‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * (C*‖P‖)) * 1 := by gcongr
    _ = _ := by ring

theorem xKernel_apply (T : Finset G) (P : Matrix G G ℝ) (h : G → Finset G → ℝ)
    (out inp : (T × G) × Finset G) :
    xKernel T P h out inp = if out.2=inp.2 then
      P inp.1.2 out.1.2 * ∑ a, h a out.2 *
        walshMatrix k (out.1.1.val+inp.1.2) a *
        walshMatrix k (inp.1.1.val+out.1.2) a else 0 := by
  classical
  rcases out with ⟨⟨j,i⟩,S⟩
  rcases inp with ⟨⟨l,b⟩,Q⟩
  unfold xKernel
  simp only [Matrix.mul_apply, Matrix.transpose_apply,xMiddle_apply,
    xAnalysis, amplifyLeft, Fintype.sum_prod_type]
  by_cases hS : S=Q
  · subst Q
    simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, zero_mul, mul_zero,
      Fintype.sum_ite_eq, Fintype.sum_ite_eq', Finset.sum_ite_irrel,
      Finset.sum_const_zero, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [walshMatrix,walshChar_add_left]
    ring
  · simp [hS,Ne.symm hS,ite_and]

end WalshKernel

section SingleLift

variable {V R : Type*} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]

def singleExtractionShuffle : (((R × V) × Finset V) × Finset V) ≃
    R × ((V × Finset V) × Finset V) where
  toFun z := (z.1.1.1,((z.1.1.2,z.2),z.1.2))
  invFun z := (((z.1,z.2.1.1),z.2.2),z.2.1.2)
  left_inv := by rintro ⟨⟨⟨j,i⟩,Q⟩,S⟩; rfl
  right_inv := by rintro ⟨j,⟨i,S⟩,Q⟩; rfl

def singleExtraction (p q : ℕ) :
    Matrix (((R × V) × Finset V) × Finset V) (RowSign R V) ℝ :=
  (amplifyLeft (K:=R) (Matrix.kronecker (gradeExtraction p) (gradeProjection q))).submatrix
    singleExtractionShuffle (Equiv.refl _)

theorem singleExtraction_norm_sq_le (p q : ℕ) :
    ‖singleExtraction (R:=R) (V:=V) p q‖^2 ≤ (p:ℝ) := by
  have he : ‖singleExtraction (R:=R) (V:=V) p q‖ ≤ ‖gradeExtraction (G:=V) p‖ := by
    unfold singleExtraction
    rw [submatrix_equiv_norm]
    calc
      _ ≤ ‖gradeExtraction (G:=V) p‖ * ‖gradeProjection (G:=V) q‖ :=
        (amplifyLeft_norm_le _).trans (kronecker_norm_le _ _)
      _ ≤ ‖gradeExtraction (G:=V) p‖ * 1 :=
        mul_le_mul_of_nonneg_left (gradeProjection_norm_le_one q) (norm_nonneg _)
      _ = _ := mul_one _
  exact (pow_le_pow_left₀ (norm_nonneg _) he 2).trans (gradeExtraction_norm_sq_le p)

def rawSingleExtraction :
    Matrix (((R × V) × Finset V) × Finset V) (RowSign R V) ℝ :=
  (amplifyLeft (K:=R) (Matrix.kronecker (extraction (G:=V)) (1:HardCore.Op V))).submatrix
    singleExtractionShuffle (Equiv.refl _)

theorem rawSingleExtraction_apply (out : ((R × V) × Finset V) × Finset V)
    (inp : RowSign R V) :
    rawSingleExtraction out inp = if out.1.1.1=inp.1 then
      if out.1.2=inp.2.2 then annihilate out.1.1.2 out.2 inp.2.1 else 0 else 0 := by
  simp [rawSingleExtraction,Matrix.submatrix_apply,amplifyLeft,Matrix.kronecker,
    Matrix.kroneckerMap,singleExtractionShuffle,extraction,Matrix.one_apply]

theorem singleExtraction_eq_raw_mul (p q : ℕ) :
    singleExtraction (R:=R) (V:=V) p q = rawSingleExtraction * rowGradeProjection p q := by
  classical
  ext out inp
  simp only [Matrix.mul_apply,rowGradeProjection_apply,mul_ite,mul_zero,Fintype.sum_ite_eq']
  simp only [singleExtraction,Matrix.submatrix_apply,amplifyLeft,Matrix.kronecker,
    Matrix.kroneckerMap,singleExtractionShuffle,Equiv.refl_apply,gradeExtraction,
    Matrix.mul_diagonal,gradeProjection,extraction,Matrix.diagonal_apply,
    rawSingleExtraction_apply]
  by_cases hj : out.1.1.1=inp.1 <;> by_cases hY : out.1.2=inp.2.2 <;>
    by_cases hp : inp.2.1.card=p <;> by_cases hq : inp.2.2.card=q <;> simp [hj,hY,hp,hq]

def rawSingleLift (K : Matrix ((R × V) × Finset V) ((R × V) × Finset V) ℝ) :
    Matrix (RowSign R V) (RowSign R V) ℝ :=
  rawSingleExtractionᵀ * amplifyRight (K:=Finset V) K * rawSingleExtraction

def singleLift (K : Matrix ((R × V) × Finset V) ((R × V) × Finset V) ℝ) (p q : ℕ) :
    Matrix (RowSign R V) (RowSign R V) ℝ :=
  (singleExtraction p q)ᵀ * amplifyRight (K:=Finset V) K * singleExtraction p q

theorem singleLift_norm_le (K : Matrix ((R × V) × Finset V) ((R × V) × Finset V) ℝ)
    (p q : ℕ) : ‖singleLift K p q‖ ≤ (p:ℝ) * ‖K‖ := by
  have ht : ‖(singleExtraction (R:=R) (V:=V) p q)ᵀ‖ =
      ‖singleExtraction (R:=R) (V:=V) p q‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (singleExtraction (R:=R) (V:=V) p q)
  unfold singleLift
  calc
    _ ≤ (‖(singleExtraction (R:=R) (V:=V) p q)ᵀ‖ *
        ‖amplifyRight (K:=Finset V) K‖) * ‖singleExtraction (R:=R) (V:=V) p q‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ = ‖singleExtraction (R:=R) (V:=V) p q‖^2 * ‖amplifyRight (K:=Finset V) K‖ := by
      rw [ht]; ring
    _ ≤ (p:ℝ) * ‖K‖ := mul_le_mul (singleExtraction_norm_sq_le p q)
      (amplifyRight_norm_le K) (norm_nonneg _) (Nat.cast_nonneg _)

theorem singleLift_eq_compression
    (K : Matrix ((R × V) × Finset V) ((R × V) × Finset V) ℝ) (p q : ℕ) :
    singleLift K p q = rowGradeProjection p q * rawSingleLift K * rowGradeProjection p q := by
  unfold singleLift rawSingleLift
  rw [singleExtraction_eq_raw_mul,Matrix.transpose_mul,rowGradeProjection_transpose]
  simp only [Matrix.mul_assoc]

theorem rawSingleLift_apply
    (K : Matrix ((R × V) × Finset V) ((R × V) × Finset V) ℝ) (out inp : RowSign R V) :
    rawSingleLift K out inp = ∑ i, ∑ l,
      K ((out.1,i),out.2.2) ((inp.1,l),inp.2.2) *
        (create i * annihilate l) out.2.1 inp.2.1 := by
  classical
  simp only [rawSingleLift,Matrix.mul_apply,Matrix.transpose_apply,rawSingleExtraction_apply,
    amplifyRight,Fintype.sum_prod_type,ite_mul,mul_ite,zero_mul,mul_zero]
  simp only [Fintype.sum_ite_eq',Fintype.sum_ite_eq,Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  simp_rw [← annihilate_transpose]
  simp only [Matrix.transpose_apply]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  let e : (V × Finset V × V) ≃ (V × V × Finset V) :=
    { toFun := fun ⟨l,S,i⟩ => ⟨i,l,S⟩
      invFun := fun ⟨i,l,S⟩ => ⟨l,S,i⟩
      left_inv := by rintro ⟨l,S,i⟩; rfl
      right_inv := by rintro ⟨i,l,S⟩; rfl }
  have he := Fintype.sum_equiv e
    (fun ⟨l,S,i⟩ => (annihilate i S out.2.1 *
      K ((out.1,i),out.2.2) ((inp.1,l),inp.2.2)) * annihilate l S inp.2.1)
    (fun ⟨i,l,S⟩ => K ((out.1,i),out.2.2) ((inp.1,l),inp.2.2) *
      (annihilate i S out.2.1 * annihilate l S inp.2.1))
    (by rintro ⟨l,S,i⟩; dsimp [e]; ring)
  simpa only [Fintype.sum_prod_type] using he

end SingleLift

section TransferBounds

variable {k : ℕ}
local notation "G" => WalshIndex k

theorem xTransfer_eq_rawSingleLift (T : Finset G) (P : Matrix G G ℝ) :
    xTransfer P (walshModes T) = rawSingleLift (xKernel T P (fun _ _ => 1)) := by
  classical
  ext ⟨j,S,Y⟩ ⟨l,Q,Z⟩
  rw [rawSingleLift_apply]
  simp only [xTransfer,tensor,modeCovariance,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,walshModes,xKernel_apply]
  by_cases hY : Y=Z
  · subst Z
    simp only [if_true,mul_one,one_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp [hY]

def frequencyOccupancy (a : G) (Y : Finset G) : ℝ := if a∈Y then 2 else 0

theorem negativeCorrection_eq_rawSingleLift (T : Finset G) (P : Matrix G G ℝ) :
    negativeCorrection P (walshModes T) = rawSingleLift (xKernel T P frequencyOccupancy) := by
  classical
  ext ⟨j,S,Y⟩ ⟨l,Q,Z⟩
  rw [rawSingleLift_apply]
  simp only [negativeCorrection,tensor,modeCorrection,Matrix.smul_apply,smul_eq_mul,
    Matrix.sum_apply,HardCore.number_apply,walshModes,xKernel_apply]
  by_cases hY : Y=Z
  · subst Z
    simp only [if_true,true_and]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    have he : (2:ℝ) * (∑ a, (walshMatrix k (j.val+b) a * walshMatrix k (l.val+i) a) *
        (if a∈Y then 1 else 0)) =
      ∑ a, frequencyOccupancy a Y * walshMatrix k (j.val+b) a * walshMatrix k (l.val+i) a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a∈Y <;> simp [frequencyOccupancy,ha] <;> ring
    rw [he]
    ring
  · simp [hY]

theorem xTransfer_compressed_norm_le (T : Finset G) (P : Matrix G G ℝ) (p q : ℕ) :
    ‖rowGradeProjection p q * xTransfer P (walshModes T) * rowGradeProjection p q‖ ≤
      (p:ℝ) * ‖P‖ := by
  rw [xTransfer_eq_rawSingleLift,← singleLift_eq_compression]
  have hk : ‖xKernel T P (fun _ _ => 1)‖ ≤ ‖P‖ := by
    simpa using xKernel_norm_le T P (fun _ _ => 1) 1 (by norm_num) (by intros; norm_num)
  exact (singleLift_norm_le _ p q).trans
    (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _))

theorem negativeCorrection_compressed_norm_le (T : Finset G) (P : Matrix G G ℝ) (p q : ℕ) :
    ‖rowGradeProjection p q * negativeCorrection P (walshModes T) * rowGradeProjection p q‖ ≤
      2 * (p:ℝ) * ‖P‖ := by
  rw [negativeCorrection_eq_rawSingleLift,← singleLift_eq_compression]
  have hk : ‖xKernel T P frequencyOccupancy‖ ≤ 2 * ‖P‖ :=
    xKernel_norm_le T P frequencyOccupancy 2 (by norm_num)
      (by intro a Y; unfold frequencyOccupancy; split_ifs <;> norm_num)
  calc
    _ ≤ (p:ℝ) * ‖xKernel T P frequencyOccupancy‖ := singleLift_norm_le _ p q
    _ ≤ (p:ℝ) * (2*‖P‖) := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _)
    _ = _ := by ring

end TransferBounds

end
end SRHT.SmallRows
