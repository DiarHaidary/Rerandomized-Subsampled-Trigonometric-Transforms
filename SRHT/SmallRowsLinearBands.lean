import SRHT.SmallRowsLinear
import SRHT.SmallRowsGrades

/-! The three actual easy creation/annihilation blocks and their grade bounds. -/

namespace SRHT.SmallRows
open HardCore MatrixNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section

section Generic
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem gradeExtraction_apply (p : ℕ) (out : V × Finset V) (inp : Finset V) :
    gradeExtraction p out inp = if inp.card=p then annihilate out.1 out.2 inp else 0 := by
  simp [gradeExtraction,Matrix.mul_diagonal,gradeProjection,extraction]

theorem twoGradeProjection_apply (r s : ℕ) (out inp : SignPair V) :
    twoGradeProjection r s out inp = if out=inp then
      if out.1.card=r ∧ out.2.card=s then 1 else 0 else 0 := by
  simp only [twoGradeProjection,Matrix.kronecker,Matrix.kroneckerMap,gradeProjection,
    Matrix.diagonal_apply]
  by_cases hX : out.1=inp.1 <;> by_cases hY : out.2=inp.2 <;>
    simp [hX,hY,Prod.ext_iff,ite_and] <;> split_ifs <;> rfl

theorem mul_rowGradeProjection_apply {O : Type*} [Fintype O]
    (A : Matrix O (D × SignPair V) ℝ) (r s : ℕ) (out : O) (inp : D × SignPair V) :
    (A * rowGradeProjection (R:=D) (G:=V) r s) out inp =
      if inp.2.1.card=r ∧ inp.2.2.card=s then A out inp else 0 := by
  simp [Matrix.mul_apply,rowGradeProjection_apply]

theorem twoGradeProjection_mul_apply {O : Type*}
    (A : Matrix (SignPair V) O ℝ) (r s : ℕ) (out : SignPair V) (inp : O) :
    (twoGradeProjection (G:=V) r s * A) out inp =
      if out.1.card=r ∧ out.2.card=s then A out inp else 0 := by
  simp [Matrix.mul_apply,twoGradeProjection_apply]

theorem linear_rowGradeProjection_norm_le_one (r s : ℕ) :
    ‖rowGradeProjection (R:=D) (G:=V) r s‖ ≤ 1 := by
  unfold rowGradeProjection twoGradeProjection
  calc
    _ ≤ ‖gradeProjection (G:=V) r‖ * ‖gradeProjection (G:=V) s‖ :=
      (amplifyLeft_norm_le _).trans (kronecker_norm_le _ _)
    _ ≤ 1*1 := mul_le_mul (gradeProjection_norm_le_one r) (gradeProjection_norm_le_one s)
      (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

def pairShuffle : ((V × V) × SignPair V) ≃ ((V × Finset V) × (V × Finset V)) where
  toFun z := ((z.1.1,z.2.1),(z.1.2,z.2.2))
  invFun z := ((z.1.1,z.2.1),(z.1.2,z.2.2))
  left_inv := by rintro ⟨⟨i,a⟩,S,Q⟩; rfl
  right_inv := by rintro ⟨⟨i,S⟩,a,Q⟩; rfl

def pairExtraction (r s : ℕ) : Matrix ((V × V) × SignPair V) (SignPair V) ℝ :=
  (Matrix.kronecker (gradeExtraction r) (gradeExtraction s)).submatrix pairShuffle (Equiv.refl _)

theorem pairExtraction_norm_sq_le (r s : ℕ) :
    ‖pairExtraction (V:=V) r s‖^2 ≤ (r:ℝ)*s := by
  have h : ‖pairExtraction (V:=V) r s‖ ≤
      ‖gradeExtraction (G:=V) r‖ * ‖gradeExtraction (G:=V) s‖ := by
    rw [pairExtraction,submatrix_equiv_norm]
    exact kronecker_norm_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at h2
  exact h2.trans (mul_le_mul (gradeExtraction_norm_sq_le r) (gradeExtraction_norm_sq_le s)
    (sq_nonneg _) (Nat.cast_nonneg _))

def raisingBlock (C : Matrix (V × V) D ℝ) : Matrix (SignPair V) (D × SignPair V) ℝ :=
  fun out inp => ∑ i, ∑ a, C (i,a) inp.1 * create i out.1 inp.2.1 * create a out.2 inp.2.2

def mixedBlock (C : Matrix V (D × V) ℝ) : Matrix (SignPair V) (D × SignPair V) ℝ :=
  fun out inp => ∑ i, ∑ a, C i (inp.1,a) * create i out.1 inp.2.1 * annihilate a out.2 inp.2.2

def raisingFactor (C : Matrix (V × V) D ℝ) (r s : ℕ) :
    Matrix (SignPair V) (D × SignPair V) ℝ :=
  (pairExtraction (r+1) (s+1))ᵀ * amplifyRight (K:=SignPair V) C * rowGradeProjection r s

theorem raisingFactor_norm_sq_le (C : Matrix (V × V) D ℝ) (r s : ℕ) :
    ‖raisingFactor C r s‖^2 ≤ ((r:ℝ)+1)*((s:ℝ)+1)*‖C‖^2 := by
  have ht : ‖(pairExtraction (V:=V) (r+1) (s+1))ᵀ‖ =
      ‖pairExtraction (V:=V) (r+1) (s+1)‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (pairExtraction (V:=V) (r+1) (s+1))
  have hb : ‖raisingFactor C r s‖ ≤ ‖pairExtraction (V:=V) (r+1) (s+1)‖ * ‖C‖ := by
    unfold raisingFactor
    calc
      _ ≤ (‖(pairExtraction (V:=V) (r+1) (s+1))ᵀ‖ * ‖amplifyRight (K:=SignPair V) C‖) *
          ‖rowGradeProjection (R:=D) (G:=V) r s‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (‖pairExtraction (V:=V) (r+1) (s+1)‖ * ‖C‖) * 1 := by
        rw [ht]
        gcongr
        · exact amplifyRight_norm_le C
        · exact linear_rowGradeProjection_norm_le_one r s
      _ = _ := mul_one _
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow] at hb2
  have he := pairExtraction_norm_sq_le (V:=V) (r+1) (s+1)
  push_cast at he
  exact hb2.trans (mul_le_mul_of_nonneg_right he (sq_nonneg _))

theorem raisingFactor_eq (C : Matrix (V × V) D ℝ) (r s : ℕ) :
    raisingFactor C r s = raisingBlock C * rowGradeProjection r s := by
  classical
  ext out inp
  rw [raisingFactor,mul_rowGradeProjection_apply,mul_rowGradeProjection_apply]
  by_cases hg : inp.2.1.card=r ∧ inp.2.2.card=s
  · rw [if_pos hg,if_pos hg]
    simp only [Matrix.mul_apply,Matrix.transpose_apply,pairExtraction,Matrix.submatrix_apply,
      Matrix.kronecker,Matrix.kroneckerMap,pairShuffle,Equiv.refl_apply,
      gradeExtraction_apply,amplifyRight,Fintype.sum_prod_type]
    simp only [mul_ite,mul_zero,Prod.ext_iff,ite_and,Fintype.sum_ite_eq',Fintype.sum_ite_eq]
    simp only [raisingBlock]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [← create_transpose]
    simp only [Matrix.transpose_apply]
    by_cases hx : create i out.1 inp.2.1=0 <;> by_cases hy : create a out.2 inp.2.2=0
    · simp [hx,hy]
    · simp [hx]
    · simp [hy]
    · have hX := HardCore.create_card i out.1 inp.2.1 hx
      have hY := HardCore.create_card a out.2 inp.2.2 hy
      simp only [hg.1,hg.2] at hX hY
      simp [hX,hY]
      ring
  · simp [hg]

def leftExtraction (r : ℕ) : Matrix (V × SignPair V) (SignPair V) ℝ :=
  (Matrix.kronecker (gradeExtraction r) (1:HardCore.Op V)).submatrix
    (Equiv.prodAssoc V (Finset V) (Finset V)).symm (Equiv.refl _)

theorem leftExtraction_norm_le (r : ℕ) : ‖leftExtraction (V:=V) r‖ ≤ ‖gradeExtraction (G:=V) r‖ := by
  have hI := isometry_norm_le_one (1:HardCore.Op V) (by simp)
  rw [leftExtraction,submatrix_equiv_norm]
  exact (kronecker_norm_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left hI (norm_nonneg (gradeExtraction (G:=V) r)))

theorem leftExtraction_apply (r : ℕ) (out : V × SignPair V) (inp : SignPair V) :
    leftExtraction r out inp = if out.2.2=inp.2 then
      if inp.1.card=r then annihilate out.1 out.2.1 inp.1 else 0 else 0 := by
  simp [leftExtraction,Matrix.kronecker,Matrix.kroneckerMap,gradeExtraction_apply,Matrix.one_apply]

def rightShuffle : ((D × V) × SignPair V) ≃ (D × (Finset V × (V × Finset V))) where
  toFun z := (z.1.1,(z.2.1,(z.1.2,z.2.2)))
  invFun z := ((z.1,z.2.2.1),(z.2.1,z.2.2.2))
  left_inv := by rintro ⟨⟨b,a⟩,S,Q⟩; rfl
  right_inv := by rintro ⟨b,S,a,Q⟩; rfl

def rightExtraction (s : ℕ) : Matrix ((D × V) × SignPair V) (D × SignPair V) ℝ :=
  (amplifyLeft (K:=D) (Matrix.kronecker (1:HardCore.Op V) (gradeExtraction s))).submatrix
    rightShuffle (Equiv.refl _)

theorem rightExtraction_norm_le (s : ℕ) :
    ‖rightExtraction (D:=D) (V:=V) s‖ ≤ ‖gradeExtraction (G:=V) s‖ := by
  have hI := isometry_norm_le_one (1:HardCore.Op V) (by simp)
  rw [rightExtraction,submatrix_equiv_norm]
  exact ((amplifyLeft_norm_le _).trans (kronecker_norm_le _ _)).trans (by
    simpa using mul_le_mul_of_nonneg_right hI (norm_nonneg (gradeExtraction (G:=V) s)))

theorem rightExtraction_apply (s : ℕ) (out : (D × V) × SignPair V) (inp : D × SignPair V) :
    rightExtraction s out inp = if out.1.1=inp.1 then if out.2.1=inp.2.1 then
      if inp.2.2.card=s then annihilate out.1.2 out.2.2 inp.2.2 else 0 else 0 else 0 := by
  by_cases hb : out.1.1=inp.1 <;> by_cases hX : out.2.1=inp.2.1 <;> by_cases hs : inp.2.2.card=s <;>
    simp [rightExtraction,Matrix.submatrix_apply,amplifyLeft,Matrix.kronecker,
      Matrix.kroneckerMap,rightShuffle,gradeExtraction_apply,Matrix.one_apply,hb,hX,hs]

def mixedFactor (C : Matrix V (D × V) ℝ) (r s : ℕ) : Matrix (SignPair V) (D × SignPair V) ℝ :=
  (leftExtraction (r+1))ᵀ * amplifyRight (K:=SignPair V) C * rightExtraction s * rowGradeProjection r s

theorem mixedFactor_norm_sq_le (C : Matrix V (D × V) ℝ) (r s : ℕ) :
    ‖mixedFactor C r s‖^2 ≤ ((r:ℝ)+1)*s*‖C‖^2 := by
  have ht : ‖(leftExtraction (V:=V) (r+1))ᵀ‖ = ‖leftExtraction (V:=V) (r+1)‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (leftExtraction (V:=V) (r+1))
  have hb : ‖mixedFactor C r s‖ ≤ ‖gradeExtraction (G:=V) (r+1)‖ * ‖C‖ *
      ‖gradeExtraction (G:=V) s‖ := by
    unfold mixedFactor
    calc
      _ ≤ ((‖(leftExtraction (V:=V) (r+1))ᵀ‖ * ‖amplifyRight (K:=SignPair V) C‖) *
          ‖rightExtraction (D:=D) (V:=V) s‖) * ‖rowGradeProjection (R:=D) (G:=V) r s‖ := by
        exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
            (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ ((‖gradeExtraction (G:=V) (r+1)‖ * ‖C‖) * ‖gradeExtraction (G:=V) s‖) * 1 := by
        rw [ht]
        gcongr
        · exact leftExtraction_norm_le _
        · exact amplifyRight_norm_le _
        · exact rightExtraction_norm_le _
        · exact linear_rowGradeProjection_norm_le_one _ _
      _ = _ := mul_one _
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simp only [mul_pow] at hb2
  have hr := gradeExtraction_norm_sq_le (G:=V) (r+1)
  have hs := gradeExtraction_norm_sq_le (G:=V) s
  push_cast at hr
  calc
    _ ≤ (‖gradeExtraction (G:=V) (r+1)‖^2 * ‖C‖^2) * ‖gradeExtraction (G:=V) s‖^2 := hb2
    _ ≤ (((r:ℝ)+1)*‖C‖^2)*(s:ℝ) := by gcongr
    _ = _ := by ring

theorem mixedFactor_eq (C : Matrix V (D × V) ℝ) (r s : ℕ) :
    mixedFactor C r s = mixedBlock C * rowGradeProjection r s := by
  classical
  ext out inp
  rw [mixedFactor,mul_rowGradeProjection_apply,mul_rowGradeProjection_apply]
  by_cases hg : inp.2.1.card=r ∧ inp.2.2.card=s
  · rw [if_pos hg,if_pos hg]
    simp only [Matrix.mul_apply,Matrix.transpose_apply,leftExtraction_apply,
      rightExtraction_apply,amplifyRight,Fintype.sum_prod_type,Prod.ext_iff,ite_and,
      ite_mul,mul_ite,mul_zero,zero_mul,Fintype.sum_ite_eq',Fintype.sum_ite_eq,
      Finset.sum_ite_irrel,Finset.sum_const_zero,hg.2,if_true]
    simp only [mixedBlock]
    simp_rw [← create_transpose]
    simp only [Matrix.transpose_apply]
    by_cases hX : out.1.card=r+1
    · simp only [hX,if_true]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      ring
    · have hz (i : V) : create i out.1 inp.2.1=0 := by
        by_contra hn
        have hc := HardCore.create_card i out.1 inp.2.1 hn
        exact hX (by simpa [hg.1] using hc)
      simp [hX,hz]
  · simp [hg]

end Generic

section Collection
variable {R I J : Type*} [Fintype R] [Fintype I] [Fintype J]
  [DecidableEq R] [DecidableEq I] [DecidableEq J]

def rowSection (A : Matrix (R × I) J ℝ) (j : R) : Matrix I J ℝ := fun i b => A (j,i) b

theorem collected_rows_norm_sq_le (A : Matrix (R × I) J ℝ) (C : ℝ) (hC : 0≤C)
    (hA : ∀ j : R, ‖rowSection A j‖^2≤C) :
    ‖A‖^2 ≤ (Fintype.card R:ℝ)*C := by
  have hn : 0≤(Fintype.card R:ℝ)*C := mul_nonneg (Nat.cast_nonneg _) hC
  have hnorm : ‖A‖≤Real.sqrt ((Fintype.card R:ℝ)*C) := by
    apply matrix_norm_le_of_energy _ _ (Real.sqrt_nonneg _)
    intro v
    rw [Real.sq_sqrt hn]
    calc
      energy (A.mulVec v) = ∑ j : R, energy ((rowSection A j).mulVec v) := by
        simp only [energy,Fintype.sum_prod_type,Matrix.mulVec,dotProduct,rowSection]
      _ ≤ ∑ j : R, C*energy v := by
        apply Finset.sum_le_sum
        intro j _
        exact (matrix_energy_le_norm _ v).trans
          (mul_le_mul_of_nonneg_right (hA j) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      _ = ((Fintype.card R:ℝ)*C)*energy v := by simp; ring
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [Real.sq_sqrt hn] at hsq
  exact hsq

end Collection

section ActualBlocks
variable {k : ℕ} {D : Type*} [Fintype D] [DecidableEq D]

def rawRaising (U : Matrix (WalshIndex k) D ℝ) (T : Finset (WalshIndex k)) :
    Matrix (RowSign T (WalshIndex k)) (D × SignPair (WalshIndex k)) ℝ :=
  fun out inp => raisingBlock (raisingCoefficient out.1.val U) out.2 inp

def rawMixedPM (U : Matrix (WalshIndex k) D ℝ) (T : Finset (WalshIndex k)) :
    Matrix (RowSign T (WalshIndex k)) (D × SignPair (WalshIndex k)) ℝ :=
  fun out inp => mixedBlock (mixedCoefficient out.1.val U) out.2 inp

def rawMixedMP (U : Matrix (WalshIndex k) D ℝ) (T : Finset (WalshIndex k)) :
    Matrix (RowSign T (WalshIndex k)) (D × SignPair (WalshIndex k)) ℝ :=
  fun out inp => ∑ i, ∑ a, (U i inp.1 * walshMatrix k (out.1.val+i) a) *
    annihilate i out.2.1 inp.2.1 * create a out.2.2 inp.2.2

theorem rawRaising_card (U : Matrix (WalshIndex k) D ℝ) (T : Finset (WalshIndex k))
    (out : RowSign T (WalshIndex k)) (inp : D × SignPair (WalshIndex k))
    (h : rawRaising U T out inp ≠ 0) :
    out.2.1.card=inp.2.1.card+1 ∧ out.2.2.card=inp.2.2.card+1 := by
  simp only [rawRaising,raisingBlock] at h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  constructor
  · apply HardCore.create_card i
    intro hz; simp [hz] at ha
  · apply HardCore.create_card a
    intro hz; simp [hz] at ha

theorem rawMixedPM_card (U : Matrix (WalshIndex k) D ℝ) (T : Finset (WalshIndex k))
    (out : RowSign T (WalshIndex k)) (inp : D × SignPair (WalshIndex k))
    (h : rawMixedPM U T out inp ≠ 0) :
    out.2.1.card=inp.2.1.card+1 ∧ inp.2.2.card=out.2.2.card+1 := by
  simp only [rawMixedPM,mixedBlock] at h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  constructor
  · apply HardCore.create_card i
    intro hz; simp [hz] at ha
  · apply HardCore.annihilate_card a
    intro hz; simp [hz] at ha

theorem rawMixedMP_card (U : Matrix (WalshIndex k) D ℝ) (T : Finset (WalshIndex k))
    (out : RowSign T (WalshIndex k)) (inp : D × SignPair (WalshIndex k))
    (h : rawMixedMP U T out inp ≠ 0) :
    inp.2.1.card=out.2.1.card+1 ∧ out.2.2.card=inp.2.2.card+1 := by
  simp only [rawMixedMP] at h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  constructor
  · apply HardCore.annihilate_card i
    intro hz; simp [hz] at ha
  · apply HardCore.create_card a
    intro hz; simp [hz] at ha

theorem rawRaising_norm_sq_le (U : Matrix (WalshIndex k) D ℝ)
    (T : Finset (WalshIndex k)) (r s : ℕ) :
    ‖rawRaising U T * rowGradeProjection r s‖^2 ≤
      (T.card:ℝ)*(((r:ℝ)+1)*((s:ℝ)+1)*‖U‖^2) := by
  have hc : 0≤((r:ℝ)+1)*((s:ℝ)+1)*‖U‖^2 := by positivity
  have h := collected_rows_norm_sq_le (rawRaising U T * rowGradeProjection r s) _ hc
    (fun j => by
      have he : rowSection (rawRaising U T * rowGradeProjection r s) j =
          raisingBlock (raisingCoefficient j.val U) * rowGradeProjection r s := by
        funext out inp
        rfl
      rw [he,← raisingFactor_eq]
      simpa only [raisingCoefficient_norm] using raisingFactor_norm_sq_le (raisingCoefficient j.val U) r s)
  simpa only [Fintype.card_coe] using h

theorem rawMixedPM_norm_sq_le (U : Matrix (WalshIndex k) D ℝ)
    (T : Finset (WalshIndex k)) (r s : ℕ) (mu : ℝ) (hmu : 0≤mu)
    (hell : ∀ i,rowLeverage U i≤mu) :
    ‖rawMixedPM U T * rowGradeProjection r s‖^2 ≤
      (T.card:ℝ)*(mu*((r:ℝ)+1)*s) := by
  have hc : 0≤mu*((r:ℝ)+1)*s := by positivity
  have h := collected_rows_norm_sq_le (rawMixedPM U T * rowGradeProjection r s) _ hc
    (fun j => by
      have he : rowSection (rawMixedPM U T * rowGradeProjection r s) j =
          mixedBlock (mixedCoefficient j.val U) * rowGradeProjection r s := by
        funext out inp
        rfl
      rw [he,← mixedFactor_eq]
      calc
        _ ≤ ((r:ℝ)+1)*s*‖mixedCoefficient j.val U‖^2 := mixedFactor_norm_sq_le _ r s
        _ ≤ ((r:ℝ)+1)*s*mu := mul_le_mul_of_nonneg_left
          (mixedCoefficient_norm_sq_le j.val U mu hmu hell) (by positivity)
        _ = _ := by ring)
  simpa only [Fintype.card_coe] using h

theorem rawMixedMP_row_eq (U : Matrix (WalshIndex k) D ℝ)
    (T : Finset (WalshIndex k)) (j : T) (r s : ℕ) :
    rowSection (rawMixedMP U T * rowGradeProjection r s) j =
      (mixedBlock (reversedMixedCoefficient j.val U) * rowGradeProjection s r).submatrix
        (Equiv.prodComm _ _) (Equiv.prodCongr (Equiv.refl D) (Equiv.prodComm _ _)) := by
  classical
  ext out inp
  change (rawMixedMP U T * rowGradeProjection (R:=D) (G:=WalshIndex k) r s) (j,out) inp = _
  rw [mul_rowGradeProjection_apply]
  simp only [Matrix.submatrix_apply,mul_rowGradeProjection_apply,Equiv.prodComm_apply,
    Equiv.prodCongr_apply,Equiv.refl_apply]
  dsimp only [Prod.map,Prod.swap]
  simp only [Equiv.prodComm_apply,Equiv.refl_apply,Prod.fst_swap,Prod.snd_swap]
  by_cases hg : inp.2.1.card=r ∧ inp.2.2.card=s
  · simp only [hg.1,hg.2,if_true,and_self]
    simp only [rawMixedMP,mixedBlock,reversedMixedCoefficient]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [Prod.swap]
    ring
  · have hg' : ¬(inp.2.2.card=s ∧ inp.2.1.card=r) := by tauto
    simp [hg,hg']

theorem rawMixedMP_norm_sq_le (U : Matrix (WalshIndex k) D ℝ)
    (T : Finset (WalshIndex k)) (r s : ℕ) (mu : ℝ) (hmu : 0≤mu)
    (hell : ∀ i,rowLeverage U i≤mu) :
    ‖rawMixedMP U T * rowGradeProjection r s‖^2 ≤
      (T.card:ℝ)*(mu*r*((s:ℝ)+1)) := by
  have hc : 0≤mu*r*((s:ℝ)+1) := by positivity
  have h := collected_rows_norm_sq_le (rawMixedMP U T * rowGradeProjection r s) _ hc
    (fun j => by
      rw [rawMixedMP_row_eq,submatrix_equiv_norm,← mixedFactor_eq]
      calc
        _ ≤ ((s:ℝ)+1)*r*‖reversedMixedCoefficient j.val U‖^2 := mixedFactor_norm_sq_le _ s r
        _ ≤ ((s:ℝ)+1)*r*mu := mul_le_mul_of_nonneg_left
          (reversedMixedCoefficient_norm_sq_le j.val U mu hmu hell) (by positivity)
        _ = _ := by ring)
  simpa only [Fintype.card_coe] using h

end ActualBlocks

end
end SRHT.SmallRows
