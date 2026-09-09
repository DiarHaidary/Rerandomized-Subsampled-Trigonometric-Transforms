import SRHT.SmallRowsY
import SRHT.SmallRowsGrades
import SRHT.Model

/-! Complete finite norm estimate for the five-term collected double-annihilation Gram. -/
namespace SRHT.SmallRows
open SRHT.HardCore SRHT.MatrixNorm
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

variable {G R D : Type*} [Fintype G] [DecidableEq G]
  [Fintype R] [DecidableEq R] [Fintype D] [DecidableEq D]

theorem rowGradeProjection_norm_le_one (p q : ℕ) :
    ‖rowGradeProjection (R:=R) (G:=G) p q‖≤1 := by
  unfold rowGradeProjection twoGradeProjection
  calc
    _ ≤ ‖gradeProjection (G:=G) p‖*‖gradeProjection (G:=G) q‖ :=
      (amplifyLeft_norm_le _).trans (kronecker_norm_le _ _)
    _ ≤ 1*1 := mul_le_mul (gradeProjection_norm_le_one p) (gradeProjection_norm_le_one q)
      (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem rowGradeProjection_compression_norm_le (A : Matrix (RowSign R G) (RowSign R G) ℝ)
    (p q : ℕ) : ‖rowGradeProjection p q * A * rowGradeProjection p q‖≤‖A‖ := by
  have hQ := rowGradeProjection_norm_le_one (R:=R) (G:=G) p q
  calc
    _ ≤ (‖rowGradeProjection (R:=R) (G:=G) p q‖*‖A‖)*
        ‖rowGradeProjection (R:=R) (G:=G) p q‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖A‖)*1 := by gcongr
    _ = ‖A‖ := by ring

/-- We retain the negative correction by its absolute norm. This costs an extra `2p`,
which remains within the final `27 q^3` allowance. -/
theorem gramKernel_compressed_norm_le {k : ℕ} (T : Finset (WalshIndex k))
    (P : Matrix (WalshIndex k) (WalshIndex k) ℝ)
    (mu : ℝ) (hmu : 0≤mu) (hell : ∀ i, ‖P i i‖≤mu) (p q : ℕ) :
    ‖rowGradeProjection p q * gramKernel P (walshModes T) * rowGradeProjection p q‖ ≤
      (∑ i, ‖P i i‖) + (3*(p:ℝ)+(p:ℝ)*q)*‖P‖ + mu*T.card*q := by
  classical
  let Q := rowGradeProjection (R:=T) (G:=WalshIndex k) p q
  let E := Q*doubleCommutator P (walshModes T)*Q
  let X := Q*xTransfer P (walshModes T)*Q
  let F := Q*negativeCorrection P (walshModes T)*Q
  let Y := Q*yTransfer P (walshModes T)*Q
  let M := Q*mixedTransfer P (walshModes T)*Q
  have hE : ‖E‖≤∑ i, ‖P i i‖ :=
    (rowGradeProjection_compression_norm_le _ p q).trans (doubleCommutator_norm_le T P)
  have hX : ‖X‖≤(p:ℝ)*‖P‖ := xTransfer_compressed_norm_le T P p q
  have hF : ‖F‖≤2*(p:ℝ)*‖P‖ := negativeCorrection_compressed_norm_le T P p q
  have hY : ‖Y‖≤mu*T.card*q := SmallRowsY.yTransfer_compressed_norm_le T P mu hmu hell p q
  have hM : ‖M‖≤(p:ℝ)*q*‖P‖ := mixedTransfer_compressed_norm_le T P p q
  have h1 := norm_add_le E X
  have h2 := norm_sub_le (E+X) F
  have h3 := norm_add_le (E+X-F) Y
  have h4 := norm_add_le (E+X-F+Y) M
  have heq : rowGradeProjection p q * gramKernel P (walshModes T) * rowGradeProjection p q =
      E+X-F+Y+M := by
    rw [gramKernel_normalOrder]
    simp only [mul_add,add_mul,mul_sub,sub_mul,E,X,F,Y,M,Q]
  rw [heq]
  linarith

theorem rectangular_grade_projection (A : Matrix (RowSign R G) (RowSign D G) ℝ)
    (r s p q : ℕ)
    (hA : ∀ out inp, A out inp≠0 → inp.2.1.card=r → inp.2.2.card=s →
      out.2.1.card=p ∧ out.2.2.card=q) :
    rowGradeProjection p q * A * rowGradeProjection r s = A * rowGradeProjection r s := by
  classical
  ext out inp
  simp only [Matrix.mul_apply,rowGradeProjection_apply,ite_mul,mul_ite,zero_mul,mul_zero,
    one_mul,mul_one,Fintype.sum_ite_eq',Fintype.sum_ite_eq]
  by_cases hr : inp.2.1.card=r <;> by_cases hs : inp.2.2.card=s
  · by_cases hz : A out inp=0
    · simp [hr,hs,hz]
    · have hpq:=hA out inp hz hr hs
      simp [hr,hs,hpq.1,hpq.2]
  · simp [hr,hs]
  · simp [hr,hs]
  · simp [hr,hs]

theorem collectedDouble_card (U : Matrix G D ℝ) (f : R→G→G→ℝ)
    (out : RowSign R G) (inp : RowSign D G) (h : collectedDouble U f out inp≠0) :
    inp.2.1.card=out.2.1.card+1 ∧ inp.2.2.card=out.2.2.card+1 := by
  simp only [collectedDouble] at h
  obtain ⟨i,_,hi⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
  have hx : annihilate i out.2.1 inp.2.1≠0 := by intro hh; simp [hh] at hi
  have hy : annihilateMode (f out.1 i) out.2.2 inp.2.2≠0 := by intro hh; simp [hh] at hi
  exact ⟨annihilate_card i _ _ hx,annihilateMode_card _ _ _ hy⟩

theorem collectedDouble_grade (U : Matrix G D ℝ) (f : R→G→G→ℝ) (p q : ℕ) :
    rowGradeProjection p q * collectedDouble U f * rowGradeProjection (p+1) (q+1) =
      collectedDouble U f * rowGradeProjection (p+1) (q+1) := by
  apply rectangular_grade_projection
  intro out inp h hp hq
  have hc := collectedDouble_card U f out inp h
  constructor <;> omega

theorem matrix_norm_sq_eq_rowGram {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J ℝ) :
    ‖A‖^2=‖A*A.transpose‖ := by
  have hg := Matrix.l2_opNorm_conjTranspose_mul_self A.transpose
  have ht : ‖A.transpose‖=‖A‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose,ht] at hg
  simpa only [pow_two] using hg.symm

theorem collectedDouble_compressed_norm_sq_le {k : ℕ} (T : Finset (WalshIndex k))
    (U : Matrix (WalshIndex k) D ℝ) (mu : ℝ) (hmu : 0≤mu)
    (hell : ∀ i, ‖(U*U.transpose) i i‖≤mu) (p q : ℕ) :
    ‖collectedDouble U (walshModes T) * rowGradeProjection (p+1) (q+1)‖^2 ≤
      (∑ i, ‖(U*U.transpose) i i‖) +
        (3*(p:ℝ)+(p:ℝ)*q)*‖U*U.transpose‖ + mu*T.card*q := by
  classical
  let A := collectedDouble U (walshModes T)
  let Q := rowGradeProjection (R:=T) (G:=WalshIndex k) p q
  have hn : ‖A*rowGradeProjection (p+1) (q+1)‖≤‖Q*A‖ := by
    rw [show A*rowGradeProjection (p+1) (q+1)=Q*A*rowGradeProjection (p+1) (q+1) from
      (collectedDouble_grade U (walshModes T) p q).symm]
    calc
      _ ≤ ‖Q*A‖*‖rowGradeProjection (R:=D) (G:=WalshIndex k) (p+1) (q+1)‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ ‖Q*A‖*1 := mul_le_mul_of_nonneg_left
        (rowGradeProjection_norm_le_one (p+1) (q+1)) (norm_nonneg _)
      _ = ‖Q*A‖ := mul_one _
  have heq : (Q*A)*(Q*A).transpose =
      Q*gramKernel (U*U.transpose) (walshModes T)*Q := by
    rw [Matrix.transpose_mul,show Q.transpose=Q from rowGradeProjection_transpose p q]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A A.transpose Q,collectedDouble_gram]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [matrix_norm_sq_eq_rowGram (Q*A),heq] at hs
  exact hs.trans (gramKernel_compressed_norm_le T _ mu hmu hell p q)

/-- The quantitative main estimate for an actual isometric input frame. -/
theorem collectedDouble_isometry_norm_sq_le {k : ℕ} (T : Finset (WalshIndex k))
    (U : Matrix (WalshIndex k) D ℝ) (hU : U.transpose*U=1) (p q : ℕ) :
    ‖collectedDouble U (walshModes T) * rowGradeProjection (p+1) (q+1)‖^2 ≤
      (Fintype.card D : ℝ) + 3*p + p*q + T.card*q := by
  have hp := isometry_projection_norm_le_one U hU
  have hell : ∀ i, ‖(U*U.transpose) i i‖≤(1:ℝ) := by
    intro i
    rw [rowLeverage_projection_diagonal,Real.norm_eq_abs,
      abs_of_nonneg (rowLeverage_nonneg U i)]
    exact rowLeverage_le_one U hU i
  have hsum : (∑ i, ‖(U*U.transpose) i i‖)=(Fintype.card D:ℝ) := by
    simp only [rowLeverage_projection_diagonal,Real.norm_eq_abs,
      abs_of_nonneg (rowLeverage_nonneg U _)]
    exact sum_rowLeverage U hU
  have h := collectedDouble_compressed_norm_sq_le T U 1 (by norm_num) hell p q
  rw [hsum,one_mul] at h
  have hmul := mul_le_mul_of_nonneg_left hp
    (show 0≤3*(p:ℝ)+(p:ℝ)*q by positivity)
  nlinarith

theorem collectedDouble_zero_firstgrade (U : Matrix G D ℝ) (f : R→G→G→ℝ) (s : ℕ) :
    collectedDouble U f * rowGradeProjection (R:=D) (G:=G) 0 s = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply,rowGradeProjection_apply,mul_ite,mul_zero,mul_one,
    Fintype.sum_ite_eq',Matrix.zero_apply]
  by_cases hx : inp.2.1.card=0
  · have hz : collectedDouble U f out inp=0 := by
      by_contra hh
      have hc:=collectedDouble_card U f out inp hh
      omega
    simp [hx,hz]
  · simp [hx]

theorem collectedDouble_zero_secondgrade (U : Matrix G D ℝ) (f : R→G→G→ℝ) (r : ℕ) :
    collectedDouble U f * rowGradeProjection (R:=D) (G:=G) r 0 = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply,rowGradeProjection_apply,mul_ite,mul_zero,mul_one,
    Fintype.sum_ite_eq',Matrix.zero_apply]
  by_cases hy : inp.2.2.card=0
  · have hz : collectedDouble U f out inp=0 := by
      by_contra hh
      have hc:=collectedDouble_card U f out inp hh
      omega
    simp [hy,hz]
  · simp [hy]

/-- All grades, including the zero-grade boundary. -/
theorem collectedDouble_isometry_norm_sq_le_all {k : ℕ} (T : Finset (WalshIndex k))
    (U : Matrix (WalshIndex k) D ℝ) (hU : U.transpose*U=1) (r s : ℕ) :
    ‖collectedDouble U (walshModes T) * rowGradeProjection r s‖^2 ≤
      (Fintype.card D : ℝ) + 3*(r-1:ℕ) + (r-1:ℕ)*(s-1:ℕ) + T.card*(s-1:ℕ) := by
  cases r with
  | zero =>
    rw [collectedDouble_zero_firstgrade]
    simp only [norm_zero,zero_pow (by decide : 2≠0)]
    positivity
  | succ p =>
    cases s with
    | zero =>
      rw [collectedDouble_zero_secondgrade]
      simp only [norm_zero,zero_pow (by decide : 2≠0)]
      positivity
    | succ q =>
      simpa only [Nat.succ_sub_one,Nat.succ_eq_add_one] using
        collectedDouble_isometry_norm_sq_le T U hU p q

/-- The finite cubic allowance used by the final theorem. This includes the extra
`2(r-1)` paid by bounding the negative correction in absolute norm. -/
theorem small_row_cost_le (d t r s q : ℕ) (hq : 1≤q) (hr : r≤2*q) (hs : s≤2*q) (ht : t≤q) :
    (d : ℝ) + 3*(r-1:ℕ) + (r-1:ℕ)*(s-1:ℕ) + t*(s-1:ℕ) +
      t*((r+1:ℕ)*(s+1:ℕ)+(r+1:ℕ)*s+r*(s+1:ℕ)) ≤ d+27*(q:ℝ)^3 := by
  have hp : (r-1:ℕ)≤2*q-1 := Nat.sub_le_sub_right hr 1
  have hq0 : (s-1:ℕ)≤2*q-1 := Nat.sub_le_sub_right hs 1
  have hpR : ((r-1:ℕ):ℝ)≤2*(q:ℝ)-1 := by
    have he : ((2*q-1:ℕ):ℝ)=2*(q:ℝ)-1 := by
      rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    have hc : ((r-1:ℕ):ℝ)≤((2*q-1:ℕ):ℝ) := by exact_mod_cast hp
    rwa [he] at hc
  have hsR : ((s-1:ℕ):ℝ)≤2*(q:ℝ)-1 := by
    have he : ((2*q-1:ℕ):ℝ)=2*(q:ℝ)-1 := by
      rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    have hc : ((s-1:ℕ):ℝ)≤((2*q-1:ℕ):ℝ) := by exact_mod_cast hq0
    rwa [he] at hc
  have hrR : (r:ℝ)≤2*(q:ℝ) := by exact_mod_cast hr
  have hsR0 : (s:ℝ)≤2*(q:ℝ) := by exact_mod_cast hs
  have htR : (t:ℝ)≤q := by exact_mod_cast ht
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  push_cast
  calc
    _ ≤ (d:ℝ)+3*(2*q-1)+(2*q-1)*(2*q-1)+q*(2*q-1)+
        q*((2*q+1)*(2*q+1)+(2*q+1)*(2*q)+(2*q)*(2*q+1)) := by gcongr <;> linarith
    _ = (d:ℝ)+12*(q:ℝ)^3+14*(q:ℝ)^2+2*q-2 := by ring
    _ ≤ (d:ℝ)+27*(q:ℝ)^3 := by
      have hpos : 0≤15*(q:ℝ)^2*((q:ℝ)-1)+((q:ℝ)-1)^2+1 := by positivity
      nlinarith

end
end SRHT.SmallRows

