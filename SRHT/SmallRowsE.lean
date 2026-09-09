import SRHT.SmallRows

/-! The grouped double commutator as a compressed Walsh conjugate of a diagonal matrix. -/

namespace SRHT.SmallRows

open SRHT.HardCore
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {k : ℕ}

theorem walsh_row_inner (a b : WalshIndex k) :
    (∑ z, walshMatrix k a z * walshMatrix k b z) = if a = b then 1 else 0 := by
  have h := congrArg (fun M : Matrix (WalshIndex k) (WalshIndex k) ℝ => M a b)
    (walshMatrix_mul_transpose k)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

theorem walsh_shift_product (a b i z : WalshIndex k) :
    walshMatrix k (a+i) z * walshMatrix k (b+i) z =
      walshMatrix k a z * walshMatrix k b z := by
  simp only [walshMatrix, walshChar_add_left]
  calc
    _ = ((Real.sqrt (Fintype.card (WalshIndex k) : ℝ))⁻¹)^2 *
        walshChar a z * walshChar b z * (walshChar i z)^2 := by ring
    _ = _ := by rw [walshChar_sq]; ring

def selectedWalsh (T : Finset (WalshIndex k)) : Matrix (WalshIndex k) T ℝ :=
  fun a j => walshMatrix k j.1 a

theorem selectedWalsh_gram (T : Finset (WalshIndex k)) :
    (selectedWalsh T).transpose * selectedWalsh T = 1 := by
  classical
  ext j l
  simp only [selectedWalsh, Matrix.mul_apply, Matrix.transpose_apply, walsh_row_inner,
    Matrix.one_apply]
  simp only [Subtype.val_inj]

theorem selectedWalsh_norm_le_one (T : Finset (WalshIndex k)) :
    ‖selectedWalsh T‖ ≤ 1 := by
  classical
  have hi : ‖(1 : Matrix T T ℝ)‖ ≤ 1 := by
    rw [show (1 : Matrix T T ℝ) = Matrix.diagonal (fun _ => (1 : ℝ)) from rfl,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro j
    norm_num
  have hg := Matrix.l2_opNorm_conjTranspose_mul_self (selectedWalsh T)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, selectedWalsh_gram] at hg
  have hn := norm_nonneg (selectedWalsh T)
  nlinarith

def siteSign (a : WalshIndex k) (S : Finset (WalshIndex k)) : ℝ :=
  if a ∈ S then -1 else 1

@[simp] theorem siteSign_norm (a : WalshIndex k) (S : Finset (WalshIndex k)) :
    ‖siteSign a S‖ = 1 := by
  unfold siteSign
  split <;> norm_num

def commutatorDiagonal (ell : WalshIndex k → ℝ) :
    Matrix (RowSign (WalshIndex k) (WalshIndex k))
      (RowSign (WalshIndex k) (WalshIndex k)) ℝ :=
  Matrix.diagonal fun out => (∑ i, ell i * siteSign i out.2.1) * siteSign out.1 out.2.2

theorem commutatorDiagonal_norm_le (ell : WalshIndex k → ℝ) :
    ‖commutatorDiagonal ell‖ ≤ ∑ i, ‖ell i‖ := by
  rw [commutatorDiagonal, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg (ell i)))).2
  intro out
  simp only [norm_mul, siteSign_norm, mul_one]
  calc
    ‖∑ i, ell i * siteSign i out.2.1‖ ≤ ∑ i, ‖ell i * siteSign i out.2.1‖ := norm_sum_le _ _
    _ = ∑ i, ‖ell i‖ := by simp only [norm_mul, siteSign_norm, mul_one]

def walshLift (T : Finset (WalshIndex k)) :
    Matrix (RowSign (WalshIndex k) (WalshIndex k)) (RowSign T (WalshIndex k)) ℝ :=
  amplifyRight (K := SignPair (WalshIndex k)) (selectedWalsh T)

theorem walshLift_norm_le_one (T : Finset (WalshIndex k)) :
    ‖walshLift T‖ ≤ 1 :=
  (amplifyRight_norm_le (selectedWalsh T)).trans (selectedWalsh_norm_le_one T)

/-- A concrete diagonal conjugate whose norm is bounded independently of all occupation grades. -/
def groupedCommutator (T : Finset (WalshIndex k)) (ell : WalshIndex k → ℝ) :
    Matrix (RowSign T (WalshIndex k)) (RowSign T (WalshIndex k)) ℝ :=
  (walshLift T).transpose * commutatorDiagonal ell * walshLift T

theorem groupedCommutator_norm_le (T : Finset (WalshIndex k)) (ell : WalshIndex k → ℝ) :
    ‖groupedCommutator T ell‖ ≤ ∑ i, ‖ell i‖ := by
  have hw := walshLift_norm_le_one T
  have ht : ‖(walshLift T).transpose‖ ≤ 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose]
    exact hw
  have hd := commutatorDiagonal_norm_le ell
  have hn : 0 ≤ ∑ i, ‖ell i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (ell i))
  unfold groupedCommutator
  calc
    ‖(walshLift T).transpose * commutatorDiagonal ell * walshLift T‖ ≤
        (‖(walshLift T).transpose‖ * ‖commutatorDiagonal ell‖) * ‖walshLift T‖ := by
          exact (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * (∑ i, ‖ell i‖)) * 1 := by gcongr
    _ = ∑ i, ‖ell i‖ := by ring

theorem localCorrection_entry (i l : WalshIndex k) (S Q : Finset (WalshIndex k)) :
    localCorrection i l S Q = if i = l ∧ S = Q then siteSign i S else 0 := by
  classical
  by_cases hi : i = l <;> by_cases hs : S = Q
  · subst l; subst Q
    by_cases hm : i ∈ S <;>
      norm_num [localCorrection, Matrix.one_apply, number_apply, siteSign, hm]
  · simp [localCorrection, hi, hs, Matrix.one_apply, number_apply]
  · simp [localCorrection, hi]
  · simp [localCorrection, hi]

theorem modeCommutator_entry (f g : WalshIndex k → ℝ)
    (S Q : Finset (WalshIndex k)) :
    (modeCovariance f g - modeCorrection f g) S Q =
      if S = Q then ∑ a, f a * g a * siteSign a S else 0 := by
  classical
  by_cases hs : S = Q
  · subst Q
    simp only [modeCovariance, modeCorrection, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, ite_true, mul_one, Matrix.sum_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hm : a ∈ S <;> simp [number_apply, siteSign, hm] <;> ring
  · simp [modeCovariance, modeCorrection, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.sum_apply, hs, Matrix.one_apply, number_apply]

theorem doubleCommutator_entry (T : Finset (WalshIndex k))
    (P : Matrix (WalshIndex k) (WalshIndex k) ℝ)
    (out inp : RowSign T (WalshIndex k)) :
    doubleCommutator P (walshModes T) out inp =
      if out.2 = inp.2 then
        (∑ i, P i i * siteSign i out.2.1) *
          (∑ a, walshMatrix k out.1.1 a * walshMatrix k inp.1.1 a * siteSign a out.2.2)
      else 0 := by
  classical
  change (WalshIndex k → WalshIndex k → ℝ) at P
  simp only [doubleCommutator, tensor, localCorrection_entry, modeCommutator_entry,
    walshModes]
  by_cases hsx : out.2.1 = inp.2.1 <;> by_cases hsy : out.2.2 = inp.2.2
  · have hs : out.2 = inp.2 := Prod.ext hsx hsy
    simp only [hs, ite_true, hsx, hsy, and_true]
    simp only [ite_mul, mul_ite, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Fintype.sum_ite_eq]
    simp_rw [walsh_shift_product]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · have hs : out.2 ≠ inp.2 := fun h => hsy (congrArg Prod.snd h)
    simp [hsx, hsy, hs]
  · have hs : out.2 ≠ inp.2 := fun h => hsx (congrArg Prod.fst h)
    simp [hsx, hsy, hs]
  · have hs : out.2 ≠ inp.2 := fun h => hsx (congrArg Prod.fst h)
    simp [hsx, hsy, hs]

theorem groupedCommutator_entry (T : Finset (WalshIndex k)) (ell : WalshIndex k → ℝ)
    (out inp : RowSign T (WalshIndex k)) :
    groupedCommutator T ell out inp =
      if out.2 = inp.2 then
        (∑ i, ell i * siteSign i out.2.1) *
          (∑ a, walshMatrix k out.1.1 a * walshMatrix k inp.1.1 a * siteSign a out.2.2)
      else 0 := by
  classical
  unfold groupedCommutator commutatorDiagonal
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, walshLift, amplifyRight,
    selectedWalsh]
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, mul_ite, mul_zero, zero_mul, Fintype.sum_ite_eq']
  by_cases hs : out.2 = inp.2
  · simp only [hs, ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · simp [hs, Ne.symm hs]
theorem doubleCommutator_eq_grouped (T : Finset (WalshIndex k))
    (P : Matrix (WalshIndex k) (WalshIndex k) ℝ) :
    doubleCommutator P (walshModes T) = groupedCommutator T (fun i => P i i) := by
  ext out inp
  rw [doubleCommutator_entry, groupedCommutator_entry]

/-- The grouped double commutator has no occupation or row-cardinality loss. -/
theorem doubleCommutator_norm_le (T : Finset (WalshIndex k))
    (P : Matrix (WalshIndex k) (WalshIndex k) ℝ) :
    ‖doubleCommutator P (walshModes T)‖ ≤ ∑ i, ‖P i i‖ := by
  rw [doubleCommutator_eq_grouped]
  exact groupedCommutator_norm_le T _

end
end SRHT.SmallRows





