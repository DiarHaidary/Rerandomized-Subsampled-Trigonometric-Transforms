import SRHT.Walsh
import SRHT.HardCore

/-! The concrete mixed row/one-particle kernel is a contraction. -/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace SRHT.SmallRowsMixed

noncomputable section

variable {k : ℕ}
local notation "G" => WalshIndex k

/-- Output and input are `(row, x-site, y-site)`, with right-associated products. -/
def kernel (T : Finset G) (P : Matrix G G ℝ) : Matrix (T × G × G) (T × G × G) ℝ :=
  fun out inp => P inp.2.1 out.2.1 *
    walshMatrix k (inp.1.1 + out.2.1) out.2.2 *
    walshMatrix k (out.1.1 + inp.2.1) inp.2.2

/-- Analyze a y-vector in the Walsh modes indexed by the restricted row set.
The intermediate register is `(x-site, input-row, analyzed-row)`. -/
def analysis (T : Finset G) : Matrix (G × (T × T)) (T × G × G) ℝ :=
  fun out inp => if inp.1 = out.2.1 then
    if inp.2.1 = out.1 then walshMatrix k (out.2.2.1 + out.1) inp.2.2 else 0 else 0

/-- Apply `Pᵀ` to the x-site and exchange the two row registers. -/
def middle (T : Finset G) (P : Matrix G G ℝ) :
    Matrix (G × (T × T)) (G × (T × T)) ℝ :=
  fun out inp => if inp.2.1 = out.2.2 then
    if inp.2.2 = out.2.1 then P inp.1 out.1 else 0 else 0

theorem analysis_gram (T : Finset G) : analysis T * (analysis T)ᵀ = 1 := by
  classical
  ext ⟨i,j,l⟩ ⟨i',j',l'⟩
  simp only [analysis, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    ite_mul, zero_mul]
  by_cases hi : i = i' <;> by_cases hj : j = j'
  · subst i'
    subst j'
    simp [walshMatrix_orthogonal, Matrix.one_apply]
  · simp [hj]
  · simp [hi]
  · simp [hi, hj]

theorem analysis_norm_le_one (T : Finset G) : ‖analysis T‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (analysis T)ᵀ
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    analysis_gram] at h
  have ht := Matrix.l2_opNorm_conjTranspose (analysis T)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at ht
  have hI : ‖(1 : Matrix (G × (T × T)) (G × (T × T)) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun _ => by simp)
  have hn := norm_nonneg (analysis T)
  nlinarith

theorem middle_mulVec (T : Finset G) (P : Matrix G G ℝ)
    (v : G × (T × T) → ℝ) (i : G) (j l : T) :
    (middle T P).mulVec v (i,j,l) =
      Pᵀ.mulVec (fun a => v (a,l,j)) i := by
  classical
  simp [middle, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_prod_type]

theorem middle_norm_le (T : Finset G) (P : Matrix G G ℝ) : ‖middle T P‖ ≤ ‖P‖ := by
  apply HardCore.matrix_norm_le_of_energy _ _ (norm_nonneg P)
  intro v
  have hPT : ‖Pᵀ‖ = ‖P‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose P
  calc
    HardCore.energy ((middle T P).mulVec v) =
        ∑ j : T, ∑ l : T, HardCore.energy (Pᵀ.mulVec (fun a => v (a,l,j))) := by
      simp only [HardCore.energy, Fintype.sum_prod_type, middle_mulVec]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ ≤ ∑ j : T, ∑ l : T, ‖P‖^2 * HardCore.energy (fun a => v (a,l,j)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      simpa only [hPT] using HardCore.matrix_energy_le_norm Pᵀ (fun a => v (a,l,j))
    _ = ‖P‖^2 * HardCore.energy v := by
      simp only [HardCore.energy, Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      congr 1
      calc
        (∑ j : T, ∑ l : T, ∑ a : G, v (a,l,j)^2) =
            ∑ j : T, ∑ a : G, ∑ l : T, v (a,l,j)^2 := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_comm]
        _ = ∑ a : G, ∑ j : T, ∑ l : T, v (a,l,j)^2 := by rw [Finset.sum_comm]
        _ = ∑ a : G, ∑ l : T, ∑ j : T, v (a,l,j)^2 := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]

theorem kernel_factorization (T : Finset G) (P : Matrix G G ℝ) :
    kernel T P = (analysis T)ᵀ * middle T P * analysis T := by
  classical
  ext ⟨j,i,a⟩ ⟨l,b,c⟩
  simp [kernel, analysis, middle, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]

/-- The exact mixed kernel has norm at most the norm of its external projection. -/
theorem kernel_norm_le (T : Finset G) (P : Matrix G G ℝ) : ‖kernel T P‖ ≤ ‖P‖ := by
  rw [kernel_factorization]
  have hA := analysis_norm_le_one T
  have hAT : ‖(analysis T)ᵀ‖ ≤ 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose (analysis T)).trans_le hA
  calc
    ‖(analysis T)ᵀ * middle T P * analysis T‖
        ≤ (‖(analysis T)ᵀ‖ * ‖middle T P‖) * ‖analysis T‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * ‖P‖) * 1 := by
      exact mul_le_mul (mul_le_mul hAT (middle_norm_le T P) (norm_nonneg _) (by norm_num))
        hA (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = ‖P‖ := by ring

theorem kernel_norm_le_one (T : Finset G) (P : Matrix G G ℝ) (hP : ‖P‖ ≤ 1) :
    ‖kernel T P‖ ≤ 1 := (kernel_norm_le T P).trans hP

end

end SRHT.SmallRowsMixed
