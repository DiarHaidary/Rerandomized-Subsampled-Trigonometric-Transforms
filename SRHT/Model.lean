import SRHT.Walsh
import SparseFockFormal.FiniteProductLaw
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Concrete sign laws, two-round matrices, and uniform fixed-size row sampling. -/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace SRHT

noncomputable section

/-- The uniform probability law on a nonempty finite type. -/
def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : SparseFock.FiniteLaw α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  weight_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_weight := by
    have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hc]

@[simp] theorem uniformLaw_weight (α : Type*) [Fintype α] [Nonempty α] (a : α) :
    (uniformLaw α).weight a = (Fintype.card α : ℝ)⁻¹ := rfl

/-- A full diagonal sign assignment, encoded by bits. -/
abbrev SignAssignment (k : ℕ) := WalshIndex k → ZMod 2

/-- Every coordinate is an independent uniform bit. -/
def signLaw (k : ℕ) : SparseFock.FiniteLaw (SignAssignment k) :=
  SparseFock.FiniteLaw.independentProduct (fun _ : WalshIndex k => uniformLaw (ZMod 2))

@[simp] theorem signLaw_weight (k : ℕ) (x : SignAssignment k) :
    (signLaw k).weight x = (1 / 2 : ℝ) ^ (2 ^ k) := by
  simp [signLaw, uniformLaw, one_div]

/-- The actual real diagonal matrix of a bit assignment. -/
def signDiagonal {k : ℕ} (x : SignAssignment k) :
    Matrix (WalshIndex k) (WalshIndex k) ℝ := Matrix.diagonal (fun i => bitSign (x i))

@[simp] theorem signDiagonal_transpose {k : ℕ} (x : SignAssignment k) :
    (signDiagonal x)ᵀ = signDiagonal x := Matrix.diagonal_transpose _

@[simp] theorem signDiagonal_mul_self {k : ℕ} (x : SignAssignment k) :
    signDiagonal x * signDiagonal x = 1 := by
  classical
  simp [signDiagonal, Matrix.diagonal_mul_diagonal]

@[simp] theorem signDiagonal_transpose_mul {k : ℕ} (x : SignAssignment k) :
    (signDiagonal x)ᵀ * signDiagonal x = 1 := by simp

/-- The exact two-round rerandomized Walsh transform, before row sampling. -/
def twoRoundMatrix {k : ℕ} (x y : SignAssignment k) :
    Matrix (WalshIndex k) (WalshIndex k) ℝ :=
  walshMatrix k * signDiagonal y * walshMatrix k * signDiagonal x

theorem transpose_mul_self_product
    {ι κ υ : Type*} [Fintype ι] [Fintype κ] [Fintype υ]
    [DecidableEq κ] [DecidableEq υ]
    {A : Matrix ι κ ℝ} {B : Matrix κ υ ℝ}
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (A * B)ᵀ * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ A B,
    hA, Matrix.one_mul, hB]

@[simp] theorem twoRoundMatrix_transpose_mul {k : ℕ} (x y : SignAssignment k) :
    (twoRoundMatrix x y)ᵀ * twoRoundMatrix x y = 1 := by
  unfold twoRoundMatrix
  apply transpose_mul_self_product _ (signDiagonal_transpose_mul x)
  apply transpose_mul_self_product _ (walshMatrix_transpose_mul k)
  exact transpose_mul_self_product (walshMatrix_transpose_mul k)
    (signDiagonal_transpose_mul y)

/-- The fixed frame after the two random sign diagonals and Hadamards. -/
def transformedFrame {k d : ℕ} (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (x y : SignAssignment k) : Matrix (WalshIndex k) (Fin d) ℝ :=
  twoRoundMatrix x y * U

theorem transformedFrame_transpose_mul {k d : ℕ}
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (hU : Uᵀ * U = 1)
    (x y : SignAssignment k) :
    (transformedFrame U x y)ᵀ * transformedFrame U x y = 1 :=
  transpose_mul_self_product (twoRoundMatrix_transpose_mul x y) hU

/-- An entry expansion exposing one sign from each diagonal in every term. -/
theorem transformedFrame_apply {k d : ℕ}
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (x y : SignAssignment k)
    (j : WalshIndex k) (b : Fin d) :
    transformedFrame U x y j b =
      ∑ a, ∑ i, walshMatrix k j a * bitSign (y a) *
        walshMatrix k a i * bitSign (x i) * U i b := by
  classical
  simp only [transformedFrame, twoRoundMatrix, signDiagonal]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A weighted row Gram; selectors may later be specialized to Bernoulli indicators. -/
def weightedGram {k d : ℕ} (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (x y : SignAssignment k) (weights : WalshIndex k → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun b c => ∑ j, weights j * transformedFrame U x y j b * transformedFrame U x y j c

@[simp] theorem weightedGram_apply {k d : ℕ}
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (x y : SignAssignment k)
    (weights : WalshIndex k → ℝ) (b c : Fin d) :
    weightedGram U x y weights b c =
      ∑ j, weights j * transformedFrame U x y j b * transformedFrame U x y j c := rfl

/-- The normalized Gram from an actual set of distinct sampled rows. -/
def sampledGram {k d : ℕ} (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (x y : SignAssignment k) (T : Finset (WalshIndex k)) : Matrix (Fin d) (Fin d) ℝ :=
  fun b c => ((Fintype.card (WalshIndex k) : ℝ) / T.card) *
    ∑ j ∈ T, transformedFrame U x y j b * transformedFrame U x y j c

/-- The literal selected and scaled frame, with rows indexed by the selected set. -/
def sampledFrame {k d : ℕ} (U : Matrix (WalshIndex k) (Fin d) ℝ)
    (x y : SignAssignment k) (T : Finset (WalshIndex k)) : Matrix T (Fin d) ℝ :=
  fun j b => Real.sqrt ((Fintype.card (WalshIndex k) : ℝ) / T.card) *
    transformedFrame U x y j.1 b

theorem sampledFrame_gram {k d : ℕ}
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (x y : SignAssignment k)
    (T : Finset (WalshIndex k)) :
    (sampledFrame U x y T)ᵀ * sampledFrame U x y T = sampledGram U x y T := by
  classical
  ext b c
  change (∑ j : T,
      (Real.sqrt ((Fintype.card (WalshIndex k) : ℝ) / T.card) * transformedFrame U x y j.1 b) *
      (Real.sqrt ((Fintype.card (WalshIndex k) : ℝ) / T.card) * transformedFrame U x y j.1 c)) =
    ((Fintype.card (WalshIndex k) : ℝ) / T.card) *
      ∑ j ∈ T, transformedFrame U x y j b * transformedFrame U x y j c
  have hn : 0 ≤ (Fintype.card (WalshIndex k) : ℝ) / (T.card : ℝ) := by positivity
  calc
    _ = ∑ j : T, ((Fintype.card (WalshIndex k) : ℝ) / T.card) *
        (transformedFrame U x y j.1 b * transformedFrame U x y j.1 c) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = Real.sqrt ((Fintype.card (WalshIndex k) : ℝ) / T.card) ^ 2 *
            (transformedFrame U x y j.1 b * transformedFrame U x y j.1 c) := by ring
        _ = _ := by rw [Real.sq_sqrt hn]
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort T (fun j => transformedFrame U x y j b * transformedFrame U x y j c)

/-- Sampling all rows is an exact isometry on every input frame. -/
theorem sampledGram_univ {k d : ℕ}
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (hU : Uᵀ * U = 1)
    (x y : SignAssignment k) : sampledGram U x y Finset.univ = 1 := by
  classical
  have hc : (Fintype.card (WalshIndex k) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext b c
  simpa [sampledGram, hc, Matrix.mul_apply, Matrix.transpose_apply] using
    congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A b c)
      (transformedFrame_transpose_mul U hU x y)

/-- Exactly `M` distinct row labels, represented as a finite subtype. -/
def RowSet (k M : ℕ) := {T : Finset (WalshIndex k) // T.card = M}

instance rowSetFintype (k M : ℕ) : Fintype (RowSet k M) := by
  classical
  unfold RowSet
  infer_instance

theorem rowSet_nonempty {k M : ℕ} (hM : M ≤ 2 ^ k) : Nonempty (RowSet k M) := by
  classical
  have h : M ≤ (Finset.univ : Finset (WalshIndex k)).card := by simpa using hM
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq h
  exact ⟨⟨T, hT⟩⟩

/-- The actual uniform law on all subsets having the prescribed cardinality. -/
def uniformRowLaw {k M : ℕ} (hM : M ≤ 2 ^ k) : SparseFock.FiniteLaw (RowSet k M) := by
  letI : Nonempty (RowSet k M) := rowSet_nonempty hM
  exact uniformLaw (RowSet k M)

@[simp] theorem uniformRowLaw_weight {k M : ℕ} (hM : M ≤ 2 ^ k) (T : RowSet k M) :
    (uniformRowLaw hM).weight T = (Fintype.card (RowSet k M) : ℝ)⁻¹ := rfl

/-- Independent first signs, second signs, and a uniform fixed-size row sample. -/
def sketchLaw {k M : ℕ} (hM : M ≤ 2 ^ k) :
    SparseFock.FiniteLaw (SignAssignment k × (SignAssignment k × RowSet k M)) :=
  (signLaw k).product ((signLaw k).product (uniformRowLaw hM))

@[simp] theorem sketchLaw_weight {k M : ℕ} (hM : M ≤ 2 ^ k)
    (x y : SignAssignment k) (T : RowSet k M) :
    (sketchLaw hM).weight (x, y, T) =
      (signLaw k).weight x * ((signLaw k).weight y * (uniformRowLaw hM).weight T) := rfl

theorem rowSet_full_eq_univ {k : ℕ} (T : RowSet k (2 ^ k)) :
    T.1 = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  simpa using T.2

theorem sampledGram_full {k d : ℕ}
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (hU : Uᵀ * U = 1)
    (x y : SignAssignment k) (T : RowSet k (2 ^ k)) : sampledGram U x y T.1 = 1 := by
  rw [rowSet_full_eq_univ, sampledGram_univ U hU]

section FrameBounds

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Every real matrix with orthonormal columns is a Euclidean contraction. -/
theorem isometry_norm_le_one (U : Matrix I J ℝ) (hU : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hU] at h
  have hI : ‖(1 : Matrix J J ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun _ => by simp)
  have hn := norm_nonneg U
  nlinarith

theorem isometry_projection_norm_le_one (U : Matrix I J ℝ) (hU : Uᵀ * U = 1) :
    ‖U * Uᵀ‖ ≤ 1 := by
  have h := isometry_norm_le_one U hU
  have ht : ‖Uᵀ‖ = ‖U‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose U
  calc
    ‖U * Uᵀ‖ ≤ ‖U‖ * ‖Uᵀ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul h (ht.trans_le h) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The row leverage is the actual sum of squared frame entries. -/
def rowLeverage (U : Matrix I J ℝ) (i : I) : ℝ := ∑ b, U i b ^ 2

theorem rowLeverage_nonneg (U : Matrix I J ℝ) (i : I) : 0 ≤ rowLeverage U i :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem rowLeverage_le_one (U : Matrix I J ℝ) (hU : Uᵀ * U = 1) (i : I) :
    rowLeverage U i ≤ 1 := by
  have h := Matrix.l2_opNorm_mulVec Uᵀ (WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  have ht : ‖Uᵀ‖ = ‖U‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose U
  have hu := isometry_norm_le_one U hU
  change ‖WithLp.toLp 2 (Uᵀ.mulVec (Pi.single i (1 : ℝ)))‖ ≤
    ‖Uᵀ‖ * ‖WithLp.toLp 2 (Pi.single i (1 : ℝ) : I → ℝ)‖ at h
  simp only [Matrix.mulVec_single_one, PiLp.toLp_single, PiLp.norm_single,
    norm_one, mul_one, ht] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) (h.trans hu) 2
  simpa [EuclideanSpace.norm_sq_eq, rowLeverage, Matrix.transpose_apply] using hs

theorem rowLeverage_projection_diagonal (U : Matrix I J ℝ) (i : I) :
    (U * Uᵀ) i i = rowLeverage U i := by
  simp [rowLeverage, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem sum_rowLeverage (U : Matrix I J ℝ) (hU : Uᵀ * U = 1) :
    (∑ i, rowLeverage U i) = Fintype.card J := by
  have hc (b : J) : (∑ i, U i b ^ 2) = 1 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using
      congrArg (fun A : Matrix J J ℝ => A b b) hU
  simp only [rowLeverage]
  rw [Finset.sum_comm]
  simp [hc]

end FrameBounds

end

end SRHT
