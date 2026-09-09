import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace SparseFock

namespace ParsevalFrame

open scoped BigOperators InnerProductSpace

noncomputable section

/-- The real Euclidean space used for the rows of the input matrix. -/
abbrev EVec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Squared Euclidean norm, kept as an inner product so all finite sums remain exact. -/
def normSq {d : ℕ} (x : EVec d) : ℝ := ⟪x, x⟫_ℝ

theorem normSq_eq_norm_sq {d : ℕ} (x : EVec d) : normSq x = ‖x‖ ^ 2 := by
  exact real_inner_self_eq_norm_sq x

/-- The rank-one matrix `x yᵀ`. -/
def outer {d : ℕ} (x y : EVec d) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b ↦ x a * y b

@[simp]
theorem outer_apply {d : ℕ} (x y : EVec d) (a b : Fin d) :
    outer x y a b = x a * y b := rfl

/-- Transposing a rank-one matrix reverses its two vector factors. -/
theorem outer_transpose {d : ℕ} (x y : EVec d) :
    (outer x y).transpose = outer y x := by
  ext a b
  simp [outer, Matrix.transpose_apply, mul_comm]

/-- A finite Parseval frame, encoded by the exact identity `Σᵢ uᵢuᵢᵀ = I`. -/
structure Frame (n d : ℕ) where
  u : Fin n → EVec d
  parseval : (∑ i, outer (u i) (u i)) = (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The `n × d` matrix whose row `i` is `u i`. -/
def rowMatrix {n d : ℕ} (u : Fin n → EVec d) : Matrix (Fin n) (Fin d) ℝ :=
  fun i a ↦ u i a

/-- The frame operator of an arbitrary finite family. -/
def frameOperator {n d : ℕ} (u : Fin n → EVec d) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, outer (u i) (u i)

/-- Apply a real matrix to a Euclidean vector, retaining the Euclidean-space wrapper. -/
def applyMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : EVec d) : EVec d :=
  WithLp.toLp 2 (A.mulVec fun a ↦ x a)

@[simp]
theorem applyMatrix_one {d : ℕ} (x : EVec d) :
    applyMatrix (1 : Matrix (Fin d) (Fin d) ℝ) x = x := by
  ext a
  simp [applyMatrix]

/-- The matrix Parseval identity is exactly the usual orthonormal-column identity `UᵀU = I`. -/
theorem parseval_iff_transpose_mul {n d : ℕ} (u : Fin n → EVec d) :
    frameOperator u = (1 : Matrix (Fin d) (Fin d) ℝ) ↔
      (rowMatrix u).transpose * rowMatrix u = (1 : Matrix (Fin d) (Fin d) ℝ) := by
  constructor
  · intro h
    rw [← h]
    ext a b
    simp [frameOperator, rowMatrix, outer, Matrix.mul_apply, Matrix.sum_apply]
  · intro h
    rw [← h]
    ext a b
    simp [frameOperator, rowMatrix, outer, Matrix.mul_apply, Matrix.sum_apply]

theorem transpose_mul_rowMatrix {n d : ℕ} (F : Frame n d) :
    (rowMatrix F.u).transpose * rowMatrix F.u =
      (1 : Matrix (Fin d) (Fin d) ℝ) :=
  (parseval_iff_transpose_mul F.u).mp F.parseval

/-- Analysis coefficients of a vector against a frame. -/
def analyze {n d : ℕ} (F : Frame n d) (x : EVec d) (i : Fin n) : ℝ :=
  ⟪F.u i, x⟫_ℝ

/-- Synthesis using only coefficients whose indices lie in `S`. -/
def synthesize {n d : ℕ} (F : Frame n d) (S : Finset (Fin n))
    (a : Fin n → ℝ) : EVec d :=
  ∑ i ∈ S, a i • F.u i

/-- The positive partial frame operator `Σ_{i∈S} uᵢuᵢᵀ`. -/
def partialFrameOperator {n d : ℕ} (F : Frame n d) (S : Finset (Fin n)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a b ↦ ∑ i ∈ S, F.u i a * F.u i b

theorem synthesize_inner {n d : ℕ} (F : Frame n d) (S : Finset (Fin n))
    (a : Fin n → ℝ) (x : EVec d) :
    ⟪synthesize F S a, x⟫_ℝ = ∑ i ∈ S, a i * ⟪F.u i, x⟫_ℝ := by
  simp [synthesize, sum_inner, real_inner_smul_left]

/-- The partial frame operator applied to `x` is synthesis of its analysis coefficients. -/
theorem partialFrameOperator_mulVec {n d : ℕ} (F : Frame n d)
    (S : Finset (Fin n)) (x : EVec d) :
    applyMatrix (partialFrameOperator F S) x = synthesize F S (analyze F x) := by
  ext a
  simp only [applyMatrix, PiLp.toLp_apply, partialFrameOperator, Matrix.mulVec, dotProduct,
    synthesize, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    PiLp.inner_apply, analyze, Pi.smul_apply, smul_eq_mul, Real.inner_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Exact reconstruction by a Parseval frame. -/
theorem reconstruct {n d : ℕ} (F : Frame n d) (x : EVec d) :
    synthesize F Finset.univ (analyze F x) = x := by
  rw [← partialFrameOperator_mulVec]
  have hpartial : partialFrameOperator F Finset.univ =
      (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext a b
    have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M a b) F.parseval
    simpa [partialFrameOperator, Matrix.sum_apply, outer] using hab
  rw [hpartial]
  exact applyMatrix_one x

/-- Parseval's exact energy identity. -/
theorem analysis_energy_eq {n d : ℕ} (F : Frame n d) (x : EVec d) :
    (∑ i, (analyze F x i) ^ 2) = normSq x := by
  have hrec := reconstruct F x
  calc
    (∑ i, (analyze F x i) ^ 2) =
        ⟪synthesize F Finset.univ (analyze F x), x⟫_ℝ := by
          rw [synthesize_inner]
          apply Finset.sum_congr rfl
          intro i hi
          simp [analyze, pow_two]
    _ = ⟪x, x⟫_ℝ := by rw [hrec]
    _ = normSq x := rfl

/-- The subset analysis/Bessel inequality from (4.16):
`Σ_{i∈S} (uᵢᵀx)² ≤ ‖x‖²`. -/
theorem subset_analysis {n d : ℕ} (F : Frame n d) (S : Finset (Fin n))
    (x : EVec d) :
    (∑ i ∈ S, (analyze F x i) ^ 2) ≤ normSq x := by
  calc
    (∑ i ∈ S, (analyze F x i) ^ 2) ≤
        ∑ i, (analyze F x i) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun i ↦ sq_nonneg (analyze F x i))
    _ = normSq x := analysis_energy_eq F x

/-- The subset synthesis inequality from (4.16):
`‖Σ_{i∈S} uᵢaᵢ‖² ≤ Σ_{i∈S}|aᵢ|²`. -/
theorem subset_synthesis {n d : ℕ} (F : Frame n d) (S : Finset (Fin n))
    (a : Fin n → ℝ) :
    normSq (synthesize F S a) ≤ ∑ i ∈ S, |a i| ^ 2 := by
  let y : EVec d := synthesize F S a
  let b : Fin n → ℝ := fun i ↦ ⟪F.u i, y⟫_ℝ
  have hid : normSq y = ∑ i ∈ S, a i * b i := by
    change ⟪y, y⟫_ℝ = _
    simpa [y, b] using synthesize_inner F S a y
  have hpoint (i : Fin n) : 2 * a i * b i ≤ (a i) ^ 2 + (b i) ^ 2 := by
    nlinarith [sq_nonneg (a i - b i)]
  have hsum :
      2 * (∑ i ∈ S, a i * b i) ≤
        (∑ i ∈ S, (a i) ^ 2) + ∑ i ∈ S, (b i) ^ 2 := by
    calc
      2 * (∑ i ∈ S, a i * b i) = ∑ i ∈ S, 2 * a i * b i := by
        simp_rw [Finset.mul_sum]
        ring
      _ ≤ ∑ i ∈ S, ((a i) ^ 2 + (b i) ^ 2) := by
        exact Finset.sum_le_sum (fun i hi ↦ hpoint i)
      _ = (∑ i ∈ S, (a i) ^ 2) + ∑ i ∈ S, (b i) ^ 2 := by
        rw [Finset.sum_add_distrib]
  have hb : (∑ i ∈ S, (b i) ^ 2) ≤ normSq y := by
    simpa [b, analyze] using subset_analysis F S y
  have hsquares : normSq y ≤ ∑ i ∈ S, (a i) ^ 2 := by
    nlinarith [hsum]
  simpa only [sq_abs] using hsquares

/-- Every vector in a Parseval frame has squared norm at most one. -/
theorem vector_normSq_le_one {n d : ℕ} (F : Frame n d) (i : Fin n) :
    normSq (F.u i) ≤ 1 := by
  have h := subset_analysis F {i} (F.u i)
  have hnonneg : 0 ≤ normSq (F.u i) := by
    exact real_inner_self_nonneg
  have hii : analyze F (F.u i) i = normSq (F.u i) := rfl
  simp only [Finset.sum_singleton, hii] at h
  nlinarith

/-- Every Parseval-frame vector has Euclidean norm at most one. -/
theorem vector_norm_le_one {n d : ℕ} (F : Frame n d) (i : Fin n) :
    ‖F.u i‖ ≤ 1 := by
  have h := vector_normSq_le_one F i
  rw [normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (F.u i)]

/-- The partial frame operator is a Euclidean contraction.  This is the
squared-norm form of `‖Σ_{i∈S}uᵢuᵢᵀ‖ ≤ 1` in (4.16). -/
theorem partialFrameOperator_contraction {n d : ℕ} (F : Frame n d)
    (S : Finset (Fin n)) (x : EVec d) :
    normSq (applyMatrix (partialFrameOperator F S) x) ≤ normSq x := by
  rw [partialFrameOperator_mulVec]
  calc
    normSq (synthesize F S (analyze F x)) ≤
        ∑ i ∈ S, |analyze F x i| ^ 2 := subset_synthesis F S (analyze F x)
    _ = ∑ i ∈ S, (analyze F x i) ^ 2 := by simp only [sq_abs]
    _ ≤ normSq x := subset_analysis F S x

end

end ParsevalFrame

end SparseFock
