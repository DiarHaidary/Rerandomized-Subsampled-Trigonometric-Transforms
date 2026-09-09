import SparseFockFormal.SparseStackDistribution
import SparseFockFormal.FiniteProbability
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace SparseFock

namespace MatrixTail

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The L2 operator norm of a real symmetric matrix is the sup norm of its
real eigenvalue list.  This is an exact consequence of unitary
diagonalization and invariance of the C-star norm under unitary factors. -/
theorem opNorm_eq_piNorm_eigenvalues (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  calc
    ‖A‖ = ‖Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ)
        hA.eigenvectorUnitary
        (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) : ι → ℝ))‖ :=
      congrArg norm hA.spectral_theorem
    _ = ‖hA.eigenvalues‖ := by
      rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rfl

/-- Trace of an arbitrary natural power of a real symmetric matrix, written
as the literal finite sum of the corresponding eigenvalue powers. -/
theorem trace_pow_eq_sum_eigenvalues (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  calc
    (A ^ k).trace =
        ((Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ)
          hA.eigenvectorUnitary
          (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) : ι → ℝ))) ^ k).trace :=
      congrArg (fun M : Matrix ι ι ℝ => (M ^ k).trace) hA.spectral_theorem
    _ = (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ)
          hA.eigenvectorUnitary
          (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) : ι → ℝ) ^ k)).trace := by
      rw [map_pow]
    _ = (star (↑hA.eigenvectorUnitary : Matrix ι ι ℝ) *
          ((↑hA.eigenvectorUnitary : Matrix ι ι ℝ) *
            (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) : ι → ℝ) ^ k))).trace := by
          rw [Unitary.conjStarAlgAut_apply]
          exact Matrix.trace_mul_comm _ _
    _ = (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) : ι → ℝ) ^ k).trace := by
          rw [← mul_assoc, Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i, hA.eigenvalues i ^ k := by
          rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
          rfl

/-- Every even power of a real symmetric matrix has nonnegative trace. -/
theorem trace_even_pow_nonneg (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (q : ℕ) :
    0 ≤ (A ^ (2 * q)).trace := by
  rw [trace_pow_eq_sum_eigenvalues A hA]
  exact Finset.sum_nonneg fun i _hi => (even_two_mul q).pow_nonneg (hA.eigenvalues i)

/-- For a nonempty finite index type, the even power of the L2 operator norm
is bounded by the trace of the corresponding even matrix power. -/
theorem opNorm_even_pow_le_trace_of_nonempty [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (q : ℕ) :
    ‖A‖ ^ (2 * q) ≤ (A ^ (2 * q)).trace := by
  rw [opNorm_eq_piNorm_eigenvalues A hA,
    trace_pow_eq_sum_eigenvalues A hA]
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.eigenvalues).1
  rw [← hi]
  calc
    ‖hA.eigenvalues i‖ ^ (2 * q) = hA.eigenvalues i ^ (2 * q) := by
      rw [Real.norm_eq_abs, ← abs_pow]
      exact abs_of_nonneg ((even_two_mul q).pow_nonneg (hA.eigenvalues i))
    _ ≤ ∑ j, hA.eigenvalues j ^ (2 * q) := by
      exact Finset.single_le_sum
        (fun j _hj => (even_two_mul q).pow_nonneg (hA.eigenvalues j))
        (Finset.mem_univ i)

set_option linter.style.haveILetI false in
/-- The operator-norm/trace bridge also covers the empty matrix index type;
there both sides are definitionally zero. -/
theorem opNorm_even_pow_le_trace (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (q : ℕ) (hq : 0 < q) :
    ‖A‖ ^ (2 * q) ≤ (A ^ (2 * q)).trace := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      haveI : IsEmpty ι := hι
      have hzero : A = 0 := Subsingleton.elim _ _
      subst A
      simp [Nat.ne_of_gt hq]
  | inr hι =>
      haveI : Nonempty ι := hι
      exact opNorm_even_pow_le_trace_of_nonempty A hA q

/-- Finite matrix Markov inequality in the precise form used by the moment
method.  The sample space is literal and finite, and symmetry is assumed
pointwise only to invoke the proved operator-norm/trace inequality above. -/
theorem matrix_markov_tail {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ ω, (A ω).IsHermitian) (q : ℕ) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε) :
    μ.prob {ω | ε ≤ ‖A ω‖} ≤
      μ.expect (fun ω => ((A ω) ^ (2 * q)).trace) / ε ^ (2 * q) := by
  have hpow_ne : 2 * q ≠ 0 := Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hq)
  have hevent : {ω | ε ≤ ‖A ω‖} = {ω | ε ^ (2 * q) ≤ ‖A ω‖ ^ (2 * q)} := by
    ext ω
    exact (pow_le_pow_iff_left₀ hε.le (norm_nonneg _) hpow_ne).symm
  rw [hevent]
  calc
    μ.prob {ω | ε ^ (2 * q) ≤ ‖A ω‖ ^ (2 * q)} ≤
        μ.expect (fun ω => ‖A ω‖ ^ (2 * q)) / ε ^ (2 * q) := by
      exact μ.markov
        (fun ω => pow_nonneg (norm_nonneg (A ω)) (2 * q))
        (pow_pos hε (2 * q))
    _ ≤ μ.expect (fun ω => ((A ω) ^ (2 * q)).trace) / ε ^ (2 * q) := by
      exact div_le_div_of_nonneg_right
        (μ.expect_mono (fun ω => opNorm_even_pow_le_trace (A ω) (hA ω) q hq))
        (pow_nonneg hε.le (2 * q))

/-- The homogeneous quadratic form associated with a real square matrix. -/
def quadraticForm (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, x⟫_ℝ

/-- For a real symmetric matrix, L2 operator-norm control is exactly uniform
control of its homogeneous quadratic form. -/
theorem opNorm_le_iff_quadraticForm (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖A‖ ≤ ε ↔
      ∀ x : EuclideanSpace ℝ ι,
        |quadraticForm A x| ≤ ε * ‖x‖ ^ 2 := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hT : (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι).IsSymmetric := by
    change (Matrix.toEuclideanLin A).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  constructor
  · intro hop x
    have hTx : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    have hTop : ‖T‖ ≤ ε := by simpa [T, Matrix.l2_opNorm_toEuclideanCLM] using hop
    calc
      |quadraticForm A x| = |⟪T x, x⟫_ℝ| := rfl
      _ ≤ ‖T x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hTx (norm_nonneg x)
      _ ≤ (ε * ‖x‖) * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hTop (norm_nonneg x)) (norm_nonneg x)
      _ = ε * ‖x‖ ^ 2 := by ring
  · intro hquad
    change ‖T‖ ≤ ε
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hε
    · have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      have hxquad := hquad x
      rw [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
        abs_of_nonneg hxpos.le]
      apply (div_le_iff₀ hxpos).2
      simpa [quadraticForm, T] using hxquad

/-- The two-sided Gram form of the oblivious-subspace-embedding property. -/
def IsGramOSE (M : Matrix ι ι ℝ) (ε : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ ι,
    (1 - ε) * ‖x‖ ^ 2 ≤ quadraticForm M x ∧
      quadraticForm M x ≤ (1 + ε) * ‖x‖ ^ 2

theorem quadraticForm_sub_one (M : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    quadraticForm (M - 1) x = quadraticForm M x - ‖x‖ ^ 2 := by
  simp [quadraticForm, inner_sub_left]

/-- Exact deterministic OSE equivalence: the L2 operator norm of the Gram
error is at most `ε` iff every vector obeys the usual two-sided squared-norm
distortion inequalities. -/
theorem gramError_norm_le_iff_isGramOSE (M : Matrix ι ι ℝ)
    (hM : M.IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖M - 1‖ ≤ ε ↔ IsGramOSE M ε := by
  have hErr : (M - 1).IsHermitian := hM.sub Matrix.isHermitian_one
  rw [opNorm_le_iff_quadraticForm (M - 1) hErr ε hε]
  constructor
  · intro h x
    have hx := h x
    rw [quadraticForm_sub_one] at hx
    rw [abs_le] at hx
    constructor <;> nlinarith
  · intro h x
    obtain ⟨hlow, hupp⟩ := h x
    rw [quadraticForm_sub_one, abs_le]
    constructor <;> nlinarith

open ParsevalFrame SparseStackModel

/-- The deterministic SparseStack embedded Gram matrix is real symmetric. -/
theorem embeddedGram_isHermitian {s b n d : ℕ}
    (F : Frame n d) (Z : Sample s b n) :
    (embeddedGram F Z).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (embeddedGram F Z).transpose = embeddedGram F Z
  simp [embeddedGram, sketchGram, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Consequently, the literal SparseStack Gram error is real symmetric. -/
theorem sparseStack_gramError_isHermitian {s b n d : ℕ}
    (F : Frame n d) (Z : Sample s b n) :
    (gramError F Z).IsHermitian := by
  exact (embeddedGram_isHermitian F Z).sub Matrix.isHermitian_one

/-- Exact SparseStack OSE equivalence in Gram form. -/
theorem sparseStack_gramError_norm_le_iff_ose {s b n d : ℕ}
    (F : Frame n d) (Z : Sample s b n) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖gramError F Z‖ ≤ ε ↔ IsGramOSE (embeddedGram F Z) ε := by
  simpa only [gramError] using
    gramError_norm_le_iff_isGramOSE (embeddedGram F Z)
      (embeddedGram_isHermitian F Z) ε hε

/-- A rectangular matrix applied to a Euclidean vector, with the codomain
retaining its Euclidean-space wrapper. -/
def applyRectMatrix {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix m n ℝ) (x : EuclideanSpace ℝ n) : EuclideanSpace ℝ m :=
  WithLp.toLp 2 (K.mulVec (WithLp.ofLp x))

/-- The quadratic form of `KᵀK` is exactly the squared Euclidean norm of
`Kx`, including all finite sums and wrappers. -/
theorem quadraticForm_transpose_mul_self {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    quadraticForm (K.transpose * K) x = ‖applyRectMatrix K x‖ ^ 2 := by
  rw [quadraticForm, real_inner_comm, Matrix.inner_toEuclideanCLM]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  rw [EuclideanSpace.norm_sq_eq]
  simp [applyRectMatrix, Real.norm_eq_abs, dotProduct, pow_two]

/-- The actual vector produced by first analyzing in the Parseval frame and
then applying the deterministic SparseStack sketch. -/
def sparseStackVector {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n)
    (x : EVec d) : EuclideanSpace ℝ (Fin s × Fin b) :=
  applyRectMatrix (stackMatrix Z * rowMatrix F.u) x

/-- Exact equality between the embedded Gram quadratic form and the squared
norm of the sketched vector. -/
theorem embeddedGram_quadraticForm {s b n d : ℕ}
    (F : Frame n d) (Z : Sample s b n) (x : EVec d) :
    quadraticForm (embeddedGram F Z) x = ‖sparseStackVector F Z x‖ ^ 2 := by
  have hgram : embeddedGram F Z =
      (stackMatrix Z * rowMatrix F.u).transpose *
        (stackMatrix Z * rowMatrix F.u) := by
    simp [embeddedGram, sketchGram, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hgram]
  exact quadraticForm_transpose_mul_self (stackMatrix Z * rowMatrix F.u) x

/-- The literal vector-norm OSE property for a deterministic SparseStack
outcome and a fixed Parseval input frame. -/
def IsSparseStackOSE {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n)
    (ε : ℝ) : Prop :=
  ∀ x : EVec d,
    (1 - ε) * ‖x‖ ^ 2 ≤ ‖sparseStackVector F Z x‖ ^ 2 ∧
      ‖sparseStackVector F Z x‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2

theorem isGramOSE_embeddedGram_iff_sparseStackOSE {s b n d : ℕ}
    (F : Frame n d) (Z : Sample s b n) (ε : ℝ) :
    IsGramOSE (embeddedGram F Z) ε ↔ IsSparseStackOSE F Z ε := by
  constructor <;> intro h x
  · simpa only [embeddedGram_quadraticForm F Z x] using h x
  · simpa only [embeddedGram_quadraticForm F Z x] using h x

/-- Final deterministic equivalence used by the probability argument: the
bad operator-norm event for the exact Gram error is precisely failure of the
usual two-sided OSE inequality. -/
theorem sparseStack_gramError_norm_le_iff_vector_ose {s b n d : ℕ}
    (F : Frame n d) (Z : Sample s b n) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖gramError F Z‖ ≤ ε ↔ IsSparseStackOSE F Z ε := by
  rw [sparseStack_gramError_norm_le_iff_ose F Z ε hε,
    isGramOSE_embeddedGram_iff_sparseStackOSE]

open SparseStackDistribution

/-- The concrete finite-law Markov tail for the actual independent uniform
signed-hash SparseStack distribution. -/
theorem sparseStack_matrix_markov_tail {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    (rawSampleLaw s b n hb).prob
        {z | ε ≤ ‖gramError F (toSample z)‖} ≤
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
        ε ^ (2 * q) := by
  exact matrix_markov_tail (rawSampleLaw s b n hb)
    (fun z => gramError F (toSample z))
    (fun z => sparseStack_gramError_isHermitian F (toSample z)) q hq ε hε

/-- Failure of the vector OSE property is contained in the concrete norm-tail
event, so it obeys the same trace-moment bound. -/
theorem sparseStack_ose_failure_tail {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    (rawSampleLaw s b n hb).prob
        {z | ¬ IsSparseStackOSE F (toSample z) ε} ≤
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
        ε ^ (2 * q) := by
  calc
    (rawSampleLaw s b n hb).prob
        {z | ¬ IsSparseStackOSE F (toSample z) ε} ≤
        (rawSampleLaw s b n hb).prob
          {z | ε ≤ ‖gramError F (toSample z)‖} := by
      apply FiniteLaw.prob_mono
      intro z hz
      have hiff := sparseStack_gramError_norm_le_iff_vector_ose
        F (toSample z) ε hε.le
      by_contra htail
      exact hz (hiff.mp (not_le.mp htail).le)
    _ ≤ (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
        ε ^ (2 * q) := sparseStack_matrix_markov_tail hb F q hq ε hε

/-- A supplied trace-moment estimate immediately yields an explicit lower
bound on the OSE success probability under the exact SparseStack law. -/
theorem sparseStack_ose_success_probability {s b n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ)
    (hmoment :
      (rawSampleLaw s b n hb).expect
          (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
        ε ^ (2 * q) ≤ δ) :
    1 - δ ≤ (rawSampleLaw s b n hb).prob
      {z | IsSparseStackOSE F (toSample z) ε} := by
  let good : Set (RawSample s b n) :=
    {z | IsSparseStackOSE F (toSample z) ε}
  have hfail : (rawSampleLaw s b n hb).prob goodᶜ ≤ δ := by
    calc
      (rawSampleLaw s b n hb).prob goodᶜ =
          (rawSampleLaw s b n hb).prob
            {z | ¬ IsSparseStackOSE F (toSample z) ε} := by
        rfl
      _ ≤ (rawSampleLaw s b n hb).expect
            (fun z => ((gramError F (toSample z)) ^ (2 * q)).trace) /
          ε ^ (2 * q) := sparseStack_ose_failure_tail hb F q hq ε hε
      _ ≤ δ := hmoment
  calc
    1 - δ ≤ 1 - (rawSampleLaw s b n hb).prob goodᶜ := by
      exact sub_le_sub_left hfail 1
    _ = (rawSampleLaw s b n hb).prob good := by
      simpa using (FiniteLaw.prob_compl (rawSampleLaw s b n hb) goodᶜ).symm
    _ = (rawSampleLaw s b n hb).prob
        {z | IsSparseStackOSE F (toSample z) ε} := rfl

end

end MatrixTail

end SparseFock
