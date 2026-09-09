import SparseFockFormal.SparseIIDTransfer
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Convexity of even trace powers

This module isolates the analytic convexity assertion used in the sparse--iid
martingale transfer.  All matrices are finite real symmetric matrices.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace SparseFock.TracePowerConvexity

open SparseIIDTransfer

noncomputable section

set_option linter.style.haveILetI false

/-- A reducible normed-group presentation of `ℝ` whose additive parent is
the algebraic instance used by the one-dimensional convexity API. -/
abbrev standardRealNormedAddCommGroup : NormedAddCommGroup ℝ :=
  { Real.normedAddCommGroup with toAddCommGroup := Real.instAddCommGroup }

/-- The usual real normed-space structure, presented with the algebraic
self-module selected by `ConvexOn`. -/
abbrev standardRealNormedSpace :
    @NormedSpace ℝ ℝ _ standardRealNormedAddCommGroup.toSeminormedAddCommGroup :=
  @NormedSpace.mk ℝ ℝ _ standardRealNormedAddCommGroup.toSeminormedAddCommGroup
    Semiring.toModule (by
      intro a b
      simp only [smul_eq_mul, norm_mul, le_refl])

/-- The homogeneous divided-difference kernel for the monomial `x ^ n`. -/
def geomKernel (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)

/-- The divided-difference kernel of an odd real monomial is nonnegative.
This includes the coincident-point case, where it is a sum of even powers. -/
theorem geomKernel_nonneg_of_odd {n : ℕ} (hn : Odd n) (x y : ℝ) :
    0 ≤ geomKernel n x y := by
  unfold geomKernel
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hpow : x ^ n < y ^ n := hn.strictMono_pow hxy
    have hgeom := (Commute.all x y).mul_geom_sum₂ n
    nlinarith

  · subst y
    obtain ⟨k, rfl⟩ := hn
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← pow_add]
    have hexp : i + (2 * k + 1 - 1 - i) = 2 * k := by omega
    rw [hexp, pow_mul]
    positivity
  · have hpow : y ^ n < x ^ n := hn.strictMono_pow hxy
    have hgeom := (Commute.all x y).mul_geom_sum₂ n
    nlinarith

/-- Matrix trace is invariant under unitary conjugation. -/
theorem trace_conjStarAlgAut {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace (Unitary.conjStarAlgAut ℝ _ U M) = Matrix.trace M := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

/-- Entrywise form of the trace expression occurring in the Hessian after
diagonalizing its symmetric base point. -/
theorem trace_mul_diagonal_pow_mul_mul_diagonal_pow
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.transpose = B) (lambda : Fin d → ℝ) (a c : ℕ) :
    Matrix.trace
        (B * (Matrix.diagonal lambda) ^ a * B * (Matrix.diagonal lambda) ^ c) =
      ∑ i, ∑ j, (B i j) ^ 2 * lambda j ^ a * lambda i ^ c := by
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow]
  rw [Matrix.mul_assoc B (Matrix.diagonal (lambda ^ a)) B]
  have hentry (i : Fin d) :
      (B * (Matrix.diagonal (lambda ^ a) * B)) i i =
        ∑ j, B i j * (lambda j ^ a * B j i) := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diagonal_mul]
    rfl
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  simp_rw [hentry]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrFun (congrFun hB j) i
  simp only [Matrix.transpose_apply] at hs
  rw [hs]
  simp only [Pi.pow_apply]
  ring

/-- Trace as a continuous real-linear functional on finite matrices equipped
with their Euclidean operator norm. -/
def traceCLM (d : ℕ) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin d) ℝ ℝ).toContinuousLinearMap

@[simp] theorem traceCLM_apply {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    traceCLM d A = Matrix.trace A := rfl

/-- An affine matrix line has its direction matrix as derivative. -/
theorem hasDerivAt_affineMatrix {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ A + r • B) B t := by
  simpa using (hasDerivAt_id t).smul_const B |>.const_add A

/-- Cyclicity collapses the noncommutative derivative of a power after taking
trace. -/
theorem trace_power_derivative_sum {d p : ℕ}
    (C B : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace
        (∑ i ∈ Finset.range p, C ^ (p.pred - i) * B * C ^ i) =
      (p : ℝ) * Matrix.trace (B * C ^ (p - 1)) := by
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Matrix.trace_sum]
    have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
    have hterm (i : ℕ) (hi : i ∈ Finset.range p) :
        Matrix.trace (C ^ (p.pred - i) * B * C ^ i) =
          Matrix.trace (B * C ^ (p - 1)) := by
      rw [Matrix.trace_mul_comm (C ^ (p.pred - i) * B) (C ^ i)]
      rw [← Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm (C ^ i * C ^ (p.pred - i)) B]
      rw [← pow_add]
      rw [Finset.mem_range] at hi
      simp only [Nat.pred_eq_sub_one]
      have hexp : i + (p - 1 - i) = p - 1 := by omega
      rw [hexp]
    calc
      (∑ i ∈ Finset.range p,
          Matrix.trace (C ^ (p.pred - i) * B * C ^ i)) =
          ∑ _i ∈ Finset.range p, Matrix.trace (B * C ^ (p - 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i hi
      _ = (p : ℝ) * Matrix.trace (B * C ^ (p - 1)) := by simp

/-- Trace of a matrix power along an affine line. -/
def tracePowerAlong {d : ℕ} (p : ℕ)
    (A B : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) : ℝ :=
  Matrix.trace ((A + t • B) ^ p)

/-- Exact first derivative of a trace power along an arbitrary matrix line. -/
theorem hasDerivAt_tracePowerAlong {d p : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    HasDerivAt (tracePowerAlong p A B)
      ((p : ℝ) * Matrix.trace (B * (A + t • B) ^ (p - 1))) t := by
  letI : NormedAddCommGroup ℝ := standardRealNormedAddCommGroup
  letI : NormedSpace ℝ ℝ := standardRealNormedSpace
  have hpow := (hasDerivAt_affineMatrix A B t).fun_pow' p
  let tr : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin d) ℝ ℝ).toContinuousLinearMap
  have htrace := (hasDerivAt_const t tr).clm_apply hpow
  simp only [zero_apply, zero_add] at htrace
  change HasDerivAt (fun y ↦ Matrix.trace ((A + y • B) ^ p))
    (Matrix.trace
      (∑ i ∈ Finset.range p,
        (A + t • B) ^ (p.pred - i) * B * (A + t • B) ^ i)) t at htrace
  rw [trace_power_derivative_sum] at htrace
  exact htrace

/-- The explicit Hessian of `trace ((A + tB)^p)` in direction `B`. -/
def tracePowerSecondAlong {d : ℕ} (p : ℕ)
    (A B : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) : ℝ :=
  (p : ℝ) *
    ∑ i ∈ Finset.range (p - 1),
      Matrix.trace
        (B * (A + t • B) ^ ((p - 1).pred - i) * B *
          (A + t • B) ^ i)

/-- Exact second derivative of the trace-power polynomial along a line. -/
theorem hasDerivAt_tracePowerFirst {d p : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    HasDerivAt
      (fun r ↦ (p : ℝ) *
        Matrix.trace (B * (A + r • B) ^ (p - 1)))
      (tracePowerSecondAlong p A B t) t := by
  letI : NormedAddCommGroup ℝ := standardRealNormedAddCommGroup
  letI : NormedSpace ℝ ℝ := standardRealNormedSpace
  have hpow := (hasDerivAt_affineMatrix A B t).fun_pow' (p - 1)
  have hleft := hpow.const_mul B
  let tr : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin d) ℝ ℝ).toContinuousLinearMap
  have htrace := (hasDerivAt_const t tr).clm_apply hleft
  simp only [zero_apply, zero_add] at htrace
  change HasDerivAt
    (fun y ↦ Matrix.trace (B * (A + y • B) ^ (p - 1)))
    (Matrix.trace
      (B * ∑ i ∈ Finset.range (p - 1),
        (A + t • B) ^ ((p - 1).pred - i) * B * (A + t • B) ^ i)) t at htrace
  have hscaled := htrace.const_mul (p : ℝ)
  have hsecond :
      Matrix.trace
          (B * ∑ i ∈ Finset.range (p - 1),
            (A + t • B) ^ ((p - 1).pred - i) * B * (A + t • B) ^ i) =
        ∑ i ∈ Finset.range (p - 1),
          Matrix.trace
            (B * (A + t • B) ^ ((p - 1).pred - i) * B *
              (A + t • B) ^ i) := by
    rw [Finset.mul_sum, Matrix.trace_sum]
    simp only [Matrix.mul_assoc]
  rw [hsecond] at hscaled
  exact hscaled

/-- The trace Hessian kernel before multiplication by the scalar exponent. -/
def traceHessianKernel {d : ℕ} (p : ℕ)
    (C B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p - 1),
    Matrix.trace (B * C ^ ((p - 1).pred - k) * B * C ^ k)

/-- Spectral-coordinate expansion of the trace Hessian. -/
theorem traceHessianKernel_eq_spectral {d p : ℕ}
    (C B : Matrix (Fin d) (Fin d) ℝ)
    (hC : C.transpose = C) (hB : B.transpose = B) :
    let hCh : C.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hC
    let U := star hCh.eigenvectorUnitary
    let B' := Unitary.conjStarAlgAut ℝ _ U B
    traceHessianKernel p C B =
      ∑ k ∈ Finset.range (p - 1), ∑ i, ∑ j,
        (B' i j) ^ 2 * (hCh.eigenvalues j) ^ ((p - 1).pred - k) *
          (hCh.eigenvalues i) ^ k := by
  dsimp only
  let hCh : C.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hC
  let U := star hCh.eigenvectorUnitary
  let phi := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) U
  let B' := phi B
  have hdiag : phi C = Matrix.diagonal hCh.eigenvalues := by
    dsimp only [phi, U]
    simpa using hCh.conjStarAlgAut_star_eigenvectorUnitary
  have hBh : B.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hB
  have hB'h : B'.IsHermitian := hBh.isSelfAdjoint.map phi |>.isHermitian
  have hB' : B'.transpose = B' :=
    Matrix.isHermitian_iff_isSymm.mp hB'h
  unfold traceHessianKernel
  apply Finset.sum_congr rfl
  intro k hk
  calc
    Matrix.trace (B * C ^ ((p - 1).pred - k) * B * C ^ k) =
        Matrix.trace
          (phi (B * C ^ ((p - 1).pred - k) * B * C ^ k)) := by
      exact (trace_conjStarAlgAut U _).symm
    _ = Matrix.trace
          (B' * (Matrix.diagonal hCh.eigenvalues) ^ ((p - 1).pred - k) *
            B' * (Matrix.diagonal hCh.eigenvalues) ^ k) := by
      simp only [map_mul, map_pow, B', hdiag]
    _ = ∑ i, ∑ j,
          (B' i j) ^ 2 * (hCh.eigenvalues j) ^ ((p - 1).pred - k) *
            (hCh.eigenvalues i) ^ k :=
      trace_mul_diagonal_pow_mul_mul_diagonal_pow B' hB'
        hCh.eigenvalues _ _

/-- The spectral Hessian sum is nonnegative for a positive even exponent. -/
theorem spectral_traceHessian_nonneg {d p : ℕ} (hp : Even p) (hp0 : p ≠ 0)
    (B : Matrix (Fin d) (Fin d) ℝ) (lambda : Fin d → ℝ) :
    0 ≤ ∑ k ∈ Finset.range (p - 1), ∑ i, ∑ j,
      (B i j) ^ 2 * lambda j ^ ((p - 1).pred - k) * lambda i ^ k := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp0
  have hn : Odd (p - 1) := Nat.Even.sub_odd hp1 hp odd_one
  have hlocal (i j : Fin d) :
      (∑ k ∈ Finset.range (p - 1),
          (B i j) ^ 2 * lambda j ^ ((p - 1).pred - k) * lambda i ^ k) =
        (B i j) ^ 2 * geomKernel (p - 1) (lambda i) (lambda j) := by
    unfold geomKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Nat.pred_eq_sub_one]
    ring
  have hsum :
      (∑ k ∈ Finset.range (p - 1), ∑ i, ∑ j,
          (B i j) ^ 2 * lambda j ^ ((p - 1).pred - k) * lambda i ^ k) =
        ∑ i, ∑ j,
          (B i j) ^ 2 * geomKernel (p - 1) (lambda i) (lambda j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact hlocal i j
  rw [hsum]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sq_nonneg _) (geomKernel_nonneg_of_odd hn _ _)

/-- Nonnegativity of the trace Hessian at symmetric matrices. -/
theorem traceHessianKernel_nonneg {d p : ℕ} (hp : Even p)
    (C B : Matrix (Fin d) (Fin d) ℝ)
    (hC : C.transpose = C) (hB : B.transpose = B) :
    0 ≤ traceHessianKernel p C B := by
  by_cases hp0 : p = 0
  · subst p
    simp [traceHessianKernel]
  · rw [traceHessianKernel_eq_spectral C B hC hB]
    exact spectral_traceHessian_nonneg hp hp0 _ _

/-- The exact second derivative along a symmetric line is nonnegative for an
even exponent. -/
theorem tracePowerSecondAlong_nonneg {d p : ℕ} (hp : Even p)
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (t : ℝ) :
    0 ≤ tracePowerSecondAlong p A B t := by
  have hC : (A + t • B).transpose = A + t • B := by
    ext i j
    have ha := congrFun (congrFun hA i) j
    have hb := congrFun (congrFun hB i) j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply] at ha hb ⊢
    rw [ha, hb]
  change 0 ≤ (p : ℝ) * traceHessianKernel p (A + t • B) B
  exact mul_nonneg (Nat.cast_nonneg p)
    (traceHessianKernel_nonneg hp (A + t • B) B hC hB)

/-- Convexity of an even trace power along every affine line in the symmetric
matrix subspace. -/
theorem convexOn_tracePowerAlong {d p : ℕ} (hp : Even p)
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) :
    ConvexOn ℝ Set.univ (tracePowerAlong p A B) := by
  let first : ℝ → ℝ := fun t ↦
    (p : ℝ) * Matrix.trace (B * (A + t • B) ^ (p - 1))
  let second : ℝ → ℝ := tracePowerSecondAlong p A B
  apply convexOn_of_hasDerivWithinAt2_nonneg (D := Set.univ)
    (f' := first) (f'' := second) convex_univ
  · intro t _
    exact (hasDerivAt_tracePowerAlong A B t).continuousAt.continuousWithinAt
  · intro t _
    exact (hasDerivAt_tracePowerAlong A B t).hasDerivWithinAt
  · intro t _
    exact (hasDerivAt_tracePowerFirst A B t).hasDerivWithinAt
  · intro t _
    exact tracePowerSecondAlong_nonneg hp A B hA hB t

/-- The even trace-power functional on the actual vector space of real
symmetric matrices used by the coupling formalization. -/
def traceEvenPower {d : ℕ} (q : ℕ) (A : SymmetricMatrix d) : ℝ :=
  Matrix.trace ((A : Matrix (Fin d) (Fin d) ℝ) ^ (2 * q))

/-- For every natural `q` (including `q = 0`), `A ↦ tr(A^(2q))` is
convex on the full real vector space of symmetric finite matrices. -/
theorem convexOn_traceEvenPower (d q : ℕ) :
    ConvexOn ℝ Set.univ (traceEvenPower (d := d) q) := by
  refine ⟨convex_univ, ?_⟩
  intro X _ Y _ a b ha hb hab
  let A : Matrix (Fin d) (Fin d) ℝ := X
  let B : Matrix (Fin d) (Fin d) ℝ := Y
  have hA : A.transpose = A := X.property
  have hB : B.transpose = B := Y.property
  have hdir : (B - A).transpose = B - A := by
    ext i j
    have ha' := congrFun (congrFun hA i) j
    have hb' := congrFun (congrFun hB i) j
    simp only [Matrix.transpose_apply, Matrix.sub_apply] at ha' hb' ⊢
    rw [ha', hb']
  have hline := convexOn_tracePowerAlong (even_two_mul q) A (B - A) hA hdir
  have hineq := hline.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    ha hb hab
  have hend : A + (B - A) = B := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  have hcombo : A + b • (B - A) = a • A + b • B := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    calc
      A i j + b * (B i j - A i j) =
          (a + b) * A i j + b * (B i j - A i j) := by rw [hab]; ring
      _ = a * A i j + b * B i j := by ring
  simp only [tracePowerAlong, smul_eq_mul, mul_zero, mul_one, zero_add,
    zero_smul, one_smul, add_zero] at hineq
  rw [hend, hcombo] at hineq
  simpa only [traceEvenPower, Submodule.coe_add,
    Submodule.coe_smul_of_tower, smul_eq_mul] using hineq

/-- The exact trace-moment comparison needed after the sparse--iid
conditional barycenter identity. -/
theorem conditional_traceEvenPower_order {b s n d : ℕ} (hb : 0 < b)
    (F : ParsevalFrame.Frame n d) (x : XArray b s n) (q : ℕ) :
    traceEvenPower q (sparseSymmetricError F x) ≤
      (conditionalArrayLaw hb x).expect
        (fun y ↦ traceEvenPower q (scaledIIDSymmetricError F y)) := by
  exact conditional_convex_order hb F x
    (traceEvenPower q) (convexOn_traceEvenPower d q)

end

end SparseFock.TracePowerConvexity
