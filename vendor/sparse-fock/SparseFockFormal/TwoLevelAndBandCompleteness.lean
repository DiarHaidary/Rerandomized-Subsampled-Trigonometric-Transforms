import SparseFockFormal.FiniteL2
import SparseFockFormal.FiniteProbability
import SparseFockFormal.Pattern
import SparseFockFormal.ParsevalFrame
import Mathlib.Tactic

/-!
# Two-level endpoint and exact completeness statements

At `b = 1` the one-site probability space and polynomial space both have
exactly two elements, with basis `(1, eta)` and Jacobi matrix
`[[0, 1], [1, 0]]`.  This file constructs that endpoint model directly,
rather than representing it as a degenerate three-level model.
-/

namespace SparseFock

open scoped BigOperators

namespace TwoLevelEndpoint

open FiniteLaw FiniteL2 ParsevalFrame

noncomputable section

/-- The literal two-point outcome space at the endpoint `b = 1`. -/
abbrev Outcome := Fin 2

/-- The normalized endpoint coordinate, taking the two values `-1` and `1`. -/
def eta (x : Outcome) : ℝ := if x = 0 then -1 else 1

@[simp] theorem eta_zero : eta (0 : Outcome) = -1 := by simp [eta]

@[simp] theorem eta_one : eta (1 : Outcome) = 1 := by simp [eta]

theorem eta_sq (x : Outcome) : eta x ^ 2 = 1 := by
  fin_cases x <;> norm_num [eta]

/-- Exhaustion of the local endpoint state space: level `2` is literally
absent from the type. -/
theorem outcome_eq_zero_or_one (x : Outcome) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- The local Fock basis index likewise has exactly levels `0` and `1`. -/
theorem localLevel_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- The endpoint law: the two signs have mass one half each. -/
def law : FiniteLaw Outcome where
  weight := fun _ ↦ (1 : ℝ) / 2
  weight_nonneg := by intro x; positivity
  sum_weight := by
    rw [Fin.sum_univ_two]
    norm_num

@[simp] theorem law_weight (x : Outcome) : law.weight x = (1 : ℝ) / 2 := rfl

/-- At the endpoint, each of the two nonzero signs has probability one half. -/
theorem prob_eta_eq_neg_one : law.prob {x | eta x = -1} = (1 : ℝ) / 2 := by
  simp [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator,
    law, eta, Fin.sum_univ_two] <;> norm_num

theorem prob_eta_eq_one : law.prob {x | eta x = 1} = (1 : ℝ) / 2 := by
  simp [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator,
    law, eta, Fin.sum_univ_two] <;> norm_num

/-- The zero value from the ternary law has zero probability when `b = 1`. -/
theorem prob_eta_eq_zero : law.prob {x | eta x = 0} = 0 := by
  simp [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator,
    law, eta, Fin.sum_univ_two]

/-- The endpoint coordinate is centered. -/
theorem expect_eta : law.expect eta = 0 := by
  simp [FiniteLaw.expect, law, Fin.sum_univ_two, eta]

/-- The endpoint coordinate has unit second moment. -/
theorem expect_eta_sq : law.expect (fun x ↦ eta x ^ 2) = 1 := by
  simp [FiniteLaw.expect, law, eta_sq, Fin.sum_univ_two]

/-- The literal local polynomial basis `(1, eta)`. -/
def basis (i : Fin 2) (x : Outcome) : ℝ :=
  if i = 0 then 1 else eta x

@[simp] theorem basis_zero (x : Outcome) : basis 0 x = 1 := by simp [basis]

@[simp] theorem basis_one (x : Outcome) : basis 1 x = eta x := by simp [basis]

/-- The two local endpoint polynomials are exactly orthonormal. -/
theorem basis_orthonormal (i j : Fin 2) :
    law.expect (fun x ↦ basis i x * basis j x) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [FiniteLaw.expect, Fin.sum_univ_two, basis, eta] <;> norm_num

/-- The two local endpoint polynomials are complete, point by point. -/
theorem basis_reconstruction (f : Outcome → ℝ) (x : Outcome) :
    f x = ∑ i : Fin 2,
      law.expect (fun y ↦ basis i y * f y) * basis i x := by
  fin_cases x <;>
    simp [FiniteLaw.expect, Fin.sum_univ_two, basis, eta] <;> ring

/-- The complete weighted local basis at the endpoint. -/
def localONBasis : WeightedONBasis Outcome (Fin 2) where
  weight := law.weight
  weight_nonneg := law.weight_nonneg
  sum_weight := law.sum_weight
  basis := basis
  orthonormal_same := by
    intro i
    simpa [FiniteLaw.expect, mul_assoc] using basis_orthonormal i i
  orthonormal_ne := by
    intro i j hij
    simpa [FiniteLaw.expect, hij, mul_assoc] using basis_orthonormal i j
  reconstruction := by
    intro f x
    simpa [FiniteLaw.expect, mul_assoc] using basis_reconstruction f x
  vacuum := 0
  vacuum_eq_one := basis_zero

/-- The endpoint Jacobi matrix `[[0,1],[1,0]]`. -/
def jacobi : Matrix (Fin 2) (Fin 2) ℝ :=
  fun out inp ↦ if out = inp then 0 else 1

@[simp] theorem jacobi_apply (out inp : Fin 2) :
    jacobi out inp = if out = inp then 0 else 1 := rfl

theorem jacobi_zero_zero : jacobi 0 0 = 0 := by simp
theorem jacobi_zero_one : jacobi 0 1 = 1 := by simp
theorem jacobi_one_zero : jacobi 1 0 = 1 := by simp
theorem jacobi_one_one : jacobi 1 1 = 0 := by simp

/-- Multiplication by `eta` in the literal basis `(1, eta)` is exactly the
two-by-two endpoint Jacobi matrix. -/
theorem local_mulOp_eta : localONBasis.mulOp eta = jacobi := by
  ext out inp
  fin_cases out <;> fin_cases inp <;>
    simp [WeightedONBasis.mulOp, WeightedONBasis.coeff, localONBasis,
      Fin.sum_univ_two, law, basis, eta, jacobi] <;> norm_num

/-- A literal endpoint product configuration. -/
abbrev Configuration (m n : ℕ) := Site m n → Outcome

/-- A literal endpoint product-Fock index.  Every site has only levels `0`
and `1`; there is no level `2` constructor in this type. -/
abbrev Pattern (m n : ℕ) := Site m n → Fin 2

/-- The independent product of the endpoint two-point laws. -/
def iidLaw (m n : ℕ) : FiniteLaw (Configuration m n) :=
  FiniteLaw.independentProduct (fun _ : Site m n ↦ law)

@[simp] theorem iidLaw_weight (m n : ℕ) (omega : Configuration m n) :
    (iidLaw m n).weight omega = ∏ _s : Site m n, (1 : ℝ) / 2 := rfl

/-- Exact factorization of all endpoint coordinate-cylinder events: the
coordinates are mutually independent, not merely pairwise independent. -/
theorem iidLaw_prob_cylinder {m n : ℕ} (events : Site m n → Set Outcome) :
    (iidLaw m n).prob (FiniteLaw.cylinder events) =
      ∏ s, law.prob (events s) := by
  simpa [iidLaw] using
    (FiniteLaw.prob_independentProduct_cylinder
      (fun _ : Site m n ↦ law) events)

/-- Tensor product of the local basis `(1, eta)` over all sites. -/
def productBasis {m n : ℕ} (p : Pattern m n) (omega : Configuration m n) : ℝ :=
  ∏ s, basis (p s) (omega s)

/-- Weighted product-space inner product. -/
def weightedInner {m n : ℕ}
    (f g : Configuration m n → ℝ) : ℝ :=
  (iidLaw m n).expect (fun omega ↦ f omega * g omega)

/-- The endpoint product basis is exactly orthonormal. -/
theorem productBasis_orthonormal {m n : ℕ} (p q : Pattern m n) :
    weightedInner (productBasis p) (productBasis q) =
      if p = q then 1 else 0 := by
  let mu : Site m n → FiniteLaw Outcome := fun _ ↦ law
  let f : Site m n → Outcome → ℝ := fun s x ↦
    basis (p s) x * basis (q s) x
  have hpoint (omega : Configuration m n) :
      productBasis p omega * productBasis q omega = ∏ s, f s (omega s) := by
    simp only [productBasis, f, Finset.prod_mul_distrib]
  have hfactor := FiniteLaw.expect_independentProduct_factorizes mu f
  have hlocal (s : Site m n) :
      (mu s).expect (f s) = if p s = q s then 1 else 0 := by
    exact basis_orthonormal (p s) (q s)
  change (iidLaw m n).expect
      (fun omega ↦ productBasis p omega * productBasis q omega) = _
  calc
    (iidLaw m n).expect
        (fun omega ↦ productBasis p omega * productBasis q omega) =
      (FiniteLaw.independentProduct mu).expect (fun omega ↦ ∏ s, f s (omega s)) := by
        apply FiniteLaw.expect_congr
        exact hpoint
    _ = ∏ s, (mu s).expect (f s) := hfactor
    _ = ∏ s, if p s = q s then 1 else 0 := by simp_rw [hlocal]
    _ = if p = q then 1 else 0 := by
      by_cases hpq : p = q
      · subst q
        simp
      · simp only [hpq, if_false]
        have hex : ∃ s, p s ≠ q s := by
          by_contra hall
          push Not at hall
          exact hpq (funext hall)
        obtain ⟨s, hs⟩ := hex
        apply Finset.prod_eq_zero (Finset.mem_univ s)
        simp [hs]

/-- The local weighted reproducing kernel for the endpoint basis. -/
theorem local_reproducing (y x : Outcome) :
    law.weight y * (∑ i : Fin 2, basis i y * basis i x) =
      if x = y then 1 else 0 := by
  fin_cases y <;> fin_cases x <;>
    simp [law, basis, eta, Fin.sum_univ_two] <;> norm_num

/-- The sum over all endpoint product patterns factors sitewise. -/
theorem product_kernel_factor {m n : ℕ}
    (omega x : Configuration m n) :
    (∑ p : Pattern m n, productBasis p omega * productBasis p x) =
      ∏ s, ∑ i : Fin 2, basis i (omega s) * basis i (x s) := by
  calc
    (∑ p : Pattern m n, productBasis p omega * productBasis p x) =
        ∑ p : Pattern m n, ∏ s,
          (basis (p s) (omega s) * basis (p s) (x s)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact Finset.prod_mul_distrib.symm
    _ = ∏ s, ∑ i : Fin 2, basis i (omega s) * basis i (x s) := by
      exact (Fintype.prod_sum (fun s i ↦
        basis i (omega s) * basis i (x s))).symm

/-- Product weight times product reproducing kernel is the point mass. -/
theorem weighted_product_kernel {m n : ℕ}
    (omega x : Configuration m n) :
    (iidLaw m n).weight omega *
        (∑ p : Pattern m n, productBasis p omega * productBasis p x) =
      ∏ s, if x s = omega s then 1 else 0 := by
  rw [iidLaw_weight, product_kernel_factor]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  exact local_reproducing (omega s) (x s)

/-- Pointwise completeness of the endpoint tensor-product basis. -/
theorem productBasis_reconstruction {m n : ℕ}
    (f : Configuration m n → ℝ) (x : Configuration m n) :
    f x = ∑ p : Pattern m n,
      ((iidLaw m n).expect (fun omega ↦ productBasis p omega * f omega)) *
        productBasis p x := by
  classical
  simp only [FiniteLaw.expect]
  calc
    f x = ∑ omega : Configuration m n,
        f omega * (∏ s, if x s = omega s then 1 else 0) := by
      symm
      calc
        (∑ omega : Configuration m n,
            f omega * (∏ s, if x s = omega s then 1 else 0)) =
          f x * (∏ s, if x s = x s then 1 else 0) := by
            apply Fintype.sum_eq_single x
            intro omega hne
            have hex : ∃ s, x s ≠ omega s := by
              by_contra hall
              push Not at hall
              exact hne (funext hall).symm
            obtain ⟨s, hs⟩ := hex
            have hz : (∏ t, if x t = omega t then (1 : ℝ) else 0) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ s)
              simp [hs]
            rw [hz, mul_zero]
        _ = f x := by simp
    _ = ∑ omega : Configuration m n,
        f omega * ((iidLaw m n).weight omega *
          ∑ p : Pattern m n, productBasis p omega * productBasis p x) := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [weighted_product_kernel omega x]
    _ = ∑ p : Pattern m n,
        (∑ omega : Configuration m n,
          (iidLaw m n).weight omega *
            (productBasis p omega * f omega)) * productBasis p x := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro omega homega
      ring

/-- The endpoint product vacuum is the all-constant (`0`) basis index. -/
def vacuumPattern (m n : ℕ) : Pattern m n := fun _ ↦ 0

/-- The complete endpoint product-Fock basis. -/
def weightedONBasis (m n : ℕ) :
    WeightedONBasis (Configuration m n) (Pattern m n) where
  weight := (iidLaw m n).weight
  weight_nonneg := (iidLaw m n).weight_nonneg
  sum_weight := (iidLaw m n).sum_weight
  basis := productBasis
  orthonormal_same := by
    intro p
    simpa [weightedInner, FiniteLaw.expect, mul_assoc] using
      productBasis_orthonormal p p
  orthonormal_ne := by
    intro p q hpq
    simpa [weightedInner, FiniteLaw.expect, hpq, mul_assoc] using
      productBasis_orthonormal p q
  reconstruction := by
    intro f x
    simpa [FiniteLaw.expect, mul_assoc] using productBasis_reconstruction f x
  vacuum := vacuumPattern m n
  vacuum_eq_one := by
    intro omega
    simp [productBasis, vacuumPattern]

/-- Coordinate observable in the two-level product model. -/
def etaCoordinate {m n : ℕ} (s : Site m n) : Configuration m n → ℝ :=
  fun omega ↦ eta (omega s)

/-- Two endpoint patterns agree away from one distinguished site. -/
def agreesOutsideSite {m n : ℕ} (s : Site m n)
    (out inp : Pattern m n) : Prop :=
  ∀ t, t ≠ s → out t = inp t

/-- Lift a two-by-two local operator to one site of the literal endpoint
product-Fock basis. -/
noncomputable def siteKernel {m n : ℕ} (s : Site m n)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Pattern m n) (Pattern m n) ℝ :=
  by
    classical
    exact fun out inp ↦
      if agreesOutsideSite s out inp then A (out s) (inp s) else 0

/-- A separated local factor used to calculate multiplication by one endpoint
coordinate in the product basis. -/
def coordinateFactor {m n : ℕ} (s : Site m n)
    (out inp : Pattern m n) (t : Site m n) (x : Outcome) : ℝ :=
  (if t = s then eta x else 1) * basis (out t) x * basis (inp t) x

theorem coordinate_product_factorization {m n : ℕ} (s : Site m n)
    (out inp : Pattern m n) (omega : Configuration m n) :
    productBasis out omega *
        (etaCoordinate s omega * productBasis inp omega) =
      ∏ t, coordinateFactor s out inp t (omega t) := by
  simp only [productBasis, etaCoordinate, coordinateFactor]
  simp_rw [Finset.prod_mul_distrib]
  simp
  ring

/-- Multiplication by one coordinate in the endpoint product basis is exactly
the endpoint Jacobi matrix lifted at that site. -/
theorem mulOp_etaCoordinate {m n : ℕ} (s : Site m n) :
    (weightedONBasis m n).mulOp (etaCoordinate s) = siteKernel s jacobi := by
  classical
  ext out inp
  let mu : Site m n → FiniteLaw Outcome := fun _ ↦ law
  let f : Site m n → Outcome → ℝ := coordinateFactor s out inp
  have hpoint (omega : Configuration m n) :
      productBasis out omega *
          (etaCoordinate s omega * productBasis inp omega) = ∏ t, f t (omega t) :=
    coordinate_product_factorization s out inp omega
  have hfactor := FiniteLaw.expect_independentProduct_factorizes mu f
  have hlocal (t : Site m n) :
      (mu t).expect (f t) =
        if t = s then jacobi (out s) (inp s)
        else if out t = inp t then 1 else 0 := by
    by_cases hts : t = s
    · subst t
      simp only [if_true]
      have hentry := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M (out s) (inp s)) local_mulOp_eta
      simpa [mu, f, coordinateFactor, WeightedONBasis.mulOp,
        WeightedONBasis.coeff, localONBasis, FiniteLaw.expect,
        mul_assoc, mul_comm, mul_left_comm] using hentry
    · simp only [hts, if_false]
      dsimp [mu, f]
      unfold coordinateFactor
      simp only [hts, if_false, one_mul]
      simpa [FiniteLaw.expect, mul_assoc] using basis_orthonormal (out t) (inp t)
  have hprod :
      (∏ t, if t = s then jacobi (out s) (inp s)
        else if out t = inp t then 1 else 0) =
      if agreesOutsideSite s out inp then jacobi (out s) (inp s) else 0 := by
    by_cases hagree : agreesOutsideSite s out inp
    · simp only [hagree, if_true]
      calc
        (∏ t, if t = s then jacobi (out s) (inp s)
          else if out t = inp t then 1 else 0) =
          ∏ t, if t = s then jacobi (out s) (inp s) else 1 := by
            apply Finset.prod_congr rfl
            intro t ht
            by_cases hts : t = s
            · simp [hts]
            · simp [hts, hagree t hts]
        _ = jacobi (out s) (inp s) := by simp
    · simp only [hagree, if_false]
      unfold agreesOutsideSite at hagree
      push Not at hagree
      obtain ⟨t, hts, hout⟩ := hagree
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp [hts, hout]
  simp only [WeightedONBasis.mulOp, WeightedONBasis.coeff,
    weightedONBasis, siteKernel]
  have hexpect : (iidLaw m n).expect
      (fun omega ↦ productBasis out omega *
        (etaCoordinate s omega * productBasis inp omega)) =
      if agreesOutsideSite s out inp then jacobi (out s) (inp s) else 0 := by
    calc
      (iidLaw m n).expect
          (fun omega ↦ productBasis out omega *
            (etaCoordinate s omega * productBasis inp omega)) =
        (FiniteLaw.independentProduct mu).expect
          (fun omega ↦ ∏ t, f t (omega t)) := by
            apply FiniteLaw.expect_congr
            exact hpoint
      _ = ∏ t, (mu t).expect (f t) := hfactor
      _ = ∏ t, if t = s then jacobi (out s) (inp s)
          else if out t = inp t then 1 else 0 := by simp_rw [hlocal]
      _ = if agreesOutsideSite s out inp then
          jacobi (out s) (inp s) else 0 := hprod
  simpa [FiniteLaw.expect, mul_assoc] using hexpect

/-- Multiplication by two endpoint coordinates is the product of their two
lifted endpoint Jacobi matrices (valid also when the two sites coincide). -/
theorem mulOp_etaCoordinate_mul {m n : ℕ} (s t : Site m n) :
    (weightedONBasis m n).mulOp
        (fun omega ↦ etaCoordinate s omega * etaCoordinate t omega) =
      siteKernel s jacobi * siteKernel t jacobi := by
  rw [← mulOp_etaCoordinate s, ← mulOp_etaCoordinate t]
  symm
  exact (weightedONBasis m n).mulOp_mul (etaCoordinate s) (etaCoordinate t)

/-- Tensor a matrix on the external `Fin d` leg with a two-level product-Fock
matrix. -/
def externalTensor {m n d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Pattern m n) (Pattern m n) ℝ) :
    Matrix (Fin d × Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ M out.1 inp.1 * K out.2 inp.2

section MatrixMulOpLinearity

variable {Omega I A K : Type*}
  [Fintype Omega] [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype K]

theorem matrixMulOp_smul (B : WeightedONBasis Omega I) (c : ℝ)
    (M : Omega → Matrix A A ℝ) :
    B.matrixMulOp (fun omega ↦ c • M omega) = c • B.matrixMulOp M := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  ring

theorem matrixMulOp_fintype_sum (B : WeightedONBasis Omega I)
    (M : K → Omega → Matrix A A ℝ) :
    B.matrixMulOp (fun omega ↦ ∑ k, M k omega) =
      ∑ k, B.matrixMulOp (M k) := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem matrixMulOp_finset_sum (B : WeightedONBasis Omega I)
    (S : Finset K) (M : K → Omega → Matrix A A ℝ) :
    B.matrixMulOp (fun omega ↦ ∑ k ∈ S, M k omega) =
      ∑ k ∈ S, B.matrixMulOp (M k) := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.coeff,
    Matrix.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end MatrixMulOpLinearity

/-- A scalar endpoint observable multiplying a fixed external matrix becomes
the external tensor product of that matrix with the scalar multiplication
matrix. -/
theorem matrixMulOp_scalar_external {m n d : ℕ}
    (a : Configuration m n → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (weightedONBasis m n).matrixMulOp (fun omega ↦ a omega • M) =
      externalTensor M ((weightedONBasis m n).mulOp a) := by
  ext out inp
  simp only [WeightedONBasis.matrixMulOp, WeightedONBasis.mulOp,
    WeightedONBasis.coeff, externalTensor, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  ring

/-- The normalized endpoint iid-coordinate Gram error. -/
def iidGramError {m n d : ℕ} (F : Frame n d)
    (omega : Configuration m n) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (m : ℝ)) •
    ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
      (etaCoordinate (r, i) omega * etaCoordinate (r, j) omega) •
        ParsevalFrame.outer (F.u i) (F.u j)

/-- Matrix-valued multiplication by the endpoint Gram error. -/
def multiplicationOperator {m n d : ℕ} (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (Fin d × Pattern m n) ℝ :=
  (weightedONBasis m n).matrixMulOp (iidGramError F)

/-- The explicit endpoint Fock operator: a normalized sum of external
rank-one coefficients tensored with products of two lifted copies of
`J = [[0,1],[1,0]]`. -/
def globalJacobiOperator {m n d : ℕ} (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (Fin d × Pattern m n) ℝ :=
  (1 / (m : ℝ)) •
    ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
      externalTensor (ParsevalFrame.outer (F.u i) (F.u j))
        (siteKernel (r, i) jacobi * siteKernel (r, j) jacobi)

/-- The product-basis multiplication matrix is literally the explicit global
sum of external rank-one terms and lifted endpoint Jacobi matrices. -/
theorem multiplicationOperator_eq_globalJacobi {m n d : ℕ}
    (F : Frame n d) :
    multiplicationOperator (m := m) F = globalJacobiOperator (m := m) F := by
  let B := weightedONBasis m n
  change B.matrixMulOp (iidGramError F) = _
  rw [show iidGramError F = fun omega ↦ (1 / (m : ℝ)) •
      ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
        (etaCoordinate (r, i) omega * etaCoordinate (r, j) omega) •
          ParsevalFrame.outer (F.u i) (F.u j) from rfl]
  rw [matrixMulOp_smul]
  rw [matrixMulOp_fintype_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [matrixMulOp_fintype_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [matrixMulOp_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixMulOp_scalar_external]
  rw [mulOp_etaCoordinate_mul]

/-- The exact endpoint vacuum-moment identity for every natural power,
including power zero.  It has no `b > 1` premise. -/
theorem vacuum_moment_identity {m n d : ℕ} (F : Frame n d) (k : ℕ) :
    (∑ a : Fin d,
      (multiplicationOperator (m := m) F ^ k)
        (a, vacuumPattern m n) (a, vacuumPattern m n)) =
      (iidLaw m n).expect
        (fun omega ↦ Matrix.trace ((iidGramError F omega) ^ k)) := by
  simpa [multiplicationOperator, weightedONBasis,
    WeightedONBasis.expect, FiniteLaw.expect] using
      (weightedONBasis m n).matrix_vacuum_moment (iidGramError F) k

/-- The same exact identity written directly with the explicit global lifted
Jacobi operator from the endpoint product Fock model. -/
theorem vacuum_moment_identity_globalJacobi {m n d : ℕ}
    (F : Frame n d) (k : ℕ) :
    (∑ a : Fin d,
      (globalJacobiOperator (m := m) F ^ k)
        (a, vacuumPattern m n) (a, vacuumPattern m n)) =
      (iidLaw m n).expect
        (fun omega ↦ Matrix.trace ((iidGramError F omega) ^ k)) := by
  rw [← multiplicationOperator_eq_globalJacobi]
  exact vacuum_moment_identity F k

end

end TwoLevelEndpoint

end SparseFock
