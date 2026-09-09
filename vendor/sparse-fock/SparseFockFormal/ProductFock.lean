import SparseFockFormal.FiniteProbability
import SparseFockFormal.FiniteL2
import SparseFockFormal.TernaryJacobi
import SparseFockFormal.FiniteSiteOperators
import Mathlib.Tactic

namespace SparseFock

namespace ProductFock

open scoped BigOperators InnerProductSpace
open FiniteL2 FiniteLaw FiniteOperator LocalOperator

noncomputable section

/-- A literal outcome of all iid normalized coordinates `eta_{ri}`. -/
abbrev Configuration (m n : ℕ) := Site m n → EtaOutcome

/-- The iid product law on all sites. -/
def iidLaw (b : ℕ) (hb : 1 < b) (m n : ℕ) : FiniteLaw (Configuration m n) :=
  FiniteLaw.independentProduct
    (fun _ : Site m n ↦ TernaryJacobi.law b (lt_trans Nat.zero_lt_one hb))

@[simp]
theorem iidLaw_weight (b : ℕ) (hb : 1 < b) (m n : ℕ)
    (omega : Configuration m n) :
    (iidLaw b hb m n).weight omega = ∏ s, TernaryJacobi.mass b (omega s) := rfl

theorem ternaryLaw_expect_eq {b : ℕ} (hb : 0 < b) (g : EtaOutcome → ℝ) :
    (TernaryJacobi.law b hb).expect g = TernaryJacobi.expect b g := rfl

/-- The product orthogonal polynomial indexed by a sparse-Fock pattern. -/
def productBasis {m n : ℕ} (b : ℕ) (p : Pattern m n)
    (omega : Configuration m n) : ℝ :=
  ∏ s, TernaryJacobi.basisFun b (p s) (omega s)

/-- Weighted inner product on the concrete iid product space. -/
def weightedInner {m n : ℕ} (b : ℕ) (hb : 1 < b)
    (f g : Configuration m n → ℝ) : ℝ :=
  (iidLaw b hb m n).expect (fun omega ↦ f omega * g omega)

/-- The product polynomials are exactly orthonormal. -/
theorem productBasis_orthonormal {m n b : ℕ} (hb : 1 < b)
    (p q : Pattern m n) :
    weightedInner b hb (productBasis b p) (productBasis b q) =
      if p = q then 1 else 0 := by
  let mu : Site m n → FiniteLaw EtaOutcome :=
    fun _ ↦ TernaryJacobi.law b (lt_trans Nat.zero_lt_one hb)
  let f : Site m n → EtaOutcome → ℝ := fun s x ↦
    TernaryJacobi.basisFun b (p s) x * TernaryJacobi.basisFun b (q s) x
  have hpoint (omega : Configuration m n) :
      productBasis b p omega * productBasis b q omega = ∏ s, f s (omega s) := by
    simp only [productBasis, f, Finset.prod_mul_distrib]
  have hfactor := FiniteLaw.expect_independentProduct_factorizes mu f
  have hlocal (s : Site m n) :
      (mu s).expect (f s) = if p s = q s then 1 else 0 := by
    dsimp [mu, f]
    change TernaryJacobi.expect b (fun x ↦
      TernaryJacobi.basisFun b (p s) x * TernaryJacobi.basisFun b (q s) x) = _
    simpa [TernaryJacobi.weightedInner] using
      TernaryJacobi.basis_orthonormal hb (p s) (q s)
  change (iidLaw b hb m n).expect
      (fun omega ↦ productBasis b p omega * productBasis b q omega) = _
  calc
    (iidLaw b hb m n).expect
        (fun omega ↦ productBasis b p omega * productBasis b q omega) =
      (FiniteLaw.independentProduct mu).expect (fun omega ↦ ∏ s, f s (omega s)) := by
        apply FiniteLaw.expect_congr
        intro omega
        exact hpoint omega
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

/-- The one-site reproducing kernel, obtained directly from the proved local
completeness formula. -/
theorem local_reproducing {b : ℕ} (hb : 1 < b) (y x : EtaOutcome) :
    TernaryJacobi.mass b y *
        (∑ i, TernaryJacobi.basisFun b i y * TernaryJacobi.basisFun b i x) =
      if x = y then 1 else 0 := by
  have h := TernaryJacobi.basis_reconstruction hb
    (fun z : EtaOutcome ↦ if z = y then 1 else 0) x
  rw [Finset.mul_sum]
  cases y <;>
    simpa [TernaryJacobi.weightedInner, TernaryJacobi.expect, mul_assoc,
      Finset.mul_sum] using h.symm

/-- The sum over all product patterns factors into one local kernel per site. -/
theorem product_kernel_factor {m n b : ℕ} (omega x : Configuration m n) :
    (∑ p : Pattern m n, productBasis b p omega * productBasis b p x) =
      ∏ s, ∑ i, TernaryJacobi.basisFun b i (omega s) *
        TernaryJacobi.basisFun b i (x s) := by
  calc
    (∑ p : Pattern m n, productBasis b p omega * productBasis b p x) =
        ∑ p : Pattern m n, ∏ s,
          (TernaryJacobi.basisFun b (p s) (omega s) *
            TernaryJacobi.basisFun b (p s) (x s)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact Finset.prod_mul_distrib.symm
    _ = ∏ s, ∑ i, TernaryJacobi.basisFun b i (omega s) *
          TernaryJacobi.basisFun b i (x s) := by
      exact (Fintype.prod_sum (fun s i ↦
        TernaryJacobi.basisFun b i (omega s) *
          TernaryJacobi.basisFun b i (x s))).symm

/-- Multiplying the product weight by the product reproducing kernel gives the
Kronecker delta of configurations. -/
theorem weighted_product_kernel {m n b : ℕ} (hb : 1 < b)
    (omega x : Configuration m n) :
    (iidLaw b hb m n).weight omega *
        (∑ p : Pattern m n, productBasis b p omega * productBasis b p x) =
      ∏ s, if x s = omega s then 1 else 0 := by
  rw [iidLaw_weight, product_kernel_factor]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  exact local_reproducing hb (omega s) (x s)

/-- Completeness of the product polynomial family, proved explicitly rather
than inherited from an assumed tensor-product interface. -/
theorem productBasis_reconstruction {m n b : ℕ} (hb : 1 < b)
    (f : Configuration m n → ℝ) (x : Configuration m n) :
    f x = ∑ p : Pattern m n,
      ((iidLaw b hb m n).expect (fun omega ↦ productBasis b p omega * f omega)) *
        productBasis b p x := by
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
            calc
              f omega * (∏ t, if x t = omega t then 1 else 0) = f omega * 0 :=
                congrArg (fun z : ℝ ↦ f omega * z) hz
              _ = 0 := by ring
        _ = f x := by simp
    _ = ∑ omega : Configuration m n,
        f omega * ((iidLaw b hb m n).weight omega *
          ∑ p : Pattern m n, productBasis b p omega * productBasis b p x) := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [weighted_product_kernel hb omega x]
    _ = ∑ p : Pattern m n,
        (∑ omega : Configuration m n,
          (iidLaw b hb m n).weight omega *
            (productBasis b p omega * f omega)) *
            productBasis b p x := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro omega homega
      ring

/-- The all-zero polynomial pattern, i.e. the product vacuum. -/
def vacuumPattern (m n : ℕ) : Pattern m n := fun _ ↦ .zero

/-- The concrete complete orthonormal basis of the iid product `L²` space. -/
def weightedONBasis (b : ℕ) (hb : 1 < b) (m n : ℕ) :
    FiniteL2.WeightedONBasis (Configuration m n) (Pattern m n) where
  weight := (iidLaw b hb m n).weight
  weight_nonneg := (iidLaw b hb m n).weight_nonneg
  sum_weight := (iidLaw b hb m n).sum_weight
  basis := productBasis b
  orthonormal_same := by
    intro p
    simpa [weightedInner, FiniteLaw.expect, mul_assoc] using
      productBasis_orthonormal hb p p
  orthonormal_ne := by
    intro p q hpq
    simpa [weightedInner, FiniteLaw.expect, hpq, mul_assoc] using
      productBasis_orthonormal hb p q
  reconstruction := by
    intro f x
    simpa [FiniteLaw.expect, mul_assoc] using productBasis_reconstruction hb f x
  vacuum := vacuumPattern m n
  vacuum_eq_one := by
    intro omega
    simp [productBasis, vacuumPattern, TernaryJacobi.basisFun]

/-- The coordinate observable `eta_s`. -/
def etaCoordinate {m n : ℕ} (b : ℕ) (s : Site m n) : Configuration m n → ℝ :=
  fun omega ↦ TernaryJacobi.eta b (omega s)

/-- A separated factor used to calculate multiplication by one coordinate. -/
def coordinateFactor {m n : ℕ} (b : ℕ) (s : Site m n)
    (out inp : Pattern m n) (t : Site m n) (x : EtaOutcome) : ℝ :=
  (if t = s then TernaryJacobi.eta b x else 1) *
    TernaryJacobi.basisFun b (out t) x * TernaryJacobi.basisFun b (inp t) x

theorem coordinate_product_factorization {m n b : ℕ} (s : Site m n)
    (out inp : Pattern m n) (omega : Configuration m n) :
    productBasis b out omega *
        (etaCoordinate b s omega * productBasis b inp omega) =
      ∏ t, coordinateFactor b s out inp t (omega t) := by
  simp only [productBasis, etaCoordinate, coordinateFactor]
  simp_rw [Finset.prod_mul_distrib]
  simp
  ring

/-- Multiplication by one iid coordinate is exactly the Jacobi matrix lifted to
that site of the concrete product basis. -/
theorem mulOp_etaCoordinate {m n b : ℕ} (hb : 1 < b) (s : Site m n) :
    (weightedONBasis b hb m n).mulOp (etaCoordinate b s) =
      siteKernel s (jacobi (Real.sqrt ((b : ℝ) - 1))) := by
  classical
  ext out inp
  let mu : Site m n → FiniteLaw EtaOutcome :=
    fun _ ↦ TernaryJacobi.law b (lt_trans Nat.zero_lt_one hb)
  let f : Site m n → EtaOutcome → ℝ := coordinateFactor b s out inp
  have hpoint (omega : Configuration m n) :
      productBasis b out omega *
          (etaCoordinate b s omega * productBasis b inp omega) = ∏ t, f t (omega t) :=
    coordinate_product_factorization s out inp omega
  have hfactor := FiniteLaw.expect_independentProduct_factorizes mu f
  have hlocal (t : Site m n) :
      (mu t).expect (f t) =
        if t = s then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s)
        else if out t = inp t then 1 else 0 := by
    by_cases hts : t = s
    · subst t
      dsimp [mu, f]
      rw [ternaryLaw_expect_eq]
      unfold coordinateFactor
      simp only [if_pos]
      simpa [TernaryJacobi.weightedInner, mul_assoc, mul_comm, mul_left_comm] using
          TernaryJacobi.multiplication_matrix hb (out s) (inp s)
    · dsimp [mu, f]
      rw [ternaryLaw_expect_eq]
      unfold coordinateFactor
      simp only [hts, if_false, one_mul]
      simpa [TernaryJacobi.weightedInner] using
          TernaryJacobi.basis_orthonormal hb (out t) (inp t)
  have hprod :
      (∏ t, if t = s then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s)
        else if out t = inp t then 1 else 0) =
      if agreesOutsideSite s out inp
        then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s) else 0 := by
    by_cases hagree : agreesOutsideSite s out inp
    · simp only [hagree, if_true]
      calc
        (∏ t, if t = s then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s)
          else if out t = inp t then 1 else 0) =
          ∏ t, if t = s then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s)
            else 1 := by
              apply Finset.prod_congr rfl
              intro t ht
              by_cases hts : t = s
              · simp [hts]
              · simp [hts, hagree t hts]
        _ = jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s) := by simp
    · simp only [hagree, if_false]
      unfold agreesOutsideSite at hagree
      push Not at hagree
      obtain ⟨t, hts, hout⟩ := hagree
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp [hts, hout]
  simp only [FiniteL2.WeightedONBasis.mulOp, FiniteL2.WeightedONBasis.coeff,
    weightedONBasis, siteKernel]
  have hexpect : (iidLaw b hb m n).expect
      (fun omega ↦ productBasis b out omega *
        (etaCoordinate b s omega * productBasis b inp omega)) =
      if agreesOutsideSite s out inp
        then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s) else 0 := by
    calc
    (iidLaw b hb m n).expect
        (fun omega ↦ productBasis b out omega *
          (etaCoordinate b s omega * productBasis b inp omega)) =
      (FiniteLaw.independentProduct mu).expect (fun omega ↦ ∏ t, f t (omega t)) := by
        apply FiniteLaw.expect_congr
        intro omega
        exact hpoint omega
    _ = ∏ t, (mu t).expect (f t) := hfactor
    _ = ∏ t, if t = s then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s)
        else if out t = inp t then 1 else 0 := by simp_rw [hlocal]
    _ = if agreesOutsideSite s out inp
        then jacobi (Real.sqrt ((b : ℝ) - 1)) (out s) (inp s) else 0 := hprod
  simpa [FiniteLaw.expect, mul_assoc] using hexpect

/-- Multiplication by two distinct coordinates is the product of the two
concrete lifted Jacobi matrices. -/
theorem mulOp_etaCoordinate_mul {m n b : ℕ} (hb : 1 < b)
    (s t : Site m n) :
    (weightedONBasis b hb m n).mulOp
        (fun omega ↦ etaCoordinate b s omega * etaCoordinate b t omega) =
      siteKernel s (jacobi (Real.sqrt ((b : ℝ) - 1))) *
        siteKernel t (jacobi (Real.sqrt ((b : ℝ) - 1))) := by
  rw [← mulOp_etaCoordinate hb s, ← mulOp_etaCoordinate hb t]
  symm
  exact (weightedONBasis b hb m n).mulOp_mul (etaCoordinate b s) (etaCoordinate b t)

end

end ProductFock

end SparseFock
