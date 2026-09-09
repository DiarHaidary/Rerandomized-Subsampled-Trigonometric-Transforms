import SparseFockFormal.SparseIIDUnconditional
import SparseFockFormal.VacuumMoment
import SparseFockFormal.MatrixTail
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Exact distribution and indexing bridges

This file identifies the selector-array law used by the martingale coupling
with the literal SparseStack law, and formalizes the flattening
`(g,a) in Fin s x Fin b` to `r in Fin (s*b)` used by the iid Fock model.
-/

namespace SparseFock.DistributionBridges

open scoped BigOperators InnerProductSpace
open ParsevalFrame SparseStackModel SparseStackDistribution
open SparseIIDCoupling SparseIIDTransfer SparseIIDUnconditional
open ProductFock VacuumMoment

noncomputable section

variable {s b n d : ℕ}

/-- The coupling's `XArray` and the SparseStack primitive sample space are
definitionally the same product type, and so are their laws. -/
theorem selectorArrayLaw_eq_rawSampleLaw (hb : 0 < b) :
    selectorArrayLaw hb s n = rawSampleLaw s b n hb :=
  rfl

/-- The selector vector in the coupling is exactly the signed basis vector in
the deterministic SparseStack model. -/
theorem selectorVector_eq_signedBasis (x : XArray b s n)
    (g : Fin s) (i : Fin n) :
    selectorVector (x (g, i)) = signedBasis (toSample x) g i := by
  ext a
  simp only [selectorVector, signedBasis_apply, toSample_hash, toSample_sign]
  by_cases h : a = (x (g, i)).1
  · simp [h]
  · have h' : (x (g, i)).1 ≠ a := Ne.symm h
    simp [h, h']

/-- The sparse matrix in the coupling is the literal deterministic
SparseStack Gram error. -/
theorem sparseVectorError_eq_gramError (hs : 0 < s)
    (F : Frame n d) (x : XArray b s n) :
    sparseVectorError F x = gramError F (toSample x) := by
  rw [SparseStackModel.gramError_eq_block_first F (toSample x) hs]
  ext a c
  simp only [sparseVectorError, Matrix.smul_apply, Matrix.sum_apply,
    ParsevalFrame.outer_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [selectorVector_eq_signedBasis, selectorVector_eq_signedBasis]
  ring

/-- Reindex one nested coordinate `((g,i),a)` as the flattened site `(r,i)`.
The chosen convention is `r = g*b+a`. -/
def nestedSiteEquiv (s b n : ℕ) :
    ((Fin s × Fin n) × Fin b) ≃ (Fin (s * b) × Fin n) where
  toFun z := (finProdFinEquiv (z.1.1, z.2), z.1.2)
  invFun z :=
    let ga := finProdFinEquiv.symm z.1
    ((ga.1, z.2), ga.2)
  left_inv z := by
    rcases z with ⟨⟨g, i⟩, a⟩
    simp
  right_inv z := by
    rcases z with ⟨r, i⟩
    apply Prod.ext
    · exact finProdFinEquiv.apply_symm_apply r
    · rfl

/-- Flatten a nested iid-vector array into the product-Fock configuration. -/
def flattenY (y : YArray b s n) : Configuration (s * b) n :=
  fun ri ↦
    let ga := finProdFinEquiv.symm ri.1
    y (ga.1, ri.2) ga.2

/-- Unflatten a product-Fock configuration into its block/vector form. -/
def unflattenY (omega : Configuration (s * b) n) : YArray b s n :=
  fun gi a ↦ omega (finProdFinEquiv (gi.1, a), gi.2)

/-- Flattening is a genuine finite equivalence, not just an informal index
identification. -/
def flattenYEquiv (s b n : ℕ) :
    YArray b s n ≃ Configuration (s * b) n where
  toFun := flattenY
  invFun := unflattenY
  left_inv y := by
    funext gi a
    rcases gi with ⟨g, i⟩
    simp [flattenY, unflattenY]
  right_inv omega := by
    funext ri
    rcases ri with ⟨r, i⟩
    change omega (finProdFinEquiv (finProdFinEquiv.symm r), i) = omega (r, i)
    rw [finProdFinEquiv.apply_symm_apply]

@[simp] theorem flattenY_apply_pair (y : YArray b s n)
    (g : Fin s) (a : Fin b) (i : Fin n) :
    flattenY y (finProdFinEquiv (g, a), i) = y (g, i) a := by
  simp [flattenY]

/-- Pointwise probability masses are preserved by flattening. -/
theorem iidArrayLaw_weight_eq_iidLaw_weight (hb : 1 < b)
    (y : YArray b s n) :
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).weight y =
      (iidLaw b hb (s * b) n).weight (flattenY y) := by
  rw [iidArrayLaw_weight, iidLaw_weight]
  simp_rw [SparseIIDCoupling.yVectorLaw_weight (lt_trans Nat.zero_lt_one hb)]
  rw [← Fintype.prod_prod_type'
    (fun z : Fin s × Fin n ↦ fun a : Fin b ↦
      TernaryJacobi.mass b (y z a))]
  apply Fintype.prod_equiv (nestedSiteEquiv s b n)
  intro z
  rcases z with ⟨⟨g, i⟩, a⟩
  simp [nestedSiteEquiv, flattenY_apply_pair]

/-- Every observable has exactly the same expectation under the nested iid
array law and the flattened product-Fock law. -/
theorem iidArrayLaw_expect_flatten_eq_iidLaw_expect (hb : 1 < b)
    (f : Configuration (s * b) n → ℝ) :
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ f (flattenY y)) =
      (iidLaw b hb (s * b) n).expect f := by
  simp only [FiniteLaw.expect]
  apply Fintype.sum_equiv (flattenYEquiv s b n)
  intro y
  rw [iidArrayLaw_weight_eq_iidLaw_weight hb y]
  rfl

/-- The normalized Fock coordinate is `sqrt(b)` times the unscaled coupling
coordinate. -/
theorem eta_eq_sqrt_mul_yValue (z : EtaOutcome) :
    TernaryJacobi.eta b z = Real.sqrt b * yValue z := by
  cases z <;> simp [TernaryJacobi.eta, yValue]

/-- The inner product of two nested iid vectors is the sum of the products of
their corresponding flattened normalized coordinates, divided by `b`. -/
theorem sum_eta_flatten_product (hb : 0 < b) (y : YArray b s n)
    (g : Fin s) (i j : Fin n) :
    (∑ a : Fin b,
      TernaryJacobi.eta b (flattenY y (finProdFinEquiv (g, a), i)) *
        TernaryJacobi.eta b (flattenY y (finProdFinEquiv (g, a), j))) =
      (b : ℝ) * inner ℝ (unscaledYVector (y (g, i)))
        (unscaledYVector (y (g, j))) := by
  simp only [flattenY_apply_pair, eta_eq_sqrt_mul_yValue,
    PiLp.inner_apply, Real.inner_apply, unscaledYVector_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hsqrt := TernaryJacobi.sq_sqrt_nat b
  calc
    Real.sqrt b * yValue (y (g, i) a) *
        (Real.sqrt b * yValue (y (g, j) a)) =
        (Real.sqrt b) ^ 2 *
          (yValue (y (g, i) a) * yValue (y (g, j) a)) := by ring
    _ = (b : ℝ) *
          (yValue (y (g, i) a) * yValue (y (g, j) a)) := by rw [hsqrt]

/-- The iid-vector error before coupling scaling is exactly the flattened
product-Fock iid Gram error. -/
theorem iidVectorError_eq_flattened_iidGramError
    (hs : 0 < s) (hb : 1 < b) (F : Frame n d) (y : YArray b s n) :
    iidVectorError F y = iidGramError b F (flattenY y) := by
  ext a c
  simp only [iidVectorError, iidGramError, Matrix.smul_apply,
    Matrix.sum_apply, ParsevalFrame.outer_apply, smul_eq_mul]
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hbR : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb))
  let C : Fin n → Fin n → ℝ := fun i j ↦ F.u i a * F.u j c
  let E : Fin (s * b) → Fin n → Fin n → ℝ := fun r i j ↦
    etaCoordinate b (r, i) (flattenY y) *
      etaCoordinate b (r, j) (flattenY y)
  let Y : Fin s → Fin n → Fin n → ℝ := fun g i j ↦
    inner ℝ (unscaledYVector (y (g, i))) (unscaledYVector (y (g, j)))
  have hrow (g : Fin s) (i j : Fin n) :
      (∑ q : Fin b, E (finProdFinEquiv (g, q)) i j) = (b : ℝ) * Y g i j := by
    simpa [E, Y, etaCoordinate] using sum_eta_flatten_product
      (b := b) (n := n) (s := s) (lt_trans Nat.zero_lt_one hb) y g i j
  have hreindex :
      (∑ r : Fin (s * b), ∑ i, ∑ j ∈ Finset.univ.erase i,
        E r i j * C i j) =
      (b : ℝ) * ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
        Y g i j * C i j := by
    calc
      (∑ r : Fin (s * b), ∑ i, ∑ j ∈ Finset.univ.erase i,
          E r i j * C i j) =
          ∑ ga : Fin s × Fin b, ∑ i, ∑ j ∈ Finset.univ.erase i,
            E (finProdFinEquiv ga) i j * C i j := by
        exact (finProdFinEquiv.sum_comp
          (fun r : Fin (s * b) ↦ ∑ i, ∑ j ∈ Finset.univ.erase i,
            E r i j * C i j)).symm
      _ = ∑ g, ∑ q, ∑ i, ∑ j ∈ Finset.univ.erase i,
            E (finProdFinEquiv (g, q)) i j * C i j := by
        rw [Fintype.sum_prod_type]
      _ = ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
            (∑ q, E (finProdFinEquiv (g, q)) i j) * C i j := by
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ = ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
            ((b : ℝ) * Y g i j) * C i j := by
        simp_rw [hrow]
      _ = (b : ℝ) * ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
            Y g i j * C i j := by
        simp_rw [Finset.mul_sum]
        ring
  change (1 / (s : ℝ)) *
      ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i, Y g i j * C i j =
    (1 / ((s * b : ℕ) : ℝ)) *
      ∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i, E r i j * C i j
  rw [hreindex]
  push_cast
  field_simp

end

end SparseFock.DistributionBridges
