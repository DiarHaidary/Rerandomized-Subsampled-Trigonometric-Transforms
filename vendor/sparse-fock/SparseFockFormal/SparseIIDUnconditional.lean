import SparseFockFormal.SparseIIDTransfer

/-!
# Unconditional sparse--iid convex-order transfer

This file completes the finite-probability part of the sparse--iid coupling.
The selectors at all `(g,i)` sites are given their literal product law.  Given
the selector array, the ternary vectors are sampled from the literal product
of the one-column conditional laws.  We prove, pointwise in every ternary
array, that the resulting mixture is exactly its iid product law.  Averaging
the conditional Jensen inequality therefore gives unconditional convex order.
-/

open scoped BigOperators

namespace SparseFock.SparseIIDUnconditional

open ParsevalFrame SparseStackDistribution SparseIIDCoupling SparseIIDTransfer

noncomputable section

/-- The literal product law of all uniform signed selectors `X_(g,i)`. -/
def selectorArrayLaw {b : ℕ} (hb : 0 < b) (s n : ℕ) :
    FiniteLaw (XArray b s n) :=
  FiniteLaw.independentProduct
    (fun _ : ArraySite s n ↦ selectorLaw b hb)

@[simp] theorem selectorArrayLaw_weight {b : ℕ} (hb : 0 < b)
    (s n : ℕ) (x : XArray b s n) :
    (selectorArrayLaw hb s n).weight x =
      ∏ z : ArraySite s n, (selectorLaw b hb).weight (x z) := rfl

/-- The literal product law of all iid ternary vectors `Y_(g,i)`.  Each vector
itself has the literal product law of its `b` ternary coordinates. -/
def iidArrayLaw {b : ℕ} (hb : 0 < b) (s n : ℕ) :
    FiniteLaw (YArray b s n) :=
  FiniteLaw.independentProduct
    (fun _ : ArraySite s n ↦ yVectorLaw b hb)

@[simp] theorem iidArrayLaw_weight {b : ℕ} (hb : 0 < b)
    (s n : ℕ) (y : YArray b s n) :
    (iidArrayLaw hb s n).weight y =
      ∏ z : ArraySite s n, (yVectorLaw b hb).weight (y z) := rfl

/-- First sample the independent selector array and then sample, conditionally
and independently at every site, its associated ternary vectors. -/
def conditionalMixtureLaw {b : ℕ} (hb : 0 < b) (s n : ℕ) :
    FiniteLaw (YArray b s n) where
  weight y := ∑ x, (selectorArrayLaw hb s n).weight x *
    (conditionalArrayLaw hb x).weight y
  weight_nonneg y := Finset.sum_nonneg fun x _hx ↦
    mul_nonneg ((selectorArrayLaw hb s n).weight_nonneg x)
      ((conditionalArrayLaw hb x).weight_nonneg y)
  sum_weight := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (conditionalArrayLaw hb _).sum_weight, mul_one]
    exact (selectorArrayLaw hb s n).sum_weight

@[simp] theorem conditionalMixtureLaw_weight {b : ℕ} (hb : 0 < b)
    (s n : ℕ) (y : YArray b s n) :
    (conditionalMixtureLaw hb s n).weight y =
      ∑ x, (selectorArrayLaw hb s n).weight x *
        (conditionalArrayLaw hb x).weight y := rfl

/-- One-column disintegration recovers the original iid ternary-vector mass. -/
theorem oneColumn_mixture_weight {b : ℕ} (hb : 0 < b) (y : YVector b) :
    (∑ x : SignedHash b, (selectorLaw b hb).weight x *
        (conditionalYLaw hb x).weight y) =
      (yVectorLaw b hb).weight y := by
  simp_rw [← jointColumn_disintegrates hb y]
  simp_rw [jointColumnLaw_weight, ← Finset.mul_sum, sum_kernelWeight hb, mul_one]

/-- The conditional product mixture has, pointwise, exactly the iid product
mass.  This is the full finite-array marginal identity, not merely equality of
selected moments. -/
theorem conditionalMixtureLaw_weight_eq_iidArrayLaw_weight
    {b : ℕ} (hb : 0 < b) (s n : ℕ) (y : YArray b s n) :
    (conditionalMixtureLaw hb s n).weight y =
      (iidArrayLaw hb s n).weight y := by
  simp only [conditionalMixtureLaw_weight, selectorArrayLaw_weight,
    conditionalArrayLaw, FiniteLaw.independentProduct_weight,
    iidArrayLaw_weight]
  simp_rw [← Finset.prod_mul_distrib]
  calc
    (∑ x : ArraySite s n → SignedHash b,
        ∏ z : ArraySite s n,
          (selectorLaw b hb).weight (x z) *
            (conditionalYLaw hb (x z)).weight (y z)) =
        ∏ z : ArraySite s n, ∑ x : SignedHash b,
          (selectorLaw b hb).weight x *
            (conditionalYLaw hb x).weight (y z) :=
      (Fintype.prod_sum (fun z (x : SignedHash b) ↦
        (selectorLaw b hb).weight x *
          (conditionalYLaw hb x).weight (y z))).symm
    _ = ∏ z : ArraySite s n, (yVectorLaw b hb).weight (y z) := by
      apply Finset.prod_congr rfl
      intro z _hz
      exact oneColumn_mixture_weight hb (y z)

/-- Consequently every real observable has the same expectation under the
conditional mixture and under the iid ternary-array law. -/
theorem conditionalMixtureLaw_expect_eq_iidArrayLaw_expect
    {b : ℕ} (hb : 0 < b) (s n : ℕ) (f : YArray b s n → ℝ) :
    (conditionalMixtureLaw hb s n).expect f =
      (iidArrayLaw hb s n).expect f := by
  rw [FiniteLaw.expect, FiniteLaw.expect]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [conditionalMixtureLaw_weight_eq_iidArrayLaw_weight hb s n y]

/-- The expectation under the explicit mixture is the iterated expectation:
first over the selector array, then over its conditional ternary array. -/
theorem conditionalMixtureLaw_expect_eq_iterated
    {b : ℕ} (hb : 0 < b) (s n : ℕ) (f : YArray b s n → ℝ) :
    (conditionalMixtureLaw hb s n).expect f =
      (selectorArrayLaw hb s n).expect
        (fun x ↦ (conditionalArrayLaw hb x).expect f) := by
  simp only [FiniteLaw.expect, conditionalMixtureLaw_weight]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  ring

/-- Unconditional sparse--iid convex order on the actual real vector space of
symmetric matrices.  The only analytic premise is the displayed convexity of
the chosen observable `Phi`; every probability law and independence claim is
the explicit finite law defined above. -/
theorem unconditional_convex_order {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (Phi : SymmetricMatrix d → ℝ)
    (hPhi : ConvexOn ℝ Set.univ Phi) :
    (selectorArrayLaw hb s n).expect
        (fun x ↦ Phi (sparseSymmetricError F x)) ≤
      (iidArrayLaw hb s n).expect
        (fun y ↦ Phi (scaledIIDSymmetricError F y)) := by
  calc
    (selectorArrayLaw hb s n).expect
        (fun x ↦ Phi (sparseSymmetricError F x)) ≤
        (selectorArrayLaw hb s n).expect
          (fun x ↦ (conditionalArrayLaw hb x).expect
            (fun y ↦ Phi (scaledIIDSymmetricError F y))) := by
      apply FiniteLaw.expect_mono
      intro x
      exact conditional_convex_order hb F x Phi hPhi
    _ = (conditionalMixtureLaw hb s n).expect
          (fun y ↦ Phi (scaledIIDSymmetricError F y)) :=
      (conditionalMixtureLaw_expect_eq_iterated hb s n
        (fun y ↦ Phi (scaledIIDSymmetricError F y))).symm
    _ = (iidArrayLaw hb s n).expect
          (fun y ↦ Phi (scaledIIDSymmetricError F y)) :=
      conditionalMixtureLaw_expect_eq_iidArrayLaw_expect hb s n
        (fun y ↦ Phi (scaledIIDSymmetricError F y))

end

end SparseFock.SparseIIDUnconditional
