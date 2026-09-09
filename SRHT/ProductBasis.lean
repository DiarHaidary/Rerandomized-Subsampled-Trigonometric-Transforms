import SparseFockFormal.FiniteL2
import SparseFockFormal.FiniteProbability
import Mathlib.Tactic

namespace SRHT.ProductBasis
open SparseFock SparseFock.FiniteL2
open scoped BigOperators
noncomputable section

variable {S Ω I : Type*} [Fintype S] [Fintype Ω] [Fintype I]
  [DecidableEq S] [DecidableEq Ω] [DecidableEq I]

def lawOfBasis (B : WeightedONBasis Ω I) : FiniteLaw Ω :=
  ⟨B.weight, B.weight_nonneg, B.sum_weight⟩

theorem local_reproducing (B : WeightedONBasis Ω I) (y x : Ω) :
    B.weight y * (∑ i, B.basis i y * B.basis i x) =
      if x = y then 1 else 0 := by
  have h := B.reconstruction (fun z => if z = y then 1 else 0) x
  simpa [Finset.mul_sum, mul_assoc] using h.symm

def piLaw (B : S → WeightedONBasis Ω I) : FiniteLaw (S → Ω) :=
  FiniteLaw.independentProduct (fun s => lawOfBasis (B s))

def piBasis (B : S → WeightedONBasis Ω I) (p : S → I) (x : S → Ω) : ℝ :=
  ∏ s, (B s).basis (p s) (x s)

theorem pi_orthonormal (B : S → WeightedONBasis Ω I) (p q : S → I) :
    (piLaw B).expect (fun x => piBasis B p x * piBasis B q x) =
      if p = q then 1 else 0 := by
  classical
  have hfactor := FiniteLaw.expect_independentProduct_factorizes
    (fun s => lawOfBasis (B s))
    (fun s x => (B s).basis (p s) x * (B s).basis (q s) x)
  have hlocal (s : S) :
      (lawOfBasis (B s)).expect (fun x =>
        (B s).basis (p s) x * (B s).basis (q s) x) =
        if p s = q s then 1 else 0 := by
    by_cases h : p s = q s
    · simpa [FiniteLaw.expect, lawOfBasis, h, mul_assoc] using
        (B s).orthonormal_same (q s)
    · simpa [FiniteLaw.expect, lawOfBasis, h, mul_assoc] using
        (B s).orthonormal_ne (p s) (q s) h
  calc
    (piLaw B).expect (fun x => piBasis B p x * piBasis B q x) =
      ∏ s, (lawOfBasis (B s)).expect (fun x =>
        (B s).basis (p s) x * (B s).basis (q s) x) := by
      simpa [piLaw, piBasis, Finset.prod_mul_distrib] using hfactor
    _ = ∏ s, if p s = q s then 1 else 0 := by simp_rw [hlocal]
    _ = if p = q then 1 else 0 := by
      by_cases h : p = q
      · simp [h]
      · simp only [h, if_false]
        obtain ⟨s, hs⟩ : ∃ s, p s ≠ q s := by
          by_contra hn
          push Not at hn
          exact h (funext hn)
        exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

theorem pi_kernel (B : S → WeightedONBasis Ω I) (y x : S → Ω) :
    (piLaw B).weight y * (∑ p, piBasis B p y * piBasis B p x) =
      ∏ s, if x s = y s then 1 else 0 := by
  have hfactor : (∑ p, piBasis B p y * piBasis B p x) =
      ∏ s, ∑ i, (B s).basis i (y s) * (B s).basis i (x s) := by
    simpa [piBasis, Finset.prod_mul_distrib] using
      (Fintype.prod_sum (fun s i => (B s).basis i (y s) * (B s).basis i (x s))).symm
  rw [hfactor]
  change (∏ s, (B s).weight (y s)) * _ = _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  exact local_reproducing (B s) (y s) (x s)

theorem pi_reconstruction (B : S → WeightedONBasis Ω I)
    (f : (S → Ω) → ℝ) (x : S → Ω) :
    f x = ∑ p, ((piLaw B).expect (fun y => piBasis B p y * f y)) * piBasis B p x := by
  classical
  have hdelta : (∑ y : S → Ω, f y * (∏ s, if x s = y s then 1 else 0)) = f x := by
    rw [Fintype.sum_eq_single x]
    · simp
    · intro y hne
      obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := by
        by_contra hn
        push Not at hn
        exact hne (funext hn).symm
      have hz : (∏ t, if x t = y t then (1 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])
      rw [hz, mul_zero]
  calc
    f x = ∑ y : S → Ω, f y * (∏ s, if x s = y s then 1 else 0) := hdelta.symm
    _ = ∑ y : S → Ω, f y * ((piLaw B).weight y *
        ∑ p, piBasis B p y * piBasis B p x) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [pi_kernel]
    _ = ∑ p, ((piLaw B).expect (fun y => piBasis B p y * f y)) * piBasis B p x := by
      simp_rw [FiniteLaw.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring

def pi (B : S → WeightedONBasis Ω I) : WeightedONBasis (S → Ω) (S → I) where
  weight := (piLaw B).weight
  weight_nonneg := (piLaw B).weight_nonneg
  sum_weight := (piLaw B).sum_weight
  basis := piBasis B
  orthonormal_same p := by
    simpa [FiniteLaw.expect, mul_assoc] using pi_orthonormal B p p
  orthonormal_ne p q h := by
    simpa [FiniteLaw.expect, mul_assoc, h] using pi_orthonormal B p q
  reconstruction f x := by
    simpa [FiniteLaw.expect, mul_assoc] using pi_reconstruction B f x
  vacuum := fun s => (B s).vacuum
  vacuum_eq_one x := by simp [piBasis, WeightedONBasis.vacuum_eq_one]

def reindex {J : Type*} [Fintype J] (B : WeightedONBasis Ω I) (e : J ≃ I) :
    WeightedONBasis Ω J where
  weight := B.weight
  weight_nonneg := B.weight_nonneg
  sum_weight := B.sum_weight
  basis j := B.basis (e j)
  orthonormal_same j := B.orthonormal_same (e j)
  orthonormal_ne j k h := B.orthonormal_ne (e j) (e k) (e.injective.ne h)
  reconstruction f x := by
    calc
      f x = ∑ i : I, (∑ y, B.weight y * B.basis i y * f y) * B.basis i x :=
        B.reconstruction f x
      _ = ∑ j : J, (∑ y, B.weight y * B.basis (e j) y * f y) * B.basis (e j) x :=
        (e.sum_comp (fun i => (∑ y, B.weight y * B.basis i y * f y) *
          B.basis i x)).symm
  vacuum := e.symm B.vacuum
  vacuum_eq_one x := by simp [B.vacuum_eq_one]

section BinaryProduct
variable {Ω' I' : Type*} [Fintype Ω'] [Fintype I']
  [DecidableEq Ω'] [DecidableEq I']

def prodFun (B : WeightedONBasis Ω I) (C : WeightedONBasis Ω' I')
    (i : I × I') (x : Ω × Ω') : ℝ :=
  B.basis i.1 x.1 * C.basis i.2 x.2

theorem prod_inner (B : WeightedONBasis Ω I) (C : WeightedONBasis Ω' I')
    (i j : I × I') :
    (∑ x : Ω × Ω', (B.weight x.1 * C.weight x.2) *
      prodFun B C i x * prodFun B C j x) =
    (∑ x, B.weight x * B.basis i.1 x * B.basis j.1 x) *
      (∑ y, C.weight y * C.basis i.2 y * C.basis j.2 y) := by
  simp only [Fintype.sum_prod_type, prodFun]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem prod_orthonormal (B : WeightedONBasis Ω I) (C : WeightedONBasis Ω' I')
    (i j : I × I') :
    (∑ x : Ω × Ω', (B.weight x.1 * C.weight x.2) *
      prodFun B C i x * prodFun B C j x) = if i = j then 1 else 0 := by
  rw [prod_inner]
  have hB : (∑ x, B.weight x * B.basis i.1 x * B.basis j.1 x) =
      if i.1 = j.1 then 1 else 0 := by
    split_ifs with h
    · rw [h]; exact B.orthonormal_same _
    · exact B.orthonormal_ne _ _ h
  have hC : (∑ y, C.weight y * C.basis i.2 y * C.basis j.2 y) =
      if i.2 = j.2 then 1 else 0 := by
    split_ifs with h
    · rw [h]; exact C.orthonormal_same _
    · exact C.orthonormal_ne _ _ h
  rw [hB,hC]
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;>
    simp [h1,h2,Prod.ext_iff]

theorem prod_kernel (B : WeightedONBasis Ω I) (C : WeightedONBasis Ω' I')
    (y x : Ω × Ω') :
    (B.weight y.1*C.weight y.2) *
      (∑ i, prodFun B C i y * prodFun B C i x) = if x=y then 1 else 0 := by
  have heq :
      (B.weight y.1*C.weight y.2) *
      (∑ i, prodFun B C i y * prodFun B C i x) =
      (B.weight y.1*(∑ i, B.basis i y.1*B.basis i x.1)) *
      (C.weight y.2*(∑ j, C.basis j y.2*C.basis j x.2)) := by
    simp only [Fintype.sum_prod_type, prodFun]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, local_reproducing, local_reproducing]
  by_cases h1 : x.1=y.1 <;> by_cases h2 : x.2=y.2 <;>
    simp [h1,h2,Prod.ext_iff]

def prod (B : WeightedONBasis Ω I) (C : WeightedONBasis Ω' I') :
    WeightedONBasis (Ω × Ω') (I × I') where
  weight x := B.weight x.1 * C.weight x.2
  weight_nonneg x := mul_nonneg (B.weight_nonneg _) (C.weight_nonneg _)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, C.sum_weight, mul_one]
    exact B.sum_weight
  basis := prodFun B C
  orthonormal_same i := by simpa using prod_orthonormal B C i i
  orthonormal_ne i j h := by simpa [h] using prod_orthonormal B C i j
  reconstruction f x := by
    calc
      f x = ∑ y, f y * (if x=y then 1 else 0) := by simp [eq_comm]
      _ = ∑ y, f y * ((B.weight y.1*C.weight y.2) *
          (∑ i, prodFun B C i y * prodFun B C i x)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [prod_kernel]
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y _
        ring
  vacuum := (B.vacuum,C.vacuum)
  vacuum_eq_one x := by simp [prodFun,B.vacuum_eq_one,C.vacuum_eq_one]

end BinaryProduct

end
end SRHT.ProductBasis
