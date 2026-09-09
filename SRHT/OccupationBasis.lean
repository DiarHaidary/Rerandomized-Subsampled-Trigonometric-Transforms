import SRHT.BinaryBasis
import SRHT.Model
import SRHT.HardCore

/-! The actual finite product probability basis and its hard-core coordinate actions. -/

open scoped BigOperators Matrix
open SparseFock SparseFock.FiniteL2

namespace SRHT.OccupationBasis

noncomputable section

variable {G Ω I : Type*} [Fintype G] [DecidableEq G]
  [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]

/-- Occupied finite subsets are exactly Boolean coordinate occupations. -/
def occupationEquiv : Finset G ≃ (G → Bool) where
  toFun S i := decide (i ∈ S)
  invFun x := Finset.univ.filter (fun i => x i = true)
  left_inv S := by ext i; simp
  right_inv x := by funext i; simp

@[simp] theorem occupationEquiv_apply (S : Finset G) (i : G) :
    occupationEquiv S i = decide (i ∈ S) := rfl

@[simp] theorem occupationEquiv_empty : occupationEquiv (∅ : Finset G) = fun _ => false := by
  funext i
  simp

/-- Multiplication by one random coordinate acts locally in a product basis. -/
theorem pi_mulOp_coordinate (B : G → WeightedONBasis Ω I) (j : G) (f : Ω → ℝ)
    (p q : G → I) :
    (ProductBasis.pi B).mulOp (fun x => f (x j)) p q =
      (B j).mulOp f (p j) (q j) *
        ∏ s ∈ Finset.univ.erase j, if p s = q s then 1 else 0 := by
  classical
  let g := fun s z => (B s).basis (p s) z * (B s).basis (q s) z *
    (if s = j then f z else 1)
  have hg (x : G → Ω) :
      (∏ s, g s (x s)) = ProductBasis.piBasis B p x *
        (f (x j) * ProductBasis.piBasis B q x) := by
    dsimp [g]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true, ProductBasis.piBasis]
    ring
  have he : (ProductBasis.pi B).mulOp (fun x => f (x j)) p q =
      ∏ s, (ProductBasis.lawOfBasis (B s)).expect (g s) := by
    have h := FiniteLaw.expect_independentProduct_factorizes
      (fun s => ProductBasis.lawOfBasis (B s)) g
    rw [show (fun x => ∏ s, g s (x s)) =
      (fun x => ProductBasis.piBasis B p x * (f (x j) * ProductBasis.piBasis B q x))
      from funext hg] at h
    simpa only [WeightedONBasis.mulOp, WeightedONBasis.coeff, ProductBasis.pi,
      ProductBasis.piLaw, FiniteLaw.expect, mul_assoc] using h
  have hlocal (s : G) : (ProductBasis.lawOfBasis (B s)).expect (g s) =
      if s = j then (B j).mulOp f (p j) (q j) else
        if p s = q s then 1 else 0 := by
    by_cases hs : s=j
    · subst s
      simp only [g, if_true, ProductBasis.lawOfBasis, FiniteLaw.expect,
        WeightedONBasis.mulOp, WeightedONBasis.coeff]
      apply Finset.sum_congr rfl
      intro z _
      ring
    · rw [if_neg hs]
      simpa [g, hs, ProductBasis.lawOfBasis, FiniteLaw.expect, WeightedONBasis.coeff,
        mul_assoc] using (B s).coeff_basis (p s) (q s)
  rw [he]
  simp_rw [hlocal]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  rw [if_neg (Finset.mem_erase.mp hs).1]

/-- Product basis reindexed by the actual finite occupation subsets. -/
def basis (B : G → WeightedONBasis Ω Bool) : WeightedONBasis (G → Ω) (Finset G) :=
  ProductBasis.reindex (ProductBasis.pi B) occupationEquiv

@[simp] theorem basis_weight (B : G → WeightedONBasis Ω Bool) (x : G → Ω) :
    (basis B).weight x = ∏ s, (B s).weight (x s) := rfl

theorem basis_mulOp_coordinate (B : G → WeightedONBasis Ω Bool) (j : G) (f : Ω → ℝ)
    (S T : Finset G) :
    (basis B).mulOp (fun x => f (x j)) S T =
      (B j).mulOp f (decide (j∈S)) (decide (j∈T)) *
        ∏ s ∈ Finset.univ.erase j, if (s∈S ↔ s∈T) then 1 else 0 := by
  have h := pi_mulOp_coordinate B j f (occupationEquiv S) (occupationEquiv T)
  simpa only [basis, ProductBasis.reindex, WeightedONBasis.mulOp, WeightedONBasis.coeff,
    occupationEquiv_apply, decide_eq_decide] using h

theorem outside_product (j : G) (S T : Finset G) :
    (∏ s ∈ Finset.univ.erase j, if (s∈S ↔ s∈T) then (1:ℝ) else 0) =
      if S.erase j = T.erase j then 1 else 0 := by
  rw [Finset.prod_boole]
  have he : (∀ s ∈ Finset.univ.erase j, s∈S ↔ s∈T) ↔ S.erase j = T.erase j := by
    constructor
    · intro h
      ext s
      by_cases hs : s=j
      · subst s; simp
      · simpa [Finset.mem_erase, hs] using h s (by simp [hs])
    · intro h s hs
      have hn := (Finset.mem_erase.mp hs).1
      have hm := congrArg (fun A : Finset G => s∈A) h
      simpa [Finset.mem_erase, hn] using hm
  simp only [he]

/-- The local two-state Jacobi matrix becomes literal subset creation,
annihilation, and occupancy after product reindexing. -/
theorem coordinate_jacobi (B : G → WeightedONBasis Ω Bool) (j : G) (f : Ω → ℝ)
    (σ τ : ℝ)
    (hlocal : ∀ b c, (B j).mulOp f b c =
      if b=c then (if b then τ else 0) else σ) :
    (basis B).mulOp (fun x => f (x j)) =
      σ • (HardCore.create j + HardCore.annihilate j) + τ • HardCore.number j := by
  ext S T
  rw [basis_mulOp_coordinate, outside_product, hlocal]
  by_cases hS : j∈S <;> by_cases hT : j∈T
  · have he : S.erase j = T.erase j ↔ S=T := by
      constructor
      · intro h
        have h' := congrArg (insert j) h
        simpa [Finset.insert_erase hS, Finset.insert_erase hT] using h'
      · rintro rfl; rfl
    have hne : T ≠ S.erase j := by intro h; rw [h] at hT; simp at hT
    simp [hS,hT,he,hne,HardCore.create,HardCore.annihilate,HardCore.number_apply]
  · have he : S.erase j = T.erase j ↔ T=S.erase j := by simp [Finset.erase_eq_of_notMem hT,eq_comm]
    have hne : S≠T := by intro h; exact hT (h ▸ hS)
    simp only [he]
    simp [hS,hT,hne,HardCore.create,HardCore.annihilate,HardCore.number_apply]
  · have he : S.erase j = T.erase j ↔ T=insert j S := by
      rw [Finset.erase_eq_of_notMem hS]
      constructor
      · intro h
        rw [h,Finset.insert_erase hT]
      · rintro rfl
        simp [hS]
    have hne : S≠T := by intro h; exact hS (h ▸ hT)
    simp only [he]
    simp [hS,hT,hne,HardCore.create,HardCore.annihilate,HardCore.number_apply]
  · have hne : T≠insert j S := by intro h; rw [h] at hT; simp at hT
    simp [hS,hT,hne,HardCore.create,HardCore.annihilate,HardCore.number_apply]

def signs : WeightedONBasis (G → ZMod 2) (Finset G) := basis (fun _ => BinaryBasis.signs)

def bernoulli (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    WeightedONBasis (G → ZMod 2) (Finset G) :=
  basis (fun _ => BinaryBasis.bernoulli p hp hp1)

@[simp] theorem signs_vacuum : (signs (G:=G)).vacuum = ∅ := by
  simp [signs,basis,ProductBasis.reindex,ProductBasis.pi,BinaryBasis.signs,occupationEquiv]

@[simp] theorem bernoulli_vacuum (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (bernoulli (G:=G) p hp hp1).vacuum = ∅ := by
  simp [bernoulli,basis,ProductBasis.reindex,ProductBasis.pi,BinaryBasis.bernoulli,occupationEquiv]

theorem local_signs_jacobi (b c : Bool) :
    BinaryBasis.signs.mulOp bitSign b c = if b=c then 0 else 1 := by
  cases b <;> cases c <;>
    norm_num [WeightedONBasis.mulOp,WeightedONBasis.coeff,BinaryBasis.signs,
      BinaryBasis.signBasisFun,bitSign]

/-- Multiplication by an actual sign is exactly one hard-core flip. -/
theorem signs_mulOp (j : G) :
    (signs (G:=G)).mulOp (fun x => bitSign (x j)) =
      HardCore.create j + HardCore.annihilate j := by
  have h := coordinate_jacobi (fun _ : G => BinaryBasis.signs) j bitSign 1 0
    (fun b c => by simpa using local_signs_jacobi b c)
  simpa [signs] using h

/-- The actual centered Bernoulli selector has its exact Jacobi coefficients. -/
theorem bernoulli_mulOp (p : ℝ) (hp : 0<p) (hp1 : p<1) (j : G) :
    (bernoulli (G:=G) p hp hp1).mulOp (fun x => BinaryBasis.bitValue (x j)/p-1) =
      Real.sqrt ((1-p)/p) • (HardCore.create j + HardCore.annihilate j) +
      ((1-2*p)/p) • HardCore.number j := by
  have h := coordinate_jacobi (fun _ : G => BinaryBasis.bernoulli p hp hp1) j
    (fun z => BinaryBasis.bitValue z/p-1) (Real.sqrt ((1-p)/p)) ((1-2*p)/p)
    (fun b c => by simpa only [BinaryBasis.amplitude_eq hp hp1] using
      BinaryBasis.bernoulli_jacobi hp hp1 b c)
  exact h

@[simp] theorem signs_weight (x : G → ZMod 2) :
    (signs (G:=G)).weight x = (1/2:ℝ) ^ Fintype.card G := by
  simp [signs,basis_weight,BinaryBasis.signs]

theorem law_ext {α : Type*} [Fintype α] (μ ν : FiniteLaw α)
    (h : μ.weight = ν.weight) : μ=ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem signs_law {k : ℕ} :
    ProductBasis.lawOfBasis (signs (G:=WalshIndex k)) = signLaw k := by
  apply law_ext
  funext x
  simp [ProductBasis.lawOfBasis]

theorem bernoulli_law (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    ProductBasis.lawOfBasis (bernoulli (G:=G) p hp hp1) =
      FiniteLaw.independentProduct (fun _ : G => BinaryBasis.law p hp.le hp1.le) := by
  apply law_ext
  funext x
  rfl

end

end SRHT.OccupationBasis
