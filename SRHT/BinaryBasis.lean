import SRHT.ProductBasis
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace SRHT.BinaryBasis
open SparseFock SparseFock.FiniteL2
open scoped BigOperators
noncomputable section

def bitValue (z : ZMod 2) : ℝ := if z = 0 then 0 else 1
def mass (p : ℝ) (z : ZMod 2) : ℝ := if z = 0 then 1-p else p
def deviation (p : ℝ) : ℝ := Real.sqrt (p*(1-p))
def basisFun (p : ℝ) (b : Bool) (z : ZMod 2) : ℝ :=
  if b then (bitValue z-p)/deviation p else 1

theorem bit_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  exact (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z

@[simp] theorem sum_bits (f : ZMod 2 → ℝ) : (∑ z, f z) = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0,1} from by decide]
  simp

theorem deviation_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < deviation p := Real.sqrt_pos.mpr (mul_pos hp (sub_pos.mpr hp1))

theorem deviation_sq {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    deviation p ^ 2 = p*(1-p) :=
  Real.sq_sqrt (mul_nonneg hp (sub_nonneg.mpr hp1))

theorem mass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (z : ZMod 2) :
    0 ≤ mass p z := by
  unfold mass
  split <;> linarith

@[simp] theorem mass_sum (p : ℝ) : (∑ z, mass p z) = 1 := by
  simp [mass]

def law (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (ZMod 2) :=
  ⟨mass p, mass_nonneg hp hp1, mass_sum p⟩

theorem basis_orthonormal {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b c : Bool) :
    (∑ z, mass p z * basisFun p b z * basisFun p c z) =
      if b = c then 1 else 0 := by
  have hs := deviation_sq hp.le hp1.le
  have hs0 := (deviation_pos hp hp1).ne'
  cases b <;> cases c <;> simp [basisFun, mass, bitValue]
  all_goals field_simp
  all_goals nlinarith

theorem basis_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (y x : ZMod 2) :
    mass p y * (∑ b, basisFun p b y * basisFun p b x) =
      if x = y then 1 else 0 := by
  have hs := deviation_sq hp.le hp1.le
  have hs0 := (deviation_pos hp hp1).ne'
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl
  all_goals simp [basisFun, mass, bitValue]
  all_goals try right
  all_goals field_simp
  all_goals nlinarith

theorem basis_reconstruction {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : ZMod 2 → ℝ) (x : ZMod 2) :
    f x = ∑ b, (∑ y, mass p y * basisFun p b y * f y) * basisFun p b x := by
  calc
    f x = ∑ y, f y * (if x = y then 1 else 0) := by simp [eq_comm]
    _ = ∑ y, f y * (mass p y * ∑ b, basisFun p b y * basisFun p b x) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [basis_kernel hp hp1]
    _ = ∑ b, (∑ y, mass p y * basisFun p b y * f y) * basisFun p b x := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring

def bernoulli (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    WeightedONBasis (ZMod 2) Bool where
  weight := mass p
  weight_nonneg := mass_nonneg hp.le hp1.le
  sum_weight := mass_sum p
  basis := basisFun p
  orthonormal_same b := by simpa using basis_orthonormal hp hp1 b b
  orthonormal_ne b c h := by simpa [h] using basis_orthonormal hp hp1 b c
  reconstruction := basis_reconstruction hp hp1
  vacuum := false
  vacuum_eq_one z := by simp [basisFun]

def signBasisFun (b : Bool) (z : ZMod 2) : ℝ :=
  if b then (if z = 0 then 1 else -1) else 1

def signs : WeightedONBasis (ZMod 2) Bool where
  weight := fun _ => 1/2
  weight_nonneg _ := by norm_num
  sum_weight := by simp
  basis := signBasisFun
  orthonormal_same b := by cases b <;> norm_num [signBasisFun]
  orthonormal_ne b c h := by cases b <;> cases c <;> norm_num [signBasisFun] at *
  reconstruction f x := by
    rcases bit_cases x with rfl | rfl <;> simp [signBasisFun, Fintype.sum_bool] <;> ring
  vacuum := false
  vacuum_eq_one z := by simp [signBasisFun]

theorem bernoulli_jacobi {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b c : Bool) :
    (bernoulli p hp hp1).mulOp (fun z => bitValue z/p-1) b c =
      if b = c then (if b then (1-2*p)/p else 0) else deviation p/p := by
  have hs := deviation_sq hp.le hp1.le
  have hs0 := (deviation_pos hp hp1).ne'
  have hp0 := hp.ne'
  cases b <;> cases c <;>
    simp [WeightedONBasis.mulOp, WeightedONBasis.coeff, bernoulli,
      basisFun, mass, bitValue]
  all_goals field_simp
  all_goals nlinarith

theorem amplitude_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    deviation p / p = Real.sqrt ((1-p)/p) := by
  have hs := deviation_sq hp.le hp1.le
  have ha : 0 ≤ deviation p / p := div_nonneg (deviation_pos hp hp1).le hp.le
  have hb : 0 ≤ (1-p)/p := div_nonneg (sub_nonneg.mpr hp1.le) hp.le
  have hsq : (deviation p/p)^2 = (1-p)/p := by
    field_simp
    nlinarith
  nlinarith [Real.sq_sqrt hb, Real.sqrt_nonneg ((1-p)/p)]

end
end SRHT.BinaryBasis

