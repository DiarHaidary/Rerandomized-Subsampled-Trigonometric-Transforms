import SRHT.Model
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The explicit alternating-support vectors in Appendix A.  The ambient
index is a product of two Walsh groups, exactly the tensor convention in A.1. -/

open scoped BigOperators Matrix

namespace SRHT.Alignment
noncomputable section
open SparseFock

abbrev Site (k : ℕ) := WalshIndex k × WalshIndex k
abbrev Signs (k : ℕ) := Site k → ZMod 2

def tensorWalsh (k : ℕ) : Matrix (Site k) (Site k) ℝ :=
  Matrix.kronecker (walshMatrix k) (walshMatrix k)

def flat (k : ℕ) : ℝ := (Real.sqrt (2 ^ k : ℝ))⁻¹

def horizontal (k : ℕ) : Site k → ℝ := fun i => if i.2 = 0 then flat k else 0
def vertical (k : ℕ) : Site k → ℝ := fun i => if i.1 = 0 then flat k else 0

def support {I : Type*} [Fintype I] (v : I → ℝ) : Finset I :=
  Finset.univ.filter (fun i => v i ≠ 0)

@[simp] theorem mem_support {I : Type*} [Fintype I] (v : I → ℝ) (i : I) :
    i ∈ support v ↔ v i ≠ 0 := by
  classical
  simp [support]

theorem flat_pos (k : ℕ) : 0 < flat k := by unfold flat; positivity
theorem flat_sq (k : ℕ) : flat k ^ 2 * (2 ^ k : ℝ) = 1 := by
  have hn : (0 : ℝ) < 2 ^ k := by positivity
  have hs := Real.sq_sqrt hn.le
  unfold flat
  rw [inv_pow, hs, inv_mul_cancel₀ (ne_of_gt hn)]

theorem horizontal_support_card (k : ℕ) : (support (horizontal k)).card = 2 ^ k := by
  classical
  have he : support (horizontal k) = Finset.univ ×ˢ ({0} : Finset (WalshIndex k)) := by
    ext ⟨a, b⟩
    simp [support, horizontal, ne_of_gt (flat_pos k), ne_of_lt (flat_pos k), eq_comm]
  rw [he]
  simp

theorem vertical_support_card (k : ℕ) : (support (vertical k)).card = 2 ^ k := by
  classical
  have he : support (vertical k) = ({0} : Finset (WalshIndex k)) ×ˢ Finset.univ := by
    ext ⟨a, b⟩
    simp [support, vertical, ne_of_gt (flat_pos k), ne_of_lt (flat_pos k), eq_comm]
  rw [he]
  simp

theorem horizontal_unit (k : ℕ) : (∑ i, horizontal k i ^ 2) = 1 := by
  classical
  simp only [Fintype.sum_prod_type, horizontal]
  simpa [mul_comm] using (flat_sq k)

theorem walsh_sum (k : ℕ) (a : WalshIndex k) :
    (∑ b, walshMatrix k a b) = if a = 0 then flat k * (2 ^ k : ℝ) else 0 := by
  simp only [walshMatrix_apply, ← Finset.mul_sum, walshChar_sum, walshIndex_card]
  split_ifs <;> simp [flat]

theorem tensor_horizontal (k : ℕ) :
    (tensorWalsh k).mulVec (horizontal k) = vertical k := by
  classical
  funext ⟨a, b⟩
  simp only [Matrix.mulVec, dotProduct, tensorWalsh, Matrix.kronecker_apply,
    Fintype.sum_prod_type, horizontal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ x, walshMatrix k a x * walshMatrix k b 0 * flat k) =
    if a = 0 then flat k else 0
  rw [← Finset.sum_mul, ← Finset.sum_mul, walsh_sum]
  rw [walshMatrix_apply]
  simp only [walshChar_zero_right, mul_one]
  split_ifs with hi
  · dsimp [flat] at *
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 ^ k by positivity)
    have hn : Real.sqrt (2 ^ k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp
    nlinarith
  · simp

theorem tensor_vertical (k : ℕ) :
    (tensorWalsh k).mulVec (vertical k) = horizontal k := by
  classical
  funext ⟨a, b⟩
  simp only [Matrix.mulVec, dotProduct, tensorWalsh, Matrix.kronecker_apply,
    Fintype.sum_prod_type, vertical]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ x, walshMatrix k a 0 * walshMatrix k b x * flat k) =
    if b = 0 then flat k else 0
  rw [← Finset.sum_mul, ← Finset.mul_sum, walsh_sum, walshMatrix_apply]
  simp only [walshChar_zero_right, mul_one]
  split_ifs with hi
  · change flat k * (flat k * (2 ^ k : ℝ)) * flat k = flat k
    calc
      _ = (flat k ^ 2 * (2 ^ k : ℝ)) * flat k := by ring
      _ = _ := by rw [flat_sq, one_mul]
  · simp

def bitLaw (k : ℕ) : FiniteLaw (Signs k) :=
  FiniteLaw.independentProduct (fun _ => uniformLaw (ZMod 2))

def signAction {k : ℕ} (x : Signs k) (v : Site k → ℝ) : Site k → ℝ :=
  fun i => bitSign (x i) * v i

def step {k : ℕ} (x : Signs k) (v : Site k → ℝ) : Site k → ℝ :=
  (tensorWalsh k).mulVec (signAction x v)

theorem signAction_eq_of_zero_on_support {k : ℕ} (x : Signs k) (v : Site k → ℝ)
    (hx : ∀ i ∈ support v, x i = 0) : signAction x v = v := by
  classical
  funext i
  by_cases hi : v i = 0
  · simp [signAction, hi]
  · simp [signAction, hx i ((mem_support v i).2 hi)]

/-- An exact cylinder probability, allowing any prescribed signs on the set. -/
theorem pattern_probability (k : ℕ) (K : Finset (Site k)) (b : Site k → ZMod 2) :
    (bitLaw k).prob {x | ∀ i ∈ K, x i = b i} = (1 / 2 : ℝ) ^ K.card := by
  classical
  have he : {x : Signs k | ∀ i ∈ K, x i = b i} =
      FiniteLaw.cylinder (fun i => if i ∈ K then {b i} else Set.univ) := by
    ext x
    simp only [FiniteLaw.cylinder, Set.mem_setOf_eq]
    constructor
    · intro hx i
      by_cases hi : i ∈ K <;> simp [hi, hx]
    · intro hx i hi
      simpa [hi] using hx i
  rw [he, bitLaw, FiniteLaw.prob_independentProduct_cylinder]
  simp only [apply_ite, FiniteLaw.prob_singleton, uniformLaw_weight,
    ZMod.card, FiniteLaw.prob_univ]
  simp

/-- The deterministic state after each successful all-plus alignment. -/
def alternating (k : ℕ) : ℕ → Site k → ℝ
  | 0 => horizontal k
  | t+1 => (tensorWalsh k).mulVec (alternating k t)

theorem alternating_cases (k t : ℕ) :
    alternating k t = horizontal k ∨ alternating k t = vertical k := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rcases ih with h | h
    · exact Or.inr (by rw [alternating, h, tensor_horizontal])
    · exact Or.inl (by rw [alternating, h, tensor_vertical])

theorem alternating_support_card (k t : ℕ) :
    (support (alternating k t)).card = 2 ^ k := by
  rcases alternating_cases k t with h | h
  · rw [h, horizontal_support_card]
  · rw [h, vertical_support_card]

/-- A tuple of successive independent diagonal sign layers. -/
@[reducible] def Layers (k : ℕ) : ℕ → Type
  | 0 => Unit
  | t+1 => Layers k t × Signs k

@[reducible] instance layersFintype (k : ℕ) : (t : ℕ) → Fintype (Layers k t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t+1 => @instFintypeProd _ _ (layersFintype k t) inferInstance

def layersLaw (k : ℕ) : (t : ℕ) → FiniteLaw (Layers k t)
  | 0 => uniformLaw Unit
  | t+1 => (layersLaw k t).product (bitLaw k)

/-- Literal successive applications of H D_j to the fixed unit input. -/
def evolve (k : ℕ) : (t : ℕ) → Layers k t → Site k → ℝ
  | 0, _ => horizontal k
  | t+1, x => step x.2 (evolve k t x.1)

def aligned (k : ℕ) : (t : ℕ) → Set (Layers k t)
  | 0 => Set.univ
  | t+1 => {x | x.1 ∈ aligned k t ∧ ∀ i ∈ support (alternating k t), x.2 i = 0}

theorem evolve_of_aligned (k t : ℕ) (x : Layers k t) (hx : x ∈ aligned k t) :
    evolve k t x = alternating k t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step x.2 (evolve k t x.1) = _
    rw [ih x.1 hx.1, step, signAction_eq_of_zero_on_support x.2 _ hx.2]
    rfl

theorem aligned_probability (k t : ℕ) :
    (layersLaw k t).prob (aligned k t) = (1 / 2 : ℝ) ^ (t * 2 ^ k) := by
  classical
  induction t with
  | zero =>
    rw [Nat.zero_mul]
    change (uniformLaw Unit).prob Set.univ = (1/2:ℝ)^0
    rw [FiniteLaw.prob_univ, pow_zero]
  | succ t ih =>
    rw [layersLaw, FiniteLaw.product_prob_eq_iterated]
    have he (x : Layers k t) :
        (bitLaw k).prob {b | (x, b) ∈ aligned k (t+1)} =
          FiniteLaw.indicator (aligned k t) x * (1/2:ℝ)^(2^k) := by
      by_cases hx : x ∈ aligned k t
      · simp only [aligned, Set.mem_setOf_eq, hx, true_and]
        rw [pattern_probability, alternating_support_card]
        simp [FiniteLaw.indicator, hx]
      · have hempty : {b : Signs k | (x, b) ∈ aligned k (t+1)} = ∅ := by
          ext b
          simp [aligned, hx]
        rw [hempty, FiniteLaw.prob_empty]
        simp [FiniteLaw.indicator, hx]
    simp_rw [he]
    calc
      _ = (1/2:ℝ)^(2^k) * (layersLaw k t).prob (aligned k t) := by
        rw [FiniteLaw.prob, ← FiniteLaw.expect_smul]
        apply FiniteLaw.expect_congr
        intro x
        ring
      _ = _ := by rw [ih, Nat.succ_mul, pow_add]; ring

/-- The literal vector obtained by retaining and scaling the selected coordinates. -/
def sampleVector {k : ℕ} (v : Site k → ℝ) (T : Finset (Site k)) :
    EuclideanSpace ℝ T :=
  WithLp.toLp 2 (fun i => Real.sqrt ((Fintype.card (Site k) : ℝ) / T.card) * v i.val)

def sampleEnergy {k : ℕ} (v : Site k → ℝ) (T : Finset (Site k)) : ℝ :=
  ‖sampleVector v T‖ ^ 2

theorem sampleEnergy_eq_zero_of_disjoint {k : ℕ} (v : Site k → ℝ)
    (T : Finset (Site k)) (h : Disjoint T (support v)) : sampleEnergy v T = 0 := by
  have he : sampleVector v T = 0 := by
    ext i
    have hv : v i.val = 0 := by
      by_contra hc
      exact Finset.disjoint_left.mp h i.property ((mem_support v i.val).2 hc)
    simp [sampleVector, hv]
  simp [sampleEnergy, he]

theorem horizontal_norm (k : ℕ) : ‖WithLp.toLp 2 (horizontal k)‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  simpa using horizontal_unit k

end
end SRHT.Alignment
