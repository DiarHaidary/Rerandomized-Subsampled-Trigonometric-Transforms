import SparseFockFormal.FiniteProbability
import SparseFockFormal.SparseStackDistribution
import SparseFockFormal.TernaryJacobi
import SparseFockFormal.PaperParameters
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# The exact sparse-selector to iid-coordinate coupling

This file formalizes the finite coupling in lines 215--247 of the v1.4 paper.
The iid vector has independent coordinates in `{-1,0,1}`.  Conditional on a
nonzero vector, a uniformly random nonzero coordinate and its sign are
retained; at the zero vector, an independent uniform signed basis selector is
generated.  All laws and kernels are explicit finite real weights.
-/

open scoped BigOperators InnerProductSpace

namespace SparseFock

namespace SparseIIDCoupling

open ParsevalFrame SparseStackModel SparseStackDistribution

noncomputable section

/-- The unscaled value of one iid coordinate `Y_a`. -/
def yValue : EtaOutcome → ℝ
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- The nonzero outcome associated with a Rademacher sign. -/
def outcomeOfSign : Sign → EtaOutcome
  | .plus => .pos
  | .minus => .neg

@[simp] theorem yValue_outcomeOfSign (e : Sign) :
    yValue (outcomeOfSign e) = e.val := by
  cases e <;> rfl

/-- Negation of a ternary atom. -/
def negateOutcome : EtaOutcome → EtaOutcome
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

@[simp] theorem negateOutcome_involutive (z : EtaOutcome) :
    negateOutcome (negateOutcome z) = z := by cases z <;> rfl

@[simp] theorem yValue_negateOutcome (z : EtaOutcome) :
    yValue (negateOutcome z) = -yValue z := by cases z <;> norm_num [yValue, negateOutcome]

/-- Flip a Rademacher sign. -/
def flipSign : Sign → Sign
  | .plus => .minus
  | .minus => .plus

@[simp] theorem flipSign_involutive (e : Sign) : flipSign (flipSign e) = e := by
  cases e <;> rfl

@[simp] theorem outcomeOfSign_flipSign (e : Sign) :
    outcomeOfSign (flipSign e) = negateOutcome (outcomeOfSign e) := by
  cases e <;> rfl

/-- One iid ternary coordinate with masses `1/(2b), 1-1/b, 1/(2b)`. -/
def coordinateLaw (b : ℕ) (hb : 0 < b) : FiniteLaw EtaOutcome where
  weight := TernaryJacobi.mass b
  weight_nonneg := TernaryJacobi.mass_nonneg hb
  sum_weight := TernaryJacobi.sum_mass hb

@[simp] theorem coordinateLaw_weight (b : ℕ) (hb : 0 < b) (z : EtaOutcome) :
    (coordinateLaw b hb).weight z = TernaryJacobi.mass b z := rfl

/-- An iid vector `Y ∈ {-1,0,1}^b`. -/
abbrev YVector (b : ℕ) := Fin b → EtaOutcome

/-- The independent-coordinate law of `Y`. -/
def yVectorLaw (b : ℕ) (hb : 0 < b) : FiniteLaw (YVector b) :=
  FiniteLaw.independentProduct (fun _ : Fin b => coordinateLaw b hb)

@[simp] theorem yVectorLaw_weight {b : ℕ} (hb : 0 < b) (y : YVector b) :
    (yVectorLaw b hb).weight y = ∏ a, TernaryJacobi.mass b (y a) := rfl

/-- The all-zero iid vector. -/
def zeroY (b : ℕ) : YVector b := fun _ => .zero

/-- The finite nonzero support. -/
def support {b : ℕ} (y : YVector b) : Finset (Fin b) :=
  Finset.univ.filter fun a => y a ≠ .zero

@[simp] theorem mem_support {b : ℕ} (y : YVector b) (a : Fin b) :
    a ∈ support y ↔ y a ≠ .zero := by simp [support]

/-- Number of nonzero coordinates. -/
def supportSize {b : ℕ} (y : YVector b) : ℕ := (support y).card

theorem supportSize_eq_zero_iff {b : ℕ} (y : YVector b) :
    supportSize y = 0 ↔ y = zeroY b := by
  constructor
  · intro h
    apply funext
    intro a
    have hempty : support y = ∅ := Finset.card_eq_zero.mp h
    have hnot : a ∉ support y := by simp [hempty]
    have : ¬y a ≠ .zero := by simpa [mem_support] using hnot
    simpa [zeroY] using not_ne_iff.mp this
  · rintro rfl
    simp [supportSize, support, zeroY]

/-- The zero-vector probability `p₀=(1-1/b)^b`. -/
def p0 (b : ℕ) : ℝ := (1 - 1 / (b : ℝ)) ^ b

theorem zeroY_weight {b : ℕ} (hb : 0 < b) :
    (yVectorLaw b hb).weight (zeroY b) = p0 b := by
  simp [yVectorLaw_weight, zeroY, TernaryJacobi.mass, p0]

theorem p0_nonneg {b : ℕ} (hb : 0 < b) : 0 ≤ p0 b := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase : (0 : ℝ) ≤ 1 - 1 / (b : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity : (0 : ℝ) < b)).2 hbR
  exact pow_nonneg hbase _

theorem p0_lt_one {b : ℕ} (hb : 0 < b) : p0 b < 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (b : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hbR).2 (by exact_mod_cast hb)
  have hbase1 : (1 : ℝ) - 1 / (b : ℝ) < 1 := by
    have : (0 : ℝ) < 1 / (b : ℝ) := one_div_pos.mpr hbR
    linarith
  exact pow_lt_one₀ hbase0 hbase1 (Nat.ne_of_gt hb)

/-- The elementary exponential estimate omitted in the prose proof. -/
theorem p0_le_exp_neg_one {b : ℕ} (hb : 0 < b) :
    p0 b ≤ Real.exp (-1) := by
  have h1b : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  simpa [p0] using
    (Real.one_sub_div_pow_le_exp_neg (n := b) (t := (1 : ℝ)) h1b)

/-- The exact coupling rescaling `c_b=(1-p₀)⁻¹`. -/
def cB (b : ℕ) : ℝ := (1 - p0 b)⁻¹

theorem one_sub_p0_pos {b : ℕ} (hb : 0 < b) : 0 < 1 - p0 b := by
  linarith [p0_lt_one hb]

theorem one_le_cB {b : ℕ} (hb : 0 < b) : 1 ≤ cB b := by
  rw [cB, one_le_inv₀ (one_sub_p0_pos hb)]
  linarith [p0_nonneg hb]

theorem cB_le_cStar {b : ℕ} (hb : 0 < b) : cB b ≤ PaperParameters.cStar := by
  rw [cB, PaperParameters.cStar]
  apply inv_anti₀ PaperParameters.expGap_pos
  linarith [p0_le_exp_neg_one hb]

/-- Whether selector `x` is one of the signed nonzero coordinates of `y`. -/
def selectorMatches {b : ℕ} (y : YVector b) (x : SignedHash b) : Prop :=
  y x.1 = outcomeOfSign x.2

/-- Weight of the support-selection kernel `X | Y=y`. -/
def kernelWeight {b : ℕ} (hb : 0 < b) (y : YVector b) (x : SignedHash b) : ℝ :=
  by
    classical
    exact if supportSize y = 0 then (selectorLaw b hb).weight x
      else if selectorMatches y x then 1 / (supportSize y : ℝ) else 0

theorem kernelWeight_nonneg {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) : 0 ≤ kernelWeight hb y x := by
  classical
  by_cases hzero : supportSize y = 0
  · simp [kernelWeight, hzero, (selectorLaw b hb).weight_nonneg x]
  · by_cases hmatch : selectorMatches y x
    · simp [kernelWeight, hzero, hmatch]
    · simp [kernelWeight, hzero, hmatch]

theorem sum_kernelWeight {b : ℕ} (hb : 0 < b) (y : YVector b) :
    ∑ x, kernelWeight hb y x = 1 := by
  classical
  by_cases hzero : supportSize y = 0
  · simp [kernelWeight, hzero, (selectorLaw b hb).sum_weight]
  · rw [Fintype.sum_prod_type]
    simp only [kernelWeight, hzero, ↓reduceIte]
    have sign_univ : (Finset.univ : Finset Sign) = {.plus, .minus} := by
      ext e
      cases e <;> simp
    have hsign (a : Fin b) :
        (∑ e : Sign, if selectorMatches y (a, e)
          then 1 / (supportSize y : ℝ) else 0) =
          if a ∈ support y then 1 / (supportSize y : ℝ) else 0 := by
      cases hya : y a <;>
        simp [sign_univ, selectorMatches, outcomeOfSign, support, hya]
    simp_rw [hsign]
    have hreindex :
        (∑ a, if a ∈ support y then 1 / (supportSize y : ℝ) else 0) =
          ∑ a ∈ support y, 1 / (supportSize y : ℝ) := by
      simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
        (Finset.sum_filter (s := Finset.univ)
          (p := fun a => a ∈ support y)
          (f := fun _ => 1 / (supportSize y : ℝ))).symm
    rw [hreindex]
    have hcard : ((support y).card : ℝ) ≠ 0 := by
      exact_mod_cast (show (support y).card ≠ 0 by simpa [supportSize] using hzero)
    simp only [Finset.sum_const, nsmul_eq_mul, supportSize]
    field_simp

/-- The normalized conditional selector law. -/
def selectionKernel {b : ℕ} (hb : 0 < b) (y : YVector b) :
    FiniteLaw (SignedHash b) where
  weight := kernelWeight hb y
  weight_nonneg := kernelWeight_nonneg hb y
  sum_weight := sum_kernelWeight hb y

@[simp] theorem selectionKernel_weight {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) :
    (selectionKernel hb y).weight x = kernelWeight hb y x := rfl

/-- One-column joint law generated by first drawing `Y`, then drawing `X|Y`. -/
def jointColumnLaw {b : ℕ} (hb : 0 < b) :
    FiniteLaw (YVector b × SignedHash b) where
  weight z := (yVectorLaw b hb).weight z.1 * kernelWeight hb z.1 z.2
  weight_nonneg z := mul_nonneg
    ((yVectorLaw b hb).weight_nonneg z.1) (kernelWeight_nonneg hb z.1 z.2)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, sum_kernelWeight hb]
    simpa using (yVectorLaw b hb).sum_weight

@[simp] theorem jointColumnLaw_weight {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) :
    (jointColumnLaw hb).weight (y, x) =
      (yVectorLaw b hb).weight y * kernelWeight hb y x := rfl

/-! ## Symmetry and the selector marginal -/

theorem mass_negateOutcome (b : ℕ) (z : EtaOutcome) :
    TernaryJacobi.mass b (negateOutcome z) = TernaryJacobi.mass b z := by
  cases z <;> rfl

/-- Flip every nonzero sign in an iid vector. -/
def negateY {b : ℕ} (y : YVector b) : YVector b :=
  fun a => negateOutcome (y a)

@[simp] theorem negateY_involutive {b : ℕ} (y : YVector b) :
    negateY (negateY y) = y := by
  funext a
  simp [negateY]

def negateYEquiv (b : ℕ) : YVector b ≃ YVector b where
  toFun := negateY
  invFun := negateY
  left_inv := negateY_involutive
  right_inv := negateY_involutive

theorem yVectorLaw_weight_negateY {b : ℕ} (hb : 0 < b) (y : YVector b) :
    (yVectorLaw b hb).weight (negateY y) = (yVectorLaw b hb).weight y := by
  simp only [yVectorLaw_weight, negateY]
  apply Finset.prod_congr rfl
  intro a _ha
  exact mass_negateOutcome b (y a)

theorem support_negateY {b : ℕ} (y : YVector b) : support (negateY y) = support y := by
  ext a
  rw [mem_support, mem_support]
  cases h : y a <;> simp [negateY, negateOutcome, h]

@[simp] theorem supportSize_negateY {b : ℕ} (y : YVector b) :
    supportSize (negateY y) = supportSize y := by
  simp [supportSize, support_negateY]

theorem kernelWeight_negateY {b : ℕ} (hb : 0 < b)
    (y : YVector b) (a : Fin b) (e : Sign) :
    kernelWeight hb (negateY y) (a, flipSign e) = kernelWeight hb y (a, e) := by
  classical
  cases e <;> cases h : y a <;>
    simp [kernelWeight, supportSize_negateY, selectorMatches, negateY,
      flipSign, outcomeOfSign, negateOutcome, h, selectorLaw]

/-- Permute two coordinate positions.  `Equiv.swap` is its own inverse. -/
def swapY {b : ℕ} (a c : Fin b) (y : YVector b) : YVector b :=
  fun k => y (Equiv.swap a c k)

@[simp] theorem swapY_involutive {b : ℕ} (a c : Fin b) (y : YVector b) :
    swapY a c (swapY a c y) = y := by
  funext k
  simp [swapY]

def swapYEquiv {b : ℕ} (a c : Fin b) : YVector b ≃ YVector b where
  toFun := swapY a c
  invFun := swapY a c
  left_inv := swapY_involutive a c
  right_inv := swapY_involutive a c

theorem yVectorLaw_weight_swapY {b : ℕ} (hb : 0 < b)
    (a c : Fin b) (y : YVector b) :
    (yVectorLaw b hb).weight (swapY a c y) = (yVectorLaw b hb).weight y := by
  simp only [yVectorLaw_weight, swapY]
  exact Function.Bijective.prod_comp (Equiv.swap a c).bijective
    (fun k => TernaryJacobi.mass b (y k))

theorem supportSize_eq_sum {b : ℕ} (y : YVector b) :
    supportSize y = ∑ a, if y a = .zero then 0 else 1 := by
  classical
  rw [supportSize, support]
  symm
  simpa using
    (Finset.sum_boole (R := ℕ) (fun a : Fin b => y a ≠ .zero) Finset.univ)

@[simp] theorem supportSize_swapY {b : ℕ} (a c : Fin b) (y : YVector b) :
    supportSize (swapY a c y) = supportSize y := by
  rw [supportSize_eq_sum, supportSize_eq_sum]
  change (∑ k, if y (Equiv.swap a c k) = .zero then 0 else 1) =
    ∑ k, if y k = .zero then 0 else 1
  exact Function.Bijective.sum_comp (Equiv.swap a c).bijective
    (fun k => if y k = .zero then 0 else 1)

theorem kernelWeight_swapY {b : ℕ} (hb : 0 < b)
    (y : YVector b) (a c : Fin b) (e : Sign) :
    kernelWeight hb (swapY a c y) (c, e) = kernelWeight hb y (a, e) := by
  classical
  cases e <;> cases h : y a <;>
    simp [kernelWeight, supportSize_swapY, selectorMatches, swapY,
      outcomeOfSign, h, selectorLaw]

/-- The `X`-fiber mass of the one-column joint law. -/
def xMarginal {b : ℕ} (hb : 0 < b) (x : SignedHash b) : ℝ :=
  ∑ y, (jointColumnLaw hb).weight (y, x)

theorem xMarginal_swap {b : ℕ} (hb : 0 < b)
    (a c : Fin b) (e : Sign) :
    xMarginal hb (c, e) = xMarginal hb (a, e) := by
  calc
    xMarginal hb (c, e) = ∑ y, (jointColumnLaw hb).weight (y, (c, e)) := rfl
    _ = ∑ y, (jointColumnLaw hb).weight (swapY a c y, (c, e)) := by
      exact ((swapYEquiv a c).sum_comp
        (fun y => (jointColumnLaw hb).weight (y, (c, e)))).symm
    _ = ∑ y, (jointColumnLaw hb).weight (y, (a, e)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [jointColumnLaw_weight, jointColumnLaw_weight,
        yVectorLaw_weight_swapY hb a c y, kernelWeight_swapY hb y a c e]
    _ = xMarginal hb (a, e) := rfl

theorem xMarginal_flip {b : ℕ} (hb : 0 < b) (a : Fin b) (e : Sign) :
    xMarginal hb (a, flipSign e) = xMarginal hb (a, e) := by
  calc
    xMarginal hb (a, flipSign e) =
        ∑ y, (jointColumnLaw hb).weight (y, (a, flipSign e)) := rfl
    _ = ∑ y, (jointColumnLaw hb).weight (negateY y, (a, flipSign e)) := by
      exact ((negateYEquiv b).sum_comp
        (fun y => (jointColumnLaw hb).weight (y, (a, flipSign e)))).symm
    _ = ∑ y, (jointColumnLaw hb).weight (y, (a, e)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [jointColumnLaw_weight, jointColumnLaw_weight,
        yVectorLaw_weight_negateY hb y, kernelWeight_negateY hb y a e]
    _ = xMarginal hb (a, e) := rfl

theorem xMarginal_constant {b : ℕ} (hb : 0 < b) (x z : SignedHash b) :
    xMarginal hb x = xMarginal hb z := by
  rcases x with ⟨a, e⟩
  rcases z with ⟨c, f⟩
  cases e <;> cases f
  · exact (xMarginal_swap hb a c .plus).symm
  · exact (xMarginal_swap hb a c .plus).symm.trans
      (by simpa [flipSign] using (xMarginal_flip hb c .plus).symm)
  · exact (xMarginal_swap hb a c .minus).symm.trans
      (by simpa [flipSign] using xMarginal_flip hb c .plus)
  · exact (xMarginal_swap hb a c .minus).symm

theorem sum_xMarginal {b : ℕ} (hb : 0 < b) :
    ∑ x, xMarginal hb x = 1 := by
  calc
    (∑ x, xMarginal hb x) =
        ∑ y, ∑ x, (jointColumnLaw hb).weight (y, x) := by
      simp only [xMarginal]
      exact Finset.sum_comm
    _ = ∑ z : YVector b × SignedHash b, (jointColumnLaw hb).weight z := by
      rw [Fintype.sum_prod_type]
    _ = 1 := (jointColumnLaw hb).sum_weight

/-- The selected signed coordinate is exactly uniform on the `2b` selectors. -/
theorem xMarginal_eq_selectorWeight {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    xMarginal hb x = (selectorLaw b hb).weight x := by
  have hconst : ∀ z : SignedHash b, xMarginal hb z = xMarginal hb x :=
    fun z => xMarginal_constant hb z x
  have hcard : Fintype.card (SignedHash b) = 2 * b := by
    simp [SignedHash, Fintype.card_prod, SparseStackDistribution.card_sign,
      Nat.mul_comm]
  have hsum : (2 * (b : ℝ)) * xMarginal hb x = 1 := by
    calc
      (2 * (b : ℝ)) * xMarginal hb x =
          (Fintype.card (SignedHash b) : ℝ) * xMarginal hb x := by
        rw [hcard]
        push_cast
        ring
      _ = ∑ z : SignedHash b, xMarginal hb x := by simp
      _ = ∑ z : SignedHash b, xMarginal hb z := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact (hconst z).symm
      _ = 1 := sum_xMarginal hb
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  rw [selectorLaw]
  dsimp
  apply (eq_div_iff (by positivity : (2 * (b : ℝ)) ≠ 0)).2
  nlinarith

/-- The second marginal of the joint law is precisely `selectorLaw`. -/
theorem jointColumn_x_marginal {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    (jointColumnLaw hb).prob {z | z.2 = x} = (selectorLaw b hb).weight x := by
  classical
  calc
    (jointColumnLaw hb).prob {z | z.2 = x} = xMarginal hb x := by
      rw [FiniteLaw.prob, FiniteLaw.expect, Fintype.sum_prod_type]
      change (∑ y, ∑ x', (jointColumnLaw hb).weight (y, x') *
        FiniteLaw.indicator {z : YVector b × SignedHash b | z.2 = x} (y, x')) =
          ∑ y, (jointColumnLaw hb).weight (y, x)
      apply Finset.sum_congr rfl
      intro y _hy
      simp [FiniteLaw.indicator]
    _ = (selectorLaw b hb).weight x := xMarginal_eq_selectorWeight hb x

/-! ## The exact conditional law `Y | X=x` and its barycenter -/

theorem selectorWeight_pos {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    0 < (selectorLaw b hb).weight x := by
  rw [selectorLaw]
  dsimp
  positivity

/-- The normalized conditional law obtained from the explicit joint fiber. -/
def conditionalYLaw {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    FiniteLaw (YVector b) where
  weight y := (jointColumnLaw hb).weight (y, x) /
    (selectorLaw b hb).weight x
  weight_nonneg y := div_nonneg ((jointColumnLaw hb).weight_nonneg (y, x))
    (selectorWeight_pos hb x).le
  sum_weight := by
    rw [← Finset.sum_div]
    change xMarginal hb x / (selectorLaw b hb).weight x = 1
    rw [xMarginal_eq_selectorWeight hb x]
    exact div_self (ne_of_gt (selectorWeight_pos hb x))

@[simp] theorem conditionalYLaw_weight {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (y : YVector b) :
    (conditionalYLaw hb x).weight y =
      (jointColumnLaw hb).weight (y, x) / (selectorLaw b hb).weight x := rfl

/-- Bayes/disintegration identity for the one-column joint law. -/
theorem jointColumn_disintegrates {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) :
    (jointColumnLaw hb).weight (y, x) =
      (selectorLaw b hb).weight x * (conditionalYLaw hb x).weight y := by
  rw [conditionalYLaw_weight]
  field_simp [ne_of_gt (selectorWeight_pos hb x)]

/-- Flip one coordinate of an iid vector. -/
def flipAt {b : ℕ} (a : Fin b) (y : YVector b) : YVector b :=
  by
    classical
    exact fun k => if k = a then negateOutcome (y k) else y k

@[simp] theorem flipAt_apply_same {b : ℕ} (a : Fin b) (y : YVector b) :
    flipAt a y a = negateOutcome (y a) := by
  simp [flipAt]

theorem flipAt_apply_of_ne {b : ℕ} {a k : Fin b} (hka : k ≠ a) (y : YVector b) :
    flipAt a y k = y k := by
  simp [flipAt, hka]

@[simp] theorem flipAt_involutive {b : ℕ} (a : Fin b) (y : YVector b) :
    flipAt a (flipAt a y) = y := by
  classical
  funext k
  by_cases hka : k = a
  · subst k
    simp
  · simp [flipAt, hka]

def flipAtEquiv {b : ℕ} (a : Fin b) : YVector b ≃ YVector b where
  toFun := flipAt a
  invFun := flipAt a
  left_inv := flipAt_involutive a
  right_inv := flipAt_involutive a

theorem yVectorLaw_weight_flipAt {b : ℕ} (hb : 0 < b)
    (a : Fin b) (y : YVector b) :
    (yVectorLaw b hb).weight (flipAt a y) = (yVectorLaw b hb).weight y := by
  simp only [yVectorLaw_weight]
  apply Finset.prod_congr rfl
  intro k _hk
  by_cases hka : k = a
  · subst k
    simp [mass_negateOutcome]
  · simp [flipAt_apply_of_ne hka]

@[simp] theorem supportSize_flipAt {b : ℕ} (a : Fin b) (y : YVector b) :
    supportSize (flipAt a y) = supportSize y := by
  rw [supportSize_eq_sum, supportSize_eq_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hka : k = a
  · subst k
    cases h : y a <;> simp [flipAt, negateOutcome, h]
  · simp [flipAt_apply_of_ne hka]

theorem kernelWeight_flipAt_of_ne {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) (a : Fin b) (ha : a ≠ x.1) :
    kernelWeight hb (flipAt a y) x = kernelWeight hb y x := by
  classical
  have hxa : x.1 ≠ a := Ne.symm ha
  simp [kernelWeight, supportSize_flipAt, selectorMatches,
    flipAt_apply_of_ne hxa]

/-- Unnormalized first moment of a conditional fiber. -/
def fiberMoment {b : ℕ} (hb : 0 < b) (x : SignedHash b) (a : Fin b) : ℝ :=
  ∑ y, (jointColumnLaw hb).weight (y, x) * yValue (y a)

theorem fiberMoment_off {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (a : Fin b) (ha : a ≠ x.1) :
    fiberMoment hb x a = 0 := by
  have hsymm : fiberMoment hb x a = -fiberMoment hb x a := by
    calc
      fiberMoment hb x a =
          ∑ y, (jointColumnLaw hb).weight (flipAt a y, x) *
            yValue ((flipAt a y) a) := by
        exact ((flipAtEquiv a).sum_comp
          (fun y => (jointColumnLaw hb).weight (y, x) * yValue (y a))).symm
      _ = ∑ y, -((jointColumnLaw hb).weight (y, x) * yValue (y a)) := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [jointColumnLaw_weight, jointColumnLaw_weight,
          yVectorLaw_weight_flipAt hb a y,
          kernelWeight_flipAt_of_ne hb y x a ha]
        simp
      _ = -fiberMoment hb x a := by
        simp [fiberMoment]
  linarith

theorem zeroSupportMass {b : ℕ} (hb : 0 < b) :
    (∑ y, (yVectorLaw b hb).weight y *
      (if supportSize y = 0 then (1 : ℝ) else 0)) = p0 b := by
  classical
  calc
    (∑ y, (yVectorLaw b hb).weight y *
        (if supportSize y = 0 then (1 : ℝ) else 0)) =
        (yVectorLaw b hb).prob {zeroY b} := by
      rw [FiniteLaw.prob, FiniteLaw.expect]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hy : y = zeroY b
      · subst y
        simp [FiniteLaw.indicator, supportSize_eq_zero_iff]
      · have hs : supportSize y ≠ 0 := by
          simpa [supportSize_eq_zero_iff] using hy
        simp [FiniteLaw.indicator, hy, hs]
    _ = (yVectorLaw b hb).weight (zeroY b) :=
      FiniteLaw.prob_singleton (yVectorLaw b hb) (zeroY b)
    _ = p0 b := zeroY_weight hb

theorem kernelWeight_mul_selectedValue {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) :
    kernelWeight hb y x * yValue (y x.1) =
      x.2.val * kernelWeight hb y x -
        x.2.val * (selectorLaw b hb).weight x *
          (if supportSize y = 0 then (1 : ℝ) else 0) := by
  classical
  by_cases hzero : supportSize y = 0
  · have hy : y = zeroY b := (supportSize_eq_zero_iff y).mp hzero
    subst y
    simp [kernelWeight, hzero, zeroY, yValue]
  · by_cases hmatch : selectorMatches y x
    · have hyx : y x.1 = outcomeOfSign x.2 := hmatch
      simp [kernelWeight, hzero, hmatch, hyx]
      ring
    · simp [kernelWeight, hzero, hmatch]

theorem fiberMoment_selected {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    fiberMoment hb x x.1 =
      x.2.val * (selectorLaw b hb).weight x * (1 - p0 b) := by
  calc
    fiberMoment hb x x.1 =
        ∑ y, (yVectorLaw b hb).weight y *
          (kernelWeight hb y x * yValue (y x.1)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [jointColumnLaw_weight]
      ring
    _ = ∑ y, (yVectorLaw b hb).weight y *
        (x.2.val * kernelWeight hb y x -
          x.2.val * (selectorLaw b hb).weight x *
            (if supportSize y = 0 then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [kernelWeight_mul_selectedValue hb y x]
    _ = x.2.val * xMarginal hb x -
        x.2.val * (selectorLaw b hb).weight x *
          (∑ y, (yVectorLaw b hb).weight y *
            (if supportSize y = 0 then (1 : ℝ) else 0)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      simp only [xMarginal, jointColumnLaw_weight]
      simp_rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro y _hy
        ring
      · apply Finset.sum_congr rfl
        intro y _hy
        ring
    _ = x.2.val * (selectorLaw b hb).weight x * (1 - p0 b) := by
      rw [xMarginal_eq_selectorWeight hb x, zeroSupportMass hb]
      ring

theorem cB_mul_one_sub_p0 {b : ℕ} (hb : 0 < b) :
    cB b * (1 - p0 b) = 1 := by
  rw [cB]
  exact inv_mul_cancel₀ (ne_of_gt (one_sub_p0_pos hb))

theorem conditional_expect_yValue {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (a : Fin b) :
    (conditionalYLaw hb x).expect (fun y => yValue (y a)) =
      if a = x.1 then x.2.val * (1 - p0 b) else 0 := by
  by_cases ha : a = x.1
  · subst a
    rw [if_pos rfl, FiniteLaw.expect]
    simp only [conditionalYLaw_weight]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    change fiberMoment hb x x.1 / (selectorLaw b hb).weight x = _
    rw [fiberMoment_selected hb x]
    field_simp [ne_of_gt (selectorWeight_pos hb x)]
  · rw [if_neg ha, FiniteLaw.expect]
    simp only [conditionalYLaw_weight]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    change fiberMoment hb x a / (selectorLaw b hb).weight x = 0
    rw [fiberMoment_off hb x a ha, zero_div]

/-- Coordinatewise martingale identity `E[c_b Y | X=x] = X`. -/
theorem conditional_barycenter_coordinate {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (a : Fin b) :
    (conditionalYLaw hb x).expect (fun y => cB b * yValue (y a)) =
      if a = x.1 then x.2.val else 0 := by
  rw [FiniteLaw.expect_smul, conditional_expect_yValue hb x a]
  by_cases ha : a = x.1
  · rw [if_pos ha, if_pos ha]
    calc
      cB b * (x.2.val * (1 - p0 b)) = x.2.val * (cB b * (1 - p0 b)) := by ring
      _ = x.2.val := by rw [cB_mul_one_sub_p0 hb, mul_one]
  · simp [ha]

/-- Signed basis vector attached directly to one selector. -/
def selectorVector {b : ℕ} (x : SignedHash b) : EVec b :=
  WithLp.toLp 2 fun a => if a = x.1 then x.2.val else 0

/-- The finite conditional barycenter as a Euclidean vector. -/
def conditionalBarycenter {b : ℕ} (hb : 0 < b) (x : SignedHash b) : EVec b :=
  WithLp.toLp 2 fun a =>
    (conditionalYLaw hb x).expect (fun y => cB b * yValue (y a))

theorem conditional_barycenter {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    conditionalBarycenter hb x = selectorVector x := by
  ext a
  exact conditional_barycenter_coordinate hb x a

end

end SparseIIDCoupling

end SparseFock
