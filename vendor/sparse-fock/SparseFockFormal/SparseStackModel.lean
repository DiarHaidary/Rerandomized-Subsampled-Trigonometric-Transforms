import SparseFockFormal.ParsevalFrame
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace SparseFock

namespace SparseStackModel

open scoped BigOperators InnerProductSpace
open ParsevalFrame

noncomputable section

/-- A Rademacher sign, with no zero constructor. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq

/-- The exact real value of a Rademacher sign. -/
def Sign.val : Sign → ℝ
  | .plus => 1
  | .minus => -1

@[simp] theorem Sign.val_plus : Sign.plus.val = 1 := rfl
@[simp] theorem Sign.val_minus : Sign.minus.val = -1 := rfl

@[simp]
theorem Sign.val_sq (z : Sign) : z.val ^ 2 = 1 := by
  cases z <;> norm_num [Sign.val]

theorem Sign.val_ne_zero (z : Sign) : z.val ≠ 0 := by
  cases z <;> norm_num [Sign.val]

@[simp]
theorem Sign.abs_val (z : Sign) : |z.val| = 1 := by
  cases z <;> norm_num [Sign.val]

/-- One fully explicit SparseStack outcome.  Both the hash and the sign are indexed
by the literal sample space `Fin s × Fin n`. -/
structure Sample (s b n : ℕ) where
  h : Fin s × Fin n → Fin b
  sign : Fin s × Fin n → Sign

def Sample.hash {s b n : ℕ} (Z : Sample s b n) (g : Fin s) (i : Fin n) : Fin b :=
  Z.h (g, i)

def Sample.sgn {s b n : ℕ} (Z : Sample s b n) (g : Fin s) (i : Fin n) : Sign :=
  Z.sign (g, i)

/-- The signed basis vector `X_{g i} = σ_{g i} e_{h_g(i)}`. -/
def signedBasis {s b n : ℕ} (Z : Sample s b n) (g : Fin s) (i : Fin n) :
    EVec b :=
  WithLp.toLp 2 fun a ↦ if a = Z.hash g i then (Z.sgn g i).val else 0

@[simp]
theorem signedBasis_apply {s b n : ℕ} (Z : Sample s b n)
    (g : Fin s) (i : Fin n) (a : Fin b) :
    signedBasis Z g i a = if a = Z.hash g i then (Z.sgn g i).val else 0 := rfl

/-- Exact collision formula for the signed basis vectors. -/
theorem inner_signedBasis {s b n : ℕ} (Z : Sample s b n)
    (g : Fin s) (i j : Fin n) :
    ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ =
      if Z.hash g i = Z.hash g j
      then (Z.sgn g i).val * (Z.sgn g j).val else 0 := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, signedBasis_apply]
  by_cases hij : Z.hash g i = Z.hash g j
  · rw [hij]
    simp
  · simp only [hij, if_false]
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hai : a = Z.hash g i
    · have haj : a ≠ Z.hash g j := by
        intro haj
        exact hij (hai.symm.trans haj)
      rw [if_pos hai, if_neg haj]
      ring
    · rw [if_neg hai]
      ring

/-- `‖X_{g i}‖² = 1` exactly, not merely almost surely. -/
@[simp]
theorem signedBasis_normSq {s b n : ℕ} (Z : Sample s b n)
    (g : Fin s) (i : Fin n) :
    normSq (signedBasis Z g i) = 1 := by
  rw [normSq, inner_signedBasis]
  simpa [pow_two] using Sign.val_sq (Z.sgn g i)

@[simp]
theorem inner_signedBasis_self {s b n : ℕ} (Z : Sample s b n)
    (g : Fin s) (i : Fin n) :
    ⟪signedBasis Z g i, signedBasis Z g i⟫_ℝ = 1 := by
  simpa [normSq] using signedBasis_normSq Z g i

/-- The normalization `s^{-1/2}`. -/
def invSqrt (s : ℕ) : ℝ := (Real.sqrt (s : ℝ))⁻¹

/-- The stacked sketch matrix, with rows indexed without flattening by
`Fin s × Fin b` and columns by `Fin n`. -/
def stackMatrix {s b n : ℕ} (Z : Sample s b n) :
    Matrix (Fin s × Fin b) (Fin n) ℝ :=
  fun r i ↦ invSqrt s * signedBasis Z r.1 i r.2

@[simp]
theorem stackMatrix_apply {s b n : ℕ} (Z : Sample s b n)
    (g : Fin s) (a : Fin b) (i : Fin n) :
    stackMatrix Z (g, a) i = invSqrt s *
      (if a = Z.hash g i then (Z.sgn g i).val else 0) := rfl

theorem invSqrt_ne_zero {s : ℕ} (hs : 0 < s) : invSqrt s ≠ 0 := by
  apply inv_ne_zero
  exact ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hs))

theorem invSqrt_sq {s : ℕ} (_hs : 0 < s) :
    invSqrt s ^ 2 = 1 / (s : ℝ) := by
  rw [invSqrt, inv_pow, Real.sq_sqrt (Nat.cast_nonneg s)]
  simp [div_eq_mul_inv]

/-- A matrix entry is nonzero exactly at the sampled hash location. -/
theorem stackMatrix_ne_zero_iff {s b n : ℕ} (Z : Sample s b n) (hs : 0 < s)
    (g : Fin s) (a : Fin b) (i : Fin n) :
    stackMatrix Z (g, a) i ≠ 0 ↔ a = Z.hash g i := by
  by_cases ha : a = Z.hash g i
  · simp [stackMatrix_apply, ha, invSqrt_ne_zero hs, Sign.val_ne_zero]
  · simp [stackMatrix_apply, ha]

/-- In each block and column there is exactly one nonzero entry. -/
theorem exactly_one_nonzero_in_block {s b n : ℕ} (Z : Sample s b n) (hs : 0 < s)
    (g : Fin s) (i : Fin n) :
    ∃! a : Fin b, stackMatrix Z (g, a) i ≠ 0 := by
  refine ⟨Z.hash g i, ?_, ?_⟩
  · exact (stackMatrix_ne_zero_iff Z hs g (Z.hash g i) i).2 rfl
  · intro a ha
    exact (stackMatrix_ne_zero_iff Z hs g a i).1 ha

/-- The nonzero support of one column is canonically equivalent to the block index. -/
def columnSupportEquiv {s b n : ℕ} (Z : Sample s b n) (hs : 0 < s) (i : Fin n) :
    {r : Fin s × Fin b // stackMatrix Z r i ≠ 0} ≃ Fin s where
  toFun r := r.1.1
  invFun g := ⟨(g, Z.hash g i),
    (stackMatrix_ne_zero_iff Z hs g (Z.hash g i) i).2 rfl⟩
  left_inv := by
    rintro ⟨⟨g, a⟩, ha⟩
    have hloc := (stackMatrix_ne_zero_iff Z hs g a i).1 ha
    subst a
    rfl
  right_inv := by
    intro g
    rfl

/-- Consequently every column has exactly `s` nonzero entries. -/
theorem exactly_s_nonzeros_per_column {s b n : ℕ} (Z : Sample s b n) (hs : 0 < s)
    (i : Fin n) :
    Fintype.card {r : Fin s × Fin b // stackMatrix Z r i ≠ 0} = s := by
  rw [Fintype.card_congr (columnSupportEquiv Z hs i)]
  simp

/-- The sketch Gram matrix `ΠᵀΠ`. -/
def sketchGram {s b n : ℕ} (Z : Sample s b n) : Matrix (Fin n) (Fin n) ℝ :=
  (stackMatrix Z).transpose * stackMatrix Z

theorem block_gram_apply {s b n : ℕ} (Z : Sample s b n)
    (g : Fin s) (i j : Fin n) :
    (∑ a : Fin b, stackMatrix Z (g, a) i * stackMatrix Z (g, a) j) =
      invSqrt s ^ 2 * ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, stackMatrix_apply, signedBasis_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Exact entrywise Gram formula for the normalized stacked sketch. -/
theorem sketchGram_apply {s b n : ℕ} (Z : Sample s b n) (hs : 0 < s)
    (i j : Fin n) :
    sketchGram Z i j =
      (1 / (s : ℝ)) * ∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ := by
  rw [sketchGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [block_gram_apply Z]
  rw [← Finset.mul_sum, invSqrt_sq hs]

/-- The embedded Gram matrix `UᵀΠᵀΠU`. -/
def embeddedGram {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (rowMatrix F.u).transpose * (sketchGram Z * rowMatrix F.u)

/-- The Gram error `UᵀΠᵀΠU - I_d`. -/
def gramError {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  embeddedGram F Z - 1

/-- The full ordered-column expansion, before canceling its diagonal. -/
def fullGramExpansion {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a c ↦ (1 / (s : ℝ)) *
    ∑ i, ∑ j, (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) *
      F.u i a * F.u j c

/-- The exact hollow sum.  `j ∈ univ.erase i` is the literal finite encoding of `i ≠ j`. -/
def hollowGram {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a c ↦ (1 / (s : ℝ)) *
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c

/-- Expanding the matrix products gives the full three-index sum. -/
theorem embeddedGram_eq_fullExpansion {s b n d : ℕ} (F : Frame n d)
    (Z : Sample s b n) (hs : 0 < s) :
    embeddedGram F Z = fullGramExpansion F Z := by
  ext a c
  simp only [embeddedGram, Matrix.mul_apply, Matrix.transpose_apply, rowMatrix]
  simp_rw [sketchGram_apply Z hs]
  simp only [fullGramExpansion]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  ring

/-- The diagonal part of the full expansion is exactly `I_d`. -/
theorem fullExpansion_eq_one_add_hollow {s b n d : ℕ} (F : Frame n d)
    (Z : Sample s b n) (hs : 0 < s) :
    fullGramExpansion F Z = 1 + hollowGram F Z := by
  classical
  ext a c
  have hs0 : (s : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs))
  have hparseval := congrArg
    (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M a c) F.parseval
  have hparseval' : (∑ i, F.u i a * F.u i c) =
      (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
    simpa [Matrix.sum_apply, outer] using hparseval
  let T : Fin n → Fin n → ℝ := fun i j ↦
    (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c
  have hsplit (i : Fin n) :
      (∑ j, T i j) = T i i + ∑ j ∈ Finset.univ.erase i, T i j := by
    have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    rw [← Finset.sum_erase_add _ _ hi]
    ring
  have hdiag :
      (1 / (s : ℝ)) * ∑ i, T i i =
        (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
    have hTi (i : Fin n) : T i i = (s : ℝ) * F.u i a * F.u i c := by
      have hone :
          (∑ g, ⟪signedBasis Z g i, signedBasis Z g i⟫_ℝ) = (s : ℝ) := by
        simp only [inner_signedBasis_self]
        simp
      dsimp [T]
      rw [hone]
    simp_rw [hTi]
    calc
      (1 / (s : ℝ)) * ∑ i, (s : ℝ) * F.u i a * F.u i c =
          ((1 / (s : ℝ)) * (s : ℝ)) * ∑ i, F.u i a * F.u i c := by
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
      _ = ∑ i, F.u i a * F.u i c := by field_simp [hs0]
      _ = (1 : Matrix (Fin d) (Fin d) ℝ) a c := hparseval'
  simp only [fullGramExpansion, hollowGram, Matrix.add_apply]
  change (1 / (s : ℝ)) * (∑ i, ∑ j, T i j) =
    (1 : Matrix (Fin d) (Fin d) ℝ) a c +
      (1 / (s : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, T i j
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  rw [mul_add]
  rw [hdiag]

/-- The exact hollow identity (paper (2.2)): the Parseval diagonal cancels from
`UᵀΠᵀΠU-I`, leaving only ordered pairs `i ≠ j`. -/
theorem gramError_eq_hollow {s b n d : ℕ} (F : Frame n d)
    (Z : Sample s b n) (hs : 0 < s) :
    gramError F Z = hollowGram F Z := by
  rw [gramError, embeddedGram_eq_fullExpansion F Z hs,
    fullExpansion_eq_one_add_hollow F Z hs]
  abel

/-- The same hollow sum with the block index written first, matching the paper's
literal order `Σ_g Σ_{i≠j}`. -/
theorem hollowGram_block_first {s b n d : ℕ} (F : Frame n d) (Z : Sample s b n) :
    hollowGram F Z = fun a c ↦ (1 / (s : ℝ)) *
      ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
  ext a c
  simp only [hollowGram]
  congr 1
  have hfixed (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i,
          (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c) =
        ∑ g, ∑ j ∈ Finset.univ.erase i,
          ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        (∑ g, ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ) * F.u i a * F.u j c) =
      ∑ i, ∑ g, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hfixed i
    _ = ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c :=
      Finset.sum_comm

/-- Paper-form statement of the hollow identity, with the block sum outermost. -/
theorem gramError_eq_block_first {s b n d : ℕ} (F : Frame n d)
    (Z : Sample s b n) (hs : 0 < s) :
    gramError F Z = fun a c ↦ (1 / (s : ℝ)) *
      ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
        ⟪signedBasis Z g i, signedBasis Z g j⟫_ℝ * F.u i a * F.u j c := by
  rw [gramError_eq_hollow F Z hs, hollowGram_block_first F Z]

end

end SparseStackModel

end SparseFock
