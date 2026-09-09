import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Positive block Schur compression with a bounded number of grade neighbors. -/

open scoped BigOperators InnerProduct Matrix Matrix.Norms.L2Operator

namespace SRHT.GradeCompression

noncomputable section

section Hilbert

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype J] [DecidableEq J]

local notation "⟪" x ", " y "⟫" => @inner ℝ H _ x y

/-- A positive operator is bounded by its quadratic form, including the zero space. -/
theorem positive_norm_le_of_quadratic (A : H →L[ℝ] H) (hA : A.IsPositive)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, ⟪v, A v⟫ ≤ C * ‖v‖^2) : ‖A‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  have hp := hb (x+y)
  have hn := hA.inner_nonneg_right (x-y)
  have hs : ⟪y, A x⟫ = ⟪x, A y⟫ := by
    rw [← hA.inner_left_eq_inner_right, real_inner_comm]
  have hnxy : ‖x+y‖ ≤ 2 := by
    have h := norm_add_le x y
    rw [hx,hy] at h
    norm_num at h ⊢
    exact h
  have hnxy0 := norm_nonneg (x+y)
  have hns : ‖x+y‖^2 ≤ 4 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hns hC
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, hs] at hp hn
  have ht : ⟪A x,y⟫ = ⟪x,A y⟫ := hA.inner_left_eq_inner_right x y
  change ⟪A x,y⟫ ≤ C
  rw [ht]
  nlinarith

/-- Positivity bounds one off-diagonal quadratic pairing by its two diagonal pairings. -/
theorem positive_cross_le (A : H →L[ℝ] H) (hA : A.IsPositive) (u v : H) :
    2 * ⟪u,A v⟫ ≤ ⟪u,A u⟫ + ⟪v,A v⟫ := by
  have h := hA.inner_nonneg_right (u-v)
  have hs : ⟪v,A u⟫ = ⟪u,A v⟫ := by
    rw [← hA.inner_left_eq_inner_right, real_inner_comm]
  simp only [map_sub, inner_sub_left, inner_sub_right, hs] at h
  linarith

/-- The sum of pair energies on a symmetric graph counts each vertex energy twice. -/
theorem neighbor_energy_sum (R : J → J → Prop) [DecidableRel R]
    (hR : ∀ a b, R a b ↔ R b a) (e : J → ℝ) :
    (∑ a, ∑ b, if R a b then e a + e b else 0) =
      2 * ∑ a, ((Finset.univ.filter (R a)).card : ℝ) * e a := by
  have h1 (a : J) : (∑ b, if R a b then e a else 0) =
      ((Finset.univ.filter (R a)).card : ℝ) * e a := by
    rw [← Finset.sum_filter]
    simp
  have h2 : (∑ a, ∑ b, if R a b then e b else 0) =
      ∑ a, ((Finset.univ.filter (R a)).card : ℝ) * e a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp_rw [← hR b]
    exact h1 b
  simp_rw [ite_add_zero, Finset.sum_add_distrib]
  rw [h2]
  simp_rw [h1]
  ring

/-- A positive operator with at most `B` neighbors has the block Schur bound
on every finite family of vectors whose diagonal energies are at most `L`. -/
theorem positive_family_schur (A : H →L[ℝ] H) (hA : A.IsPositive)
    (R : J → J → Prop) [DecidableRel R] (hR : ∀ a b, R a b ↔ R b a)
    (B : ℕ) (hB : ∀ a, (Finset.univ.filter (R a)).card ≤ B)
    {L : ℝ} (hL : 0 ≤ L) (f : J → H)
    (hzero : ∀ a b, ¬ R a b → ⟪f a,A (f b)⟫ = 0)
    (hdiag : ∀ a, ⟪f a,A (f a)⟫ ≤ L * ‖f a‖^2) :
    ⟪∑ a,f a, A (∑ a,f a)⟫ ≤ (B:ℝ) * L * ∑ a, ‖f a‖^2 := by
  have hterm (a b : J) :
      2 * ⟪f a,A (f b)⟫ ≤ if R a b then L * (‖f a‖^2 + ‖f b‖^2) else 0 := by
    by_cases hr : R a b
    · rw [if_pos hr]
      have hc := positive_cross_le A hA (f a) (f b)
      have ha := hdiag a
      have hb := hdiag b
      nlinarith
    · rw [if_neg hr, hzero a b hr]
      norm_num
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun b _ => hterm a b))
  have hcount : (∑ a, ((Finset.univ.filter (R a)).card:ℝ) * ‖f a‖^2) ≤
      (B:ℝ) * ∑ a, ‖f a‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB a) (sq_nonneg _)
  have he := neighbor_energy_sum R hR (fun a => ‖f a‖^2)
  have he' : (∑ a, ∑ b, if R a b then L * (‖f a‖^2 + ‖f b‖^2) else 0) =
      L * (2 * ∑ a, ((Finset.univ.filter (R a)).card:ℝ) * ‖f a‖^2) := by
    rw [← he]
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [he'] at hsum
  simp only [← Finset.mul_sum] at hsum
  have hmul := mul_le_mul_of_nonneg_left hcount hL
  simp only [map_sum, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  nlinarith

/-- The block Schur bound for an actual positive resolution of the identity.
No off-diagonal norm hypothesis is imposed. -/
theorem positive_projection_schur (A : H →L[ℝ] H) (hA : A.IsPositive)
    (P : J → H →L[ℝ] H) (hP : ∀ a, (P a).IsPositive)
    (hP2 : ∀ a, P a * P a = P a) (hPsum : ∑ a, P a = 1)
    (R : J → J → Prop) [DecidableRel R] (hR : ∀ a b, R a b ↔ R b a)
    (B : ℕ) (hB : ∀ a, (Finset.univ.filter (R a)).card ≤ B)
    {L : ℝ} (hL : 0 ≤ L)
    (hzero : ∀ a b, ¬ R a b → P a * A * P b = 0)
    (hdiag : ∀ a, ‖P a * A * P a‖ ≤ L) : ‖A‖ ≤ (B:ℝ) * L := by
  apply positive_norm_le_of_quadratic A hA (mul_nonneg (Nat.cast_nonneg B) hL)
  intro v
  have hsplit : (∑ a, P a v) = v := by
    rw [← ContinuousLinearMap.sum_apply, hPsum]
    rfl
  have hfix (a : J) : P a (P a v) = P a v :=
    congrArg (fun Q : H →L[ℝ] H => Q v) (hP2 a)
  have henergy : (∑ a, ‖P a v‖^2) = ‖v‖^2 := by
    calc
      _ = ∑ a, ⟪v,P a v⟫ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← real_inner_self_eq_norm_sq, (hP a).inner_left_eq_inner_right, hfix]
      _ = ⟪v,∑ a,P a v⟫ := by rw [inner_sum]
      _ = _ := by rw [hsplit, real_inner_self_eq_norm_sq]
  have hz (a b : J) (hr : ¬R a b) : ⟪P a v,A (P b v)⟫ = 0 := by
    rw [(hP a).inner_left_eq_inner_right]
    change ⟪v,(P a * A * P b) v⟫ = 0
    rw [hzero a b hr]
    simp
  have hd (a : J) : ⟪P a v,A (P a v)⟫ ≤ L * ‖P a v‖^2 := by
    have he : ⟪P a v,A (P a v)⟫ = ⟪P a v,(P a * A * P a) (P a v)⟫ := by
      simp only [ContinuousLinearMap.mul_apply, hfix]
      rw [← (hP a).inner_left_eq_inner_right, hfix]
    rw [he]
    calc
      _ ≤ ‖P a v‖ * ‖(P a * A * P a) (P a v)‖ := real_inner_le_norm _ _
      _ ≤ ‖P a v‖ * (‖P a * A * P a‖ * ‖P a v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖P a v‖ * (L * ‖P a v‖) := by gcongr; exact hdiag a
      _ = L * ‖P a v‖^2 := by ring
  have h := positive_family_schur A hA R hR B hB hL (fun a => P a v) hz hd
  simpa only [hsplit, henergy, mul_assoc] using h

end Hilbert

section Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem matrix_positive (A : Matrix I I ℝ) (hA : A.PosSemidef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).2
  constructor
  · change star (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) A) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) A
    rw [← map_star]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) hA.isHermitian
  · intro x
    rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
    simpa using hA.dotProduct_mulVec_nonneg (WithLp.ofLp x)

/-- Matrix form of the positive block Schur theorem, in the true Euclidean norm. -/
theorem matrix_projection_schur (A : Matrix I I ℝ) (hA : A.PosSemidef)
    (P : J → Matrix I I ℝ) (hP : ∀ a, (P a).PosSemidef)
    (hP2 : ∀ a, P a * P a = P a) (hPsum : ∑ a, P a = 1)
    (R : J → J → Prop) [DecidableRel R] (hR : ∀ a b, R a b ↔ R b a)
    (B : ℕ) (hB : ∀ a, (Finset.univ.filter (R a)).card ≤ B)
    {L : ℝ} (hL : 0 ≤ L)
    (hzero : ∀ a b, ¬ R a b → P a * A * P b = 0)
    (hdiag : ∀ a, ‖P a * A * P a‖ ≤ L) : ‖A‖ ≤ (B:ℝ) * L := by
  let F := Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ)
  have h := positive_projection_schur (F A) (matrix_positive A hA)
    (fun a => F (P a)) (fun a => matrix_positive _ (hP a))
    (fun a => by rw [← map_mul, hP2])
    (by rw [← map_sum, hPsum, map_one]) R hR B hB hL
    (fun a b hr => by rw [← map_mul, ← map_mul, hzero a b hr, map_zero])
    (fun a => by simpa only [← map_mul, F, Matrix.l2_opNorm_toEuclideanCLM] using hdiag a)
  simpa only [F, Matrix.l2_opNorm_toEuclideanCLM] using h

/-- The coordinate projection onto one grade of a concrete partition. -/
def gradeProjection (grade : I → J) (a : J) : Matrix I I ℝ :=
  Matrix.diagonal (fun i => if grade i = a then 1 else 0)

theorem gradeProjection_positive (grade : I → J) (a : J) :
    (gradeProjection grade a).PosSemidef :=
  Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> norm_num)

theorem gradeProjection_square (grade : I → J) (a : J) :
    gradeProjection grade a * gradeProjection grade a = gradeProjection grade a := by
  rw [gradeProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem sum_gradeProjection (grade : I → J) : (∑ a, gradeProjection grade a) = 1 := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [gradeProjection, Matrix.sum_apply, Matrix.diagonal_apply]
  · simp [gradeProjection, Matrix.sum_apply, Matrix.diagonal_apply, hij]

theorem grade_block_apply (A : Matrix I I ℝ) (grade : I → J) (a b : J) (i j : I) :
    (gradeProjection grade a * A * gradeProjection grade b) i j =
      if grade i=a ∧ grade j=b then A i j else 0 := by
  by_cases hi : grade i=a <;> by_cases hj : grade j=b <;>
    simp [gradeProjection,Matrix.mul_diagonal,Matrix.diagonal_mul,hi,hj]

/-- Pointwise degree support suffices for the zero off-diagonal block condition. -/
theorem grade_block_zero_of_entries (A : Matrix I I ℝ) (grade : I → J)
    (R : J → J → Prop)
    (hzero : ∀ i j, ¬R (grade i) (grade j) → A i j=0)
    (a b : J) (hab : ¬R a b) :
    gradeProjection grade a * A * gradeProjection grade b = 0 := by
  ext i j
  rw [grade_block_apply]
  by_cases h : grade i=a ∧ grade j=b
  · rw [if_pos h]
    exact hzero i j (by simpa only [h.1,h.2] using hab)
  · simp [h]

/-- A positive matrix split by an actual grade map loses only the maximum
number of allowed neighboring grades. -/
theorem grade_schur (A : Matrix I I ℝ) (hA : A.PosSemidef) (grade : I → J)
    (R : J → J → Prop) [DecidableRel R] (hR : ∀ a b, R a b ↔ R b a)
    (B : ℕ) (hB : ∀ a, (Finset.univ.filter (R a)).card ≤ B)
    {L : ℝ} (hL : 0 ≤ L)
    (hzero : ∀ a b, ¬ R a b → gradeProjection grade a * A * gradeProjection grade b = 0)
    (hdiag : ∀ a, ‖gradeProjection grade a * A * gradeProjection grade a‖ ≤ L) :
    ‖A‖ ≤ (B:ℝ) * L :=
  matrix_projection_schur A hA (gradeProjection grade) (gradeProjection_positive grade)
    (gradeProjection_square grade) (sum_gradeProjection grade) R hR B hB hL hzero hdiag

end Matrix

section NineNeighbors

/-- A quadratic sign multiplication changes occupation by exactly `-2`, `0`, or `2`. -/
def evenStep (a b : ℕ) : Prop := a = b ∨ a + 2 = b ∨ b + 2 = a

instance : DecidableRel evenStep := fun a b => inferInstanceAs (Decidable (a=b ∨ a+2=b ∨ b+2=a))

theorem evenStep_symm (a b : ℕ) : evenStep a b ↔ evenStep b a := by
  unfold evenStep
  omega

theorem evenStep_neighbor_count {N : ℕ} (a : Fin N) :
    (Finset.univ.filter (fun b : Fin N => evenStep a.val b.val)).card ≤ 3 := by
  classical
  let S := Finset.univ.filter (fun b : Fin N => evenStep a.val b.val)
  have hsub : S.image Fin.val ⊆ {a.val, a.val+2, a.val-2} := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have h := (Finset.mem_filter.mp hc).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    unfold evenStep at h
    omega
  calc
    S.card = (S.image Fin.val).card := (Finset.card_image_of_injective S Fin.val_injective).symm
    _ ≤ ({a.val, a.val+2, a.val-2}:Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 3 := by
      have h := Finset.card_insert_le a.val ({a.val+2,a.val-2}:Finset ℕ)
      have h' := Finset.card_insert_le (a.val+2) ({a.val-2}:Finset ℕ)
      simp only [Finset.card_singleton] at h'
      omega

def pairEvenStep {N M : ℕ} (a b : Fin N × Fin M) : Prop :=
  evenStep a.1.val b.1.val ∧ evenStep a.2.val b.2.val

instance {N M : ℕ} : DecidableRel (@pairEvenStep N M) :=
  fun a b => inferInstanceAs (Decidable (evenStep a.1.val b.1.val ∧ evenStep a.2.val b.2.val))

theorem pairEvenStep_symm {N M : ℕ} (a b : Fin N × Fin M) :
    pairEvenStep a b ↔ pairEvenStep b a := by
  simp only [pairEvenStep, evenStep_symm]

theorem pairEvenStep_neighbor_count {N M : ℕ} (a : Fin N × Fin M) :
    (Finset.univ.filter (pairEvenStep a)).card ≤ 9 := by
  have hset : Finset.univ.filter (pairEvenStep a) =
      (Finset.univ.filter (fun b : Fin N => evenStep a.1.val b.val)) ×ˢ
      (Finset.univ.filter (fun b : Fin M => evenStep a.2.val b.val)) := by
    ext b
    simp [pairEvenStep]
  rw [hset, Finset.card_product]
  have h1 := evenStep_neighbor_count a.1
  have h2 := evenStep_neighbor_count a.2
  exact (Nat.mul_le_mul h1 h2).trans (by norm_num)

/-- The sign-pair instance of the generic theorem has the exact factor nine. -/
theorem grade_schur_nine {I : Type*} [Fintype I] [DecidableEq I] {N M : ℕ}
    (A : Matrix I I ℝ) (hA : A.PosSemidef) (grade : I → Fin N × Fin M)
    {L : ℝ} (hL : 0 ≤ L)
    (hzero : ∀ a b, ¬pairEvenStep a b →
      gradeProjection grade a * A * gradeProjection grade b = 0)
    (hdiag : ∀ a, ‖gradeProjection grade a * A * gradeProjection grade a‖ ≤ L) :
    ‖A‖ ≤ 9 * L := by
  simpa only [Nat.cast_ofNat] using grade_schur A hA grade pairEvenStep pairEvenStep_symm
    9 pairEvenStep_neighbor_count hL hzero hdiag

end NineNeighbors

end

end SRHT.GradeCompression
