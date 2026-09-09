import SparseFockFormal.LightBandsConcrete
import SparseFockFormal.HeavyBandsConcrete
import SparseFockFormal.DirectionalNormalized
import SparseFockFormal.BandCoefficientBounds
import SparseFockFormal.BandEnvelope
import Mathlib.Tactic

/-!
# Concrete mixed light--heavy band estimates

This module realizes the mixed bands as literal products through the
row-indexed scalar Fock space.  Same-site terms are proved to vanish in the
finite pattern matrices, so the products agree exactly with the physical
distinct-site word sums.
-/

namespace SparseFock.MixedBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands
  BandInventory NamedBands FiniteHilbert ConcreteLadder
  HeavyBandsConcrete LightBandsConcrete DirectionalConcrete
  DirectionalNormalized BandCoefficientBounds BandEnvelope
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1000000

variable {d m n : ℕ}

/-- The lifted same-site product `P† R` vanishes in literal pattern
coordinates. -/
theorem pDagAt_mul_rUpAt_self (r : Fin m) (i : Fin n) :
    LightSectorConcrete.pDagAt r i * rUpAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [LightBandsConcrete.pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single (setSite out (r, i) .zero)]
    · simp [rUpAt_apply, setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [LightBandsConcrete.pDagAt_apply, hout]

/-- The lifted same-site product `P† R†` also vanishes. -/
theorem pDagAt_mul_rDownAt_self (r : Fin m) (i : Fin n) :
    LightSectorConcrete.pDagAt r i * rDownAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [LightBandsConcrete.pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single (setSite out (r, i) .zero)]
    · simp [rDownAt_apply, setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [LightBandsConcrete.pDagAt_apply, hout]

theorem pDagAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    LightSectorConcrete.pDagAt r i * rUpAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rUp) := by
  simpa [LightSectorConcrete.pDagAt, rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rPromote

theorem pDagAt_mul_rDownAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    LightSectorConcrete.pDagAt r i * rDownAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rDown) := by
  simpa [LightSectorConcrete.pDagAt, rDownAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rDemote

theorem COne_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.AUpOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.AUpOne, orderedWordTerm, externalTensor,
    ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u j inp.1 * rUpAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rUpAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .rUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rUpAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

theorem COne_mul_AUpOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.AUpOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.AUpOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u i inp.1 * rUpAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rUpAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rUpAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

theorem COne_mul_ADownOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.ADownOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.ADownOne, orderedWordTerm, externalTensor,
    ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u j inp.1 * rDownAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rDownAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .rDown) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rDownAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

theorem COne_mul_ADownOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.ADownOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.ADownOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u i inp.1 * rDownAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rDownAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rDownAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Exact row-local mixed raising factorization; the diagonal terms vanish. -/
theorem CMatrix_mul_AUpMatrix (F : Frame n d) (r : Fin m) :
    LightSectorConcrete.CMatrix F r * HeavyBandsConcrete.AUpMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rUp) := by
  classical
  rw [LightBandsConcrete.CMatrix_eq_sum_COne,
    HeavyBandsConcrete.AUpMatrix_eq_sum_one, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [COne_mul_AUpOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_AUpOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- Exact row-local grade-preserving mixed factorization. -/
theorem CMatrix_mul_ADownMatrix (F : Frame n d) (r : Fin m) :
    LightSectorConcrete.CMatrix F r * HeavyBandsConcrete.ADownMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rDown) := by
  classical
  rw [LightBandsConcrete.CMatrix_eq_sum_COne,
    HeavyBandsConcrete.ADownMatrix_eq_sum_one, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [COne_mul_ADownOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_ADownOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The physical `X₊` word sum is literally `CStack * AUpStack`. -/
theorem Xplus_eq_CStack_mul_AUpStack (F : Frame n d) :
    Xplus m (DirectionalConcrete.frameRows F) =
      LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [Xplus, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, LightBandsConcrete.CStack,
    HeavyBandsConcrete.AUpStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_AUpMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- The physical `X₀` word sum is literally `CStack * ADownStack`. -/
theorem Xzero_eq_CStack_mul_ADownStack (F : Frame n d) :
    Xzero m (DirectionalConcrete.frameRows F) =
      LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.ADownStack (m := m) F := by
  classical
  ext out inp
  simp only [Xzero, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, LightBandsConcrete.CStack,
    HeavyBandsConcrete.ADownStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_ADownMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- Fully projected typed factorization of `X₊` on input grade `nu`. -/
theorem Xplus_grade_factor (F : Frame n d) (nu : ℕ) :
    Xplus m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu =
      (gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (HeavyBandsConcrete.AUpStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) := by
  rw [Xplus_eq_CStack_mul_AUpStack]
  have hins := HeavyBandsConcrete.rowProjection_AUpStack_gradeProjection
    (m := m) F nu
  have hout := LightBandsConcrete.gradeProjection_CStack_rowProjection
    (m := m) F (nu + 1)
  have hout' :
      gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) =
        LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) := by
    convert hout using 1
  calc
    (LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.AUpStack (m := m) F) * gradeProjection (d := d) nu =
      LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [Matrix.mul_assoc]
    _ = LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) *
          HeavyBandsConcrete.AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [hins]
    _ = (LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (HeavyBandsConcrete.AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hout']

/-- Fully projected typed factorization of `X₀` on positive input grade. -/
theorem Xzero_grade_factor_add_one (F : Frame n d) (k : ℕ) :
    Xzero m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) (k + 1) =
      (gradeProjection (d := d) (m := m) (n := n) (k + 1) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k) *
        (HeavyBandsConcrete.ADownStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) (k + 1)) := by
  rw [Xzero_eq_CStack_mul_ADownStack]
  have hins := HeavyBandsConcrete.rowProjection_ADownStack_output
    (m := m) F k
  have hout := LightBandsConcrete.gradeProjection_CStack_rowProjection
    (m := m) F k
  calc
    (LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.ADownStack (m := m) F) *
          gradeProjection (d := d) (k + 1) =
      LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.ADownStack (m := m) F *
          gradeProjection (d := d) (k + 1)) := by
      rw [Matrix.mul_assoc]
    _ = LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k *
          HeavyBandsConcrete.ADownStack (m := m) F *
            gradeProjection (d := d) (k + 1)) := by
      rw [hins]
    _ = (LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k) *
        (HeavyBandsConcrete.ADownStack (m := m) F *
          gradeProjection (d := d) (k + 1)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hout]

theorem Xzero_gradeProjection_zero (F : Frame n d) :
    Xzero m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  rw [Xzero_eq_CStack_mul_ADownStack, Matrix.mul_assoc,
    HeavyBandsConcrete.ADownStack_gradeProjection_zero, Matrix.mul_zero]

@[simp] theorem transpose_Xplus (u : Fin n → Fin d → ℝ) :
    (Xplus m u).transpose = XplusAdj m u := by
  simpa [Xplus, XplusAdj, NamedBands.wordSum, Word.orderedAdjoint,
    Leg.adjoint] using
    DirectionalConcrete.transpose_physicalWordSum (m := m) u (.pUp, .rUp)

@[simp] theorem transpose_XplusAdj (u : Fin n → Fin d → ℝ) :
    (XplusAdj m u).transpose = Xplus m u := by
  rw [← transpose_Xplus (m := m) u, Matrix.transpose_transpose]

@[simp] theorem transpose_Xzero (u : Fin n → Fin d → ℝ) :
    (Xzero m u).transpose = XzeroAdj m u := by
  simpa [Xzero, XzeroAdj, NamedBands.wordSum, Word.orderedAdjoint,
    Leg.adjoint] using
    DirectionalConcrete.transpose_physicalWordSum (m := m) u (.pUp, .rDown)

@[simp] theorem transpose_XzeroAdj (u : Fin n → Fin d → ℝ) :
    (XzeroAdj m u).transpose = Xzero m u := by
  rw [← transpose_Xzero (m := m) u, Matrix.transpose_transpose]

theorem Xplus_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 2
      (Xplus m (DirectionalConcrete.frameRows F)) := by
  simpa [Xplus, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.pUp, .rUp)

theorem Xzero_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0
      (Xzero m (DirectionalConcrete.frameRows F)) := by
  simpa [Xzero, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.pUp, .rDown)

theorem XplusAdj_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous (-2)
      (XplusAdj m (DirectionalConcrete.frameRows F)) := by
  simpa [XplusAdj, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.rDown, .pDown)

theorem XzeroAdj_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0
      (XzeroAdj m (DirectionalConcrete.frameRows F)) := by
  simpa [XzeroAdj, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.rUp, .pDown)

/-- Exact L2-norm scaling for the nested normalized mixed coefficient. -/
theorem norm_normalized_mixed_term_eq {s b : ℕ}
    (A : FullOp d m n) (P : FullOp d m n) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • A)) * P‖ =
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * ‖A * P‖ := by
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
      0 ≤ (1 : ℝ) / (((s * b : ℕ) : ℝ))),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Raw restricted norm of the concrete `X₊` factorization. -/
theorem norm_Xplus_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Xplus m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
  have hC := LightBandsConcrete.CStack_restricted_norm (m := m) F (nu + 1)
  have hC' :
      ‖gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)‖ ≤
        Real.sqrt ((d : ℝ) + (nu + 1 : ℕ)) := by
    convert hC using 1
  calc
    _ = ‖(gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
            LightBandsConcrete.CStack (m := m) F *
            HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
          (HeavyBandsConcrete.AUpStack (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu)‖ :=
      congrArg norm (Xplus_grade_factor (m := m) F nu)
    _ ≤
        ‖gradeProjection (d := d) (nu + 2) *
            LightBandsConcrete.CStack (m := m) F *
            HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)‖ *
          ‖HeavyBandsConcrete.AUpStack (m := m) F *
            gradeProjection (d := d) nu‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((d : ℝ) + (nu + 1 : ℕ)) * Real.sqrt nu := by
      exact mul_le_mul
        hC'
        (HeavyBandsConcrete.AUpStack_gradeProjection_norm (m := m) F nu)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg nu)]
      push_cast
      ring

/-- Raw restricted norm of the concrete grade-preserving `X₀` band. -/
theorem norm_Xzero_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Xzero m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  rcases nu with (_ | k)
  · rw [Xzero_gradeProjection_zero]
    simp
  · have hC := LightBandsConcrete.CStack_restricted_norm (m := m) F k
    have hC' :
        ‖gradeProjection (d := d) (m := m) (n := n) (k + 1) *
            LightBandsConcrete.CStack (m := m) F *
            HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k‖ ≤
          Real.sqrt ((d : ℝ) + ((k + 1 : ℕ) : ℝ)) := by
      calc
        _ ≤ Real.sqrt ((d : ℝ) + (k : ℝ)) := hC
        _ ≤ Real.sqrt ((d : ℝ) + ((k + 1 : ℕ) : ℝ)) := by
          apply Real.sqrt_le_sqrt
          norm_num
    calc
      _ = ‖(gradeProjection (d := d) (m := m) (n := n) (k + 1) *
              LightBandsConcrete.CStack (m := m) F *
              HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k) *
            (HeavyBandsConcrete.ADownStack (m := m) F *
              gradeProjection (d := d) (m := m) (n := n) (k + 1))‖ :=
        congrArg norm (Xzero_grade_factor_add_one (m := m) F k)
      _ ≤
          ‖gradeProjection (d := d) (k + 1) *
              LightBandsConcrete.CStack (m := m) F *
              HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k‖ *
            ‖HeavyBandsConcrete.ADownStack (m := m) F *
              gradeProjection (d := d) (k + 1)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ Real.sqrt ((d : ℝ) + ((k + 1 : ℕ) : ℝ)) *
          Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul hC'
          (HeavyBandsConcrete.ADownStack_gradeProjection_norm
            (m := m) F (k + 1))
          (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (((k + 1 : ℕ) : ℝ) *
          ((d : ℝ) + ((k + 1 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg (k + 1))]
        ring

/-- Exact shifted adjoint estimate for `X₊†`. -/
theorem norm_XplusAdj_restricted_add_two_le (F : Frame n d) (k : ℕ) :
    ‖XplusAdj m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) (k + 2)‖ ≤
      Real.sqrt ((k : ℝ) * ((d : ℝ) + k + 1)) := by
  calc
    _ = ‖(XplusAdj m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) (k + 2)).transpose‖ := by
      exact (DirectionalNormalized.l2_norm_transpose _).symm
    _ = ‖gradeProjection (d := d) (k + 2) *
          Xplus m (DirectionalConcrete.frameRows F)‖ := by
      rw [Matrix.transpose_mul, transpose_XplusAdj, gradeProjection_transpose]
    _ = ‖Xplus m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) k‖ := by
      rw [DirectionalNormalized.gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Xplus_homogeneous (m := m) F) (k + 2) k (by norm_num)]
    _ ≤ _ := norm_Xplus_restricted_le (m := m) F k

theorem XplusAdj_gradeProjection_zero (F : Frame n d) :
    XplusAdj m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  apply FiniteHilbert.input_grade_vanishes_of_no_output
    (XplusAdj_homogeneous (m := m) F) 0
  intro mu
  omega

theorem XplusAdj_gradeProjection_one (F : Frame n d) :
    XplusAdj m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 1 = 0 := by
  apply FiniteHilbert.input_grade_vanishes_of_no_output
    (XplusAdj_homogeneous (m := m) F) 1
  intro mu
  omega

/-- Uniform same-grade form of the transpose mixed raising bound. -/
theorem norm_XplusAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖XplusAdj m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
  rcases nu with (_ | _ | k)
  · rw [XplusAdj_gradeProjection_zero]
    simp
  · rw [XplusAdj_gradeProjection_one]
    simp
  · calc
      _ ≤ Real.sqrt ((k : ℝ) * ((d : ℝ) + k + 1)) :=
        norm_XplusAdj_restricted_add_two_le (m := m) F k
      _ ≤ Real.sqrt (((k + 2 : ℕ) : ℝ) *
          ((d : ℝ) + ((k + 2 : ℕ) : ℝ) + 1)) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d),
          (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The grade-preserving adjoint has exactly the same restricted norm. -/
theorem norm_XzeroAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖XzeroAdj m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  calc
    _ = ‖(XzeroAdj m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) nu).transpose‖ := by
      exact (DirectionalNormalized.l2_norm_transpose _).symm
    _ = ‖gradeProjection (d := d) nu *
          Xzero m (DirectionalConcrete.frameRows F)‖ := by
      rw [Matrix.transpose_mul, transpose_XzeroAdj, gradeProjection_transpose]
    _ = ‖Xzero m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) nu‖ := by
      rw [DirectionalNormalized.gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Xzero_homogeneous (m := m) F) nu nu (by norm_num)]
    _ ≤ _ := norm_Xzero_restricted_le (m := m) F nu

theorem norm_normalized_Xplus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          Xplus (s * b) (DirectionalConcrete.frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      (1 / 2 : ℝ) *
        (BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
  rw [norm_normalized_mixed_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖Xplus (s * b) (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (norm_Xplus_restricted_le (m := s * b) F nu)
        BandCoefficientBounds.rho_div_stack_nonneg
    _ ≤ _ := by
      simpa [BandEnvelope.bTerm] using
        BandCoefficientBounds.mixed_plus_absorb
          (d := d) (nu := nu) hs hb

theorem norm_normalized_XplusAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          XplusAdj (s * b) (DirectionalConcrete.frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      (1 / 2 : ℝ) *
        (BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
  rw [norm_normalized_mixed_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖XplusAdj (s * b) (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (norm_XplusAdj_restricted_le (m := s * b) F nu)
        BandCoefficientBounds.rho_div_stack_nonneg
    _ ≤ _ := by
      simpa [BandEnvelope.bTerm] using
        BandCoefficientBounds.mixed_plus_absorb
          (d := d) (nu := nu) hs hb

theorem norm_normalized_Xzero_restricted_le (F : Frame n d)
    (s b nu : ℕ) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          Xzero (s * b) (DirectionalConcrete.frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  rw [norm_normalized_mixed_term_eq]
  exact mul_le_mul_of_nonneg_left
    (norm_Xzero_restricted_le (m := s * b) F nu)
    BandCoefficientBounds.rho_div_stack_nonneg

theorem norm_normalized_XzeroAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          XzeroAdj (s * b) (DirectionalConcrete.frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  rw [norm_normalized_mixed_term_eq]
  exact mul_le_mul_of_nonneg_left
    (norm_XzeroAdj_restricted_le (m := s * b) F nu)
    BandCoefficientBounds.rho_div_stack_nonneg

/-- The two normalized `X₀` orientations satisfy the exact TeX allowance. -/
theorem norm_normalized_Xzero_pair_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xzero (s * b) (DirectionalConcrete.frameRows F) +
            XzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
        gradeProjection (d := d) nu‖ ≤
      ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (DirectionalConcrete.frameRows F) +
              XzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xzero (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XzeroAdj (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xzero (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XzeroAdj (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ 2 * (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu))) := by
      have h₁ := norm_normalized_Xzero_restricted_le F s b nu
      have h₂ := norm_normalized_XzeroAdj_restricted_le F s b nu
      linarith
    _ ≤ _ := BandCoefficientBounds.mixed_zero_absorb hs hb

private theorem nu_div_s_le_cTerm {s nu : ℕ} (hs : 0 < s) :
    (nu : ℝ) / s ≤ BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  unfold BandEnvelope.cTerm
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Equation (mixed-plus), before replacing `nu/s` by the uniform envelope
term `(nu+1)/s`. -/
theorem norm_normalized_mixed_plus_restricted_le_tex (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xplus (s * b) (DirectionalConcrete.frameRows F) +
            Yplus (s * b) (DirectionalConcrete.frameRows F)))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * ((nu : ℝ) / s) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xplus (s * b) (DirectionalConcrete.frameRows F) +
              Yplus (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xplus (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Yplus (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  have hX := norm_normalized_Xplus_restricted_le F s b nu hs hb
  have hY := DirectionalNormalized.norm_normalized_Yplus_restricted_le
    F s b nu hs hb
  have hB : 0 ≤ BandEnvelope.bTerm (d : ℝ) (nu : ℝ)
      (((s * b : ℕ) : ℝ)) :=
    BandEnvelope.bTerm_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xplus (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Yplus (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
            (nu : ℝ) / s) + (nu : ℝ) / s := add_le_add hX hY
    _ ≤ BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * ((nu : ℝ) / s) := by linarith

/-- Assembly-shaped normalized mixed `+2` estimate. -/
theorem norm_normalized_mixed_plus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xplus (s * b) (DirectionalConcrete.frameRows F) +
            Yplus (s * b) (DirectionalConcrete.frameRows F)))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  calc
    _ ≤ BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * ((nu : ℝ) / s) :=
      norm_normalized_mixed_plus_restricted_le_tex F s b nu hs hb
    _ ≤ _ := by
      have h := nu_div_s_le_cTerm (nu := nu) hs
      nlinarith

/-- Assembly-shaped normalized mixed `-2` estimate. -/
theorem norm_normalized_mixed_minus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (XplusAdj (s * b) (DirectionalConcrete.frameRows F) +
            YplusAdj (s * b) (DirectionalConcrete.frameRows F)))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (XplusAdj (s * b) (DirectionalConcrete.frameRows F) +
              YplusAdj (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XplusAdj (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            YplusAdj (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  have hX := norm_normalized_XplusAdj_restricted_le F s b nu hs hb
  have hY := DirectionalNormalized.norm_normalized_YplusAdj_restricted_le
    F s b nu hs hb
  have hB : 0 ≤ BandEnvelope.bTerm (d : ℝ) (nu : ℝ)
      (((s * b : ℕ) : ℝ)) :=
    BandEnvelope.bTerm_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)
  have hnu := nu_div_s_le_cTerm (nu := nu) hs
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XplusAdj (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            YplusAdj (s * b) (DirectionalConcrete.frameRows F))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
            (nu : ℝ) / s) + (nu : ℝ) / s := add_le_add hX hY
    _ ≤ _ := by nlinarith

/-- Equation (mixed-zero), before the uniform-envelope relaxation. -/
theorem norm_normalized_mixed_zero_restricted_le_tex (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xzero (s * b) (DirectionalConcrete.frameRows F) +
            XzeroAdj (s * b) (DirectionalConcrete.frameRows F) +
            Yzero (s * b) (DirectionalConcrete.frameRows F) +
            YzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
        gradeProjection (d := d) nu‖ ≤
      ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) +
        (1 + Real.sqrt 2) * ((nu : ℝ) / s) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (DirectionalConcrete.frameRows F) +
              XzeroAdj (s * b) (DirectionalConcrete.frameRows F) +
              Yzero (s * b) (DirectionalConcrete.frameRows F) +
              YzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (DirectionalConcrete.frameRows F) +
              XzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Yzero (s * b) (DirectionalConcrete.frameRows F) +
              YzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
    abel
  rw [hsplit]
  have hX := norm_normalized_Xzero_pair_restricted_le F s b nu hs hb
  have hY := DirectionalNormalized.norm_normalized_Yzero_pair_restricted_le
    F s b nu hs hb
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (DirectionalConcrete.frameRows F) +
              XzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Yzero (s * b) (DirectionalConcrete.frameRows F) +
              YzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ (((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s) +
        Real.sqrt 2 * ((nu : ℝ) / s) := add_le_add hX hY
    _ = _ := by ring

/-- Assembly-shaped normalized four-orientation grade-zero mixed bound. -/
theorem norm_normalized_mixed_zero_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xzero (s * b) (DirectionalConcrete.frameRows F) +
            XzeroAdj (s * b) (DirectionalConcrete.frameRows F) +
            Yzero (s * b) (DirectionalConcrete.frameRows F) +
            YzeroAdj (s * b) (DirectionalConcrete.frameRows F)))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (1 + Real.sqrt 2) * BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  calc
    _ ≤ ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) +
        (1 + Real.sqrt 2) * ((nu : ℝ) / s) :=
      norm_normalized_mixed_zero_restricted_le_tex F s b nu hs hb
    _ ≤ _ := by
      have hM : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
      have hfirst :
          ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) ≤
            BandEnvelope.bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) := by
        unfold BandEnvelope.bTerm
        exact div_le_div_of_nonneg_right (by linarith) hM.le
      have hnu := nu_div_s_le_cTerm (nu := nu) hs
      have hsqrt : 0 ≤ 1 + Real.sqrt 2 := by positivity
      exact add_le_add hfirst (mul_le_mul_of_nonneg_left hnu hsqrt)

end

end SparseFock.MixedBandsConcrete
