import SparseFockFormal.LightSectorConcrete
import SparseFockFormal.DirectionalNormalized
import SparseFockFormal.HeavyBandsConcrete
import SparseFockFormal.ConcreteLadder
import SparseFockFormal.TypedBlockCS
import SparseFockFormal.BandEnvelope
import Mathlib.Tactic

/-!
# Concrete light-light bands

This file realizes the row synthesis/analysis operators used in the light
sector as literal finite matrices.  In particular, it records the exact
factorizations behind the light raising and grade-preserving bands; all norms
below are the Euclidean `L2` matrix operator norm.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace SparseFock.LightBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
open NamedBands ConcreteLadder DirectionalConcrete DirectionalNormalized
open LightSectorConcrete
open BandInventory GlobalBands

noncomputable section

variable {d m n : ℕ}

/-- The common middle space: one scalar Fock copy for every physical row. -/
abbrev RowFock (m n : ℕ) := HeavyBandsConcrete.RowFock m n

/-- One creation-synthesis summand `u_i ⊗ P†_(r,i)`. -/
def COne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out inp ↦ F.u i out.1 * pDagAt r i out.2 inp

/-- One creation-analysis summand.  Its external index is on the input side. -/
def cOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ F.u i inp.1 * pDagAt r i out inp.2

/-- The row-local creation-analysis operator `c_r`. -/
def cMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  ∑ i, cOne F r i

/-- Row-stacked creation synthesis.  This is reusable in the mixed bands. -/
def CStack (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (RowFock m n) ℝ :=
  fun out inp ↦ CMatrix F inp.1 out inp.2

/-- Row-stacked creation analysis. -/
def CreateAnalysisStack (F : Frame n d) :
    Matrix (RowFock m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ cMatrix F out.1 out.2 inp

@[simp] theorem CMatrix_eq_sum_COne (F : Frame n d) (r : Fin m) :
    CMatrix F r = ∑ i, COne F r i := by
  ext out inp
  simp [CMatrix, COne, Matrix.sum_apply]

@[simp] theorem cMatrix_eq_sum_cOne (F : Frame n d) (r : Fin m) :
    cMatrix F r = ∑ i, cOne F r i := by
  rfl

/-- The stacked synthesis cogram is exactly the concrete shared-leg operator. -/
theorem CStack_mul_transpose (F : Frame n d) :
    CStack (m := m) F * (CStack (m := m) F).transpose = ghat F := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, CStack, Matrix.transpose_apply, ghat,
    Matrix.sum_apply]
  rw [Fintype.sum_prod_type]

@[simp] theorem CStack_transpose_apply (F : Frame n d)
    (out : RowFock m n) (inp : Fin d × Pattern m n) :
    (CStack F).transpose out inp = (CMatrix F out.1).transpose out.2 inp := by
  rfl

/-- The row-local creation synthesis is grade `+1`. -/
theorem CMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Fin d × Pattern m n} {inp : Pattern m n}
    (hentry : CMatrix F r out inp ≠ 0) :
    (out.2.grade : ℤ) = (inp.grade : ℤ) + 1 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : pDagAt r i out.2 inp ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous pCreate_homogeneous (r, i) hk
  simpa [pDagAt, gradeZ_eq_cast_grade] using hh

/-- The row-local creation analysis is also grade `+1`. -/
theorem cMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Pattern m n} {inp : Fin d × Pattern m n}
    (hentry : cMatrix F r out inp ≠ 0) :
    (out.grade : ℤ) = (inp.2.grade : ℤ) + 1 := by
  classical
  rw [cMatrix_eq_sum_cOne] at hentry
  simp only [Matrix.sum_apply, cOne] at hentry
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : pDagAt r i out inp.2 ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous pCreate_homogeneous (r, i) hk
  simpa [cOne, pDagAt, gradeZ_eq_cast_grade] using hh

theorem pDagAt_apply (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) :
    pDagAt r i out inp =
      if out (r, i) = .one ∧
          inp = HeavyBandsConcrete.setSite out (r, i) .zero then 1 else 0 := by
  simpa [pDagAt, pCreate] using
    HeavyBandsConcrete.siteKernel_ketBra_apply
      (m := m) (n := n) (r, i) .one .zero out inp

theorem pDagAt_sq_zero (r : Fin m) (i : Fin n) :
    pDagAt r i * pDagAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single (HeavyBandsConcrete.setSite out (r, i) .zero)]
    · simp [HeavyBandsConcrete.setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [pDagAt_apply, hout]

theorem pDagAt_mul_pDagAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * pDagAt r j =
      wordKernel (r, i) (r, j) (.pUp, .pUp) := by
  simpa [pDagAt, wordKernel, BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate pCreate

theorem COne_mul_cOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * cOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .pUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, cOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * pDagAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p * pDagAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .pUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_pDagAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

theorem COne_mul_cOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    COne F r i * cOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, cOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u i inp.1 * pDagAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p * pDagAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_sq_zero r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Exact row-local factorization: the diagonal terms vanish by `P†²=0`. -/
theorem CMatrix_mul_cMatrix (F : Frame n d) (r : Fin m) :
    CMatrix F r * cMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .pUp) := by
  classical
  rw [CMatrix_eq_sum_COne, cMatrix_eq_sum_cOne, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [COne_mul_cOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_cOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The named light raising band is the row synthesis times row analysis. -/
theorem Lplus_eq_CStack_mul_CreateAnalysisStack (F : Frame n d) :
    Lplus m (DirectionalConcrete.frameRows F) =
      CStack (m := m) F * CreateAnalysisStack (m := m) F := by
  classical
  ext out inp
  simp only [Lplus, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, CStack, CreateAnalysisStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg
    (fun M : FullOp d m n ↦ M out inp) (CMatrix_mul_cMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- Fixing the input at grade `nu` forces the creation-analysis stack to land
in row grade `nu+1`. -/
theorem rowProjection_CreateAnalysisStack_gradeProjection
    (F : Frame n d) (nu : ℕ) :
    HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) *
        CreateAnalysisStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu =
      CreateAnalysisStack (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu := by
  classical
  ext out inp
  simp only [HeavyBandsConcrete.rowGradeProjection, gradeProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : CreateAnalysisStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := cMatrix_grade_relation F out.1 hentry
      have hout : out.2.grade = nu + 1 := by
        rw [hin] at hrel
        exact_mod_cast hrel
      simp [hin, hout]
  · simp [hin]

/-- On row grade `mu`, the synthesis stack lands at full grade `mu+1`. -/
theorem gradeProjection_CStack_rowProjection (F : Frame n d) (mu : ℕ) :
    gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu =
      CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu := by
  classical
  ext out inp
  simp only [HeavyBandsConcrete.rowGradeProjection, gradeProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = mu
  · by_cases hentry : CStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := CMatrix_grade_relation F inp.1 hentry
      have hout : out.2.grade = mu + 1 := by
        rw [hin] at hrel
        exact_mod_cast hrel
      simp [hin, hout]
  · simp [hin]

/-- Fully typed projected factorization of the light `+2` band. -/
theorem Lplus_grade_factor (F : Frame n d) (nu : ℕ) :
    Lplus m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu =
      (gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (CreateAnalysisStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) := by
  rw [Lplus_eq_CStack_mul_CreateAnalysisStack]
  have hins := rowProjection_CreateAnalysisStack_gradeProjection
    (m := m) F nu
  have hout := gradeProjection_CStack_rowProjection (m := m) F (nu + 1)
  calc
    (CStack (m := m) F * CreateAnalysisStack (m := m) F) *
        gradeProjection (d := d) (m := m) (n := n) nu =
        CStack (m := m) F *
          (CreateAnalysisStack (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu) := by
      rw [Matrix.mul_assoc]
    _ = CStack (m := m) F *
        (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) *
          CreateAnalysisStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [hins]
    _ = (CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (CreateAnalysisStack (m := m) F * gradeProjection (d := d) nu) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hout]

@[simp] theorem pDagAt_transpose (r : Fin m) (i : Fin n) :
    (pDagAt r i).transpose = pAt r i := by
  simp [pDagAt, pAt, transpose_siteKernel]

theorem pAt_mul_pDagAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pAt r i * pDagAt r j =
      wordKernel (r, i) (r, j) (.pDown, .pUp) := by
  simpa [pAt, pDagAt, wordKernel, BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pDestroy pCreate

theorem cOne_transpose_mul_cOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    (cOne F r i).transpose * cOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pDown, .pUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i p out.2) *
        (F.u j inp.1 * pDagAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, (pDagAt r i).transpose out.2 p * pDagAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Matrix.transpose_apply]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pDown, .pUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pAt_mul_pDagAt_of_ne r hij)
      rw [pDagAt_transpose]
      change (F.u i out.1 * F.u j inp.1) *
        ((pAt r i * pDagAt r j) out.2 inp.2) = _
      rw [h]

/-- The same-site, fresh-site diagonal part of one analysis Gram. -/
def D0Row (F : Frame n d) (r : Fin m) : FullOp d m n :=
  ∑ i, (cOne F r i).transpose * cOne F r i

/-- The global fresh-site diagonal Gram term. -/
def D0 (F : Frame n d) : FullOp d m n :=
  ∑ r, D0Row F r

theorem cMatrix_transpose_mul_cMatrix (F : Frame n d) (r : Fin m) :
    (cMatrix F r).transpose * cMatrix F r =
      D0Row F r +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (DirectionalConcrete.frameRows F) r i j
            (.pDown, .pUp) := by
  classical
  rw [cMatrix_eq_sum_cOne, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  rw [D0Row]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, (cOne F r i).transpose * cOne F r j) =
        (∑ j ∈ Finset.univ.erase i,
          (cOne F r i).transpose * cOne F r j) +
          (cOne F r i).transpose * cOne F r i := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = (cOne F r i).transpose * cOne F r i +
        ∑ j ∈ Finset.univ.erase i,
          (cOne F r i).transpose * cOne F r j := add_comm _ _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact cOne_transpose_mul_cOne_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The full creation-analysis Gram is the fresh diagonal plus the exact
light transpose hop `H'`. -/
theorem CreateAnalysisStack_transpose_mul_self (F : Frame n d) :
    (CreateAnalysisStack (m := m) F).transpose * CreateAnalysisStack F =
      D0 F + Hprime m (DirectionalConcrete.frameRows F) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, CreateAnalysisStack]
  rw [Fintype.sum_prod_type]
  simp only [D0, Matrix.sum_apply, Hprime, NamedBands.wordSum,
    physicalWordSum, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (cMatrix_transpose_mul_cMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h

/-- The same-site creation column has exactly the fresh-site projection as
its scalar Gram. -/
theorem pDagAt_column_inner (r : Fin m) (i : Fin n)
    (a b : Pattern m n) :
    (∑ p, pDagAt r i p a * pDagAt r i p b) =
      if a = b ∧ a (r, i) = .zero then 1 else 0 := by
  classical
  let s : Site m n := (r, i)
  let marked := HeavyBandsConcrete.setSite a s .one
  by_cases ha : a s = .zero
  · have hrestore : HeavyBandsConcrete.setSite marked s .zero = a := by
      simpa [marked, s] using
        HeavyBandsConcrete.setSite_restore (b := .one) a s ha
    rw [Finset.sum_eq_single marked]
    · simp only [pDagAt_apply]
      simp [marked, s, hrestore, ha, eq_comm]
    · intro p _ hpne
      by_cases hp : p s = .one
      · by_cases heq : a = HeavyBandsConcrete.setSite p s .zero
        · have hpmark : p = marked := by
            calc
              p = HeavyBandsConcrete.setSite
                    (HeavyBandsConcrete.setSite p s .zero) s .one := by
                symm
                exact HeavyBandsConcrete.setSite_restore (b := .zero) p s hp
              _ = marked := by rw [← heq]
          exact (hpne hpmark).elim
        · simp [pDagAt_apply, s, hp, heq]
      · simp [pDagAt_apply, s, hp]
    · simp
  · have hzero (p : Pattern m n) : pDagAt r i p a = 0 := by
      rw [pDagAt_apply]
      by_cases hp : p s = .one
      · by_cases heq : a = HeavyBandsConcrete.setSite p s .zero
        · exfalso
          apply ha
          rw [heq]
          exact HeavyBandsConcrete.setSite_apply_self _ _ _
        · simp [s, hp, heq]
      · simp [s, hp]
    have hane : a (r, i) ≠ .zero := by simpa [s] using ha
    simp [hzero, hane]

/-- Entrywise form of the fresh-site diagonal Gram: on each Fock pattern it
is precisely the partial frame operator over the currently fresh columns. -/
theorem D0Row_apply (F : Frame n d) (r : Fin m)
    (out inp : Fin d × Pattern m n) :
    D0Row F r out inp =
      if out.2 = inp.2 then
        partialFrameOperator F (out.2.freshInRow r) out.1 inp.1 else 0 := by
  classical
  simp only [D0Row, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply, cOne]
  calc
    (∑ i, ∑ p,
        (F.u i out.1 * pDagAt r i p out.2) *
          (F.u i inp.1 * pDagAt r i p inp.2)) =
        ∑ i, (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i p out.2 * pDagAt r i p inp.2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = ∑ i, (F.u i out.1 * F.u i inp.1) *
        (if out.2 = inp.2 ∧ out.2 (r, i) = .zero then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pDagAt_column_inner]
    _ = _ := by
      by_cases hp : out.2 = inp.2
      · simp only [hp, true_and, if_true]
        simp [partialFrameOperator, Pattern.freshInRow, Finset.sum_filter]
      · simp [hp]

theorem D0Row_fullFiber (F : Frame n d) (r : Fin m)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fullFiber (Matrix.mulVec (D0Row F r) x) p =
      applyMatrix (partialFrameOperator F (p.freshInRow r)) (fullFiber x p) := by
  classical
  ext k
  simp only [fullFiber, Matrix.mulVec, dotProduct, D0Row_apply, applyMatrix,
    PiLp.toLp_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  simp

/-- One row's fresh-site diagonal is a Euclidean contraction. -/
theorem D0Row_norm_le_one (F : Frame n d) (r : Fin m) :
    ‖D0Row F r‖ ≤ 1 := by
  apply FiniteHilbert.norm_le_of_normSq_mulVec_le (by norm_num)
  intro x
  rw [DirectionalConcrete.full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (D0Row F r) x) p)) =
        ∑ p, ParsevalFrame.normSq
          (applyMatrix (partialFrameOperator F (p.freshInRow r))
            (fullFiber x p)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [D0Row_fullFiber]
    _ ≤ ∑ p, ParsevalFrame.normSq (fullFiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      exact partialFrameOperator_contraction F (p.freshInRow r) (fullFiber x p)
    _ = 1 ^ 2 * FiniteHilbert.normSq x := by
      rw [DirectionalConcrete.full_normSq_eq_sum_fiber]
      ring

/-- Summing the row contractions gives the exact paper bound `D₀ ≼ m I`. -/
theorem D0_norm_le (F : Frame n d) :
    ‖D0 (m := m) F‖ ≤ (m : ℝ) := by
  rw [D0]
  calc
    ‖∑ r, D0Row F r‖ ≤ ∑ r, ‖D0Row F r‖ := norm_sum_le _ _
    _ ≤ ∑ _r : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      exact D0Row_norm_le_one F r
    _ = (m : ℝ) := by simp

/-- Finite-matrix specialization of typed block Cauchy--Schwarz.  The middle
index type is genuine and may differ from both endpoint types. -/
theorem matrix_typed_block_cs
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (B : Matrix K J ℝ) (A : Matrix J I ℝ) :
    ‖B * A‖ ^ 2 ≤ ‖A.transpose * A‖ * ‖B * B.transpose‖ := by
  have hmul : ‖B * A‖ ≤ ‖B‖ * ‖A‖ := Matrix.l2_opNorm_mul B A
  have hAconj : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hBconj : B.transpose.conjTranspose = B := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hAgram : ‖A.transpose * A‖ = ‖A‖ * ‖A‖ := by
    rw [← hAconj, Matrix.l2_opNorm_conjTranspose_mul_self]
  have hBcogram : ‖B * B.transpose‖ = ‖B‖ * ‖B‖ := by
    calc
      ‖B * B.transpose‖ =
          ‖B.transpose.conjTranspose * B.transpose‖ := by rw [hBconj]
      _ = ‖B.transpose‖ * ‖B.transpose‖ :=
        Matrix.l2_opNorm_conjTranspose_mul_self B.transpose
      _ = ‖B‖ * ‖B‖ := by
        rw [HeavyBandsConcrete.l2_opNorm_transpose_real]
  calc
    ‖B * A‖ ^ 2 ≤ (‖B‖ * ‖A‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hmul 2
    _ = (‖A‖ * ‖A‖) * (‖B‖ * ‖B‖) := by ring
    _ = ‖A.transpose * A‖ * ‖B * B.transpose‖ := by rw [hAgram, hBcogram]

theorem CreateAnalysisStack_restricted_gram (F : Frame n d) (nu : ℕ) :
    (CreateAnalysisStack (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu).transpose *
      (CreateAnalysisStack (m := m) F * gradeProjection (d := d) nu) =
        gradeProjection (d := d) (m := m) (n := n) nu *
          (D0 F + Hprime m (DirectionalConcrete.frameRows F)) *
            gradeProjection (d := d) (m := m) (n := n) nu := by
  rw [Matrix.transpose_mul, gradeProjection_transpose]
  calc
    (gradeProjection (d := d) (m := m) (n := n) nu *
        (CreateAnalysisStack (m := m) F).transpose) *
        (CreateAnalysisStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) =
      gradeProjection (d := d) (m := m) (n := n) nu *
        ((CreateAnalysisStack (m := m) F).transpose *
          CreateAnalysisStack (m := m) F) *
            gradeProjection (d := d) (m := m) (n := n) nu := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [CreateAnalysisStack_transpose_mul_self]

/-- The analysis Gram bound `m+ν`, obtained from the fresh diagonal and the
concrete directional estimate for `H'`. -/
theorem CreateAnalysisStack_gradeProjection_norm
    (F : Frame n d) (nu : ℕ) :
    ‖CreateAnalysisStack (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((m : ℝ) + (nu : ℝ)) := by
  let A := CreateAnalysisStack (m := m) F *
    gradeProjection (d := d) (m := m) (n := n) nu
  let P := gradeProjection (d := d) (m := m) (n := n) nu
  have hP : ‖P‖ ≤ 1 := gradeProjection_norm_le_one nu
  have hD0P : ‖D0 F * P‖ ≤ (m : ℝ) := by
    calc
      ‖D0 F * P‖ ≤ ‖D0 F‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (m : ℝ) * 1 := mul_le_mul (D0_norm_le F) hP
        (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (m : ℝ) := mul_one _
  have hHP :
      ‖Hprime m (DirectionalConcrete.frameRows F) * P‖ ≤ (nu : ℝ) := by
    simpa [P] using DirectionalConcrete.norm_Hprime_restricted_le
      (m := m) F nu
  have hgram : ‖A.transpose * A‖ ≤ (m : ℝ) + (nu : ℝ) := by
    rw [show A.transpose * A = P *
        (D0 F + Hprime m (DirectionalConcrete.frameRows F)) * P by
      simpa [A, P] using CreateAnalysisStack_restricted_gram
        (m := m) F nu]
    calc
      ‖P * (D0 F + Hprime m (DirectionalConcrete.frameRows F)) * P‖ ≤
          ‖P‖ * ‖(D0 F + Hprime m
            (DirectionalConcrete.frameRows F)) * P‖ := by
        rw [Matrix.mul_assoc]
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖(D0 F + Hprime m
            (DirectionalConcrete.frameRows F)) * P‖ := by
        exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ = ‖D0 F * P + Hprime m
            (DirectionalConcrete.frameRows F) * P‖ := by
        rw [one_mul, Matrix.add_mul]
      _ ≤ ‖D0 F * P‖ +
          ‖Hprime m (DirectionalConcrete.frameRows F) * P‖ := norm_add_le _ _
      _ ≤ (m : ℝ) + (nu : ℝ) := add_le_add hD0P hHP
  have hconj : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hsquare : ‖A‖ * ‖A‖ = ‖A.transpose * A‖ := by
    rw [← hconj, Matrix.l2_opNorm_conjTranspose_mul_self]
  have hmn : 0 ≤ (m : ℝ) + (nu : ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hmn
  change ‖A‖ ≤ Real.sqrt ((m : ℝ) + (nu : ℝ))
  nlinarith [norm_nonneg A, Real.sqrt_nonneg ((m : ℝ) + (nu : ℝ))]

theorem pDagAt_mul_pAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * pAt r j =
      wordKernel (r, i) (r, j) (.pUp, .pDown) := by
  simpa [pAt, pDagAt, wordKernel, BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate pDestroy

theorem COne_mul_COne_transpose_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * (COne F r j).transpose =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pUp, .pDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, COne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * pDagAt r j inp.2 p)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p *
            (pDagAt r j).transpose p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Matrix.transpose_apply]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .pDown) out.2 inp.2 := by
      rw [pDagAt_transpose]
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_pAt_of_ne r hij)
      change (F.u i out.1 * F.u j inp.1) *
        ((pDagAt r i * pAt r j) out.2 inp.2) = _
      rw [h]

/-- Same-site part of the shared-leg cogram. -/
def D1Row (F : Frame n d) (r : Fin m) : FullOp d m n :=
  ∑ i, COne F r i * (COne F r i).transpose

/-- Global same-site light-occupancy diagonal. -/
def D1 (F : Frame n d) : FullOp d m n :=
  ∑ r, D1Row F r

theorem CMatrix_mul_transpose_decomposition (F : Frame n d) (r : Fin m) :
    CMatrix F r * (CMatrix F r).transpose =
      D1Row F r +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (DirectionalConcrete.frameRows F) r i j
            (.pUp, .pDown) := by
  classical
  rw [CMatrix_eq_sum_COne, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  rw [D1Row, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, COne F r i * (COne F r j).transpose) =
        (∑ j ∈ Finset.univ.erase i,
          COne F r i * (COne F r j).transpose) +
          COne F r i * (COne F r i).transpose := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = COne F r i * (COne F r i).transpose +
        ∑ j ∈ Finset.univ.erase i,
          COne F r i * (COne F r j).transpose := add_comm _ _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact COne_mul_COne_transpose_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

theorem ghat_eq_D1_add_lightHop (F : Frame n d) :
    ghat (m := m) F = D1 F +
      NamedBands.wordSum m (DirectionalConcrete.frameRows F) .pUp .pDown := by
  classical
  rw [ghat]
  simp only [D1, NamedBands.wordSum, physicalWordSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  exact CMatrix_mul_transpose_decomposition F r

/-- Exact grade-zero light-band identity from the two diagonal/cross Grams. -/
theorem Lzero_eq_ghat_sub_D1_add_Hprime (F : Frame n d) :
    Lzero m (DirectionalConcrete.frameRows F) =
      (ghat F - D1 F) + Hprime m (DirectionalConcrete.frameRows F) := by
  rw [Lzero, Hprime]
  have h := ghat_eq_D1_add_lightHop (m := m) F
  rw [h]
  abel

/-- The scalar row kernel `P†P` is exactly the indicator of a light site. -/
theorem pDagAt_row_inner (r : Fin m) (i : Fin n)
    (a b : Pattern m n) :
    (∑ p, pDagAt r i a p * pDagAt r i b p) =
      if a = b ∧ a (r, i) = .one then 1 else 0 := by
  classical
  let s : Site m n := (r, i)
  let erased := HeavyBandsConcrete.setSite a s .zero
  by_cases ha : a s = .one
  · rw [Finset.sum_eq_single erased]
    · have hfirst : a (r, i) = .one ∧
          erased = HeavyBandsConcrete.setSite a (r, i) .zero := by
        constructor
        · simpa [s] using ha
        · rfl
      have hsecond :
          (b (r, i) = .one ∧
            erased = HeavyBandsConcrete.setSite b (r, i) .zero) ↔ b = a := by
        constructor
        · rintro ⟨hb, heq⟩
          calc
            b = HeavyBandsConcrete.setSite
                (HeavyBandsConcrete.setSite b (r, i) .zero) (r, i) .one := by
              symm
              exact HeavyBandsConcrete.setSite_restore (b := .zero) b (r, i) hb
            _ = HeavyBandsConcrete.setSite erased (r, i) .one := by rw [← heq]
            _ = a := by
              exact HeavyBandsConcrete.setSite_restore
                (b := .zero) a (r, i) (by simpa [s] using ha)
        · rintro rfl
          exact hfirst
      simp only [pDagAt_apply, if_pos hfirst]
      by_cases hab : b = a
      · subst b
        simp [hfirst]
      · have hn : ¬(b (r, i) = .one ∧
            erased = HeavyBandsConcrete.setSite b (r, i) .zero) :=
          fun hb ↦ hab (hsecond.mp hb)
        have hab' : a ≠ b := Ne.symm hab
        simp [hn, hab']
    · intro p _ hpne
      have hz : pDagAt r i a p = 0 := by
        rw [pDagAt_apply]
        simp [s, erased, ha, hpne]
      rw [hz, zero_mul]
    · simp
  · have hzero (p : Pattern m n) : pDagAt r i a p = 0 := by
      rw [pDagAt_apply]
      simp [s, ha]
    have hane : a (r, i) ≠ .one := by simpa [s] using ha
    simp [hzero, hane]

theorem D1Row_apply (F : Frame n d) (r : Fin m)
    (out inp : Fin d × Pattern m n) :
    D1Row F r out inp =
      if out.2 = inp.2 then
        partialFrameOperator F (out.2.lightInRow r) out.1 inp.1 else 0 := by
  classical
  simp only [D1Row, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply, COne]
  calc
    (∑ i, ∑ p,
        (F.u i out.1 * pDagAt r i out.2 p) *
          (F.u i inp.1 * pDagAt r i inp.2 p)) =
        ∑ i, (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p * pDagAt r i inp.2 p := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = ∑ i, (F.u i out.1 * F.u i inp.1) *
        (if out.2 = inp.2 ∧ out.2 (r, i) = .one then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pDagAt_row_inner]
    _ = _ := by
      by_cases hp : out.2 = inp.2
      · simp only [hp, true_and, if_true]
        simp [partialFrameOperator, Pattern.lightInRow, Finset.sum_filter]
      · simp [hp]

theorem D1_apply (F : Frame n d) (out inp : Fin d × Pattern m n) :
    D1 (m := m) F out inp =
      if out.2 = inp.2 then
        ∑ r, partialFrameOperator F (out.2.lightInRow r) out.1 inp.1
      else 0 := by
  classical
  simp only [D1, Matrix.sum_apply, D1Row_apply]
  by_cases hp : out.2 = inp.2
  · simp [hp]
  · simp [hp]

theorem D1_fullFiber_rows (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fullFiber (Matrix.mulVec (D1 (m := m) F) x) p =
      ∑ r, applyMatrix (partialFrameOperator F (p.lightInRow r))
        (fullFiber x p) := by
  classical
  ext k
  simp only [fullFiber, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    applyMatrix, WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ inp : Fin d × Pattern m n,
      D1 (m := m) F (k, p) inp * x inp) =
    ∑ r, ∑ l, (partialFrameOperator F (p.lightInRow r)) k l * x (l, p)
  rw [Fintype.sum_prod_type]
  simp_rw [D1_apply]
  calc
    (∑ l, ∑ q,
        (if p = q then
          ∑ r, (partialFrameOperator F (p.lightInRow r)) k l else 0) *
            x (l, q)) =
        ∑ l, (∑ r, (partialFrameOperator F (p.lightInRow r)) k l) *
          x (l, p) := by
      apply Finset.sum_congr rfl
      intro l _
      simp
    _ = ∑ l, ∑ r,
        (partialFrameOperator F (p.lightInRow r)) k l * x (l, p) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm]

theorem D1_fullFiber_sites (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fullFiber (Matrix.mulVec (D1 (m := m) F) x) p =
      ∑ s ∈ p.light,
        (analyze F (fullFiber x p) s.2) • F.u s.2 := by
  rw [D1_fullFiber_rows]
  simp_rw [partialFrameOperator_mulVec]
  ext k
  simp only [synthesize, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply]
  exact DirectionalConcrete.sum_rows_light_eq_sum_light p
    (fun s ↦ analyze F (fullFiber x p) s.2 * F.u s.2 k)

theorem analyze_smul_frame_normSq_le (F : Frame n d)
    (v : EVec d) (i : Fin n) :
    ParsevalFrame.normSq ((analyze F v i) • F.u i) ≤
      ParsevalFrame.normSq v := by
  have ha : (analyze F v i) ^ 2 ≤ ParsevalFrame.normSq v := by
    have h := subset_analysis F ({i} : Finset (Fin n)) v
    simpa using h
  have hu := vector_normSq_le_one F i
  have hscale :
      ParsevalFrame.normSq ((analyze F v i) • F.u i) =
        (analyze F v i) ^ 2 * ParsevalFrame.normSq (F.u i) := by
    simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hscale]
  calc
    (analyze F v i) ^ 2 * ParsevalFrame.normSq (F.u i) ≤
        (analyze F v i) ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hu (sq_nonneg _)
    _ ≤ ParsevalFrame.normSq v := by simpa using ha

theorem D1_output_fiber_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (D1 (m := m) F) x) p) ≤
      (p.light.card : ℝ) ^ 2 *
        ParsevalFrame.normSq (fullFiber x p) := by
  rw [D1_fullFiber_sites]
  calc
    ParsevalFrame.normSq
        (∑ s ∈ p.light, (analyze F (fullFiber x p) s.2) • F.u s.2) ≤
        (p.light.card : ℝ) * ∑ s ∈ p.light,
          ParsevalFrame.normSq
            ((analyze F (fullFiber x p) s.2) • F.u s.2) :=
      DirectionalConcrete.normSq_sum_le_card p.light
        (fun s ↦ (analyze F (fullFiber x p) s.2) • F.u s.2)
    _ ≤ (p.light.card : ℝ) * ∑ _s ∈ p.light,
          ParsevalFrame.normSq (fullFiber x p) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro s _
      exact analyze_smul_frame_normSq_le F (fullFiber x p) s.2
    _ = (p.light.card : ℝ) ^ 2 *
          ParsevalFrame.normSq (fullFiber x p) := by
      simp
      ring

theorem D1_supported_energy_le (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ}
    (hx : DirectionalConcrete.SupportedAtGrade nu x) :
    FiniteHilbert.normSq (Matrix.mulVec (D1 (m := m) F) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  rw [DirectionalConcrete.full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (D1 (m := m) F) x) p)) ≤
        ∑ p, (nu : ℝ) ^ 2 *
          ParsevalFrame.normSq (fullFiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.grade = nu
      · have hcardNat : p.light.card ≤ nu := by
          simpa [hp] using p.card_light_le_grade
        have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
          exact_mod_cast hcardNat
        have hsquare : (p.light.card : ℝ) ^ 2 ≤ (nu : ℝ) ^ 2 := by
          have hc0 : 0 ≤ (p.light.card : ℝ) := Nat.cast_nonneg _
          have hn0 : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
          nlinarith
        exact (D1_output_fiber_energy_le F x p).trans
          (mul_le_mul_of_nonneg_right hsquare real_inner_self_nonneg)
      · have hz : fullFiber x p = 0 := by
          ext k
          exact hx k p hp
        have hlocal := D1_output_fiber_energy_le (m := m) F x p
        rw [hz] at hlocal ⊢
        simpa [ParsevalFrame.normSq] using hlocal
    _ = (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      rw [DirectionalConcrete.full_normSq_eq_sum_fiber, Finset.mul_sum]

theorem D1_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
        (Matrix.mulVec
          (D1 (m := m) F * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  rw [← Matrix.mulVec_mulVec]
  calc
    FiniteHilbert.normSq
        (Matrix.mulVec (D1 (m := m) F)
          (Matrix.mulVec (gradeProjection (d := d) nu) x)) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) :=
      D1_supported_energy_le F (DirectionalConcrete.gradeProjection_supported nu x)
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left (gradeProjection_normSq_le nu x)
        (sq_nonneg (nu : ℝ))

/-- The light-occupancy diagonal has restricted norm at most the input grade. -/
theorem D1_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖D1 (m := m) F * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact FiniteHilbert.norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (D1_restricted_energy (m := m) F nu)

/-- The transpose synthesis stack sends full grade `mu+1` exactly to row
grade `mu`. -/
theorem rowProjection_CStackTranspose_gradeProjection
    (F : Frame n d) (mu : ℕ) :
    HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
        (CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1) =
      (CStack (m := m) F).transpose *
        gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
  classical
  ext out inp
  simp only [HeavyBandsConcrete.rowGradeProjection, gradeProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = mu + 1
  · by_cases hentry : (CStack F).transpose out inp = 0
    · have hz : CStack F inp out = 0 := by
        simpa [Matrix.transpose_apply] using hentry
      simp [hin, hz]
    · have hentry' : CStack F inp out ≠ 0 := by
        simpa [Matrix.transpose_apply] using hentry
      have hrel := CMatrix_grade_relation F out.1 hentry'
      have hout : out.2.grade = mu := by
        rw [hin] at hrel
        push_cast at hrel
        have hz : (out.2.grade : ℤ) = (mu : ℤ) := by omega
        exact_mod_cast hz
      simp [hin, hout]
  · simp [hin]

/-- Exact cogram of the projected synthesis factor. -/
theorem CStack_restricted_cogram (F : Frame n d) (mu : ℕ) :
    let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
    let R := HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu
    let B := P * CStack (m := m) F * R
    B * B.transpose = P * ghat F * P := by
  dsimp
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    HeavyBandsConcrete.rowGradeProjection_transpose, gradeProjection_transpose]
  have hins := rowProjection_CStackTranspose_gradeProjection
    (m := m) F mu
  have hins' :
      HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1)) =
      (CStack (m := m) F).transpose *
        gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
    rw [← Matrix.mul_assoc, hins]
  calc
    (gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu) *
      (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1))) =
      (gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
          CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu) *
          ((CStack (m := m) F).transpose *
            gradeProjection (d := d) (m := m) (n := n) (mu + 1)) := by
      rw [hins']
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
          (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
            ((CStack (m := m) F).transpose *
              gradeProjection (d := d) (m := m) (n := n) (mu + 1))) := by
      simp only [Matrix.mul_assoc]
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1)) := by
      rw [hins']
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        (CStack (m := m) F * (CStack (m := m) F).transpose) *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [CStack_mul_transpose]

/-- Sharp restricted synthesis-stack bound.  The output projection is one
grade above the row input projection, exactly as required by the light and
mixed factorizations. -/
theorem CStack_restricted_norm (F : Frame n d) (mu : ℕ) :
    ‖gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu‖ ≤
      Real.sqrt ((d : ℝ) + (mu : ℝ)) := by
  let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
  let R := HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu
  let B := P * CStack (m := m) F * R
  have hP : ‖P‖ ≤ 1 := gradeProjection_norm_le_one (mu + 1)
  have hG :
      ‖ghat (m := m) F * P‖ ≤ (d : ℝ) + (mu : ℝ) := by
    have hsharp := LightSectorConcrete.ghat_gradeProjection_norm_le
      (m := m) F (mu + 1) (Nat.succ_le_succ (Nat.zero_le mu))
    dsimp [P]
    convert hsharp using 1 <;> push_cast <;> ring
  have hcogram : ‖B * B.transpose‖ ≤ (d : ℝ) + (mu : ℝ) := by
    rw [show B * B.transpose = P * ghat (m := m) F * P by
      simpa [B, P, R] using CStack_restricted_cogram (m := m) F mu]
    calc
      ‖P * ghat (m := m) F * P‖ ≤ ‖P‖ * ‖ghat (m := m) F * P‖ := by
        rw [Matrix.mul_assoc]
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ((d : ℝ) + (mu : ℝ)) := by
        exact mul_le_mul hP hG (norm_nonneg _) (by positivity)
      _ = (d : ℝ) + (mu : ℝ) := one_mul _
  have hBconj : B.transpose.conjTranspose = B := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hsquare : ‖B * B.transpose‖ = ‖B‖ * ‖B‖ := by
    calc
      ‖B * B.transpose‖ =
          ‖B.transpose.conjTranspose * B.transpose‖ := by rw [hBconj]
      _ = ‖B.transpose‖ * ‖B.transpose‖ :=
        Matrix.l2_opNorm_conjTranspose_mul_self B.transpose
      _ = ‖B‖ * ‖B‖ := by
        rw [HeavyBandsConcrete.l2_opNorm_transpose_real]
  have hdm : 0 ≤ (d : ℝ) + (mu : ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hdm
  change ‖B‖ ≤ Real.sqrt ((d : ℝ) + (mu : ℝ))
  rw [hsquare] at hcogram
  nlinarith [norm_nonneg B, Real.sqrt_nonneg ((d : ℝ) + (mu : ℝ))]

theorem pDagAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * HeavyBandsConcrete.rUpAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rUp) := by
  simpa [pDagAt, HeavyBandsConcrete.rUpAt, wordKernel,
    BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rPromote

theorem pDagAt_mul_rDownAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * HeavyBandsConcrete.rDownAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rDown) := by
  simpa [pDagAt, HeavyBandsConcrete.rDownAt, wordKernel,
    BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rDemote

theorem pDagAt_mul_rUpAt_self (r : Fin m) (i : Fin n) :
    pDagAt r i * HeavyBandsConcrete.rUpAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single
      (HeavyBandsConcrete.setSite out (r, i) .zero)]
    · simp [HeavyBandsConcrete.rUpAt_apply, HeavyBandsConcrete.setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [pDagAt_apply, hout]

theorem pDagAt_mul_rDownAt_self (r : Fin m) (i : Fin n) :
    pDagAt r i * HeavyBandsConcrete.rDownAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single
      (HeavyBandsConcrete.setSite out (r, i) .zero)]
    · simp [HeavyBandsConcrete.rDownAt_apply, HeavyBandsConcrete.setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [pDagAt_apply, hout]

theorem COne_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * HeavyBandsConcrete.AUpOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pUp, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.AUpOne,
    orderedWordTerm, externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * HeavyBandsConcrete.rUpAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rUpAt r j p inp.2 := by
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

theorem COne_mul_ADownOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * HeavyBandsConcrete.ADownOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pUp, .rDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.ADownOne,
    orderedWordTerm, externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * HeavyBandsConcrete.rDownAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rDownAt r j p inp.2 := by
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

theorem COne_mul_AUpOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    COne F r i * HeavyBandsConcrete.AUpOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.AUpOne,
    Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u i inp.1 * HeavyBandsConcrete.rUpAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rUpAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rUpAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

theorem COne_mul_ADownOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    COne F r i * HeavyBandsConcrete.ADownOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.ADownOne,
    Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u i inp.1 * HeavyBandsConcrete.rDownAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rDownAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rDownAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

theorem CMatrix_mul_AUpMatrix (F : Frame n d) (r : Fin m) :
    CMatrix F r * HeavyBandsConcrete.AUpMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j
          (.pUp, .rUp) := by
  classical
  rw [CMatrix_eq_sum_COne, HeavyBandsConcrete.AUpMatrix_eq_sum_one,
    Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    COne_mul_AUpOne_self, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_AUpOne_of_ne F r
    (Ne.symm (Finset.mem_erase.mp hj).1)

theorem CMatrix_mul_ADownMatrix (F : Frame n d) (r : Fin m) :
    CMatrix F r * HeavyBandsConcrete.ADownMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j
          (.pUp, .rDown) := by
  classical
  rw [CMatrix_eq_sum_COne, HeavyBandsConcrete.ADownMatrix_eq_sum_one,
    Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    COne_mul_ADownOne_self, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_ADownOne_of_ne F r
    (Ne.symm (Finset.mem_erase.mp hj).1)

/-- Reusable exact mixed-band factorization requested downstream. -/
theorem Xplus_eq_CStack_mul_AUpStack (F : Frame n d) :
    Xplus m (DirectionalConcrete.frameRows F) =
      CStack (m := m) F * HeavyBandsConcrete.AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [Xplus, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, CStack, HeavyBandsConcrete.AUpStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_AUpMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- Reusable exact mixed grade-zero factorization requested downstream. -/
theorem Xzero_eq_CStack_mul_ADownStack (F : Frame n d) :
    Xzero m (DirectionalConcrete.frameRows F) =
      CStack (m := m) F * HeavyBandsConcrete.ADownStack (m := m) F := by
  classical
  ext out inp
  simp only [Xzero, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, CStack, HeavyBandsConcrete.ADownStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_ADownMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

theorem Lplus_transpose_eq_Lminus (F : Frame n d) :
    (Lplus m (DirectionalConcrete.frameRows F)).transpose =
      Lminus m (DirectionalConcrete.frameRows F) := by
  rw [Lplus, Lminus, NamedBands.wordSum, NamedBands.wordSum,
    DirectionalConcrete.transpose_physicalWordSum]
  rfl

theorem Lminus_transpose_eq_Lplus (F : Frame n d) :
    (Lminus m (DirectionalConcrete.frameRows F)).transpose =
      Lplus m (DirectionalConcrete.frameRows F) := by
  rw [← Lplus_transpose_eq_Lminus (m := m) F,
    Matrix.transpose_transpose]

theorem Lplus_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 2
      (Lplus m (DirectionalConcrete.frameRows F)) := by
  simpa [Lplus, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.pUp, .pUp)

theorem Lminus_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous (-2)
      (Lminus m (DirectionalConcrete.frameRows F)) := by
  simpa [Lminus, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.pDown, .pDown)

theorem aTerm_add_bTerm_mono_nat {k nu m : ℕ} (d : ℕ)
    (hknu : k ≤ nu) (hm : 1 ≤ m) :
    BandEnvelope.aTerm d k m + BandEnvelope.bTerm d k m ≤
      BandEnvelope.aTerm d nu m + BandEnvelope.bTerm d nu m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hknuR : (k : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hknu
  have hfrac :
      ((d : ℝ) + (k : ℝ) + 1) / (m : ℝ) ≤
        ((d : ℝ) + (nu : ℝ) + 1) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) hmR.le
  have ha : BandEnvelope.aTerm d k m ≤ BandEnvelope.aTerm d nu m := by
    exact Real.sqrt_le_sqrt hfrac
  have hb : BandEnvelope.bTerm d k m ≤ BandEnvelope.bTerm d nu m := by
    exact hfrac
  exact add_le_add ha hb

/-- Raw restricted norm of the concrete light-light raising band. -/
theorem Lplus_gradeProjection_norm_le (F : Frame n d) (nu : ℕ) :
    ‖Lplus m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) := by
  rw [Lplus_grade_factor]
  have hC := CStack_restricted_norm (m := m) F (nu + 1)
  have hC' :
      ‖gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)‖ ≤
        Real.sqrt ((d : ℝ) + (nu : ℝ) + 1) := by
    convert hC using 1 <;> push_cast <;> ring
  calc
    _ ≤
        ‖gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
            CStack (m := m) F *
            HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)‖ *
          ‖CreateAnalysisStack (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((d : ℝ) + (nu : ℝ) + 1) *
        Real.sqrt ((m : ℝ) + (nu : ℝ)) := by
      exact mul_le_mul hC'
        (CreateAnalysisStack_gradeProjection_norm (m := m) F nu)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) := by
      rw [Real.sqrt_mul (by positivity :
        0 ≤ (d : ℝ) + (nu : ℝ) + 1)]

/-- Exact normalized light raising estimate before its scalar envelope. -/
theorem normalized_Lplus_gradeProjection_norm_le
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lplus m (DirectionalConcrete.frameRows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) /
          (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (one_div_pos.mpr hmR)]
  calc
    (1 / (m : ℝ)) *
        ‖Lplus m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (1 / (m : ℝ)) * Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (Lplus_gradeProjection_norm_le (m := m) F nu) (by positivity)
    _ = _ := by ring

/-- Assembly-shaped light raising estimate, with exactly the `aTerm+bTerm`
right-hand side consumed by `ConcreteBandAssembly`. -/
theorem normalized_Lplus_gradeProjection_norm_le_envelope
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lplus m (DirectionalConcrete.frameRows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      BandEnvelope.aTerm d nu m + BandEnvelope.bTerm d nu m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact (normalized_Lplus_gradeProjection_norm_le (m := m) F nu hm).trans
    (BandEnvelope.lightPlus_scalar_bound
      (Nat.cast_nonneg d) (Nat.cast_nonneg nu) hmR)

/-- Raw restricted norm of the concrete grade-preserving light-light band. -/
theorem Lzero_gradeProjection_norm_le (F : Frame n d) (nu : ℕ) :
    ‖Lzero m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      3 * ((d : ℝ) + (nu : ℝ)) := by
  let P := gradeProjection (d := d) (m := m) (n := n) nu
  have hG : ‖ghat (m := m) F * P‖ ≤ (d : ℝ) + (nu : ℝ) := by
    simpa [P] using LightSectorConcrete.ghat_gradeProjection_norm_le_all
      (m := m) F nu
  have hD : ‖D1 (m := m) F * P‖ ≤ (nu : ℝ) := by
    simpa [P] using D1_gradeProjection_norm (m := m) F nu
  have hH :
      ‖Hprime m (DirectionalConcrete.frameRows F) * P‖ ≤ (nu : ℝ) := by
    simpa [P] using DirectionalConcrete.norm_Hprime_restricted_le
      (m := m) F nu
  rw [Lzero_eq_ghat_sub_D1_add_Hprime, Matrix.add_mul, Matrix.sub_mul]
  change ‖ghat (m := m) F * P - D1 (m := m) F * P +
      Hprime m (DirectionalConcrete.frameRows F) * P‖ ≤ _
  calc
    _ ≤ ‖ghat (m := m) F * P - D1 (m := m) F * P‖ +
        ‖Hprime m (DirectionalConcrete.frameRows F) * P‖ := norm_add_le _ _
    _ ≤ (‖ghat (m := m) F * P‖ + ‖D1 (m := m) F * P‖) +
        ‖Hprime m (DirectionalConcrete.frameRows F) * P‖ := by
      exact add_le_add
        (norm_sub_le (ghat (m := m) F * P) (D1 (m := m) F * P))
        (le_refl ‖Hprime m (DirectionalConcrete.frameRows F) * P‖)
    _ ≤ (((d : ℝ) + (nu : ℝ)) + (nu : ℝ)) + (nu : ℝ) := by
      exact add_le_add (add_le_add hG hD) hH
    _ ≤ 3 * ((d : ℝ) + (nu : ℝ)) := by
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith

/-- Exact normalized grade-preserving light estimate before the assembly
envelope. -/
theorem normalized_Lzero_gradeProjection_norm_le
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lzero m (DirectionalConcrete.frameRows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      3 * ((d : ℝ) + (nu : ℝ)) / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (one_div_pos.mpr hmR)]
  calc
    (1 / (m : ℝ)) *
        ‖Lzero m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (1 / (m : ℝ)) * (3 * ((d : ℝ) + (nu : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (Lzero_gradeProjection_norm_le (m := m) F nu) (by positivity)
    _ = _ := by ring

/-- Assembly-shaped grade-preserving light estimate, with exactly the
`3*bTerm` right-hand side consumed by `ConcreteBandAssembly`. -/
theorem normalized_Lzero_gradeProjection_norm_le_envelope
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lzero m (DirectionalConcrete.frameRows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      3 * BandEnvelope.bTerm d nu m := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  calc
    _ ≤ 3 * ((d : ℝ) + (nu : ℝ)) / (m : ℝ) :=
      normalized_Lzero_gradeProjection_norm_le (m := m) F nu hm
    _ ≤ 3 * BandEnvelope.bTerm d nu m := by
      unfold BandEnvelope.bTerm
      calc
        3 * ((d : ℝ) + (nu : ℝ)) / (m : ℝ) ≤
            (3 * ((d : ℝ) + (nu : ℝ) + 1)) / (m : ℝ) := by
          exact div_le_div_of_nonneg_right (by linarith) hmR.le
        _ = 3 * (((d : ℝ) + (nu : ℝ) + 1) / (m : ℝ)) := by ring

theorem Lminus_gradeProjection_zero (F : Frame n d) :
    Lminus m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  apply FiniteHilbert.input_grade_vanishes_of_no_output
    (Lminus_homogeneous (m := m) F) 0
  intro mu
  omega

theorem Lminus_gradeProjection_one (F : Frame n d) :
    Lminus m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 1 = 0 := by
  apply FiniteHilbert.input_grade_vanishes_of_no_output
    (Lminus_homogeneous (m := m) F) 1
  intro mu
  omega

/-- Exact adjoint-grade transfer, including the normalized scalar. -/
theorem normalized_Lminus_gradeProjection_norm_eq_shift
    (F : Frame n d) (k : ℕ) :
    ‖((1 / (m : ℝ)) • Lminus m (DirectionalConcrete.frameRows F)) *
        gradeProjection (d := d) (m := m) (n := n) (k + 2)‖ =
      ‖((1 / (m : ℝ)) • Lplus m (DirectionalConcrete.frameRows F)) *
        gradeProjection (d := d) (m := m) (n := n) k‖ := by
  have hshift :
      gradeProjection (d := d) (m := m) (n := n) (k + 2) *
          Lplus m (DirectionalConcrete.frameRows F) =
        Lplus m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) (m := m) (n := n) k := by
    exact DirectionalNormalized.gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
      (Lplus_homogeneous (m := m) F) (k + 2) k (by norm_num)
  calc
    _ = ‖(((1 / (m : ℝ)) •
          Lminus m (DirectionalConcrete.frameRows F)) *
          gradeProjection (d := d) (m := m) (n := n) (k + 2)).transpose‖ := by
      exact (DirectionalNormalized.l2_norm_transpose _).symm
    _ = _ := by
      rw [Matrix.transpose_mul, Matrix.transpose_smul,
        Lminus_transpose_eq_Lplus, gradeProjection_transpose,
        Matrix.mul_smul, hshift, Matrix.smul_mul]

/-- Assembly-shaped lowering estimate.  The two bottom grades vanish, while
all higher grades transfer exactly to the raising estimate two grades below. -/
theorem normalized_Lminus_gradeProjection_norm_le_envelope
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lminus m (DirectionalConcrete.frameRows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      BandEnvelope.aTerm d nu m + BandEnvelope.bTerm d nu m := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  have henv_nonneg (r : ℕ) :
      0 ≤ BandEnvelope.aTerm d r m + BandEnvelope.bTerm d r m :=
    add_nonneg (BandEnvelope.aTerm_nonneg _ _ _)
      (BandEnvelope.bTerm_nonneg
        (Nat.cast_nonneg d) (Nat.cast_nonneg r) hmR)
  rcases nu with (_ | _ | k)
  · rw [Matrix.smul_mul, Lminus_gradeProjection_zero]
    simpa using henv_nonneg 0
  · rw [Matrix.smul_mul, Lminus_gradeProjection_one]
    simpa using henv_nonneg 1
  · calc
      _ = ‖((1 / (m : ℝ)) • Lplus m
            (DirectionalConcrete.frameRows F)) *
          gradeProjection (d := d) (m := m) (n := n) k‖ := by
        exact normalized_Lminus_gradeProjection_norm_eq_shift (m := m) F k
      _ ≤ BandEnvelope.aTerm d k m + BandEnvelope.bTerm d k m :=
        normalized_Lplus_gradeProjection_norm_le_envelope (m := m) F k hm
      _ ≤ BandEnvelope.aTerm d (((k + 2 : ℕ) : ℝ)) m +
          BandEnvelope.bTerm d (((k + 2 : ℕ) : ℝ)) m :=
        aTerm_add_bTerm_mono_nat (k := k) (nu := k + 2) (m := m)
          d (by omega) hm
      _ = _ := by push_cast; ring

end

end SparseFock.LightBandsConcrete
