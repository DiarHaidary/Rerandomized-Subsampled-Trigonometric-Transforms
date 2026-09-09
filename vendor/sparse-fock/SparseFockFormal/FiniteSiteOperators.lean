import SparseFockFormal.BandInventory
import Mathlib.Tactic

namespace SparseFock

namespace FiniteOperator

open LocalOperator BandInventory

variable {m n : ℕ}

/-- A finite matrix on the sparse-Fock pattern basis. -/
abbrev FockOp (m n : ℕ) := Matrix (Pattern m n) (Pattern m n) ℝ

def gradeZ (p : Pattern m n) : ℤ :=
  ∑ s, weightZ (p s)

def agreesOutsideSite (s : Site m n) (out inp : Pattern m n) : Prop :=
  ∀ x, x ≠ s → out x = inp x

def agreesOutsidePair (s t : Site m n) (out inp : Pattern m n) : Prop :=
  ∀ x, x ≠ s → x ≠ t → out x = inp x

theorem agreesOutsideSite_symm {s : Site m n} {out inp : Pattern m n} :
    agreesOutsideSite s out inp ↔ agreesOutsideSite s inp out := by
  constructor <;> intro h x hx <;> exact (h x hx).symm

theorem agreesOutsidePair_symm {s t : Site m n} {out inp : Pattern m n} :
    agreesOutsidePair s t out inp ↔ agreesOutsidePair s t inp out := by
  constructor <;> intro h x hxs hxt <;> exact (h x hxs hxt).symm

theorem agreesOutsidePair_swap {s t : Site m n} {out inp : Pattern m n} :
    agreesOutsidePair s t out inp ↔ agreesOutsidePair t s out inp := by
  constructor <;> intro h x hxt hxs <;> exact h x hxs hxt

/-- Lift a local matrix to one specified site of the finite tensor-product basis. -/
noncomputable def siteKernel (s : Site m n) (A : LocalOperator.Op) : FockOp m n := by
  classical
  exact fun out inp =>
    if agreesOutsideSite s out inp then A (out s) (inp s) else 0

/-- Lift two local matrices to two specified sites. -/
noncomputable def pairKernel (s t : Site m n) (A B : LocalOperator.Op) : FockOp m n := by
  classical
  exact fun out inp =>
    if agreesOutsidePair s t out inp then A (out s) (inp s) * B (out t) (inp t) else 0

theorem transpose_siteKernel (s : Site m n) (A : LocalOperator.Op) :
    (siteKernel s A).transpose = siteKernel s A.transpose := by
  ext out inp
  simp only [Matrix.transpose_apply]
  by_cases h : agreesOutsideSite s inp out
  · have h' : agreesOutsideSite s out inp := agreesOutsideSite_symm.mpr h
    simp [siteKernel, h, h']
  · have h' : ¬ agreesOutsideSite s out inp := by
      intro hs
      exact h (agreesOutsideSite_symm.mp hs)
    simp [siteKernel, h, h']

theorem transpose_pairKernel (s t : Site m n) (A B : LocalOperator.Op) :
    (pairKernel s t A B).transpose = pairKernel s t A.transpose B.transpose := by
  ext out inp
  simp only [Matrix.transpose_apply]
  by_cases h : agreesOutsidePair s t inp out
  · have h' : agreesOutsidePair s t out inp := agreesOutsidePair_symm.mpr h
    simp [pairKernel, h, h']
  · have h' : ¬ agreesOutsidePair s t out inp := by
      intro hs
      exact h (agreesOutsidePair_symm.mp hs)
    simp [pairKernel, h, h']

theorem pairKernel_swap (s t : Site m n) (A B : LocalOperator.Op) :
    pairKernel s t A B = pairKernel t s B A := by
  ext out inp
  by_cases h : agreesOutsidePair s t out inp
  · have h' : agreesOutsidePair t s out inp := agreesOutsidePair_swap.mp h
    simp [pairKernel, h, h', mul_comm]
  · have h' : ¬ agreesOutsidePair t s out inp := by
      intro hs
      exact h (agreesOutsidePair_swap.mpr hs)
    simp [pairKernel, h, h']

theorem gradeZ_sub_eq_site {s : Site m n} {out inp : Pattern m n}
    (h : agreesOutsideSite s out inp) :
    gradeZ out - gradeZ inp = weightZ (out s) - weightZ (inp s) := by
  classical
  rw [gradeZ, gradeZ, ← Finset.sum_sub_distrib]
  calc
    (∑ x, (weightZ (out x) - weightZ (inp x))) =
        ∑ x, if x = s then weightZ (out s) - weightZ (inp s) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = s
          · subst x
            simp
          · have heq := h x hx
            simp [hx, heq]
    _ = weightZ (out s) - weightZ (inp s) := by simp

theorem gradeZ_sub_eq_pair {s t : Site m n} {out inp : Pattern m n}
    (hst : s ≠ t) (h : agreesOutsidePair s t out inp) :
    gradeZ out - gradeZ inp =
      (weightZ (out s) - weightZ (inp s)) +
      (weightZ (out t) - weightZ (inp t)) := by
  classical
  rw [gradeZ, gradeZ, ← Finset.sum_sub_distrib]
  calc
    (∑ x, (weightZ (out x) - weightZ (inp x))) =
        ∑ x, if x = s then weightZ (out s) - weightZ (inp s)
          else if x = t then weightZ (out t) - weightZ (inp t) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hxs : x = s
            · subst x
              simp
            · by_cases hxt : x = t
              · subst x
                simp [hxs]
              · have heq := h x hxs hxt
                simp [hxs, hxt, heq]
    _ = ∑ x, ((if x = s then weightZ (out s) - weightZ (inp s) else 0) +
        (if x = t then weightZ (out t) - weightZ (inp t) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxs : x = s
          · subst x
            simp [hst]
          · by_cases hxt : x = t
            · subst x
              simp [hxs]
            · simp [hxs, hxt]
    _ = (weightZ (out s) - weightZ (inp s)) +
        (weightZ (out t) - weightZ (inp t)) := by simp [Finset.sum_add_distrib]

/-- A finite pattern matrix changes total grade by `δ` on every nonzero entry. -/
def Homogeneous (δ : ℤ) (K : FockOp m n) : Prop :=
  ∀ ⦃out inp : Pattern m n⦄, K out inp ≠ 0 → gradeZ out = gradeZ inp + δ

theorem siteKernel_homogeneous {δ : ℤ} {A : LocalOperator.Op}
    (hA : LocalOperator.Homogeneous δ A) (s : Site m n) :
    Homogeneous δ (siteKernel s A) := by
  intro out inp hnonzero
  by_cases hoff : agreesOutsideSite s out inp
  · have hlocal : A (out s) (inp s) ≠ 0 := by
      simpa [siteKernel, hoff] using hnonzero
    have hw := hA hlocal
    have hd := gradeZ_sub_eq_site hoff
    omega
  · exact (hnonzero (by simp [siteKernel, hoff])).elim

theorem pairKernel_homogeneous {δ ε : ℤ} {A B : LocalOperator.Op}
    (hA : LocalOperator.Homogeneous δ A)
    (hB : LocalOperator.Homogeneous ε B)
    {s t : Site m n} (hst : s ≠ t) :
    Homogeneous (δ + ε) (pairKernel s t A B) := by
  intro out inp hnonzero
  by_cases hoff : agreesOutsidePair s t out inp
  · have hprod : A (out s) (inp s) * B (out t) (inp t) ≠ 0 := by
      simpa [pairKernel, hoff] using hnonzero
    have hAlocal : A (out s) (inp s) ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have hBlocal : B (out t) (inp t) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    have hwA := hA hAlocal
    have hwB := hB hBlocal
    have hd := gradeZ_sub_eq_pair hst hoff
    omega
  · exact (hnonzero (by simp [pairKernel, hoff])).elim

noncomputable def wordKernel (s t : Site m n) (w : Word) : FockOp m n :=
  pairKernel s t w.1.op w.2.op

theorem wordKernel_homogeneous (w : Word) {s t : Site m n} (hst : s ≠ t) :
    Homogeneous w.degree (wordKernel s t w) := by
  simpa [wordKernel, Word.degree] using
    pairKernel_homogeneous w.1.op_homogeneous w.2.op_homogeneous hst

/-- Matrix transpose agrees with the adjoint word after swapping the ordered sites. -/
theorem transpose_wordKernel (s t : Site m n) (w : Word) :
    (wordKernel s t w).transpose = wordKernel t s w.orderedAdjoint := by
  rw [wordKernel, transpose_pairKernel, pairKernel_swap]
  rcases w with ⟨a, b⟩
  simp [wordKernel, Word.orderedAdjoint, Leg.transpose_op]

end FiniteOperator

end SparseFock


