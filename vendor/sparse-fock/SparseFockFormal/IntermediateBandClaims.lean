import SparseFockFormal.HeavyBandsConcrete
import SparseFockFormal.LightBandsConcrete
import Mathlib.Tactic

/-!
# Intermediate concrete band claims

This module isolates the claim-by-claim inequalities used in the heavy- and
light-leg arguments of the paper.  All statements are on the literal finite
pattern basis; quadratic inequalities are therefore exact finite-dimensional
Loewner inequalities.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace SparseFock.IntermediateBandClaims

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator
open FiniteHilbert NamedBands DirectionalConcrete
open HeavyBandsConcrete LightBandsConcrete

noncomputable section

variable {d m n : ℕ}

/-- A pattern with one marked site in a fixed physical row. -/
structure RowMarked (r : Fin m) (a : Level) where
  pattern : Pattern m n
  col : Fin n
  state : pattern (r, col) = a
  deriving DecidableEq, Fintype

theorem RowMarked.ext' {r : Fin m} {a : Level}
    {x y : RowMarked (n := n) r a}
    (hp : x.pattern = y.pattern) (hc : x.col = y.col) : x = y := by
  cases x
  cases y
  simp_all

def rowMarkedEquivSigma (r : Fin m) (a : Level) :
    RowMarked (n := n) r a ≃
      Σ p : Pattern m n, {i : Fin n // p (r, i) = a} where
  toFun z := ⟨z.pattern, ⟨z.col, z.state⟩⟩
  invFun z := { pattern := z.1, col := z.2.1, state := z.2.2 }
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨p, i⟩; rfl

theorem sum_rowMarked (r : Fin m) (a : Level)
    (f : Pattern m n → Fin n → ℝ) :
    (∑ p, ∑ i ∈ Finset.univ.filter (fun i ↦ p (r, i) = a), f p i) =
      ∑ z : RowMarked (n := n) r a, f z.pattern z.col := by
  classical
  calc
    (∑ p, ∑ i ∈ Finset.univ.filter (fun i ↦ p (r, i) = a), f p i) =
        ∑ p, ∑ i : {i : Fin n // p (r, i) = a}, f p i := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_subtype _ (by simp) (f p)
    _ = ∑ z : Σ p : Pattern m n, {i : Fin n // p (r, i) = a},
        f z.1 z.2.1 := by rw [Fintype.sum_sigma]
    _ = ∑ z : RowMarked (n := n) r a, f z.pattern z.col := by
      have h := Equiv.sum_comp (rowMarkedEquivSigma (m := m) (n := n) r a)
        (fun z : Σ p : Pattern m n, {i : Fin n // p (r, i) = a} ↦
          f z.1 z.2.1)
      simpa [rowMarkedEquivSigma] using h.symm

/-- Change the marked state within one fixed row. -/
def rowMarkedTransition (r : Fin m) (a b : Level) :
    RowMarked (n := n) r a ≃ RowMarked (n := n) r b where
  toFun z :=
    { pattern := setSite z.pattern (r, z.col) b
      col := z.col
      state := setSite_apply_self _ _ _ }
  invFun z :=
    { pattern := setSite z.pattern (r, z.col) a
      col := z.col
      state := setSite_apply_self _ _ _ }
  left_inv z := by
    cases z with
    | mk p i h =>
      exact RowMarked.ext' (setSite_restore (b := b) p (r, i) h) rfl
  right_inv z := by
    cases z with
    | mk p i h =>
      exact RowMarked.ext' (setSite_restore (b := a) p (r, i) h) rfl

theorem sum_rowMarked_reindex (r : Fin m) (a b : Level)
    (f : RowMarked (n := n) r a → ℝ) :
    (∑ z : RowMarked (n := n) r a, f z) =
      ∑ z : RowMarked (n := n) r b,
        f ((rowMarkedTransition (n := n) r a b).symm z) := by
  have h := Equiv.sum_comp (rowMarkedTransition (n := n) r a b).symm f
  simpa using h.symm

/-- Exact sharp cardinality behind the `A_r` row-stratum estimate. -/
theorem card_heavy_after_promote_le_half_rowGrade
    {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .one) :
    ((setSite p (r, i) .two).heavyInRow r).card ≤
      (rowGrade p r + 1) / 2 := by
  rw [card_heavyInRow_setSite_two hi]
  have hlight : 1 ≤ (p.lightInRow r).card :=
    Finset.one_le_card.mpr ⟨i, by simp [hi]⟩
  simp only [rowGrade]
  omega

/-- Exact sharp cardinality behind the `Ã_r` row-stratum estimate. -/
theorem card_light_after_demote_le_rowGrade_sub_one
    {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .two) :
    ((setSite p (r, i) .one).lightInRow r).card ≤ rowGrade p r - 1 := by
  rw [card_lightInRow_setSite_one hi]
  have hheavy : 1 ≤ (p.heavyInRow r).card :=
    Finset.one_le_card.mpr ⟨i, by simp [hi]⟩
  simp only [rowGrade]
  omega

end

end SparseFock.IntermediateBandClaims
