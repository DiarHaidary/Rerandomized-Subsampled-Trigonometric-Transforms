import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace SparseFock

/-- The three local orthogonal-polynomial levels used by the sparse-Fock model. -/
inductive Level where
  | zero
  | one
  | two
  deriving DecidableEq, Repr

/-- A concrete enumeration: local pattern states really form a finite type. -/
instance : Fintype Level where
  elems := {.zero, .one, .two}
  complete x := by
    cases x <;> simp

@[simp] theorem card_level : Fintype.card Level = 3 := by
  decide

/-- Occupation weight in the total-grade decomposition. -/
def Level.weight : Level → ℕ
  | .zero => 0
  | .one => 1
  | .two => 2

/-- A site is an incidence `(row, column)`. -/
abbrev Site (m n : ℕ) := Fin m × Fin n

/-- A finite sparse-Fock pattern. -/
abbrev Pattern (m n : ℕ) := Site m n → Level

namespace Pattern

variable {m n : ℕ}

/-- Total particle grade. -/
def grade (p : Pattern m n) : ℕ := ∑ s, (p s).weight

def fresh (p : Pattern m n) : Finset (Site m n) :=
  Finset.univ.filter fun s => p s = .zero

def light (p : Pattern m n) : Finset (Site m n) :=
  Finset.univ.filter fun s => p s = .one

def heavy (p : Pattern m n) : Finset (Site m n) :=
  Finset.univ.filter fun s => p s = .two

def freshInRow (p : Pattern m n) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (r, i) = .zero

def lightInRow (p : Pattern m n) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (r, i) = .one

def heavyInRow (p : Pattern m n) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (r, i) = .two

@[simp] theorem mem_fresh {p : Pattern m n} {s : Site m n} :
    s ∈ p.fresh ↔ p s = .zero := by
  simp [fresh]

@[simp] theorem mem_light {p : Pattern m n} {s : Site m n} :
    s ∈ p.light ↔ p s = .one := by
  simp [light]

@[simp] theorem mem_heavy {p : Pattern m n} {s : Site m n} :
    s ∈ p.heavy ↔ p s = .two := by
  simp [heavy]

@[simp] theorem mem_freshInRow {p : Pattern m n} {r : Fin m} {i : Fin n} :
    i ∈ p.freshInRow r ↔ p (r, i) = .zero := by
  simp [freshInRow]

@[simp] theorem mem_lightInRow {p : Pattern m n} {r : Fin m} {i : Fin n} :
    i ∈ p.lightInRow r ↔ p (r, i) = .one := by
  simp [lightInRow]

@[simp] theorem mem_heavyInRow {p : Pattern m n} {r : Fin m} {i : Fin n} :
    i ∈ p.heavyInRow r ↔ p (r, i) = .two := by
  simp [heavyInRow]

theorem fresh_disjoint_light (p : Pattern m n) : Disjoint p.fresh p.light := by
  refine Finset.disjoint_left.mpr ?_
  intro s hs0 hs1
  simp only [mem_fresh] at hs0
  simp only [mem_light] at hs1
  cases hs0.symm.trans hs1

theorem fresh_disjoint_heavy (p : Pattern m n) : Disjoint p.fresh p.heavy := by
  refine Finset.disjoint_left.mpr ?_
  intro s hs0 hs2
  simp only [mem_fresh] at hs0
  simp only [mem_heavy] at hs2
  cases hs0.symm.trans hs2

theorem light_disjoint_heavy (p : Pattern m n) : Disjoint p.light p.heavy := by
  refine Finset.disjoint_left.mpr ?_
  intro s hs1 hs2
  simp only [mem_light] at hs1
  simp only [mem_heavy] at hs2
  cases hs1.symm.trans hs2

/-- Every site is in exactly one of the three occupation classes. -/
theorem fresh_union_light_union_heavy (p : Pattern m n) :
    (p.fresh ∪ p.light) ∪ p.heavy = Finset.univ := by
  ext s
  cases h : p s <;> simp [h]

/-- The row-local light counts sum to the global light count. -/
theorem card_light_eq_sum_card_lightInRow (p : Pattern m n) :
    p.light.card = ∑ r, (p.lightInRow r).card := by
  classical
  simp only [light, lightInRow, Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- The row-local heavy counts sum to the global heavy count. -/
theorem card_heavy_eq_sum_card_heavyInRow (p : Pattern m n) :
    p.heavy.card = ∑ r, (p.heavyInRow r).card := by
  classical
  simp only [heavy, heavyInRow, Finset.card_filter]
  rw [Fintype.sum_prod_type]

theorem grade_eq_card_light_add_two_mul_card_heavy (p : Pattern m n) :
    p.grade = p.light.card + 2 * p.heavy.card := by
  classical
  simp only [grade, light, heavy, Finset.card_filter]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  cases h : p s <;> simp [Level.weight]

theorem card_light_le_grade (p : Pattern m n) : p.light.card ≤ p.grade := by
  rw [grade_eq_card_light_add_two_mul_card_heavy]
  omega

theorem two_mul_card_heavy_le_grade (p : Pattern m n) :
    2 * p.heavy.card ≤ p.grade := by
  rw [grade_eq_card_light_add_two_mul_card_heavy]
  omega

end Pattern

end SparseFock


