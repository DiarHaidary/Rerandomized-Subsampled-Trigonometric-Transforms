import SparseFockFormal.LocalOperators
import Mathlib.Tactic

namespace SparseFock

namespace BandInventory

/-- The four oriented summands of the local Jacobi matrix. -/
inductive Leg where
  | pUp
  | pDown
  | rUp
  | rDown
  deriving DecidableEq, Repr

instance : Fintype Leg where
  elems := {.pUp, .pDown, .rUp, .rDown}
  complete x := by cases x <;> simp

def Leg.op : Leg → LocalOperator.Op
  | .pUp => LocalOperator.pCreate
  | .pDown => LocalOperator.pDestroy
  | .rUp => LocalOperator.rPromote
  | .rDown => LocalOperator.rDemote

def Leg.degree : Leg → ℤ
  | .pUp | .rUp => 1
  | .pDown | .rDown => -1

def Leg.heavy : Leg → ℕ
  | .pUp | .pDown => 0
  | .rUp | .rDown => 1

def Leg.adjoint : Leg → Leg
  | .pUp => .pDown
  | .pDown => .pUp
  | .rUp => .rDown
  | .rDown => .rUp

@[simp] theorem Leg.adjoint_adjoint (a : Leg) : a.adjoint.adjoint = a := by
  cases a <;> rfl

@[simp] theorem Leg.degree_adjoint (a : Leg) :
    a.adjoint.degree = -a.degree := by
  cases a <;> rfl

@[simp] theorem Leg.heavy_adjoint (a : Leg) :
    a.adjoint.heavy = a.heavy := by
  cases a <;> rfl

theorem Leg.transpose_op (a : Leg) : a.op.transpose = a.adjoint.op := by
  cases a <;> simp [Leg.op, Leg.adjoint]

theorem Leg.op_homogeneous (a : Leg) :
    LocalOperator.Homogeneous a.degree a.op := by
  cases a <;>
    simp only [Leg.degree, Leg.op] <;>
    first
    | exact LocalOperator.pCreate_homogeneous
    | exact LocalOperator.pDestroy_homogeneous
    | exact LocalOperator.rPromote_homogeneous
    | exact LocalOperator.rDemote_homogeneous

/-- A local word records the two oriented transitions at two distinct sites. -/
abbrev Word := Leg × Leg

def Word.degree (w : Word) : ℤ := w.1.degree + w.2.degree

def Word.heavy (w : Word) : ℕ := w.1.heavy + w.2.heavy

/-- Adjoint after transposing the external rank-one coefficient and relabeling the
ordered site pair. -/
def Word.orderedAdjoint (w : Word) : Word := (w.2.adjoint, w.1.adjoint)

@[simp] theorem Word.orderedAdjoint_involutive (w : Word) :
    w.orderedAdjoint.orderedAdjoint = w := by
  rcases w with ⟨a, b⟩
  simp [Word.orderedAdjoint]

@[simp] theorem Word.degree_orderedAdjoint (w : Word) :
    w.orderedAdjoint.degree = -w.degree := by
  rcases w with ⟨a, b⟩
  simp [Word.orderedAdjoint, Word.degree]

@[simp] theorem Word.heavy_orderedAdjoint (w : Word) :
    w.orderedAdjoint.heavy = w.heavy := by
  rcases w with ⟨a, b⟩
  simp [Word.orderedAdjoint, Word.heavy, Nat.add_comm]

inductive Shift where
  | plus
  | zero
  | minus
  deriving DecidableEq, Repr

instance : Fintype Shift where
  elems := {.plus, .zero, .minus}
  complete x := by cases x <;> simp

inductive Heaviness where
  | lightLight
  | lightHeavy
  | heavyHeavy
  deriving DecidableEq, Repr

instance : Fintype Heaviness where
  elems := {.lightLight, .lightHeavy, .heavyHeavy}
  complete x := by cases x <;> simp

def Word.shift : Word → Shift
  | (.pUp, .pUp) | (.pUp, .rUp) | (.rUp, .pUp) | (.rUp, .rUp) => .plus
  | (.pDown, .pDown) | (.pDown, .rDown) | (.rDown, .pDown) |
      (.rDown, .rDown) => .minus
  | _ => .zero

def Word.heaviness : Word → Heaviness
  | (.pUp, .pUp) | (.pUp, .pDown) | (.pDown, .pUp) | (.pDown, .pDown) =>
      .lightLight
  | (.rUp, .rUp) | (.rUp, .rDown) | (.rDown, .rUp) | (.rDown, .rDown) =>
      .heavyHeavy
  | _ => .lightHeavy

def Shift.degree : Shift → ℤ
  | .plus => 2
  | .zero => 0
  | .minus => -2

theorem Word.degree_eq_shift (w : Word) : w.degree = w.shift.degree := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

theorem Word.heavy_eq_heaviness (w : Word) :
    w.heavy =
      match w.heaviness with
      | .lightLight => 0
      | .lightHeavy => 1
      | .heavyHeavy => 2 := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

def Shift.adjoint : Shift → Shift
  | .plus => .minus
  | .zero => .zero
  | .minus => .plus

@[simp] theorem Word.shift_orderedAdjoint (w : Word) :
    w.orderedAdjoint.shift = w.shift.adjoint := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

@[simp] theorem Word.heaviness_orderedAdjoint (w : Word) :
    w.orderedAdjoint.heaviness = w.heaviness := by
  rcases w with ⟨a, b⟩
  cases a <;> cases b <;> rfl

def wordsIn (δ : Shift) (h : Heaviness) : Finset Word :=
  Finset.univ.filter fun w => w.shift = δ ∧ w.heaviness = h

@[simp] theorem mem_wordsIn (w : Word) (δ : Shift) (h : Heaviness) :
    w ∈ wordsIn δ h ↔ w.shift = δ ∧ w.heaviness = h := by
  simp [wordsIn]

/-- Every word lies in its uniquely determined grade/heaviness cell. -/
theorem word_has_unique_cell (w : Word) :
    w ∈ wordsIn w.shift w.heaviness ∧
      ∀ δ h, w ∈ wordsIn δ h → δ = w.shift ∧ h = w.heaviness := by
  constructor
  · simp
  · intro δ h hw
    rw [mem_wordsIn] at hw
    exact ⟨hw.1.symm, hw.2.symm⟩

@[simp] theorem card_all_words : Fintype.card Word = 16 := by decide

/-- The exact `3 × 3` inventory counts.  The middle grade contains each word together
with its distinct adjoint; the plus/minus rows are interchanged by adjoint. -/
theorem card_plus_lightLight : (wordsIn .plus .lightLight).card = 1 := by decide
theorem card_plus_lightHeavy : (wordsIn .plus .lightHeavy).card = 2 := by decide
theorem card_plus_heavyHeavy : (wordsIn .plus .heavyHeavy).card = 1 := by decide
theorem card_zero_lightLight : (wordsIn .zero .lightLight).card = 2 := by decide
theorem card_zero_lightHeavy : (wordsIn .zero .lightHeavy).card = 4 := by decide
theorem card_zero_heavyHeavy : (wordsIn .zero .heavyHeavy).card = 2 := by decide
theorem card_minus_lightLight : (wordsIn .minus .lightLight).card = 1 := by decide
theorem card_minus_lightHeavy : (wordsIn .minus .lightHeavy).card = 2 := by decide
theorem card_minus_heavyHeavy : (wordsIn .minus .heavyHeavy).card = 1 := by decide

/-- Summing the nine inventory cells accounts for all sixteen local products. -/
theorem nine_cell_count_total :
    (wordsIn .plus .lightLight).card +
      (wordsIn .plus .lightHeavy).card +
      (wordsIn .plus .heavyHeavy).card +
      (wordsIn .zero .lightLight).card +
      (wordsIn .zero .lightHeavy).card +
      (wordsIn .zero .heavyHeavy).card +
      (wordsIn .minus .lightLight).card +
      (wordsIn .minus .lightHeavy).card +
    (wordsIn .minus .heavyHeavy).card = 16 := by
  decide

end BandInventory

end SparseFock


