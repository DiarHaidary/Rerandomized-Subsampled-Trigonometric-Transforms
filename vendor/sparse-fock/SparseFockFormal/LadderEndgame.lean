import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Finite ladder bookkeeping

This file formalizes only the finite combinatorics behind the three-band ladder
expansion.  It does not define the Fock-space bands or prove that an operator
word has the scalar weight used below.
-/

namespace SparseFock

namespace LadderEndgame

/-- The three possible band directions in one ladder factor. -/
inductive Band where
  | down
  | level
  | up
  deriving DecidableEq, Repr

instance : Fintype Band where
  elems := {.down, .level, .up}
  complete b := by
    cases b <;> simp

@[simp] theorem card_band : Fintype.card Band = 3 := by
  decide

/-- A length-`N` band word. -/
abbrev BandWord (N : ℕ) := Fin N → Band

/-- There are exactly `3^N` words in the three-band expansion. -/
@[simp] theorem card_bandWord (N : ℕ) : Fintype.card (BandWord N) = 3 ^ N := by
  simp [BandWord]

/-- The grade update associated with a band direction.  `down` is truncated at
zero; valid vacuum paths are a subset of these words. -/
def Band.nextGrade : Band → ℕ → ℕ
  | .down, grade => grade - 1
  | .level, grade => grade
  | .up, grade => grade + 1

theorem nextGrade_le_succ (band : Band) (grade : ℕ) :
    band.nextGrade grade ≤ grade + 1 := by
  cases band with
  | down =>
      exact (Nat.sub_le grade 1).trans (Nat.le_succ grade)
  | level => exact Nat.le_succ grade
  | up => exact le_rfl

/-- Grade reached after reading a list of bands from an initial grade. -/
def walkGradeFrom (initial : ℕ) : List Band → ℕ
  | [] => initial
  | band :: rest => walkGradeFrom (band.nextGrade initial) rest

@[simp] theorem walkGradeFrom_nil (initial : ℕ) : walkGradeFrom initial [] = initial := rfl

@[simp] theorem walkGradeFrom_cons (initial : ℕ) (band : Band) (rest : List Band) :
    walkGradeFrom initial (band :: rest) =
      walkGradeFrom (band.nextGrade initial) rest := rfl

/-- Along `N` ladder steps, grade can increase by at most `N`. -/
theorem walkGradeFrom_le_add_length (steps : List Band) (initial : ℕ) :
    walkGradeFrom initial steps ≤ initial + steps.length := by
  induction steps generalizing initial with
  | nil => simp
  | cons band rest ih =>
      calc
        walkGradeFrom initial (band :: rest) =
            walkGradeFrom (band.nextGrade initial) rest := rfl
        _ ≤ band.nextGrade initial + rest.length := ih _
        _ ≤ (initial + 1) + rest.length :=
          Nat.add_le_add_right (nextGrade_le_succ band initial) _
        _ = initial + (band :: rest).length := by simp; omega

/-- A vacuum-started prefix never visits a grade above the total word length. -/
theorem vacuum_prefix_grade_le_total (pre suffix : List Band) :
    walkGradeFrom 0 pre ≤ (pre ++ suffix).length := by
  calc
    walkGradeFrom 0 pre ≤ pre.length := by
      simpa using walkGradeFrom_le_add_length pre 0
    _ ≤ (pre ++ suffix).length := by simp

/-- Scalar word counting: if each of the `3^N` words contributes at most
`beta^N`, their total contributes at most `(3*beta)^N`.

The premise `weight word ≤ beta^N` is where all operator and reachability
arguments must enter; it is not proved here. -/
theorem sum_bandWords_le
    {N : ℕ} (weight : BandWord N → ℝ) (beta : ℝ)
    (hword : ∀ word, weight word ≤ beta ^ N) :
    (∑ word, weight word) ≤ (3 * beta) ^ N := by
  calc
    (∑ word, weight word) ≤ ∑ _word : BandWord N, beta ^ N := by
      exact Finset.sum_le_sum fun word _ => hword word
    _ = (Fintype.card (BandWord N) : ℝ) * beta ^ N := by simp
    _ = (3 * beta) ^ N := by simp [mul_pow]

/-- The scalar `d`-vacuum-vector factor in the ladder estimate. -/
theorem vacuum_sum_bandWords_le
    {N : ℕ} (weight : BandWord N → ℝ) {d beta : ℝ}
    (hd : 0 ≤ d)
    (hword : ∀ word, weight word ≤ beta ^ N) :
    d * (∑ word, weight word) ≤ d * (3 * beta) ^ N := by
  exact mul_le_mul_of_nonneg_left (sum_bandWords_le weight beta hword) hd

end LadderEndgame

end SparseFock


