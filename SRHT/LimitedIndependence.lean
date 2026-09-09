import SparseFockFormal.FiniteLocalMoments
import SparseFockFormal.FiniteProductLaw
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Local-degree bounds for the literal two-round Gram polynomial.
The hypotheses below concern every low-coordinate observable, not a target moment. -/
namespace SRHT
open SparseFock SparseFock.FiniteLocalMoments
open scoped BigOperators
noncomputable section

variable {I A J K L : Type*} [DecidableEq I]

theorem matchesUpTo_of_min_card [Fintype I] [Fintype A]
    {μ ν : FiniteLaw (I → A)} {k : ℕ}
    (h : MatchesUpTo μ ν (min (Fintype.card I) k)) : MatchesUpTo μ ν k := by
  intro S hS f hf
  exact h S (le_min (Finset.card_le_univ S) hS) f hf

def MatrixDegree (k : ℕ) (F : (I → A) → Matrix J K ℝ) : Prop :=
  ∀ j k', HasLocalDegree k (fun x => F x j k')

namespace MatrixDegree

theorem constant (k : ℕ) (B : Matrix J K ℝ) :
    MatrixDegree (I := I) (A := A) k (fun _ => B) := by
  intro j l
  exact HasLocalDegree.constant k (B j l)

theorem transpose {k : ℕ} {F : (I → A) → Matrix J K ℝ}
    (hF : MatrixDegree k F) :
    MatrixDegree k (fun x => (F x).transpose) := by
  intro j l
  exact hF l j

theorem sub {k : ℕ} {F G : (I → A) → Matrix J K ℝ}
    (hF : MatrixDegree k F) (hG : MatrixDegree k G) :
    MatrixDegree k (fun x => F x - G x) := by
  intro j l
  exact HasLocalDegree.sub (hF j l) (hG j l)

theorem mul [Fintype K] {k l : ℕ}
    {F : (I → A) → Matrix J K ℝ} {G : (I → A) → Matrix K L ℝ}
    (hF : MatrixDegree k F) (hG : MatrixDegree l G) :
    MatrixDegree (k + l) (fun x => F x * G x) := by
  intro j z
  exact HasLocalDegree.sum_fintype
    (fun a x => F x j a * G x a z)
    (fun a => HasLocalDegree.mul (hF j a) (hG a z))

theorem smul {k : ℕ} {F : (I → A) → Matrix J K ℝ}
    (c : ℝ) (hF : MatrixDegree k F) :
    MatrixDegree k (fun x => c • F x) := by
  intro j l
  exact HasLocalDegree.smul c (hF j l)

theorem diagonal (σ : A → ℝ) :
    MatrixDegree (I := I) 1 (fun x => Matrix.diagonal (fun i => σ (x i))) := by
  intro i j
  by_cases h : i = j
  · subst j
    apply HasLocalDegree.atom {i} (fun x => Matrix.diagonal (fun i => σ (x i)) i i)
    · simp
    · intro x y hxy
      simp only [Matrix.diagonal_apply_eq]
      rw [hxy i (Finset.mem_singleton_self i)]
  · simpa [Matrix.diagonal_apply_ne _ h] using
      (HasLocalDegree.zero : HasLocalDegree (ι := I) (α := A) 1 (fun _ => 0))

theorem pow [Fintype J] [DecidableEq J] {k : ℕ}
    {F : (I → A) → Matrix J J ℝ} (hF : MatrixDegree k F) (t : ℕ) :
    MatrixDegree (k * t) (fun x => F x ^ t) := by
  induction t with
  | zero => simpa using constant (I := I) (A := A) 0 (1 : Matrix J J ℝ)
  | succ t ih =>
      simpa [pow_succ, Nat.mul_succ] using mul ih hF

theorem trace [Fintype J] {k : ℕ} {F : (I → A) → Matrix J J ℝ}
    (hF : MatrixDegree k F) :
    HasLocalDegree k (fun x => (F x).trace) :=
  HasLocalDegree.sum_fintype (fun j x => F x j j) (fun j => hF j j)

end MatrixDegree

variable [Fintype I] [Fintype J] [DecidableEq J]

/-- This definition uses arbitrary deterministic H; Walsh orthogonality is
not needed for the exact polynomial-degree argument. -/
def twoRoundPolynomial (H : Matrix I I ℝ) (σ : A → ℝ)
    (U : Matrix I J ℝ) (x y : I → A) : Matrix I J ℝ :=
  H * Matrix.diagonal (fun i => σ (y i)) * H *
    Matrix.diagonal (fun i => σ (x i)) * U

def weightedGramError (W : Matrix I J ℝ) (c : I → ℝ) : Matrix J J ℝ :=
  W.transpose * Matrix.diagonal c * W - 1

theorem twoRound_degree_x (H : Matrix I I ℝ) (σ : A → ℝ)
    (U : Matrix I J ℝ) (y : I → A) :
    MatrixDegree 1 (fun x => twoRoundPolynomial H σ U x y) := by
  unfold twoRoundPolynomial
  exact MatrixDegree.mul
    (MatrixDegree.mul (MatrixDegree.constant 0 _)
      (MatrixDegree.diagonal σ)) (MatrixDegree.constant 0 U)

theorem twoRound_degree_y (H : Matrix I I ℝ) (σ : A → ℝ)
    (U : Matrix I J ℝ) (x : I → A) :
    MatrixDegree 1 (fun y => twoRoundPolynomial H σ U x y) := by
  unfold twoRoundPolynomial
  exact MatrixDegree.mul
    (MatrixDegree.mul
      (MatrixDegree.mul
        (MatrixDegree.mul (MatrixDegree.constant 0 H) (MatrixDegree.diagonal σ))
        (MatrixDegree.constant 0 H))
      (MatrixDegree.constant 0 _)) (MatrixDegree.constant 0 U)

theorem weightedGram_degree {k : ℕ} {W : (I → A) → Matrix I J ℝ}
    (hW : MatrixDegree k W) (c : I → ℝ) :
    MatrixDegree (2 * k) (fun x => weightedGramError (W x) c) := by
  unfold weightedGramError
  have h := MatrixDegree.mul
    (MatrixDegree.mul hW.transpose (MatrixDegree.constant 0 (Matrix.diagonal c))) hW
  have h' : MatrixDegree (2 * k)
      (fun x => (W x).transpose * Matrix.diagonal c * W x) := by
    simpa [two_mul] using h
  exact MatrixDegree.sub h' (MatrixDegree.constant _ _)

theorem weightedGram_degree_selector (W : Matrix I J ℝ) (c : A → ℝ) :
    MatrixDegree 1 (fun η => weightedGramError W (fun i => c (η i))) := by
  unfold weightedGramError
  exact MatrixDegree.sub
    (MatrixDegree.mul
      (MatrixDegree.mul (MatrixDegree.constant 0 W.transpose) (MatrixDegree.diagonal c))
      (MatrixDegree.constant 0 W)) (MatrixDegree.constant _ _)

theorem traceGram_degree_x (H : Matrix I I ℝ) (σ : A → ℝ)
    (U : Matrix I J ℝ) (y : I → A) (c : I → ℝ) (q : ℕ) :
    HasLocalDegree (4 * q)
      (fun x => (weightedGramError (twoRoundPolynomial H σ U x y) c ^ (2*q)).trace) := by
  have h := (weightedGram_degree (twoRound_degree_x H σ U y) c).pow (2*q)
  convert h.trace using 1 <;> omega

theorem traceGram_degree_y (H : Matrix I I ℝ) (σ : A → ℝ)
    (U : Matrix I J ℝ) (x : I → A) (c : I → ℝ) (q : ℕ) :
    HasLocalDegree (4 * q)
      (fun y => (weightedGramError (twoRoundPolynomial H σ U x y) c ^ (2*q)).trace) := by
  have h := (weightedGram_degree (twoRound_degree_y H σ U x) c).pow (2*q)
  convert h.trace using 1 <;> omega

theorem traceGram_degree_selector (W : Matrix I J ℝ) (c : A → ℝ) (q : ℕ) :
    HasLocalDegree (2 * q)
      (fun η => (weightedGramError W (fun i => c (η i)) ^ (2*q)).trace) := by
  simpa using ((weightedGram_degree_selector W c).pow (2*q)).trace

theorem traceGram_match_x [Fintype A] (H : Matrix I I ℝ) (σ : A → ℝ)
    (U : Matrix I J ℝ) (y : I → A) (c : I → ℝ) (q : ℕ)
    {μ ν : FiniteLaw (I → A)} (hmatch : MatchesUpTo μ ν (4*q)) :
    μ.expect (fun x => (weightedGramError (twoRoundPolynomial H σ U x y) c ^ (2*q)).trace) =
    ν.expect (fun x => (weightedGramError (twoRoundPolynomial H σ U x y) c ^ (2*q)).trace) :=
  (traceGram_degree_x H σ U y c q).expect_eq_of_matchesUpTo hmatch

theorem traceGram_match_y [Fintype A] (H : Matrix I I ℝ) (σ : A → ℝ)
    (U : Matrix I J ℝ) (x : I → A) (c : I → ℝ) (q : ℕ)
    {μ ν : FiniteLaw (I → A)} (hmatch : MatchesUpTo μ ν (4*q)) :
    μ.expect (fun y => (weightedGramError (twoRoundPolynomial H σ U x y) c ^ (2*q)).trace) =
    ν.expect (fun y => (weightedGramError (twoRoundPolynomial H σ U x y) c ^ (2*q)).trace) :=
  (traceGram_degree_y H σ U x c q).expect_eq_of_matchesUpTo hmatch

theorem localDegree_expect {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    {k : ℕ} (f : Ω → (I → A) → ℝ)
    (hf : ∀ ω, HasLocalDegree k (f ω)) :
    HasLocalDegree k (fun x => μ.expect (fun ω => f ω x)) := by
  exact HasLocalDegree.sum_fintype
    (fun ω x => μ.weight ω * f ω x)
    (fun ω => HasLocalDegree.smul _ (hf ω))

/-- Exact transfer under separate marginal matching and mutual independence
of the three families. All three laws are actual finite probability laws. -/
theorem product3_expect_eq {B : Type*} [Fintype A] [Fintype B]
    {μx νx μy νy : FiniteLaw (I → A)} {μz νz : FiniteLaw (I → B)}
    {kx ky kz : ℕ} (hx : MatchesUpTo μx νx kx)
    (hy : MatchesUpTo μy νy ky) (hz : MatchesUpTo μz νz kz)
    (f : (I → A) → (I → A) → (I → B) → ℝ)
    (hfx : ∀ y z, HasLocalDegree kx (fun x => f x y z))
    (hfy : ∀ x z, HasLocalDegree ky (fun y => f x y z))
    (hfz : ∀ x y, HasLocalDegree kz (fun z => f x y z)) :
    (μx.product (μy.product μz)).expect (fun ω => f ω.1 ω.2.1 ω.2.2) =
    (νx.product (νy.product νz)).expect (fun ω => f ω.1 ω.2.1 ω.2.2) := by
  simp_rw [FiniteLaw.product_expect_eq_iterated]
  calc
    μx.expect (fun x => μy.expect (fun y => μz.expect (fun z => f x y z))) =
        μx.expect (fun x => μy.expect (fun y => νz.expect (fun z => f x y z))) := by
      apply μx.expect_congr
      intro x
      apply μy.expect_congr
      intro y
      exact (hfz x y).expect_eq_of_matchesUpTo hz
    _ = μx.expect (fun x => νy.expect (fun y => νz.expect (fun z => f x y z))) := by
      apply μx.expect_congr
      intro x
      exact (localDegree_expect νz (fun z y => f x y z)
        (fun z => hfy x z)).expect_eq_of_matchesUpTo hy
    _ = νx.expect (fun x => νy.expect (fun y => νz.expect (fun z => f x y z))) := by
      exact (localDegree_expect νy (fun y x => νz.expect (fun z => f x y z))
        (fun y => localDegree_expect νz (fun z x => f x y z)
          (fun z => hfx y z))).expect_eq_of_matchesUpTo hx

theorem twoRound_trace_moment_match {B : Type*} [Fintype A] [Fintype B]
    (H : Matrix I I ℝ) (σ : A → ℝ) (c : B → ℝ)
    (U : Matrix I J ℝ) (q : ℕ)
    {μx νx μy νy : FiniteLaw (I → A)} {μz νz : FiniteLaw (I → B)}
    (hx : MatchesUpTo μx νx (4*q)) (hy : MatchesUpTo μy νy (4*q))
    (hz : MatchesUpTo μz νz (2*q)) :
    (μx.product (μy.product μz)).expect
      (fun ω => (weightedGramError (twoRoundPolynomial H σ U ω.1 ω.2.1)
        (fun i => c (ω.2.2 i)) ^ (2*q)).trace) =
    (νx.product (νy.product νz)).expect
      (fun ω => (weightedGramError (twoRoundPolynomial H σ U ω.1 ω.2.1)
        (fun i => c (ω.2.2 i)) ^ (2*q)).trace) := by
  apply product3_expect_eq hx hy hz
    (fun x y z => (weightedGramError (twoRoundPolynomial H σ U x y)
      (fun i => c (z i)) ^ (2*q)).trace)
  · intro y z
    exact traceGram_degree_x H σ U y (fun i => c (z i)) q
  · intro x z
    exact traceGram_degree_y H σ U x (fun i => c (z i)) q
  · intro x y
    exact traceGram_degree_selector (twoRoundPolynomial H σ U x y) c q

end
end SRHT
