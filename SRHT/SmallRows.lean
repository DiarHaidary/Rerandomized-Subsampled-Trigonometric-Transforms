import SRHT.HardCore
import SRHT.Walsh

/-!
# Concrete two-sign normal ordering for restricted rows

Every operator below is a literal matrix on two finite subset registers.
The generic mode parameter is subsequently specialized to translated Walsh rows.
-/

namespace SRHT.SmallRows

open SRHT.HardCore
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {G R : Type*} [Fintype G] [DecidableEq G]
  [Fintype R] [DecidableEq R]

abbrev SignPair (G : Type*) := Finset G × Finset G
abbrev TwoOp (G : Type*) := Matrix (SignPair G) (SignPair G) ℝ

/-- The actual matrix tensor product on the two sign registers. -/
def tensor (A B : HardCore.Op G) : TwoOp G :=
  fun out inp => A out.1 inp.1 * B out.2 inp.2

def localCorrection (i l : G) : HardCore.Op G :=
  if i = l then 1 - (2 : ℝ) • number i else 0

def modeCovariance (f g : G → ℝ) : HardCore.Op G :=
  (∑ a, f a * g a) • (1 : HardCore.Op G)

def modeCorrection (f g : G → ℝ) : HardCore.Op G :=
  (2 : ℝ) • ∑ a, (f a * g a) • number a

/-- One matrix entry of the concrete five-term normal-order identity. -/
theorem local_normalOrder (i l : G) (f g : G → ℝ) :
    tensor (annihilate i * create l) (annihilateMode f * createMode g) =
      tensor (localCorrection i l) (modeCovariance f g - modeCorrection f g) +
      tensor (create l * annihilate i) (modeCovariance f g) -
      tensor (create l * annihilate i) (modeCorrection f g) +
      tensor (localCorrection i l) (createMode g * annihilateMode f) +
      tensor (create l * annihilate i) (createMode g * annihilateMode f) := by
  rw [annihilate_create, annihilateMode_createMode]
  ext out inp
  simp only [tensor, localCorrection, modeCovariance, modeCorrection,
    Matrix.add_apply, Matrix.sub_apply]
  ring

abbrev RowSign (R G : Type*) := R × SignPair G

/-- The Gram kernel before putting the two annihilation/creation pairs in normal order. -/
def gramKernel (P : Matrix G G ℝ) (f : R → G → G → ℝ) :
    Matrix (RowSign R G) (RowSign R G) ℝ := fun out inp =>
  ∑ i, ∑ l, P i l *
    tensor (annihilate i * create l)
      (annihilateMode (f out.1 i) * createMode (f inp.1 l)) out.2 inp.2

def doubleCommutator (P : Matrix G G ℝ) (f : R → G → G → ℝ) :
    Matrix (RowSign R G) (RowSign R G) ℝ := fun out inp =>
  ∑ i, ∑ l, P i l *
    tensor (localCorrection i l)
      (modeCovariance (f out.1 i) (f inp.1 l) -
        modeCorrection (f out.1 i) (f inp.1 l)) out.2 inp.2

def xTransfer (P : Matrix G G ℝ) (f : R → G → G → ℝ) :
    Matrix (RowSign R G) (RowSign R G) ℝ := fun out inp =>
  ∑ i, ∑ l, P i l *
    tensor (create l * annihilate i)
      (modeCovariance (f out.1 i) (f inp.1 l)) out.2 inp.2

def negativeCorrection (P : Matrix G G ℝ) (f : R → G → G → ℝ) :
    Matrix (RowSign R G) (RowSign R G) ℝ := fun out inp =>
  ∑ i, ∑ l, P i l *
    tensor (create l * annihilate i)
      (modeCorrection (f out.1 i) (f inp.1 l)) out.2 inp.2

def yTransfer (P : Matrix G G ℝ) (f : R → G → G → ℝ) :
    Matrix (RowSign R G) (RowSign R G) ℝ := fun out inp =>
  ∑ i, ∑ l, P i l *
    tensor (localCorrection i l)
      (createMode (f inp.1 l) * annihilateMode (f out.1 i)) out.2 inp.2

def mixedTransfer (P : Matrix G G ℝ) (f : R → G → G → ℝ) :
    Matrix (RowSign R G) (RowSign R G) ℝ := fun out inp =>
  ∑ i, ∑ l, P i l *
    tensor (create l * annihilate i)
      (createMode (f inp.1 l) * annihilateMode (f out.1 i)) out.2 inp.2

/-- The complete five-term matrix identity, proved from the actual subset operators. -/
theorem gramKernel_normalOrder (P : Matrix G G ℝ) (f : R → G → G → ℝ) :
    gramKernel P f = doubleCommutator P f + xTransfer P f -
      negativeCorrection P f + yTransfer P f + mixedTransfer P f := by
  ext out inp
  simp only [gramKernel, doubleCommutator, xTransfer, negativeCorrection,
    yTransfer, mixedTransfer, Matrix.add_apply, Matrix.sub_apply]
  simp_rw [local_normalOrder]
  simp only [Matrix.add_apply, Matrix.sub_apply, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The SRHT specialization retains the actual chosen row labels. -/
def walshModes {k : ℕ} (T : Finset (WalshIndex k)) :
    T → WalshIndex k → WalshIndex k → ℝ :=
  fun j i a => walshMatrix k (j.1 + i) a

private theorem sum_rotate_five
    {B X Y I L : Type*} [Fintype B] [Fintype X] [Fintype Y]
    [Fintype I] [Fintype L] (F : B → X → Y → I → L → ℝ) :
    (∑ b, ∑ x, ∑ y, ∑ i, ∑ l, F b x y i l) =
      ∑ i, ∑ l, ∑ b, ∑ x, ∑ y, F b x y i l := by
  let e : (B × X × Y × I × L) ≃ (I × L × B × X × Y) :=
    { toFun := fun ⟨b,x,y,i,l⟩ => ⟨i,l,b,x,y⟩
      invFun := fun ⟨i,l,b,x,y⟩ => ⟨b,x,y,i,l⟩
      left_inv := by rintro ⟨b,x,y,i,l⟩; rfl
      right_inv := by rintro ⟨i,l,b,x,y⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun z => F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)
    (fun z => F z.2.2.1 z.2.2.2.1 z.2.2.2.2 z.1 z.2.1)
    (by intro z; rfl)
  simpa only [Fintype.sum_prod_type] using h

/-- The actual row collection, without its common `1/sqrt(n)` scalar. -/
def collectedDouble {D : Type*} [Fintype D]
    (U : Matrix G D ℝ) (f : R → G → G → ℝ) :
    Matrix (RowSign R G) (D × SignPair G) ℝ := fun out inp =>
  ∑ i, U i inp.1 * annihilate i out.2.1 inp.2.1 *
    annihilateMode (f out.1 i) out.2.2 inp.2.2

/-- The raw kernel is the genuine collected-row Gram, not a postulated model. -/
theorem collectedDouble_gram {D : Type*} [Fintype D] [DecidableEq D]
    (U : Matrix G D ℝ) (f : R → G → G → ℝ) :
    collectedDouble U f * (collectedDouble U f).transpose =
      gramKernel (U * U.transpose) f := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, collectedDouble,
    Fintype.sum_prod_type, gramKernel, tensor]
  simp_rw [← annihilate_transpose, ← annihilateMode_transpose]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul_sum]
  rw [sum_rotate_five]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end
end SRHT.SmallRows
