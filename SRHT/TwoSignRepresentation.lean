import SRHT.OccupationBasis
import SRHT.MatrixRepresentation
import SRHT.SmallRows

/-! The actual Walsh frame in the finite occupation basis. -/
namespace SRHT.TwoSignRepresentation
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open SparseFock.FiniteL2 SRHT.HardCore Matrix

theorem prod_mulOp_factor
    {Ω I Ω' I' : Type*} [Fintype Ω] [Fintype I] [Fintype Ω'] [Fintype I']
    [DecidableEq Ω] [DecidableEq I] [DecidableEq Ω'] [DecidableEq I']
    (B : WeightedONBasis Ω I) (C : WeightedONBasis Ω' I') (f : Ω → ℝ) (g : Ω' → ℝ)
    (out inp : I × I') :
    (ProductBasis.prod B C).mulOp (fun x => f x.1*g x.2) out inp =
      B.mulOp f out.1 inp.1 * C.mulOp g out.2 inp.2 := by
  simp only [WeightedONBasis.mulOp,WeightedONBasis.coeff,ProductBasis.prod,
    ProductBasis.prodFun,Fintype.sum_prod_type]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

variable {k d : ℕ}
abbrev G (k : ℕ) := WalshIndex k

def basis (k : ℕ) : WeightedONBasis (SignAssignment k × SignAssignment k)
    (SmallRows.SignPair (G k)) :=
  ProductBasis.prod OccupationBasis.signs OccupationBasis.signs

@[simp] theorem basis_vacuum : (basis k).vacuum = (∅,∅) := by
  simp [basis,ProductBasis.prod]

theorem basis_law : ProductBasis.lawOfBasis (basis k) =
    (signLaw k).product (signLaw k) := by
  apply OccupationBasis.law_ext
  funext x
  have h1 := congrArg (fun μ => μ.weight x.1) (OccupationBasis.signs_law (k:=k))
  have h2 := congrArg (fun μ => μ.weight x.2) (OccupationBasis.signs_law (k:=k))
  change _ * _ = _ * _
  exact congrArg₂ (· * ·) h1 h2

def flip (i : G k) : Op (G k) := create i + annihilate i

theorem signs_product (i a : G k) (out inp : SmallRows.SignPair (G k)) :
    (basis k).mulOp (fun x => bitSign (x.1 i)*bitSign (x.2 a)) out inp =
      flip i out.1 inp.1 * flip a out.2 inp.2 := by
  have h := prod_mulOp_factor (OccupationBasis.signs (G:=G k))
    (OccupationBasis.signs (G:=G k)) (fun x : SignAssignment k => bitSign (x i))
    (fun y : SignAssignment k => bitSign (y a)) out inp
  rw [OccupationBasis.signs_mulOp,OccupationBasis.signs_mulOp] at h
  exact h

def liftedFrame (U : Matrix (G k) (Fin d) ℝ) (T : Finset (G k)) :
    Matrix (SmallRows.RowSign T (G k)) (Fin d × SmallRows.SignPair (G k)) ℝ :=
  MatrixRepresentation.rect (basis k) (fun x =>
    (transformedFrame U x.1 x.2).submatrix Subtype.val id)

theorem liftedFrame_apply (U : Matrix (G k) (Fin d) ℝ) (T : Finset (G k))
    (out : SmallRows.RowSign T (G k)) (inp : Fin d × SmallRows.SignPair (G k)) :
    liftedFrame U T out inp = ∑ a, ∑ i,
      (walshMatrix k out.1.1 a * walshMatrix k a i * U i inp.1) *
        flip i out.2.1 inp.2.1 * flip a out.2.2 inp.2.2 := by
  change (basis k).coeff out.2 (fun x =>
    transformedFrame U x.1 x.2 out.1.1 inp.1 * (basis k).basis inp.2 x) = _
  simp only [transformedFrame_apply,Finset.sum_mul]
  rw [(basis k).coeff_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [(basis k).coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := signs_product i a out.2 inp.2
  unfold WeightedONBasis.mulOp at h
  rw [mul_assoc _ (flip i out.2.1 inp.2.1) (flip a out.2.2 inp.2.2), ← h]
  simp only [WeightedONBasis.coeff,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem flip_card (i : G k) (S T : Finset (G k)) (h : flip i S T ≠ 0) :
    S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 := by
  by_cases hc : create i S T=0
  · have ha : annihilate i S T≠0 := by simpa [flip,hc] using h
    have he : i∉S ∧ T=insert i S := by
      simpa [annihilate] using ha
    rw [he.2,Finset.card_insert_of_notMem he.1]
    omega
  · have he : i∈S ∧ T=S.erase i := by
      simpa [create] using hc
    rw [he.2,Finset.card_erase_of_mem he.1]
    have hp := Finset.card_pos.mpr ⟨i,he.1⟩
    omega

theorem liftedFrame_bandwidth (U : Matrix (G k) (Fin d) ℝ) (T : Finset (G k))
    (out : SmallRows.RowSign T (G k)) (inp : Fin d × SmallRows.SignPair (G k))
    (h : liftedFrame U T out inp ≠ 0) :
    out.2.1.card ≤ inp.2.1.card+1 ∧ inp.2.1.card ≤ out.2.1.card+1 ∧
    out.2.2.card ≤ inp.2.2.card+1 ∧ inp.2.2.card ≤ out.2.2.card+1 := by
  rw [liftedFrame_apply] at h
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  have hx : flip i out.2.1 inp.2.1 ≠ 0 := by intro he; simp [he] at hi
  have hy : flip a out.2.2 inp.2.2 ≠ 0 := by intro he; simp [he] at hi
  exact ⟨(flip_card i _ _ hx).1,(flip_card i _ _ hx).2,flip_card a _ _ hy⟩

def rowEffect (U : Matrix (G k) (Fin d) ℝ) (j : G k)
    (x : SignAssignment k × SignAssignment k) : Matrix (Fin d) (Fin d) ℝ :=
  fun b c => transformedFrame U x.1 x.2 j b * transformedFrame U x.1 x.2 j c

def effect (U : Matrix (G k) (Fin d) ℝ) (j : G k) :
    Matrix (Fin d × SmallRows.SignPair (G k)) (Fin d × SmallRows.SignPair (G k)) ℝ :=
  (basis k).matrixMulOp (rowEffect U j)

theorem rowEffect_positive (U : Matrix (G k) (Fin d) ℝ) (j : G k)
    (x : SignAssignment k × SignAssignment k) : (rowEffect U j x).PosSemidef := by
  let v := transformedFrame U x.1 x.2 j
  have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.replicateRow Unit v)
  convert h using 1
  ext b c
  simp [Matrix.mul_apply,Matrix.replicateRow,Matrix.conjTranspose_apply,rowEffect,v]

theorem effect_positive (U : Matrix (G k) (Fin d) ℝ) (j : G k) :
    (effect U j).PosSemidef :=
  MatrixRepresentation.matrixMulOp_positive _ _ (rowEffect_positive U j)

theorem rowEffect_sum (U : Matrix (G k) (Fin d) ℝ) (T : Finset (G k))
    (x : SignAssignment k × SignAssignment k) :
    (∑ j : T, rowEffect U j.1 x) =
      ((transformedFrame U x.1 x.2).submatrix (fun j : T => j.1) id).transpose *
        ((transformedFrame U x.1 x.2).submatrix (fun j : T => j.1) id) := by
  ext b c
  simp [Matrix.sum_apply,Matrix.mul_apply,rowEffect,Matrix.transpose_apply]

theorem effect_sum_gram (U : Matrix (G k) (Fin d) ℝ) (T : Finset (G k)) :
    (∑ j ∈ T, effect U j) = (liftedFrame U T).transpose * liftedFrame U T := by
  rw [liftedFrame,MatrixRepresentation.rect_gram]
  have hf : (fun x =>
      ((transformedFrame U x.1 x.2).submatrix (fun j : T => j.1) id).transpose *
        ((transformedFrame U x.1 x.2).submatrix (fun j : T => j.1) id)) =
      (fun x => ∑ j : T, rowEffect U j.1 x) := by
    funext x
    exact (rowEffect_sum U T x).symm
  rw [hf,MatrixRepresentation.matrixMulOp_sum]
  exact (Finset.sum_coe_sort T (effect U)).symm

theorem effects_sum_one (U : Matrix (G k) (Fin d) ℝ)
    (hU : U.transpose*U=1) : ∑ j, effect U j = 1 := by
  have hf : (fun x => ∑ j, rowEffect U j x) = (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    funext x
    have ht := transformedFrame_transpose_mul U hU x.1 x.2
    convert ht using 1
    ext b c
    simp [Matrix.sum_apply,rowEffect,Matrix.mul_apply,Matrix.transpose_apply]
  change ∑ j, (basis k).matrixMulOp (rowEffect U j) = 1
  rw [← MatrixRepresentation.matrixMulOp_sum,hf,(basis k).matrixMulOp_one]

theorem effect_bandwidth (U : Matrix (G k) (Fin d) ℝ) (j : G k)
    (out inp : Fin d × SmallRows.SignPair (G k)) (h : effect U j out inp ≠ 0) :
    out.2.1.card ≤ inp.2.1.card+2 ∧ out.2.2.card ≤ inp.2.2.card+2 := by
  have he : effect U j = (liftedFrame U {j}).transpose * liftedFrame U {j} := by
    simpa using effect_sum_gram U {j}
  rw [he,Matrix.mul_apply] at h
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ho : liftedFrame U {j} a out ≠ 0 := by intro hz; simp [Matrix.transpose_apply,hz] at ha
  have hi : liftedFrame U {j} a inp ≠ 0 := by intro hz; simp [hz] at ha
  have hbo := liftedFrame_bandwidth U {j} a out ho
  have hbi := liftedFrame_bandwidth U {j} a inp hi
  constructor <;> omega

end
end SRHT.TwoSignRepresentation
