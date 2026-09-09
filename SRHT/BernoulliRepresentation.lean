import SRHT.TwoSignRepresentation
import SRHT.VacuumMoment

/-! The Bernoulli Gram error as an exact three-register multiplication matrix. -/
namespace SRHT.BernoulliRepresentation
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix SparseFock.FiniteL2 SRHT.HardCore TwoSignRepresentation

variable {k d : ℕ}

def basis (k : ℕ) (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    WeightedONBasis ((SignAssignment k × SignAssignment k) × SignAssignment k)
      (SmallRows.SignPair (G k) × Finset (G k)) :=
  ProductBasis.prod (TwoSignRepresentation.basis k) (OccupationBasis.bernoulli p hp hp1)

@[simp] theorem basis_vacuum (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (basis k p hp hp1).vacuum = ((∅,∅),∅) := by
  simp [basis,ProductBasis.prod]

def error (U : Matrix (G k) (Fin d) ℝ) (p : ℝ)
    (x : (SignAssignment k × SignAssignment k) × SignAssignment k) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ j, (BinaryBasis.bitValue (x.2 j)/p-1) • rowEffect U j x.1

theorem error_symmetric (U : Matrix (G k) (Fin d) ℝ) (p : ℝ) (x) :
    (error U p x).transpose = error U p x := by
  ext b c
  simp only [error,Matrix.transpose_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,rowEffect]
  apply Finset.sum_congr rfl
  intro j _
  ring

def selector (p : ℝ) (j : G k) : Op (G k) :=
  Real.sqrt ((1-p)/p) • (create j+annihilate j) + ((1-2*p)/p) • number j

def operator (U : Matrix (G k) (Fin d) ℝ) (p : ℝ) :
    Matrix ((Fin d × SmallRows.SignPair (G k)) × Finset (G k))
      ((Fin d × SmallRows.SignPair (G k)) × Finset (G k)) ℝ :=
  ∑ j, Matrix.kronecker (effect U j) (selector p j)

theorem multiplication_eq (U : Matrix (G k) (Fin d) ℝ)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (basis k p hp hp1).matrixMulOp (error U p) =
      (operator U p).submatrix (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm := by
  unfold error
  rw [MatrixRepresentation.matrixMulOp_sum]
  ext out inp
  simp only [operator,Matrix.sum_apply,Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap,
    Equiv.prodAssoc_symm_apply]
  apply Finset.sum_congr rfl
  intro j _
  have h := TwoSignRepresentation.prod_mulOp_factor
    (TwoSignRepresentation.basis k) (OccupationBasis.bernoulli (G:=G k) p hp hp1)
    (fun x => rowEffect U j x out.1 inp.1)
    (fun z => BinaryBasis.bitValue (z j)/p-1) out.2 inp.2
  rw [OccupationBasis.bernoulli_mulOp] at h
  change (basis k p hp hp1).coeff out.2 (fun x =>
    ((BinaryBasis.bitValue (x.2 j)/p-1) * rowEffect U j x.1 out.1 inp.1) *
      (basis k p hp hp1).basis inp.2 x) = _
  have hc : (fun x : (SignAssignment k × SignAssignment k) × SignAssignment k =>
      ((BinaryBasis.bitValue (x.2 j)/p-1) * rowEffect U j x.1 out.1 inp.1) *
        (basis k p hp hp1).basis inp.2 x) =
      (fun x => (rowEffect U j x.1 out.1 inp.1 * (BinaryBasis.bitValue (x.2 j)/p-1)) *
        (basis k p hp hp1).basis inp.2 x) := by funext x; ring
  rw [hc]
  exact h

theorem selector_bandwidth (p : ℝ) (j : G k) (S T : Finset (G k))
    (h : selector p j S T ≠ 0) : S.card ≤ T.card+1 := by
  by_cases hf : flip j S T=0
  · have hn : number j S T≠0 := by
      intro hz
      change Real.sqrt ((1-p)/p) * TwoSignRepresentation.flip j S T +
        ((1-2*p)/p) * number j S T ≠ 0 at h
      rw [hf,hz] at h
      simp at h
    have he : S=T := by
      by_contra he
      simp [number_apply,he] at hn
    rw [he]
    omega
  · exact (flip_card j S T hf).1

theorem operator_bandwidth (U : Matrix (G k) (Fin d) ℝ) (p : ℝ)
    (out inp : (Fin d × SmallRows.SignPair (G k)) × Finset (G k))
    (h : operator U p out inp ≠ 0) :
    out.1.2.1.card ≤ inp.1.2.1.card+2 ∧ out.1.2.2.card ≤ inp.1.2.2.card+2 ∧
      out.2.card ≤ inp.2.card+1 := by
  simp only [operator,Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap] at h
  obtain ⟨j,_,hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have he : effect U j out.1 inp.1≠0 := by intro hz; simp [hz] at hj
  have hs : selector p j out.2 inp.2≠0 := by intro hz; simp [hz] at hj
  exact ⟨(effect_bandwidth U j _ _ he).1,(effect_bandwidth U j _ _ he).2,
    selector_bandwidth p j _ _ hs⟩

def reachable (k d r : ℕ) : Finset (Fin d × (SmallRows.SignPair (G k) × Finset (G k))) :=
  Finset.univ.filter fun z => z.2.1.1.card ≤ 2*r ∧ z.2.1.2.card ≤ 2*r ∧ z.2.2.card ≤ r

theorem vacuum_reachable (a : Fin d) : (a,((∅,∅),∅)) ∈ reachable k d 0 := by
  simp [reachable]

theorem reachable_mono {r q : ℕ} (h : r≤q) : reachable k d r ⊆ reachable k d q := by
  intro z hz
  simp only [reachable,Finset.mem_filter,Finset.mem_univ,true_and] at *
  omega

theorem multiplication_reachable (U : Matrix (G k) (Fin d) ℝ)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) (r : ℕ)
    (out inp : Fin d × (SmallRows.SignPair (G k) × Finset (G k)))
    (hi : inp ∈ reachable k d r)
    (h : (basis k p hp hp1).matrixMulOp (error U p) out inp ≠ 0) :
    out ∈ reachable k d (r+1) := by
  rw [multiplication_eq] at h
  have hb := operator_bandwidth U p _ _ h
  simp only [Equiv.prodAssoc_symm_apply] at hb
  simp only [reachable,Finset.mem_filter,Finset.mem_univ,true_and] at *
  omega

end
end SRHT.BernoulliRepresentation
