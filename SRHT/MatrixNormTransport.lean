import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Explicit transport of the concrete L2 matrix norm across finite-type
instances. This only changes instance witnesses, not the operator norm. -/
namespace SRHT.MatrixNormTransport
noncomputable section
open scoped Matrix.Norms.L2Operator

theorem norm_independent_of_fintype {I J : Type*}
    (fI gI : Fintype I) (fJ gJ : Fintype J)
    (dI eI : DecidableEq I) (dJ eJ : DecidableEq J)
    (A : Matrix I J ℝ) :
    (letI := fI; letI := fJ; letI := dI; letI := dJ; ‖A‖) =
    (letI := gI; letI := gJ; letI := eI; letI := eJ; ‖A‖) := by
  cases Subsingleton.elim fI gI
  cases Subsingleton.elim fJ gJ
  cases Subsingleton.elim dI eI
  cases Subsingleton.elim dJ eJ
  rfl

theorem square_norm_independent_of_fintype {I : Type*}
    (f g : Fintype I) (d e : DecidableEq I) (A : Matrix I I ℝ) :
    (letI := f; letI := d; ‖A‖) = (letI := g; letI := e; ‖A‖) := by
  cases Subsingleton.elim f g
  cases Subsingleton.elim d e
  rfl

theorem square_addCommGroup_norm_eq_ring_norm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) :
    @Norm.norm (Matrix I I ℝ)
      (@NormedAddCommGroup.toNorm _ (Matrix.instL2OpNormedAddCommGroup (𝕜:=ℝ))) A =
    @Norm.norm (Matrix I I ℝ)
      (@NormedRing.toNorm _ (Matrix.instL2OpNormedRing (𝕜:=ℝ))) A := by
  rfl

theorem square_addCommGroup_norm_instance_eq_ring_norm {I : Type*} [Fintype I] [DecidableEq I] :
    (@NormedAddCommGroup.toNorm (Matrix I I ℝ) (Matrix.instL2OpNormedAddCommGroup (𝕜:=ℝ))) =
    (@NormedRing.toNorm (Matrix I I ℝ) (Matrix.instL2OpNormedRing (𝕜:=ℝ))) := by
  rfl

end
end SRHT.MatrixNormTransport
