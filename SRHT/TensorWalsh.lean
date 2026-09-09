import SRHT.Alignment

/-! The tensor Walsh model of Appendix A is an ordinary Walsh matrix with
its binary coordinates regrouped into two halves. -/
namespace SRHT.Alignment
noncomputable section
open scoped BigOperators

def splitIndex (k : ℕ) : WalshIndex (k+k) ≃ Site k where
  toFun a := (fun i => a (Fin.castAdd k i), fun i => a (Fin.natAdd k i))
  invFun a := Fin.append a.1 a.2
  left_inv a := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  right_inv a := by
    apply Prod.ext
    · funext i; exact Fin.append_left _ _ i
    · funext i; exact Fin.append_right _ _ i

theorem walshChar_append (k : ℕ) (a b : Site k) :
    walshChar (Fin.append a.1 a.2) (Fin.append b.1 b.2) =
      walshChar a.1 b.1 * walshChar a.2 b.2 := by
  simp only [walshChar, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- Equality of the actual normalized matrices after an explicit bijective
relabeling.  In particular the tensor model introduces no new transform. -/
theorem tensorWalsh_eq_reindex (k : ℕ) :
    tensorWalsh k = (walshMatrix (k+k)).submatrix (splitIndex k).symm (splitIndex k).symm := by
  ext ⟨a,b⟩ ⟨c,d⟩
  change walshMatrix k a c * walshMatrix k b d =
    walshMatrix (k+k) (Fin.append a b) (Fin.append c d)
  simp only [walshMatrix_apply, pow_add,
    Real.sqrt_mul (show (0:ℝ) ≤ 2^k by positivity), mul_inv_rev]
  rw [walshChar_append k (a,b) (c,d)]
  dsimp
  ring

end
end SRHT.Alignment
