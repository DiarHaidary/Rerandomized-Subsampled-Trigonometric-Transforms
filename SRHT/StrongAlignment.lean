import SRHT.Alignment
import SRHT.SupportMiss

/-! Appendix A.4: the disjoint signed-character alignment family. -/
namespace SRHT.StrongAlignment
noncomputable section
open SparseFock Alignment
open scoped BigOperators Matrix
variable {k : ℕ}

abbrev Label (k : ℕ) := ZMod 2 × WalshIndex k

def pattern (l : Label k) (z : WalshIndex k) : ZMod 2 :=
  l.1 + ∑ i, l.2 i*z i

theorem bitSign_sum {I : Type*} (S : Finset I) (f : I → ZMod 2) :
    bitSign (∑ i∈S,f i) = ∏ i∈S,bitSign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi,bitSign_add,ih]

theorem pattern_sign (l : Label k) (z : WalshIndex k) :
    bitSign (pattern l z) = bitSign l.1*walshChar l.2 z := by
  rw [pattern,bitSign_add,bitSign_sum]
  rfl

theorem pattern_injective : Function.Injective (pattern (k:=k)) := by
  intro l m h
  have he : l.1=m.1 := by
    have hh := congrFun h 0
    simpa [pattern] using hh
  apply Prod.ext he
  funext i
  have hh := congrFun h (Pi.single i 1)
  simpa [pattern,he,Pi.single_apply,mul_ite] using hh

def horizontalStrip (b : WalshIndex k) (f : WalshIndex k → ℝ) : Site k → ℝ :=
  fun i => if i.2=b then f i.1 else 0

def verticalStrip (a : WalshIndex k) (f : WalshIndex k → ℝ) : Site k → ℝ :=
  fun i => if i.1=a then f i.2 else 0

theorem tensor_horizontalStrip (b : WalshIndex k) (f : WalshIndex k → ℝ)
    (r s : WalshIndex k) :
    (tensorWalsh k).mulVec (horizontalStrip b f) (r,s) =
      walshMatrix k s b*((walshMatrix k).mulVec f r) := by
  classical
  simp only [Matrix.mulVec,dotProduct,tensorWalsh,Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply,
    Fintype.sum_prod_type,horizontalStrip,mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem tensor_verticalStrip (a : WalshIndex k) (f : WalshIndex k → ℝ)
    (r s : WalshIndex k) :
    (tensorWalsh k).mulVec (verticalStrip a f) (r,s) =
      walshMatrix k r a*((walshMatrix k).mulVec f s) := by
  classical
  simp only [Matrix.mulVec,dotProduct,tensorWalsh,Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply,
    Fintype.sum_prod_type,verticalStrip,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem walsh_signed_row (a : WalshIndex k) (e : ℝ) (r : WalshIndex k) :
    (walshMatrix k).mulVec (fun i => e*walshMatrix k a i) r =
      if r=a then e else 0 := by
  have hh := congrArg (fun A : Matrix (WalshIndex k) (WalshIndex k) ℝ => A r a)
    (walshMatrix_mul_self k)
  have ht (i : WalshIndex k) : walshMatrix k a i=walshMatrix k i a := by
    exact congrArg (fun A : Matrix (WalshIndex k) (WalshIndex k) ℝ => A i a)
      (walshMatrix_transpose k)
  simp only [Matrix.mulVec,dotProduct,ht]
  calc
    _ = e*∑ i,walshMatrix k r i*walshMatrix k i a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [show (∑ i,walshMatrix k r i*walshMatrix k i a)=if r=a then 1 else 0 by
        simpa [Matrix.mul_apply,Matrix.one_apply] using hh]
      split_ifs <;> simp

def firstEvent (l : Label k) : Set (Signs k) :=
  {x | ∀ i, x (i,0)=pattern l i}

def secondEvent (a : WalshIndex k) (l : Label k) : Set (Signs k) :=
  {y | ∀ i, y (a,i)=pattern l i}

def firstState (l : Label k) : Site k → ℝ :=
  verticalStrip l.2 (fun _ => bitSign l.1*flat k)

def finalState (l m : Label k) : Site k → ℝ :=
  horizontalStrip m.2 (fun r => bitSign l.1*bitSign m.1*walshMatrix k r l.2)

theorem first_signAction (l : Label k) (x : Signs k) (hx : x∈firstEvent l) :
    signAction x (horizontal k) =
      horizontalStrip 0 (fun i => bitSign l.1*walshMatrix k l.2 i) := by
  funext ⟨i,j⟩
  by_cases hj : j=0
  · subst j
    simp only [signAction,horizontal,horizontalStrip,if_true,hx i,pattern_sign,
      walshMatrix_apply,flat]
    ring
  · simp [signAction,horizontal,horizontalStrip,hj]

theorem first_alignment (l : Label k) (x : Signs k) (hx : x∈firstEvent l) :
    step x (horizontal k)=firstState l := by
  unfold step
  rw [first_signAction l x hx]
  funext ⟨r,s⟩
  rw [tensor_horizontalStrip,walsh_signed_row]
  simp only [firstState,verticalStrip,walshMatrix_apply,walshChar_zero_right,mul_one]
  split_ifs <;> simp [flat,mul_comm]

theorem second_signAction (l m : Label k) (y : Signs k) (hy : y∈secondEvent l.2 m) :
    signAction y (firstState l) =
      verticalStrip l.2 (fun i => (bitSign l.1*bitSign m.1)*walshMatrix k m.2 i) := by
  funext ⟨i,j⟩
  by_cases hi : i=l.2
  · subst i
    simp only [signAction,firstState,verticalStrip,if_true,hy j,pattern_sign,
      walshMatrix_apply,flat]
    ring
  · simp [signAction,firstState,verticalStrip,hi]

theorem second_alignment (l m : Label k) (y : Signs k) (hy : y∈secondEvent l.2 m) :
    step y (firstState l)=finalState l m := by
  unfold step
  rw [second_signAction l m y hy]
  funext ⟨r,s⟩
  rw [tensor_verticalStrip,walsh_signed_row]
  simp only [finalState,horizontalStrip]
  split_ifs <;> simp [mul_comm,mul_left_comm,mul_assoc]

def horizontalSet (b : WalshIndex k) : Finset (Site k) := Finset.univ ×ˢ {b}
def verticalSet (a : WalshIndex k) : Finset (Site k) := {a} ×ˢ Finset.univ

@[simp] theorem horizontalSet_card (b : WalshIndex k) : (horizontalSet b).card=2^k := by
  simp [horizontalSet]

@[simp] theorem verticalSet_card (a : WalshIndex k) : (verticalSet a).card=2^k := by
  simp [verticalSet]

theorem firstEvent_probability (l : Label k) :
    (bitLaw k).prob (firstEvent l) = (1/2:ℝ)^(2^k) := by
  have he : firstEvent l = {x | ∀ i∈horizontalSet (0:WalshIndex k), x i=pattern l i.1} := by
    ext x
    simp [firstEvent,horizontalSet]
  rw [he,pattern_probability,horizontalSet_card]

theorem secondEvent_probability (a : WalshIndex k) (l : Label k) :
    (bitLaw k).prob (secondEvent a l) = (1/2:ℝ)^(2^k) := by
  have he : secondEvent a l = {x | ∀ i∈verticalSet a, x i=pattern l i.2} := by
    ext x
    simp [secondEvent,verticalSet]
  rw [he,pattern_probability,verticalSet_card]

theorem firstEvent_unique {l m : Label k} {x : Signs k}
    (hl : x∈firstEvent l) (hm : x∈firstEvent m) : l=m := by
  apply pattern_injective
  funext i
  exact (hl i).symm.trans (hm i)

theorem secondEvent_unique {a : WalshIndex k} {l m : Label k} {x : Signs k}
    (hl : x∈secondEvent a l) (hm : x∈secondEvent a m) : l=m := by
  apply pattern_injective
  funext i
  exact (hl i).symm.trans (hm i)

theorem bitSign_ne_zero (b : ZMod 2) : bitSign b≠0 := by
  unfold bitSign
  split_ifs <;> norm_num

theorem walshEntry_ne_zero (a b : WalshIndex k) : walshMatrix k a b≠0 := by
  rw [walshMatrix_apply]
  apply mul_ne_zero (ne_of_gt (flat_pos k))
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => bitSign_ne_zero _)

theorem finalState_support (l m : Label k) : support (finalState l m)=horizontalSet m.2 := by
  have hc (i : WalshIndex k) : bitSign l.1*bitSign m.1*walshMatrix k i l.2≠0 :=
    mul_ne_zero (mul_ne_zero (bitSign_ne_zero _) (bitSign_ne_zero _)) (walshEntry_ne_zero _ _)
  ext ⟨i,j⟩
  simp [support,finalState,horizontalStrip,horizontalSet,hc]
  exact eq_comm

theorem finalState_support_card (l m : Label k) : (support (finalState l m)).card=2^k := by
  rw [finalState_support,horizontalSet_card]

theorem product_probability {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : FiniteLaw B) (s : Set A) (t : Set B) :
    (μ.product ν).prob {z | z.1∈s ∧ z.2∈t}=μ.prob s*ν.prob t := by
  classical
  rw [FiniteLaw.product_prob_eq_iterated]
  have h (a : A) : ν.prob {b | (a,b)∈{z : A×B | z.1∈s ∧ z.2∈t}} =
      FiniteLaw.indicator s a*ν.prob t := by
    by_cases ha : a∈s
    · simp [ha,FiniteLaw.indicator]
    · simp [ha,FiniteLaw.indicator]
  simp_rw [h]
  calc
    _ = μ.expect (fun a => ν.prob t*FiniteLaw.indicator s a) := by
      apply μ.expect_congr
      intro a
      ring
    _ = ν.prob t*μ.prob s := FiniteLaw.expect_smul _ _ _
    _ = _ := mul_comm _ _

theorem sum_probability_le_of_unique {A Ω : Type*} [Fintype A] [Fintype Ω]
    (μ : FiniteLaw Ω) (E : A → Set Ω) (bad : Set Ω)
    (huniq : ∀ ω a b, ω∈E a → ω∈E b → a=b)
    (hsub : ∀ a, E a⊆bad) : (∑ a,μ.prob (E a))≤μ.prob bad := by
  classical
  have he : (∑ a,μ.prob (E a)) = μ.expect (fun ω => ∑ a,FiniteLaw.indicator (E a) ω) := by
    simp only [FiniteLaw.prob,FiniteLaw.expect,Finset.mul_sum]
    exact Finset.sum_comm
  rw [he,FiniteLaw.prob]
  apply μ.expect_mono
  intro ω
  by_cases hex : ∃ a,ω∈E a
  · obtain ⟨a,ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · simp [FiniteLaw.indicator,ha,hsub a ha]
    · intro b hb hba
      have hnot : ω∉E b := fun h => hba (huniq ω b a h ha)
      simp [FiniteLaw.indicator,hnot]
    · simp
  · push_neg at hex
    have hz : (∑ a,FiniteLaw.indicator (E a) ω)=0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp [FiniteLaw.indicator,hex a]
    rw [hz]
    unfold FiniteLaw.indicator
    split_ifs <;> norm_num

def missEvent {M : ℕ} (l m : Label k) :
    Set (Signs k × (Signs k × Sampling.Exact (Site k) M)) :=
  {z | z.1∈firstEvent l ∧ z.2.1∈secondEvent l.2 m ∧ Disjoint z.2.2.val (horizontalSet m.2)}

theorem missEvent_probability {M : ℕ} (hM : M≤Fintype.card (Site k)) (l m : Label k) :
    ((bitLaw k).product ((bitLaw k).product (SupportMiss.missLaw hM))).prob (missEvent l m) =
      ((1/2:ℝ)^(2^k))^2 * SupportMiss.missRatio ((2^k)^2) (2^k) M := by
  change ((bitLaw k).product ((bitLaw k).product (SupportMiss.missLaw hM))).prob
    {z | z.1∈firstEvent l ∧ z.2∈{v | v.1∈secondEvent l.2 m ∧ Disjoint v.2.val (horizontalSet m.2)}} = _
  rw [product_probability]
  have hsecond := product_probability (bitLaw k) (SupportMiss.missLaw hM) (secondEvent l.2 m)
    {T | Disjoint T.val (horizontalSet m.2)}
  simp only [Set.mem_setOf_eq] at hsecond
  rw [hsecond]
  rw [firstEvent_probability,secondEvent_probability,
    SupportMiss.miss_probability,horizontalSet_card]
  simp only [Fintype.card_prod,walshIndex_card]
  rw [show 2^k*2^k=(2^k)^2 by ring]
  ring

theorem missEvent_unique {M : ℕ} (z : Signs k × (Signs k × Sampling.Exact (Site k) M))
    (a b : Label k × Label k) (ha : z∈missEvent a.1 a.2) (hb : z∈missEvent b.1 b.2) : a=b := by
  have h1 : a.1=b.1 := firstEvent_unique ha.1 hb.1
  have h2 : a.2=b.2 := secondEvent_unique ha.2.1 (by simpa only [h1] using hb.2.1)
  exact Prod.ext h1 h2

theorem missEvent_failure {M : ℕ} (ε : ℝ) (hε : ε<1) (l m : Label k)
    (z : Signs k × (Signs k × Sampling.Exact (Site k) M)) (hz : z∈missEvent l m) :
    sampleEnergy (step z.2.1 (step z.1 (horizontal k))) z.2.2.val < 1-ε := by
  rw [first_alignment l z.1 hz.1,second_alignment l m z.2.1 hz.2.1]
  have hdisj : Disjoint z.2.2.val (support (finalState l m)) := by
    rw [finalState_support]
    exact hz.2.2
  rw [sampleEnergy_eq_zero_of_disjoint _ _ hdisj]
  linarith

/-- Appendix A.4: the complete 2L-by-2L disjoint signed-character family.
Its final support has L sites, so uniform sampling misses it with the exact
hypergeometric ratio. The endpoint uses the literal two-round sampled energy. -/
theorem two_round_failure_lower {M : ℕ} (hM : M≤Fintype.card (Site k))
    (ε : ℝ) (hε0 : 0<ε) (hε1 : ε<1) :
    (2*(2^k:ℝ)*(1/2:ℝ)^(2^k))^2 * SupportMiss.missRatio ((2^k)^2) (2^k) M ≤
      ((bitLaw k).product ((bitLaw k).product (SupportMiss.missLaw hM))).prob
        {z | sampleEnergy (step z.2.1 (step z.1 (horizontal k))) z.2.2.val < 1-ε} := by
  have hh := sum_probability_le_of_unique
    ((bitLaw k).product ((bitLaw k).product (SupportMiss.missLaw hM)))
    (fun a : Label k × Label k => missEvent a.1 a.2)
    {z | sampleEnergy (step z.2.1 (step z.1 (horizontal k))) z.2.2.val < 1-ε}
    missEvent_unique (fun a z hz => missEvent_failure ε hε1 a.1 a.2 z hz)
  simp_rw [missEvent_probability hM] at hh
  have hn : Fintype.card (Label k × Label k)=(2*(2^k))^2 := by
    simp [Label,pow_two]
  simp only [Finset.sum_const,Finset.card_univ,hn,nsmul_eq_mul] at hh
  convert hh using 1
  push_cast
  ring

end
end SRHT.StrongAlignment
