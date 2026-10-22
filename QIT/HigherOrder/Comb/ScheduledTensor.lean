/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Closure
public import QIT.HigherOrder.Comb.EventSchedule
public import QIT.Core.Map.LinkProductPositivity

/-!
# Tensor products scheduled in causal order

Independent combs can be interleaved whenever both original tooth orders are
preserved. This module describes their actual tensor-product operator on the
joint ordered input and output families.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder.Comb
open QIT.WireFam

/-- Reading a joint configuration along two component index maps. -/
def rankConfig {n nA nB : Nat} {I O : Fin n → Type u}
    (l : Fin nA → Fin n) (r : Fin nB → Fin n) (x : Space I O) :
    Space (fun i => I (l i)) (fun i => O (l i)) × Space (fun j => I (r j)) (fun j => O (r j)) :=
  (((fun i => x.1 (l i)), (fun i => x.2 (l i))),
    ((fun j => x.1 (r j)), (fun j => x.2 (r j))))

/-- The tensor product read in a joint family, through its component ranks. -/
def rankTensor {n nA nB : Nat} {I O : Fin n → Type u}
    (l : Fin nA → Fin n) (r : Fin nB → Fin n)
    (J : CMatrix (Space (fun i => I (l i)) (fun i => O (l i))))
    (K : CMatrix (Space (fun j => I (r j)) (fun j => O (r j)))) : CMatrix (Space I O) :=
  fun x y => J (rankConfig l r x).1 (rankConfig l r y).1 *
    K (rankConfig l r x).2 (rankConfig l r y).2

/-- Positivity needs no order assumptions. -/
theorem rankTensor_posSemidef {n nA nB : Nat} {I O : Fin n → Type u}
    [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
    (l : Fin nA → Fin n) (r : Fin nB → Fin n)
    {J : CMatrix (Space (fun i => I (l i)) (fun i => O (l i)))}
    {K : CMatrix (Space (fun j => I (r j)) (fun j => O (r j)))}
    (hJ : J.PosSemidef) (hK : K.PosSemidef) : (rankTensor l r J K).PosSemidef :=
  (hJ.kronecker hK).submatrix (rankConfig l r)

private theorem normalized_psd {n : Nat} {I O : Fin n → Type u}
    [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    {J : CMatrix (Space I O)} (hJ : Normalized I O J) : J.PosSemidef := by
  cases n with
  | zero => exact (normalized_zero I O J).mp hJ ▸ Matrix.PosSemidef.one
  | succ n => exact hJ.posSemidef

private theorem rankTensor_swap {n nA nB : Nat} {I O : Fin n → Type u}
    (l : Fin nA → Fin n) (r : Fin nB → Fin n)
    (J : CMatrix (Space (fun i => I (l i)) (fun i => O (l i))))
    (K : CMatrix (Space (fun j => I (r j)) (fun j => O (r j)))) :
    rankTensor l r J K = rankTensor r l K J := by
  ext x y
  exact mul_comm _ _

/-- Tensor normalization for two disjoint increasing rank maps covering every
joint event. No assumption that either component has positive length is needed. -/
theorem normalized_rankTensor {n nA nB : Nat} {I O : Fin n → Type u}
    [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (l : Fin nA → Fin n) (r : Fin nB → Fin n)
    (hl : StrictMono l) (hr : StrictMono r) (hd : ∀ i j, l i ≠ r j)
    (hc : ∀ t, (∃ i, l i = t) ∨ (∃ j, r j = t))
    {J : CMatrix (Space (fun i => I (l i)) (fun i => O (l i)))}
    {K : CMatrix (Space (fun j => I (r j)) (fun j => O (r j)))}
    (hJ : Normalized _ _ J) (hK : Normalized _ _ K) :
    Normalized I O (rankTensor l r J K) := by
  induction n generalizing nA nB with
  | zero =>
    have ha : nA = 0 := by
      by_contra h
      exact Fin.elim0 (l ⟨0, Nat.pos_of_ne_zero h⟩)
    have hb : nB = 0 := by
      by_contra h
      exact Fin.elim0 (r ⟨0, Nat.pos_of_ne_zero h⟩)
    subst nA; subst nB
    change J = 1 at hJ
    change K = 1 at hK
    change rankTensor l r J K = 1
    subst J; subst K
    ext x y
    simp [rankTensor, Matrix.one_apply, Subsingleton.elim x y]
  | succ n ih =>
    have step {a b : Nat} (l : Fin (a + 1) → Fin (n + 1)) (r : Fin b → Fin (n + 1))
        (hl : StrictMono l) (hr : StrictMono r) (hd : ∀ i j, l i ≠ r j)
        (hc : ∀ t, (∃ i, l i = t) ∨ (∃ j, r j = t)) (hf : l (Fin.last a) = Fin.last n)
        {J : CMatrix (Space (fun i => I (l i)) (fun i => O (l i)))}
        {K : CMatrix (Space (fun j => I (r j)) (fun j => O (r j)))}
        (hJ : Normalized _ _ J) (hK : Normalized _ _ K) :
        Normalized I O (rankTensor l r J K) := by
      have hll (i : Fin a) : (l i.castSucc).val < n := by
        have := hl (Fin.castSucc_lt_last i)
        simpa only [hf, Fin.lt_def, Fin.val_last] using this
      have hrr (j : Fin b) : (r j).val < n := by
        have hn : r j ≠ Fin.last n := by simpa only [hf] using (hd (Fin.last a) j).symm
        have := (r j).isLt
        have : (r j).val ≠ n := fun h => hn (Fin.ext h)
        omega
      let lp : Fin a → Fin n := fun i => ⟨(l i.castSucc).val, hll i⟩
      let rp : Fin b → Fin n := fun j => ⟨(r j).val, hrr j⟩
      have hlp : StrictMono lp := fun _ _ h => hl h
      have hrp : StrictMono rp := fun _ _ h => hr h
      have hdp : ∀ i j, lp i ≠ rp j := by
        intro i j he
        exact hd i.castSucc j (Fin.ext (congrArg (fun t : Fin n => t.val) he))
      have hcp (t : Fin n) : (∃ i, lp i = t) ∨ (∃ j, rp j = t) := by
        rcases hc t.castSucc with ⟨i, hi⟩ | ⟨j, hj⟩
        · cases i using Fin.lastCases with
          | last =>
            rw [hf] at hi
            exact (Fin.castSucc_ne_last t hi.symm).elim
          | cast i => exact Or.inl ⟨i, Fin.ext (congrArg (fun t : Fin (n + 1) => t.val) hi)⟩
        · exact Or.inr ⟨j, Fin.ext (congrArg (fun t : Fin (n + 1) => t.val) hj)⟩
      rcases hJ with ⟨hJpos, J₀, hJ₀, htrace⟩
      refine ⟨rankTensor_posSemidef l r hJpos (normalized_psd hK),
        rankTensor (I := fun t => I t.castSucc) (O := fun t => O t.castSucc) lp rp J₀ K,
        ih lp rp hlp hrp hdp hcp hJ₀ hK, ?_⟩
      intro x x' y y'
      let e : O (Fin.last n) ≃ O (l (Fin.last a)) := Equiv.cast (congrArg O hf.symm)
      have hleft (y : ∀ t : Fin n, O t.castSucc) (z : O (Fin.last n)) :
          (fun i => Fin.snoc y z (l i)) = Fin.snoc (fun i => y (lp i)) (e z) := by
        funext i
        cases i using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last]
          have hlast (t : Fin (n + 1)) (ht : t = Fin.last n) :
              Fin.snoc y z t = cast (congrArg O ht.symm) z := by
            subst t
            simp
          exact hlast _ hf
        | cast i =>
          exact (Fin.snoc_castSucc z y (lp i)).trans
            (Fin.snoc_castSucc (α := fun i => O (l i)) (e z) (fun i => y (lp i)) i).symm
      have hright (y : ∀ t : Fin n, O t.castSucc) (z : O (Fin.last n)) :
          (fun j => Fin.snoc y z (r j)) = (fun j => y (rp j)) := by
        funext j
        exact Fin.snoc_castSucc z y (rp j)
      simp only [rankTensor, rankConfig, hleft, hright]
      rw [← Finset.sum_mul]
      have hsum := e.sum_comp (fun z =>
        J ((fun i => x (l i)), Fin.snoc (fun i => y (lp i)) z)
          ((fun i => x' (l i)), Fin.snoc (fun i => y' (lp i)) z))
      rw [hsum]
      rw [htrace]
      have heq : (x (l (Fin.last a)) = x' (l (Fin.last a))) ↔
          (x (Fin.last n) = x' (Fin.last n)) := by rw [hf]
      simp only [heq]
      split
      · rfl
      · exact zero_mul _
    rcases hc (Fin.last n) with ⟨i, hi⟩ | ⟨j, hj⟩
    · cases nA with
      | zero => exact Fin.elim0 i
      | succ a =>
        have hf : l (Fin.last a) = Fin.last n := by
          apply le_antisymm (Fin.le_last _)
          rw [← hi]
          exact hl.monotone (Fin.le_last i)
        exact step l r hl hr hd hc hf hJ hK
    · cases nB with
      | zero => exact Fin.elim0 j
      | succ b =>
        have hf : r (Fin.last b) = Fin.last n := by
          apply le_antisymm (Fin.le_last _)
          rw [← hj]
          exact hr.monotone (Fin.le_last j)
        rw [rankTensor_swap]
        exact step r l hr hl (fun j i => (hd i j).symm) (fun t => (hc t).symm) hf hK hJ

/-- The dependent wire family at each event of a schedule. -/
def EventSchedule.family {nA nB : Nat} (s : EventSchedule nA nB)
    (I : Fin nA → Type u) (P : Fin nB → Type u) : Fin (nA + nB) → Type u :=
  fun t => Sum.elim I P (s.order t)

instance {nA nB : Nat} (s : EventSchedule nA nB)
    (I : Fin nA → Type u) (P : Fin nB → Type u)
    [∀ i, Fintype (I i)] [∀ j, Fintype (P j)] (t : Fin (nA + nB)) :
    Fintype (s.family I P t) := by
  unfold EventSchedule.family
  cases s.order t <;> dsimp <;> infer_instance

instance {nA nB : Nat} (s : EventSchedule nA nB)
    (I : Fin nA → Type u) (P : Fin nB → Type u)
    [∀ i, DecidableEq (I i)] [∀ j, DecidableEq (P j)] (t : Fin (nA + nB)) :
    DecidableEq (s.family I P t) := by
  unfold EventSchedule.family
  cases s.order t <;> dsimp <;> infer_instance

/-- Split a scheduled dependent tuple into the original component tuples. -/
def EventSchedule.tupleEquiv {nA nB : Nat} (s : EventSchedule nA nB)
    (I : Fin nA → Type u) (P : Fin nB → Type u) :
    (∀ t, s.family I P t) ≃ ((∀ i, I i) × (∀ j, P j)) :=
  (Equiv.piCongrLeft (Sum.elim I P) s.order).trans (Equiv.sumPiEquivProdPi _)

/-- The scheduled comb space is exactly the product of the two original spaces. -/
def EventSchedule.configEquiv {nA nB : Nat} (s : EventSchedule nA nB)
    (I O : Fin nA → Type u) (P Q : Fin nB → Type u) :
    Space (s.family I P) (s.family O Q) ≃ (Space I O × Space P Q) :=
  ((s.tupleEquiv I P).prodCongr (s.tupleEquiv O Q)).trans (Equiv.prodProdProdComm _ _ _ _)

/-- The tensor product of two comb operators in the schedule's coordinates. -/
def EventSchedule.tensor {nA nB : Nat} (s : EventSchedule nA nB)
    {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
    (J : CMatrix (Space I O)) (K : CMatrix (Space P Q)) :
    CMatrix (Space (s.family I P) (s.family O Q)) :=
  matReindex (s.configEquiv I O P Q).symm (Matrix.kronecker J K)

/-- The scheduled operator is the actual product of component matrix entries. -/
theorem EventSchedule.tensor_apply {nA nB : Nat} (s : EventSchedule nA nB)
    {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
    (J : CMatrix (Space I O)) (K : CMatrix (Space P Q))
    (x y : Space (s.family I P) (s.family O Q)) :
    s.tensor J K x y = J ((s.configEquiv I O P Q) x).1 ((s.configEquiv I O P Q) y).1 *
      K ((s.configEquiv I O P Q) x).2 ((s.configEquiv I O P Q) y).2 := rfl

/-- Tensor positivity is preserved by the schedule's configuration equivalence. -/
theorem EventSchedule.tensor_posSemidef {nA nB : Nat} (s : EventSchedule nA nB)
    {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
    [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
    [∀ j, Fintype (P j)] [∀ j, Fintype (Q j)]
    {J : CMatrix (Space I O)} {K : CMatrix (Space P Q)}
    (hJ : J.PosSemidef) (hK : K.PosSemidef) : (s.tensor J K).PosSemidef :=
  matReindex_posSemidef _ (hJ.kronecker hK)

/-- At a left event the scheduled family is the original left wire. -/
def EventSchedule.leftFamilyEquiv {nA nB : Nat} (s : EventSchedule nA nB)
    (I : Fin nA → Type u) (P : Fin nB → Type u) (i : Fin nA) :
    I i ≃ s.family I P (s.leftRank i) :=
  Equiv.cast (by simp [EventSchedule.family])

/-- At a right event the scheduled family is the original right wire. -/
def EventSchedule.rightFamilyEquiv {nA nB : Nat} (s : EventSchedule nA nB)
    (I : Fin nA → Type u) (P : Fin nB → Type u) (j : Fin nB) :
    P j ≃ s.family I P (s.rightRank j) :=
  Equiv.cast (by simp [EventSchedule.family])

/-- Rank extraction agrees with the configuration equivalence, including all
casts of heterogeneous wire types. -/
theorem EventSchedule.configEquiv_eq_rankConfig {nA nB : Nat} (s : EventSchedule nA nB)
    (I O : Fin nA → Type u) (P Q : Fin nB → Type u)
    (x : Space (s.family I P) (s.family O Q)) :
    s.configEquiv I O P Q x =
      ((spaceEquiv (s.leftFamilyEquiv I P) (s.leftFamilyEquiv O Q)).symm
        (rankConfig s.leftRank s.rightRank x).1,
       (spaceEquiv (s.rightFamilyEquiv I P) (s.rightFamilyEquiv O Q)).symm
        (rankConfig s.leftRank s.rightRank x).2) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change Equiv.piCongrLeft (Sum.elim I P) s.order x.1 (Sum.inl i) =
        (s.leftFamilyEquiv I P i).symm (x.1 (s.leftRank i))
      exact Equiv.piCongrLeft_apply_eq_cast x.1 (Sum.inl i)
    · funext i
      change Equiv.piCongrLeft (Sum.elim O Q) s.order x.2 (Sum.inl i) =
        (s.leftFamilyEquiv O Q i).symm (x.2 (s.leftRank i))
      exact Equiv.piCongrLeft_apply_eq_cast x.2 (Sum.inl i)
  · apply Prod.ext
    · funext j
      change Equiv.piCongrLeft (Sum.elim I P) s.order x.1 (Sum.inr j) =
        (s.rightFamilyEquiv I P j).symm (x.1 (s.rightRank j))
      exact Equiv.piCongrLeft_apply_eq_cast x.1 (Sum.inr j)
    · funext j
      change Equiv.piCongrLeft (Sum.elim O Q) s.order x.2 (Sum.inr j) =
        (s.rightFamilyEquiv O Q j).symm (x.2 (s.rightRank j))
      exact Equiv.piCongrLeft_apply_eq_cast x.2 (Sum.inr j)

/-- The actual scheduled tensor product of two normalized combs is normalized.
Both original tooth orders are preserved, and either component may be empty. -/
theorem EventSchedule.normalized_tensor {nA nB : Nat} (s : EventSchedule nA nB)
    {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
    [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    [∀ j, Fintype (P j)] [∀ j, DecidableEq (P j)]
    [∀ j, Fintype (Q j)] [∀ j, DecidableEq (Q j)]
    {J : CMatrix (Space I O)} {K : CMatrix (Space P Q)}
    (hJ : Normalized I O J) (hK : Normalized P Q K) :
    Normalized (s.family I P) (s.family O Q) (s.tensor J K) := by
  let eA := spaceEquiv (s.leftFamilyEquiv I P) (s.leftFamilyEquiv O Q)
  let eB := spaceEquiv (s.rightFamilyEquiv I P) (s.rightFamilyEquiv O Q)
  have hA := (Normalized.reindex_iff (s.leftFamilyEquiv I P) (s.leftFamilyEquiv O Q) J).mp hJ
  have hB := (Normalized.reindex_iff (s.rightFamilyEquiv I P) (s.rightFamilyEquiv O Q) K).mp hK
  have hc (t : Fin (nA + nB)) :
      (∃ i, s.leftRank i = t) ∨ (∃ j, s.rightRank j = t) := by
    cases he : s.order t with
    | inl i =>
      left
      exact ⟨i, by rw [EventSchedule.leftRank, ← he, s.order.symm_apply_apply]⟩
    | inr j =>
      right
      exact ⟨j, by rw [EventSchedule.rightRank, ← he, s.order.symm_apply_apply]⟩
  have hn := normalized_rankTensor (I := s.family I P) (O := s.family O Q) s.leftRank s.rightRank s.leftRank_strictMono
    s.rightRank_strictMono s.leftRank_ne_rightRank hc hA hB
  have he : rankTensor s.leftRank s.rightRank (matReindex eA J) (matReindex eB K) =
      s.tensor J K := by
    ext x y
    simp only [EventSchedule.tensor_apply, EventSchedule.configEquiv_eq_rankConfig,
      rankTensor, matReindex_apply, eA, eB]
  exact he ▸ hn

end QIT.HigherOrder.Comb
