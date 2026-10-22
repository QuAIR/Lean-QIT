/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.PortReplacement

/-!
# A forward connection within a normalized comb

Connecting an earlier output to a later input is a positive matrix compression.
The consumed ports retain their positions with unit types. Recursive normalization
follows by commuting the contraction with the final output trace, or, when the
connection enters the final tooth, by collapsing its input identity and discarding
the earlier output. This lemma permits empty wire types.

This is a single-connection primitive for the network composition described in
[Chiribella2009Networks, comblong-pub.tex:1279-1286], whose join conditions at
lines 1233-1243 of the same source require acyclic composition. Iterating a general
matching and identifying it with the raw matched-wire link product remain separate
obligations; this module does not assert that integration theorem.
-/

@[expose] public section
open QIT
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
universe u
namespace QIT.HigherOrder.Comb

/-- Contract matching basis values in an output and an input. The algebraic
operation is defined for any two positions; normalization requires `a < b`. -/
def forwardContraction {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (O j)] (a b : Fin n) (e : O a ≃ I b)
    (J : CMatrix (Space I O)) :
    CMatrix (Space (erasePort I b.val) (erasePort O a.val)) :=
  sumCompression (fun p z => (fillPort I b p.1 (e z), fillPort O a p.2 z)) J

/-- Independent row and column sums for the actual connected ports. -/
@[simp] theorem forwardContraction_apply {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (O j)] (a b : Fin n) (e : O a ≃ I b)
    (J : CMatrix (Space I O)) (p q : Space (erasePort I b.val) (erasePort O a.val)) :
    forwardContraction a b e J p q = ∑ z, ∑ z',
      J (fillPort I b p.1 (e z), fillPort O a p.2 z)
        (fillPort I b q.1 (e z'), fillPort O a q.2 z') := rfl

/-- Forward contraction is positive by rectangular matrix congruence. -/
theorem forwardContraction_posSemidef {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (I j)] [∀ j, Fintype (O j)]
    (a b : Fin n) (e : O a ≃ I b) {J : CMatrix (Space I O)}
    (hJ : J.PosSemidef) : (forwardContraction a b e J).PosSemidef :=
  sumCompression_posSemidef _ hJ

private theorem forwardContraction_trace_prefix {n : Nat} {I O : Fin (n+1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (a b : Fin n) (e : O a.castSucc ≃ I b.castSucc)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin n => I j.castSucc) (fun j => O j.castSucc)))
    (htrace : ∀ i i' o o', (∑ z, J (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
      if i (Fin.last n) = i' (Fin.last n) then
        K ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o') else 0)
    (i i' : ∀ j, erasePort I b.val j)
    (o o' : ∀ j : Fin n, erasePort O a.val j.castSucc) :
    (∑ t, forwardContraction a.castSucc b.castSucc e J (i, Fin.snoc o t) (i', Fin.snoc o' t)) =
      if i (Fin.last n) = i' (Fin.last n) then
        forwardContraction a b e K ((fun j => i j.castSucc),o) ((fun j => i' j.castSucc),o') else 0 := by
  classical
  have heach (z z' : O a.castSucc) :
      (∑ t, J (fillPort I b.castSucc i (e z), fillPort O a.castSucc (Fin.snoc o t) z)
        (fillPort I b.castSucc i' (e z'), fillPort O a.castSucc (Fin.snoc o' t) z')) =
      if i (Fin.last n) = i' (Fin.last n) then
        K (fillPort (fun j : Fin n => I j.castSucc) b (fun j => i j.castSucc) (e z),
            fillPort (fun j : Fin n => O j.castSucc) a o z)
          (fillPort (fun j : Fin n => I j.castSucc) b (fun j => i' j.castSucc) (e z'),
            fillPort (fun j : Fin n => O j.castSucc) a o' z') else 0 := by
    simp_rw [fillPort_snoc_castSucc]
    trans ∑ t : O (Fin.last n), J
      (fillPort I b.castSucc i (e z), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o z) t)
      (fillPort I b.castSucc i' (e z'), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o' z') t)
    · exact (erasePortEquiv O a.val (Fin.last n) (Nat.ne_of_gt a.isLt)).sum_comp
        (fun t : O (Fin.last n) => J
          (fillPort I b.castSucc i (e z), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o z) t)
          (fillPort I b.castSucc i' (e z'), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o' z') t))
    rw [htrace]
    simp only [fillPort_castSucc, fillPort_last_of_castSucc]
    have hi : (cast (by simp [erasePort, Nat.ne_of_gt b.isLt]) (i (Fin.last n)) : I (Fin.last n)) =
        cast (by simp [erasePort, Nat.ne_of_gt b.isLt]) (i' (Fin.last n)) ↔
        i (Fin.last n) = i' (Fin.last n) :=
      (erasePortEquiv I b.val (Fin.last n) (Nat.ne_of_gt b.isLt)).injective.eq_iff
    simp only [hi]
  simp only [forwardContraction_apply]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext z; rw [Finset.sum_comm]
  simp_rw [heach]
  split_ifs <;> simp


private theorem forwardContraction_trace_last {n : Nat} {I O : Fin (n+1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (a : Fin n) (e : O a.castSucc ≃ I (Fin.last n))
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin n => I j.castSucc) (fun j => O j.castSucc)))
    (htrace : ∀ i i' o o', (∑ z, J (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
      if i (Fin.last n) = i' (Fin.last n) then
        K ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o') else 0)
    (i i' : ∀ j, erasePort I n j)
    (o o' : ∀ j : Fin n, erasePort O a.val j.castSucc) :
    (∑ t, forwardContraction a.castSucc (Fin.last n) e J (i, Fin.snoc o t) (i', Fin.snoc o' t)) =
      discardOutput a K
        ((fun j => erasePortEquiv I n j.castSucc (Nat.ne_of_lt j.isLt) (i j.castSucc)),o)
        ((fun j => erasePortEquiv I n j.castSucc (Nat.ne_of_lt j.isLt) (i' j.castSucc)),o') := by
  classical
  have heach (z z' : O a.castSucc) :
      (∑ t, J (fillPort I (Fin.last n) i (e z), fillPort O a.castSucc (Fin.snoc o t) z)
        (fillPort I (Fin.last n) i' (e z'), fillPort O a.castSucc (Fin.snoc o' t) z')) =
      if z = z' then
        K ((fun j => erasePortEquiv I n j.castSucc (Nat.ne_of_lt j.isLt) (i j.castSucc)),
            fillPort (fun j : Fin n => O j.castSucc) a o z)
          ((fun j => erasePortEquiv I n j.castSucc (Nat.ne_of_lt j.isLt) (i' j.castSucc)),
            fillPort (fun j : Fin n => O j.castSucc) a o' z') else 0 := by
    simp_rw [fillPort_snoc_castSucc]
    trans ∑ t : O (Fin.last n), J
      (fillPort I (Fin.last n) i (e z), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o z) t)
      (fillPort I (Fin.last n) i' (e z'), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o' z') t)
    · exact (erasePortEquiv O a.val (Fin.last n) (Nat.ne_of_gt a.isLt)).sum_comp
        (fun t : O (Fin.last n) => J
          (fillPort I (Fin.last n) i (e z), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o z) t)
          (fillPort I (Fin.last n) i' (e z'), Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) a o' z') t))
    rw [htrace]
    simp only [fillPort_at, e.injective.eq_iff]
    have hrestrict (v : ∀ j, erasePort I n j) (w : I (Fin.last n)) :
        (fun j : Fin n => fillPort I (Fin.last n) v w j.castSucc) =
        (fun j : Fin n => erasePortEquiv I n j.castSucc (Nat.ne_of_lt j.isLt) (v j.castSucc)) := by
      funext j
      exact fillPort_of_ne I (Fin.last n) j.castSucc v w (Nat.ne_of_lt j.isLt)
    simp only [hrestrict]
  simp only [forwardContraction_apply]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext z; rw [Finset.sum_comm]
  simp_rw [heach]
  simp [discardOutput_apply]


set_option maxHeartbeats 800000 in
/-- A strictly forward connection preserves normalization on the unit-padded
boundary, without requiring any wire to be inhabited. -/
theorem Normalized.forwardContraction {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (a b : Fin n) (hab : a < b) (e : O a ≃ I b)
    {J : CMatrix (Space I O)} (hJ : Normalized I O J) :
    Normalized (erasePort I b.val) (erasePort O a.val) (forwardContraction a b e J) := by
  classical
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    obtain ⟨hpsd, K, hK, htrace⟩ := hJ
    refine Fin.lastCases ?_ (fun b => ?_) b e hab
    · intro e hab
      refine Fin.lastCases ?_ (fun a => ?_) a e hab
      · intro e hab
        exact (lt_irrefl _ hab).elim
      · intro e _
        let eI : ∀ j : Fin n, I j.castSucc ≃ erasePort I n j.castSucc :=
          fun j => (erasePortEquiv I n j.castSucc (Nat.ne_of_lt j.isLt)).symm
        let K' := QIT.WireFam.matReindex
          (spaceEquiv eI (fun j : Fin n => Equiv.refl (erasePort O a.val j.castSucc)))
          (Comb.discardOutput a K)
        refine ⟨forwardContraction_posSemidef _ _ _ hpsd, K',
          (Normalized.reindex_iff _ _ _).mp (hK.discardOutput a), ?_⟩
        intro i i' o o'
        have hi : i (Fin.last n) = i' (Fin.last n) :=
          (erasePortUnitEquiv I (Fin.last n)).injective (Subsingleton.elim _ _)
        rw [ite_eq_left hi]
        exact forwardContraction_trace_last a e J K htrace i i' o o'
    · intro e hab
      refine Fin.lastCases ?_ (fun a => ?_) a e hab
      · intro e hab
        exact (not_lt_of_ge (Fin.le_last b.castSucc) hab).elim
      · intro e hab
        refine ⟨forwardContraction_posSemidef _ _ _ hpsd, Comb.forwardContraction a b e K,
          ih (I := fun j : Fin n => I j.castSucc) (O := fun j : Fin n => O j.castSucc) a b (show a < b from hab) e hK, ?_⟩
        exact forwardContraction_trace_prefix a b e J K htrace

end QIT.HigherOrder.Comb
