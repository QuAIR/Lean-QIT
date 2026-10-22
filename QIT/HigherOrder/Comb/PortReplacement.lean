/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Closure
public import QIT.HigherOrder.Comb.Compression

/-!
# Replacing a comb output by a unit wire

Tracing an output and retaining its position as a unit wire preserves recursive
comb normalization. The proof uses the actual predecessor witness from
`Comb.Normalized`, and therefore also applies when input or output types are empty.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder.Comb
open QIT.WireFam

/-- Replace a port at a natural-number position by a unit type. Natural indices
make restriction to a prefix definitionally commute with this operation. -/
@[reducible] def erasePort {n : Nat} (W : Fin n → Type u) (a : Nat) (j : Fin n) : Type u :=
  if j.val = a then PUnit else W j

instance erasePortFintype {n : Nat} (W : Fin n → Type u) [∀ j, Fintype (W j)]
    (a : Nat) (j : Fin n) : Fintype (erasePort W a j) := by
  unfold erasePort
  split <;> infer_instance

instance erasePortDecidableEq {n : Nat} (W : Fin n → Type u) [∀ j, DecidableEq (W j)]
    (a : Nat) (j : Fin n) : DecidableEq (erasePort W a j) := by
  unfold erasePort
  split <;> infer_instance

/-- Restore the erased port with the supplied value. -/
def fillPort {n : Nat} (W : Fin n → Type u) (a : Fin n)
    (v : ∀ j, erasePort W a.val j) (z : W a) (j : Fin n) : W j :=
  if h : j.val = a.val then
    cast (congrArg W (Fin.ext h).symm) z
  else cast (by simp [erasePort, h]) (v j)

@[simp] theorem fillPort_at {n : Nat} (W : Fin n → Type u) (a : Fin n)
    (v : ∀ j, erasePort W a.val j) (z : W a) : fillPort W a v z a = z := by
  simp [fillPort]

/-- Readback at a port other than the restored one. -/
theorem fillPort_of_ne {n : Nat} (W : Fin n → Type u) (a j : Fin n)
    (v : ∀ j, erasePort W a.val j) (z : W a) (h : j.val ≠ a.val) :
    fillPort W a v z j = cast (by simp [erasePort, h]) (v j) := by
  simp [fillPort, h]

@[simp] theorem erasePort_castSucc {n : Nat} (W : Fin (n + 1) → Type u)
    (a : Nat) (j : Fin n) :
    erasePort W a j.castSucc = erasePort (fun j : Fin n => W j.castSucc) a j := rfl

/-- Restoring a prefix port commutes with restricting the configuration. -/
@[simp] theorem fillPort_castSucc {n : Nat} (W : Fin (n + 1) → Type u)
    (a : Fin n) (v : ∀ j, erasePort W a.val j) (z : W a.castSucc) (j : Fin n) :
    fillPort W a.castSucc v z j.castSucc =
      fillPort (fun j : Fin n => W j.castSucc) a (fun j => v j.castSucc) z j := by
  by_cases h : j.val = a.val <;> simp [fillPort, h]

/-- Reading the final port after restoring an earlier port. -/
theorem fillPort_last_of_castSucc {n : Nat} (W : Fin (n + 1) → Type u)
    (a : Fin n) (v : ∀ j, erasePort W a.val j) (z : W a.castSucc) :
    fillPort W a.castSucc v z (Fin.last n) =
      cast (by simp [erasePort, Nat.ne_of_gt a.isLt]) (v (Fin.last n)) := by
  apply fillPort_of_ne
  exact Nat.ne_of_gt a.isLt

/-- An untouched erased-family port is canonically its original type. -/
def erasePortEquiv {n : Nat} (W : Fin n → Type u) (a : Nat) (j : Fin n)
    (h : j.val ≠ a) : erasePort W a j ≃ W j :=
  Equiv.cast (by simp [erasePort, h])

/-- The selected erased-family port is canonically the unit type. -/
def erasePortUnitEquiv {n : Nat} (W : Fin n → Type u) (a : Fin n) :
    erasePort W a.val a ≃ PUnit := Equiv.cast (by simp [erasePort])

/-- Restoring an earlier port commutes with appending the final value. -/
theorem fillPort_snoc_castSucc {n : Nat} (W : Fin (n + 1) → Type u)
    (a : Fin n) (o : ∀ j : Fin n, erasePort W a.val j.castSucc)
    (z : erasePort W a.val (Fin.last n)) (w : W a.castSucc) :
    fillPort W a.castSucc (Fin.snoc o z) w =
      Fin.snoc (fillPort (fun j : Fin n => W j.castSucc) a o w)
        (erasePortEquiv W a.val (Fin.last n) (Nat.ne_of_gt a.isLt) z) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [fillPort_last_of_castSucc, erasePortEquiv]
  · simp

/-- Restoring the last port leaves the prefix values unchanged. -/
theorem fillPort_snoc_last {n : Nat} (W : Fin (n + 1) → Type u)
    (o : ∀ j : Fin n, erasePort W n j.castSucc)
    (z : erasePort W n (Fin.last n)) (w : W (Fin.last n)) :
    fillPort W (Fin.last n) (Fin.snoc o z) w =
      Fin.snoc (fun j : Fin n =>
        erasePortEquiv W n j.castSucc (Nat.ne_of_lt j.isLt) (o j)) w := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp [fillPort, Nat.ne_of_lt k.isLt, erasePortEquiv]

/-- Trace the selected output, retaining its position as a unit output. -/
def discardOutput {n : Nat} {I O : Fin n → Type u} [∀ j, Fintype (O j)]
    (a : Fin n) (J : CMatrix (Space I O)) : CMatrix (Space I (erasePort O a.val)) :=
  diagonalSum (fun p z => (p.1, fillPort O a p.2 z)) J

@[simp] theorem discardOutput_apply {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (O j)] (a : Fin n) (J : CMatrix (Space I O))
    (p q : Space I (erasePort O a.val)) :
    discardOutput a J p q = ∑ z, J (p.1, fillPort O a p.2 z)
      (q.1, fillPort O a q.2 z) := rfl

/-- Discarding an output preserves positivity, including for empty wires. -/
theorem discardOutput_posSemidef {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (O j)] (a : Fin n) {J : CMatrix (Space I O)}
    (hJ : J.PosSemidef) : (discardOutput a J).PosSemidef :=
  diagonalSum_posSemidef _ hJ

/-- Tracing one output preserves the recursive normalization at the same depth,
with the consumed output replaced by a unit wire. No input wire is required
to be inhabited. -/
theorem Normalized.discardOutput {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (a : Fin n) {J : CMatrix (Space I O)} (hJ : Normalized I O J) :
    Normalized I (erasePort O a.val) (Comb.discardOutput a J) := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    obtain ⟨hpsd, K, hK, htr⟩ := hJ
    refine Fin.lastCases ?_ (fun b => ?_) a
    · let eO : ∀ j : Fin n, O j.castSucc ≃ erasePort O n j.castSucc :=
        fun j => (erasePortEquiv O n j.castSucc (Nat.ne_of_lt j.isLt)).symm
      let K' := matReindex (spaceEquiv (fun j : Fin n => Equiv.refl (I j.castSucc)) eO) K
      refine ⟨discardOutput_posSemidef _ hpsd, K', (Normalized.reindex_iff _ _ _).mp hK, ?_⟩
      intro i i' o o'
      have hf (z : erasePort O n (Fin.last n)) :
          Comb.discardOutput (Fin.last n) J (i, Fin.snoc o z) (i', Fin.snoc o' z) =
            if i (Fin.last n) = i' (Fin.last n) then
              K' ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o') else 0 := by
        simp only [discardOutput_apply, fillPort_snoc_last]
        exact htr i i' _ _
      simp only [hf]
      have hu : Fintype.card (erasePort O n (Fin.last n)) = 1 :=
        Fintype.card_congr (erasePortUnitEquiv O (Fin.last n)) |>.trans (by simp)
      simp [hu]
    · refine ⟨discardOutput_posSemidef _ hpsd, Comb.discardOutput b K, ih b hK, ?_⟩
      intro i i' o o'
      change (∀ j : Fin n, erasePort (fun j : Fin n => O j.castSucc) b.val j) at o o'
      simp only [discardOutput_apply, fillPort_snoc_castSucc]
      rw [Finset.sum_comm]
      let he := erasePortEquiv O b.val (Fin.last n) (Nat.ne_of_gt b.isLt)
      conv_lhs =>
        arg 2
        ext w
        equals (∑ z : O (Fin.last n),
          J (i, Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) b o w) z)
            (i', Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) b o' w) z)) =>
          exact he.sum_comp (fun z : O (Fin.last n) =>
            J (i, Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) b o w) z)
              (i', Fin.snoc (fillPort (fun j : Fin n => O j.castSucc) b o' w) z))
      simp_rw [htr]
      split_ifs <;> simp_all

end QIT.HigherOrder.Comb
end
