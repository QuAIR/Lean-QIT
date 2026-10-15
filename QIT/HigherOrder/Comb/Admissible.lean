/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Basic
public import QIT.Channels.CompleteAdmissibility
public import QIT.Util.Wires.LinkProduct

/-!
# Completely admissible action on recursive combs

For an outer comb, the inner wires are `H₁,...,H₂ₙ`, paired as
`O j.castSucc → I j.succ`; the resulting channel runs from `I 0` to
`O (Fin.last _)`. This is the source order in
[Chiribella2009Networks, comblong-pub.tex:1417-1423] and
[Chiribella2009Networks, comblong-pub.tex:1425-1433].

The complete preservation predicates use independent finite boundary
ancillas: the first inner input and last inner output are extended. They
quantify over all joint operators, not just product operators. Choi-space
complete positivity is a separate condition. The equivalence with recursive
normalization is not part of these definitions.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder.Comb

section Boundary
variable {n : Nat} (I O : Fin (n + 1) → Type u) (r s : Type u)

/-- Attach the spectator input at the first input boundary. -/
def boundaryInput : Fin (n + 1) → Type u := Fin.cons (I 0 × r) (fun j => I j.succ)
/-- Attach the spectator output at the last output boundary. -/
def boundaryOutput : Fin (n + 1) → Type u :=
  Fin.snoc (fun j : Fin n => O j.castSucc) (O (Fin.last n) × s)

instance [∀ j, Fintype (I j)] [Fintype r] (j : Fin (n + 1)) :
    Fintype (boundaryInput I r j) :=
  by
  cases j using Fin.cases with
  | zero => simpa [boundaryInput] using (inferInstance : Fintype (I 0 × r))
  | succ j => simpa [boundaryInput] using (inferInstance : Fintype (I j.succ))
instance [∀ j, DecidableEq (I j)] [DecidableEq r] (j : Fin (n + 1)) :
    DecidableEq (boundaryInput I r j) :=
  by
  cases j using Fin.cases with
  | zero => simpa [boundaryInput] using (inferInstance : DecidableEq (I 0 × r))
  | succ j => simpa [boundaryInput] using (inferInstance : DecidableEq (I j.succ))
instance [∀ j, Fintype (O j)] [Fintype s] (j : Fin (n + 1)) :
    Fintype (boundaryOutput O s j) := by
  induction j using Fin.lastCases with
  | last => simpa [boundaryOutput] using (inferInstance : Fintype (O (Fin.last n) × s))
  | cast j => simpa [boundaryOutput] using (inferInstance : Fintype (O j.castSucc))
instance [∀ j, DecidableEq (O j)] [DecidableEq s] (j : Fin (n + 1)) :
    DecidableEq (boundaryOutput O s j) := by
  induction j using Fin.lastCases with
  | last => simpa [boundaryOutput] using (inferInstance : DecidableEq (O (Fin.last n) × s))
  | cast j => simpa [boundaryOutput] using (inferInstance : DecidableEq (O j.castSucc))

/-- Reading the first input ancilla separately from the original input tuple. -/
def boundaryInputEquiv : (∀ j, boundaryInput I r j) ≃ (∀ j, I j) × r := by
  let e : (∀ j, boundaryInput I r j) ≃ (I 0 × r) × (∀ j : Fin n, I j.succ) :=
    (Fin.consEquiv (boundaryInput I r)).symm |>.trans
      (Equiv.prodCongr (Equiv.cast (by simp [boundaryInput]))
        (Equiv.piCongrRight (fun j => Equiv.cast (by simp [boundaryInput]))))
  let shuffle : ((I 0 × r) × (∀ j : Fin n, I j.succ)) ≃
      (I 0 × (∀ j : Fin n, I j.succ)) × r :=
    { toFun := fun p => ((p.1.1, p.2), p.1.2)
      invFun := fun p => ((p.1.1, p.2), p.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans (shuffle.trans (Equiv.prodCongr (Fin.consEquiv I) (Equiv.refl r)))

/-- Reading the last output ancilla separately from the original output tuple. -/
def boundaryOutputEquiv : (∀ j, boundaryOutput O s j) ≃ (∀ j, O j) × s := by
  let e : (∀ j, boundaryOutput O s j) ≃
      (O (Fin.last n) × s) × (∀ j : Fin n, O j.castSucc) :=
    (Fin.snocEquiv (boundaryOutput O s)).symm |>.trans
      (Equiv.prodCongr (Equiv.cast (by simp [boundaryOutput]))
        (Equiv.piCongrRight (fun j => Equiv.cast (by simp [boundaryOutput]))))
  let shuffle : ((O (Fin.last n) × s) × (∀ j : Fin n, O j.castSucc)) ≃
      (O (Fin.last n) × (∀ j : Fin n, O j.castSucc)) × s :=
    { toFun := fun p => ((p.1.1, p.2), p.1.2)
      invFun := fun p => ((p.1.1, p.2), p.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans (shuffle.trans (Equiv.prodCongr (Fin.snocEquiv O) (Equiv.refl s)))

/-- Canonical grouping for the previously defined blockwise ancillary action. -/
def boundaryEquiv : Space (boundaryInput I r) (boundaryOutput O s) ≃
    ((∀ j, I j) × r) × ((∀ j, O j) × s) :=
  Equiv.prodCongr (boundaryInputEquiv I r) (boundaryOutputEquiv O s)

variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Recursive normalization of a joint comb with arbitrary boundary spectators. -/
def ExtendedNormalized (J : CMatrix (((∀ j, I j) × r) × ((∀ j, O j) × s))) : Prop :=
  Normalized (boundaryInput I r) (boundaryOutput O s)
    (J.submatrix (boundaryEquiv I O r s) (boundaryEquiv I O r s))

/-- Joint probabilistic inputs have a single joint deterministic completion. -/
def ExtendedProbabilistic (J : CMatrix (((∀ j, I j) × r) × ((∀ j, O j) × s))) : Prop :=
  J.PosSemidef ∧ ∃ K, ExtendedNormalized I O r s K ∧ J ≤ K
end Boundary

section Action
variable {n : Nat} (I O : Fin (n + 1) → Type u)
/-- The input wires of the inner comb are the outer nonfinal outputs. -/
abbrev innerInput (j : Fin n) := O j.castSucc
/-- The output wires of the inner comb are the outer noninitial inputs. -/
abbrev innerOutput (j : Fin n) := I j.succ

/-- Source order to input-first Choi order for the map on inner combs.
Both finite families remain heterogeneous. -/
def actionEquiv : Space I O ≃
    Space (innerInput O) (innerOutput I) × (I 0 × O (Fin.last n)) where
  toFun p := ((Fin.init p.2, Fin.tail p.1), (p.1 0, p.2 (Fin.last n)))
  invFun p := (Fin.cons p.2.1 p.1.2, Fin.snoc p.1.1 p.2.2)
  left_inv p := by simp
  right_inv p := by simp

variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The linear Choi-space action of an operator on the source-ordered wires. -/
def actionMap (J : CMatrix (Space I O)) :
    MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O (Fin.last n)) :=
  MatrixMap.ofChoiMatrix (WireFam.matReindex (actionEquiv I O) J)

/-- The Choi operator of the action is precisely the original operator with
its input/output blocks explicitly reordered. -/
@[simp] theorem choi_actionMap (J : CMatrix (Space I O)) :
    MatrixMap.choi (actionMap I O J) = WireFam.matReindex (actionEquiv I O) J :=
  MatrixMap.choi_ofChoiMatrix _

/-- Positivity of the source operator is equivalent to complete positivity
of its Choi-space action; it imposes no normalization by itself. -/
theorem actionMap_cp_iff (J : CMatrix (Space I O)) :
    MatrixMap.IsCompletelyPositive (actionMap I O J) ↔ J.PosSemidef := by
  rw [MatrixMap.IsCompletelyPositive, choi_actionMap]
  exact Matrix.posSemidef_submatrix_equiv (actionEquiv I O).symm
/-- Contract every inner wire using the shared wire-family link product.
The inner and outer configurations are grouped into single aggregate wires;
`actionEquiv` specifies the heterogeneous source-wire ordering inside them.
The first factor is the inserted operator, so its shared block is transposed
by `WireFam.linkProduct`, exactly as in the source convention. -/
def linkAction (J : CMatrix (Space I O))
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    CMatrix (I 0 × O (Fin.last n)) := by
  let E : Fin 0 → Type u := fun _ => PUnit
  let S : Fin 1 → Type u := fun _ => Space (innerInput O) (innerOutput I)
  let R : Fin 1 → Type u := fun _ => I 0 × O (Fin.last n)
  let M : CMatrix (∀ i, WireFam.append E S i) := fun p q =>
    X ((WireFam.splitAppendEquiv E S p).2 0) ((WireFam.splitAppendEquiv E S q).2 0)
  let K : CMatrix (∀ i, WireFam.append S R i) := fun p q =>
    WireFam.matReindex (actionEquiv I O) J
      ((WireFam.splitAppendEquiv S R p).1 0, (WireFam.splitAppendEquiv S R p).2 0)
      ((WireFam.splitAppendEquiv S R q).1 0, (WireFam.splitAppendEquiv S R q).2 0)
  exact fun p q => WireFam.linkProduct E S R M K
    ((WireFam.splitAppendEquiv E R).symm ((fun j => Fin.elim0 j), (fun _ => p)))
    ((WireFam.splitAppendEquiv E R).symm ((fun j => Fin.elim0 j), (fun _ => q)))

/-- The Choi inverse and the actual shared-wire link product give the same
operator, with no dimension, rank or invertibility hypothesis. -/
theorem actionMap_eq_linkAction (J : CMatrix (Space I O))
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    actionMap I O J X = linkAction I O J X := by
  classical
  ext p q
  change (∑ z, ∑ z', X z z' * WireFam.matReindex (actionEquiv I O) J (z,p) (z',q)) = _
  simp only [linkAction, WireFam.linkProduct, Equiv.apply_symm_apply]
  change (∑ z, ∑ z', X z z' * WireFam.matReindex (actionEquiv I O) J (z,p) (z',q)) =
    ∑ z : Fin 1 → Space (innerInput O) (innerOutput I),
      ∑ z' : Fin 1 → Space (innerInput O) (innerOutput I),
        X (z' 0) (z 0) * WireFam.matReindex (actionEquiv I O) J (z' 0,p) (z 0,q)
  rw [Finset.sum_comm]
  symm
  apply Fintype.sum_equiv (Equiv.piUnique (fun _ : Fin 1 => Space (innerInput O) (innerOutput I)))
  intro z
  apply Fintype.sum_equiv (Equiv.piUnique (fun _ : Fin 1 => Space (innerInput O) (innerOutput I)))
  intro z'
  rfl

end Action

section Admissibility
variable {n : Nat} (I O : Fin (n + 2) → Type u)
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- Complete deterministic preservation for the recursive step `N ≥ 2`.
The base `N = 1` is ordinary channels. Complete positivity is on Choi space;
normalization is tested on every jointly normalized inner comb with
independent finite boundary ancillas. -/
def IsDeterministicMap (S : MatrixMap (Space (innerInput O) (innerOutput I))
    (I 0 × O (Fin.last (n + 1)))) : Prop :=
  MatrixMap.IsCompletelyPositive S ∧
    CompletelyPreserves S (fun r s _ _ _ _ =>
      ExtendedNormalized (innerInput O) (innerOutput I) r s)
      channelPredicate

/-- A probabilistic recursive map has a common deterministic completion.
Pointwise preservation of trace bounds alone is not this definition.
[Chiribella2009Networks, comblong-pub.tex:1425-1433]. -/
def IsProbabilisticMap (S : MatrixMap (Space (innerInput O) (innerOutput I))
    (I 0 × O (Fin.last (n + 1)))) : Prop :=
  MatrixMap.IsCompletelyPositive S ∧ ∃ T, IsDeterministicMap I O T ∧
    MatrixMap.IsCompletelyPositive (T - S)

/-- Deterministic maps are their own probabilistic completion. -/
theorem IsDeterministicMap.isProbabilistic {S} (h : IsDeterministicMap I O S) :
    IsProbabilisticMap I O S := by
  refine ⟨h.1, S, h, ?_⟩
  simp only [sub_self]
  change (MatrixMap.choi (0 : MatrixMap _ _)).PosSemidef
  have hz : MatrixMap.choi (0 : MatrixMap (Space (innerInput O) (innerOutput I))
      (I 0 × O (Fin.last (n + 1)))) = 0 := by ext p q; rfl
  rw [hz]
  exact Matrix.PosSemidef.zero
/-- Complete deterministic action returns a channel on the two outer wires. -/
theorem IsDeterministicMap.channel {S} (h : IsDeterministicMap I O S)
    (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (J : CMatrix ((((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))))
    (hJ : ExtendedNormalized (innerInput O) (innerOutput I) r s J) :
    (ancillaryExtension S J).PosSemidef ∧ partialTraceB (ancillaryExtension S J) = 1 :=
  h.2 r s J hJ

private theorem extension_mono {a b c d r s : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (S : MatrixMap (a × b) (c × d)) (hS : MatrixMap.IsCompletelyPositive S)
    {J K : CMatrix ((a × r) × (b × s))} (h : J ≤ K) :
    ancillaryExtension S J ≤ ancillaryExtension S K := by
  apply Matrix.le_iff.mpr
  have hpos := ancillaryExtension_posSemidef S hS (K - J) (Matrix.le_iff.mp h)
  have heq : ancillaryExtension S (K - J) = ancillaryExtension S K - ancillaryExtension S J := by
    ext p q
    change S (ancillaryBlock (K - J) _ _) _ _ = _
    have hb : ancillaryBlock (K - J) (p.1.2, p.2.2) (q.1.2, q.2.2) =
        ancillaryBlock K _ _ - ancillaryBlock J _ _ := rfl
    rw [hb, map_sub]
    rfl
  rwa [heq] at hpos

/-- Probabilistic action returns an actual trace-nonincreasing CP operation
on every joint probabilistic input, including zero and singular inputs. -/
theorem IsProbabilisticMap.operation {S} (h : IsProbabilisticMap I O S)
    (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (J : CMatrix ((((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))))
    (hJ : ExtendedProbabilistic (innerInput O) (innerOutput I) r s J) :
    MatrixMap.TraceNonincreasingCP (MatrixMap.ofChoiMatrix (ancillaryExtension S J)) := by
  rcases h with ⟨hS, T, hT, hTS⟩
  rcases hJ with ⟨hJ, K, hK, hJK⟩
  apply (MatrixMap.traceNonincreasingCP_iff_choi _).mpr
  rw [MatrixMap.choi_ofChoiMatrix]
  refine ⟨ancillaryExtension_posSemidef S hS J hJ, ?_⟩
  have hST : ancillaryExtension S J ≤ ancillaryExtension T J := by
    apply Matrix.le_iff.mpr
    exact ancillaryExtension_posSemidef (T - S) hTS J hJ
  have hTK := extension_mono T hT.1 hJK
  have htrace := partialTraceB_mono (hST.trans hTK)
  rwa [(IsDeterministicMap.channel I O hT r s K hK).2] at htrace

/-- Deterministic maps also act on probabilistic inputs as operations. -/
theorem IsDeterministicMap.operation {S} (h : IsDeterministicMap I O S)
    (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (J : CMatrix ((((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))))
    (hJ : ExtendedProbabilistic (innerInput O) (innerOutput I) r s J) :
    MatrixMap.TraceNonincreasingCP (MatrixMap.ofChoiMatrix (ancillaryExtension S J)) :=
  IsProbabilisticMap.operation I O (IsDeterministicMap.isProbabilistic I O h) r s J hJ

end Admissibility
end QIT.HigherOrder.Comb
