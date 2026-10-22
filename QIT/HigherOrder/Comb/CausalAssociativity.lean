/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.Core.Map.MatchedWireAssociativity
public import QIT.HigherOrder.Comb.CausalComposition
/-!
# Regrouping actual scheduled network compositions

A three-factor network has private ports and disjoint AB, AC, and BC connection
blocks. `Regrouping` records their positions and per-wire basis maps, together
with the two actual first-step causal joins. Configuration and complement
readback are derived; no matrix equality is a structural hypothesis.

`composeLeft` and `composeRight` use `CausalJoin.comp` for their first step and
the actual aggregate-wire link product for their second step. The first
composite's `boundaryEquiv.symm` removes unit padding, so subsequent matching
uses only genuine free ports. Pending AC/BC or AB/AC blocks are retained.

`Regrouping.assoc` and `assoc_reindex` reuse `MatchedWire.triangle_assoc`, hence
`WireFam.linkProduct_assoc`, for arbitrary finite heterogeneous wires, including
empty individual types. The equality is algebraic: the data do not assert a
common topological schedule for all three factors. They cover every source-valid
acyclic instance; normalization of an actual causal join is the separate
`CausalJoin.comp_normalized` theorem. The source associativity and network
composition rules are [Chiribella2009Networks, comblong-pub.tex:342-355,1279-1286].
-/

@[expose] public section

open QIT QIT.WireFam QIT.WireFam.MatchedWire QIT.HigherOrder.Comb
open scoped BigOperators
noncomputable section
universe u
namespace QIT.HigherOrder.Comb.CausalJoin
variable {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
  {l r : Nat} {L : Fin l → Type u} {R : Fin r → Type u}
/-- The actual scheduled boundary in the two private-port configuration blocks. -/
def boundaryCoordinates (j : CausalJoin I O P Q)
    {S : Fin j.toWireJoin.toWireMatch.s → Type u}
    (p : PortPartition (append I O) L S) (q : PortPartition (append P Q) R S)
    (hp : ∀ k, p.index (j.toWireJoin.toWireMatch.ι₁ k) = Sum.inr k)
    (hq : ∀ k, q.index (j.toWireJoin.toWireMatch.ι₂ k) = Sum.inr k) :
    Space j.boundaryInput j.boundaryOutput ≃ (∀ i, L i) × (∀ i, R i) :=
  j.boundaryEquiv.symm.trans (partitionBoundaryEquiv j.toWireJoin.toWireMatch p q hp hq)

/-- Actual matched-wire composition in coordinates derived from endpoint maps. -/
theorem comp_coordinates [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
    (j : CausalJoin I O P Q) {S : Fin j.toWireJoin.toWireMatch.s → Type u}
    [∀ i, Fintype (S i)]
    (p : PortPartition (append I O) L S) (q : PortPartition (append P Q) R S)
    (hp : ∀ k, p.index (j.toWireJoin.toWireMatch.ι₁ k) = Sum.inr k)
    (hq : ∀ k, q.index (j.toWireJoin.toWireMatch.ι₂ k) = Sum.inr k)
    (he : ∀ k, (j.toWireJoin.toWireMatch.e k).trans
      (q.atRight (j.toWireJoin.toWireMatch.ι₂ k) (hq k)) =
      p.atRight (j.toWireJoin.toWireMatch.ι₁ k) (hp k))
    (J : CMatrix (Space I O)) (K : CMatrix (Space P Q)) :
    matReindex (j.boundaryCoordinates p q hp hq) (j.comp J K) =
      productLink
        (matReindex ((splitAppendEquiv I O).symm.trans p.configEquiv) J)
        (matReindex ((splitAppendEquiv P Q).symm.trans
          (q.configEquiv.trans (Equiv.prodComm _ _))) K) := by
  let : ∀ k, Fintype (j.toWireJoin.toWireMatch.connFam₁ k) := fun k => by
    change Fintype (append I O (j.toWireJoin.toWireMatch.ι₁ k))
    infer_instance
  unfold boundaryCoordinates comp
  rw [matReindex_trans_apply, matReindex_symm_matReindex]
  simpa only [WireJoin.rawComp, matReindex_trans_apply] using
    partition_linkProduct j.toWireJoin.toWireMatch p q hp hq he
      (matReindex (splitAppendEquiv I O).symm J)
      (matReindex (splitAppendEquiv P Q).symm K)
end QIT.HigherOrder.Comb.CausalJoin

namespace QIT.HigherOrder.Comb.CausalJoin
variable {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
  {l r : Nat} {L : Fin l → Type u} {R : Fin r → Type u}
/-- Relabel the two private boundary blocks after actual composition. -/
theorem comp_coordinates_reindex [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
    (j : CausalJoin I O P Q) {S : Fin j.toWireJoin.toWireMatch.s → Type u}
    [∀ i, Fintype (S i)] {A B : Type u}
    (p : PortPartition (append I O) L S) (q : PortPartition (append P Q) R S)
    (hp : ∀ k, p.index (j.toWireJoin.toWireMatch.ι₁ k) = Sum.inr k)
    (hq : ∀ k, q.index (j.toWireJoin.toWireMatch.ι₂ k) = Sum.inr k)
    (he : ∀ k, (j.toWireJoin.toWireMatch.e k).trans
      (q.atRight (j.toWireJoin.toWireMatch.ι₂ k) (hq k)) =
      p.atRight (j.toWireJoin.toWireMatch.ι₁ k) (hp k))
    (eL : (∀ i, L i) ≃ A) (eR : (∀ i, R i) ≃ B)
    (J : CMatrix (Space I O)) (K : CMatrix (Space P Q)) :
    matReindex ((j.boundaryCoordinates p q hp hq).trans (eL.prodCongr eR)) (j.comp J K) =
      productLink
        (matReindex (((splitAppendEquiv I O).symm.trans p.configEquiv).trans
          (eL.prodCongr (Equiv.refl _))) J)
        (matReindex (((splitAppendEquiv P Q).symm.trans
          (q.configEquiv.trans (Equiv.prodComm _ _))).trans
          ((Equiv.refl _).prodCongr eR)) K) := by
  rw [matReindex_trans_apply, j.comp_coordinates p q hp hq he]
  symm
  simpa only [matReindex_trans_apply] using
    productLink_reindex eL (Equiv.refl (∀ i, S i)) eR
      (matReindex ((splitAppendEquiv I O).symm.trans p.configEquiv) J)
      (matReindex ((splitAppendEquiv P Q).symm.trans
        (q.configEquiv.trans (Equiv.prodComm _ _))) K)
end QIT.HigherOrder.Comb.CausalJoin

namespace QIT.HigherOrder.Comb.CausalJoin
/-- Structural port partitions for one three-factor network. AB and BC carry
their own schedules; the operator equality requires no global causal-order
assumption and therefore applies in particular to globally acyclic networks. -/
structure Regrouping {nA nB nC : Nat}
    {IA OA : Fin nA → Type u} {IB OB : Fin nB → Type u} {IC OC : Fin nC → Type u}
    (jAB : CausalJoin IA OA IB OB) (jBC : CausalJoin IB OB IC OC)
    {ra rb rc y : Nat} (A : Fin ra → Type u) (B : Fin rb → Type u)
    (C : Fin rc → Type u) (X : Fin jAB.toWireJoin.toWireMatch.s → Type u)
    (Y : Fin y → Type u) (Z : Fin jBC.toWireJoin.toWireMatch.s → Type u) where
  partitionA : PortPartition (append IA OA) (append A Y) X
  partitionB : PortPartition (append IB OB) X (append B Z)
  partitionC : PortPartition (append IC OC) (append Y Z) C
  ab_left : ∀ k, partitionA.index (jAB.toWireJoin.toWireMatch.ι₁ k) = Sum.inr k
  ab_right : ∀ k, partitionB.swap.index (jAB.toWireJoin.toWireMatch.ι₂ k) = Sum.inr k
  ab_basis : ∀ k, (jAB.toWireJoin.toWireMatch.e k).trans
    (partitionB.swap.atRight (jAB.toWireJoin.toWireMatch.ι₂ k) (ab_right k)) =
    partitionA.atRight (jAB.toWireJoin.toWireMatch.ι₁ k) (ab_left k)
  bc_left : ∀ k, partitionB.assoc.index (jBC.toWireJoin.toWireMatch.ι₁ k) = Sum.inr k
  bc_right : ∀ k, partitionC.swapMiddle.index (jBC.toWireJoin.toWireMatch.ι₂ k) = Sum.inr k
  bc_basis : ∀ k, (jBC.toWireJoin.toWireMatch.e k).trans
    (partitionC.swapMiddle.atRight (jBC.toWireJoin.toWireMatch.ι₂ k) (bc_right k)) =
    partitionB.assoc.atRight (jBC.toWireJoin.toWireMatch.ι₁ k) (bc_left k)

namespace Regrouping
variable {nA nB nC ra rb rc y : Nat}
  {IA OA : Fin nA → Type u} {IB OB : Fin nB → Type u} {IC OC : Fin nC → Type u}
  {jAB : CausalJoin IA OA IB OB} {jBC : CausalJoin IB OB IC OC}
  {A : Fin ra → Type u} {B : Fin rb → Type u} {C : Fin rc → Type u}
  {X : Fin jAB.toWireJoin.toWireMatch.s → Type u} {Y : Fin y → Type u}
  {Z : Fin jBC.toWireJoin.toWireMatch.s → Type u}

/-- Free configurations after AB, retaining both pending AC and BC blocks. -/
def leftBoundary (r : Regrouping jAB jBC A B C X Y Z) :
    Space jAB.boundaryInput jAB.boundaryOutput ≃
      ((∀ i, A i) × (∀ i, Y i)) × ((∀ i, B i) × (∀ i, Z i)) :=
  (jAB.boundaryCoordinates r.partitionA r.partitionB.swap r.ab_left r.ab_right).trans
    ((splitAppendEquiv A Y).prodCongr (splitAppendEquiv B Z))

/-- Free configurations after BC, retaining both pending AB and AC blocks. -/
def rightBoundary (r : Regrouping jAB jBC A B C X Y Z) :
    Space jBC.boundaryInput jBC.boundaryOutput ≃
      ((∀ i, X i) × (∀ i, B i)) × ((∀ i, Y i) × (∀ i, C i)) :=
  (jBC.boundaryCoordinates r.partitionB.assoc r.partitionC.swapMiddle
    r.bc_left r.bc_right).trans
      ((splitAppendEquiv X B).prodCongr (splitAppendEquiv Y C))

end Regrouping
end QIT.HigherOrder.Comb.CausalJoin

namespace QIT.HigherOrder.Comb.CausalJoin.Regrouping
variable {nA nB nC ra rb rc y : Nat}
  {IA OA : Fin nA → Type u} {IB OB : Fin nB → Type u} {IC OC : Fin nC → Type u}
  {jAB : CausalJoin IA OA IB OB} {jBC : CausalJoin IB OB IC OC}
  {A : Fin ra → Type u} {B : Fin rb → Type u} {C : Fin rc → Type u}
  {X : Fin jAB.toWireJoin.toWireMatch.s → Type u} {Y : Fin y → Type u}
  {Z : Fin jBC.toWireJoin.toWireMatch.s → Type u}
  [∀ i, Fintype (IA i)] [∀ i, Fintype (OA i)]
  [∀ i, Fintype (IB i)] [∀ i, Fintype (OB i)]
  [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

/-- Compose AB by its actual causal join, then link the pending AC/BC ports to C. -/
def composeLeft (r : Regrouping jAB jBC A B C X Y Z)
    (J : CMatrix (Space IA OA)) (K : CMatrix (Space IB OB))
    (T : CMatrix (Space IC OC)) : CMatrix (((∀ i, A i) × (∀ i, B i)) × (∀ i, C i)) :=
  productLink (matReindex (r.leftBoundary.trans (gather _ _ _ _)) (jAB.comp J K))
    (matReindex ((splitAppendEquiv IC OC).symm.trans r.partitionC.leftTriple) T)

/-- Compose BC by its actual causal join, then link the pending AB/AC ports to A. -/
def composeRight (r : Regrouping jAB jBC A B C X Y Z)
    (J : CMatrix (Space IA OA)) (K : CMatrix (Space IB OB))
    (T : CMatrix (Space IC OC)) : CMatrix ((∀ i, A i) × ((∀ i, B i) × (∀ i, C i))) :=
  productLink
    (matReindex (((splitAppendEquiv IA OA).symm.trans r.partitionA.leftTriple).trans
      (leftOrder _ _ _)) J)
    (matReindex (r.rightBoundary.trans (gather _ _ _ _)) (jBC.comp K T))

omit [∀ i, Fintype (IB i)] [∀ i, Fintype (OB i)]
  [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)] in
/-- AB composition in the unique three-factor port partition coordinates. -/
theorem left_coordinates (r : Regrouping jAB jBC A B C X Y Z)
    (J : CMatrix (Space IA OA)) (K : CMatrix (Space IB OB)) :
    matReindex r.leftBoundary (jAB.comp J K) =
      productLink (matReindex ((splitAppendEquiv IA OA).symm.trans r.partitionA.leftTriple) J)
        (matReindex ((splitAppendEquiv IB OB).symm.trans r.partitionB.rightTriple) K) := by
  have h := jAB.comp_coordinates_reindex r.partitionA r.partitionB.swap
    r.ab_left r.ab_right r.ab_basis (splitAppendEquiv A Y) (splitAppendEquiv B Z) J K
  have hA : (((splitAppendEquiv IA OA).symm.trans r.partitionA.configEquiv).trans
      ((splitAppendEquiv A Y).prodCongr (Equiv.refl _))) =
      ((splitAppendEquiv IA OA).symm.trans r.partitionA.leftTriple) := rfl
  have hB : (((splitAppendEquiv IB OB).symm.trans
      (r.partitionB.swap.configEquiv.trans (Equiv.prodComm _ _))).trans
      ((Equiv.refl _).prodCongr (splitAppendEquiv B Z))) =
      ((splitAppendEquiv IB OB).symm.trans r.partitionB.rightTriple) := by
    rw [PortPartition.configEquiv_swap]
    apply Equiv.ext
    intro p
    rfl
  rw [hA, hB] at h
  exact h

omit [∀ i, Fintype (IA i)] [∀ i, Fintype (OA i)]
  [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
/-- BC composition in the same three-factor port partition coordinates. -/
theorem right_coordinates (r : Regrouping jAB jBC A B C X Y Z)
    (K : CMatrix (Space IB OB)) (T : CMatrix (Space IC OC)) :
    matReindex r.rightBoundary (jBC.comp K T) =
      productLink
        (matReindex (((splitAppendEquiv IB OB).symm.trans r.partitionB.rightTriple).trans
          (Equiv.prodAssoc _ _ _).symm) K)
        (matReindex (((splitAppendEquiv IC OC).symm.trans r.partitionC.leftTriple).trans
          (midSwapEquiv _ _ _)) T) := by
  have h := jBC.comp_coordinates_reindex r.partitionB.assoc r.partitionC.swapMiddle
    r.bc_left r.bc_right r.bc_basis (splitAppendEquiv X B) (splitAppendEquiv Y C) K T
  have hB : (((splitAppendEquiv IB OB).symm.trans r.partitionB.assoc.configEquiv).trans
      ((splitAppendEquiv X B).prodCongr (Equiv.refl _))) =
      (((splitAppendEquiv IB OB).symm.trans r.partitionB.rightTriple).trans
        (Equiv.prodAssoc _ _ _).symm) := by
    change (splitAppendEquiv IB OB).symm.trans r.partitionB.assoc.leftTriple = _
    rw [PortPartition.leftTriple_assoc]
    rfl
  have hC : (((splitAppendEquiv IC OC).symm.trans
      (r.partitionC.swapMiddle.configEquiv.trans (Equiv.prodComm _ _))).trans
      ((Equiv.refl _).prodCongr (splitAppendEquiv Y C))) =
      (((splitAppendEquiv IC OC).symm.trans r.partitionC.leftTriple).trans
        (midSwapEquiv _ _ _)) := by
    calc
      _ = (splitAppendEquiv IC OC).symm.trans
          (r.partitionC.swapMiddle.leftTriple.trans (Equiv.prodComm _ _)) := by
        apply Equiv.ext
        intro p
        rfl
      _ = _ := by
        rw [PortPartition.leftTriple_swapMiddle]
        apply Equiv.ext
        intro p
        rfl
  rw [hB, hC] at h
  exact h

omit [∀ i, Fintype (IB i)] [∀ i, Fintype (OB i)] in
/-- The left grouping in canonical six-block coordinates, derived from the
actual AB matching and its complement boundary. -/
theorem composeLeft_eq_triangle (r : Regrouping jAB jBC A B C X Y Z)
    (J : CMatrix (Space IA OA)) (K : CMatrix (Space IB OB)) (T : CMatrix (Space IC OC)) :
    r.composeLeft J K T =
      triangleLeft (matReindex ((splitAppendEquiv IA OA).symm.trans r.partitionA.leftTriple) J)
        (matReindex ((splitAppendEquiv IB OB).symm.trans r.partitionB.rightTriple) K)
        (matReindex ((splitAppendEquiv IC OC).symm.trans r.partitionC.leftTriple) T) := by
  unfold composeLeft triangleLeft
  rw [matReindex_trans_apply, r.left_coordinates]

omit [∀ i, Fintype (IA i)] [∀ i, Fintype (OA i)] in
/-- The right grouping in the same six-block coordinates, retaining all
pending AB and AC ports after the actual BC matching. -/
theorem composeRight_eq_triangle (r : Regrouping jAB jBC A B C X Y Z)
    (J : CMatrix (Space IA OA)) (K : CMatrix (Space IB OB)) (T : CMatrix (Space IC OC)) :
    r.composeRight J K T =
      triangleRight (matReindex ((splitAppendEquiv IA OA).symm.trans r.partitionA.leftTriple) J)
        (matReindex ((splitAppendEquiv IB OB).symm.trans r.partitionB.rightTriple) K)
        (matReindex ((splitAppendEquiv IC OC).symm.trans r.partitionC.leftTriple) T) := by
  unfold composeRight triangleRight
  simp only [matReindex_trans_apply]
  rw [r.right_coordinates]
  simp only [matReindex_trans_apply]

/-- Both actual binary link-product groupings of the network agree, with the
explicit associator on the surviving private configurations. -/
theorem assoc (r : Regrouping jAB jBC A B C X Y Z)
    (J : CMatrix (Space IA OA)) (K : CMatrix (Space IB OB)) (T : CMatrix (Space IC OC)) :
    matReindex (Equiv.prodAssoc _ _ _) (r.composeLeft J K T) = r.composeRight J K T := by
  rw [r.composeLeft_eq_triangle, r.composeRight_eq_triangle]
  exact triangle_assoc _ _ _


/-- Coherence after any further equivalence of the final private boundary. -/
theorem assoc_reindex (r : Regrouping jAB jBC A B C X Y Z)
    (J : CMatrix (Space IA OA)) (K : CMatrix (Space IB OB)) (T : CMatrix (Space IC OC))
    {D : Type u} (f : (∀ i, A i) × ((∀ i, B i) × (∀ i, C i)) ≃ D) :
    matReindex ((Equiv.prodAssoc _ _ _).trans f) (r.composeLeft J K T) =
      matReindex f (r.composeRight J K T) := by
  rw [matReindex_trans_apply, r.assoc]

end QIT.HigherOrder.Comb.CausalJoin.Regrouping

end
