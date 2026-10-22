/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Composition
public import QIT.Core.Map.MatchedWireAssociativity

/-!
# Nested comb contraction coherence

A suffix contraction consumes every wire of its inner factor. In a nested
network, regrouping must therefore retain the inner window until its own
factor is contracted. The intermediate composition on the other grouping
connects only the complementary wires. The algebraic equality reuses
[Chiribella2009Networks, comblong-pub.tex:342-355] through
`WireFam.linkProduct_assoc`; no normalization or inhabited-wire hypothesis
is needed. The suffix packaging is the one used by the composition rule
[Chiribella2009Networks, comblong-pub.tex:1279-1286].

The same coordinate argument applies to `relabeledSuffixComp`, retaining
its pointwise basis identifications. These results concern the suffix
operator; genuine selected-wire composition is defined by `CausalJoin.comp`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open QIT.WireFam
universe u
namespace QIT.HigherOrder.Comb

/-- Package a configuration space as one aggregate wire. -/
abbrev configBlock (α : Type u) : Fin 1 → Type u := MatchedWire.block α

/-- Split two aggregate wires into their product configuration space. -/
def configPairEquiv (α β : Type u) : (∀ i, append (configBlock α) (configBlock β) i) ≃ α × β :=
  MatchedWire.pairEquiv α β

/-- The core link product in product coordinates, retaining the first and
last blocks and connecting only the middle block. -/
def partialComp {α β γ : Type u} [Fintype β]
    (M : CMatrix (α × β)) (N : CMatrix (β × γ)) : CMatrix (α × γ) :=
  MatchedWire.productLink M N

/-- Entrywise reading of the partial composition, with transpose on the
first factor's connected block. -/
theorem partialComp_apply {α β γ : Type u} [Fintype β]
    (M : CMatrix (α × β)) (N : CMatrix (β × γ)) (a a' : α) (c c' : γ) :
    partialComp M N (a, c) (a', c') =
      ∑ b, ∑ b', M (a, b') (a', b) * N (b', c) (b, c') :=
  MatchedWire.productLink_apply M N a a' c c'

/-- Associativity in product coordinates is transported from the existing
core theorem. -/
theorem partialComp_assoc {α β γ δ : Type u} [Fintype β] [Fintype γ]
    (M : CMatrix (α × β)) (N : CMatrix (β × γ)) (P : CMatrix (γ × δ)) :
    partialComp (partialComp M N) P = partialComp M (partialComp N P) :=
  MatchedWire.productLink_assoc M N P

/-- Contract a complete window while retaining the complementary block. -/
def consume {β γ : Type u} [Fintype β] (Y : CMatrix β) (X : CMatrix (β × γ)) :
    CMatrix γ :=
  (partialComp (Y.submatrix (Prod.snd : PUnit × β → β) Prod.snd) X).submatrix
    (fun c => (PUnit.unit, c)) (fun c => (PUnit.unit, c))

theorem consume_apply {β γ : Type u} [Fintype β]
    (Y : CMatrix β) (X : CMatrix (β × γ)) (c c' : γ) :
    consume Y X c c' = ∑ b, ∑ b', Y b' b * X (b', c) (b, c') :=
  partialComp_apply _ _ _ _ _ _

/-- The nested contraction keeps the pending window on the right-hand
intermediate matrix. -/
theorem consume_partialComp {β γ δ : Type u} [Fintype β] [Fintype γ]
    (Y : CMatrix β) (X : CMatrix (β × γ)) (J : CMatrix (γ × δ)) :
    consume (consume Y X) J = consume Y (partialComp X J) := by
  have h : (consume Y X).submatrix (Prod.snd : PUnit × γ → γ) Prod.snd =
      partialComp (Y.submatrix (Prod.snd : PUnit × β → β) Prod.snd) X := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    cases a; cases a'
    rfl
  change (partialComp ((consume Y X).submatrix Prod.snd Prod.snd) J).submatrix _ _ = _
  rw [h, partialComp_assoc]
  rfl


/-- Relabeling both factors and their common window commutes with complete
contraction. No normalization or inhabitance is required. -/
theorem consume_reindex {β β' γ γ' : Type u} [Fintype β] [Fintype β']
    (e : β ≃ β') (f : γ ≃ γ') (Y : CMatrix β) (X : CMatrix (β × γ)) :
    consume (matReindex e Y) (matReindex (e.prodCongr f) X) =
      matReindex f (consume Y X) := by
  ext c c'
  simp only [consume_apply, matReindex_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun b =>
    Fintype.sum_equiv e.symm _ _ (fun b' => rfl))

/-- Relabel the still exposed blocks of a partial contraction. -/
theorem partialComp_reindex {α α' β γ γ' : Type u} [Fintype β]
    (e : α ≃ α') (f : γ ≃ γ') (M : CMatrix (α × β)) (N : CMatrix (β × γ)) :
    partialComp (matReindex (e.prodCongr (Equiv.refl β)) M)
      (matReindex ((Equiv.refl β).prodCongr f) N) =
      matReindex (e.prodCongr f) (partialComp M N) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [partialComp_apply, matReindex_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_symm, Equiv.refl_apply]


section SuffixCoordinates
variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The wholly consumed factor has a unique empty complement configuration. -/
instance suffixVacuumUnique (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Unique (∀ i, (suffixMatch (I := I) (O := O) k m hkm).complFam₁ i) where
  default := fun j => absurd j.isLt (by simp [suffixMatch])
  uniq x := funext fun j => absurd j.isLt (by simp [suffixMatch])

/-- Canonical coordinates of the wholly connected inner window, obtained
from the actual suffix matching's first-factor transport. -/
def suffixWindowEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Space (suffixOut O k m hkm) (suffixIn I k m hkm) ≃
      (∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i) :=
  (XFlatEquiv k m hkm).trans ((suffixMatch k m hkm).eM.trans
    ((splitAppendEquiv _ _).trans (Equiv.uniqueProd _ _)))

/-- Coordinates of the suffix complement, as induced by `compInS` and
`compOutS` through the existing packing equivalences. -/
def suffixComplementEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Space (fun j => I (compInS k m hkm j)) (fun j => O (compOutS k m hkm j)) ≃
      (∀ i, (suffixMatch (I := I) (O := O) k m hkm).complFam₂ i) :=
  (spaceIdxEquiv k m hkm).trans ((spacePackEquiv k m hkm).trans
    ((splitAppendEquiv _ _).trans (Equiv.uniqueProd _ _)))

/-- Split an outer comb's configurations into its connected window and
remaining comb configurations. All transports come from the suffix index
maps, including the explicit identification of matched basis labels. -/
def suffixSplitEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Space I O ≃ Space (suffixOut O k m hkm) (suffixIn I k m hkm) ×
      Space (fun j => I (compInS k m hkm j)) (fun j => O (compOutS k m hkm j)) :=
  (splitAppendEquiv I O).symm.trans
    (((suffixMatch k m hkm).eN.trans (suffixMatch k m hkm).eTransportEquiv).trans
      ((splitAppendEquiv _ _).trans
        ((suffixWindowEquiv k m hkm).symm.prodCongr (suffixComplementEquiv k m hkm).symm)))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
private theorem suffixWindowEquiv_symm (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (z : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i) :
    (suffixWindowEquiv (I := I) (O := O) k m hkm).symm z =
      (XFlatEquiv k m hkm).symm ((suffixMatch k m hkm).read₁ (default, z)) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
private theorem suffixComplementEquiv_apply (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (p : Space (fun j => I (compInS k m hkm j)) (fun j => O (compOutS k m hkm j))) :
    suffixComplementEquiv (I := I) (O := O) k m hkm p =
      complPack k m hkm (spaceIdxEquiv k m hkm p).1 (spaceIdxEquiv k m hkm p).2 := by
  simp only [suffixComplementEquiv, Equiv.trans_apply, spacePackEquiv, spacePack,
    Equiv.coe_fn_mk, Equiv.apply_symm_apply, Equiv.uniqueProd_apply]
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
private theorem suffixSplitEquiv_symm (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (b : Space (suffixOut O k m hkm) (suffixIn I k m hkm))
    (p : Space (fun j => I (compInS k m hkm j)) (fun j => O (compOutS k m hkm j))) :
    (suffixSplitEquiv (I := I) (O := O) k m hkm).symm (b, p) =
      splitAppendEquiv I O ((suffixMatch k m hkm).read₂
        (suffixWindowEquiv k m hkm b) (suffixComplementEquiv k m hkm p)) := by
  simp only [suffixSplitEquiv, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_symm,
    WireMatch.eTransportEquiv_symm_pack, WireMatch.read₂]

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- The existing suffix composition is precisely complete consumption of
its window in the explicitly derived split coordinates. -/
theorem suffixCompS_eq_consume (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))) :
    suffixCompS k m hkm J X =
      consume X (matReindex (suffixSplitEquiv k m hkm) J) := by
  ext p q
  rw [suffixCompS, matReindex_apply, suffixComp_apply, consume_apply]
  simp only [matReindex_apply, suffixSplitEquiv_symm, suffixComplementEquiv_apply]
  apply Fintype.sum_equiv (suffixWindowEquiv (I := I) (O := O) k m hkm).symm
  intro z
  apply Fintype.sum_equiv (suffixWindowEquiv (I := I) (O := O) k m hkm).symm
  intro z'
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
  simp only [suffixWindowEquiv_symm]
  congr 3

end SuffixCoordinates

section NestedSuffix
variable {nx nj : Nat} {IX OX : Fin (nx + 2) → Type u}
  {IJ OJ : Fin (nj + 2) → Type u}
  [∀ j, Fintype (IX j)] [∀ j, Fintype (OX j)]
  [∀ j, Fintype (IJ j)] [∀ j, Fintype (OJ j)]
  (kx mx : Nat) (hx : kx + mx + 1 ≤ nx + 1)
  (kj : Nat) (hj : kj + (nx - mx) + 1 ≤ nj + 1)
  (eI : ∀ j, IX (compInS kx mx hx j) ≃ suffixOut OJ kj (nx - mx) hj j)
  (eO : ∀ j, OX (compOutS kx mx hx j) ≃ suffixIn IJ kj (nx - mx) hj j)
  (J : CMatrix (Space IJ OJ)) (X : CMatrix (Space IX OX))
  (Y : CMatrix (Space (suffixOut OX kx mx hx) (suffixIn IX kx mx hx)))

/-- Nested suffix associativity at arbitrary depths and heterogeneous wires.
The right intermediate connects the complement of the pending window to `J`,
retaining that window for `Y`. Using a full suffix contraction for this
intermediate would consume those wires and change the network. The matching
between the two combs is given tooth by tooth by `eI` and `eO`. -/
theorem suffixCompS_assoc :
    let e := spaceEquiv eI eO
    let xp := matReindex (suffixSplitEquiv kx mx hx) X
    let jp := matReindex ((suffixSplitEquiv kj (nx - mx) hj).trans
      (e.symm.prodCongr (Equiv.refl _))) J
    suffixCompS kj (nx - mx) hj J (matReindex e (suffixCompS kx mx hx X Y)) =
      consume Y (partialComp xp jp) := by
  dsimp only
  rw [suffixCompS_eq_consume, suffixCompS_eq_consume]
  rw [← consume_partialComp]
  have h := consume_reindex (spaceEquiv eI eO) (Equiv.refl _)
    (consume Y (matReindex (suffixSplitEquiv kx mx hx) X))
    (matReindex ((suffixSplitEquiv kj (nx - mx) hj).trans
      ((spaceEquiv eI eO).symm.prodCongr (Equiv.refl _))) J)
  have hc : matReindex ((spaceEquiv eI eO).prodCongr (Equiv.refl _))
      (matReindex ((suffixSplitEquiv kj (nx - mx) hj).trans
        ((spaceEquiv eI eO).symm.prodCongr (Equiv.refl _))) J) =
      matReindex (suffixSplitEquiv kj (nx - mx) hj) J := by
    rw [matReindex_trans_apply]
    change matReindex ((spaceEquiv eI eO).prodCongr (Equiv.refl _))
      (matReindex ((spaceEquiv eI eO).prodCongr (Equiv.refl _)).symm
        (matReindex (suffixSplitEquiv kj (nx - mx) hj) J)) = _
    exact matReindex_matReindex_symm
      ((spaceEquiv eI eO).prodCongr (Equiv.refl _)) _
  rw [hc, matReindex_refl] at h
  exact h

/-- Explicit reindex coherence for the surviving configurations. The two
suffix packings are induced by the original index maps; `f` chooses the
coordinates of their final complement. In particular it can be the actual
`suffixComplementEquiv` or a toothwise family equivalence. -/
theorem suffixCompS_assoc_reindex {δ : Type u}
    (f : Space (fun j => IJ (compInS kj (nx - mx) hj j))
      (fun j => OJ (compOutS kj (nx - mx) hj j)) ≃ δ) :
    let e := spaceEquiv eI eO
    let xp := matReindex (suffixSplitEquiv kx mx hx) X
    let jp := matReindex ((suffixSplitEquiv kj (nx - mx) hj).trans
      (e.symm.prodCongr f)) J
    matReindex f
      (suffixCompS kj (nx - mx) hj J (matReindex e (suffixCompS kx mx hx X Y))) =
      consume Y (partialComp xp jp) := by
  dsimp only
  rw [suffixCompS_assoc kx mx hx kj hj eI eO]
  rw [← consume_reindex (Equiv.refl _) f, ← partialComp_reindex (Equiv.refl _) f]
  change consume Y (partialComp _ _) = consume Y (partialComp _ _)
  congr 2

end NestedSuffix

/-! ## Transport to the relabeled suffix API -/

section RelabeledSuffixCoordinates
variable {n m : Nat} {I O : Fin (n + 2) → Type u} {P Q : Fin (m + 1) → Type u}

/-- Split the outer configurations into the original inner configurations
and the complement selected by this join. This uses exactly the basis relabeling
and window identifications carried by `RelabeledSuffixData`, followed by the
index-derived suffix packing. It does not identify different join witnesses. -/
def RelabeledSuffixData.splitEquiv (a : RelabeledSuffixData I O m P Q) :
    Space I O ≃ Space P Q ×
      Space (fun j => I (a.compInIdx j)) (fun j => O (a.compOutIdx j)) :=
  (spaceEquiv a.eσI a.eσO).trans
    ((suffixSplitEquiv a.k m a.hkm).trans
      ((spaceEquiv a.winEquivP a.winEquivQ).symm.prodCongr (Equiv.refl _)))

/-- The relabeled suffix composition is complete consumption in its actual
join coordinates. Both the outer basis relabeling and the inner wire identifications
are retained; the bridge does not assume an independent link-product
characterization of arbitrary graph matches. -/
theorem relabeledSuffixComp_eq_consume [∀ j, Fintype (I j)] [∀ j, Fintype (O j)]
    [∀ j, Fintype (P j)] [∀ j, Fintype (Q j)]
    (a : RelabeledSuffixData I O m P Q) (J : CMatrix (Space I O)) (X : CMatrix (Space P Q)) :
    relabeledSuffixComp a J X = consume X (matReindex a.splitEquiv J) := by
  rw [relabeledSuffixComp, suffixCompS_eq_consume]
  have h := consume_reindex (spaceEquiv a.winEquivP a.winEquivQ) (Equiv.refl _)
    X (matReindex a.splitEquiv J)
  have hc : matReindex ((spaceEquiv a.winEquivP a.winEquivQ).prodCongr (Equiv.refl _))
      (matReindex a.splitEquiv J) =
      matReindex (suffixSplitEquiv a.k m a.hkm) (matReindex (spaceEquiv a.eσI a.eσO) J) := by
    unfold RelabeledSuffixData.splitEquiv
    rw [matReindex_trans_apply, matReindex_trans_apply]
    change matReindex ((spaceEquiv a.winEquivP a.winEquivQ).prodCongr (Equiv.refl _))
      (matReindex ((spaceEquiv a.winEquivP a.winEquivQ).prodCongr (Equiv.refl _)).symm _) = _
    exact matReindex_matReindex_symm _ _
  rw [hc, matReindex_refl] at h
  exact h

end RelabeledSuffixCoordinates

section NestedRelabeledSuffix
variable {nx nj m : Nat} {IX OX : Fin (nx + 2) → Type u}
  {IJ OJ : Fin (nj + 2) → Type u} {P Q : Fin (m + 1) → Type u}
  [∀ j, Fintype (IX j)] [∀ j, Fintype (OX j)]
  [∀ j, Fintype (IJ j)] [∀ j, Fintype (OJ j)]
  [∀ j, Fintype (P j)] [∀ j, Fintype (Q j)]
  (a : RelabeledSuffixData IX OX m P Q)
  (b : RelabeledSuffixData IJ OJ (nx - m)
    (fun j => IX (a.compInIdx j)) (fun j => OX (a.compOutIdx j)))
  (J : CMatrix (Space IJ OJ)) (X : CMatrix (Space IX OX)) (Y : CMatrix (Space P Q))

/-- Nested associativity for two pointwise-relabeled suffix operators, at
arbitrary depths and heterogeneous finite wires. The partial intermediate
connects the complement of `a` to `J` through `b`, retaining the window for
`Y`. This transports the existing product-coordinate associativity, whose
proof uses `WireFam.linkProduct_assoc`, without a new summation argument
[Chiribella2009Networks, comblong-pub.tex:342-355].

The statement is per pair of join witnesses. It makes no assertion that
changing their basis equivalences leaves the operators unchanged. -/
theorem relabeledSuffixComp_assoc :
    relabeledSuffixComp b J (relabeledSuffixComp a X Y) =
      consume Y (partialComp (matReindex a.splitEquiv X) (matReindex b.splitEquiv J)) := by
  rw [relabeledSuffixComp_eq_consume, relabeledSuffixComp_eq_consume, consume_partialComp]

/-- Reindex coherence of nested relabeled suffix composition. The surviving wires
are exactly `b.compInIdx` and `b.compOutIdx`; `f` may in particular be their
toothwise family equivalence. All intermediate transports are the explicit
`RelabeledSuffixData.splitEquiv` maps induced by the two joins. -/
theorem relabeledSuffixComp_assoc_reindex {δ : Type u}
    (f : Space (fun j => IJ (b.compInIdx j)) (fun j => OJ (b.compOutIdx j)) ≃ δ) :
    matReindex f (relabeledSuffixComp b J (relabeledSuffixComp a X Y)) =
      consume Y (partialComp (matReindex a.splitEquiv X)
        (matReindex (b.splitEquiv.trans ((Equiv.refl _).prodCongr f)) J)) := by
  rw [relabeledSuffixComp_assoc, ← consume_reindex (Equiv.refl _) f,
    ← partialComp_reindex (Equiv.refl _) f]
  change consume Y (partialComp _ _) = consume Y (partialComp _ _)
  congr 2

end NestedRelabeledSuffix
end QIT.HigherOrder.Comb
