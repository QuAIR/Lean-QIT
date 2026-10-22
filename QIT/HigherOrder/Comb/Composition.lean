/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Closure

/-!
# Suffix composition with pointwise basis relabeling

This module transports monotone-window composition through pointwise wire
basis equivalences. `RelabeledSuffixData` records a target family, a suffix
window, and its basis identifications. Its `σ` selects the target wire types;
`spaceEquiv eσI eσO` relabels each basis at the same position. It does not
permute the configurations of the original teeth.

Consequently the endpoint selections `ιO` and `ιI` alone do not specify the
network contracted by `relabeledSuffixComp`, and the data do not certify
acyclicity of those selections. The normalization results below concern this
precisely defined relabeled suffix operator. Genuine selected-wire network
composition and its causal normalization are provided by `CausalJoin.comp`
in `QIT.HigherOrder.Comb.CausalComposition`.

The suffix rule and normalization recursion are the specializations at
[Chiribella2009Networks, comblong-pub.tex:1279-1286,860-877].
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder.Comb
open QIT.WireFam

/-! ## Relabeled suffix data -/

section RelabeledSuffixDataDef
variable {n m : Nat} {I O : Fin (n + 2) → Type u} {P Q : Fin (m + 1) → Type u}

/-- Pointwise basis relabeling into a suffix window. The endpoint maps and
`σ` identify target wire types; they do not assert that the operator realizes
the network defined by those endpoint maps. -/
structure RelabeledSuffixData (I O : Fin (n + 2) → Type u) (m : Nat)
    (P Q : Fin (m + 1) → Type u) where
  /-- Selected output indices naming the target window types. -/
  ιO : Fin (m + 1) → Fin (n + 2)
  /-- Selected input indices naming the target window types. -/
  ιI : Fin (m + 1) → Fin (n + 2)
  /-- No outer output wire is consumed twice. -/
  hιO : Function.Injective ιO
  /-- No outer input wire is fed twice. -/
  hιI : Function.Injective ιI
  /-- The inner comb's input wires, identified with the consumed outer
  output wires. -/
  eP : ∀ j, P j ≃ O (ιO j)
  /-- The inner comb's output wires, identified with the fed outer input
  wires. -/
  eQ : ∀ j, Q j ≃ I (ιI j)
  /-- The offset of the monotone window in the target family. -/
  k : Nat
  /-- The window fits into the target outer family. -/
  hkm : k + m + 1 ≤ n + 1
  /-- Target-family index permutation; not a configuration permutation. -/
  σ : Fin (n + 2) ≃ Fin (n + 2)
  /-- Selected outputs name the target window output types. -/
  hσO : ∀ j, σ (suffixOutIdx k m hkm j) = ιO j
  /-- Selected inputs name the target window input types. -/
  hσI : ∀ j, σ (suffixInIdx k m hkm j) = ιI j
  /-- Pointwise input basis equivalences into the target family. -/
  eσI : ∀ j, I j ≃ I (σ j)
  /-- Pointwise output basis equivalences into the target family. -/
  eσO : ∀ j, O j ≃ O (σ j)

/-- The original index naming the target composite input-wire type. -/
def RelabeledSuffixData.compInIdx (a : RelabeledSuffixData I O m P Q) (j : Fin (n - m + 1)) :
    Fin (n + 2) :=
  a.σ (compInS a.k m a.hkm j)

/-- The original index naming the target composite output-wire type. -/
def RelabeledSuffixData.compOutIdx (a : RelabeledSuffixData I O m P Q) (j : Fin (n - m + 1)) :
    Fin (n + 2) :=
  a.σ (compOutS a.k m a.hkm j)

/-- The inner comb's input wires, read as window outputs of the target
outer family. -/
def RelabeledSuffixData.winEquivP (a : RelabeledSuffixData I O m P Q) (j : Fin (m + 1)) :
    P j ≃ suffixOut (fun j => O (a.σ j)) a.k m a.hkm j :=
  (a.eP j).trans (Equiv.cast (congrArg O (a.hσO j))).symm

/-- The inner comb's output wires, read as window inputs of the target
outer family. -/
def RelabeledSuffixData.winEquivQ (a : RelabeledSuffixData I O m P Q) (j : Fin (m + 1)) :
    Q j ≃ suffixIn (fun j => I (a.σ j)) a.k m a.hkm j :=
  (a.eQ j).trans (Equiv.cast (congrArg I (a.hσI j))).symm

/-- Apply pointwise basis equivalences, contract the resulting suffix
window, and retain its complement in the target wire families. -/
noncomputable def relabeledSuffixComp [instI : ∀ j, Fintype (I j)] [instO : ∀ j, Fintype (O j)]
    (a : RelabeledSuffixData I O m P Q)
    (J : CMatrix (Space I O)) (X : CMatrix (Space P Q)) :
    CMatrix (Space (fun j : Fin (n - m + 1) => I (a.compInIdx j))
      (fun j : Fin (n - m + 1) => O (a.compOutIdx j))) :=
  @suffixCompS n (fun j => I (a.σ j)) (fun j => O (a.σ j))
    (fun j => instI (a.σ j)) (fun j => instO (a.σ j))
    a.k m a.hkm (matReindex (spaceEquiv a.eσI a.eσO) J)
    (matReindex (spaceEquiv a.winEquivP a.winEquivQ) X)

end RelabeledSuffixDataDef

/-! ## Closure by transport -/

section Closures
variable {n m : Nat} {I O : Fin (n + 2) → Type u} {P Q : Fin (m + 1) → Type u}
variable [instI : ∀ j, Fintype (I j)] [instDI : ∀ j, DecidableEq (I j)]
variable [instO : ∀ j, Fintype (O j)] [instDO : ∀ j, DecidableEq (O j)]
variable [instP : ∀ j, Fintype (P j)] [instDP : ∀ j, DecidableEq (P j)]
variable [instQ : ∀ j, Fintype (Q j)] [instDQ : ∀ j, DecidableEq (Q j)]

/-- Probabilistic domination transports along pointwise wire equivalences:
positivity, the dominating normalized comb, and domination each ride the
`matReindex` transports. -/
theorem isProbabilistic_reindex {r : Nat} {A B A' B' : Fin (r + 1) → Type u}
    [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    [∀ j, Fintype (A' j)] [∀ j, DecidableEq (A' j)]
    [∀ j, Fintype (B' j)] [∀ j, DecidableEq (B' j)]
    (eA : ∀ j, A j ≃ A' j) (eB : ∀ j, B j ≃ B' j)
    {J : CMatrix (Space A B)} (h : IsProbabilistic A B J) :
    IsProbabilistic A' B' (matReindex (spaceEquiv eA eB) J) := by
  obtain ⟨hpsd, K, hK, hle⟩ := h
  exact ⟨(matReindex_posSemidef_iff (spaceEquiv eA eB) J).mpr hpsd,
    matReindex (spaceEquiv eA eB) K, (Normalized.reindex_iff eA eB K).mp hK,
    matReindex_le _ hle⟩

/-- Pointwise basis transport and suffix contraction preserve normalization.
This theorem is about the relabeled suffix operator defined above. -/
theorem Normalized.relabeled_suffix_comp (a : RelabeledSuffixData I O m P Q)
    {J : CMatrix (Space I O)} (hJ : Normalized I O J)
    {X : CMatrix (Space P Q)} (hX : Normalized P Q X) :
    Normalized (fun j : Fin (n - m + 1) => I (a.compInIdx j))
      (fun j : Fin (n - m + 1) => O (a.compOutIdx j)) (relabeledSuffixComp a J X) :=
  @normalized_suffix_comp_final n (fun j => I (a.σ j)) (fun j => O (a.σ j))
    (fun j => instI (a.σ j)) (fun j => instDI (a.σ j))
    (fun j => instO (a.σ j)) (fun j => instDO (a.σ j))
    a.k m a.hkm
    (matReindex (spaceEquiv a.eσI a.eσO) J)
    ((@Normalized.reindex_iff (n + 2) I O (fun j => I (a.σ j)) (fun j => O (a.σ j))
      instI instDI instO instDO (fun j => instI (a.σ j))
      (fun j => instDI (a.σ j)) (fun j => instO (a.σ j))
      (fun j => instDO (a.σ j)) a.eσI a.eσO J).mp hJ)
    (matReindex (spaceEquiv a.winEquivP a.winEquivQ) X)
    ((@Normalized.reindex_iff (m + 1) P Q
      (suffixOut (fun j => O (a.σ j)) a.k m a.hkm)
      (suffixIn (fun j => I (a.σ j)) a.k m a.hkm)
      instP instDP instQ instDQ
      (fun j => instO (a.σ (suffixOutIdx a.k m a.hkm j)))
      (fun j => instDO (a.σ (suffixOutIdx a.k m a.hkm j)))
      (fun j => instI (a.σ (suffixInIdx a.k m a.hkm j)))
      (fun j => instDI (a.σ (suffixInIdx a.k m a.hkm j))) a.winEquivP a.winEquivQ X).mp hX)

omit instP instDP instQ instDQ in
/-- Composition of a positive outer operator with a positive inner comb
after suffix basis relabeling is positive. -/
theorem relabeledSuffixComp_posSemidef (a : RelabeledSuffixData I O m P Q)
    {J : CMatrix (Space I O)} (hJ : J.PosSemidef)
    {X : CMatrix (Space P Q)} (hX : X.PosSemidef) :
    (relabeledSuffixComp a J X).PosSemidef :=
  matReindex_posSemidef _
    (@suffixComp_posSemidef n (fun j => I (a.σ j)) (fun j => O (a.σ j))
      (fun j => instI (a.σ j)) (fun j => instDI (a.σ j))
      (fun j => instO (a.σ j)) (fun j => instDO (a.σ j))
      a.k m a.hkm _ _
      ((matReindex_posSemidef_iff (spaceEquiv a.eσI a.eσO) J).mpr hJ)
      ((matReindex_posSemidef_iff (spaceEquiv a.winEquivP a.winEquivQ) X).mpr hX))

/-- A probabilistic outer comb composed with a normalized inner comb after
suffix basis relabeling is probabilistic. -/
theorem IsProbabilistic.relabeled_suffix_comp (a : RelabeledSuffixData I O m P Q)
    {J : CMatrix (Space I O)} (hJ : IsProbabilistic (n := n + 1) I O J)
    {X : CMatrix (Space P Q)} (hX : Normalized P Q X) :
    IsProbabilistic (fun j : Fin (n - m + 1) => I (a.compInIdx j))
      (fun j : Fin (n - m + 1) => O (a.compOutIdx j)) (relabeledSuffixComp a J X) :=
  @IsProbabilistic.suffix_comp n (fun j => I (a.σ j)) (fun j => O (a.σ j))
    (fun j => instI (a.σ j)) (fun j => instDI (a.σ j))
    (fun j => instO (a.σ j)) (fun j => instDO (a.σ j))
    a.k m a.hkm _
    (@isProbabilistic_reindex (n + 1) I O (fun j => I (a.σ j)) (fun j => O (a.σ j))
      instI instDI instO instDO (fun j => instI (a.σ j))
      (fun j => instDI (a.σ j)) (fun j => instO (a.σ j))
      (fun j => instDO (a.σ j)) a.eσI a.eσO _ hJ) _
    ((@Normalized.reindex_iff (m + 1) P Q
      (suffixOut (fun j => O (a.σ j)) a.k m a.hkm)
      (suffixIn (fun j => I (a.σ j)) a.k m a.hkm)
      instP instDP instQ instDQ
      (fun j => instO (a.σ (suffixOutIdx a.k m a.hkm j)))
      (fun j => instDO (a.σ (suffixOutIdx a.k m a.hkm j)))
      (fun j => instI (a.σ (suffixInIdx a.k m a.hkm j)))
      (fun j => instDI (a.σ (suffixInIdx a.k m a.hkm j))) a.winEquivP a.winEquivQ X).mp hX)

/-- Composition of two probabilistic combs after suffix basis relabeling is
probabilistic. -/
theorem IsProbabilistic.relabeled_suffix_comp_probabilistic (a : RelabeledSuffixData I O m P Q)
    {J : CMatrix (Space I O)} (hJ : IsProbabilistic (n := n + 1) I O J)
    {X : CMatrix (Space P Q)} (hX : IsProbabilistic (n := m) P Q X) :
    IsProbabilistic (fun j : Fin (n - m + 1) => I (a.compInIdx j))
      (fun j : Fin (n - m + 1) => O (a.compOutIdx j)) (relabeledSuffixComp a J X) :=
  @IsProbabilistic.suffix_comp_probabilistic n (fun j => I (a.σ j)) (fun j => O (a.σ j))
    (fun j => instI (a.σ j)) (fun j => instDI (a.σ j))
    (fun j => instO (a.σ j)) (fun j => instDO (a.σ j))
    a.k m a.hkm _
    (@isProbabilistic_reindex (n + 1) I O (fun j => I (a.σ j)) (fun j => O (a.σ j))
      instI instDI instO instDO (fun j => instI (a.σ j))
      (fun j => instDI (a.σ j)) (fun j => instO (a.σ j))
      (fun j => instDO (a.σ j)) a.eσI a.eσO _ hJ) _
    (@isProbabilistic_reindex m P Q
      (suffixOut (fun j => O (a.σ j)) a.k m a.hkm)
      (suffixIn (fun j => I (a.σ j)) a.k m a.hkm)
      instP instDP instQ instDQ
      (fun j => instO (a.σ (suffixOutIdx a.k m a.hkm j)))
      (fun j => instDO (a.σ (suffixOutIdx a.k m a.hkm j)))
      (fun j => instI (a.σ (suffixInIdx a.k m a.hkm j)))
      (fun j => instDI (a.σ (suffixInIdx a.k m a.hkm j))) a.winEquivP a.winEquivQ _ hX)

end Closures

end QIT.HigherOrder.Comb

end

end
