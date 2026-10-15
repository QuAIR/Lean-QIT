/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Map.ChoiCharacterization
public import QIT.Core.Channel
public import QIT.Util.Wires.LinkProduct

/-!
# Choi matrices of composed maps via the link product

The Choi matrix of a composition of finite matrix maps is the link product of
the two Choi matrices over the shared wire, in the shape in which the sources
compose Choi operators of higher-order maps
[Chiribella2009Networks, comblong-pub.tex:295-302], with the circuit
composition rule [Chiribella2007Architecture, qcombs-2.tex:223-235].

The Choi convention of this library is input-first (`choi Φ : CMatrix (a × b)`),
so the first-applied map's Choi matrix enters the link product in the first
position (private input block first, shared output block last) and the
second-applied map's Choi matrix enters in the second position (shared input
block first): the built-in transpose of the link product on the shared block
of the first factor is exactly the source transpose on the first-applied
map's Choi operator. The engine form `choi_comp_eq_engine` spells the source
partial trace of a tensor-fashion product literally.

Every statement holds for arbitrary complex-linear maps: no complete
positivity, trace preservation, dimension, or invertibility hypothesis is
used.

The swap, associativity, and permutation-coherence properties of the link
product are realized on the link-product layer; positivity preservation is
realized on top of this bridge in `QIT.Core.Map.LinkProductPositivity`
(`QIT.WireFam.linkProduct_posSemidef`), following the source proof of the
link-product properties theorem
[Chiribella2009Networks, comblong-pub.tex:342-355].

## Symbol correspondence with the sources

For a first-applied map `E : MatrixMap a b` and a second-applied map
`N : MatrixMap b c` over the shared index type `b`:

* the source's first-applied map `M` and its output-first Choi operator
  `J^M` correspond to `E` and `choi E` (input-first: the shared block `b` is
  the second factor of `a × b`), so the source transpose on the shared
  factor of the first Choi operator is exactly the built-in shared-block
  transpose of the link product on its first factor, spelled
  `partialTransposeB` in the engine form `choi_comp_eq_engine`;
* the source's second-applied map `N` and `J^N` correspond to `N` and
  `choi N` (the shared block `b` is the first factor of `b × c`);
* the source composition link `N * M` corresponds to `WireFam.linkProduct`;
* the source partial trace `Tr` over the shared system corresponds to the
  partial-trace packaging of `choi_comp_eq_engine`;
* reading a Choi matrix in the source's output-first order is the product
  swap `.submatrix (Equiv.prodComm _ _)`, available in `choi_comp_prodComm`.

## Main results

* `MatrixMap.choi_comp_apply`: entrywise basis equation for the Choi matrix
  of a composition.
* `MatrixMap.choi_comp_eq_linkProduct`: the family-form bridge, packaging the
  three Choi matrices through the split transports of the wire layer.
* `MatrixMap.choi_comp_eq_engine`: the source partial-trace engine form.
* `MatrixMap.choi_comp`: the plain-type specialization at a single shared
  wire.
* `MatrixMap.choi_comp_channel`: the channel-typed corollary.

## Tags

Choi matrix, composition, link product, higher-order map
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open QIT.WireFam

namespace QIT

universe u v w

noncomputable section

namespace MatrixMap

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-! ## The entrywise basis equation -/

/-- Entrywise Choi matrix of a composition: the `(i, j), (i', j')` entry of
the Choi matrix of `N ∘ E` is the contraction of the Choi matrices of `E` and
`N` over the shared basis indices, in the composition shape of
[Chiribella2009Networks, comblong-pub.tex:295-302]. -/
theorem choi_comp_apply (E : MatrixMap a b) (N : MatrixMap b c) (i i' : a) (j j' : c) :
    choi (N.comp E) (i, j) (i', j') =
      ∑ z : b, ∑ z' : b, choi E (i, z) (i', z') * choi N (z, j) (z', j') := by
  have hN := map_eq_sum_single N (E (Matrix.single i i' (1 : ℂ)))
  simp only [choi, LinearMap.comp_apply]
  rw [hN]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq b] in
private theorem sum_swap (f : b → b → ℂ) :
    ∑ z : b, ∑ z' : b, f z z' = ∑ z : b, ∑ z' : b, f z' z := by
  have h1 : ∑ z : b, ∑ z' : b, f z z' = ∑ p : b × b, f p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : b × b => f p.1 p.2)).symm
  have h2 : ∑ z : b, ∑ z' : b, f z' z = ∑ p : b × b, f p.2 p.1 :=
    (Fintype.sum_prod_type (fun p : b × b => f p.2 p.1)).symm
  rw [h1, h2]
  exact (Equiv.sum_comp (Equiv.prodComm b b) (fun p : b × b => f p.1 p.2)).symm

/-- Transposed entrywise reading: the same entry expands with the shared
indices of both factors exchanged, which is the literal entrywise shape of
the link product (the shared block of the first factor enters transposed),
matching the transposed entrywise form of the source composition rule
[Chiribella2009Networks, comblong-pub.tex:295-302]. -/
theorem choi_comp_apply_swap (E : MatrixMap a b) (N : MatrixMap b c)
    (i i' : a) (j j' : c) :
    choi (N.comp E) (i, j) (i', j') =
      ∑ z : b, ∑ z' : b, choi E (i, z') (i', z) * choi N (z', j) (z, j') := by
  rw [choi_comp_apply]
  exact sum_swap (fun z z' => choi E (i, z) (i', z') * choi N (z, j) (z', j'))

/-! ## The family-form bridge -/

section Families

variable {m s r : ℕ}
variable {A : Fin m → Type u} {B : Fin s → Type u} {C : Fin r → Type u}
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ k, Fintype (B k)] [∀ k, DecidableEq (B k)]
variable [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]

/-- The family-form bridge: the Choi matrix of a composition, packaged through
the split transport, is the link product of the two packaged Choi matrices
over the shared wire family, in the composition shape of
[Chiribella2009Networks, comblong-pub.tex:295-302] with the general link
product of [Chiribella2009Networks, comblong-pub.tex:315-327]. With the
input-first Choi convention of this library, the first-applied map's private
input block is the link product's first block, so the built-in shared-block
transpose of the link product lands on the first-applied map's shared output
block, exactly as in the source transpose. -/
theorem choi_comp_eq_linkProduct (E : MatrixMap (∀ i, A i) (∀ k, B k))
    (N : MatrixMap (∀ k, B k) (∀ j, C j)) :
    matReindex (splitAppendEquiv A C).symm (choi (N.comp E)) =
      linkProduct A B C (matReindex (splitAppendEquiv A B).symm (choi E))
        (matReindex (splitAppendEquiv B C).symm (choi N)) := by
  ext p q
  rw [matReindex_apply, Equiv.symm_symm]
  rcases hp : splitAppendEquiv A C p with ⟨g, w⟩
  rcases hq : splitAppendEquiv A C q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv A C).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv A C).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, choi_comp_apply, linkProduct_apply]
  simp only [matReindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact sum_swap (fun z z' => choi E (g, z) (g', z') * choi N (z, w) (z', w'))

/-- Engine form of the composition rule: the packaged Choi matrix of the
composition is the two-system partial trace of the tensor-fashion product of
the partially transposed first Choi matrix with the second, in the literal
shape in which the source composes Choi operators
[Chiribella2009Networks, comblong-pub.tex:295-302]. -/
theorem choi_comp_eq_engine (E : MatrixMap (∀ i, A i) (∀ k, B k))
    (N : MatrixMap (∀ k, B k) (∀ j, C j)) :
    matReindex (splitAppendEquiv A C).symm (choi (N.comp E)) =
      matReindex (splitAppendEquiv A C).symm
        (QIT.partialTraceA (matReindex (midSwapEquiv _ _ _)
          (engineProduct A B C (matReindex (splitAppendEquiv A B).symm (choi E))
            (matReindex (splitAppendEquiv B C).symm (choi N))))) := by
  rw [choi_comp_eq_linkProduct, linkProduct_eq_engine]

end Families

/-! ## The plain-type specialization at a single shared wire -/

section Plain

variable {α β γ : Type u}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

/-- Reading a single-wire constant append family back as a plain product
index. -/
def appendToProd (a b : Type u) :
    (∀ i, append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) i) ≃ a × b :=
  (splitAppendEquiv (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)).trans
    ((Equiv.funUnique (Fin 1) a).prodCongr (Equiv.funUnique (Fin 1) b))

/-- Transport between a plain product index and the single-wire constant
append family. -/
def prodToAppend (a b : Type u) :
    (a × b) ≃ (∀ i, append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) i) :=
  (appendToProd a b).symm

/-- Reading a packaged point of the single-wire append family back through
the product transport recovers the pair of the two singleton readings. -/
theorem appendToProd_pack (a b : Type u) (g : Fin 1 → a) (z : Fin 1 → b) :
    appendToProd a b
        ((splitAppendEquiv (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)).symm (g, z)) =
      (g default, z default) := by
  simp [appendToProd, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply,
    Equiv.funUnique_apply]

/-- Assembling a plain pair through the product transport produces the
packaged constant configuration. -/
theorem appendToProd_symm_apply (a b : Type u) (i : a) (j : b) :
    (appendToProd a b).symm (i, j) =
      (splitAppendEquiv (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)).symm
        (fun _ => i, fun _ => j) := by
  apply (appendToProd a b).injective
  rw [Equiv.apply_symm_apply, appendToProd_pack]

/-- Plain-type specialization at a single shared wire: the Choi matrix of the
composition of two maps on plain index types is the link product of the two
Choi matrices over the constant single-wire families, transported back to
the plain product index, in the composition shape of
[Chiribella2009Networks, comblong-pub.tex:295-302] with the circuit
composition rule [Chiribella2007Architecture, qcombs-2.tex:223-235]. -/
theorem choi_comp (E : MatrixMap α β) (N : MatrixMap β γ) :
    choi (N.comp E) =
      matReindex (appendToProd α γ)
        (linkProduct (fun _ : Fin 1 => α) (fun _ : Fin 1 => β) (fun _ : Fin 1 => γ)
          (matReindex (prodToAppend α β) (choi E))
          (matReindex (prodToAppend β γ) (choi N))) := by
  ext ij kl
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨i', j'⟩
  rw [choi_comp_apply]
  simp only [matReindex_apply]
  rw [appendToProd_symm_apply α γ i j, appendToProd_symm_apply α γ i' j',
    linkProduct_apply (fun _ : Fin 1 => α) (fun _ : Fin 1 => β) (fun _ : Fin 1 => γ)
      (matReindex (prodToAppend α β) (choi E)) (matReindex (prodToAppend β γ) (choi N))
      (fun _ => i) (fun _ => i') (fun _ => j) (fun _ => j')]
  simp only [matReindex_apply]
  have hE : ∀ z : Fin 1 → β, (prodToAppend α β).symm
      ((splitAppendEquiv (fun _ : Fin 1 => α) (fun _ : Fin 1 => β)).symm (fun _ => i, z))
      = (i, z default) := fun z => appendToProd_pack α β (fun _ => i) z
  have hE' : ∀ z : Fin 1 → β, (prodToAppend α β).symm
      ((splitAppendEquiv (fun _ : Fin 1 => α) (fun _ : Fin 1 => β)).symm (fun _ => i', z))
      = (i', z default) := fun z => appendToProd_pack α β (fun _ => i') z
  have hN : ∀ z : Fin 1 → β, (prodToAppend β γ).symm
      ((splitAppendEquiv (fun _ : Fin 1 => β) (fun _ : Fin 1 => γ)).symm (z, fun _ => j))
      = (z default, j) := fun z => appendToProd_pack β γ z (fun _ => j)
  have hN' : ∀ z : Fin 1 → β, (prodToAppend β γ).symm
      ((splitAppendEquiv (fun _ : Fin 1 => β) (fun _ : Fin 1 => γ)).symm (z, fun _ => j'))
      = (z default, j') := fun z => appendToProd_pack β γ z (fun _ => j')
  simp only [hE, hE', hN, hN']
  have hfin : ∀ G : β → β → ℂ,
      ∑ z : Fin 1 → β, ∑ z' : Fin 1 → β, G (z default) (z' default)
        = ∑ t : β, ∑ t' : β, G t t' := by
    intro G
    have hout : ∑ z : Fin 1 → β, ∑ z' : Fin 1 → β, G (z default) (z' default)
        = ∑ t : β, ∑ z' : Fin 1 → β, G t (z' default) :=
      Equiv.sum_comp (Equiv.funUnique (Fin 1) β) (fun t => ∑ z' : Fin 1 → β, G t (z' default))
    rw [hout]
    exact Finset.sum_congr rfl fun t _ =>
      Equiv.sum_comp (Equiv.funUnique (Fin 1) β) (fun t' => G t t')
  rw [hfin (fun t t' => choi E (i, t') (i', t) * choi N (t', j) (t, j'))]
  exact sum_swap (fun z z' => choi E (i, z) (i', z') * choi N (z, j) (z', j'))

/-- Channel-typed corollary: the Choi matrix of the sequential composition of
two channels is the shared-wire link product of the two Choi matrices, the
ordinary sequential composition specialization of the source composition
rule [Chiribella2009Networks, comblong-pub.tex:295-302]. -/
theorem choi_comp_channel (Phi : Channel α β) (Psi : Channel β γ) :
    choi (Psi.comp Phi).map =
      matReindex (appendToProd α γ)
        (linkProduct (fun _ : Fin 1 => α) (fun _ : Fin 1 => β) (fun _ : Fin 1 => γ)
          (matReindex (prodToAppend α β) (choi Phi.map))
          (matReindex (prodToAppend β γ) (choi Psi.map))) :=
  choi_comp Phi.map Psi.map

/-- Source-ordering spelling: reading every Choi matrix in the output-first
order of the sources (through the product swap) carries the plain-type
composition rule to the source-shaped statement. -/
theorem choi_comp_prodComm (E : MatrixMap α β) (N : MatrixMap β γ) :
    (choi (N.comp E)).submatrix (Equiv.prodComm γ α) (Equiv.prodComm γ α) =
      (matReindex (appendToProd α γ)
        (linkProduct (fun _ : Fin 1 => α) (fun _ : Fin 1 => β) (fun _ : Fin 1 => γ)
          (matReindex (prodToAppend α β) (choi E))
          (matReindex (prodToAppend β γ) (choi N)))).submatrix
        (Equiv.prodComm γ α) (Equiv.prodComm γ α) := by
  rw [choi_comp]

end Plain

end MatrixMap

end

end QIT
