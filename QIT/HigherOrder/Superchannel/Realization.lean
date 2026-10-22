/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HigherOrder.Superchannel
public import QIT.HigherOrder.Superchannel.MemoryCircuit
public import QIT.Channels.Superchannel.Relabel

/-!
# Finite-memory realization of deterministic superchannels

A deterministic superchannel acts on input-first Choi matrices indexed by
`a × b` and returns Choi matrices indexed by `c × d`. Its deterministic 2-comb
has chronological inputs `(c, b)` and outputs `(a, d)`. Physical relabeling
identifies singleton inner configurations with the original system labels.
The existing normalized-comb realization then supplies the two isometries.

The intermediate memory is carried coherently between the two steps. Exact
agreement is proved for every linear input operation, and spectator Choi blocks
extend the same fixed circuit to arbitrary joint ancillary operations. No rank,
invertibility, nonempty-system, or dimension-equality hypothesis is required.

The isometric and channel interfaces implement the realization theorem in
[Chiribella2008Supermaps, VersioneArchivio.tex:340-349].
-/

@[expose] public section

noncomputable section
namespace QIT.HigherOrder
universe u y z
variable {a b c d : Type u}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
open Comb

/-- Every deterministic superchannel has one fixed pair of finite-memory
isometries realizing all linear input operations and all independently typed
ancillary extensions. This is the isometric realization theorem of
[Chiribella2008Supermaps, VersioneArchivio.tex:340-349], with slot-first memory
ordering. Empty finite systems and zero-dimensional memories are included. -/
theorem IsDeterministicSuperchannel.exists_prePost_isometries
    {S : MatrixMap (a × b) (c × d)}
    (hS : IsDeterministicSuperchannel.{u,u,u,u,y,z} S) :
    ∃ (m n : Nat) (V : ReferenceIsometry c (a × Memory.{u} m))
      (W : ReferenceIsometry (b × Memory.{u} m) (d × Memory.{u} n)),
      (∀ Φ : MatrixMap a b, action S Φ =
        prePostAction (MatrixMap.ofReferenceIsometry V) W.outputChannel.map Φ) ∧
      ∀ (r : Type y) (s : Type z)
        [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Φ : MatrixMap (a × r) (b × s)),
        ancillaryAction S Φ = prePostAncillaryAction
          (MatrixMap.ofReferenceIsometry V) W.outputChannel.map Φ := by
  classical
  let I : Fin 2 → Type u := Fin.cons (α := fun _ : Fin 2 => Type u) c (fun _ => b)
  let O : Fin 2 → Type u := Fin.cons (α := fun _ : Fin 2 => Type u) a (fun _ => d)
  let : ∀ j, Fintype (I j) :=
    Fin.cases (motive := fun j => Fintype
      (Fin.cons (α := fun _ : Fin 2 => Type u) c (fun _ : Fin 1 => b) j))
      (inferInstance : Fintype c) (fun _ => (inferInstance : Fintype b))
  let : ∀ j, Fintype (O j) :=
    Fin.cases (motive := fun j => Fintype
      (Fin.cons (α := fun _ : Fin 2 => Type u) a (fun _ : Fin 1 => d) j))
      (inferInstance : Fintype a) (fun _ => (inferInstance : Fintype d))
  let : ∀ j, DecidableEq (I j) :=
    Fin.cases (motive := fun j => DecidableEq
      (Fin.cons (α := fun _ : Fin 2 => Type u) c (fun _ : Fin 1 => b) j))
      (inferInstance : DecidableEq c) (fun _ => (inferInstance : DecidableEq b))
  let : ∀ j, DecidableEq (O j) :=
    Fin.cases (motive := fun j => DecidableEq
      (Fin.cons (α := fun _ : Fin 2 => Type u) a (fun _ : Fin 1 => d) j))
      (inferInstance : DecidableEq a) (fun _ => (inferInstance : DecidableEq d))
  let ea : (∀ j, innerInput O j) ≃ a := oneConfigEquiv (innerInput O)
  let eb : (∀ j, innerOutput I j) ≃ b := oneConfigEquiv (innerOutput I)
  let R := relabelSupermap ea eb
  let T := S.comp R
  have hT : IsDeterministicSuperchannel.{u,u,u,u,y,z} T :=
    hS.comp (isDeterministicSuperchannel_relabel ea eb)
  have hN := (isDeterministicSuperchannel_iff_normalized_choi I O T).mp hT
  obtain ⟨dims, chain, hc⟩ := (normalized_iff_exists_memoryChain _).mp hN
  have hcT : actionMap I O (MatrixMap.choi chain.chainMap) = T := by
    rw [hc]
    exact actionMap_reindexed_choi I O T
  let V := chain.preIsometry ea
  let W := chain.postIsometry eb
  have hordinary (Φ : MatrixMap a b) :
      action S Φ = prePostAction (MatrixMap.ofReferenceIsometry V)
        W.outputChannel.map Φ := by
    rw [chain.prePostAction_eq_reindexedAction ea eb Φ, hcT]
    change MatrixMap.ofChoiMatrix (S (MatrixMap.choi Φ)) =
      MatrixMap.ofChoiMatrix (S (relabelSupermap ea eb
        ((MatrixMap.choi Φ).submatrix (Equiv.prodCongr ea eb) (Equiv.prodCongr ea eb))))
    rw [relabelSupermap_submatrix]
  refine ⟨dims 0, dims 1, V, W, hordinary, ?_⟩
  intro r s _ _ _ _ Φ
  exact ancillaryAction_eq_prePostAncillaryAction S _ _ hordinary Φ

/-- Channel form of `exists_prePost_isometries`: preprocessing produces the
slot input and memory, and postprocessing consumes the slot output and the same
memory. The same channels realize every input map and every ancillary extension. -/
theorem IsDeterministicSuperchannel.exists_prePost_channels
    {S : MatrixMap (a × b) (c × d)}
    (hS : IsDeterministicSuperchannel.{u,u,u,u,y,z} S) :
    ∃ (m : Nat) (P : Channel c (a × Memory.{u} m))
      (Q : Channel (b × Memory.{u} m) d),
      (∀ Φ : MatrixMap a b, action S Φ = prePostAction P.map Q.map Φ) ∧
      ∀ (r : Type y) (s : Type z)
        [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Φ : MatrixMap (a × r) (b × s)),
        ancillaryAction S Φ = prePostAncillaryAction P.map Q.map Φ := by
  obtain ⟨m, n, V, W, h, ha⟩ := hS.exists_prePost_isometries
  exact ⟨m, Channel.ofReferenceIsometry V, W.outputChannel, h, ha⟩

/-- Literal isometric circuit formula of
[Chiribella2008Supermaps, VersioneArchivio.tex:340-349], together with exact action
on every ancillary extension using the same witnesses. The final partial trace
discards only the postprocessing environment; the intermediate memory remains
coherent across the inserted operation. Equality holds on every input matrix. -/
theorem IsDeterministicSuperchannel.exists_prePost_formula
    {S : MatrixMap (a × b) (c × d)}
    (hS : IsDeterministicSuperchannel.{u,u,u,u,y,z} S) :
    ∃ (m n : Nat) (V : ReferenceIsometry c (a × Memory.{u} m))
      (W : ReferenceIsometry (b × Memory.{u} m) (d × Memory.{u} n)),
      (∀ (Φ : MatrixMap a b) (X : CMatrix c),
        action S Φ X = partialTraceB
          (W.matrix * (MatrixMap.kron Φ LinearMap.id
            (V.matrix * X * V.matrix.conjTranspose)) * W.matrix.conjTranspose)) ∧
      ∀ (r : Type y) (s : Type z)
        [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Φ : MatrixMap (a × r) (b × s)),
        ancillaryAction S Φ = prePostAncillaryAction
          (MatrixMap.ofReferenceIsometry V) W.outputChannel.map Φ := by
  obtain ⟨m, n, V, W, h, ha⟩ := hS.exists_prePost_isometries
  refine ⟨m, n, V, W, ?_, ha⟩
  intro Φ X
  calc
    action S Φ X = prePostAction (MatrixMap.ofReferenceIsometry V)
        W.outputChannel.map Φ X := congrArg (fun F : MatrixMap c d => F X) (h Φ)
    _ = _ := by
      rw [prePostAction_apply, W.outputChannel_map, MatrixMap.ofReferenceIsometry_apply]

end QIT.HigherOrder
