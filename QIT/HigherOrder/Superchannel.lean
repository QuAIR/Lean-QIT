/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.Superchannel
public import QIT.Channels.CompleteAdmissibility.Positivity
public import QIT.HigherOrder.Comb.Characterization
public import QIT.HigherOrder.Comb.OneTooth

/-!
# One-slot superchannels are deterministic two-combs

The chronological wires are `H₀ = I 0`, `H₁ = O 0`, `H₂ = I 1`,
`H₃ = O 1`. An inserted channel runs from `H₁` to `H₂`, and the resulting
channel runs from `H₀` to `H₃`. A channel is a one-comb; this transformation
of channels is a two-comb.

The local Choi order of the transformation is `((H₁,H₂),(H₀,H₃))`.
`Comb.actionEquiv` permutes the comb order `((H₀,H₂),(H₁,H₃))` to that
local order. This permutation introduces no transpose. Insertion uses the
existing link product, which transposes the shared `H₁,H₂` factors; on a
joint input its spectator factors are untouched.

The equivalence below concerns the independent operational definition of a
superchannel: preservation of quantum operations and channels on every joint
input, with arbitrary finite ancillary input and output systems. The ancillary
universes are independent of each other and of the comb wires. Empty systems
are included throughout.

Sources: [Chiribella2008Supermaps, VersioneArchivio.tex:132-134,143-150] and
[Chiribella2009Networks, comblong-pub.tex:1417-1423,1425-1433,1504-1514].
-/

@[expose] public section
noncomputable section

namespace QIT.HigherOrder.Comb

universe u y z

variable (I O : Fin 2 → Type u)
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- At two teeth the independently defined comb-map predicate is exactly
complete deterministic superchannel admissibility. Independent ancillary
universes are transported through finite equivalences, not restricted. -/
theorem isDeterministicSuperchannel_iff_isDeterministicMap
    (S : MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O 1)) :
    IsDeterministicSuperchannel.{u, u, u, u, y, z} S ↔
      IsDeterministicMap I O S := by
  constructor
  · intro hS
    refine ⟨hS.1.isCompletelyPositive, ?_⟩
    intro r s _ _ _ _ J hJ
    exact hS.2.channels_changeUniverse r s J
      ((extendedNormalized_one_iff_channelPredicate r s J).mp hJ)
  · intro hS
    have hc : CompletelyPreserves S channelPredicate.{u, u, u, u} channelPredicate := by
      intro r s _ _ _ _ J hJ
      exact hS.2 r s J ((extendedNormalized_one_iff_channelPredicate r s J).mpr hJ)
    apply (isDeterministicSuperchannel_iff_channels S).mpr
    intro r s _ _ _ _ N
    have hN := hc.channels_changeUniverse r s (MatrixMap.choi N.map)
      ⟨N.completelyPositive,
        (MatrixMap.isTracePreserving_iff_partialTraceB_choi N.map).mp N.tracePreserving⟩
    constructor
    · simpa only [MatrixMap.IsCompletelyPositive, choi_ancillaryAction] using hN.1
    · simpa only [MatrixMap.isTracePreserving_iff_partialTraceB_choi,
        choi_ancillaryAction] using hN.2

/-- A positive recursively normalized two-comb defines a deterministic one-slot
superchannel, and every deterministic superchannel has these constraints.
This is the two-comb specialization of the general comb characterization. -/
theorem normalized_two_iff_isDeterministicSuperchannel (J : CMatrix (Space I O)) :
    Normalized I O J ↔
      IsDeterministicSuperchannel.{u, u, u, u, y, z} (actionMap I O J) := by
  rw [isDeterministicSuperchannel_iff_isDeterministicMap,
    normalized_iff_isDeterministicMap]

/-- Exact Choi characterization of one-slot deterministic superchannels.
The inverse of `actionEquiv` changes local input-first Choi order to comb
order; no partial or full transpose is hidden in this reindexing. -/
theorem isDeterministicSuperchannel_iff_normalized_choi
    (S : MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O 1)) :
    IsDeterministicSuperchannel.{u, u, u, u, y, z} S ↔
      Normalized I O (WireFam.matReindex (actionEquiv I O).symm (MatrixMap.choi S)) := by
  rw [isDeterministicSuperchannel_iff_isDeterministicMap,
    isDeterministicMap_iff_normalized_choi]

/-- Reconstructing a transformation from its comb-ordered Choi matrix recovers
the entire linear map, hence its action on every operation. -/
@[simp] theorem actionMap_reindexed_choi
    (S : MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O 1)) :
    actionMap I O (WireFam.matReindex (actionEquiv I O).symm (MatrixMap.choi S)) = S := by
  apply MatrixMap.choi_inj
  rw [choi_actionMap, WireFam.matReindex_matReindex_symm]

/-- The Choi characterization is surjective, with the original comb operator
recovered exactly. The witness is the explicit Choi-inverse action map. -/
theorem normalized_two_iff_exists_superchannel (J : CMatrix (Space I O)) :
    Normalized I O J ↔ ∃ S,
      IsDeterministicSuperchannel.{u, u, u, u, y, z} S ∧
        MatrixMap.choi S = WireFam.matReindex (actionEquiv I O) J := by
  constructor
  · intro hJ
    exact ⟨actionMap I O J,
      (normalized_two_iff_isDeterministicSuperchannel I O J).mp hJ, choi_actionMap I O J⟩
  · rintro ⟨S, hS, hchoi⟩
    have hJ := (isDeterministicSuperchannel_iff_normalized_choi I O S).mp hS
    simpa only [hchoi, WireFam.matReindex_symm_matReindex] using hJ

/-- A superchannel acts by the shared-wire link product of its comb Choi
operator, on every matrix, with no positivity or rank hypothesis. -/
theorem linkAction_reindexed_choi
    (S : MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O 1))
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    linkAction I O (WireFam.matReindex (actionEquiv I O).symm (MatrixMap.choi S)) X =
      S X := by
  rw [← actionMap_eq_linkAction, actionMap_reindexed_choi]

/-- On an arbitrary joint operation each spectator block is contracted by
the same link product. Thus only the inserted channel wires are transposed,
and no tensor-product assumption on the operation or its spectators is made. -/
theorem ancillaryAction_linkAction_block (J : CMatrix (Space I O))
    {r : Type y} {s : Type z}
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (Φ : MatrixMap ((∀ j, innerInput O j) × r) ((∀ j, innerOutput I j) × s))
    (p q : r × s) :
    ancillaryBlock (MatrixMap.choi (ancillaryAction (actionMap I O J) Φ)) p q =
      linkAction I O J (ancillaryBlock (MatrixMap.choi Φ) p q) := by
  rw [choi_ancillaryAction, ancillaryBlock_extension, actionMap_eq_linkAction]

end QIT.HigherOrder.Comb
