/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.EntanglementAssistedConverse

/-!
# Entanglement-assisted weak-converse bridge

This module records the weak-converse one-shot upper-bound surface for
entanglement-assisted classical communication.

The Khatri--Wilde source proves the one-shot upper bound

`C_EA^ε(N) <= (I(N) + h₂(ε)) / (1 - ε)`

by combining the hypothesis-testing converse with a weak-converse comparison
from hypothesis-testing mutual information to the ordinary channel mutual
information
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427].

The source-level comparison ultimately depends on the finite-blocklength
entropy comparison from the source's hypothesis-testing-to-relative-entropy
proposition.  The current Lean API does not yet contain the required
Fano/relative-entropy bridge, so the channel-level comparison is kept as an
explicit, named hypothesis.  The final capacity assembly from that comparison
is fully proved here and reuses the hypothesis-testing converse.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace EntanglementAssistedWeakConverse

/-- Binary entropy `h₂(ε) = -ε log₂ ε - (1 - ε) log₂(1 - ε)`.

This is intentionally local to the entanglement-assisted weak-converse surface;
a global entropy API can later reuse or replace it once the surrounding binary
entropy lemmas are formalized. -/
def binaryEntropy (ε : ℝ) : ℝ :=
  -xlog2 ε - xlog2 (1 - ε)

end EntanglementAssistedWeakConverse

namespace State

/-- State-level weak-converse comparison from hypothesis-testing mutual
information to ordinary mutual information plus the binary-entropy penalty.

This is the local formal surface for the source comparison
`I_H^ε(A;B)_ρ <= (I(A;B)_ρ + h₂(ε)) / (1 - ε)`. -/
def HypothesisTestingMutualInformationWeakConverseBound
    (rhoAB : State (Prod a b)) (ε : ℝ) : Prop :=
  rhoAB.hypothesisTestingMutualInformationE ε ≤
    ((mutualInformation rhoAB +
        EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε) : EReal)

/-- Barred hypothesis-testing relative-entropy comparison at the product of
the marginals.

This is the source-shaped remaining comparison behind the state-level
weak-converse bound: instantiate the hypothesis-testing-to-relative-entropy
comparison of
[KhatriWilde2024Principles, Chapters/entropies.tex:6952-6984] at
`σ = ρ_A ⊗ ρ_B`, where the trace-normalization term vanishes, and identify the
relative entropy with `I(A;B)_ρ`. -/
def HypothesisTestingRelativeEntropyMarginalsWeakConverseBound
    (rhoAB : State (Prod a b)) (ε : ℝ) : Prop :=
  rhoAB.hypothesisTestingRelativeEntropyE
      (rhoAB.marginalA.prod rhoAB.marginalB) ε ≤
    ((mutualInformation rhoAB +
        EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε) : EReal)

/-- Optimizing hypothesis-testing mutual information over Bob-side states is
bounded by the barred choice `σ_B = ρ_B`. -/
theorem hypothesisTestingMutualInformationE_le_relativeEntropyE_marginals
    (rhoAB : State (Prod a b)) (ε : ℝ) :
    rhoAB.hypothesisTestingMutualInformationE ε ≤
      rhoAB.hypothesisTestingRelativeEntropyE
        (rhoAB.marginalA.prod rhoAB.marginalB) ε := by
  rw [hypothesisTestingMutualInformationE_eq_sInf]
  exact sInf_le ⟨rhoAB.marginalB, rfl⟩

/-- Reduce the state-level weak-converse comparison to the barred
hypothesis-testing-relative-entropy comparison at the marginal product. -/
theorem hypothesisTestingMutualInformationWeakConverseBound_of_relativeEntropy_marginals
    (rhoAB : State (Prod a b)) {ε : ℝ}
    (hrel : rhoAB.HypothesisTestingRelativeEntropyMarginalsWeakConverseBound ε) :
    rhoAB.HypothesisTestingMutualInformationWeakConverseBound ε :=
  (rhoAB.hypothesisTestingMutualInformationE_le_relativeEntropyE_marginals ε).trans
    hrel

end State

namespace Channel

variable (N : Channel a b)

/-- Every input-reference mutual information value is bounded by the channel
supremum `I(N)`. -/
theorem entanglementAssistedMutualInformation_le_information [Nonempty a]
    (ψ : PureVector (Prod a a)) :
    N.entanglementAssistedMutualInformation ψ ≤
      N.entanglementAssistedInformation := by
  let f : PureVector (Prod a a) → ℝ :=
    fun ψ => N.entanglementAssistedMutualInformation ψ
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hne : (Set.univ : Set (PureVector (Prod a a))).Nonempty :=
    Set.univ_nonempty
  obtain ⟨ψmax, _hψmem, hψmax⟩ :=
    isCompact_univ.exists_isMaxOn hne
      (N.entanglementAssistedMutualInformation_continuous (r := a)).continuousOn
  rw [entanglementAssistedInformation]
  refine le_csSup ?_ ⟨ψ, rfl⟩
  refine ⟨f ψmax, ?_⟩
  intro y hy
  rcases hy with ⟨φ, rfl⟩
  exact hψmax trivial

/-- Real-valued weak-converse upper-bound expression
`(I(N) + h₂(ε)) / (1 - ε)`. -/
def entanglementAssistedWeakConverseBound (ε : ℝ) : ℝ :=
  (N.entanglementAssistedInformation +
      EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε)

/-- Channel-level weak-converse comparison needed for Khatri--Wilde's
one-shot upper-bound theorem.

This is the remaining mathematical comparison: the optimized
hypothesis-testing mutual information is bounded by the ordinary
entanglement-assisted mutual-information objective plus the binary-entropy
penalty. -/
def HypothesisTestingMutualInformationWeakConverseBound (ε : ℝ) : Prop :=
  N.hypothesisTestingMutualInformationE ε ≤
    (N.entanglementAssistedWeakConverseBound ε : EReal)

/-- Lift the state-level weak-converse comparison for every pure
input-reference output state through the channel supremum. -/
theorem hypothesisTestingMutualInformationWeakConverseBound_of_state
    [Nonempty a] {ε : ℝ} (hε_lt_one : ε < 1)
    (hstate :
      ∀ ψ : PureVector (Prod a a),
        State.HypothesisTestingMutualInformationWeakConverseBound
          (N.hypothesisTestingOutputState ψ) ε) :
    N.HypothesisTestingMutualInformationWeakConverseBound ε := by
  rw [HypothesisTestingMutualInformationWeakConverseBound,
    hypothesisTestingMutualInformationE_eq_sSup]
  refine sSup_le ?_
  intro value hvalue
  rcases hvalue with ⟨ψ, rfl⟩
  have hstateψ :=
    hstate ψ
  have hmi :
      mutualInformation (N.hypothesisTestingOutputState ψ) ≤
        N.entanglementAssistedInformation := by
    simpa [Channel.hypothesisTestingOutputState,
      Channel.entanglementAssistedOutputState,
      Channel.entanglementAssistedMutualInformation] using
      N.entanglementAssistedMutualInformation_le_information ψ
  have hden : 0 ≤ 1 - ε := sub_nonneg.mpr (le_of_lt hε_lt_one)
  have hreal :
      (mutualInformation (N.hypothesisTestingOutputState ψ) +
            EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε) ≤
        N.entanglementAssistedWeakConverseBound ε := by
    unfold entanglementAssistedWeakConverseBound
    exact div_le_div_of_nonneg_right (add_le_add hmi le_rfl) hden
  exact hstateψ.trans (EReal.coe_le_coe_iff.mpr hreal)

/--
Algebraic bridge from the hypothesis-testing one-shot converse and the
channel-level weak-converse comparison to the Khatri--Wilde one-shot weak
converse upper bound.

This is the final assembly step of
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427].  The comparison
hypothesis represents the still-separate entropy/Fano-to-relative-entropy
ingredient from the same source development.
-/
theorem oneShotEntanglementAssistedClassicalCapacityE_le_weakConverseBound_of_comparison
    {ε : ℝ} (hε_nonneg : 0 ≤ ε) (_hε_lt_one : ε < 1)
    (hcmp : N.HypothesisTestingMutualInformationWeakConverseBound ε) :
    N.oneShotEntanglementAssistedClassicalCapacityE ε ≤
      (N.entanglementAssistedWeakConverseBound ε : EReal) :=
  (N.oneShotEntanglementAssistedClassicalCapacityE_le_hypothesisTestingMutualInformationE
    hε_nonneg).trans hcmp

end Channel

namespace EntanglementAssistedClassicalCode

variable {N : Channel a b}
variable {M : Type w} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Per-code assembly form of the weak-converse upper bound, assuming the
channel-level weak-converse comparison. -/
theorem log_card_le_channel_entanglementAssistedWeakConverseBoundE_of_comparison
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hC : C.maxErrorAtMost ε)
    (hcmp : N.HypothesisTestingMutualInformationWeakConverseBound ε) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      (N.entanglementAssistedWeakConverseBound ε : EReal) :=
  (C.log_card_le_channel_hypothesisTestingMutualInformationE hε_nonneg hC).trans
    hcmp

/-- Real-valued per-code assembly form of the weak-converse upper bound,
assuming the channel-level weak-converse comparison. -/
theorem log_card_le_channel_entanglementAssistedWeakConverseBound_of_comparison
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hC : C.maxErrorAtMost ε)
    (hcmp : N.HypothesisTestingMutualInformationWeakConverseBound ε) :
    log2 (Fintype.card M : ℝ) ≤
      N.entanglementAssistedWeakConverseBound ε :=
  EReal.coe_le_coe_iff.mp
    (C.log_card_le_channel_entanglementAssistedWeakConverseBoundE_of_comparison
      hε_nonneg hC hcmp)

end EntanglementAssistedClassicalCode

end

end QIT
