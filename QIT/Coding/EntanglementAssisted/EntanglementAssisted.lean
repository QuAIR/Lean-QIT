/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.Holevo
public import QIT.HypothesisTesting.MutualInformation
public import QIT.Core.Channel
public import QIT.Core.POVMProbability
public import QIT.Core.Pure

/-!
# Entanglement-assisted classical capacity API

This module records the finite-dimensional API for entanglement-assisted
classical communication.  It defines the channel mutual-information objective
`I(N)` from the BSST theorem and an operational entanglement-assisted code
surface.

The full BSST equality `C_E(N) = I(N)`, its one-shot converse/achievability
ingredients, and the final capacity-supremum squeeze are separate proof
obligations.  This file uses supremum-style definitions for `I(N)` and the
one-shot capacity, and proves separately that this finite pure-state supremum
is attained on nonempty input systems.

Source alignment:
* [KhatriWilde2024Principles, Chapters/entropies.tex:8132-8144] defines the
  channel mutual information `I(N)` as a supremum over pure input-reference
  states.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:18-207] defines
  one-shot entanglement-assisted protocols, maximal error, and
  `C_EA^ε(N)`.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665] proves the
  hypothesis-testing one-shot lower bound by position-based coding and
  sequential decoding.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:679-721] derives the
  Renyi one-shot lower bound.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:857-884] states the
  capacity theorem and its one-shot proof ingredients.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:894-982] derives
  asymptotic achievability from the one-shot bounds.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331] derives the
  strong-converse side from the one-shot upper bounds.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Pure vectors carry the topology induced by their amplitudes. -/
instance PureVector.instTopologicalSpace {a : Type u} [Fintype a] [DecidableEq a] :
    TopologicalSpace (PureVector a) :=
  TopologicalSpace.induced PureVector.amp inferInstance

namespace PureVector

variable {a : Type u} [Fintype a] [DecidableEq a]

@[fun_prop]
theorem continuous_amp : Continuous (fun ψ : PureVector a => ψ.amp) :=
  continuous_induced_dom

omit [Fintype a] [DecidableEq a] in
theorem rankOneMatrix_continuous : Continuous (fun ψ : a → ℂ => rankOneMatrix ψ) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp only [rankOneMatrix_apply]
  exact (continuous_apply i).mul (continuous_star.comp (continuous_apply j))

theorem state_continuous : Continuous (fun ψ : PureVector a => ψ.state) := by
  rw [continuous_induced_rng]
  change Continuous fun ψ : PureVector a => rankOneMatrix ψ.amp
  exact rankOneMatrix_continuous.comp PureVector.continuous_amp

/-- The amplitude vectors underlying normalized pure vectors. -/
private def normalizedAmplitudeSet (a : Type u) [Fintype a] : Set (a → ℂ) :=
  {ψ | (rankOneMatrix ψ).trace = 1}

omit [DecidableEq a] in
private theorem trace_eq_sum_norm_sq {ψ : a → ℂ}
    (hψ : (rankOneMatrix ψ).trace = 1) :
    ∑ i, ‖ψ i‖ ^ 2 = (1 : ℝ) := by
  have hre := congrArg Complex.re hψ
  rw [rankOneMatrix_trace] at hre
  simp [dotProduct] at hre
  calc
    ∑ i, ‖ψ i‖ ^ 2 =
        ∑ i, ((ψ i).re * (ψ i).re + (ψ i).im * (ψ i).im) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Complex.sq_norm, Complex.normSq_apply]
    _ = 1 := hre

omit [DecidableEq a] in
private theorem norm_le_one_of_mem_normalizedAmplitudeSet
    {ψ : a → ℂ} (hψ : ψ ∈ normalizedAmplitudeSet a) (i : a) :
    ‖ψ i‖ ≤ 1 := by
  have hsum : ∑ j, ‖ψ j‖ ^ 2 = (1 : ℝ) :=
    trace_eq_sum_norm_sq hψ
  have hsingle : ‖ψ i‖ ^ 2 ≤ ∑ j, ‖ψ j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (‖ψ j‖)) (Finset.mem_univ i)
  have hsquare : ‖ψ i‖ ^ 2 ≤ 1 := by simpa [hsum] using hsingle
  exact (sq_le_one_iff₀ (norm_nonneg (ψ i))).mp hsquare

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isClosed :
    IsClosed (normalizedAmplitudeSet a) := by
  unfold normalizedAmplitudeSet
  exact isClosed_eq (Continuous.matrix_trace rankOneMatrix_continuous) continuous_const

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isBounded :
    Bornology.IsBounded (normalizedAmplitudeSet a) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : a → ℂ)]
  refine ⟨1, ?_⟩
  intro ψ hψ
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  exact norm_le_one_of_mem_normalizedAmplitudeSet hψ i

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isCompact :
    IsCompact (normalizedAmplitudeSet a) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨normalizedAmplitudeSet_isClosed, normalizedAmplitudeSet_isBounded⟩

private def ampSubtypeEquiv :
    PureVector a ≃ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toFun ψ := ⟨ψ.amp, ψ.trace_rankOne_eq_one⟩
  invFun ψ := ⟨ψ.1, ψ.2⟩
  left_inv ψ := by
    cases ψ
    rfl
  right_inv ψ := by
    cases ψ
    rfl

private noncomputable def ampSubtypeHomeomorph :
    PureVector a ≃ₜ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toEquiv := ampSubtypeEquiv
  continuous_toFun := PureVector.continuous_amp.subtype_mk fun ψ => ψ.trace_rankOne_eq_one
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous fun ψ : {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} => ψ.1
    exact continuous_subtype_val

instance instCompactSpace : CompactSpace (PureVector a) := by
  haveI : CompactSpace {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} :=
    isCompact_iff_compactSpace.mp normalizedAmplitudeSet_isCompact
  exact ampSubtypeHomeomorph.symm.compactSpace

/-- A canonical basis pure vector on a nonempty finite system. -/
def basisPureVector [Nonempty a] : PureVector a where
  amp := fun i => if i = Classical.choice (inferInstance : Nonempty a) then 1 else 0
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace, dotProduct]
    simp

end PureVector

theorem mutualInformation_continuous :
    Continuous (fun ρ : State (Prod a b) => mutualInformation ρ) := by
  unfold mutualInformation
  exact ((State.vonNeumann_continuous.comp State.marginalA_continuous).add
    (State.vonNeumann_continuous.comp State.marginalB_continuous)).sub
    State.vonNeumann_continuous

namespace Channel

variable (N : Channel a b)

theorem applyState_continuous : Continuous (fun ρ : State a => N.applyState ρ) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State a => N.map ρ.matrix
  exact (LinearMap.continuous_of_finiteDimensional N.map).comp State.continuous_matrix

/-- Output state `(id_R ⊗ N)(|ψ⟩⟨ψ|)` for a pure input-reference state. -/
def entanglementAssistedOutputState {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) : State (Prod r b) :=
  ((Channel.idChannel r).prod N).applyState ψ.state

theorem entanglementAssistedOutputState_continuous {r : Type w} [Fintype r] [DecidableEq r] :
    Continuous (fun ψ : PureVector (Prod r a) => N.entanglementAssistedOutputState ψ) :=
  (((Channel.idChannel r).prod N).applyState_continuous).comp PureVector.state_continuous

/-- Mutual information of the entanglement-assisted channel output state. -/
def entanglementAssistedMutualInformation {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) : ℝ :=
  mutualInformation (N.entanglementAssistedOutputState ψ)

theorem entanglementAssistedMutualInformation_continuous
    {r : Type w} [Fintype r] [DecidableEq r] :
    Continuous (fun ψ : PureVector (Prod r a) =>
      N.entanglementAssistedMutualInformation ψ) :=
  mutualInformation_continuous.comp N.entanglementAssistedOutputState_continuous

/-- Single-letter entanglement-assisted channel information `I(N)`.

The source states `I(N)` as a maximum over pure `A A'` inputs.  The Lean API
uses `sSup` over pure states on a reference copy of the input system; the
separate compactness/maximizer proof for the attained `max` is tracked
downstream. -/
def entanglementAssistedInformation : ℝ :=
  sSup (Set.range fun ψ : PureVector (Prod a a) =>
    N.entanglementAssistedMutualInformation ψ)

/-- The supremum in `Channel.entanglementAssistedInformation` is attained on a
pure input-reference state for nonempty finite input systems. -/
theorem exists_entanglementAssistedInformation_maximizer [Nonempty a] :
    ∃ ψ : PureVector (Prod a a),
      N.entanglementAssistedInformation =
        N.entanglementAssistedMutualInformation ψ := by
  let f : PureVector (Prod a a) → ℝ :=
    fun ψ => N.entanglementAssistedMutualInformation ψ
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hne : (Set.univ : Set (PureVector (Prod a a))).Nonempty :=
    Set.univ_nonempty
  obtain ⟨ψ, _hψmem, hψmax⟩ :=
    isCompact_univ.exists_isMaxOn hne
      (N.entanglementAssistedMutualInformation_continuous (r := a)).continuousOn
  refine ⟨ψ, ?_⟩
  change sSup (Set.range f) = f ψ
  refine le_antisymm ?_ ?_
  · exact csSup_le (Set.range_nonempty f) fun y hy => by
      rcases hy with ⟨φ, rfl⟩
      exact hψmax trivial
  · exact le_csSup (by
      refine ⟨f ψ, ?_⟩
      intro y hy
      rcases hy with ⟨φ, rfl⟩
      exact hψmax trivial) ⟨ψ, rfl⟩

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

end Channel

/-- Register rate for an entanglement-assisted classical message code. -/
def entanglementAssistedMessageRate (M : Type w) [Fintype M] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card M : ℝ) / (n : ℝ)

/-- A finite entanglement-assisted classical communication code for `n` uses
of channel `N`.

Alice and Bob share a finite state on `EA × EB`.  For each message, Alice
applies an encoder channel to her share `EA` to prepare the channel input
`A^n`; Bob decodes from the channel output `B^n` together with his retained
share `EB`. -/
structure EntanglementAssistedClassicalCode (N : Channel a b) (n : ℕ)
    (M : Type w) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type x) [Fintype EA] [DecidableEq EA]
    (EB : Type y) [Fintype EB] [DecidableEq EB] where
  sharedState : State (Prod EA EB)
  encoder : M → Channel EA (TensorPower a n)
  decoder : POVM M (Prod (TensorPower b n) EB)

namespace EntanglementAssistedClassicalCode

variable {N : Channel a b} {n : ℕ}
variable {M : Type w} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Joint channel-input and Bob-side state after Alice encodes a message. -/
def channelInputState (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : State (Prod (TensorPower a n) EB) :=
  ((C.encoder m).prod (Channel.idChannel EB)).applyState C.sharedState

/-- Bob's received state after the `n` channel uses and before decoding. -/
def outputState (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : State (Prod (TensorPower b n) EB) :=
  ((N.tensorPower n).prod (Channel.idChannel EB)).applyState
    (C.channelInputState m)

/-- Born-rule probability that Bob decodes the transmitted message. -/
def successProbability (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : ℝ :=
  (C.decoder.prob (C.outputState m) m : ℝ)

/-- Message-wise error probability. -/
def error (C : EntanglementAssistedClassicalCode N n M EA EB) (m : M) : ℝ :=
  1 - C.successProbability m

/-- Maximal message error bounded by `ε`. -/
def maxErrorAtMost (C : EntanglementAssistedClassicalCode N n M EA EB)
    (ε : ℝ) : Prop :=
  ∀ m : M, C.error m ≤ ε

/-- Classical communication rate of the message set. -/
def rate (_C : EntanglementAssistedClassicalCode N n M EA EB) : ℝ :=
  entanglementAssistedMessageRate M n

@[simp]
theorem rate_one (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    C.rate = log2 (Fintype.card M : ℝ) := by
  unfold rate entanglementAssistedMessageRate
  norm_num

end EntanglementAssistedClassicalCode

namespace Channel

variable (N : Channel a b)

/-- Operational achievability of an entanglement-assisted classical rate. -/
def IsAchievableEntanglementAssistedClassicalRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N n M EA EB,
            C.rate ≥ R - δ ∧ C.maxErrorAtMost ε

/-- `B` is an upper bound on every achievable entanglement-assisted classical
rate for channel `N`. -/
def IsEntanglementAssistedClassicalRateUpperBound (B : ℝ) : Prop :=
  ∀ R : ℝ, N.IsAchievableEntanglementAssistedClassicalRate R → R ≤ B

/-- Operational strong-converse rate for entanglement-assisted classical
communication.

This is the rate-normalized Lean form of the Khatri--Wilde definition
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:724-854]: for every
positive slack `δ` and every target error threshold `ε < 1`, all sufficiently
long `ε`-reliable protocols have rate strictly below `R + δ`. -/
def IsStrongConverseEntanglementAssistedClassicalRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
        ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
          ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
            ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
              C.maxErrorAtMost ε → C.rate < R + δ

/-- Operational entanglement-assisted classical capacity as the supremum of
achievable rates.  The BSST theorem later identifies this quantity with
`N.entanglementAssistedInformation`. -/
def entanglementAssistedClassicalCapacity : ℝ :=
  sSup {R : ℝ | N.IsAchievableEntanglementAssistedClassicalRate R}

/-- Strong-converse entanglement-assisted classical capacity as the infimum of
strong-converse rates, following
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:724-854]. -/
def strongConverseEntanglementAssistedClassicalCapacity : ℝ :=
  sInf {R : ℝ | N.IsStrongConverseEntanglementAssistedClassicalRate R}

/-- One-shot `ε`-error entanglement-assisted classical capacity.

This is the Lean counterpart of `C_EA^ε(N)`: the supremum of one-use code rates
over entanglement-assisted classical codes whose maximal error is at most `ε`.
For `n = 1`, the rate unfolds to `log2 |M|`. -/
def oneShotEntanglementAssistedClassicalCapacity (ε : ℝ) : ℝ :=
  sSup {R : ℝ |
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
            C.maxErrorAtMost ε ∧ R = C.rate}

/-- Extended-real one-shot `ε`-error entanglement-assisted classical capacity.

This version matches the extended-real hypothesis-testing convention used by
`D_H^ε`: if the type-II beta quantity vanishes, the converse upper bound is
`⊤`.  The real-valued capacity above is kept as the compatibility wrapper for
finite numerical statements. -/
def oneShotEntanglementAssistedClassicalCapacityE (ε : ℝ) : EReal :=
  sSup {R : EReal |
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
            C.maxErrorAtMost ε ∧ R = (C.rate : EReal)}

/-- `B` upper-bounds all one-shot `ε`-reliable entanglement-assisted codes. -/
def IsOneShotEntanglementAssistedClassicalCapacityUpperBound
    (ε B : ℝ) : Prop :=
  ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
    ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
      ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
        ∀ C : EntanglementAssistedClassicalCode N 1 M EA EB,
          C.maxErrorAtMost ε → C.rate ≤ B

/-- `B` upper-bounds all one-shot `ε`-reliable entanglement-assisted codes in
the extended-real convention. -/
def IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE
    (ε : ℝ) (B : EReal) : Prop :=
  ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
    ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
      ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
        ∀ C : EntanglementAssistedClassicalCode N 1 M EA EB,
          C.maxErrorAtMost ε → (C.rate : EReal) ≤ B

theorem oneShotEntanglementAssistedClassicalCapacityE_le_of_upperBound
    {ε : ℝ} {B : EReal}
    (hB : N.IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE ε B) :
    N.oneShotEntanglementAssistedClassicalCapacityE ε ≤ B := by
  unfold oneShotEntanglementAssistedClassicalCapacityE
  refine sSup_le ?_
  intro R hR
  rcases hR with
    ⟨M, _hM, _hMeq, _hMne, EA, _hEA, _hEAeq, EB, _hEB, _hEBeq, C, hC, rfl⟩
  exact hB M EA EB C hC

end Channel

/-- Source-shaped witness for one block of the entanglement-assisted direct
coding route for a fixed pure input-reference state.

The witness packages an already-constructed code and the estimates expected
from the BSST direct proof: rate at least the output mutual information minus
`δ`, and maximal decoding error at most `ε`.  This structure is an API for
later proof leaves; this module does not prove the direct coding theorem. -/
structure EntanglementAssistedDirectCodingWitness {r : Type u}
    [Fintype r] [DecidableEq r] (N : Channel a b)
    (ψ : PureVector (Prod r a)) (n : ℕ) (δ ε : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type u) [Fintype EA] [DecidableEq EA]
    (EB : Type u) [Fintype EB] [DecidableEq EB] where
  code : EntanglementAssistedClassicalCode N n M EA EB
  rate_ge : code.rate ≥ N.entanglementAssistedMutualInformation ψ - δ
  maxError_le : code.maxErrorAtMost ε

/-- Source-shaped one-shot achievability witness.

The Khatri--Wilde one-shot lower bound constructs such a witness using
position-based coding and sequential decoding.  This structure records only the
resulting code and numerical lower-bound estimate; it does not prove the
one-shot theorem. -/
structure EntanglementAssistedOneShotAchievabilityWitness (N : Channel a b)
    (ε lowerBound : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type u) [Fintype EA] [DecidableEq EA]
    (EB : Type u) [Fintype EB] [DecidableEq EB] where
  code : EntanglementAssistedClassicalCode N 1 M EA EB
  maxError_le : code.maxErrorAtMost ε
  lowerBound_le_rate : lowerBound ≤ code.rate

/-- Source-shaped family of converse estimates for entanglement-assisted
classical communication.

For every rate slack `η > 0` and reliability threshold `ε > 0`, all
sufficiently long reliable EA codes have rate at most
`N.entanglementAssistedInformation + η`.  In the source proof, this estimate is
where the Fano/continuity, quantum data-processing, mutual-information chain
rule, and additivity arguments enter; this structure keeps those estimates
explicit for the converse assembly theorem below. -/
structure EntanglementAssistedConverseWitnessFamily (N : Channel a b) where
  rate_le :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  C.rate ≤ N.entanglementAssistedInformation + η

namespace Channel

variable (N : Channel a b)

/-- Entanglement-assisted direct achievability from a family of BSST
direct-coding witnesses.

This is the direct-coding side of the BSST route currently formalized in
Lean.  In the modern source route, the concrete witnesses come from
Khatri--Wilde one-shot position-based coding and the asymptotic passage from
their one-shot lower bound.  The one-shot theorem itself, converse,
compactness/maximizer theorem, and final capacity equality are separate proof
obligations. -/
theorem entanglementAssisted_direct_achievable_of_directCodingWitness
    {r : Type u} [Fintype r] [DecidableEq r] (ψ : PureVector (Prod r a))
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
            ∃ (_ : Nonempty M),
              ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
                ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                  Nonempty (EntanglementAssistedDirectCodingWitness N ψ n δ ε M EA EB)) :
    N.IsAchievableEntanglementAssistedClassicalRate
      (N.entanglementAssistedMutualInformation ψ) := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, ⟨witness⟩⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    witness.code, witness.rate_ge, witness.maxError_le⟩

/-- Entanglement-assisted converse upper bound from source-shaped converse
estimates.

This theorem is the Lean assembly of the BSST converse route: once the
Fano/continuity, data-processing, mutual-information chain-rule, and additivity
estimates are supplied as an `EntanglementAssistedConverseWitnessFamily`, the
single-letter information quantity `I(N)` upper-bounds every achievable
entanglement-assisted classical rate. -/
theorem entanglementAssisted_information_isUpperBound_of_converseWitness
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.IsEntanglementAssistedClassicalRateUpperBound
      N.entanglementAssistedInformation := by
  intro R hR
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  have hone : 0 < (1 : ℝ) := by norm_num
  obtain ⟨Nach, hNach⟩ := hR (η / 2) hhalf 1 hone
  obtain ⟨Nconv, hNconv⟩ := hconv.rate_le (η / 2) hhalf 1 hone
  let n : ℕ := max Nach Nconv
  have hnAch : n ≥ Nach := Nat.le_max_left Nach Nconv
  have hnConv : n ≥ Nconv := Nat.le_max_right Nach Nconv
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hrate_ge, herror⟩ :=
    hNach n hnAch
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  have hrate_le :
      C.rate ≤ N.entanglementAssistedInformation + η / 2 :=
    hNconv n hnConv M EA EB C herror
  linarith

/-- Every strong-converse rate is an upper bound on every achievable rate.

This is the order-theoretic content behind the source inequality
`C_EA(N) ≤ Ctilde_EA(N)`: an achievable sequence with rate `R - δ/2` and a
strong-converse bound at `S + δ/2` can be compared at the same blocklength. -/
theorem achievable_le_of_strongConverseRate
    {R S : ℝ}
    (hR : N.IsAchievableEntanglementAssistedClassicalRate R)
    (hS : N.IsStrongConverseEntanglementAssistedClassicalRate S) :
    R ≤ S := by
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  have heps_pos : 0 < (1 / 2 : ℝ) := by norm_num
  have heps_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have heps_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨Nach, hNach⟩ := hR (η / 2) hhalf (1 / 2) heps_pos
  obtain ⟨Nstrong, hNstrong⟩ :=
    hS (η / 2) hhalf (1 / 2) heps_nonneg heps_lt_one
  let n : ℕ := max Nach Nstrong
  have hnAch : n ≥ Nach := Nat.le_max_left Nach Nstrong
  have hnStrong : n ≥ Nstrong := Nat.le_max_right Nach Nstrong
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hrate_ge, herror⟩ :=
    hNach n hnAch
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  have hrate_lt : C.rate < S + η / 2 :=
    hNstrong n hnStrong M EA EB C herror
  have hR_lt : R - η / 2 < S + η / 2 :=
    lt_of_le_of_lt hrate_ge hrate_lt
  linarith

/-- The source-shaped converse witness implies that `I(N)` is a
strong-converse rate.

The witness is stated for positive error thresholds.  The definition of
strong-converse rate allows `ε = 0`; this proof handles that endpoint by
applying the witness to the positive threshold `max ε (1/2)`, since any
`ε`-reliable code is also `max ε (1/2)`-reliable. -/
theorem entanglementAssisted_information_isStrongConverseRate_of_converseWitness
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.IsStrongConverseEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation := by
  intro δ hδ ε _hε_nonneg _hε_lt_one
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hεpos : 0 < max ε (1 / 2 : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right ε (1 / 2))
  obtain ⟨N0, hN0⟩ := hconv.rate_le (δ / 2) hhalf (max ε (1 / 2)) hεpos
  refine ⟨N0, ?_⟩
  intro n hn M _hMfin _hMdec _hMnonempty EA _hEAfin _hEAdec EB _hEBfin _hEBdec C hC
  have hCmax : C.maxErrorAtMost (max ε (1 / 2 : ℝ)) := by
    intro m
    exact (hC m).trans (le_max_left ε (1 / 2))
  have hrate_le :
      C.rate ≤ N.entanglementAssistedInformation + δ / 2 :=
    hN0 n hn M EA EB C hCmax
  have hstrict :
      N.entanglementAssistedInformation + δ / 2 <
        N.entanglementAssistedInformation + δ := by
    linarith
  exact lt_of_le_of_lt hrate_le hstrict

/-- Capacity upper bound from a converse witness. -/
theorem entanglementAssistedClassicalCapacity_le_information_of_converseWitness
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.entanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation := by
  unfold entanglementAssistedClassicalCapacity
  exact csSup_le ⟨N.entanglementAssistedInformation, hach⟩
    (N.entanglementAssisted_information_isUpperBound_of_converseWitness hconv)

/-- Capacity lower bound from achievability of the channel mutual information. -/
theorem entanglementAssistedInformation_le_classicalCapacity_of_achievable
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.entanglementAssistedInformation ≤
      N.entanglementAssistedClassicalCapacity := by
  unfold entanglementAssistedClassicalCapacity
  exact le_csSup
    ⟨N.entanglementAssistedInformation,
      N.entanglementAssisted_information_isUpperBound_of_converseWitness hconv⟩
    hach

/-- Abstract capacity squeeze: achievability plus the converse witness identify
the operational entanglement-assisted capacity with the channel mutual
information. -/
theorem entanglementAssistedClassicalCapacity_eq_information_of_achievable_of_converseWitness
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.entanglementAssistedClassicalCapacity =
      N.entanglementAssistedInformation := by
  exact le_antisymm
    (N.entanglementAssistedClassicalCapacity_le_information_of_converseWitness hach hconv)
    (N.entanglementAssistedInformation_le_classicalCapacity_of_achievable hach hconv)

/-- The operational capacity is bounded by every strong-converse rate. -/
theorem entanglementAssistedClassicalCapacity_le_of_strongConverseRate
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    {S : ℝ} (hS : N.IsStrongConverseEntanglementAssistedClassicalRate S) :
    N.entanglementAssistedClassicalCapacity ≤ S := by
  unfold entanglementAssistedClassicalCapacity
  exact csSup_le ⟨N.entanglementAssistedInformation, hach⟩
    (fun R hR => N.achievable_le_of_strongConverseRate hR hS)

/-- The usual capacity is at most the strong-converse capacity. -/
theorem entanglementAssistedClassicalCapacity_le_strongConverseCapacity
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hsc :
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation) :
    N.entanglementAssistedClassicalCapacity ≤
      N.strongConverseEntanglementAssistedClassicalCapacity := by
  unfold strongConverseEntanglementAssistedClassicalCapacity
  exact le_csInf ⟨N.entanglementAssistedInformation, hsc⟩
    (fun S hS => N.entanglementAssistedClassicalCapacity_le_of_strongConverseRate hach hS)

/-- The strong-converse capacity is at most `I(N)` when `I(N)` is a
strong-converse rate. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_le_information
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hsc :
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation) :
    N.strongConverseEntanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation := by
  unfold strongConverseEntanglementAssistedClassicalCapacity
  exact csInf_le
    ⟨N.entanglementAssistedClassicalCapacity, by
      intro S hS
      exact N.entanglementAssistedClassicalCapacity_le_of_strongConverseRate hach hS⟩
    hsc

/-- Abstract strong-converse capacity squeeze: achievability plus the converse
witness identify the strong-converse entanglement-assisted capacity with the
channel mutual information. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_eq_information_of_achievable_of_converseWitness
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.strongConverseEntanglementAssistedClassicalCapacity =
      N.entanglementAssistedInformation := by
  have hsc :=
    N.entanglementAssisted_information_isStrongConverseRate_of_converseWitness hconv
  exact le_antisymm
    (N.strongConverseEntanglementAssistedClassicalCapacity_le_information hach hsc)
    (le_trans
      (by
        rw [← N.entanglementAssistedClassicalCapacity_eq_information_of_achievable_of_converseWitness
          hach hconv])
      (N.entanglementAssistedClassicalCapacity_le_strongConverseCapacity hach hsc))

/-- Final abstract Khatri--Wilde capacity squeeze:
`C_EA(N) = Ctilde_EA(N) = I(N)` once the asymptotic achievability and converse
witnesses have been supplied. -/
theorem entanglementAssisted_capacity_and_strongConverseCapacity_eq_information
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.entanglementAssistedClassicalCapacity = N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity =
        N.entanglementAssistedInformation :=
  ⟨N.entanglementAssistedClassicalCapacity_eq_information_of_achievable_of_converseWitness
      hach hconv,
    N.strongConverseEntanglementAssistedClassicalCapacity_eq_information_of_achievable_of_converseWitness
      hach hconv⟩


end Channel

end

end QIT
