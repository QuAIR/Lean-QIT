/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.Channels.Diamond
public import QIT.States.MaximallyEntangled
public import QIT.States.Geometry.PureTargetFidelity
public import QIT.States.Geometry.PurifiedDistance
public import QIT.Information.Entropy.CoherentInformation

/-!
# Quantum communication codes and operational capacity

Entanglement generation permits arbitrary mixed encoded states and joint
decoders [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:129-135].
Transmission codes are the special case obtained by encoding one half of a
normalized maximally entangled state
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:219-227].

The code interfaces correspond to the generation and transmission protocols in
[KhatriWilde2024Principles, Chapters/quantum_capacity.tex:256-293], with the
paper's explicit allowance for mixed generation inputs. All fidelities below
are squared fidelities. Reference and decoded registers have equal dimension,
expressed by a basis equivalence, independently of the channel input dimension.
-/

@[expose] public section

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A one-shot entanglement-generation code. The encoded state may be mixed,
and its reference marginal is unrestricted. For `n` memoryless uses, take
the channel to be `N.tensorPower n`; the decoder can act jointly on all outputs
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:129-135]. -/
structure EntanglementGenerationCode (N : Channel a b)
    (r : Type w) (t : Type x) [Fintype r] [DecidableEq r] [Nonempty r]
    [Fintype t] [DecidableEq t] where
  encodedState : State (r × a)
  decoder : Channel b t
  pairing : r ≃ t

namespace EntanglementGenerationCode

variable {N : Channel a b} {r : Type w} {t : Type x}
variable [Fintype r] [DecidableEq r] [Nonempty r] [Fintype t] [DecidableEq t]

/-- Dimension of the reference and decoded registers. -/
def dimension (_C : EntanglementGenerationCode N r t) : ℕ := Fintype.card r

/-- The target has the same dimension as the reference. -/
theorem dimension_eq_target_card (C : EntanglementGenerationCode N r t) :
    C.dimension = Fintype.card t := Fintype.card_congr C.pairing

/-- A code has positive message dimension. -/
theorem dimension_pos (C : EntanglementGenerationCode N r t) : 0 < C.dimension :=
  Fintype.card_pos

/-- Message size in qubits, using base-two logarithms. -/
def logDimension (C : EntanglementGenerationCode N r t) : ℝ := log2 C.dimension

/-- Qubits per channel use for a code regarded as an `n`-use block code.
Operational predicates use only positive `n`; real division totalizes this
expression to zero at `n = 0`
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:592-596]. -/
def rate (C : EntanglementGenerationCode N r t) (n : ℕ) : ℝ :=
  C.logDimension / (n : ℝ)

/-- Joint reference/channel-output state before decoding. -/
def channelOutput (C : EntanglementGenerationCode N r t) : State (r × b) :=
  ((Channel.idChannel r).prod N).applyState C.encodedState

/-- Joint reference/decoded state, leaving the reference untouched. -/
def outputState (C : EntanglementGenerationCode N r t) : State (r × t) :=
  ((Channel.idChannel r).prod C.decoder).applyState C.channelOutput

/-- Normalized maximally entangled target selected by the basis pairing. -/
def targetState (C : EntanglementGenerationCode N r t) : State (r × t) :=
  State.maximallyEntangled C.pairing

/-- Entanglement fidelity in the squared-fidelity convention. -/
def fidelity (C : EntanglementGenerationCode N r t) : ℝ :=
  C.outputState.squaredFidelity C.targetState

/-- Entanglement-generation error, one minus squared fidelity. -/
def error (C : EntanglementGenerationCode N r t) : ℝ := 1 - C.fidelity

/-- The pure maximally entangled target makes squared fidelity a trace overlap. -/
theorem fidelity_eq_trace (C : EntanglementGenerationCode N r t) :
    C.fidelity = ((C.outputState.matrix * C.targetState.matrix).trace).re :=
  State.squaredFidelity_pure_right_eq_trace C.outputState
    (PureVector.maximallyEntangled C.pairing)

/-- Squared code fidelity is nonnegative. -/
theorem fidelity_nonneg (C : EntanglementGenerationCode N r t) : 0 ≤ C.fidelity :=
  State.squaredFidelity_nonneg _ _

/-- Squared code fidelity is at most one. -/
theorem fidelity_le_one (C : EntanglementGenerationCode N r t) : C.fidelity ≤ 1 :=
  State.squaredFidelity_le_one_of_uhlmann _ _

/-- Code error is nonnegative. -/
theorem error_nonneg (C : EntanglementGenerationCode N r t) : 0 ≤ C.error :=
  sub_nonneg.mpr C.fidelity_le_one

/-- Code error is at most one. -/
theorem error_le_one (C : EntanglementGenerationCode N r t) : C.error ≤ 1 :=
  sub_le_self _ C.fidelity_nonneg

/-- Error thresholds can be consumed as lower bounds on squared fidelity. -/
theorem error_le_iff (C : EntanglementGenerationCode N r t) (ε : ℝ) :
    C.error ≤ ε ↔ 1 - ε ≤ C.fidelity := by
  unfold error
  constructor <;> intro h <;> linarith

end EntanglementGenerationCode

/-- A transmission code has arbitrary CPTP encoding and decoding channels,
and fixed basis identifications for its input and target entangled pairs
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:219-227]. -/
structure EntanglementTransmissionCode (N : Channel a b)
    (r : Type w) (l : Type y) (t : Type x)
    [Fintype r] [DecidableEq r] [Nonempty r]
    [Fintype l] [DecidableEq l] [Fintype t] [DecidableEq t] where
  encoder : Channel l a
  decoder : Channel b t
  inputPairing : r ≃ l
  targetPairing : r ≃ t

/-- Transmission is a special case of generation: encode one half of the
canonical maximally entangled input. A general encoder can produce a mixed
state [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:219-227]. -/
def EntanglementGenerationCode.ofTransmission
    {N : Channel a b} {r : Type w} {l : Type y} {t : Type x}
    [Fintype r] [DecidableEq r] [Nonempty r]
    [Fintype l] [DecidableEq l] [Fintype t] [DecidableEq t]
    (C : EntanglementTransmissionCode N r l t) : EntanglementGenerationCode N r t where
  encodedState := ((Channel.idChannel r).prod C.encoder).applyState
    (State.maximallyEntangled C.inputPairing)
  decoder := C.decoder
  pairing := C.targetPairing

namespace EntanglementTransmissionCode

variable {N : Channel a b} {r : Type w} {l : Type y} {t : Type x}
variable [Fintype r] [DecidableEq r] [Nonempty r]
variable [Fintype l] [DecidableEq l] [Fintype t] [DecidableEq t]

/-- Transmission fidelity is exactly the fidelity of its generation code. -/
def fidelity (C : EntanglementTransmissionCode N r l t) : ℝ :=
  (EntanglementGenerationCode.ofTransmission C).fidelity

/-- Transmission error in the squared-fidelity convention. -/
def error (C : EntanglementTransmissionCode N r l t) : ℝ :=
  (EntanglementGenerationCode.ofTransmission C).error

/-- Transmission rate for a positive-length block, with the same totalized
zero-length convention as the generation rate. -/
def rate (C : EntanglementTransmissionCode N r l t) (n : ℕ) : ℝ :=
  (EntanglementGenerationCode.ofTransmission C).rate n

/-- Transmission encoding preserves the maximally mixed reference marginal.
This property is not imposed on arbitrary generation codes. -/
theorem ofTransmission_encodedState_marginalA (C : EntanglementTransmissionCode N r l t) :
    (EntanglementGenerationCode.ofTransmission C).encodedState.marginalA =
      State.maximallyMixed r := by
  change (((Channel.idChannel r).prod C.encoder).applyState
    (State.maximallyEntangled C.inputPairing)).marginalA = _
  rw [State.marginalA_applyState_id_prod]
  exact PureVector.maximallyEntangled_marginalA C.inputPairing

end EntanglementTransmissionCode

namespace Channel

variable (N : Channel a b)

/-- Operational achievability using entanglement-transmission codes.
For every positive rate slack and error tolerance, every sufficiently large
positive blocklength admits a code. This is the epsilon/slack formulation of
the reliable code-family definition in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:592-596], following
the quantifier pattern of [KhatriWilde2024Principles,
Chapters/quantum_capacity.tex:575-591]. The textbook's strongest quantum
communication error criterion is not identified with transmission error here.
The three logical registers use copies of the same finite label type; their
basis pairings and arbitrary joint encoder/decoder remain part of the code. -/
def IsAchievableQuantumRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → 0 < n →
      ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ C : EntanglementTransmissionCode (N.tensorPower n) M M M,
          R - δ ≤ C.rate n ∧ C.error ≤ ε

/-- Achievability is downward closed in the communication rate. -/
theorem IsAchievableQuantumRate.mono {N : Channel a b} {R S : ℝ}
    (hS : N.IsAchievableQuantumRate S) (hRS : R ≤ S) : N.IsAchievableQuantumRate R := by
  intro δ hδ ε hε
  obtain ⟨n₀, hn₀⟩ := hS δ hδ ε hε
  refine ⟨n₀, fun n hn hpos => ?_⟩
  obtain ⟨M, iF, iD, iN, C, hrate, herr⟩ := hn₀ n hn hpos
  exact ⟨M, iF, iD, iN, C, (sub_le_sub_right hRS δ).trans hrate, herr⟩

/-- Operational quantum capacity: the real supremum of reliable transmission
rates [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:592-596].
This is separate from regularized coherent information. As for the other
real-valued capacity interfaces, supremum introduction requires a proof that
the operational rate set is bounded above; no converse is built into this
definition. -/
def quantumCapacity : ℝ := sSup {R : ℝ | N.IsAchievableQuantumRate R}

/-- An achievable rate lies below capacity when the rate set is bounded above. -/
theorem le_quantumCapacity
    (hbdd : BddAbove {R : ℝ | N.IsAchievableQuantumRate R})
    {R : ℝ} (hR : N.IsAchievableQuantumRate R) : R ≤ N.quantumCapacity :=
  le_csSup hbdd hR

/-- An upper bound on a nonempty operational rate set bounds its capacity.
The hypotheses carry all coding/converse content. -/
theorem quantumCapacity_le
    (hne : {R : ℝ | N.IsAchievableQuantumRate R}.Nonempty)
    {q : ℝ} (hq : ∀ R, N.IsAchievableQuantumRate R → R ≤ q) :
    N.quantumCapacity ≤ q :=
  csSup_le hne hq

/-- Exponential strong converse above an explicit threshold `q`.
For each positive gap, one exponent and one blocklength threshold work for
all generation codes, including arbitrary mixed encodings and joint decoders.
This uniform code-wise formulation is suited to the exponential bound in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:137-144].
The predicate states the conclusion only; it supplies no weak-converse or
achievability assumption. -/
def HasExponentialQuantumStrongConverseAt (q : ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ α : ℝ, 0 < α ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → 0 < n →
      ∀ (r t : Type u) [Fintype r] [DecidableEq r] [Nonempty r]
        [Fintype t] [DecidableEq t],
      ∀ C : EntanglementGenerationCode (N.tensorPower n) r t,
        q + γ ≤ C.rate n → C.fidelity < Real.rpow 2 (-α * (n : ℝ))

/-- Exponential strong converse at operational quantum capacity. -/
def HasExponentialQuantumStrongConverse : Prop :=
  N.HasExponentialQuantumStrongConverseAt N.quantumCapacity

end Channel

end

end QIT
