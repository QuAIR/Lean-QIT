/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.FQSW.Core
public import QIT.States.Geometry.FuchsVdG

/-!
# Operational semantics for quantum state merging

This module formalizes the finite one-way-LOCC protocol contract in the
definition of Horodecki--Oppenheim--Winter state merging.  A protocol acts on
the grouped IID source and an input maximally entangled pair.  Its output,
ideal target, fidelity error, net entanglement rate, and classical rate are
derived from the instrument, conditional Bob channels, and register
cardinalities; none of them is freely assignable.

The source definition and rate convention are in
`swlong.6.2.tex:545-608`.  The equality of the optimal cost with `H(A|B)` is a
separate direct/converse theorem and is not asserted here.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p q u' v'

noncomputable section

/-- A finite quantum instrument.  Each outcome branch is completely positive
and trace-nonincreasing, and the sum of all branches is a channel. -/
structure FiniteInstrument
    (input : Type u) (output : Type v) (outcome : Type w)
    [Fintype input] [DecidableEq input]
    [Fintype output] [DecidableEq output]
    [Fintype outcome] where
  branch : outcome → MatrixMap input output
  branchTraceNonincreasingCP :
    ∀ result, MatrixMap.TraceNonincreasingCP (branch result)
  total : Channel input output
  sum_branch_eq_total : (∑ result, branch result) = total.map

namespace FiniteInstrument

variable {input : Type u} {output : Type v} {outcome : Type w}
variable [Fintype input] [DecidableEq input]
variable [Fintype output] [DecidableEq output]
variable [Fintype outcome]

/-- The channel obtained by forgetting the classical outcome. -/
def totalChannel (M : FiniteInstrument input output outcome) : Channel input output :=
  M.total

theorem branch_completelyPositive
    (M : FiniteInstrument input output outcome) (result : outcome) :
    MatrixMap.IsCompletelyPositive (M.branch result) :=
  (M.branchTraceNonincreasingCP result).completelyPositive

end FiniteInstrument

/-- A finite one-way LOCC operation.  Alice applies an instrument, sends its
classical result, and Bob applies the channel indexed by that result.  The
realization is constrained exactly to the corresponding finite branch sum, so
it is not an arbitrary replacement channel. -/
structure OneWayLOCC
    (aliceInput : Type u) (aliceOutput : Type v)
    (bobInput : Type w) (bobOutput : Type x) (outcome : Type y)
    [Fintype aliceInput] [DecidableEq aliceInput]
    [Fintype aliceOutput] [DecidableEq aliceOutput]
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    [Fintype outcome] where
  aliceInstrument : FiniteInstrument aliceInput aliceOutput outcome
  bobChannel : outcome → Channel bobInput bobOutput
  realization : Channel (Prod aliceInput bobInput) (Prod aliceOutput bobOutput)
  realization_map :
    realization.map =
      ∑ result,
        MatrixMap.kron (aliceInstrument.branch result) (bobChannel result).map

namespace OneWayLOCC

variable {aliceInput : Type u} {aliceOutput : Type v}
variable {bobInput : Type w} {bobOutput : Type x} {outcome : Type y}
variable [Fintype aliceInput] [DecidableEq aliceInput]
variable [Fintype aliceOutput] [DecidableEq aliceOutput]
variable [Fintype bobInput] [DecidableEq bobInput]
variable [Fintype bobOutput] [DecidableEq bobOutput]
variable [Fintype outcome]

/-- The CPTP map computed by the one-way LOCC realization. -/
def toChannel
    (L : OneWayLOCC aliceInput aliceOutput bobInput bobOutput outcome) :
    Channel (Prod aliceInput bobInput) (Prod aliceOutput bobOutput) :=
  L.realization

theorem toChannel_map
    (L : OneWayLOCC aliceInput aliceOutput bobInput bobOutput outcome) :
    L.toChannel.map =
      ∑ result,
        MatrixMap.kron (L.aliceInstrument.branch result) (L.bobChannel result).map :=
  L.realization_map

end OneWayLOCC

/-- Regroup the block source and input entanglement as local Alice, local Bob,
and inaccessible reference registers. -/
def stateMergingInputEquiv
    (A : Type u) (B : Type v) (R : Type w) (KA : Type x) (KB : Type y) :
    Prod (Prod (Prod A B) R) (Prod KA KB) ≃
      Prod (Prod (Prod A KA) (Prod B KB)) R where
  toFun t := (((t.1.1.1, t.2.1), (t.1.1.2, t.2.2)), t.1.2)
  invFun t := (((t.1.1.1, t.1.2.1), t.2), (t.1.1.2, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Regroup the transferred source and output entanglement in the output order
of the one-way LOCC channel, followed by the untouched reference. -/
def stateMergingTargetEquiv
    (A : Type u) (B : Type v) (R : Type w) (LA : Type x) (LB : Type y) :
    Prod (Prod (Prod A B) R) (Prod LA LB) ≃
      Prod (Prod LA (Prod (Prod A B) LB)) R where
  toFun t := ((t.2.1, (t.1.1, t.2.2)), t.1.2)
  invFun t := ((t.1.2.1, t.2), (t.1.1, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- The grouped IID pure source `(A^n B^n) R^n`. -/
def stateMergingBlockSource
    (psi : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    PureVector
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (psi.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n)

/-- A source-shaped finite block state-merging protocol.

Alice holds `A^n K_A`, Bob holds `B^n K_B`, and the input pair has Schmidt
rank `K = |K_A|`.  The one-way LOCC operation leaves Alice with `L_A` and
gives Bob `B' B^n L_B`, where `B'` has the same basis as `A^n`; the output pair
has rank `L = |L_A|`. -/
structure StateMergingBlockProtocol
    (psi : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (kA : Type x) (kB : Type y) (lA : Type z) (lB : Type p)
    (outcome : Type q)
    [Fintype kA] [DecidableEq kA] [Nonempty kA]
    [Fintype kB] [DecidableEq kB]
    [Fintype lA] [DecidableEq lA] [Nonempty lA]
    [Fintype lB] [DecidableEq lB]
    [Fintype outcome] [DecidableEq outcome] [Nonempty outcome] where
  inputEbitPairing : kA ≃ kB
  outputEbitPairing : lA ≃ lB
  locc :
    OneWayLOCC
      (Prod (TensorPower a n) kA)
      lA
      (Prod (TensorPower b n) kB)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)
      outcome

namespace StateMergingBlockProtocol

variable {psi : PureVector (Prod (Prod a b) r)} {n : ℕ}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

local instance stateMergingOutputDecidableEq :
    DecidableEq
      (Prod
        (Prod lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))
        (TensorPower r n)) :=
  @instDecidableEqProd _ _
    (@instDecidableEqProd _ _ inferInstance
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _
          (tensorPowerDecidableEq n) (tensorPowerDecidableEq n))
        inferInstance))
    (tensorPowerDecidableEq n)

variable (C : StateMergingBlockProtocol psi n kA kB lA lB outcome)

/-- The physical input `psi^n tensor Phi_K`, regrouped as local Alice, local
Bob, and reference systems. -/
def initialState :
    State
      (Prod
        (Prod (Prod (TensorPower a n) kA) (Prod (TensorPower b n) kB))
        (TensorPower r n)) :=
  ((stateMergingBlockSource psi n).prod
      (maximallyEntangledPureVector C.inputEbitPairing)).state.reindex
    (stateMergingInputEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) kA kB)

/-- The output computed by the one-way LOCC operation, tensored with the
identity channel on the inaccessible reference. -/
def outputState :
    State
      (Prod
        (Prod lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))
        (TensorPower r n)) :=
  (C.locc.toChannel.prod (Channel.idChannel (TensorPower r n))).applyState C.initialState

/-- The ideal target `Phi_L tensor psi_{B'BR}^n`, expressed in the same output
register order as `outputState`. -/
def targetState :
    State
      (Prod
        (Prod lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))
        (TensorPower r n)) :=
  ((stateMergingBlockSource psi n).prod
      (maximallyEntangledPureVector C.outputEbitPairing)).state.reindex
    (stateMergingTargetEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) lA lB)

/-- Fidelity error `1 - F`, with `F` the repository's squared-fidelity
convention used for the HOW state-merging criterion. -/
def fidelityError : ℝ :=
  1 - C.outputState.squaredFidelity C.targetState

theorem fidelityError_nonneg : 0 ≤ C.fidelityError :=
  sub_nonneg.mpr (State.squaredFidelity_le_one _ _)

theorem fidelityError_le_iff (epsilon : ℝ) :
    C.fidelityError ≤ epsilon ↔
      1 - epsilon ≤ C.outputState.squaredFidelity C.targetState := by
  unfold fidelityError
  constructor <;> intro h <;> linarith

/-- Net entanglement consumption `(log K - log L) / n`.  This real-valued
quantity is intentionally allowed to be negative. -/
def netEntanglementRate
    (_C : StateMergingBlockProtocol psi n kA kB lA lB outcome) : ℝ :=
  if n = 0 then 0
  else (log2 (Fintype.card kA : ℝ) - log2 (Fintype.card lA : ℝ)) / (n : ℝ)

/-- One-way classical communication rate `log |X| / n`. -/
def classicalCommunicationRate
    (_C : StateMergingBlockProtocol psi n kA kB lA lB outcome) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card outcome : ℝ) / (n : ℝ)

end StateMergingBlockProtocol

namespace PureVector

/-- Achievable net entanglement rate for standard state merging.  Every
positive rate slack and fidelity-error tolerance is met by concrete one-way
LOCC block protocols at all sufficiently large blocklengths. -/
def IsAchievableStateMergingRate
    (psi : PureVector (Prod (Prod a b) r)) (R : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (kA : Type x), ∃ (_ : Fintype kA), ∃ (_ : DecidableEq kA),
        ∃ (_ : Nonempty kA),
      ∃ (kB : Type y), ∃ (_ : Fintype kB), ∃ (_ : DecidableEq kB),
      ∃ (lA : Type z), ∃ (_ : Fintype lA), ∃ (_ : DecidableEq lA),
        ∃ (_ : Nonempty lA),
      ∃ (lB : Type p), ∃ (_ : Fintype lB), ∃ (_ : DecidableEq lB),
      ∃ (outcome : Type q), ∃ (_ : Fintype outcome), ∃ (_ : DecidableEq outcome),
        ∃ (_ : Nonempty outcome),
      ∃ C : StateMergingBlockProtocol psi n kA kB lA lB outcome,
        C.netEntanglementRate ≤ R + delta ∧ C.fidelityError ≤ epsilon

/-- Standard state-merging cost: the infimum of achievable net entanglement
rates.  No sign restriction is imposed, so negative conditional-entropy
sources can be represented as net entanglement generation. -/
def stateMergingCost (psi : PureVector (Prod (Prod a b) r)) : ℝ :=
  sInf {R : ℝ |
    PureVector.IsAchievableStateMergingRate.{u, v, w, x, y, z, p, q} psi R}

end PureVector

end

end QIT
