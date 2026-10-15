/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.Core.Map.QuantumOperation

/-!
# Ordinary finite quantum instruments

An instrument is a finite family of trace-nonincreasing CP maps whose sum is
one channel. Discarding the outcome recovers that channel. This definition is
promoted unchanged from the LOCC layer; protocols use the same public type.
There is no nonempty outcome or system assumption, and this module does not
define higher-order instruments.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT
universe u v w
noncomputable section

/-- A finite quantum instrument. Each outcome branch is completely positive
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

namespace FiniteInstrument

variable {input : Type u} {output : Type v} {outcome : Type w}
variable [Fintype input] [DecidableEq input]
variable [Fintype output] [DecidableEq output] [Fintype outcome]

/-- Summing branch outputs forgets the observed outcome. -/
theorem sum_branch_apply (M : FiniteInstrument input output outcome) (X : CMatrix input) :
    (∑ result, M.branch result X) = M.totalChannel.map X := by
  have h := congrArg (fun f : MatrixMap input output => f X) M.sum_branch_eq_total
  simpa [totalChannel] using h

/-- The sum of the unnormalized branch traces is the input trace. -/
theorem sum_trace_branch (M : FiniteInstrument input output outcome) (X : CMatrix input) :
    (∑ result, (M.branch result X).trace) = X.trace := by
  rw [← Matrix.trace_sum, M.sum_branch_apply, M.totalChannel.tracePreserving]

/-- Every branch satisfies the finite quantum-operation Choi criterion. -/
theorem branch_choi (M : FiniteInstrument input output outcome) (result : outcome) :
    (MatrixMap.choi (M.branch result)).PosSemidef ∧
      QIT.partialTraceB (MatrixMap.choi (M.branch result)) ≤ 1 :=
  (MatrixMap.traceNonincreasingCP_iff_choi _).mp (M.branchTraceNonincreasingCP result)

/-- A channel is an instrument with one deterministic outcome. -/
def ofChannel (N : Channel input output) : FiniteInstrument input output Unit where
  branch _ := N.map
  branchTraceNonincreasingCP _ :=
    MatrixMap.traceNonincreasingCP_of_tracePreserving N.completelyPositive N.tracePreserving
  total := N
  sum_branch_eq_total := by simp

@[simp]
theorem ofChannel_totalChannel (N : Channel input output) :
    (ofChannel N).totalChannel = N := rfl

end FiniteInstrument
end
end QIT
