/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.MaximallyEntangled

/-!
# Maximally entangled invariant

The invariant is stated directly through the two reduced density states.  It
does not depend on a protocol-specific representation of an entangled pair.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

namespace PureVector

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Nonempty b]

/-- A bipartite pure vector is maximally entangled when both marginals are the
corresponding canonical maximally mixed states. -/
def IsMaximallyEntangled (ψ : PureVector (Prod a b)) : Prop :=
  ψ.state.marginalA = State.maximallyMixed a ∧
    ψ.state.marginalB = State.maximallyMixed b

theorem maximallyEntangled_isMaximallyEntangled (pairing : a ≃ b) :
    (maximallyEntangled pairing).IsMaximallyEntangled := by
  constructor
  · exact maximallyEntangled_marginalA pairing
  · exact maximallyEntangled_marginalB pairing

end PureVector

end
end QIT
