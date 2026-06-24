/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel

/-!
# Measurement maps with quantum side information

Applying a measurement on subsystem `A` of a bipartite state while leaving the
side-information system `B` untouched, as required by the tripartite entropic
uncertainty statement. The identity-on-`B` factor is a single-Kraus (identity)
channel, so the side-information map is `Channel.measure M ⊗ Channel.idChannel`.

Source: Tomamichel2015FiniteResources, `apps.tex` (measurement maps
`M_X ∈ CPTP(A,X)`, applied to a tripartite `rho_ABC`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {x : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype x] [DecidableEq x]

/-- Measure subsystem `A` of a bipartite state with a POVM `M`, keeping the
quantum side information `B` untouched. The output lives on `Prod x b`, where
`x` indexes the measurement outcomes. -/
def measureSubsystemState (M : POVM x a) (ρ : State (Prod a b)) :
    State (Prod x b) :=
  (Channel.prod (Channel.measure M) (Channel.idChannel b)).applyState ρ

end

end QIT
