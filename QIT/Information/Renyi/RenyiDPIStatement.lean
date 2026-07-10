/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyi
public import QIT.Measurements.Map

/-!
# Sandwiched Renyi DPI statement surfaces

Planning-only statement surfaces for sandwiched Renyi data processing,
upward sandwiched conditional Renyi duality, and measurement-map monotonicity.

These declarations are `Prop`-valued targets used by local reduction theorems.
The completed public PSD-reference sandwiched Renyi DPI theorem is
`QIT.State.sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt`
in `QIT.Information.Renyi.FrankLieb`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State
namespace RenyiDPI
namespace Statement

/-- Sandwiched Renyi data-processing inequality `D̃_α(Φρ ‖ Φσ) ≤ D̃_α(ρ ‖ σ)`
over the range `α ∈ [1/2, ∞)`, `α ≠ 1`, for an endomorphism channel.

This is a planning-only statement surface. The completed public PSD-reference
DPI theorem lives in `QIT.Information.Renyi.FrankLieb`. -/
def sandwichedRenyi_dataProcessing_statement (ρ σ : State a) (Φ : Channel a a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

/-- Same full-rank state-level sandwiched Renyi data-processing statement, but
with a general input-output channel `Φ : Channel a b`.

This is still weaker than the public source theorem for `sandwiched-renyi-dpi`:
the source statement allows a positive semidefinite reference operator `σ`, while
this local surface keeps the current full-rank `State + PosDef` domain. -/
def sandwichedRenyi_dataProcessing_channel_statement (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

/-- Upward sandwiched conditional Renyi duality: for a pure tripartite state
with `AB` and `AC` marginals, `H̃^↑_α(A|B) = -H̃^↑_β(A|C)` when
`1/α + 1/β = 2`. The two bipartite arguments are the `AB` and `AC` marginals of
a common pure state (the purity condition is the documented precondition).

This is a planning-only statement surface. -/
def conditionalSandwichedRenyi_duality_statement (ρ : State (Prod a b))
    (σ : State (Prod a c)) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β) (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (_hab : 1 / α + 1 / β = 2) : Prop :=
  conditionalSandwichedRenyi ρ hρ α hα hα1 =
    - conditionalSandwichedRenyi σ hσ β hβ hβ1

/-- Measurement-map monotonicity: measuring subsystem `A` does not decrease the
upward sandwiched conditional Renyi entropy `H̃^↑_α(·|B)` (a DPI instance).

This is a planning-only statement surface. -/
def measurementMap_conditionalRenyi_monotonicity_statement (ρ : State (Prod a b))
    (hρ : ρ.matrix.PosDef) (M : POVM c a)
    (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα1 : α ≠ 1) : Prop :=
  conditionalSandwichedRenyi (measureSubsystemState M ρ) hρM α hα hα1 ≥
    conditionalSandwichedRenyi ρ hρ α hα hα1

end Statement
end RenyiDPI
end State

end

end QIT
