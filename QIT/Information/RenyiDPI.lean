/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi
public import QIT.Information.ConditionalRenyi
public import QIT.Measurements.Map

/-!
# Sandwiched Renyi DPI, duality, and measurement monotonicity (statement layer)

Source-shaped statement targets for the deep theorems on the proof route of the
tripartite entropic uncertainty relation: sandwiched Renyi data processing,
upward sandwiched conditional Renyi duality, and the measurement-map monotonicity
that follows from DPI.

These are statement-only (`def : Prop`); the proofs require pinching and complex
interpolation not currently available in the local stack, so no proof is claimed
and no forbidden placeholder tokens are introduced.

Source: Tomamichel2015FiniteResources, `renyi.tex` (sandwiched DPI / pinching),
`cond.tex` (upward conditional Renyi duality, `pr:dual-new`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

/-- Sandwiched Renyi data-processing inequality `D̃_α(Φρ ‖ Φσ) ≤ D̃_α(ρ ‖ σ)`
over the range `α ∈ [1/2, ∞)`, `α ≠ 1`. Statement only; the proof needs pinching
and complex interpolation. -/
def sandwichedRenyi_dataProcessing_statement (ρ σ : State a) (Φ : Channel a a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

/-- Upward sandwiched conditional Renyi duality: for a pure tripartite state
with `AB` and `AC` marginals, `H̃^↑_α(A|B) = -H̃^↑_β(A|C)` when
`1/α + 1/β = 2`. The two bipartite arguments are the `AB` and `AC` marginals of
a common pure state (the purity condition is the documented precondition).
Statement only. -/
def conditionalSandwichedRenyi_duality_statement (ρ : State (Prod a b))
    (σ : State (Prod a c)) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β) (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hab : 1 / α + 1 / β = 2) : Prop :=
  conditionalSandwichedRenyi ρ hρ α hα hα1 =
    - conditionalSandwichedRenyi σ hσ β hβ hβ1

/-- Measurement-map monotonicity: measuring subsystem `A` does not decrease the
upward sandwiched conditional Renyi entropy `H̃^↑_α(·|B)` (a DPI instance).
Statement only. -/
def measurementMap_conditionalRenyi_monotonicity_statement (ρ : State (Prod a b))
    (hρ : ρ.matrix.PosDef) (M : POVM c a)
    (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα1 : α ≠ 1) : Prop :=
  conditionalSandwichedRenyi (measureSubsystemState M ρ) hρM α hα hα1 ≥
    conditionalSandwichedRenyi ρ hρ α hα hα1

end State

end

end QIT
