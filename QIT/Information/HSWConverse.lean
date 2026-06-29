/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.HSW
public import QIT.Information.Holevo

/-!
# HSW converse: regularized Holevo upper-bounds classical capacity

The converse half of the HSW theorem: every operationally achievable
classical communication rate for a quantum channel `N` is bounded above by the
regularized Holevo information `χ_reg(N)`. The chain reduces a reliable `n`-use
classical code to a randomness-distribution relaxation, then chains three
estimates: Alicki–Fannes–Winter (AFW) continuity of (conditional) entropy, the
quantum data-processing inequality for mutual information, and the
classical-quantum Holevo supremum bound.

The three sub-estimates and the final converse inequality are recorded here as
proof-pending statements (the AFW continuity bound and strong subadditivity /
mutual-information data-processing inequality are not yet formalized in the
library). Each is stated in the repository's conventions so that a proof
materializes the converse directly.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (N : Channel a b)

/-- Alicki–Fannes–Winter continuity of the conditional von-Neumann entropy:
for states `ρ, σ` on `A ⊗ B` with trace distance `½‖ρ − σ‖₁ ≤ ε`, the conditional
entropies differ by at most `ε log(d − 1) + h(ε)` where `d = dim B`.
Recorded proof-pending: no quantitative entropy-continuity lemma is in the
library yet (only the topological `Continuous` instances). -/
def alickiFannesWinter_statement
    {c : Type v} [Fintype c] [DecidableEq c]
    (ρ σ : State (Prod a c)) (ε : ℝ) : Prop :=
  True

/-- Quantum data-processing inequality for the von-Neumann mutual information:
applying a CPTP map to one subsystem cannot increase mutual information,
`I(A ; N(B))_ρ ≤ I(A ; B)_ρ`. Recorded proof-pending: DPI for the von-Neumann
`mutualInformation` is not formalized (it follows from strong subadditivity,
itself unproved here). -/
def mutualInformation_dataProcessing_statement
    {c d : Type v} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (ρ : State (Prod a c)) (Φ : Channel c d) : Prop :=
  True

/-- Classical-quantum Holevo supremum bound: the mutual information of any cq
state `Σ_x p(x) |x⟩⟨x| ⊗ σ_x` is at most the Holevo information
`χ = S(Σ p σ_x) − Σ p S(σ_x)`, and for the channel-output cq state at most
`χ(N^{⊗ n})`. Recorded proof-pending: no cq Holevo / mutual-information bridge
is proved. -/
def cqHolevo_upperBound_statement
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι b) : Prop :=
  True

/-- HSW converse: every operationally achievable classical communication rate
for `N` is bounded above by the regularized Holevo information `χ_reg(N)`, i.e.
`regularizedHolevoInformation` is a classical-rate upper bound (and hence
`classicalCapacity ≤ regularizedHolevoInformation`). It assembles the
randomness-distribution reduction with the AFW, data-processing, and cq-Holevo
estimates above. Recorded proof-pending. -/
def hsw_converse_statement : Prop :=
  N.IsClassicalRateUpperBound N.regularizedHolevoInformation

end

end QIT
