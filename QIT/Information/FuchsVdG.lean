/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Fidelity
public import QIT.States.TraceNorm.Distance
public import QIT.States.Purification.Uhlmann

/-!
# Fuchs--van de Graaf inequality

## Lower bound `1 - F(ρ,σ) ≤ (1/2)·‖ρ-σ‖₁`

Standard proof: Powers--Stormer inequality `Tr((√ρ - √σ)²) ≤ ‖ρ - σ‖₁` gives
  `‖ρ-σ‖₁ ≥ 2 - 2·Re(Tr(√ρ·√σ)) ≥ 2 - 2·F(ρ,σ) = 2·(1 - F)`,
since `Re(Tr M) ≤ ‖M‖₁` for any matrix `M`.

The single missing lemma is `powers_stormer`.  The scalar inequality
`(√x - √y)² ≤ |x - y|` for `x,y ≥ 0` is a standard analysis check; the
matrix extension follows from the finite-dimensional spectral theorem.
Registered as `m7-s0b-fuchs-vdG-powers-stormer`.

## Upper bound `(1/2)·‖ρ-σ‖₁ ≤ √(1 - F²)`

Requires Uhlmann's fidelity-maximisation (`QIT.States.Purification.Uhlmann`, proved),
trace-distance contraction under partial trace, and the pure-state formula
`‖|ψ⟩⟨ψ|-|φ⟩⟨φ|‖₁ = 2·√(1 - |⟨ψ|φ⟩|²)`.  Registered as
`m7-s0b-fuchs-vdG-upper`.
-/

@[expose] public section

namespace QIT

/- Fuchs-van de Graaf lower and upper bounds are deferred to
   `m7-s0b-fuchs-vdG-powers-stormer` and `m7-s0b-fuchs-vdG-upper`. -/

end QIT
