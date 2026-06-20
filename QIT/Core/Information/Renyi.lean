/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Information.Entropy

/-!
# Quantum Renyi divergences

Petz and sandwiched Renyi divergences defined via `CFC.rpow`, plus their
tensor-power additivity under `State.prod` (Kronecker product). This is the
FQAEP engine layer — the Renyi family is the workhorse of the finite-N AEP
and one-shot decoupling bounds.

The definitions expose positive-definite input witnesses and order-domain
witnesses `0 < α`, `α ≠ 1` as API preconditions. The witnesses are not
computationally used by `CFC.rpow`, but they keep downstream theorem
statements aligned with the mathematical domain.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- Petz quantum Renyi divergence D_α(ρ‖σ) = 1/(α-1) · log2 Tr(ρ^α · σ^(1-α)).

Requires α > 0, α ≠ 1 and both states positive-definite (invertible). -/
def petzRenyi (ρ σ : State a) (_hρ : ρ.matrix.PosDef) (_hσ : σ.matrix.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let A := CFC.rpow ρ.matrix α
  let B := CFC.rpow σ.matrix (1 - α)
  r * log2 ((A * B).trace.re)

/-- Sandwiched quantum Renyi divergence D̃_α(ρ‖σ).

D̃_α(ρ‖σ) = 1/(α-1) · log2 Tr((σ^((1-α)/2α) · ρ · σ^((1-α)/2α))^α). -/
def sandwichedRenyi (ρ σ : State a) (_hρ : ρ.matrix.PosDef) (_hσ : σ.matrix.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ.matrix s
  let M := CFC.rpow (C * ρ.matrix * C) α
  r * log2 (M.trace.re)

/- The tensor-power additivity theorems (`petzRenyi_additive`,
   `sandwichedRenyi_additive`) require `CFC.rpow (A ⊗ B) α = (CFC.rpow A α) ⊗ (CFC.rpow B α)`,
   a lemma not yet available in mathlib. -/

end State

end

end QIT
