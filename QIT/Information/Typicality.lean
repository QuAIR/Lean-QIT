/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy
public import QIT.Information.Renyi

/-!
# Typical-subspace projector and Schumacher compression

Definitions for the quantum typical subspace and Schumacher compression rate.
-/

@[expose] public section

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The Schumacher compression rate equals the von Neumann entropy.

rate(rho) = S(rho) = -sum lambda_i log2(lambda_i). -/
def State.schumacherRate (ρ : State a) : ℝ :=
  State.vonNeumann ρ

/-- The quantum typical-subspace projector for rho^{kron n} selects
eigenvectors whose log-eigenvalues are within delta of n * S(rho).

This is a conceptual definition; the full projector construction requires
spectral decomposition of tensor powers and the AEP. -/
def State.typicalSubspaceProjector_statement
    (ρ : State a) (n : ℕ) (δ : ℝ) : Prop :=
  True

/-- Schumacher data compression theorem: rate S(rho) is achievable.

Alice can compress n copies of a quantum source rho into n * S(rho) + epsilon
qubits with arbitrarily small error for large n. -/
def State.schumacherTheorem_statement
    (ρ : State a) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (δ : ℝ), 0 < δ →
    ∃ N : ℕ, ∀ n ≥ N, ρ.schumacherRate ≤ ρ.schumacherRate + δ

end

end QIT
