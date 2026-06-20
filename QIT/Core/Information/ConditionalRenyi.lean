/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Information.Smooth
public import QIT.Core.Information.Renyi

/-!
# Conditional upward sandwiched Renyi entropy

The one-shot conditional upward sandwiched Renyi entropy

  H̃^↑_α(A|B)_ρ = sup_{σ_B}  −D̃_α(ρ_AB ‖ I_A ⊗ σ_B)

in the repository bits convention, over the data-processing-valid range
`α ≥ 1/2` (`α ≠ 1`).

The second argument `I_A ⊗ σ_B` is subnormalized (trace `d_A`), so this kernel
works at the matrix level via `CFC.rpow` on the Kronecker product directly; it
does not require a `CFC.rpow` Kronecker factorization lemma. The supremum is
over full-rank (normalized, `PosDef`) side-information states `σ_B`.

Source: Tomamichel2015FiniteResources, `cond.tex` (the four conditional Renyi
entropies; the sandwiched data-processing range `α ∈ [1/2, ∞]`).

Optimizer existence, compactness, data processing, duality, and the entropic
uncertainty theorem are out of scope for this definition layer.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- The per-side-information candidate `−D̃_α(ρ_AB ‖ I_A ⊗ σ_B)`.

Both witnesses are API preconditions aligning the statement with the
mathematical domain (positive-definite `ρ_AB` and `σ_B`); they are not needed
for `CFC.rpow` to typecheck, mirroring `State.sandwichedRenyi`. -/
def conditionalSandwichedRenyiCandidate (ρ : State (Prod a b)) (_hρ : ρ.matrix.PosDef)
    (σ : State b) (_hσ : σ.matrix.PosDef) (α : ℝ) (_hα_pos : 0 < α)
    (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := -(1 / (α - 1))
  let s := (1 - α) / (2 * α)
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let M := CFC.rpow (CFC.rpow τ s * ρ.matrix * CFC.rpow τ s) α
  r * log2 M.trace.re

/-- Conditional upward sandwiched Renyi entropy `H̃^↑_α(A|B)_ρ` as the supremum
over normalized full-rank side-information states `σ_B` of the candidate value.

The `α = 1` boundary is not covered by the sandwiched kernel (it would require
the Umegaki limit) and is left as a precise blocker rather than a convention;
the API surface is `α ≥ 1/2`, `α ≠ 1`. -/
def conditionalSandwichedRenyi (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : ℝ :=
  sSup {h | ∃ σ : State b, ∃ hσ : σ.matrix.PosDef,
    h = conditionalSandwichedRenyiCandidate ρ hρ σ hσ α (by linarith) hα_ne_one}

@[simp]
theorem conditionalSandwichedRenyi_eq (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one =
      sSup {h | ∃ σ : State b, ∃ hσ : σ.matrix.PosDef,
        h = ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one} :=
  rfl

end State

end

end QIT
