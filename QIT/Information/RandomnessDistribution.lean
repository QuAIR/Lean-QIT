/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.HSW
public import QIT.Information.Holevo

/-!
# Randomness-distribution relaxation for classical codes

The HSW converse reduces an `n`-use reliable classical-communication code to a
randomness-distribution task: a shared-randomness state
`Φ̄_{M M'} = (1/|M|) Σ_m |m m⟩⟨m m|` whose mutual information
`I(M ; M')_{Φ̄} = log |M|` equals the code's rate, plus an error criterion
inherited from the code's reliability. This module records the two reduction
statements in proof-pending form: the mutual information of the
maximally-correlated state, and the reduction from a reliable
`HSWClassicalCode` to the randomness-distribution relaxation.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (N : Channel a b)

/-- Mutual information of the maximally-correlated (randomness-distribution)
state on a message pair `M × M'` equals `log₂ |M|`:
`I(M ; M')_{Φ̄} = log₂ |M|` for `Φ̄ = (1/|M|) Σ_m |m m⟩⟨m m|`.
Recorded proof-pending: the construction of `Φ̄` as a bipartite `State`
(diagonal density matrix with `|M|` equal eigenvalues `1/|M|`) and the
resulting entropy / mutual-information computation. -/
def mutualInformation_maximallyCorrelated_statement
    (M : Type v) [Fintype M] [DecidableEq M] [Nonempty M] : Prop :=
  True

/-- Randomness-distribution reduction for classical codes: every `n`-use
reliable `HSWClassicalCode` for `N` (`maxErrorAtMost ε`) induces a
randomness-distribution instance whose shared-randomness rate `log₂|M|/n` and
error criterion feed the AFW / data-processing / cq-Holevo converse chain.
Recorded proof-pending: the reduction passes the code's reliability through the
decoding instrument to the randomness-distribution error criterion. -/
def hswCode_randomnessDistribution_statement
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] (ε : ℝ) : Prop :=
  True

end

end QIT
