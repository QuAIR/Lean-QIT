/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.EntanglementAssistedAsymptotic
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedOneShotUpper
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwichedConverse
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwichedAdditivity

/-!
# Asymptotic upper bounds for entanglement-assisted classical communication

This module defines an assembly interface for the Khatri--Wilde asymptotic
upper-bound and strong-converse route
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331].

Sandwiched-Renyi channel mutual-information additivity and the `alpha -> 1`
limit are kept as an explicit input.  Once that input is available, the
theorems below package it into the existing converse witness, ordinary
capacity upper bound, and strong-converse upper-bound interfaces.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- Source-shaped input expected from the sandwiched-Renyi asymptotic
upper-bound route.

The field is exactly the eventual `n`-use log-cardinality estimate consumed by
`entanglementAssisted_converseWitnessFamily_of_logCardUpperBounds`: for every
rate slack and positive reliability threshold, all sufficiently long reliable
codes have message size bounded by `n * (I(N) + eta)`.

This is a proof-dependency interface, not the asymptotic upper-bound theorem by
itself. -/
structure EntanglementAssistedAsymptoticUpperInput where
  logCard_upper :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  log2 (Fintype.card M : ℝ) ≤
                    (n : ℝ) * (N.entanglementAssistedInformation + η)

/-- The asymptotic upper input gives the standard converse witness family used
by the final capacity-squeeze theorem. -/
theorem entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    EntanglementAssistedConverseWitnessFamily N :=
  N.entanglementAssisted_converseWitnessFamily_of_logCardUpperBounds H.logCard_upper

/-- Ordinary-rate upper-bound consequence of the asymptotic upper input. -/
theorem entanglementAssistedInformation_isRateUpperBound_of_asymptoticUpperInput
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isUpperBound_of_converseWitness
    (N.entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput H)

/-- Strong-converse-rate consequence of the asymptotic upper input. -/
theorem entanglementAssistedInformation_isStrongConverseRate_of_asymptoticUpperInput
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.IsStrongConverseEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isStrongConverseRate_of_converseWitness
    (N.entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput H)

/-- Capacity upper-bound consequence, separated from the asymptotic upper input
so the dependence on the already-proved lower-bound/achievability route stays
explicit. -/
theorem entanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.entanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.entanglementAssistedClassicalCapacity_le_information_of_converseWitness
    hach (N.entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput H)

/-- Strong-converse capacity upper-bound consequence, again keeping the
achievability input explicit for the final capacity squeeze. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.strongConverseEntanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.strongConverseEntanglementAssistedClassicalCapacity_le_information hach
    (N.entanglementAssistedInformation_isStrongConverseRate_of_asymptoticUpperInput H)

/-- Assembly theorem for the asymptotic upper-bound route.

After `EntanglementAssistedAsymptoticUpperInput` is supplied, this theorem
returns the source-facing ordinary upper-bound and strong-converse conclusions,
together with the two capacity inequalities needed by the final capacity
theorem. -/
theorem entanglementAssisted_asymptoticUpperBounds_of_asymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
        N.entanglementAssistedInformation ∧
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation ∧
      N.entanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation := by
  exact
    ⟨N.entanglementAssistedInformation_isRateUpperBound_of_asymptoticUpperInput H,
      N.entanglementAssistedInformation_isStrongConverseRate_of_asymptoticUpperInput H,
      N.entanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
        hach H,
      N.strongConverseEntanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
        hach H⟩

end Channel

end

end QIT
