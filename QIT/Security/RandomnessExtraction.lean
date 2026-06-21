/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.ExtractorQuadraticBridge

/-!
# Direct randomness-extraction bound

This module assembles the extractor trace bridge, centered collision-uniform
quadratic collapse, and positive-definite conditional-min-entropy quadratic
bound into the direct leftover-hash achievability statement.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe uF uZ uS ue

noncomputable section

variable {F : Type uF} {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype e] [DecidableEq e]

namespace HashFamily

/--
Seed-averaged direct extractor bound in squared form.

This is the direct achievability route under the source-shaped
collision-uniform hash-family hypothesis and an explicit positive-definite
side-information reference state.
-/
theorem extractorSeedAverageTraceDistance_sq_le_card_mul_rpow_of_collisionUniform_conditionalMinEntropyFeasible_posDef
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) (σ : State e) (lam : ℝ)
    (hσ : σ.matrix.PosDef)
    (hmin : State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam) :
    (extractorSeedAverageTraceDistance H E) ^ 2 ≤
      (Fintype.card S : ℝ) * Real.rpow 2 (-lam) := by
  classical
  let q : F → ℝ := fun f => H.extractorSeedCenteredQuadraticTerm E σ f
  have hcard_nonneg : 0 ≤ (Fintype.card S : ℝ) := by positivity
  have hq : ∀ f, 0 ≤ q f := by
    intro f
    simpa [q] using H.extractorSeedCenteredQuadraticTerm_nonneg_of_posDef E σ f hσ
  have hseed : ∀ f,
      extractorSeedTraceDistance H E f ≤
        Real.sqrt ((Fintype.card S : ℝ) * q f) := by
    intro f
    simpa [q] using
      H.extractorSeedTraceDistance_le_sqrt_card_mul_centeredQuadraticTerm_posDef
        E σ f hσ
  have havg :
      (extractorSeedAverageTraceDistance H E) ^ 2 ≤
        (Fintype.card S : ℝ) * extractorSeedQuadraticAverage H q :=
    H.extractorSeedAverageTraceDistance_sq_le_scaled_quadraticAverage
      E (Fintype.card S : ℝ) q hcard_nonneg hq hseed
  have hcollapse :
      extractorSeedQuadraticAverage H q ≤ extractorCqQuadraticTerm E σ := by
    simpa [q] using
      H.extractorSeedCenteredQuadraticAverage_le_cqQuadratic_of_collisionUniform_posDef
        E σ hH hσ
  have hcq :
      extractorCqQuadraticTerm E σ ≤ Real.rpow 2 (-lam) :=
    extractorCqQuadratic_le_rpow_of_conditionalMinEntropyFeasible_posDef
      E σ lam hσ hmin
  exact havg.trans
    (mul_le_mul_of_nonneg_left (hcollapse.trans hcq) hcard_nonneg)

/--
Direct leftover-hash achievability bound for extractor secrecy distance.

The theorem proves the direct bound only, under `CollisionUniform` and
`σ.matrix.PosDef`; Tomamichel's converse and the full two-sided extractable
length theorem are intentionally outside this statement.
-/
theorem extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropyFeasible_posDef
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) (σ : State e) (lam : ℝ)
    (hσ : σ.matrix.PosDef)
    (hmin : State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam) :
    extractorSecrecyDistance (extractorOutputState H E) ≤
      Real.sqrt ((Fintype.card S : ℝ) * Real.rpow 2 (-lam)) := by
  classical
  let q : F → ℝ := fun f => H.extractorSeedCenteredQuadraticTerm E σ f
  have hcard_nonneg : 0 ≤ (Fintype.card S : ℝ) := by positivity
  have hq : ∀ f, 0 ≤ q f := by
    intro f
    simpa [q] using H.extractorSeedCenteredQuadraticTerm_nonneg_of_posDef E σ f hσ
  have hseed : ∀ f,
      extractorSeedTraceDistance H E f ≤
        Real.sqrt ((Fintype.card S : ℝ) * q f) := by
    intro f
    simpa [q] using
      H.extractorSeedTraceDistance_le_sqrt_card_mul_centeredQuadraticTerm_posDef
        E σ f hσ
  have hsec_sq_base :
      (extractorSecrecyDistance (extractorOutputState H E)) ^ 2 ≤
        (Fintype.card S : ℝ) * extractorSeedQuadraticAverage H q :=
    H.extractorSecrecyDistance_sq_le_scaled_quadraticAverage
      E (Fintype.card S : ℝ) q hcard_nonneg hq hseed
  have hcollapse :
      extractorSeedQuadraticAverage H q ≤ extractorCqQuadraticTerm E σ := by
    simpa [q] using
      H.extractorSeedCenteredQuadraticAverage_le_cqQuadratic_of_collisionUniform_posDef
        E σ hH hσ
  have hcq :
      extractorCqQuadraticTerm E σ ≤ Real.rpow 2 (-lam) :=
    extractorCqQuadratic_le_rpow_of_conditionalMinEntropyFeasible_posDef
      E σ lam hσ hmin
  have hsec_sq :
      (extractorSecrecyDistance (extractorOutputState H E)) ^ 2 ≤
        (Fintype.card S : ℝ) * Real.rpow 2 (-lam) :=
    hsec_sq_base.trans
      (mul_le_mul_of_nonneg_left (hcollapse.trans hcq) hcard_nonneg)
  exact Real.le_sqrt_of_sq_le hsec_sq

end HashFamily

end

end QIT.Security
