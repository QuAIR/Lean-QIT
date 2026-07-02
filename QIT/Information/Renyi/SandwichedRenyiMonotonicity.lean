/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwiched
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Sandwiched Renyi monotonicity support

This module isolates reusable high-parameter monotonicity ingredients for the
sandwiched Renyi divergence and mutual information.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The Holder conjugate exponent associated with a high Renyi parameter. -/
theorem highAlpha_holderConjugate {alpha : Real} (halpha : 1 < alpha) :
    alpha.HolderConjugate (alpha / (alpha - 1)) := by
  simpa [Real.conjExponent] using Real.HolderConjugate.conjExponent halpha

/-- Reciprocal of the high-parameter Holder conjugate. -/
theorem one_div_highAlpha_conjExponent {alpha : Real} (halpha : 1 < alpha) :
    1 / (alpha / (alpha - 1)) = (alpha - 1) / alpha := by
  have halpha_pos : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
  have hden : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt halpha)
  field_simp [halpha_pos, hden]

/-- The high-parameter Holder conjugate exponent is positive. -/
theorem highAlpha_conjExponent_pos {alpha : Real} (halpha : 1 < alpha) :
    0 < alpha / (alpha - 1) := by
  exact div_pos (lt_trans zero_lt_one halpha) (sub_pos.mpr halpha)

/-- The high-parameter Holder conjugate exponent is strictly above one. -/
theorem one_lt_highAlpha_conjExponent {alpha : Real} (halpha : 1 < alpha) :
    1 < alpha / (alpha - 1) := by
  have hden : 0 < alpha - 1 := sub_pos.mpr halpha
  rw [lt_div_iff₀ hden]
  linarith

/-- The reciprocal high-parameter Holder conjugate lies in `(0, 1)`. -/
theorem highAlpha_conjExponent_inv_mem_Ioo {alpha : Real} (halpha : 1 < alpha) :
    (alpha - 1) / alpha ∈ Set.Ioo (0 : Real) 1 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  constructor
  · exact div_pos (sub_pos.mpr halpha) halpha_pos
  · rw [div_lt_one halpha_pos]
    linarith

/-- The high-parameter sandwiched reference exponent is negative. -/
theorem highAlpha_sandwichExponent_neg {alpha : Real} (halpha : 1 < alpha) :
    (1 - alpha) / (2 * alpha) < 0 := by
  have hnum : 1 - alpha < 0 := sub_neg.mpr halpha
  have hden : 0 < 2 * alpha := mul_pos (by norm_num) (lt_trans zero_lt_one halpha)
  exact div_neg_of_neg_of_pos hnum hden

/-- A derivative-sign criterion for monotonicity on an open right ray. -/
theorem monotoneOn_Ioi_of_deriv_nonneg {f : Real → Real} {c : Real}
    (hcont : ContinuousOn f (Set.Ioi c))
    (hdiff : DifferentiableOn Real f (Set.Ioi c))
    (hderiv : ∀ x, c < x → 0 ≤ deriv f x) :
    MonotoneOn f (Set.Ioi c) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi c) hcont ?_ ?_
  · simpa [interior_Ioi] using hdiff
  · intro x hx
    exact hderiv x (by simpa [interior_Ioi] using hx)

/-- Convert monotonicity on the open high-parameter ray into the subtype form
used by right-limit and minimax handoffs. -/
theorem highAlphaSubtype_mono_of_monotoneOn_Ioi {β : Type*} [Preorder β]
    {f : Real → β} (hmono : MonotoneOn f (Set.Ioi (1 : Real))) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 → f alpha.1 ≤ f beta.1 := by
  intro alpha beta hab
  exact hmono alpha.2 beta.2 hab

namespace State

/-- A derivative-sign criterion specialized to the finite high-parameter
PSD-reference branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_mono_of_deriv_nonneg
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    (hcont :
      ContinuousOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha)
        (Set.Ioi (1 : Real)))
    (hdiff :
      DifferentiableOn Real
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha)
        (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ alpha : Real, 1 < alpha →
        0 ≤ deriv
          (fun beta : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma beta)
          alpha)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha.1 ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma beta.1 := by
  have hmono :
      MonotoneOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha)
        (Set.Ioi (1 : Real)) :=
    monotoneOn_Ioi_of_deriv_nonneg hcont hdiff hderiv
  exact hmono alpha.2 beta.2 hab

/-- On a positive-definite reference, finite-branch monotonicity lifts to the
support-aware high-parameter extended-real branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_mono_posDef_reference_of_finite_mono
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosDef)
    {alpha beta : {alpha : Real // 1 < alpha}}
    (hfinite :
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef alpha.1 ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef beta.1) :
    sandwichedRenyiPSDReferenceHighAlphaE rho sigma hsigma.posSemidef alpha.1 ≤
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hsigma.posSemidef beta.1 := by
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hsigma.posSemidef alpha.1
      (Matrix.Supports.of_right_posDef rho.matrix sigma hsigma),
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hsigma.posSemidef beta.1
      (Matrix.Supports.of_right_posDef rho.matrix sigma hsigma)]
  exact EReal.coe_le_coe_iff.mpr hfinite

/-- On a positive-definite reference, derivative nonnegativity of the finite
branch gives monotonicity of the PSD-reference extended-real divergence. -/
theorem sandwichedRenyiPSDReferenceE_mono_posDef_reference_of_deriv_nonneg
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosDef)
    (hcont :
      ContinuousOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef alpha)
        (Set.Ioi (1 : Real)))
    (hdiff :
      DifferentiableOn Real
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef alpha)
        (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ alpha : Real, 1 < alpha →
        0 ≤ deriv
          (fun beta : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef beta)
          alpha)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1) :
    sandwichedRenyiPSDReferenceE rho sigma hsigma.posSemidef alpha.1 ≤
      sandwichedRenyiPSDReferenceE rho sigma hsigma.posSemidef beta.1 := by
  rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt alpha.2)),
    sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt beta.2))]
  exact
    sandwichedRenyiPSDReferenceHighAlphaE_mono_posDef_reference_of_finite_mono
      rho hsigma
      (sandwichedRenyiPSDReferenceHighAlphaFinite_mono_of_deriv_nonneg
        rho hsigma.posSemidef hcont hdiff hderiv hab)

/-- For a full-rank product reference `rho_A ⊗ sigma_B`, derivative
nonnegativity of the finite branch gives monotonicity of the fixed
side-information candidate. -/
theorem sandwichedRenyiMutualInformationCandidateE_mono_posDef_reference_of_deriv_nonneg
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrhoA : rhoAB.marginalA.matrix.PosDef) (hsigmaB : sigmaB.matrix.PosDef)
    (hcont :
      ContinuousOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos alpha)
        (Set.Ioi (1 : Real)))
    (hdiff :
      DifferentiableOn Real
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos alpha)
        (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ alpha : Real, 1 < alpha →
        0 ≤ deriv
          (fun beta : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB).matrix
              (rhoAB.marginalA.prod sigmaB).pos beta)
          alpha)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1 := by
  have href : (rhoAB.marginalA.prod sigmaB).matrix.PosDef :=
    State.prod_posDef hrhoA hsigmaB
  simpa [sandwichedRenyiMutualInformationCandidateE_eq] using
    sandwichedRenyiPSDReferenceE_mono_posDef_reference_of_deriv_nonneg
      rhoAB href hcont hdiff hderiv hab

/-- If the optimized side-state infimum has been restricted to full-rank side
states, monotonicity of every full-rank fixed candidate gives monotonicity of
the optimized state quantity. -/
theorem sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_candidate_mono
    (rhoAB : State (Prod a b))
    (hfullRankInf :
      ∀ gamma : {gamma : Real // 1 < gamma},
        rhoAB.sandwichedRenyiMutualInformationE gamma.1 =
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 gamma.1)
    (hmono :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ∀ alpha beta : {alpha : Real // 1 < alpha},
          alpha.1 ≤ beta.1 →
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha.1 ≤
              rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 beta.1) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  intro alpha beta hab
  rw [hfullRankInf alpha, hfullRankInf beta]
  refine le_iInf fun sigmaB => ?_
  exact (iInf_le
    (fun tauB : {tauB : State b // tauB.matrix.PosDef} =>
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha.1)
    sigmaB).trans (hmono sigmaB alpha beta hab)

/-- Full-rank optimized monotonicity from derivative nonnegativity of each
full-rank fixed-candidate finite branch. -/
theorem sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_deriv_nonneg
    (rhoAB : State (Prod a b)) (hrhoA : rhoAB.marginalA.matrix.PosDef)
    (hfullRankInf :
      ∀ gamma : {gamma : Real // 1 < gamma},
        rhoAB.sandwichedRenyiMutualInformationE gamma.1 =
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 gamma.1)
    (hcont :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ContinuousOn
          (fun alpha : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB.1).matrix
              (rhoAB.marginalA.prod sigmaB.1).pos alpha)
          (Set.Ioi (1 : Real)))
    (hdiff :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        DifferentiableOn Real
          (fun alpha : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB.1).matrix
              (rhoAB.marginalA.prod sigmaB.1).pos alpha)
          (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ∀ alpha : Real, 1 < alpha →
          0 ≤ deriv
            (fun beta : Real =>
              sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.marginalA.prod sigmaB.1).matrix
                (rhoAB.marginalA.prod sigmaB.1).pos beta)
            alpha) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  refine
    sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_candidate_mono
      rhoAB hfullRankInf ?_
  intro sigmaB alpha beta hab
  exact
    sandwichedRenyiMutualInformationCandidateE_mono_posDef_reference_of_deriv_nonneg
      rhoAB sigmaB.1 hrhoA sigmaB.2 (hcont sigmaB) (hdiff sigmaB)
      (hderiv sigmaB) hab

end State

end

end QIT
