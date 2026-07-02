/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.SandwichedRenyiMonotonicity
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Optimized sandwiched Renyi upper semicontinuity support

This module isolates the full-rank approximation route for optimized
sandwiched Renyi mutual information.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Positive definiteness is eventually preserved along PSD-constrained
matrix paths converging to a positive-definite limit. -/
theorem eventually_posDef_of_tendsto_posDef
    {X : Type*} {l : Filter X} {M : X -> CMatrix a} {A : CMatrix a}
    (hM : Tendsto M l (nhds A))
    (hMpsd : Filter.Eventually (fun x => (M x).PosSemidef) l)
    (hA : A.PosDef) :
    Filter.Eventually (fun x => (M x).PosDef) l := by
  have hdet_ne : A.det ≠ 0 :=
    hA.posSemidef.posDef_iff_det_ne_zero.mp hA
  have hdet :
      Tendsto (fun x : X => (M x).det) l (nhds A.det) :=
    continuous_id.matrix_det.tendsto A |>.comp hM
  have hevent_det : Filter.Eventually (fun x : X => (M x).det ≠ 0) l :=
    hdet.eventually (isOpen_ne.mem_nhds hdet_ne)
  filter_upwards [hMpsd, hevent_det] with x hxpsd hxdet
  exact hxpsd.posDef_iff_det_ne_zero.mpr hxdet

namespace State

/-- The high-parameter sandwiched trace power is continuous when the input
state and reference state vary together, provided the reference path is
eventually full-rank and the limiting reference is full-rank. -/
theorem sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_state_reference
    {X : Type*} {l : Filter X} {rhoF sigmaF : X -> State a} {rho sigma : State a}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma))
    (hsigmaFpd : Filter.Eventually (fun x => (sigmaF x).matrix.PosDef) l)
    (hsigma : sigma.matrix.PosDef)
    (alpha : Real) (halpha_pos : 0 < alpha) :
    Tendsto
      (fun x : X =>
        (((CFC.rpow
          (sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha)
          alpha).trace).re))
      l
      (nhds
        (((CFC.rpow
          (sandwichedRenyiReferenceInner rho sigma.matrix alpha)
          alpha).trace).re)) := by
  let s : Real := (1 - alpha) / (2 * alpha)
  have hrhoMatrix :
      Tendsto (fun x : X => (rhoF x).matrix) l (nhds rho.matrix) :=
    State.continuous_matrix.tendsto rho |>.comp hrhoF
  have hsigmaMatrix :
      Tendsto (fun x : X => (sigmaF x).matrix) l (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp hsigmaF
  have hsigmaPow :
      Tendsto (fun x : X => CFC.rpow (sigmaF x).matrix s) l
        (nhds (CFC.rpow sigma.matrix s)) :=
    _root_.QIT.cMatrix_rpow_tendsto_of_tendsto_posDef
      s hsigmaMatrix hsigmaFpd hsigma
  have hinner :
      Tendsto
        (fun x : X =>
          sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha)
        l
        (nhds (sandwichedRenyiReferenceInner rho sigma.matrix alpha)) := by
    unfold sandwichedRenyiReferenceInner
    exact (hsigmaPow.mul hrhoMatrix).mul hsigmaPow
  have hinner_psd :
      Filter.Eventually
        (fun x : X =>
          (sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha).PosSemidef)
        l :=
    hsigmaFpd.mono fun x hx =>
      sandwichedRenyiReferenceInner_posSemidef (rhoF x) hx.posSemidef alpha
  exact
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      halpha_pos hinner hinner_psd
      (sandwichedRenyiReferenceInner_posSemidef rho hsigma.posSemidef alpha)

/-- The finite high-parameter PSD-reference branch is continuous when the
input state and a full-rank reference state vary together. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_tendsto_posDef_state_reference
    {X : Type*} {l : Filter X} {rhoF sigmaF : X -> State a} {rho sigma : State a}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma))
    (hsigmaFpd : Filter.Eventually (fun x => (sigmaF x).matrix.PosDef) l)
    (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    Tendsto
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaFinite
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
      l
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          rho sigma.matrix sigma.pos alpha)) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have htrace :=
    sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_state_reference
      hrhoF hsigmaF hsigmaFpd hsigma alpha halpha_pos
  have htarget_pos :
      0 <
        (((CFC.rpow
          (sandwichedRenyiReferenceInner rho sigma.matrix alpha)
          alpha).trace).re) := by
    simpa [psdTracePower] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        rho hsigma alpha
  have hlog :
      Tendsto
        (fun x : X =>
          log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha)
              alpha).trace).re))
        l
        (nhds
          (log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner rho sigma.matrix alpha)
              alpha).trace).re))) := by
    have hrawLog := Filter.Tendsto.log htrace (ne_of_gt htarget_pos)
    simpa [log2] using
      hrawLog.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  simpa [sandwichedRenyiPSDReferenceHighAlphaFinite, psdTracePower] using
    tendsto_const_nhds.mul hlog

/-- The support-aware high-parameter PSD-reference branch is continuous as an
extended-real function along full-rank reference paths. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_tendsto_of_tendsto_posDef_state_reference
    {X : Type*} {l : Filter X} {rhoF sigmaF : X -> State a} {rho sigma : State a}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma))
    (hsigmaFpd : Filter.Eventually (fun x => (sigmaF x).matrix.PosDef) l)
    (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    Tendsto
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaE
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
      l
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaE
          rho sigma.matrix sigma.pos alpha)) := by
  have hfinite :
      Tendsto
        (fun x : X =>
          sandwichedRenyiPSDReferenceHighAlphaFinite
            (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
        l
        (nhds
          (sandwichedRenyiPSDReferenceHighAlphaFinite
            rho sigma.matrix sigma.pos alpha)) :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_tendsto_posDef_state_reference
      hrhoF hsigmaF hsigmaFpd hsigma halpha
  have htarget :
      sandwichedRenyiPSDReferenceHighAlphaE
          rho sigma.matrix sigma.pos alpha =
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          rho sigma.matrix sigma.pos alpha : EReal) := by
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho sigma.pos alpha
      (Matrix.Supports.of_right_posDef rho.matrix sigma.matrix hsigma)]
  have hcongr :
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaE
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
        =ᶠ[l]
      (fun x : X =>
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha : EReal)) := by
    filter_upwards [hsigmaFpd] with x hx
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (rhoF x) (sigmaF x).pos alpha
      (Matrix.Supports.of_right_posDef (rhoF x).matrix (sigmaF x).matrix hx)]
  simpa [htarget] using (EReal.tendsto_coe.mpr hfinite).congr' hcongr.symm

/-- Product states are continuous in both factors. -/
theorem prod_tendsto
    {X : Type*} {l : Filter X} {rhoF : X -> State a} {sigmaF : X -> State b}
    {rho : State a} {sigma : State b}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma)) :
    Tendsto (fun x : X => (rhoF x).prod (sigmaF x)) l (nhds (rho.prod sigma)) := by
  have hleft :
      Tendsto (fun x : X => (rhoF x).matrix) l (nhds rho.matrix) :=
    State.continuous_matrix.tendsto rho |>.comp hrhoF
  have hright :
      Tendsto (fun x : X => (sigmaF x).matrix) l (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp hsigmaF
  have hpair :
      Tendsto
        (fun x : X => ((rhoF x).matrix, (sigmaF x).matrix))
        l
        (nhds (rho.matrix, sigma.matrix)) :=
    hleft.prodMk_nhds hright
  have hkr :
      Continuous fun M : CMatrix a × CMatrix b => Matrix.kronecker M.1 M.2 := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        (continuous_fst.matrix_elem x.1 y.1).mul
          (continuous_snd.matrix_elem x.2 y.2)
  have hmatrix :
      Tendsto (fun x : X => ((rhoF x).prod (sigmaF x)).matrix)
        l (nhds (rho.prod sigma).matrix) := by
    simpa [State.prod] using
      hkr.tendsto (rho.matrix, sigma.matrix) |>.comp hpair
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  exact hmatrix

/-- A fixed full-rank side-information candidate is continuous along input
state paths whose limiting left marginal is full-rank. -/
theorem sandwichedRenyiMutualInformationCandidateE_tendsto_of_tendsto_posDef
    {X : Type*} {l : Filter X}
    {rhoF : X -> State (Prod a b)} {rho : State (Prod a b)}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hrhoA : rho.marginalA.matrix.PosDef)
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    Tendsto
      (fun x : X => (rhoF x).sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      l
      (nhds (rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)) := by
  have hmarg :
      Tendsto (fun x : X => (rhoF x).marginalA) l (nhds rho.marginalA) :=
    State.marginalA_continuous.tendsto rho |>.comp hrhoF
  have hmarg_matrix :
      Tendsto (fun x : X => (rhoF x).marginalA.matrix)
        l (nhds rho.marginalA.matrix) :=
    State.continuous_matrix.tendsto rho.marginalA |>.comp hmarg
  have hmarg_pd :
      Filter.Eventually (fun x : X => (rhoF x).marginalA.matrix.PosDef) l :=
    eventually_posDef_of_tendsto_posDef hmarg_matrix
      (Filter.Eventually.of_forall fun x => (rhoF x).marginalA.pos) hrhoA
  have href_tend :
      Tendsto (fun x : X => (rhoF x).marginalA.prod sigmaB)
        l (nhds (rho.marginalA.prod sigmaB)) :=
    State.prod_tendsto hmarg tendsto_const_nhds
  have href_pd :
      Filter.Eventually
        (fun x : X => ((rhoF x).marginalA.prod sigmaB).matrix.PosDef) l := by
    filter_upwards [hmarg_pd] with x hx
    exact State.prod_posDef hx hsigmaB
  have hhigh :
      Tendsto
        (fun x : X =>
          sandwichedRenyiPSDReferenceHighAlphaE
            (rhoF x) ((rhoF x).marginalA.prod sigmaB).matrix
            ((rhoF x).marginalA.prod sigmaB).pos alpha)
        l
        (nhds
          (sandwichedRenyiPSDReferenceHighAlphaE
            rho (rho.marginalA.prod sigmaB).matrix
            (rho.marginalA.prod sigmaB).pos alpha)) :=
    sandwichedRenyiPSDReferenceHighAlphaE_tendsto_of_tendsto_posDef_state_reference
      hrhoF href_tend href_pd (State.prod_posDef hrhoA hsigmaB) halpha
  have htarget :
      rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        sandwichedRenyiPSDReferenceHighAlphaE
          rho (rho.marginalA.prod sigmaB).matrix
          (rho.marginalA.prod sigmaB).pos alpha := by
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
  have hcongr :
      (fun x : X => (rhoF x).sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
        =ᶠ[l]
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaE
          (rhoF x) ((rhoF x).marginalA.prod sigmaB).matrix
          ((rhoF x).marginalA.prod sigmaB).pos alpha) := by
    filter_upwards with x
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
  simpa [htarget] using hhigh.congr' hcongr.symm

/-- Full-rank fixed-side candidates are continuous at states whose left
marginal is full-rank. -/
theorem sandwichedRenyiMutualInformationCandidateE_continuousAt_of_posDef
    (rho : State (Prod a b)) (hrhoA : rho.marginalA.matrix.PosDef)
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    ContinuousAt
      (fun rho' : State (Prod a b) =>
        rho'.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      rho := by
  exact sandwichedRenyiMutualInformationCandidateE_tendsto_of_tendsto_posDef
    (rhoF := fun rho' : State (Prod a b) => rho')
    (rho := rho) tendsto_id hrhoA sigmaB hsigmaB halpha

/-- Full-rank fixed-side candidates are upper semicontinuous on the locus where
the left marginal is full-rank. -/
theorem sandwichedRenyiMutualInformationCandidateE_upperSemicontinuousOn_posDefMarginalA
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) =>
        rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      {rho : State (Prod a b) | rho.marginalA.matrix.PosDef} := by
  intro rho hrho
  exact (sandwichedRenyiMutualInformationCandidateE_continuousAt_of_posDef
    rho hrho sigmaB hsigmaB halpha).continuousWithinAt.upperSemicontinuousWithinAt

/-- The unrestricted side-state infimum is bounded above by the infimum
restricted to full-rank side states. -/
theorem sandwichedRenyiMutualInformationE_le_iInf_posDef_candidates
    (rhoAB : State (Prod a b)) (alpha : Real) :
    rhoAB.sandwichedRenyiMutualInformationE alpha ≤
      ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha := by
  refine le_iInf fun sigmaB => ?_
  exact rhoAB.sandwichedRenyiMutualInformationE_le_candidate sigmaB.1 alpha

/-- A pointwise approximation lower bound against every side state gives the
reverse inequality needed to restrict the optimized infimum to full-rank side
states. -/
theorem iInf_posDef_candidates_le_sandwichedRenyiMutualInformationE_of_le_candidate
    (rhoAB : State (Prod a b)) (alpha : Real)
    (happrox :
      ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha) :
    (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
        rhoAB.sandwichedRenyiMutualInformationE alpha := by
  haveI : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
  refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  intro y hy
  rcases hy with ⟨sigmaB, rfl⟩
  exact happrox sigmaB

/-- The full-rank side-state restriction is equivalent to the original
optimized infimum once every side state is dominated by full-rank
approximants. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
    (rhoAB : State (Prod a b)) (alpha : Real)
    (happrox :
      ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha) :
    rhoAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha := by
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_le_iInf_posDef_candidates rhoAB alpha)
    (iInf_posDef_candidates_le_sandwichedRenyiMutualInformationE_of_le_candidate
      rhoAB alpha happrox)

/-- State optimized monotonicity from the full-rank side-state approximation
lower bound and monotonicity of all full-rank fixed candidates. -/
theorem sandwichedRenyiMutualInformationE_mono_of_posDef_candidate_approx_and_candidate_mono
    (rhoAB : State (Prod a b))
    (happrox :
      ∀ gamma : {gamma : Real // 1 < gamma}, ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 gamma.1) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1)
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
  refine
    sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_candidate_mono
      rhoAB ?_ hmono
  intro gamma
  exact sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
    rhoAB gamma.1 (happrox gamma)

/-- State optimized monotonicity from the full-rank side-state approximation
lower bound and a derivative-sign proof for all full-rank fixed candidates. -/
theorem sandwichedRenyiMutualInformationE_mono_of_posDef_candidate_approx_and_deriv_nonneg
    (rhoAB : State (Prod a b)) (hrhoA : rhoAB.marginalA.matrix.PosDef)
    (happrox :
      ∀ gamma : {gamma : Real // 1 < gamma}, ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 gamma.1) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1)
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
    sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_deriv_nonneg
      rhoAB hrhoA ?_ hcont hdiff hderiv
  intro gamma
  exact sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
    rhoAB gamma.1 (happrox gamma)

/-- If the side-state infimum has been restricted to full-rank candidates,
full-rank candidate upper semicontinuity gives optimized upper semicontinuity
on any locus with full-rank left marginal. -/
theorem sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
    {s : Set (State (Prod a b))}
    {alpha : Real} (halpha : 1 < alpha)
    (hposA : ∀ rho ∈ s, rho.marginalA.matrix.PosDef)
    (hfullRankInf :
      ∀ rho : State (Prod a b),
        rho.sandwichedRenyiMutualInformationE alpha =
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha)
      s := by
  have hcandidates :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        UpperSemicontinuousOn
          (fun rho : State (Prod a b) =>
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha)
          s := by
    intro sigmaB
    exact
      (sandwichedRenyiMutualInformationCandidateE_upperSemicontinuousOn_posDefMarginalA
        sigmaB.1 sigmaB.2 halpha).mono hposA
  have hiInf :
      UpperSemicontinuousOn
        (fun rho : State (Prod a b) =>
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha)
        s :=
    upperSemicontinuousOn_iInf hcandidates
  have hfun :
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha) =
        (fun rho : State (Prod a b) =>
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha) := by
    funext rho
    exact hfullRankInf rho
  simpa [hfun] using hiInf

/-- Optimized upper semicontinuity from the full-rank approximation lower-bound
form of the side-state restriction. -/
theorem sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_posDef_candidate_approx
    {s : Set (State (Prod a b))}
    {alpha : Real} (halpha : 1 < alpha)
    (hposA : ∀ rho ∈ s, rho.marginalA.matrix.PosDef)
    (happrox :
      ∀ rho : State (Prod a b), ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rho.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha)
      s :=
  sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
    halpha hposA fun rho =>
      sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
        rho alpha (happrox rho)

/-- Affine full-rank approximation matrix for a side state.

The path is `(1 - delta) * sigma + delta * mu`; when `mu` is full-rank and
`delta > 0`, the corresponding normalized state is full-rank. -/
def fullRankApproxMatrix (sigma mu : State a) (delta : Real) : CMatrix a :=
  regularizedStateMatrix sigma mu delta

/-- Affine full-rank approximation state for a side state. -/
def fullRankApproxState (sigma mu : State a) (delta : Real)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) : State a :=
  regularizedWithState sigma mu delta hdelta0 hdelta1

@[simp]
theorem fullRankApproxState_matrix (sigma mu : State a) (delta : Real)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (fullRankApproxState sigma mu delta hdelta0 hdelta1).matrix =
      fullRankApproxMatrix sigma mu delta := by
  rfl

/-- Positive regularization by a full-rank noise state is full-rank. -/
theorem fullRankApproxState_posDef_of_noise
    (sigma mu : State a) (hmu : mu.matrix.PosDef) {delta : Real}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hdelta_pos : 0 < delta) :
    (fullRankApproxState sigma mu delta hdelta0 hdelta1).matrix.PosDef := by
  exact regularizedWithState_posDef_of_noise sigma mu hmu hdelta0 hdelta1 hdelta_pos

/-- The full-rank approximation matrix path converges back to the side state. -/
theorem fullRankApproxMatrix_tendsto_zero (sigma mu : State a) :
    Tendsto (fun delta : Real => fullRankApproxMatrix sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma.matrix) := by
  simpa [fullRankApproxMatrix] using regularizedStateMatrix_tendsto_zero sigma mu

/-- Total full-rank approximation path, filled in by the limiting state outside
the probability interval. -/
def fullRankApproxStatePath (sigma mu : State a) (delta : Real) : State a :=
  if hdelta : delta ∈ Set.Ioo (0 : Real) 1 then
    fullRankApproxState sigma mu delta hdelta.1.le hdelta.2.le
  else
    sigma

theorem fullRankApproxStatePath_eq_of_mem
    (sigma mu : State a) {delta : Real} (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    fullRankApproxStatePath sigma mu delta =
      fullRankApproxState sigma mu delta hdelta.1.le hdelta.2.le := by
  rw [fullRankApproxStatePath, dif_pos hdelta]

/-- The full-rank approximation path converges back to the side state. -/
theorem fullRankApproxStatePath_tendsto_zero (sigma mu : State a) :
    Tendsto (fun delta : Real => fullRankApproxStatePath sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  refine Tendsto.congr' ?_ (fullRankApproxMatrix_tendsto_zero sigma mu)
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  change fullRankApproxMatrix sigma mu delta =
    (fullRankApproxStatePath sigma mu delta).matrix
  rw [fullRankApproxStatePath, dif_pos hdelta]
  rfl

/-- The side-state approximation is eventually full-rank when the noise is
full-rank. -/
theorem fullRankApproxStatePath_eventually_posDef_of_noise
    (sigma mu : State a) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxStatePath sigma mu delta).matrix.PosDef := by
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  rw [fullRankApproxStatePath, dif_pos hdelta]
  exact fullRankApproxState_posDef_of_noise
    sigma mu hmu hdelta.1.le hdelta.2.le hdelta.1

/-- A full-rank approximation reference eventually supports every fixed input
matrix. -/
theorem fullRankApproxStatePath_eventually_supports_of_noise
    (rho : State a) (sigma mu : State a) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rho.matrix (fullRankApproxStatePath sigma mu delta).matrix := by
  filter_upwards [fullRankApproxStatePath_eventually_posDef_of_noise sigma mu hmu]
    with delta hdelta
  exact Matrix.Supports.of_right_posDef rho.matrix
    (fullRankApproxStatePath sigma mu delta).matrix hdelta

/-- Canonical full-rank approximation path using the maximally mixed state as
noise. -/
def fullRankApproxMaximallyMixedStatePath (sigma : State a) (delta : Real) : State a :=
  letI : Nonempty a := sigma.nonempty
  fullRankApproxStatePath sigma (maximallyMixed a) delta

/-- The canonical full-rank approximation path converges back to the target
state. -/
theorem fullRankApproxMaximallyMixedStatePath_tendsto_zero (sigma : State a) :
    Tendsto (fun delta : Real => fullRankApproxMaximallyMixedStatePath sigma delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma) := by
  classical
  letI : Nonempty a := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedStatePath] using
    fullRankApproxStatePath_tendsto_zero sigma (maximallyMixed a)

/-- The canonical full-rank approximation path is eventually full-rank. -/
theorem fullRankApproxMaximallyMixedStatePath_eventually_posDef (sigma : State a) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxMaximallyMixedStatePath sigma delta).matrix.PosDef := by
  classical
  letI : Nonempty a := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedStatePath] using
    fullRankApproxStatePath_eventually_posDef_of_noise
      sigma (maximallyMixed a) (maximallyMixed_posDef (a := a))

/-- The canonical full-rank approximation path eventually supports every fixed
input matrix. -/
theorem fullRankApproxMaximallyMixedStatePath_eventually_supports
    (rho sigma : State a) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rho.matrix (fullRankApproxMaximallyMixedStatePath sigma delta).matrix := by
  classical
  letI : Nonempty a := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedStatePath] using
    fullRankApproxStatePath_eventually_supports_of_noise
      rho sigma (maximallyMixed a) (maximallyMixed_posDef (a := a))

/-- If the fixed left reference is full-rank, the product with the full-rank
side-state approximation is full-rank. -/
theorem prod_fullRankApproxState_posDef_of_left
    (rhoA : State a) (sigma mu : State b)
    (hrhoA : rhoA.matrix.PosDef) (hmu : mu.matrix.PosDef) {delta : Real}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hdelta_pos : 0 < delta) :
    (rhoA.prod (fullRankApproxState sigma mu delta hdelta0 hdelta1)).matrix.PosDef := by
  exact State.prod_posDef hrhoA
    (fullRankApproxState_posDef_of_noise sigma mu hmu hdelta0 hdelta1 hdelta_pos)

/-- Product reference path obtained by regularizing only the side state. -/
def fullRankApproxProductReferencePath
    (rhoA : State a) (sigma mu : State b) (delta : Real) : State (Prod a b) :=
  rhoA.prod (fullRankApproxStatePath sigma mu delta)

/-- Matrix convergence of the product reference path with a fixed left state. -/
theorem fullRankApproxProductReferencePath_matrix_tendsto_zero
    (rhoA : State a) (sigma mu : State b) :
    Tendsto
      (fun delta : Real =>
        (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhds (rhoA.prod sigma).matrix) := by
  have hside :
      Tendsto (fun delta : Real => (fullRankApproxStatePath sigma mu delta).matrix)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp
      (fullRankApproxStatePath_tendsto_zero sigma mu)
  have hkr :
      Continuous fun M : CMatrix b => Matrix.kronecker rhoA.matrix M := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  simpa [fullRankApproxProductReferencePath, State.prod] using
    hkr.tendsto sigma.matrix |>.comp hside

/-- State-level convergence of the product reference path with a fixed left
state. -/
theorem fullRankApproxProductReferencePath_tendsto_zero
    (rhoA : State a) (sigma mu : State b) :
    Tendsto (fun delta : Real => fullRankApproxProductReferencePath rhoA sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (rhoA.prod sigma)) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  exact fullRankApproxProductReferencePath_matrix_tendsto_zero rhoA sigma mu

/-- The product reference path with fixed full-rank left state is eventually
full-rank. -/
theorem fullRankApproxProductReferencePath_eventually_posDef_of_left
    (rhoA : State a) (sigma mu : State b)
    (hrhoA : rhoA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix.PosDef := by
  filter_upwards [fullRankApproxStatePath_eventually_posDef_of_noise sigma mu hmu] with delta hdelta
  simpa [fullRankApproxProductReferencePath] using State.prod_posDef hrhoA hdelta

/-- A fixed-left product reference path eventually supports every fixed input
matrix when both product factors are full-rank along the path. -/
theorem fullRankApproxProductReferencePath_eventually_supports_of_left
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma mu : State b)
    (hrhoA : rhoA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rhoAB.matrix
        (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix := by
  filter_upwards [
      fullRankApproxProductReferencePath_eventually_posDef_of_left
        rhoA sigma mu hrhoA hmu] with delta hdelta
  exact Matrix.Supports.of_right_posDef rhoAB.matrix
    (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix hdelta

/-- Product reference path obtained by regularizing both marginal reference
states. -/
def fullRankApproxProductReferenceBothPath
    (rhoA muA : State a) (sigma mu : State b) (delta : Real) : State (Prod a b) :=
  (fullRankApproxStatePath rhoA muA delta).prod
    (fullRankApproxStatePath sigma mu delta)

/-- Matrix convergence of the product reference path when both sides are
regularized. -/
theorem fullRankApproxProductReferenceBothPath_matrix_tendsto_zero
    (rhoA muA : State a) (sigma mu : State b) :
    Tendsto
      (fun delta : Real =>
        (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhds (rhoA.prod sigma).matrix) := by
  have hleft :
      Tendsto (fun delta : Real => (fullRankApproxStatePath rhoA muA delta).matrix)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds rhoA.matrix) :=
    State.continuous_matrix.tendsto rhoA |>.comp
      (fullRankApproxStatePath_tendsto_zero rhoA muA)
  have hright :
      Tendsto (fun delta : Real => (fullRankApproxStatePath sigma mu delta).matrix)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp
      (fullRankApproxStatePath_tendsto_zero sigma mu)
  have hpair :
      Tendsto
        (fun delta : Real =>
          ((fullRankApproxStatePath rhoA muA delta).matrix,
            (fullRankApproxStatePath sigma mu delta).matrix))
        (nhdsWithin (0 : Real) (Set.Ioo 0 1))
        (nhds (rhoA.matrix, sigma.matrix)) :=
    hleft.prodMk_nhds hright
  have hkr :
      Continuous fun M : CMatrix a × CMatrix b => Matrix.kronecker M.1 M.2 := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        (continuous_fst.matrix_elem x.1 y.1).mul
          (continuous_snd.matrix_elem x.2 y.2)
  simpa [fullRankApproxProductReferenceBothPath, State.prod] using
    hkr.tendsto (rhoA.matrix, sigma.matrix) |>.comp hpair

/-- State-level convergence of the product reference path when both sides are
regularized. -/
theorem fullRankApproxProductReferenceBothPath_tendsto_zero
    (rhoA muA : State a) (sigma mu : State b) :
    Tendsto (fun delta : Real => fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (rhoA.prod sigma)) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  exact fullRankApproxProductReferenceBothPath_matrix_tendsto_zero rhoA muA sigma mu

/-- Regularizing both marginal reference states by full-rank noise makes the
product reference path eventually full-rank. -/
theorem fullRankApproxProductReferenceBothPath_eventually_posDef_of_noise
    (rhoA muA : State a) (sigma mu : State b)
    (hmuA : muA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix.PosDef := by
  filter_upwards [
      fullRankApproxStatePath_eventually_posDef_of_noise rhoA muA hmuA,
      fullRankApproxStatePath_eventually_posDef_of_noise sigma mu hmu] with delta hleft hright
  simpa [fullRankApproxProductReferenceBothPath] using State.prod_posDef hleft hright

/-- A product reference path regularized on both factors eventually supports
every fixed input matrix. -/
theorem fullRankApproxProductReferenceBothPath_eventually_supports_of_noise
    (rhoAB : State (Prod a b)) (rhoA muA : State a) (sigma mu : State b)
    (hmuA : muA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rhoAB.matrix
        (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix := by
  filter_upwards [
      fullRankApproxProductReferenceBothPath_eventually_posDef_of_noise
        rhoA muA sigma mu hmuA hmu] with delta hdelta
  exact Matrix.Supports.of_right_posDef rhoAB.matrix
    (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix hdelta

/-- Canonical product reference path obtained by regularizing both factors
with maximally mixed noise. -/
def fullRankApproxMaximallyMixedProductReferenceBothPath
    (rhoA : State a) (sigma : State b) (delta : Real) : State (Prod a b) :=
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  fullRankApproxProductReferenceBothPath rhoA (maximallyMixed a) sigma (maximallyMixed b) delta

/-- The canonical product reference path converges back to the target product
state. -/
theorem fullRankApproxMaximallyMixedProductReferenceBothPath_tendsto_zero
    (rhoA : State a) (sigma : State b) :
    Tendsto
      (fun delta : Real =>
        fullRankApproxMaximallyMixedProductReferenceBothPath rhoA sigma delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (rhoA.prod sigma)) := by
  classical
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedProductReferenceBothPath] using
    fullRankApproxProductReferenceBothPath_tendsto_zero
      rhoA (maximallyMixed a) sigma (maximallyMixed b)

/-- The canonical product reference path is eventually full-rank. -/
theorem fullRankApproxMaximallyMixedProductReferenceBothPath_eventually_posDef
    (rhoA : State a) (sigma : State b) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxMaximallyMixedProductReferenceBothPath rhoA sigma delta).matrix.PosDef := by
  classical
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedProductReferenceBothPath] using
    fullRankApproxProductReferenceBothPath_eventually_posDef_of_noise
      rhoA (maximallyMixed a) sigma (maximallyMixed b)
      (maximallyMixed_posDef (a := a)) (maximallyMixed_posDef (a := b))

/-- The canonical product reference path eventually supports every fixed input
state. -/
theorem fullRankApproxMaximallyMixedProductReferenceBothPath_eventually_supports
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rhoAB.matrix
        (fullRankApproxMaximallyMixedProductReferenceBothPath rhoA sigma delta).matrix := by
  classical
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedProductReferenceBothPath] using
    fullRankApproxProductReferenceBothPath_eventually_supports_of_noise
      rhoAB rhoA (maximallyMixed a) sigma (maximallyMixed b)
      (maximallyMixed_posDef (a := a)) (maximallyMixed_posDef (a := b))

end State

end

end QIT
