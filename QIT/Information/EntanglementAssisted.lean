/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Holevo
public import QIT.Core.Channel
public import QIT.Core.POVMProbability
public import QIT.Core.Pure
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entanglement-assisted classical capacity API

This module records the finite-dimensional API for entanglement-assisted
classical communication.  It defines the channel mutual-information objective
`I(N)` from the BSST theorem and an operational entanglement-assisted code
surface.

The full BSST equality `C_E(N) = I(N)`, its converse, and the final
capacity-supremum squeeze are separate proof obligations.  This file uses a
supremum-style definition for `I(N)` and proves separately that this finite
pure-state supremum is attained on nonempty input systems.

Source alignment:
* [Wilde2011Qst, qit-notes.tex:35326-35342] states the BSST formula
  `C_E(N) = I(N)` and defines `I(N)` as a maximum over pure input-reference
  states.
* [Wilde2011Qst, qit-notes.tex:35345-35361] states the direct coding resource
  inequality for a fixed pure input-reference state.
* [Wilde2011Qst, qit-notes.tex:35474-35520] describes entanglement-assisted
  message encoding and channel-output codewords.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

noncomputable local instance matrixCStarAlgebra {n : Type u} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where

noncomputable local instance matrixNormalCFC {n : Type u} [Fintype n] [DecidableEq n] :
    ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance matrixNormalIsometricCFC {n : Type u} [Fintype n] [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instIsometricContinuousFunctionalCalculus

/-- States carry the topology induced by their density matrices. -/
instance State.instTopologicalSpace {a : Type u} [Fintype a] [DecidableEq a] :
    TopologicalSpace (State a) :=
  TopologicalSpace.induced State.matrix inferInstance

/-- Pure vectors carry the topology induced by their amplitudes. -/
instance PureVector.instTopologicalSpace {a : Type u} [Fintype a] [DecidableEq a] :
    TopologicalSpace (PureVector a) :=
  TopologicalSpace.induced PureVector.amp inferInstance

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

@[fun_prop]
theorem continuous_matrix : Continuous (fun ρ : State a => ρ.matrix) :=
  continuous_induced_dom

private noncomputable def entropyCfcScalar (x : ℝ) : ℝ :=
  -(x * Real.log x / Real.log 2)

private noncomputable def entropyCfcComplex (z : ℂ) : ℂ :=
  (entropyCfcScalar z.re : ℂ)

private theorem entropyCfcScalar_eq_neg_xlog2 (x : ℝ) :
    entropyCfcScalar x = -xlog2 x := by
  unfold entropyCfcScalar xlog2 log2
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]
    ring

private theorem continuous_entropyCfcScalar : Continuous entropyCfcScalar := by
  unfold entropyCfcScalar
  exact (Real.continuous_mul_log.div_const _).neg

private theorem continuous_entropyCfcComplex : Continuous entropyCfcComplex := by
  unfold entropyCfcComplex
  exact Complex.continuous_ofReal.comp (continuous_entropyCfcScalar.comp Complex.continuous_re)

private theorem vonNeumann_eq_cfc_trace (ρ : State a) :
    ρ.vonNeumann = ((cfc entropyCfcComplex ρ.matrix).trace).re := by
  rw [State.vonNeumann]
  have hreal :
      cfc entropyCfcScalar ρ.matrix = cfc entropyCfcComplex ρ.matrix := by
    simpa [entropyCfcComplex] using
      (cfc_real_eq_complex (a := ρ.matrix) entropyCfcScalar
        (ha := ρ.pos.isHermitian.isSelfAdjoint))
  rw [← hreal]
  have hcfc :
      cfc entropyCfcScalar ρ.matrix =
        ρ.pos.isHermitian.cfc entropyCfcScalar :=
    Matrix.IsHermitian.cfc_eq (𝕜 := ℂ) ρ.pos.isHermitian entropyCfcScalar
  rw [hcfc]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  rw [Matrix.trace_diagonal]
  simp only [Function.comp_apply, entropyCfcScalar_eq_neg_xlog2]
  simp [Finset.sum_neg_distrib]

/-- Eigenvalues of a state sum to one. -/
private lemma eigenvalue_sum (ρ : State a) :
    ∑ i, ρ.pos.isHermitian.eigenvalues i = 1 := by
  have hc : (∑ i, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 := by
    exact ρ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
  exact Complex.ofReal_injective (by simpa using hc)

/-- Eigenvalues of a state are bounded above by one. -/
private lemma eigenvalue_le_one (ρ : State a) (i : a) :
    ρ.pos.isHermitian.eigenvalues i ≤ 1 := by
  have hnonneg (j : a) : 0 ≤ ρ.pos.isHermitian.eigenvalues j :=
    ρ.pos.eigenvalues_nonneg j
  have hsum : ∑ j, ρ.pos.isHermitian.eigenvalues j = 1 :=
    eigenvalue_sum ρ
  calc ρ.pos.isHermitian.eigenvalues i
      ≤ ρ.pos.isHermitian.eigenvalues i
        + ∑ j ∈ Finset.univ.erase i, ρ.pos.isHermitian.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
    _ = ∑ j, ρ.pos.isHermitian.eigenvalues j :=
          by
            rw [add_comm]
            exact Finset.sum_erase_add (s := Finset.univ)
              (f := fun j => ρ.pos.isHermitian.eigenvalues j) (Finset.mem_univ i)
    _ = 1 := hsum

private theorem spectrum_subset_stateInterval (ρ : State a) :
    spectrum ℂ ρ.matrix ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  intro z hz
  rw [ρ.pos.isHermitian.spectrum_eq_image_range] at hz
  rcases hz with ⟨x, ⟨i, rfl⟩, rfl⟩
  exact ⟨ρ.pos.isHermitian.eigenvalues i,
    ⟨ρ.pos.eigenvalues_nonneg i, eigenvalue_le_one ρ i⟩, rfl⟩

/-- Von Neumann entropy is continuous on finite-dimensional density states. -/
theorem vonNeumann_continuous : Continuous (fun ρ : State a => ρ.vonNeumann) := by
  let K : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    CompactIccSpace.isCompact_Icc.image Complex.continuous_ofReal
  have hcfc : Continuous fun ρ : State a =>
      (cfc entropyCfcComplex (ρ.matrix : Matrix a a ℂ) : Matrix a a ℂ) := by
    exact Continuous.cfc' (A := Matrix a a ℂ) (p := IsStarNormal)
      (s := K) hK entropyCfcComplex State.continuous_matrix
      (fun ρ => spectrum_subset_stateInterval ρ)
      (continuous_entropyCfcComplex.continuousOn)
      (fun ρ => ρ.pos.isHermitian.isSelfAdjoint.isStarNormal)
  have htrace : Continuous fun ρ : State a =>
      ((cfc entropyCfcComplex ρ.matrix).trace).re :=
    Complex.continuous_re.comp (Continuous.matrix_trace hcfc)
  exact htrace.congr fun ρ => (vonNeumann_eq_cfc_trace ρ).symm

theorem marginalA_continuous {b : Type v} [Fintype b] [DecidableEq b] :
    Continuous (fun ρ : State (Prod a b) => ρ.marginalA) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State (Prod a b) =>
    partialTraceB (a := a) (b := b) ρ.matrix
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro i'
  simp only [partialTraceB]
  refine continuous_finsetSum Finset.univ ?_
  intro j _
  exact (continuous_apply (i', j)).comp
    ((continuous_apply (i, j)).comp State.continuous_matrix)

theorem marginalB_continuous {b : Type v} [Fintype b] [DecidableEq b] :
    Continuous (fun ρ : State (Prod a b) => ρ.marginalB) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State (Prod a b) =>
    partialTraceA (a := a) (b := b) ρ.matrix
  refine continuous_pi ?_
  intro j
  refine continuous_pi ?_
  intro j'
  simp only [partialTraceA]
  refine continuous_finsetSum Finset.univ ?_
  intro i _
  exact (continuous_apply (i, j')).comp
    ((continuous_apply (i, j)).comp State.continuous_matrix)

end State

namespace PureVector

variable {a : Type u} [Fintype a] [DecidableEq a]

@[fun_prop]
theorem continuous_amp : Continuous (fun ψ : PureVector a => ψ.amp) :=
  continuous_induced_dom

omit [Fintype a] [DecidableEq a] in
theorem rankOneMatrix_continuous : Continuous (fun ψ : a → ℂ => rankOneMatrix ψ) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp only [rankOneMatrix_apply]
  exact (continuous_apply i).mul (continuous_star.comp (continuous_apply j))

theorem state_continuous : Continuous (fun ψ : PureVector a => ψ.state) := by
  rw [continuous_induced_rng]
  change Continuous fun ψ : PureVector a => rankOneMatrix ψ.amp
  exact rankOneMatrix_continuous.comp PureVector.continuous_amp

/-- The amplitude vectors underlying normalized pure vectors. -/
private def normalizedAmplitudeSet (a : Type u) [Fintype a] : Set (a → ℂ) :=
  {ψ | (rankOneMatrix ψ).trace = 1}

omit [DecidableEq a] in
private theorem trace_eq_sum_norm_sq {ψ : a → ℂ}
    (hψ : (rankOneMatrix ψ).trace = 1) :
    ∑ i, ‖ψ i‖ ^ 2 = (1 : ℝ) := by
  have hre := congrArg Complex.re hψ
  rw [rankOneMatrix_trace] at hre
  simp [dotProduct] at hre
  calc
    ∑ i, ‖ψ i‖ ^ 2 =
        ∑ i, ((ψ i).re * (ψ i).re + (ψ i).im * (ψ i).im) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Complex.sq_norm, Complex.normSq_apply]
    _ = 1 := hre

omit [DecidableEq a] in
private theorem norm_le_one_of_mem_normalizedAmplitudeSet
    {ψ : a → ℂ} (hψ : ψ ∈ normalizedAmplitudeSet a) (i : a) :
    ‖ψ i‖ ≤ 1 := by
  have hsum : ∑ j, ‖ψ j‖ ^ 2 = (1 : ℝ) :=
    trace_eq_sum_norm_sq hψ
  have hsingle : ‖ψ i‖ ^ 2 ≤ ∑ j, ‖ψ j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (‖ψ j‖)) (Finset.mem_univ i)
  have hsquare : ‖ψ i‖ ^ 2 ≤ 1 := by simpa [hsum] using hsingle
  exact (sq_le_one_iff₀ (norm_nonneg (ψ i))).mp hsquare

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isClosed :
    IsClosed (normalizedAmplitudeSet a) := by
  unfold normalizedAmplitudeSet
  exact isClosed_eq (Continuous.matrix_trace rankOneMatrix_continuous) continuous_const

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isBounded :
    Bornology.IsBounded (normalizedAmplitudeSet a) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : a → ℂ)]
  refine ⟨1, ?_⟩
  intro ψ hψ
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  exact norm_le_one_of_mem_normalizedAmplitudeSet hψ i

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isCompact :
    IsCompact (normalizedAmplitudeSet a) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨normalizedAmplitudeSet_isClosed, normalizedAmplitudeSet_isBounded⟩

private def ampSubtypeEquiv :
    PureVector a ≃ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toFun ψ := ⟨ψ.amp, ψ.trace_rankOne_eq_one⟩
  invFun ψ := ⟨ψ.1, ψ.2⟩
  left_inv ψ := by
    cases ψ
    rfl
  right_inv ψ := by
    cases ψ
    rfl

private noncomputable def ampSubtypeHomeomorph :
    PureVector a ≃ₜ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toEquiv := ampSubtypeEquiv
  continuous_toFun := PureVector.continuous_amp.subtype_mk fun ψ => ψ.trace_rankOne_eq_one
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous fun ψ : {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} => ψ.1
    exact continuous_subtype_val

instance instCompactSpace : CompactSpace (PureVector a) := by
  haveI : CompactSpace {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} :=
    isCompact_iff_compactSpace.mp normalizedAmplitudeSet_isCompact
  exact ampSubtypeHomeomorph.symm.compactSpace

/-- A canonical basis pure vector on a nonempty finite system. -/
def basisPureVector [Nonempty a] : PureVector a where
  amp := fun i => if i = Classical.choice (inferInstance : Nonempty a) then 1 else 0
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace, dotProduct]
    simp

end PureVector

theorem mutualInformation_continuous :
    Continuous (fun ρ : State (Prod a b) => mutualInformation ρ) := by
  unfold mutualInformation
  exact ((State.vonNeumann_continuous.comp State.marginalA_continuous).add
    (State.vonNeumann_continuous.comp State.marginalB_continuous)).sub
    State.vonNeumann_continuous

namespace Channel

variable (N : Channel a b)

theorem applyState_continuous : Continuous (fun ρ : State a => N.applyState ρ) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State a => N.map ρ.matrix
  exact (LinearMap.continuous_of_finiteDimensional N.map).comp State.continuous_matrix

/-- Output state `(id_R ⊗ N)(|ψ⟩⟨ψ|)` for a pure input-reference state. -/
def entanglementAssistedOutputState {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) : State (Prod r b) :=
  ((Channel.idChannel r).prod N).applyState ψ.state

theorem entanglementAssistedOutputState_continuous {r : Type w} [Fintype r] [DecidableEq r] :
    Continuous (fun ψ : PureVector (Prod r a) => N.entanglementAssistedOutputState ψ) :=
  (((Channel.idChannel r).prod N).applyState_continuous).comp PureVector.state_continuous

/-- Mutual information of the entanglement-assisted channel output state. -/
def entanglementAssistedMutualInformation {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) : ℝ :=
  mutualInformation (N.entanglementAssistedOutputState ψ)

theorem entanglementAssistedMutualInformation_continuous
    {r : Type w} [Fintype r] [DecidableEq r] :
    Continuous (fun ψ : PureVector (Prod r a) =>
      N.entanglementAssistedMutualInformation ψ) :=
  mutualInformation_continuous.comp N.entanglementAssistedOutputState_continuous

/-- Single-letter entanglement-assisted channel information `I(N)`.

The source states `I(N)` as a maximum over pure `A A'` inputs.  The Lean API
uses `sSup` over pure states on a reference copy of the input system; the
separate compactness/maximizer proof for the attained `max` is tracked
downstream. -/
def entanglementAssistedInformation : ℝ :=
  sSup (Set.range fun ψ : PureVector (Prod a a) =>
    N.entanglementAssistedMutualInformation ψ)

/-- The supremum in `Channel.entanglementAssistedInformation` is attained on a
pure input-reference state for nonempty finite input systems. -/
theorem exists_entanglementAssistedInformation_maximizer [Nonempty a] :
    ∃ ψ : PureVector (Prod a a),
      N.entanglementAssistedInformation =
        N.entanglementAssistedMutualInformation ψ := by
  let f : PureVector (Prod a a) → ℝ :=
    fun ψ => N.entanglementAssistedMutualInformation ψ
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hne : (Set.univ : Set (PureVector (Prod a a))).Nonempty :=
    Set.univ_nonempty
  obtain ⟨ψ, _hψmem, hψmax⟩ :=
    isCompact_univ.exists_isMaxOn hne
      (N.entanglementAssistedMutualInformation_continuous (r := a)).continuousOn
  refine ⟨ψ, ?_⟩
  change sSup (Set.range f) = f ψ
  refine le_antisymm ?_ ?_
  · exact csSup_le (Set.range_nonempty f) fun y hy => by
      rcases hy with ⟨φ, rfl⟩
      exact hψmax trivial
  · exact le_csSup (by
      refine ⟨f ψ, ?_⟩
      intro y hy
      rcases hy with ⟨φ, rfl⟩
      exact hψmax trivial) ⟨ψ, rfl⟩

end Channel

/-- Register rate for an entanglement-assisted classical message code. -/
def entanglementAssistedMessageRate (M : Type w) [Fintype M] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card M : ℝ) / (n : ℝ)

/-- A finite entanglement-assisted classical communication code for `n` uses
of channel `N`.

Alice and Bob share a finite state on `EA × EB`.  For each message, Alice
applies an encoder channel to her share `EA` to prepare the channel input
`A^n`; Bob decodes from the channel output `B^n` together with his retained
share `EB`. -/
structure EntanglementAssistedClassicalCode (N : Channel a b) (n : ℕ)
    (M : Type w) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type x) [Fintype EA] [DecidableEq EA]
    (EB : Type y) [Fintype EB] [DecidableEq EB] where
  sharedState : State (Prod EA EB)
  encoder : M → Channel EA (TensorPower a n)
  decoder : POVM M (Prod (TensorPower b n) EB)

namespace EntanglementAssistedClassicalCode

variable {N : Channel a b} {n : ℕ}
variable {M : Type w} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Joint channel-input and Bob-side state after Alice encodes a message. -/
def channelInputState (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : State (Prod (TensorPower a n) EB) :=
  ((C.encoder m).prod (Channel.idChannel EB)).applyState C.sharedState

/-- Bob's received state after the `n` channel uses and before decoding. -/
def outputState (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : State (Prod (TensorPower b n) EB) :=
  ((N.tensorPower n).prod (Channel.idChannel EB)).applyState
    (C.channelInputState m)

/-- Born-rule probability that Bob decodes the transmitted message. -/
def successProbability (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : ℝ :=
  (C.decoder.prob (C.outputState m) m : ℝ)

/-- Message-wise error probability. -/
def error (C : EntanglementAssistedClassicalCode N n M EA EB) (m : M) : ℝ :=
  1 - C.successProbability m

/-- Maximal message error bounded by `ε`. -/
def maxErrorAtMost (C : EntanglementAssistedClassicalCode N n M EA EB)
    (ε : ℝ) : Prop :=
  ∀ m : M, C.error m ≤ ε

/-- Classical communication rate of the message set. -/
def rate (_C : EntanglementAssistedClassicalCode N n M EA EB) : ℝ :=
  entanglementAssistedMessageRate M n

end EntanglementAssistedClassicalCode

namespace Channel

variable (N : Channel a b)

/-- Operational achievability of an entanglement-assisted classical rate. -/
def IsAchievableEntanglementAssistedClassicalRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N n M EA EB,
            C.rate ≥ R - δ ∧ C.maxErrorAtMost ε

/-- `B` is an upper bound on every achievable entanglement-assisted classical
rate for channel `N`. -/
def IsEntanglementAssistedClassicalRateUpperBound (B : ℝ) : Prop :=
  ∀ R : ℝ, N.IsAchievableEntanglementAssistedClassicalRate R → R ≤ B

/-- Operational entanglement-assisted classical capacity as the supremum of
achievable rates.  The BSST theorem later identifies this quantity with
`N.entanglementAssistedInformation`. -/
def entanglementAssistedClassicalCapacity : ℝ :=
  sSup {R : ℝ | N.IsAchievableEntanglementAssistedClassicalRate R}

end Channel

/-- Source-shaped witness for one block of the entanglement-assisted direct
coding route for a fixed pure input-reference state.

The witness packages an already-constructed code and the estimates expected
from the BSST direct proof: rate at least the output mutual information minus
`δ`, and maximal decoding error at most `ε`.  This structure is an API for
later proof leaves; this module does not prove the direct coding theorem. -/
structure EntanglementAssistedDirectCodingWitness {r : Type u}
    [Fintype r] [DecidableEq r] (N : Channel a b)
    (ψ : PureVector (Prod r a)) (n : ℕ) (δ ε : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type u) [Fintype EA] [DecidableEq EA]
    (EB : Type u) [Fintype EB] [DecidableEq EB] where
  code : EntanglementAssistedClassicalCode N n M EA EB
  rate_ge : code.rate ≥ N.entanglementAssistedMutualInformation ψ - δ
  maxError_le : code.maxErrorAtMost ε

/-- Source-shaped family of converse estimates for entanglement-assisted
classical communication.

For every rate slack `η > 0` and reliability threshold `ε > 0`, all
sufficiently long reliable EA codes have rate at most
`N.entanglementAssistedInformation + η`.  In the source proof, this estimate is
where the Fano/continuity, quantum data-processing, mutual-information chain
rule, and additivity arguments enter; this structure keeps those estimates
explicit for the converse assembly theorem below. -/
structure EntanglementAssistedConverseWitnessFamily (N : Channel a b) where
  rate_le :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  C.rate ≤ N.entanglementAssistedInformation + η

namespace Channel

variable (N : Channel a b)

/-- Entanglement-assisted direct achievability from a family of BSST
direct-coding witnesses.

This is the direct-coding side of the BSST route currently formalized in
Lean.  The random-unitary code construction, packing/typicality estimates,
converse, compactness/maximizer theorem, and final capacity equality are
separate proof obligations. -/
theorem entanglementAssisted_direct_achievable_of_directCodingWitness
    {r : Type u} [Fintype r] [DecidableEq r] (ψ : PureVector (Prod r a))
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
            ∃ (_ : Nonempty M),
              ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
                ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                  Nonempty (EntanglementAssistedDirectCodingWitness N ψ n δ ε M EA EB)) :
    N.IsAchievableEntanglementAssistedClassicalRate
      (N.entanglementAssistedMutualInformation ψ) := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, ⟨witness⟩⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    witness.code, witness.rate_ge, witness.maxError_le⟩

/-- Entanglement-assisted converse upper bound from source-shaped converse
estimates.

This theorem is the Lean assembly of the BSST converse route: once the
Fano/continuity, data-processing, mutual-information chain-rule, and additivity
estimates are supplied as an `EntanglementAssistedConverseWitnessFamily`, the
single-letter information quantity `I(N)` upper-bounds every achievable
entanglement-assisted classical rate. -/
theorem entanglementAssisted_information_isUpperBound_of_converseWitness
    (hconv : EntanglementAssistedConverseWitnessFamily N) :
    N.IsEntanglementAssistedClassicalRateUpperBound
      N.entanglementAssistedInformation := by
  intro R hR
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  have hone : 0 < (1 : ℝ) := by norm_num
  obtain ⟨Nach, hNach⟩ := hR (η / 2) hhalf 1 hone
  obtain ⟨Nconv, hNconv⟩ := hconv.rate_le (η / 2) hhalf 1 hone
  let n : ℕ := max Nach Nconv
  have hnAch : n ≥ Nach := Nat.le_max_left Nach Nconv
  have hnConv : n ≥ Nconv := Nat.le_max_right Nach Nconv
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hrate_ge, herror⟩ :=
    hNach n hnAch
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  have hrate_le :
      C.rate ≤ N.entanglementAssistedInformation + η / 2 :=
    hNconv n hnConv M EA EB C herror
  linarith

end Channel

end

end QIT
