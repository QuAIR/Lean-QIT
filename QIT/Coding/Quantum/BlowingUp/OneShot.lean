/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.Stinespring
public import QIT.OneShot.SmoothEndpoint.Companion

/-!
# One-shot witnesses for quantum blowing-up

Explicit one-shot witnesses and the quantum code conversion of
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419].
The one-shot achievability fact enters through an explicit hypothesis.
Conditional entropy uses the reference-first carrier `R × E`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

universe u

variable {a b e : Type u} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

/-- Discard the receiver from a reference-first Stinespring pure vector.
The remaining carrier is `R × E`, so conditional min-entropy conditions on E.
This is the register-reordered state in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:275-287]. -/
def PureVector.referenceEnvironmentState
    {r : Type u} [Fintype r] [DecidableEq r]
    (ψ : PureVector (r × (b × e))) : State (r × e) :=
  (ψ.state.reindex (Equiv.prodAssoc r b e).symm).marginalAC

/-- The one-shot quantum achievability fact, carried as an explicit hypothesis.
The output message type is existential and independent of the input reference.
The strict parameter range includes the erratum in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:275-287]. -/
def Channel.HasOneShotQuantumAchievability
    (N : Channel a b) (V : ReferenceIsometry a (b × e)) : Prop :=
  ∀ (r : Type u) [Fintype r] [DecidableEq r] [Nonempty r],
    ∀ (ξ : PureVector (r × a)) (δ η : ℝ)
      (_hη : 0 < η) (hηδ : η < δ) (_hδ : δ < 1),
    let ρ := (V.applyPureVectorRight ξ).referenceEnvironmentState
    ∃ (m : Type u), ∃ (_ : Fintype m), ∃ (_ : DecidableEq m), ∃ (_ : Nonempty m),
      ∃ C : EntanglementTransmissionCode N m m m,
        1 - δ ^ 2 ≤ C.fidelity ∧
        ρ.smoothConditionalMinEntropy (δ - η)
            (le_of_lt (sub_pos.mpr hηδ))
            (by linarith) -
          4 * log2 (1 / η) - 1 ≤ log2 (Fintype.card m : ℝ)

/-- A weak-converse witness above an explicit rate threshold. At
`q = N.quantumCapacity` this is the external fact in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:598-600].
It is separate from one-shot achievability and is not a premise of blowing-up. -/
def Channel.HasQuantumWeakConverseAt (N : Channel a b) (q : ℝ) : Prop :=
  ∀ r₀ : ℝ, q < r₀ → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ (m : Type u) [Fintype m] [DecidableEq m] [Nonempty m],
      ∀ C : EntanglementTransmissionCode (N.tensorPower n) m m m,
        1 - ε ^ 2 ≤ C.fidelity → log2 (Fintype.card m : ℝ) ≤ (n : ℝ) * r₀

/-- The substitution used to pass from one-shot achievability to blowing-up
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:275-287]. -/
theorem blowingUp_half_error_parameters {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    0 < ε / 2 ∧ ε / 2 < ε ∧ ε < 1 ∧ ε - ε / 2 = ε / 2 ∧
      1 / (ε / 2) = 2 / ε := by
  refine ⟨by linarith, by linarith, hε₁, by ring, ?_⟩
  field_simp

set_option maxHeartbeats 200000 in
/-- The final numerical substitution retains the one-shot penalty of one bit
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem blowingUp_log_dimension_lower_bound
    {logM logM' logF logΓ H ε : ℝ}
    (hH : logM + logF - 2 * logΓ ≤ H)
    (hcode : H - 4 * log2 (1 / (ε / 2)) - 1 ≤ logM') :
    logM + logF - 2 * logΓ - 4 * log2 (2 / ε) - 1 ≤ logM' := by
  have heq : 1 / (ε / 2) = 2 / ε := by field_simp
  rw [heq] at hcode
  linarith

/-- A dimension-one transmission code can prepare any input and discard the
channel output. This is the trivial branch of
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
def EntanglementTransmissionCode.dimensionOne (N : Channel a b) (ρ : State a) :
    EntanglementTransmissionCode N PUnit.{u + 1} PUnit.{u + 1} PUnit.{u + 1} where
  encoder := Channel.replacer ρ
  decoder := Channel.replacer State.unit
  inputPairing := Equiv.refl _
  targetPairing := Equiv.refl _

/-- The trivial transmission code has squared fidelity one. -/
theorem EntanglementTransmissionCode.dimensionOne_fidelity
    (N : Channel a b) (ρ : State a) :
    (EntanglementTransmissionCode.dimensionOne N ρ).fidelity = 1 := by
  let C := EntanglementGenerationCode.ofTransmission
    (EntanglementTransmissionCode.dimensionOne N ρ)
  change C.outputState.squaredFidelity C.targetState = 1
  have heq : C.outputState = C.targetState :=
    (State.eq_maximallyMixed_of_subsingleton _).trans
      (State.eq_maximallyMixed_of_subsingleton _).symm
  rw [heq, State.squaredFidelity_self_eq_traceNorm_matrix_sq,
    traceNorm_posSemidef_eq_trace_re _ C.targetState.pos, C.targetState.trace_re_eq_one]
  norm_num

/-- Any nonpositive rate lower bound is met by a dimension-one code, including
the negative-bound branch of
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem exists_dimension_one_transmissionCode
    (N : Channel a b) (ρ : State a) {L ε : ℝ} (hL : L ≤ 0) :
    ∃ C : EntanglementTransmissionCode N PUnit.{u + 1} PUnit.{u + 1} PUnit.{u + 1},
      1 - ε ^ 2 ≤ C.fidelity ∧ L ≤ log2 (Fintype.card PUnit.{u + 1} : ℝ) := by
  refine ⟨EntanglementTransmissionCode.dimensionOne N ρ, ?_, ?_⟩
  · rw [EntanglementTransmissionCode.dimensionOne_fidelity]
    nlinarith [sq_nonneg ε]
  · simpa [log2] using hL

end

end QIT
