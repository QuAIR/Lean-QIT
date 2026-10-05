/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.BlowingUp.OneShot
public import QIT.Coding.Quantum.BlowingUp.Geometry
public import QIT.Coding.Quantum.BlowingUp.Entropy
public import QIT.Coding.Quantum.BlowingUp.CodeSupport

/-!
# Quantum blowing-up

The one-shot code conversion of
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

universe u

variable {a b r t e : Type u}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
  [Fintype e] [DecidableEq e]

namespace QuantumBlowingUp

omit [DecidableEq b] [DecidableEq e] in
/-- The receiver-first lift acts by reindexing the reference-first action. -/
theorem receiverEnvironmentLift_mulVec (T : CMatrix (b × e))
    (v : r × (b × e) → ℂ) :
    (receiverEnvironmentLift r T).mulVec (WireFam.vecReindex (referenceReceiverSwap r b e) v) =
      WireFam.vecReindex (referenceReceiverSwap r b e)
        ((Matrix.kronecker (1 : CMatrix r) T).mulVec v) := by
  let s := referenceReceiverSwap r b e
  change (Matrix.kronecker (1 : CMatrix r) T).submatrix s.symm s.symm *ᵥ
    (v ∘ s.symm) = ((Matrix.kronecker (1 : CMatrix r) T).mulVec v) ∘ s.symm
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

/-- The normalized filtered vector has the matrix form consumed by the
projective-norm entropy estimate. -/
theorem referenceEnvironmentState_filtered_matrix
    (T : CMatrix (b × e)) (Q : CMatrix (r × (b × e)))
    (ψ φ : PureVector (r × (b × e))) (d : ℝ)
    (hφ : φ.state.matrix = ((d⁻¹ : ℝ) : ℂ) •
      rankOneMatrix ((Matrix.kronecker (1 : CMatrix r) T * Q).mulVec ψ.amp)) :
    φ.referenceEnvironmentState.matrix = ((d⁻¹ : ℝ) : ℂ) • partialTraceA
      (rankOneMatrix ((receiverEnvironmentLift r T).mulVec
        (WireFam.vecReindex (referenceReceiverSwap r b e) (Q.mulVec ψ.amp)))) := by
  rw [receiverEnvironmentLift_mulVec, Matrix.mulVec_mulVec]
  change partialTraceA (WireFam.matReindex (referenceReceiverSwap r b e) φ.state.matrix) = _
  rw [hφ]
  exact partialTraceA_smul _ _

end QuantumBlowingUp

namespace EntanglementGenerationCode

variable [Nonempty r] {N : Channel a b}

/-- The projector approximation supplies a pure input and a normalized
smoothing candidate with the required conditional min-entropy. The candidate
is a `State`, so its trace is exactly one
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem exists_input_and_smoothing_candidate
    (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N)
    (T : CMatrix (b × e)) {Γ ε : ℝ}
    (hf : 0 < C.fidelity) (hΓ : 0 < Γ) (hε : 0 < ε)
    (hPT : V.imageProjector * T = V.imageProjector)
    (hpi : piNorm T ≤ Γ)
    (happrox : ‖T - V.imageProjector‖ ≤ ε * Real.sqrt C.fidelity / 2) :
    ∃ (ξ : PureVector (r × a)) (σ : State (r × e)),
      (V.applyPureVectorRight ξ).referenceEnvironmentState.purifiedDistance σ ≤ ε / 2 ∧
      log2 (C.dimension : ℝ) + log2 C.fidelity - 2 * log2 Γ ≤ σ.conditionalMinEntropy := by
  let P := Matrix.kronecker (1 : CMatrix r) V.imageProjector
  let Q := C.decoderTestWithEnvironment e
  let A := Matrix.kronecker (1 : CMatrix r) T
  let lam : ℝ := ‖P * Q * P‖
  have hf_lam : C.fidelity ≤ lam := C.fidelity_le_compressed_decoder_norm V hV
  have hlam : 0 < lam := hf.trans_le hf_lam
  obtain ⟨ψ, hψ, heig⟩ := C.exists_supported_decoder_eigenvector V hV hf
  have hPA : P * A = P := by
    simp only [P, A, Matrix.kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hPT]
  have hnorm : ‖A - P‖ = ‖T - V.imageProjector‖ := by
    have hsub : A - P = Matrix.kronecker (1 : CMatrix r) (T - V.imageProjector) := by
      ext i j
      exact (mul_sub _ _ _).symm
    rw [hsub, matrix_l2_opNorm_kronecker, norm_one, one_mul]
  have herr : ‖A - P‖ ^ 2 ≤ ε ^ 2 * lam / 4 := by
    rw [hnorm]
    calc
      _ ≤ (ε * Real.sqrt C.fidelity / 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) happrox 2
      _ = ε ^ 2 * C.fidelity / 4 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hf.le]
        ring
      _ ≤ _ := by gcongr
  obtain ⟨hd, hdlam, _, φ, hφ, hdist⟩ := blowingUp_filter_geometry
    P A Q V.reference_imageProjector_isHermitian V.reference_imageProjector_idempotent
    hPA (C.decoderTestWithEnvironment_posSemidef e) (C.decoderTestWithEnvironment_le_one e)
    ψ hψ hlam hε heig herr
  obtain ⟨τ, hτ, htr, hdom⟩ := C.exists_decoder_side_operator V ψ hψ lam heig
  have hM : 0 < (C.dimension : ℝ) := by exact_mod_cast C.dimension_pos
  have hmat := QuantumBlowingUp.referenceEnvironmentState_filtered_matrix T Q ψ φ _ hφ
  have hent := QuantumBlowingUp.conditionalMinEntropy_filtered_ge T
    (WireFam.vecReindex (QuantumBlowingUp.referenceReceiverSwap r b e) (Q.mulVec ψ.amp))
    τ hτ hdom φ.referenceEnvironmentState hd hM hlam hΓ hpi hdlam htr hmat
  obtain ⟨ξ, hξ⟩ := V.exists_applyPureVectorRight_of_supported ψ hψ
  refine ⟨ξ, φ.referenceEnvironmentState, ?_, ?_⟩
  · rw [hξ]
    exact (ψ.referenceEnvironmentState_purifiedDistance_le φ).trans hdist
  · have hlog := log2_mono_of_pos hf hf_lam
    linarith

/-- The normalized candidate is admitted by the full subnormalized smoothing
optimization [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem exists_input_smoothConditionalMinEntropy_ge
    (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N)
    (T : CMatrix (b × e)) {Γ ε : ℝ}
    (hf : 0 < C.fidelity) (hΓ : 0 < Γ) (hε : 0 < ε) (hε₁ : ε < 1)
    (hPT : V.imageProjector * T = V.imageProjector)
    (hpi : piNorm T ≤ Γ)
    (happrox : ‖T - V.imageProjector‖ ≤ ε * Real.sqrt C.fidelity / 2) :
    ∃ ξ : PureVector (r × a),
      log2 (C.dimension : ℝ) + log2 C.fidelity - 2 * log2 Γ ≤
        (V.applyPureVectorRight ξ).referenceEnvironmentState.smoothConditionalMinEntropy
          (ε / 2) (by positivity) (by linarith) := by
  obtain ⟨ξ, σ, hdist, hent⟩ :=
    C.exists_input_and_smoothing_candidate V hV T hf hΓ hε hPT hpi happrox
  exact ⟨ξ, QuantumBlowingUp.smoothConditionalMinEntropy_ge_of_normalized_candidate
    _ σ (by positivity) (by linarith) hdist hent⟩

/-- Fully quantum blowing-up, conditional only on the explicit one-shot
achievability witness. The output is a transmission code even when the input
generation code has a mixed encoding. Both projector identities, the squared
fidelity convention, and the final one-bit penalty match
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem exists_transmissionCode_of_oneShotAchievability
    (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N)
    (hFact1 : N.HasOneShotQuantumAchievability V)
    (T : CMatrix (b × e)) {Γ ε : ℝ}
    (hf : 0 < C.fidelity) (hΓ : 0 < Γ) (hε : 0 < ε) (hε₁ : ε < 1)
    (_hTP : T * V.imageProjector = V.imageProjector)
    (hPT : V.imageProjector * T = V.imageProjector)
    (hpi : piNorm T ≤ Γ)
    (happrox : ‖T - V.imageProjector‖ ≤ ε * Real.sqrt C.fidelity / 2) :
    ∃ (m : Type u), ∃ (_ : Fintype m), ∃ (_ : DecidableEq m), ∃ (_ : Nonempty m),
      ∃ C' : EntanglementTransmissionCode N m m m,
        1 - ε ^ 2 ≤ C'.fidelity ∧
        log2 (C.dimension : ℝ) + log2 C.fidelity - 2 * log2 Γ -
          4 * log2 (2 / ε) - 1 ≤ log2 (Fintype.card m : ℝ) := by
  by_cases hL : log2 (C.dimension : ℝ) + log2 C.fidelity - 2 * log2 Γ -
      4 * log2 (2 / ε) - 1 ≤ 0
  · obtain ⟨C', hfid, hdim⟩ := exists_dimension_one_transmissionCode
      N C.encodedState.marginalB (ε := ε) hL
    exact ⟨PUnit.{u + 1}, inferInstance, inferInstance, inferInstance, C', hfid, hdim⟩
  · obtain ⟨ξ, hent⟩ := C.exists_input_smoothConditionalMinEntropy_ge
      V hV T hf hΓ hε hε₁ hPT hpi happrox
    obtain ⟨hhalf, hhalfε, _, hsub, _⟩ := blowingUp_half_error_parameters hε hε₁
    obtain ⟨m, imF, imD, imN, C', hfid, hcode⟩ := hFact1 r ξ ε (ε / 2) hhalf hhalfε hε₁
    refine ⟨m, imF, imD, imN, C', hfid, ?_⟩
    simp only [hsub] at hcode
    exact blowingUp_log_dimension_lower_bound hent hcode

end EntanglementGenerationCode

end

end QIT
