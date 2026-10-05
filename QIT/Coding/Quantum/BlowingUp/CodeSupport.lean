/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.Stinespring
public import QIT.Coding.Quantum.BlowingUp.OneShot
public import QIT.Coding.Quantum.BlowingUp.Geometry
public import QIT.Coding.Quantum.BlowingUp.Entropy
public import QIT.Util.Matrix.SpectralSupport

/-!
# Code support and marginal bridges for quantum blowing-up

The supported decoder eigenvector and its environment marginal for
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

namespace ReferenceIsometry

/-- Extending the image projector by a reference preserves Hermiticity. -/
theorem reference_imageProjector_isHermitian (V : ReferenceIsometry a b) :
    (Matrix.kronecker (1 : CMatrix r) V.imageProjector).IsHermitian :=
  (Matrix.PosSemidef.one.kronecker V.imageProjector_posSemidef).isHermitian

/-- Extending the image projector by a reference preserves idempotence. -/
theorem reference_imageProjector_idempotent (V : ReferenceIsometry a b) :
    Matrix.kronecker (1 : CMatrix r) V.imageProjector *
      Matrix.kronecker (1 : CMatrix r) V.imageProjector =
      Matrix.kronecker (1 : CMatrix r) V.imageProjector := by
  simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    V.imageProjector_idempotent]

/-- Every pure vector supported on the extended image has an input pure
preimage; no full-rank assumption is needed. -/
theorem exists_applyPureVectorRight_of_supported (V : ReferenceIsometry a b)
    (ψ : PureVector (r × b))
    (hψ : (Matrix.kronecker (1 : CMatrix r) V.imageProjector).mulVec ψ.amp = ψ.amp) :
    ∃ ξ : PureVector (r × a), V.applyPureVectorRight ξ = ψ := by
  let v : r × a → ℂ := fun x => V.matrixᴴ.mulVec (fun j => ψ.amp (x.1, j)) x.2
  have hv : V.applyAmpRight v = ψ.amp := by
    ext x
    have hx := congrFun hψ x
    have hh : V.applyAmpRight v x =
        (Matrix.kronecker (1 : CMatrix r) V.imageProjector).mulVec ψ.amp x := by
      change (V.matrix.mulVec (V.matrixᴴ.mulVec (fun j => ψ.amp (x.1, j)))) x.2 = _
      rw [Matrix.mulVec_mulVec]
      simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
        imageProjector]
    exact hh.trans hx
  have htr : (rankOneMatrix v).trace = 1 := by
    have ht := congrArg Matrix.trace (V.partialTraceB_applyMatrixRight (rankOneMatrix v))
    rw [partialTraceB_trace, partialTraceB_trace, ← V.rankOne_applyAmpRight, hv] at ht
    exact ht.symm.trans ψ.trace_rankOne_eq_one
  refine ⟨⟨v, htr⟩, ?_⟩
  apply PureVector.ext_amp
  exact hv

end ReferenceIsometry

namespace EntanglementGenerationCode
variable [Nonempty r] {N : Channel a b}

/-- Code fidelity is bounded by the norm of the supported decoder test
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:435-440]. -/
theorem fidelity_le_compressed_decoder_norm (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N) :
    C.fidelity ≤ ‖Matrix.kronecker (1 : CMatrix r) V.imageProjector *
      C.decoderTestWithEnvironment e * Matrix.kronecker (1 : CMatrix r) V.imageProjector‖ := by
  let P := Matrix.kronecker (1 : CMatrix r) V.imageProjector
  let Q := C.decoderTestWithEnvironment e
  let ρ := C.stinespringState V
  have hP : P.IsHermitian := V.reference_imageProjector_isHermitian
  have hpos : (P * Q * P).PosSemidef := by
    simpa only [hP.eq] using (C.decoderTestWithEnvironment_posSemidef e).mul_mul_conjTranspose_same P
  have h := cMatrix_trace_mul_le_of_le_posSemidef_right ρ.pos
    (cMatrix_le_norm_smul_one _ hpos)
  have hleft : ((P * Q * P) * ρ.matrix).trace = (ρ.matrix * Q).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, C.stinespringState_supported_left V]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, C.stinespringState_supported_right V]
  rw [hleft, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, ρ.trace_eq_one] at h
  rw [C.fidelity_eq_trace_stinespringState V hV]
  simpa only [smul_eq_mul, mul_one, Complex.ofReal_re] using h

/-- Positive code fidelity gives a normalized supported top eigenvector
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:435-440]. -/
theorem exists_supported_decoder_eigenvector (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N) (hf : 0 < C.fidelity) :
    let P := Matrix.kronecker (1 : CMatrix r) V.imageProjector
    let Q := C.decoderTestWithEnvironment e
    ∃ ψ : PureVector (r × (b × e)), P.mulVec ψ.amp = ψ.amp ∧
      (P * Q).mulVec ψ.amp = (‖P * Q * P‖ : ℂ) • ψ.amp := by
  dsimp only
  obtain ⟨v, hv, _, hs, he⟩ := exists_unit_top_eigenvector_supported
    _ _ V.reference_imageProjector_isHermitian V.reference_imageProjector_idempotent
    (C.decoderTestWithEnvironment_posSemidef e)
    (hf.trans_le (C.fidelity_le_compressed_decoder_norm V hV))
  have htr : (rankOneMatrix (v : r × (b × e) → ℂ)).trace = 1 := by
    apply Complex.ext
    · rw [rankOneMatrix_trace_re_eq_norm_sq]
      change ‖v‖ ^ 2 = 1
      rw [hv, one_pow]
    · exact (rankOneMatrix_pos _).trace_nonneg.2.symm
  exact ⟨⟨v, htr⟩, hs, he⟩

/-- The decoder-filtered eigenvector has an environment side operator with
exact trace `lam / M`
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem exists_decoder_side_operator (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (ψ : PureVector (r × (b × e)))
    (hψ : (Matrix.kronecker (1 : CMatrix r) V.imageProjector).mulVec ψ.amp = ψ.amp)
    (lam : ℝ)
    (heig : (Matrix.kronecker (1 : CMatrix r) V.imageProjector *
      C.decoderTestWithEnvironment e).mulVec ψ.amp = (lam : ℂ) • ψ.amp) :
    ∃ τ : CMatrix e, τ.PosSemidef ∧ τ.trace.re = lam / (C.dimension : ℝ) ∧
      partialTraceA (rankOneMatrix (WireFam.vecReindex
        (QuantumBlowingUp.referenceReceiverSwap r b e)
        ((C.decoderTestWithEnvironment e).mulVec ψ.amp))) ≤
        Matrix.kronecker (1 : CMatrix r) τ := by
  let s := (QuantumBlowingUp.referenceReceiverSwap r b e).trans (Equiv.prodAssoc b r e).symm
  let D := WireFam.matReindex (Equiv.prodComm r b) C.decoderTest
  let ρ := WireFam.matReindex s ψ.state.matrix
  let S := Matrix.kronecker (psdSqrt D) (1 : CMatrix e)
  let c : ℝ := (C.dimension : ℝ)⁻¹
  let τ := (c : ℂ) • partialTraceA (S * ρ * S)
  have hD : D.PosSemidef := C.decoderTest_posSemidef.submatrix _
  have hρ : ρ.PosSemidef := ψ.state.pos.submatrix _
  have hS : Sᴴ = S := by
    simp only [S, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      (psdSqrt_isHermitian D).eq, Matrix.conjTranspose_one]
  have hc : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hSS : S * S = Matrix.kronecker D (1 : CMatrix e) := by
    simp only [S, Matrix.kronecker, ← Matrix.mul_kronecker_mul,
      psdSqrt_mul_self_of_posSemidef hD, Matrix.one_mul]
  have hX : (S * ρ * S).PosSemidef := by
    simpa only [hS] using hρ.mul_mul_conjTranspose_same S
  have hDtr : partialTraceB D = (c : ℂ) • (1 : CMatrix b) := by
    change partialTraceA C.decoderTest = _
    simpa only [c, Complex.ofReal_inv, Complex.ofReal_natCast] using C.partialTraceA_decoderTest
  have hQ : WireFam.matReindex s (C.decoderTestWithEnvironment e) =
      Matrix.kronecker D (1 : CMatrix e) := by
    rfl
  have htr : (S * ρ * S).trace = (lam : ℂ) := by
    rw [Matrix.trace_mul_cycle, hSS, ← hQ, ← WireFam.matReindex_mul,
      WireFam.matReindex_trace]
    exact blowingUp_test_state_trace _ _ V.reference_imageProjector_isHermitian ψ hψ lam heig
  have hbound := partialTraceA_reassoc_filtered_le_of_marginal_le D ρ hD hρ c hc hDtr.le
  have hleft : WireFam.matReindex (Equiv.prodAssoc b r e)
      (Matrix.kronecker D (1 : CMatrix e) * ρ * Matrix.kronecker D (1 : CMatrix e)) =
      rankOneMatrix (WireFam.vecReindex (QuantumBlowingUp.referenceReceiverSwap r b e)
        ((C.decoderTestWithEnvironment e).mulVec ψ.amp)) := by
    rw [← hQ, ← WireFam.matReindex_mul, ← WireFam.matReindex_mul]
    have hherm := (C.decoderTestWithEnvironment_posSemidef e).isHermitian
    change WireFam.matReindex (QuantumBlowingUp.referenceReceiverSwap r b e)
      (C.decoderTestWithEnvironment e * rankOneMatrix ψ.amp * C.decoderTestWithEnvironment e) = _
    have hrank := rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
      (C.decoderTestWithEnvironment e) ψ.amp
    rw [hherm.eq] at hrank
    rw [← hrank]
    rfl
  refine ⟨τ, (partialTraceA_posSemidef hX).smul (by exact_mod_cast hc), ?_, ?_⟩
  · change ((c : ℂ) • partialTraceA (S * ρ * S)).trace.re = _
    rw [Matrix.trace_smul, partialTraceA_trace, htr]
    simp only [smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re, c]
    exact mul_comm _ _
  · rw [hleft] at hbound
    have hτ : Matrix.kronecker (1 : CMatrix r) τ =
        (c : ℂ) • Matrix.kronecker (1 : CMatrix r) (partialTraceA (S * ρ * S)) :=
      Matrix.kronecker_smul _ _ _
    exact hbound.trans_eq hτ.symm

end EntanglementGenerationCode

namespace PureVector

/-- Discarding the receiver is a partial trace on the receiver-first carrier. -/
theorem referenceEnvironmentState_matrix (ψ : PureVector (r × (b × e))) :
    ψ.referenceEnvironmentState.matrix = partialTraceA
      (rankOneMatrix (WireFam.vecReindex (QuantumBlowingUp.referenceReceiverSwap r b e) ψ.amp)) := by
  rfl

/-- Register reordering followed by discarding the receiver contracts distance. -/
theorem referenceEnvironmentState_purifiedDistance_le
    (ψ φ : PureVector (r × (b × e))) :
    ψ.referenceEnvironmentState.purifiedDistance φ.referenceEnvironmentState ≤
      ψ.state.purifiedDistance φ.state := by
  let s := QuantumBlowingUp.referenceReceiverSwap r b e
  have hψ : (ψ.reindex s).Purifies ψ.referenceEnvironmentState := by
    exact (ψ.reindex s).purifies_marginalB
  have hφ : (φ.reindex s).Purifies φ.referenceEnvironmentState := by
    exact (φ.reindex s).purifies_marginalB
  have h := State.purifiedDistance_le_sqrt_one_sub_overlapSq_of_purifies hψ hφ
  rw [PureVector.overlapSq_reindex] at h
  rw [State.purifiedDistance_eq ψ.state φ.state, State.squaredFidelity_pure_right_eq_trace,
    PureVector.state_matrix, PureVector.state_matrix,
    PureVector.rankOneMatrix_mul_trace_re_eq_overlapSq]
  exact h

end PureVector

end
end QIT
