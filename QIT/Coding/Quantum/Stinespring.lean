/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.Basic
public import QIT.Channels.Stinespring
public import QIT.States.Purification.Uhlmann

/-!
# Stinespring lifts and decoder tests for quantum codes

The decoder pulls the normalized maximally entangled target back to an effect
on the reference and channel output. Its reference partial trace is `I / M`,
and pairing it with the channel output gives squared code fidelity
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:422-432].

Registers are reference-first, as in the code interface. Stinespring lifts use
`R × (B × E)`; explicit reassociation gives `(R × B) × E` for trace pairings.
This implements the source's convention that omitted factors carry identities
and tensor factors may be reordered
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:216-216].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix

namespace QIT

universe u v w x y

noncomputable section

namespace Channel

variable {a : Type u} {b : Type v}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The canonical finite Kraus witness stacked as a Stinespring isometry.
Its environment is `a × b`, with no minimality assertion. This realizes the
representation in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:219-227]. -/
def krausStinespring (N : Channel a b) : ReferenceIsometry a (b × (a × b)) :=
  MatrixMap.krausStinespringIsometry N.kraus (by
    rw [← N.map_eq_ofKraus]
    exact N.tracePreserving)

/-- Tracing the stacked Kraus environment recovers the original channel. -/
@[simp]
theorem krausStinespring_outputChannel (N : Channel a b) :
    N.krausStinespring.outputChannel = N := by
  apply ReferenceIsometry.outputChannel_eq_of_realizes
  intro X
  rw [krausStinespring, MatrixMap.partialTraceB_krausStinespringIsometry]
  exact congrArg (fun Φ : MatrixMap a b => Φ X) N.map_eq_ofKraus

end Channel

namespace EntanglementGenerationCode

variable {a : Type u} {b : Type v} {r : Type w} {t : Type x} {e : Type y}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype r] [DecidableEq r] [Nonempty r] [Fintype t] [DecidableEq t]
  [Fintype e] [DecidableEq e] {N : Channel a b}

/-- Lift the possibly mixed encoded state through an arbitrary Stinespring
isometry, preserving the reference register
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:422-432]. -/
def stinespringState (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) : State (r × (b × e)) :=
  ((Channel.idChannel r).prod (Channel.ofReferenceIsometry V)).applyState C.encodedState

/-- The lifted density matrix is the canonical right-isometry action. -/
theorem stinespringState_matrix (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) :
    (C.stinespringState V).matrix = V.applyMatrixRight C.encodedState.matrix :=
  MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight V C.encodedState.matrix

/-- The lifted state is fixed by the image projector on the left. -/
theorem stinespringState_supported_left (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) :
    Matrix.kronecker (1 : CMatrix r) V.imageProjector * (C.stinespringState V).matrix =
      (C.stinespringState V).matrix := by
  rw [stinespringState_matrix]
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single x.1]
  · simp only [ite_true, one_mul]
    change (V.imageProjector * (V.matrix *
        ReferenceIsometry.rightBlock C.encodedState.matrix x.1 y.1 * V.matrixᴴ)) x.2 y.2 = _
    have h := congrArg (fun X : CMatrix (b × e) => X x.2 y.2)
      (V.imageProjector_mul_lift
        (ReferenceIsometry.rightBlock C.encodedState.matrix x.1 y.1))
    simp only [MatrixMap.ofReferenceIsometry_apply] at h
    exact h
  · intro i _ hi
    simp only [ite_eq_right (Ne.symm hi), zero_mul, Finset.sum_const_zero]
  · simp

/-- The lifted state is fixed by the image projector on the right. -/
theorem stinespringState_supported_right (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) :
    (C.stinespringState V).matrix * Matrix.kronecker (1 : CMatrix r) V.imageProjector =
      (C.stinespringState V).matrix := by
  have h := congrArg Matrix.conjTranspose (C.stinespringState_supported_left V)
  have hp : (Matrix.kronecker (1 : CMatrix r) V.imageProjector).IsHermitian :=
    ((Matrix.PosSemidef.one : (1 : CMatrix r).PosSemidef).kronecker
      V.imageProjector_posSemidef).isHermitian
  rw [Matrix.conjTranspose_mul, (C.stinespringState V).pos.isHermitian.eq, hp.eq] at h
  exact h

/-- The encoded state lifted through the isometry is supported on its image,
including mixed encoded states
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:422-432]. -/
theorem stinespringState_supported (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) :
    Matrix.kronecker (1 : CMatrix r) V.imageProjector * (C.stinespringState V).matrix *
      Matrix.kronecker (1 : CMatrix r) V.imageProjector = (C.stinespringState V).matrix := by
  rw [C.stinespringState_supported_left V, C.stinespringState_supported_right V]

/-- Reassociate the lifted state so the environment is the final factor. -/
def stinespringOutput (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) : State ((r × b) × e) :=
  (C.stinespringState V).reindex (Equiv.prodAssoc r b e).symm

/-- Discarding the environment gives the code's joint reference/output state. -/
theorem stinespringOutput_marginalA (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N) :
    (C.stinespringOutput V).marginalA = C.channelOutput := by
  apply State.ext
  ext p q
  change (∑ z : e, (C.stinespringState V).matrix (p.1, (p.2, z)) (q.1, (q.2, z))) =
    MatrixMap.kron (Channel.idChannel r).map N.map C.encodedState.matrix p q
  rw [stinespringState_matrix, MatrixMap.kron_idChannel_left_apply_slice]
  change partialTraceB (V.matrix *
      ReferenceIsometry.rightBlock C.encodedState.matrix p.1 q.1 * V.matrixᴴ) p.2 q.2 = _
  rw [← V.outputChannel_map, hV]
  rfl

/-- Pull the normalized entangled target back through the decoder, with the
reference register first. This is `Q` in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:422-432]. -/
def decoderTest (C : EntanglementGenerationCode N r t) : CMatrix (r × b) :=
  ((Channel.idChannel r).prod C.decoder).dualEffect C.targetState.matrix

/-- Trace duality for the decoder test holds for arbitrary matrices, without
positivity or normalization hypotheses. -/
theorem decoderTest_trace_duality (C : EntanglementGenerationCode N r t)
    (X : CMatrix (r × b)) :
    (X * C.decoderTest).trace =
      (((Channel.idChannel r).prod C.decoder).map X * C.targetState.matrix).trace := by
  rw [Channel.map_eq_ofKraus]
  exact (MatrixMap.ofKraus_trace_duality _ X C.targetState.matrix).symm

/-- The decoder adjoint preserves positivity of the target projector. -/
theorem decoderTest_posSemidef (C : EntanglementGenerationCode N r t) :
    C.decoderTest.PosSemidef :=
  Channel.dualEffect_posSemidef _ C.targetState.pos

/-- The decoder test is Hermitian. -/
theorem decoderTest_isHermitian (C : EntanglementGenerationCode N r t) :
    C.decoderTest.IsHermitian :=
  C.decoderTest_posSemidef.isHermitian

/-- Pulling back the normalized target projector gives an effect bounded by
the identity, as in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:422-432]. -/
theorem decoderTest_le_one (C : EntanglementGenerationCode N r t) :
    C.decoderTest ≤ 1 := by
  apply Channel.dualEffect_le_one_of_le_one
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent C.targetState.matrix
    C.targetState.pos (PureVector.maximallyEntangled C.pairing).state_matrix_mul_self

/-- Tracing out the reference gives exactly the identity divided by the code
dimension, independently of the encoded state's reference marginal
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:422-432]. -/
theorem partialTraceA_decoderTest (C : EntanglementGenerationCode N r t) :
    partialTraceA C.decoderTest = (C.dimension : ℂ)⁻¹ • (1 : CMatrix b) := by
  let : Nonempty t := ⟨C.pairing (Classical.choice inferInstance)⟩
  have htarget : partialTraceA C.targetState.matrix =
      (C.dimension : ℂ)⁻¹ • (1 : CMatrix t) := by
    have h := congrArg State.matrix (PureVector.maximallyEntangled_marginalB C.pairing)
    change partialTraceA C.targetState.matrix = (State.maximallyMixed t).matrix at h
    simpa [State.maximallyMixed_matrix, ← C.dimension_eq_target_card] using h
  have htrace (X : CMatrix b) :
      (X * partialTraceA C.decoderTest).trace =
        (X * ((C.dimension : ℂ)⁻¹ • (1 : CMatrix b))).trace := by
    calc
      _ = (Matrix.kronecker (1 : CMatrix r) X * C.decoderTest).trace :=
        (trace_kronecker_one_mul_eq_trace_mul_partialTraceA C.decoderTest X).symm
      _ = (((Channel.idChannel r).prod C.decoder).map
          (Matrix.kronecker (1 : CMatrix r) X) * C.targetState.matrix).trace :=
        C.decoderTest_trace_duality _
      _ = (Matrix.kronecker (1 : CMatrix r) (C.decoder.map X) *
          C.targetState.matrix).trace := by
        rw [Channel.prod_map_kronecker]
        simp [Channel.idChannel, MatrixMap.ofKraus]
      _ = (C.decoder.map X * partialTraceA C.targetState.matrix).trace :=
        trace_kronecker_one_mul_eq_trace_mul_partialTraceA _ _
      _ = _ := by
        rw [htarget, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
          C.decoder.tracePreserving, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  ext i j
  have h := htrace (Matrix.single j i (1 : ℂ))
  simpa only [Matrix.trace_single_mul, one_smul] using h

/-- Squared code fidelity is the expectation of the decoder test on the joint
reference/channel output. -/
theorem fidelity_eq_trace_decoderTest (C : EntanglementGenerationCode N r t) :
    C.fidelity = ((C.channelOutput.matrix * C.decoderTest).trace).re := by
  rw [C.fidelity_eq_trace, C.decoderTest_trace_duality]
  rfl

/-- The environment lift turns code fidelity into pairing with `Q ⊗ I_E`,
with the environment in the final tensor factor
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:422-432]. -/
theorem fidelity_eq_trace_stinespringOutput (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N) :
    C.fidelity = (((C.stinespringOutput V).matrix *
      Matrix.kronecker C.decoderTest (1 : CMatrix e)).trace).re := by
  rw [trace_mul_kronecker_one_right_eq_partialTraceB]
  change C.fidelity = (((C.stinespringOutput V).marginalA.matrix * C.decoderTest).trace).re
  rw [C.stinespringOutput_marginalA V hV, C.fidelity_eq_trace_decoderTest]

/-- Extend the decoder test by the environment identity and reassociate it
onto the same registers as `stinespringState`. -/
def decoderTestWithEnvironment (C : EntanglementGenerationCode N r t)
    (e : Type y) [Fintype e] [DecidableEq e] : CMatrix (r × (b × e)) :=
  WireFam.matReindex (Equiv.prodAssoc r b e) (Matrix.kronecker C.decoderTest (1 : CMatrix e))

/-- Adding the unused environment and reassociating preserves positivity. -/
theorem decoderTestWithEnvironment_posSemidef (C : EntanglementGenerationCode N r t)
    (e : Type y) [Fintype e] [DecidableEq e] :
    (C.decoderTestWithEnvironment e).PosSemidef :=
  (C.decoderTest_posSemidef.kronecker
    (Matrix.PosSemidef.one : (1 : CMatrix e).PosSemidef)).submatrix
      (Equiv.prodAssoc r b e).symm

/-- The extended decoder test remains bounded by the identity. -/
theorem decoderTestWithEnvironment_le_one (C : EntanglementGenerationCode N r t)
    (e : Type y) [Fintype e] [DecidableEq e] :
    C.decoderTestWithEnvironment e ≤ 1 := by
  have hsum : Matrix.kronecker C.decoderTest (1 : CMatrix e) +
      Matrix.kronecker (1 - C.decoderTest) (1 : CMatrix e) = 1 := by
    simp only [Matrix.kronecker]
    rw [← Matrix.add_kronecker, add_sub_cancel, Matrix.one_kronecker_one]
  have hk : (1 - Matrix.kronecker C.decoderTest (1 : CMatrix e)).PosSemidef := by
    rw [← hsum, add_sub_cancel_left]
    exact (Matrix.le_iff.mp C.decoderTest_le_one).kronecker Matrix.PosSemidef.one
  rw [Matrix.le_iff, decoderTestWithEnvironment,
    ← WireFam.matReindex_one (Equiv.prodAssoc r b e), ← WireFam.matReindex_sub]
  exact hk.submatrix (Equiv.prodAssoc r b e).symm

/-- The test and image-support identities can be consumed on the same
reference-first Stinespring space, with the environment identity explicit. -/
theorem fidelity_eq_trace_stinespringState (C : EntanglementGenerationCode N r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N) :
    C.fidelity = (((C.stinespringState V).matrix * C.decoderTestWithEnvironment e).trace).re := by
  rw [C.fidelity_eq_trace_stinespringOutput V hV]
  have hρ : (C.stinespringState V).matrix =
      WireFam.matReindex (Equiv.prodAssoc r b e) (C.stinespringOutput V).matrix := rfl
  rw [hρ, decoderTestWithEnvironment, ← WireFam.matReindex_mul, WireFam.matReindex_trace]

end EntanglementGenerationCode

/-- The dimension constant for a chosen output/environment bipartition.
This is the constant in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530].
It depends on the chosen environment, which need not be minimal. For a
memoryless channel, later block estimates must use a fixed single-use
realization before taking tensor powers. -/
def stinespringKappa (b : Type u) (e : Type v) [Fintype b] [Fintype e] : ℕ :=
  min (Fintype.card b ^ 2) (Fintype.card e ^ 2)

/-- The chosen dimension constant is positive for nonempty systems. -/
theorem stinespringKappa_pos (b : Type u) (e : Type v)
    [Fintype b] [Fintype e] [Nonempty b] [Nonempty e] :
    0 < stinespringKappa b e :=
  lt_min (pow_pos Fintype.card_pos 2) (pow_pos Fintype.card_pos 2)

/-- The receiver dimension always bounds the chosen constant. -/
theorem stinespringKappa_le_output (b : Type u) (e : Type v)
    [Fintype b] [Fintype e] : stinespringKappa b e ≤ Fintype.card b ^ 2 :=
  Nat.min_le_left _ _

/-- The environment dimension always bounds the chosen constant. -/
theorem stinespringKappa_le_environment (b : Type u) (e : Type v)
    [Fintype b] [Fintype e] : stinespringKappa b e ≤ Fintype.card e ^ 2 :=
  Nat.min_le_right _ _

/-- The stacked Kraus environment has dimension `|A||B|`. When the input
system is nonempty its dimension constant is exactly `|B|²`. This explicitly
re-estimates the source constant for this non-minimal realization; it does
not assert equality with the constant of a minimal Stinespring environment. -/
theorem stinespringKappa_krausEnvironment (a : Type u) (b : Type v)
    [Fintype a] [Nonempty a] [Fintype b] :
    stinespringKappa b (a × b) = Fintype.card b ^ 2 := by
  rw [stinespringKappa, Fintype.card_prod, min_eq_left]
  have hcard : Fintype.card b ≤ Fintype.card a * Fintype.card b := by
    simpa using Nat.mul_le_mul_right (Fintype.card b) (Fintype.card_pos (α := a))
  nlinarith

end

end QIT
