/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.Diamond

/-!
# Stinespring image projectors and complementary channels

A reference isometry has an orthogonal image projector. For an isometry into a
product space, tracing either factor gives the output or complementary channel.

The Stinespring representation and its image projector are used in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:219-227] and
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. The support
identities below are elementary consequences of the isometry equation. The
complement convention follows the complementary-map definition at lines
2206-2207 within [KhatriWilde2024Principles, Chapters/EA_capacity.tex:2152-2240].
-/

@[expose] public section

namespace QIT

open scoped ComplexOrder MatrixOrder Matrix

universe u v w

noncomputable section

namespace ReferenceIsometry

variable {a : Type u} {b : Type v} {e : Type w}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype e] [DecidableEq e]

/-- The orthogonal projector onto the image of an isometry, as in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
def imageProjector (V : ReferenceIsometry a b) : CMatrix b :=
  V.matrix * V.matrixᴴ

/-- The image projector is positive semidefinite. -/
theorem imageProjector_posSemidef (V : ReferenceIsometry a b) :
    V.imageProjector.PosSemidef := by
  simpa [imageProjector] using Matrix.posSemidef_conjTranspose_mul_self V.matrixᴴ

/-- The image projector is Hermitian. -/
theorem imageProjector_isHermitian (V : ReferenceIsometry a b) :
    V.imageProjector.IsHermitian :=
  V.imageProjector_posSemidef.isHermitian

/-- The isometry equation makes the image projector idempotent. -/
@[simp]
theorem imageProjector_idempotent (V : ReferenceIsometry a b) :
    V.imageProjector * V.imageProjector = V.imageProjector := by
  change (V.matrix * V.matrixᴴ) * (V.matrix * V.matrixᴴ) = V.matrix * V.matrixᴴ
  calc
    _ = V.matrix * (V.matrixᴴ * V.matrix) * V.matrixᴴ := by simp [Matrix.mul_assoc]
    _ = _ := by rw [V.isometry, Matrix.mul_one]

/-- The orthogonal complement of the isometry image is positive semidefinite. -/
theorem one_sub_imageProjector_posSemidef (V : ReferenceIsometry a b) :
    (1 - V.imageProjector).PosSemidef :=
  MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent V.imageProjector
    V.imageProjector_posSemidef V.imageProjector_idempotent

/-- The image projector is bounded above by the identity in the Loewner order. -/
theorem imageProjector_le_one (V : ReferenceIsometry a b) :
    V.imageProjector ≤ 1 := by
  rw [Matrix.le_iff]
  exact V.one_sub_imageProjector_posSemidef

/-- The projector fixes the isometry matrix. -/
@[simp]
theorem imageProjector_mul_matrix (V : ReferenceIsometry a b) :
    V.imageProjector * V.matrix = V.matrix := by
  simp only [imageProjector, Matrix.mul_assoc, V.isometry, Matrix.mul_one]

/-- The adjoint is fixed by right multiplication with the image projector. -/
@[simp]
theorem conjTranspose_matrix_mul_imageProjector (V : ReferenceIsometry a b) :
    V.matrixᴴ * V.imageProjector = V.matrixᴴ := by
  rw [imageProjector, ← Matrix.mul_assoc, V.isometry, Matrix.one_mul]

/-- Every lifted matrix is supported on the isometry image on the left. -/
@[simp]
theorem imageProjector_mul_lift (V : ReferenceIsometry a b) (X : CMatrix a) :
    V.imageProjector * MatrixMap.ofReferenceIsometry V X =
      MatrixMap.ofReferenceIsometry V X := by
  simp only [MatrixMap.ofReferenceIsometry_apply, ← Matrix.mul_assoc,
    imageProjector_mul_matrix]

/-- Every lifted matrix is supported on the isometry image on the right. -/
@[simp]
theorem lift_mul_imageProjector (V : ReferenceIsometry a b) (X : CMatrix a) :
    MatrixMap.ofReferenceIsometry V X * V.imageProjector =
      MatrixMap.ofReferenceIsometry V X := by
  simp only [MatrixMap.ofReferenceIsometry_apply, Matrix.mul_assoc,
    conjTranspose_matrix_mul_imageProjector]

/-- Projecting on both sides leaves an arbitrary lifted matrix unchanged. -/
theorem imageProjector_mul_lift_mul_imageProjector
    (V : ReferenceIsometry a b) (X : CMatrix a) :
    V.imageProjector * MatrixMap.ofReferenceIsometry V X * V.imageProjector =
      MatrixMap.ofReferenceIsometry V X := by
  rw [imageProjector_mul_lift, lift_mul_imageProjector]

/-- The joint output state of the isometry channel is supported on its image. -/
theorem imageProjector_mul_applyState_matrix_mul_imageProjector
    (V : ReferenceIsometry a b) (ρ : State a) :
    V.imageProjector * ((Channel.ofReferenceIsometry V).applyState ρ).matrix *
        V.imageProjector = ((Channel.ofReferenceIsometry V).applyState ρ).matrix :=
  V.imageProjector_mul_lift_mul_imageProjector ρ.matrix

/-- A vector is fixed by the image projector exactly when it lies in the
isometry image. The preimage can be chosen by applying the adjoint. -/
theorem imageProjector_mulVec_eq_self_iff (V : ReferenceIsometry a b) (y : b → ℂ) :
    V.imageProjector.mulVec y = y ↔ ∃ x, V.matrix.mulVec x = y := by
  constructor
  · intro h
    exact ⟨V.matrixᴴ.mulVec y, by simpa [imageProjector, Matrix.mulVec_mulVec] using h⟩
  · rintro ⟨x, rfl⟩
    rw [Matrix.mulVec_mulVec, imageProjector_mul_matrix]

/-- The output channel of a Stinespring isometry, obtained by tracing out the
environment, as in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:219-227]. -/
def outputChannel (V : ReferenceIsometry a (b × e)) : Channel a b :=
  (Channel.traceOutRight b e).comp (Channel.ofReferenceIsometry V)

/-- The complementary channel obtained by tracing out the output system,
specializing the complementary-map definition at lines 2206-2207 within
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2152-2240]. -/
def complementaryChannel (V : ReferenceIsometry a (b × e)) : Channel a e :=
  (Channel.traceOutLeft b e).comp (Channel.ofReferenceIsometry V)

/-- The output channel traces the environment of the lifted matrix. -/
@[simp]
theorem outputChannel_map (V : ReferenceIsometry a (b × e)) (X : CMatrix a) :
    V.outputChannel.map X = partialTraceB (V.matrix * X * V.matrixᴴ) := by
  change partialTraceB (MatrixMap.ofReferenceIsometry V X) = _
  rw [MatrixMap.ofReferenceIsometry_apply]

/-- The complementary channel traces the output system of the lifted matrix. -/
@[simp]
theorem complementaryChannel_map (V : ReferenceIsometry a (b × e)) (X : CMatrix a) :
    V.complementaryChannel.map X = partialTraceA (V.matrix * X * V.matrixᴴ) := by
  change partialTraceA (MatrixMap.ofReferenceIsometry V X) = _
  rw [MatrixMap.ofReferenceIsometry_apply]

/-- The output state is the first marginal of the joint isometry output. -/
@[simp]
theorem outputChannel_applyState (V : ReferenceIsometry a (b × e)) (ρ : State a) :
    V.outputChannel.applyState ρ =
      ((Channel.ofReferenceIsometry V).applyState ρ).marginalA := by
  rw [outputChannel, Channel.applyState_comp, Channel.traceOutRight_applyState]

/-- The complementary output state is the environment marginal. -/
@[simp]
theorem complementaryChannel_applyState (V : ReferenceIsometry a (b × e)) (ρ : State a) :
    V.complementaryChannel.applyState ρ =
      ((Channel.ofReferenceIsometry V).applyState ρ).marginalB := by
  rw [complementaryChannel, Channel.applyState_comp, Channel.traceOutLeft_applyState]

/-- A Stinespring witness recovers the channel it realizes. This packages the
representation equation of
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:219-227]
as equality of bundled channels, without choosing a Kraus environment. -/
theorem outputChannel_eq_of_realizes (V : ReferenceIsometry a (b × e)) (N : Channel a b)
    (hN : ∀ X, N.map X = partialTraceB (V.matrix * X * V.matrixᴴ)) :
    V.outputChannel = N := by
  have hm : V.outputChannel.map = N.map := by
    ext X i j
    exact congrFun (congrFun ((V.outputChannel_map X).trans (hN X).symm) i) j
  cases hV : V.outputChannel
  cases N
  rw [hV] at hm
  cases hm
  rfl

end ReferenceIsometry

end

end QIT
