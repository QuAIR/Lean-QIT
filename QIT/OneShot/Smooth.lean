/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.CQState
public import QIT.Information.Entropy.Entropy
public import QIT.States.Geometry.Fidelity
public import QIT.States.Geometry.FuchsVdG
public import QIT.Core.POVMProbability
public import QIT.Channels.Diamond
public import QIT.States.Schatten
public import QIT.States.Purification.PureGeometry
public import QIT.States.Purification.Uhlmann
public import QIT.States.Subnormalized
public import QIT.States.TraceNorm.PositivePart
public import Mathlib.Data.Real.Archimedean

/-!
# Smooth min/max entropy

Definition-level normalized-state API for purified-distance smoothing and
smooth conditional min/max entropies. The definitions follow the finite
normalized-state route used in one-shot quantum information: purified distance is
the normalized specialization of [Tomamichel2015FiniteResources,
metric.tex:512-513], conditional min/max entropy follow
[Tomamichel2015FiniteResources, calculus.tex:81-89] and
[Tomamichel2015FiniteResources, calculus.tex:191-198], and smoothing follows
[Tomamichel2015FiniteResources, calculus.tex:418-426].

Lean-QIT records entropy values in bits. Thus the min-entropy order constraint
uses `2^{-λ}` rather than the natural-exponential notation used in the source.
The cq guessing-probability interface follows [Tomamichel2015FiniteResources,
calculus.tex:348-357], but the SDP/duality proof of optimality remains a
downstream proof dependency.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-! ## Purified distance and smoothing balls -/

/-- Purified distance between normalized finite-dimensional states,
`P(ρ,σ) = sqrt(1 - F(ρ,σ)^2)`, using the local squared-fidelity convention. -/
def purifiedDistance (ρ σ : State a) : ℝ :=
  Real.sqrt (1 - ρ.squaredFidelity σ)

@[simp]
theorem purifiedDistance_eq (ρ σ : State a) :
    ρ.purifiedDistance σ = Real.sqrt (1 - ρ.squaredFidelity σ) :=
  rfl

/-- The closed purified-distance epsilon ball around a normalized state. -/
def purifiedBall (ρ : State a) (ε : ℝ) (σ : State a) : Prop :=
  ρ.purifiedDistance σ ≤ ε

@[simp]
theorem purifiedBall_eq (ρ σ : State a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔ ρ.purifiedDistance σ ≤ ε :=
  Iff.rfl

/-- Purified-distance balls are monotone in the smoothing radius. -/
theorem purifiedBall_mono {ρ σ : State a} {ε δ : ℝ} (hεδ : ε ≤ δ) :
    ρ.purifiedBall ε σ → ρ.purifiedBall δ σ := by
  intro hball
  exact le_trans hball hεδ

/-- Purified distance is antitone in squared fidelity.

This is the algebraic handoff used by fidelity-monotonicity arguments: once a
map is known to increase squared fidelity, its output purified distance is
bounded by the input purified distance. -/
theorem purifiedDistance_le_of_squaredFidelity_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : State a} {τ υ : State b}
    (hF : ρ.squaredFidelity σ ≤ τ.squaredFidelity υ) :
    τ.purifiedDistance υ ≤ ρ.purifiedDistance σ := by
  rw [State.purifiedDistance_eq, State.purifiedDistance_eq]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The same squared-fidelity monotonicity handoff, phrased for purified balls. -/
theorem purifiedBall_of_squaredFidelity_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : State a} {τ υ : State b} {ε : ℝ}
    (hF : ρ.squaredFidelity σ ≤ τ.squaredFidelity υ)
    (hball : ρ.purifiedBall ε σ) :
    τ.purifiedBall ε υ := by
  exact le_trans (purifiedDistance_le_of_squaredFidelity_le hF) hball

/-- Squared fidelity is symmetric, proved here from Uhlmann's purification
characterization so the basic purified-distance layer can use it without
importing endpoint trace-norm symmetry. -/
theorem squaredFidelity_comm_of_uhlmann (ρ σ : State a) :
    ρ.squaredFidelity σ = σ.squaredFidelity ρ := by
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  obtain ⟨Φ, hΦ, hΦeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := ρ) (σ := σ) hΨ (le_refl (Fintype.card a))
  have hle_forward : ρ.squaredFidelity σ ≤ σ.squaredFidelity ρ := by
    calc
      ρ.squaredFidelity σ = Ψ.overlapSq Φ := hΦeq.symm
      _ = Φ.overlapSq Ψ := PureVector.overlapSq_comm Φ Ψ
      _ ≤ σ.squaredFidelity ρ :=
          PureVector.overlapSq_le_squaredFidelity_of_purifies hΦ hΨ
  let Ω : PureVector (Prod a a) := σ.canonicalPurification
  have hΩ : Ω.Purifies σ := by
    simpa [Ω] using σ.canonicalPurification_purifies
  obtain ⟨Θ, hΘ, hΘeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := σ) (σ := ρ) hΩ (le_refl (Fintype.card a))
  have hle_reverse : σ.squaredFidelity ρ ≤ ρ.squaredFidelity σ := by
    calc
      σ.squaredFidelity ρ = Ω.overlapSq Θ := hΘeq.symm
      _ = Θ.overlapSq Ω := PureVector.overlapSq_comm Θ Ω
      _ ≤ ρ.squaredFidelity σ :=
          PureVector.overlapSq_le_squaredFidelity_of_purifies hΘ hΩ
  exact le_antisymm hle_forward hle_reverse

/-- Squared fidelity is bounded by one. -/
theorem squaredFidelity_le_one_of_uhlmann (ρ σ : State a) :
    ρ.squaredFidelity σ ≤ 1 := by
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  obtain ⟨Φ, _hΦ, hΦeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := ρ) (σ := σ) hΨ (le_refl (Fintype.card a))
  have hoverlap := PureVector.one_sub_overlapSq_nonneg Ψ Φ
  rw [← hΦeq]
  linarith

/-- Purified distance is symmetric on normalized states. -/
theorem purifiedDistance_comm (ρ σ : State a) :
    σ.purifiedDistance ρ = ρ.purifiedDistance σ := by
  rw [State.purifiedDistance_eq, State.purifiedDistance_eq,
    squaredFidelity_comm_of_uhlmann σ ρ]

/-- Any two purifications give an upper bound on the purified distance of
their reduced states. -/
theorem purifiedDistance_le_sqrt_one_sub_overlapSq_of_purifies
    {r : Type v} [Fintype r] [DecidableEq r]
    {ρ σ : State a} {Ψ Φ : PureVector (Prod r a)}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies σ) :
    ρ.purifiedDistance σ ≤ Real.sqrt (1 - Ψ.overlapSq Φ) := by
  rw [State.purifiedDistance_eq]
  exact Real.sqrt_le_sqrt (by
    have hF := PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ
    linarith)

/-- Uhlmann's theorem, phrased directly for purified distance: for a fixed
purification of `ρ` on a large enough reference, one can choose a purification
of `σ` whose pure overlap realizes the purified distance. -/
theorem exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
    {r : Type v} [Fintype r] [DecidableEq r]
    {ρ σ : State a} {Ψ : PureVector (Prod r a)}
    (hΨ : Ψ.Purifies ρ) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ Φ : PureVector (Prod r a),
      Φ.Purifies σ ∧
        ρ.purifiedDistance σ = Real.sqrt (1 - Ψ.overlapSq Φ) := by
  obtain ⟨Φ, hΦ, hΦeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := ρ) (σ := σ) hΨ hcard
  refine ⟨Φ, hΦ, ?_⟩
  rw [State.purifiedDistance_eq, hΦeq]

/-- Purified distance satisfies the triangle inequality on normalized finite
states. -/
theorem purifiedDistance_triangle (ρ σ τ : State a) :
    ρ.purifiedDistance τ ≤ ρ.purifiedDistance σ + σ.purifiedDistance τ := by
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  obtain ⟨Φ, hΦ, hρσ⟩ :=
    exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
      (ρ := ρ) (σ := σ) hΨ (le_refl (Fintype.card a))
  obtain ⟨Ω, hΩ, hστ⟩ :=
    exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
      (ρ := σ) (σ := τ) hΦ (le_refl (Fintype.card a))
  calc
    ρ.purifiedDistance τ ≤ Real.sqrt (1 - Ψ.overlapSq Ω) :=
      purifiedDistance_le_sqrt_one_sub_overlapSq_of_purifies hΨ hΩ
    _ ≤ Real.sqrt (1 - Ψ.overlapSq Φ) +
          Real.sqrt (1 - Φ.overlapSq Ω) :=
      PureVector.sqrt_one_sub_overlapSq_triangle Ψ Φ Ω
    _ = ρ.purifiedDistance σ + σ.purifiedDistance τ := by
      rw [← hρσ, ← hστ]

end State

namespace PureVector

/-- The squared overlap of two pure vectors is bounded by the squared fidelity
of their rank-one states. -/
theorem overlapSq_le_state_squaredFidelity (Ψ Φ : PureVector a) :
    Ψ.overlapSq Φ ≤ Ψ.state.squaredFidelity Φ.state := by
  classical
  let e : a ≃ Prod PUnit.{u + 1} a := (Equiv.punitProd a).symm
  let Ψ' : PureVector (Prod PUnit.{u + 1} a) := Ψ.reindex e
  let Φ' : PureVector (Prod PUnit.{u + 1} a) := Φ.reindex e
  have hΨm : Ψ'.state.marginalB = Ψ.state := by
    apply State.ext
    ext i j
    simp [Ψ', e, PureVector.reindex_state, State.reindex, State.marginalB,
      partialTraceA, PureVector.state_matrix, rankOneMatrix_apply]
  have hΦm : Φ'.state.marginalB = Φ.state := by
    apply State.ext
    ext i j
    simp [Φ', e, PureVector.reindex_state, State.reindex, State.marginalB,
      partialTraceA, PureVector.state_matrix, rankOneMatrix_apply]
  have hΨpur : Ψ'.Purifies Ψ.state := by
    simpa [hΨm] using PureVector.purifies_marginalB Ψ'
  have hΦpur : Φ'.Purifies Φ.state := by
    simpa [hΦm] using PureVector.purifies_marginalB Φ'
  have hbound := PureVector.overlapSq_le_squaredFidelity_of_purifies hΨpur hΦpur
  simpa [Ψ', Φ', e, PureVector.overlapSq_reindex] using hbound

end PureVector

namespace State

variable {b : Type v} [Fintype b] [DecidableEq b]

variable {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]

/-! ## Conditioning-register isometries -/

/-- Apply a finite reference isometry to the conditioning/right register of a
state on `A × B`. -/
def conditioningIsometryApply (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    State (Prod a bPlus) where
  matrix := V.applyMatrixRight ρ.matrix
  pos := by
    rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
      (a := a) V ρ.matrix]
    exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V))
      (MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V))
      ρ.matrix ρ.pos
  trace_eq_one := by
    rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
      (a := a) V ρ.matrix]
    have hTP := MatrixMap.isTracePreserving_kron (Channel.idChannel a).map
      (MatrixMap.ofReferenceIsometry V)
      (Channel.idChannel a).tracePreserving
      (MatrixMap.ofReferenceIsometry_isTracePreserving V)
    rw [hTP ρ.matrix, ρ.trace_eq_one]

@[simp]
theorem conditioningIsometryApply_matrix (ρ : State (Prod a b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).matrix = V.applyMatrixRight ρ.matrix :=
  rfl

theorem conditioningIsometryApply_matrix_eq_kronecker_conj
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).matrix =
      Matrix.kronecker (1 : CMatrix a) V.matrix * ρ.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) := by
  ext x y
  simp [conditioningIsometryApply_matrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.rightBlock, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_kronecker,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_ite_eq', apply_ite, mul_assoc, mul_comm]

theorem conditioningIsometryApply_marginalA (ρ : State (Prod a b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).marginalA = ρ.marginalA := by
  apply State.ext
  rw [State.marginalA_matrix, State.marginalA_matrix, conditioningIsometryApply_matrix]
  exact V.partialTraceB_applyMatrixRight ρ.matrix

theorem conditioningIsometryApply_marginalB_matrix (ρ : State (Prod a b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).marginalB.matrix =
      V.matrix * ρ.marginalB.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalB_matrix, State.marginalB_matrix, conditioningIsometryApply_matrix]
  exact V.partialTraceA_applyMatrixRight ρ.matrix

/-- The support isometry of a PSD right-register reference, as a
`ReferenceIsometry` from the compressed support register into the original
right register. -/
noncomputable def psdSupportReferenceIsometry
    (N : CMatrix b) (hN : N.PosSemidef) :
    ReferenceIsometry (psdSupportIndex N hN) b where
  matrix := psdSupportIsometry N hN
  isometry := psdSupportIsometry_isometry N hN

/-- Compress the right register of a bipartite matrix to the positive spectral
support of a PSD right-register reference. -/
noncomputable def psdSupportCompressRight
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (Prod a b)) :
    CMatrix (Prod a (psdSupportIndex N hN)) :=
  fun x y =>
    (Matrix.conjTranspose (psdSupportIsometry N hN) *
      ReferenceIsometry.rightBlock X x.1 y.1 *
      psdSupportIsometry N hN) x.2 y.2

theorem psdSupportCompressRight_eq_conj
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (Prod a b)) :
    psdSupportCompressRight (a := a) N hN X =
      Matrix.conjTranspose
        (Matrix.kronecker (1 : CMatrix a) (psdSupportIsometry N hN)) *
        X * Matrix.kronecker (1 : CMatrix a) (psdSupportIsometry N hN) := by
  classical
  ext x y
  simp [psdSupportCompressRight, ReferenceIsometry.rightBlock, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_ite_eq',
    apply_ite]

omit [DecidableEq a] in
theorem partialTraceA_psdSupportCompressRight
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (Prod a b)) :
    partialTraceA (a := a) (b := psdSupportIndex N hN)
        (psdSupportCompressRight (a := a) N hN X) =
      psdSupportCompress N hN (partialTraceA (a := a) (b := b) X) := by
  classical
  ext i j
  simp [partialTraceA, psdSupportCompressRight, psdSupportCompress,
    ReferenceIsometry.rightBlock, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  have hswap_outer :
      (∑ x : a, ∑ y : b, ∑ i₁ : b,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j) =
        ∑ y : b, ∑ x : a, ∑ i₁ : b,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j := by
    simpa using
      (Finset.sum_comm
        (s := (Finset.univ : Finset a)) (t := (Finset.univ : Finset b))
        (β := ℂ)
        (f := fun (x : a) (y : b) =>
          ∑ i₁ : b, (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j))
  have hswap_inner :
      (∑ y : b, ∑ x : a, ∑ i₁ : b,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j) =
        ∑ y : b, ∑ i₁ : b, ∑ x : a,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j := by
    refine Finset.sum_congr rfl fun (y : b) _ => ?_
    simpa using
      (Finset.sum_comm
        (s := (Finset.univ : Finset a)) (t := (Finset.univ : Finset b))
        (β := ℂ)
        (f := fun (x : a) (i₁ : b) =>
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j))
  rw [hswap_outer, hswap_inner]

/-- A bipartite state is supported by the identity tensor its right marginal. -/
theorem matrix_supports_identityTensor_marginalB (ρ : State (Prod a b)) :
    Matrix.Supports ρ.matrix
      (Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix) := by
  classical
  have hρ : Matrix.Supports ρ.matrix (ρ.marginalA.prod ρ.marginalB).matrix :=
    ρ.matrix_supports_prod_marginals
  have hprod :
      Matrix.Supports (ρ.marginalA.prod ρ.marginalB).matrix
        (Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix) := by
    intro v hv
    let L : CMatrix (Prod a b) :=
      Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix
    let K : CMatrix (Prod a b) :=
      Matrix.kronecker ρ.marginalA.matrix (1 : CMatrix b)
    have hfactor : (ρ.marginalA.prod ρ.marginalB).matrix = K * L := by
      change Matrix.kronecker ρ.marginalA.matrix ρ.marginalB.matrix = K * L
      simpa [K, L] using
        (Matrix.mul_kronecker_mul ρ.marginalA.matrix (1 : CMatrix a)
          (1 : CMatrix b) ρ.marginalB.matrix)
    calc
      Matrix.mulVec (ρ.marginalA.prod ρ.marginalB).matrix v =
          Matrix.mulVec (K * L) v := by rw [hfactor]
      _ = Matrix.mulVec K (Matrix.mulVec L v) := by
          rw [Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [show Matrix.mulVec L v = 0 from by simpa [L] using hv]
          simp
  exact Matrix.Supports.trans hρ hprod

/-- Every fixed right-register block of a bipartite state is supported by the
right marginal. -/
theorem rightBlock_supports_marginalB
    (ρ : State (Prod a b)) (x y : a) :
    Matrix.Supports (ReferenceIsometry.rightBlock ρ.matrix x y)
      ρ.marginalB.matrix := by
  classical
  intro v hv
  let w : Prod a b → ℂ := fun z => if z.1 = y then v z.2 else 0
  have hNw :
      Matrix.mulVec (Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix) w = 0 := by
    ext z
    by_cases hzy : z.1 = y
    ·
      simpa [w, Matrix.mulVec, dotProduct, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Finset.sum_ite_eq', hzy] using congrFun hv z.2
    · simp [w, Matrix.mulVec, dotProduct, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Finset.sum_ite_eq', hzy]
  have hSupport := matrix_supports_identityTensor_marginalB (a := a) (b := b) ρ
  have hMw := hSupport w hNw
  ext k
  have hk := congrFun hMw (x, k)
  simpa [ReferenceIsometry.rightBlock, Matrix.mulVec, dotProduct, w,
    Fintype.sum_prod_type, Finset.sum_ite_eq'] using hk

theorem rightBlock_conjTranspose
    (ρ : State (Prod a b)) (x y : a) :
    Matrix.conjTranspose (ReferenceIsometry.rightBlock ρ.matrix x y) =
      ReferenceIsometry.rightBlock ρ.matrix y x := by
  ext i j
  have h := congrFun (congrFun ρ.pos.isHermitian.eq (y, i)) (x, j)
  simpa [ReferenceIsometry.rightBlock, Matrix.conjTranspose_apply] using h

/-- Compress a bipartite state to the positive spectral support of its right
marginal. -/
noncomputable def conditioningSupportCompressedState
    (ρ : State (Prod a b)) :
    State (Prod a (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos)) where
  matrix :=
    psdSupportCompressRight (a := a) ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix
  pos := by
    rw [psdSupportCompressRight_eq_conj]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same ρ.pos
      (Matrix.kronecker (1 : CMatrix a)
        (psdSupportIsometry ρ.marginalB.matrix ρ.marginalB.pos))
  trace_eq_one := by
    let X : CMatrix (Prod a (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos)) :=
      psdSupportCompressRight (a := a) ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix
    calc
      X.trace =
          (partialTraceA (a := a)
            (b := psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) X).trace := by
          rw [partialTraceA_trace]
      _ = (psdSupportCompress ρ.marginalB.matrix ρ.marginalB.pos
            ρ.marginalB.matrix).trace := by
          rw [partialTraceA_psdSupportCompressRight]
          simp
      _ = ρ.marginalB.matrix.trace := by
          rw [psdSupportCompress_trace_self]
      _ = 1 := ρ.marginalB.trace_eq_one

@[simp]
theorem conditioningSupportCompressedState_matrix
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.matrix =
      psdSupportCompressRight (a := a)
        ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix := rfl

@[simp]
theorem conditioningSupportCompressedState_marginalB_matrix
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.marginalB.matrix =
      psdSupportCompress ρ.marginalB.matrix ρ.marginalB.pos
        ρ.marginalB.matrix := by
  change partialTraceA
      (psdSupportCompressRight (a := a)
        ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix) =
      psdSupportCompress ρ.marginalB.matrix ρ.marginalB.pos
        ρ.marginalB.matrix
  rw [partialTraceA_psdSupportCompressRight]
  rfl

theorem conditioningSupportCompressedState_marginalB_posDef
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.marginalB.matrix.PosDef := by
  rw [conditioningSupportCompressedState_marginalB_matrix]
  exact psdSupportCompress_self_posDef ρ.marginalB.matrix ρ.marginalB.pos

@[simp]
theorem conditioningSupportCompressedState_conditioningIsometryApply
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.conditioningIsometryApply
      (psdSupportReferenceIsometry ρ.marginalB.matrix ρ.marginalB.pos) = ρ := by
  apply State.ext
  ext x y
  let N : CMatrix b := ρ.marginalB.matrix
  let hN : N.PosSemidef := ρ.marginalB.pos
  let B : CMatrix b := ReferenceIsometry.rightBlock ρ.matrix x.1 y.1
  have hB : Matrix.Supports B N := by
    simpa [B, N] using rightBlock_supports_marginalB (a := a) (b := b) ρ x.1 y.1
  have hBstar : Matrix.Supports (Matrix.conjTranspose B) N := by
    rw [show Matrix.conjTranspose B =
        ReferenceIsometry.rightBlock ρ.matrix y.1 x.1 from by
      simpa [B] using rightBlock_conjTranspose (a := a) (b := b) ρ x.1 y.1]
    simpa [N] using rightBlock_supports_marginalB (a := a) (b := b) ρ y.1 x.1
  have hrec :=
    psdSupportCompress_reconstruct_of_supports_right_and_conjTranspose
      (M := B) (N := N) hN hB hBstar
  have hentry := congrFun (congrFun hrec x.2) y.2
  simpa [conditioningIsometryApply_matrix, ReferenceIsometry.applyMatrixRight,
    conditioningSupportCompressedState_matrix, psdSupportReferenceIsometry,
    psdSupportCompressRight, ReferenceIsometry.rightBlock, psdSupportCompress,
    B, N, hN] using hentry

/-- Purified distance cannot increase after tracing out the second subsystem. -/
theorem purifiedDistance_marginalA_le [Nonempty b]
    (ρ σ : State (Prod a b)) :
    ρ.marginalA.purifiedDistance σ.marginalA ≤ ρ.purifiedDistance σ :=
  purifiedDistance_le_of_squaredFidelity_le
    (State.squaredFidelity_le_marginalA_squaredFidelity ρ σ)

/-- Purified distance cannot increase after tracing out the first subsystem. -/
theorem purifiedDistance_marginalB_le [Nonempty a]
    (ρ σ : State (Prod a b)) :
    ρ.marginalB.purifiedDistance σ.marginalB ≤ ρ.purifiedDistance σ :=
  purifiedDistance_le_of_squaredFidelity_le
    (State.squaredFidelity_le_marginalB_squaredFidelity ρ σ)

/-- Taking the first marginal transports purified-distance balls. -/
theorem purifiedBall_marginalA_of_purifiedBall [Nonempty b]
    {ρ σ : State (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε σ) :
    ρ.marginalA.purifiedBall ε σ.marginalA :=
  le_trans (purifiedDistance_marginalA_le ρ σ) hball

/-- Taking the second marginal transports purified-distance balls. -/
theorem purifiedBall_marginalB_of_purifiedBall [Nonempty a]
    {ρ σ : State (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε σ) :
    ρ.marginalB.purifiedBall ε σ.marginalB :=
  le_trans (purifiedDistance_marginalB_le ρ σ) hball

end State

variable {b : Type v} [Fintype b] [DecidableEq b]

namespace State

variable {b : Type v} [Fintype b] [DecidableEq b]

/-! ## Embedded complementary purification transport -/

variable {c : Type w} [Fintype c] [DecidableEq c]

/-- Reindex a purification of an `AB` target so that the discarded `B` system
is the reference and the kept target is `AC`. -/
def abToACReferenceEquiv (c a b : Type*) :
    Prod c (Prod a b) ≃ Prod b (Prod a c) where
  toFun x := (x.2.2, (x.2.1, x.1))
  invFun x := (x.2.2, (x.2.1, x.1))
  left_inv x := by
    cases x with
    | mk z xy =>
      cases xy
      rfl
  right_inv x := by
    cases x with
    | mk y xz =>
      cases xz
      rfl

/-- Reindex a purification of an `AC` target so that the discarded `C` system
is the reference and the kept target is `AB`. -/
def acToABReferenceEquiv (b a c : Type*) :
    Prod b (Prod a c) ≃ Prod c (Prod a b) where
  toFun x := (x.2.2, (x.2.1, x.1))
  invFun x := (x.2.2, (x.2.1, x.1))
  left_inv x := by
    cases x with
    | mk y xz =>
      cases xz
      rfl
  right_inv x := by
    cases x with
    | mk z xy =>
      cases xy
      rfl

/-- The `AB` marginal of a purification whose reference is `C`. -/
def abMarginalFromTripartitePure (Ψ : PureVector (Prod c (Prod a b))) :
    State (Prod a b) :=
  Ψ.state.marginalB

/-- The complementary `AC` marginal of a purification of an `AB` target. -/
def acMarginalFromABPurification (Ψ : PureVector (Prod c (Prod a b))) :
    State (Prod a c) :=
  (Ψ.reindex (abToACReferenceEquiv c a b)).state.marginalB

/-- The complementary `AB` marginal of a purification of an `AC` target. -/
def abMarginalFromACPurification (Ψ : PureVector (Prod b (Prod a c))) :
    State (Prod a b) :=
  (Ψ.reindex (acToABReferenceEquiv b a c)).state.marginalB

/-- An `AB` smooth candidate has an embedded complementary `AC⁺` candidate when
both arise from nearby purifications after embedding the original `C` reference
into the enlarged register `C⁺ = (A × B) ⊕ C`. -/
def EmbeddedABToACSmoothCandidate
    (Ψ : PureVector (Prod c (Prod a b))) (ε : ℝ)
    (ρAB' : State (Prod a b)) : Prop :=
  ∃ Φ : PureVector (Prod (Sum (Prod a b) c) (Prod a b)),
    Φ.Purifies ρAB' ∧
      (acMarginalFromABPurification
        ((ReferenceIsometry.sumInr (Prod a b) c).applyPureVector Ψ)).purifiedBall ε
        (acMarginalFromABPurification Φ)

/-- An `AC` smooth candidate has an embedded complementary `AB⁺` candidate when
both arise from nearby purifications after embedding the original `B` reference
into the enlarged register `B⁺ = (A × C) ⊕ B`. -/
def EmbeddedACToABSmoothCandidate
    (Ψ : PureVector (Prod c (Prod a b))) (ε : ℝ)
    (ρAC' : State (Prod a c)) : Prop :=
  let Ω : PureVector (Prod b (Prod a c)) :=
    Ψ.reindex (abToACReferenceEquiv c a b)
  ∃ Φ : PureVector (Prod (Sum (Prod a c) b) (Prod a c)),
    Φ.Purifies ρAC' ∧
      (abMarginalFromACPurification
        ((ReferenceIsometry.sumInr (Prod a c) b).applyPureVector Ω)).purifiedBall ε
        (abMarginalFromACPurification Φ)

/-- Embedded purification-ball transport for smooth min/max candidate pairing.

This is the mathematically correct finite-dimensional replacement for a fixed
`B/C` pairing: smoothed candidates are paired after enlarging the complementary
reference register when necessary. -/
def EmbeddedSmoothConditionalMinMaxPairing
    (Ψ : PureVector (Prod c (Prod a b))) (ε : ℝ) : Prop :=
  (∀ ρAB' : State (Prod a b),
      (abMarginalFromTripartitePure Ψ).purifiedBall ε ρAB' →
        EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c) Ψ ε ρAB') ∧
    (∀ ρAC' : State (Prod a c),
      (acMarginalFromABPurification Ψ).purifiedBall ε ρAC' →
        EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c) Ψ ε ρAC')

private theorem card_prod_le_sum_prod_left
    {x y : Type*} [Fintype x] [Fintype y] [DecidableEq x] [DecidableEq y] :
    Fintype.card x ≤ Fintype.card (Sum x y) := by
  simp [Fintype.card_sum]

/-- Pure-state overlap equality plus arbitrary-purification Uhlmann gives the
purified-ball transport for the `AB → AC⁺` direction. -/
private theorem embeddedABToAC_of_purifiedBall
    (Ψ : PureVector (Prod c (Prod a b))) {ε : ℝ}
    {ρAB' : State (Prod a b)}
    (hball : (abMarginalFromTripartitePure Ψ).purifiedBall ε ρAB') :
    EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c) Ψ ε ρAB' := by
  classical
  let V := ReferenceIsometry.sumInr (Prod a b) c
  let Ψplus : PureVector (Prod (Sum (Prod a b) c) (Prod a b)) :=
    V.applyPureVector Ψ
  have hΨ : Ψ.Purifies (abMarginalFromTripartitePure Ψ) := by
    exact PureVector.purifies_marginalB Ψ
  have hΨplus : Ψplus.Purifies (abMarginalFromTripartitePure Ψ) := by
    exact V.applyPureVector_purifies hΨ
  have hcard : Fintype.card (Prod a b) ≤ Fintype.card (Sum (Prod a b) c) := by
    exact card_prod_le_sum_prod_left (x := Prod a b) (y := c)
  obtain ⟨Φ, hΦ, hoverlap⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := Ψplus) (ρ := abMarginalFromTripartitePure Ψ) (σ := ρAB')
      hΨplus hcard
  refine ⟨Φ, hΦ, ?_⟩
  let e := abToACReferenceEquiv (Sum (Prod a b) c) a b
  have hbasePur :
      (Ψplus.reindex e).Purifies
        (acMarginalFromABPurification Ψplus) := by
    exact PureVector.purifies_marginalB (Ψplus.reindex e)
  have hcandPur :
      (Φ.reindex e).Purifies
        (acMarginalFromABPurification Φ) := by
    exact PureVector.purifies_marginalB (Φ.reindex e)
  have hF :
      (abMarginalFromTripartitePure Ψ).squaredFidelity ρAB' ≤
        (acMarginalFromABPurification Ψplus).squaredFidelity
          (acMarginalFromABPurification Φ) := by
    have hbound :=
      PureVector.overlapSq_le_squaredFidelity_of_purifies hbasePur hcandPur
    rw [PureVector.overlapSq_reindex, hoverlap] at hbound
    exact hbound
  exact purifiedBall_of_squaredFidelity_le hF hball

/-- Pure-state overlap equality plus arbitrary-purification Uhlmann gives the
purified-ball transport for the `AC → AB⁺` direction. -/
private theorem embeddedACToAB_of_purifiedBall
    (Ψ : PureVector (Prod c (Prod a b))) {ε : ℝ}
    {ρAC' : State (Prod a c)}
    (hball : (acMarginalFromABPurification Ψ).purifiedBall ε ρAC') :
    EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c) Ψ ε ρAC' := by
  classical
  let Ω : PureVector (Prod b (Prod a c)) :=
    Ψ.reindex (abToACReferenceEquiv c a b)
  let V := ReferenceIsometry.sumInr (Prod a c) b
  let Ωplus : PureVector (Prod (Sum (Prod a c) b) (Prod a c)) :=
    V.applyPureVector Ω
  have hΩ : Ω.Purifies (acMarginalFromABPurification Ψ) := by
    exact PureVector.purifies_marginalB Ω
  have hΩplus : Ωplus.Purifies (acMarginalFromABPurification Ψ) := by
    exact V.applyPureVector_purifies hΩ
  have hcard : Fintype.card (Prod a c) ≤ Fintype.card (Sum (Prod a c) b) := by
    exact card_prod_le_sum_prod_left (x := Prod a c) (y := b)
  obtain ⟨Φ, hΦ, hoverlap⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := Ωplus) (ρ := acMarginalFromABPurification Ψ) (σ := ρAC')
      hΩplus hcard
  refine ⟨Φ, hΦ, ?_⟩
  let e := acToABReferenceEquiv (Sum (Prod a c) b) a c
  have hbasePur :
      (Ωplus.reindex e).Purifies
        (abMarginalFromACPurification Ωplus) := by
    exact PureVector.purifies_marginalB (Ωplus.reindex e)
  have hcandPur :
      (Φ.reindex e).Purifies
        (abMarginalFromACPurification Φ) := by
    exact PureVector.purifies_marginalB (Φ.reindex e)
  have hF :
      (acMarginalFromABPurification Ψ).squaredFidelity ρAC' ≤
        (abMarginalFromACPurification Ωplus).squaredFidelity
          (abMarginalFromACPurification Φ) := by
    have hbound :=
      PureVector.overlapSq_le_squaredFidelity_of_purifies hbasePur hcandPur
    rw [PureVector.overlapSq_reindex, hoverlap] at hbound
    exact hbound
  exact purifiedBall_of_squaredFidelity_le hF hball

/-- Embedded purification-ball transport for a pure tripartite state.

The theorem deliberately uses enlarged complementary references (`C⁺` and
`B⁺`) rather than asserting a generally false fixed-register pairing. -/
theorem embeddedSmoothConditionalMinMaxPairing_of_pure
    (Ψ : PureVector (Prod c (Prod a b))) (ε : ℝ) :
    EmbeddedSmoothConditionalMinMaxPairing (a := a) (b := b) (c := c) Ψ ε := by
  constructor
  · intro ρAB' hball
    exact embeddedABToAC_of_purifiedBall Ψ hball
  · intro ρAC' hball
    exact embeddedACToAB_of_purifiedBall Ψ hball

/-! ## Complementary pure-marginal relation -/

/-- Two bipartite states are complementary pure marginals when they arise from
one pure state on `C × (A × B)`: the first is the `AB` target marginal and the
second is the complementary `AC` marginal. -/
def ComplementaryPureMarginalRel
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) : Prop :=
  ∃ Ψ : PureVector (Prod c (Prod a b)),
    Ψ.Purifies ρAB ∧ acMarginalFromABPurification Ψ = ρAC

theorem complementaryPureMarginalRel_of_pure
    (Ψ : PureVector (Prod c (Prod a b))) :
    ComplementaryPureMarginalRel (a := a) (b := b) (c := c)
      (abMarginalFromTripartitePure Ψ) (acMarginalFromABPurification Ψ) := by
  exact ⟨Ψ, PureVector.purifies_marginalB Ψ, rfl⟩

/-- An embedded `AB` smooth candidate gives a concrete enlarged complementary
pure-marginal candidate. This is the relation-level handoff from purification
transport to the unsmoothed min/max duality leaf. -/
theorem EmbeddedABToACSmoothCandidate.exists_complementaryPureMarginalRel
    {Ψ : PureVector (Prod c (Prod a b))} {ε : ℝ}
    {ρAB' : State (Prod a b)}
    (h : EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c) Ψ ε ρAB') :
    ∃ ρACplus' : State (Prod a (Sum (Prod a b) c)),
      (acMarginalFromABPurification
        ((ReferenceIsometry.sumInr (Prod a b) c).applyPureVector Ψ)).purifiedBall ε
        ρACplus' ∧
      ComplementaryPureMarginalRel (a := a) (b := b) (c := Sum (Prod a b) c)
        ρAB' ρACplus' := by
  rcases h with ⟨Φ, hΦ, hball⟩
  refine ⟨acMarginalFromABPurification Φ, hball, ?_⟩
  exact ⟨Φ, hΦ, rfl⟩

/-! ## Normalized/subnormalized purified-distance bridge -/

/-- Generalized fidelity reduces to squared fidelity for normalized states. -/
theorem toSubnormalized_generalizedFidelity_eq_squaredFidelity (ρ σ : State a) :
    ρ.toSubnormalized.generalizedFidelity σ.toSubnormalized = ρ.squaredFidelity σ := by
  rw [SubnormalizedState.generalizedFidelity_eq,
    State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  have hρ : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hσ : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  simp [State.sqrtMatrix, hρ, hσ]

/-- The subnormalized purified distance agrees with the normalized one after
embedding normalized states via `State.toSubnormalized`. -/
theorem toSubnormalized_purifiedDistance_eq (ρ σ : State a) :
    ρ.toSubnormalized.purifiedDistance σ.toSubnormalized = ρ.purifiedDistance σ := by
  rw [SubnormalizedState.purifiedDistance_eq, State.purifiedDistance_eq,
    toSubnormalized_generalizedFidelity_eq_squaredFidelity]

end State

/-- Subnormalized purified distance agrees with normalized purified distance
after adjoining the one-dimensional failure register in the hat extension.
This is the purified-distance specialization of Tomamichel's hat route from
`metric.tex`, lines 512-513 and 584-604. -/
theorem SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
    (ρ σ : SubnormalizedState a) :
    ρ.purifiedDistance σ =
      ρ.hatExtension.purifiedDistance σ.hatExtension := by
  rw [SubnormalizedState.purifiedDistance_eq, State.purifiedDistance_eq,
    SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension]

/-- Subnormalized purified balls are exactly normalized purified balls after
hat extension. -/
theorem SubnormalizedState.purifiedBall_iff_hatExtension_purifiedBall
    (ρ σ : SubnormalizedState a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔ ρ.hatExtension.purifiedBall ε σ.hatExtension := by
  rw [SubnormalizedState.purifiedBall_eq, State.purifiedBall_eq,
    SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension]

/-- Hat extension is injective on subnormalized states. -/
theorem SubnormalizedState.eq_of_hatExtension_eq {ρ σ : SubnormalizedState a}
    (h : ρ.hatExtension = σ.hatExtension) :
    ρ = σ := by
  apply SubnormalizedState.ext
  ext i j
  have hmatrix := congrArg State.matrix h
  have hentry :
      ρ.hatExtension.matrix (Sum.inr i) (Sum.inr j) =
        σ.hatExtension.matrix (Sum.inr i) (Sum.inr j) := by
    rw [hmatrix]
  simpa [SubnormalizedState.hatExtension_matrix,
    SubnormalizedState.hatExtensionMatrix_state_state] using hentry

/-- Subnormalized purified distance is symmetric via the normalized
hat-extension bridge. -/
theorem SubnormalizedState.purifiedDistance_comm
    (ρ σ : SubnormalizedState a) :
    σ.purifiedDistance ρ = ρ.purifiedDistance σ := by
  let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{u + 1} a) := σ.hatExtension
  have hσρ : σ.purifiedDistance ρ = σhat.purifiedDistance ρhat := by
    simpa [σhat, ρhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) σ ρ)
  have hρσ : ρ.purifiedDistance σ = ρhat.purifiedDistance σhat := by
    simpa [ρhat, σhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) ρ σ)
  rw [hσρ, hρσ, State.purifiedDistance_comm ρhat σhat]

/-- Subnormalized purified distance satisfies the triangle inequality via the
normalized hat-extension bridge. -/
theorem SubnormalizedState.purifiedDistance_triangle
    (ρ σ τ : SubnormalizedState a) :
    ρ.purifiedDistance τ ≤ ρ.purifiedDistance σ + σ.purifiedDistance τ := by
  let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{u + 1} a) := σ.hatExtension
  let τhat : State (Sum PUnit.{u + 1} a) := τ.hatExtension
  have hρτ : ρ.purifiedDistance τ = ρhat.purifiedDistance τhat := by
    simpa [ρhat, τhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) ρ τ)
  have hρσ : ρ.purifiedDistance σ = ρhat.purifiedDistance σhat := by
    simpa [ρhat, σhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) ρ σ)
  have hστ : σ.purifiedDistance τ = σhat.purifiedDistance τhat := by
    simpa [σhat, τhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) σ τ)
  rw [hρτ, hρσ, hστ]
  exact State.purifiedDistance_triangle ρhat σhat τhat

/-- Moving the center of a subnormalized purified ball only increases the
radius by the purified distance between the old and new centers. -/
theorem SubnormalizedState.purifiedBall_center_migration
    {ρ η τ : SubnormalizedState a} {ε δ : ℝ}
    (hcenter : η.purifiedDistance ρ ≤ δ)
    (hwit : η.purifiedBall ε τ) :
    ρ.purifiedBall (ε + δ) τ := by
  rw [SubnormalizedState.purifiedBall_eq] at hwit ⊢
  have hρη : ρ.purifiedDistance η ≤ δ := by
    rw [SubnormalizedState.purifiedDistance_comm ρ η] at hcenter
    exact hcenter
  have htri := SubnormalizedState.purifiedDistance_triangle ρ η τ
  linarith

/-- Normalized-center convenience wrapper for migrating a subnormalized
purified ball after embedding normalized states. -/
theorem State.toSubnormalized_purifiedBall_center_migration
    {ρ η : State a} {τ : SubnormalizedState a} {ε δ : ℝ}
    (hcenter : η.toSubnormalized.purifiedDistance ρ.toSubnormalized ≤ δ)
    (hwit : η.toSubnormalized.purifiedBall ε τ) :
    ρ.toSubnormalized.purifiedBall (ε + δ) τ :=
  SubnormalizedState.purifiedBall_center_migration hcenter hwit

/-- Trace-nonincreasing completely positive maps increase generalized fidelity
between subnormalized states. This is Tomamichel's hat-extension route for
purified-distance monotonicity, using the completed channel on failure
registers. -/
theorem SubnormalizedState.generalizedFidelity_le_applyTraceNonincreasingCP
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : SubnormalizedState a) (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    ρ.generalizedFidelity σ ≤
      (ρ.applyTraceNonincreasingCP Φ hΦ).generalizedFidelity
        (σ.applyTraceNonincreasingCP Φ hΦ) := by
  let τ : SubnormalizedState b := ρ.applyTraceNonincreasingCP Φ hΦ
  let υ : SubnormalizedState b := σ.applyTraceNonincreasingCP Φ hΦ
  let ρhat : State (Sum PUnit.{max u v + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{max u v + 1} a) := σ.hatExtension
  let τhat : State (Sum PUnit.{max u v + 1} b) := τ.hatExtension
  let υhat : State (Sum PUnit.{max u v + 1} b) := υ.hatExtension
  have hρF : ρ.generalizedFidelity σ = ρhat.squaredFidelity σhat := by
    simpa [ρhat, σhat] using
      (SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension ρ σ)
  have hτF : τ.generalizedFidelity υ = τhat.squaredFidelity υhat := by
    simpa [τhat, υhat] using
      (SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension τ υ)
  have hτhat : τhat = hΦ.hatCompletion.applyState ρhat := by
    simpa [τ, τhat, ρhat] using
      (SubnormalizedState.hatExtension_applyTraceNonincreasingCP ρ Φ hΦ)
  have hυhat : υhat = hΦ.hatCompletion.applyState σhat := by
    simpa [υ, υhat, σhat] using
      (SubnormalizedState.hatExtension_applyTraceNonincreasingCP σ Φ hΦ)
  rw [hρF]
  change τ.generalizedFidelity υ = _ at hτF
  rw [hτF, hτhat, hυhat]
  exact State.squaredFidelity_le_applyState_squaredFidelity hΦ.hatCompletion ρhat σhat

/-- Purified distance is monotone under trace-nonincreasing completely positive
maps between subnormalized states. -/
theorem SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : SubnormalizedState a) (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    (ρ.applyTraceNonincreasingCP Φ hΦ).purifiedDistance
        (σ.applyTraceNonincreasingCP Φ hΦ) ≤
      ρ.purifiedDistance σ := by
  let τ : SubnormalizedState b := ρ.applyTraceNonincreasingCP Φ hΦ
  let υ : SubnormalizedState b := σ.applyTraceNonincreasingCP Φ hΦ
  let ρhat : State (Sum PUnit.{max u v + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{max u v + 1} a) := σ.hatExtension
  let τhat : State (Sum PUnit.{max u v + 1} b) := τ.hatExtension
  let υhat : State (Sum PUnit.{max u v + 1} b) := υ.hatExtension
  have hρP : ρ.purifiedDistance σ = ρhat.purifiedDistance σhat := by
    simpa [ρhat, σhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension ρ σ)
  have hτP : τ.purifiedDistance υ = τhat.purifiedDistance υhat := by
    simpa [τhat, υhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension τ υ)
  have hτhat : τhat = hΦ.hatCompletion.applyState ρhat := by
    simpa [τ, τhat, ρhat] using
      (SubnormalizedState.hatExtension_applyTraceNonincreasingCP ρ Φ hΦ)
  have hυhat : υhat = hΦ.hatCompletion.applyState σhat := by
    simpa [υ, υhat, σhat] using
      (SubnormalizedState.hatExtension_applyTraceNonincreasingCP σ Φ hΦ)
  change τ.purifiedDistance υ ≤ ρ.purifiedDistance σ
  rw [hτP, hρP, hτhat, hυhat]
  exact State.purifiedDistance_le_of_squaredFidelity_le
    (State.squaredFidelity_le_applyState_squaredFidelity hΦ.hatCompletion ρhat σhat)

/-- Trace-nonincreasing completely positive maps transport purified-distance
balls between subnormalized states. -/
theorem SubnormalizedState.purifiedBall_of_traceNonincreasingCP
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : SubnormalizedState a} {ε : ℝ} (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ)
    (hball : ρ.purifiedBall ε σ) :
    (ρ.applyTraceNonincreasingCP Φ hΦ).purifiedBall ε
      (σ.applyTraceNonincreasingCP Φ hΦ) :=
  le_trans (SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP ρ σ Φ hΦ) hball

/-- A subnormalized purified-distance ball of radius smaller than
`sqrt (Tr ρ)` contains only positive-trace witnesses. -/
theorem SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
    (ρ σ : SubnormalizedState a) {ε : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hball : ρ.purifiedBall ε σ) :
    0 < σ.matrix.trace.re := by
  by_contra hnot
  have hσle : σ.matrix.trace.re ≤ 0 := le_of_not_gt hnot
  have hσzero : σ.matrix.trace.re = 0 := le_antisymm hσle σ.trace_nonneg
  have hσtrace : σ.matrix.trace = 0 := by
    apply Complex.ext
    · exact hσzero
    · exact σ.trace_im_zero
  have hσmat : σ.matrix = 0 := (Matrix.PosSemidef.trace_eq_zero_iff σ.pos).mp hσtrace
  have hfid : ρ.generalizedFidelity σ = 1 - ρ.matrix.trace.re := by
    rw [SubnormalizedState.generalizedFidelity_eq]
    rw [hσzero, hσmat]
    simp
    exact Real.sq_sqrt (sub_nonneg.mpr ρ.trace_le_one)
  have hdist : ρ.purifiedDistance σ = Real.sqrt ρ.matrix.trace.re := by
    rw [SubnormalizedState.purifiedDistance_eq, hfid]
    ring_nf
  have hle : Real.sqrt ρ.matrix.trace.re ≤ ε := by
    change ρ.purifiedDistance σ ≤ ε at hball
    rwa [hdist] at hball
  exact (not_lt_of_ge hle) hε

private theorem punit_psdSqrt_const (r : ℝ) (hr : 0 ≤ r) :
    psdSqrt (fun _ _ : PUnit.{u + 1} => ((r : ℝ) : ℂ) : CMatrix PUnit.{u + 1}) =
      (fun _ _ : PUnit.{u + 1} => ((Real.sqrt r : ℝ) : ℂ) :
        CMatrix PUnit.{u + 1}) := by
  let A : CMatrix PUnit.{u + 1} := fun _ _ => ((r : ℝ) : ℂ)
  let S : CMatrix PUnit.{u + 1} := fun _ _ => ((Real.sqrt r : ℝ) : ℂ)
  have hsqrt_sq : ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) = (r : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  have hSsq : S * S = A := by
    ext i j
    cases i
    cases j
    simp [S, A, Matrix.mul_apply, hsqrt_sq]
  have hSpos : S.PosSemidef := by
    have hdiag :
        S = Matrix.diagonal (fun _ : PUnit.{u + 1} => ((Real.sqrt r : ℝ) : ℂ)) := by
      ext i j
      cases i
      cases j
      simp [S, Matrix.diagonal]
    rw [hdiag]
    exact Matrix.PosSemidef.diagonal fun _ =>
      Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg r, by simp⟩
  change psdSqrt A = S
  simpa [psdSqrt] using (CFC.sqrt_unique (a := A) (b := S) hSsq hSpos.nonneg)

private theorem traceNorm_punit_const_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    traceNorm (fun _ _ : PUnit.{u + 1} => ((r : ℝ) : ℂ) :
      CMatrix PUnit.{u + 1}) = r := by
  let A : CMatrix PUnit.{u + 1} := fun _ _ => ((r : ℝ) : ℂ)
  have hgram :
      Aᴴ * A =
        (fun _ _ : PUnit.{u + 1} => ((r * r : ℝ) : ℂ) :
          CMatrix PUnit.{u + 1}) := by
    ext i j
    cases i
    cases j
    simp [A, Matrix.mul_apply, ← Complex.ofReal_mul]
  have hsqrt : psdSqrt (Aᴴ * A) = A := by
    rw [hgram]
    rw [punit_psdSqrt_const (r * r) (mul_self_nonneg r)]
    ext i j
    cases i
    cases j
    simp [A, Real.sqrt_mul_self hr]
  rw [traceNorm, hsqrt]
  simp [A, Matrix.trace]

private theorem punit_subnormalized_matrix_eq_trace
    (ρ : SubnormalizedState PUnit.{u + 1}) :
    ρ.matrix =
      (fun _ _ : PUnit.{u + 1} => ((ρ.matrix.trace.re : ℝ) : ℂ) :
        CMatrix PUnit.{u + 1}) := by
  ext i j
  cases i
  cases j
  apply Complex.ext
  · simp [Matrix.trace]
  · simpa [Matrix.trace] using ρ.trace_im_zero

private theorem punit_generalizedFidelity_eq
    (ρ σ : SubnormalizedState PUnit.{u + 1}) :
    ρ.generalizedFidelity σ =
      (Real.sqrt (ρ.matrix.trace.re * σ.matrix.trace.re) +
        Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re))) ^ 2 := by
  rw [SubnormalizedState.generalizedFidelity_eq]
  rw [punit_subnormalized_matrix_eq_trace ρ, punit_subnormalized_matrix_eq_trace σ]
  rw [punit_psdSqrt_const ρ.matrix.trace.re ρ.trace_nonneg,
    punit_psdSqrt_const σ.matrix.trace.re σ.trace_nonneg]
  let R : CMatrix PUnit.{u + 1} :=
    fun _ _ => ((Real.sqrt ρ.matrix.trace.re : ℝ) : ℂ)
  let S : CMatrix PUnit.{u + 1} :=
    fun _ _ => ((Real.sqrt σ.matrix.trace.re : ℝ) : ℂ)
  change
    (traceNorm (R * S) +
        Real.sqrt ((1 -
            (Matrix.trace
              (fun _ _ : PUnit.{u + 1} => ((ρ.matrix.trace.re : ℝ) : ℂ))).re) *
          (1 -
            (Matrix.trace
              (fun _ _ : PUnit.{u + 1} => ((σ.matrix.trace.re : ℝ) : ℂ))).re))) ^ 2 =
      (Real.sqrt
          ((Matrix.trace
              (fun _ _ : PUnit.{u + 1} => ((ρ.matrix.trace.re : ℝ) : ℂ))).re *
            (Matrix.trace
              (fun _ _ : PUnit.{u + 1} => ((σ.matrix.trace.re : ℝ) : ℂ))).re) +
        Real.sqrt ((1 -
            (Matrix.trace
              (fun _ _ : PUnit.{u + 1} => ((ρ.matrix.trace.re : ℝ) : ℂ))).re) *
          (1 -
            (Matrix.trace
              (fun _ _ : PUnit.{u + 1} => ((σ.matrix.trace.re : ℝ) : ℂ))).re))) ^ 2
  have hprod :
      R * S =
        (fun _ _ : PUnit.{u + 1} =>
          (((Real.sqrt ρ.matrix.trace.re * Real.sqrt σ.matrix.trace.re : ℝ)) : ℂ)) := by
    ext i j
    cases i
    cases j
    simp [R, S, Matrix.mul_apply, ← Complex.ofReal_mul]
  rw [hprod]
  rw [traceNorm_punit_const_of_nonneg
    (Real.sqrt ρ.matrix.trace.re * Real.sqrt σ.matrix.trace.re)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hsqrt_trace :
      Real.sqrt (ρ.matrix.trace.re * σ.matrix.trace.re) =
        Real.sqrt ρ.matrix.trace.re * Real.sqrt σ.matrix.trace.re := by
    exact Real.sqrt_mul ρ.trace_nonneg _
  simp [Matrix.trace]
  have hentry_sqrt :
      Real.sqrt ((ρ.matrix PUnit.unit PUnit.unit).re *
          (σ.matrix PUnit.unit PUnit.unit).re) =
        Real.sqrt (ρ.matrix PUnit.unit PUnit.unit).re *
          Real.sqrt (σ.matrix PUnit.unit PUnit.unit).re := by
    exact Real.sqrt_mul (by simpa [Matrix.trace] using ρ.trace_nonneg) _
  rw [hentry_sqrt]

private theorem scalar_sqrt_trace_sub_le_binary_purified
    {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.sqrt r - Real.sqrt s ≤
      Real.sqrt (1 - (Real.sqrt (r * s) + Real.sqrt ((1 - r) * (1 - s))) ^ 2) := by
  by_cases hrs : Real.sqrt r ≤ Real.sqrt s
  · have hright_nonneg :
        0 ≤ Real.sqrt (1 - (Real.sqrt (r * s) +
          Real.sqrt ((1 - r) * (1 - s))) ^ 2) := Real.sqrt_nonneg _
    linarith
  · have hlt : Real.sqrt s < Real.sqrt r := lt_of_not_ge hrs
    let A := Real.sqrt r
    let B := Real.sqrt s
    let C := Real.sqrt (1 - r)
    let D := Real.sqrt (1 - s)
    have hA0 : 0 ≤ A := Real.sqrt_nonneg r
    have hB0 : 0 ≤ B := Real.sqrt_nonneg s
    have hC0 : 0 ≤ C := Real.sqrt_nonneg (1 - r)
    have hD0 : 0 ≤ D := Real.sqrt_nonneg (1 - s)
    have hC1 : C ≤ 1 := by
      dsimp [C]
      exact Real.sqrt_le_one.mpr (by linarith)
    have hD1 : D ≤ 1 := by
      dsimp [D]
      exact Real.sqrt_le_one.mpr (by linarith)
    have hAB : B < A := by simpa [A, B] using hlt
    have hunitA : A ^ 2 + C ^ 2 = 1 := by
      dsimp [A, C]
      rw [Real.sq_sqrt hr0, Real.sq_sqrt (by linarith : 0 ≤ 1 - r)]
      ring
    have hunitB : B ^ 2 + D ^ 2 = 1 := by
      dsimp [B, D]
      rw [Real.sq_sqrt hs0, Real.sq_sqrt (by linarith : 0 ≤ 1 - s)]
      ring
    have hexpr_nonneg : 0 ≤ A * D - B * C := by
      have hsq_le : B ^ 2 ≤ A ^ 2 := by nlinarith
      have hmul : B * C ≤ A * D := by
        have hright_nonneg : 0 ≤ A * D := mul_nonneg hA0 hD0
        exact le_of_sq_le_sq (by nlinarith) hright_nonneg
      linarith
    have htarget : A - B ≤ A * D - B * C := by
      have hden_pos : 0 < A * D + B * C := by
        by_cases hBz : B = 0
        · subst B
          have hD2 : D ^ 2 = 1 := by nlinarith
          have hDpos : 0 < D := by nlinarith
          nlinarith
        · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBz)
          have hDpos : 0 < D := by
            by_contra hnot
            have hDle : D ≤ 0 := le_of_not_gt hnot
            have hDz : D = 0 := le_antisymm hDle hD0
            subst D
            nlinarith
          nlinarith
      have hden_le : A * D + B * C ≤ A + B := by nlinarith
      have hmul_eq : (A * D - B * C) * (A * D + B * C) = (A - B) * (A + B) := by
        nlinarith
      have htarget_mul :
          (A - B) * (A * D + B * C) ≤ (A - B) * (A + B) := by
        have hABnonneg : 0 ≤ A - B := by linarith
        exact mul_le_mul_of_nonneg_left hden_le hABnonneg
      have hmul_le :
          (A - B) * (A * D + B * C) ≤ (A * D - B * C) * (A * D + B * C) := by
        simpa [hmul_eq] using htarget_mul
      exact le_of_mul_le_mul_right hmul_le hden_pos
    have hpyth :
        1 - (Real.sqrt (r * s) + Real.sqrt ((1 - r) * (1 - s))) ^ 2 =
          (A * D - B * C) ^ 2 := by
      dsimp [A, B, C, D]
      rw [Real.sqrt_mul hr0, Real.sqrt_mul (by linarith : 0 ≤ 1 - r)]
      ring_nf
      rw [Real.sq_sqrt hr0, Real.sq_sqrt hs0,
        Real.sq_sqrt (by linarith : 0 ≤ 1 - r),
        Real.sq_sqrt (by linarith : 0 ≤ 1 - s)]
      ring
    have hdist :
        Real.sqrt (1 - (Real.sqrt (r * s) + Real.sqrt ((1 - r) * (1 - s))) ^ 2) =
          A * D - B * C := by
      rw [hpyth, Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg hexpr_nonneg
    simpa [A, B] using htarget.trans_eq hdist.symm

private theorem punit_sqrt_trace_sub_le_purifiedDistance
    (ρ σ : SubnormalizedState PUnit.{u + 1}) :
    Real.sqrt ρ.matrix.trace.re - Real.sqrt σ.matrix.trace.re ≤
      ρ.purifiedDistance σ := by
  rw [SubnormalizedState.purifiedDistance_eq, punit_generalizedFidelity_eq]
  exact scalar_sqrt_trace_sub_le_binary_purified
    ρ.trace_nonneg ρ.trace_le_one σ.trace_nonneg σ.trace_le_one

private theorem traceEffectToUnit_one_apply_trace
    (ρ : SubnormalizedState a) :
    (ρ.applyTraceNonincreasingCP (MatrixMap.traceEffectToUnit (1 : CMatrix a))
      (MatrixMap.traceEffectToUnit_traceNonincreasingCP Matrix.PosSemidef.one le_rfl)).matrix.trace.re =
        ρ.matrix.trace.re := by
  rw [SubnormalizedState.applyTraceNonincreasingCP_matrix]
  rw [MatrixMap.traceEffectToUnit_apply_of_posSemidef Matrix.PosSemidef.one]
  simp [Matrix.trace]

/-- A subnormalized purified-distance ball with radius below `sqrt (Tr ρ)`
has a uniform trace floor. -/
theorem SubnormalizedState.purifiedBall_trace_lower_bound
    (ρ σ : SubnormalizedState a) {ε : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hball : ρ.purifiedBall ε σ) :
    (Real.sqrt ρ.matrix.trace.re - ε) ^ 2 ≤ σ.matrix.trace.re := by
  let Φ : MatrixMap a PUnit.{u + 1} := MatrixMap.traceEffectToUnit (1 : CMatrix a)
  let hΦ : MatrixMap.TraceNonincreasingCP Φ :=
    MatrixMap.traceEffectToUnit_traceNonincreasingCP Matrix.PosSemidef.one le_rfl
  let τ : SubnormalizedState PUnit.{u + 1} := ρ.applyTraceNonincreasingCP Φ hΦ
  let υ : SubnormalizedState PUnit.{u + 1} := σ.applyTraceNonincreasingCP Φ hΦ
  have hballUnit : τ.purifiedBall ε υ := by
    exact SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ) (σ := σ) Φ hΦ hball
  have hdist_le : τ.purifiedDistance υ ≤ ε := hballUnit
  have hsqrt_le : Real.sqrt ρ.matrix.trace.re - ε ≤ Real.sqrt σ.matrix.trace.re := by
    have hunit := punit_sqrt_trace_sub_le_purifiedDistance τ υ
    have hτtrace : τ.matrix.trace.re = ρ.matrix.trace.re := by
      simpa [τ, Φ, hΦ] using traceEffectToUnit_one_apply_trace ρ
    have hυtrace : υ.matrix.trace.re = σ.matrix.trace.re := by
      simpa [υ, Φ, hΦ] using traceEffectToUnit_one_apply_trace σ
    rw [hτtrace, hυtrace] at hunit
    linarith
  have hleft_nonneg : 0 ≤ Real.sqrt ρ.matrix.trace.re - ε := by
    linarith
  have hsquare :=
    (sq_le_sq₀ hleft_nonneg (Real.sqrt_nonneg σ.matrix.trace.re)).mpr hsqrt_le
  rwa [Real.sq_sqrt σ.trace_nonneg] at hsquare

private theorem traceNorm_eq_trace_re_of_posSemidef
    (A : CMatrix a) (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  rw [traceNorm]
  have hherm : Matrix.conjTranspose A = A := hA.isHermitian.eq
  have hs : psdSqrt (Matrix.conjTranspose A * A) = A := by
    rw [hherm]
    simpa [psdSqrt, sq] using (CFC.sqrt_sq A hA.nonneg)
  rw [hs]

@[simp]
theorem State.purifiedDistance_self (ρ : State a) :
    ρ.purifiedDistance ρ = 0 := by
  rw [State.purifiedDistance_eq, State.squaredFidelity_self_eq_traceNorm_matrix_sq,
    traceNorm_eq_trace_re_of_posSemidef ρ.matrix ρ.pos]
  have htrace : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  rw [htrace]
  norm_num

/-- Every normalized state lies in its own purified-distance ball for every
nonnegative radius. -/
theorem State.purifiedBall_self_of_nonneg
    (ρ : State a) {ε : ℝ} (hε : 0 ≤ ε) :
    ρ.purifiedBall ε ρ := by
  rw [State.purifiedBall_eq, State.purifiedDistance_self]
  exact hε

/-- The zero-radius purified-distance ball of a normalized state is the
singleton containing the center.

This is the normalized-state specialization of
[Tomamichel2015FiniteResources, calculus.tex:398-411]. -/
theorem State.purifiedBall_zero_iff_eq (ρ σ : State a) :
    ρ.purifiedBall 0 σ ↔ ρ = σ := by
  constructor
  · intro hball
    have hdist_nonneg : 0 ≤ ρ.purifiedDistance σ := by
      rw [State.purifiedDistance_eq]
      exact Real.sqrt_nonneg _
    have hdist : ρ.purifiedDistance σ = 0 := le_antisymm hball hdist_nonneg
    have htrace_le_zero : ρ.normalizedTraceDistance σ ≤ 0 := by
      calc
        ρ.normalizedTraceDistance σ ≤ ρ.purifiedDistance σ :=
          State.fuchs_van_de_graaf_upper ρ σ
        _ = 0 := hdist
    have htrace_nonneg : 0 ≤ ρ.normalizedTraceDistance σ :=
      State.normalizedTraceDistance_nonneg ρ σ
    have htrace : ρ.normalizedTraceDistance σ = 0 :=
      le_antisymm htrace_le_zero htrace_nonneg
    exact State.eq_of_normalizedTraceDistance_eq_zero htrace
  · intro h
    simpa [h] using State.purifiedBall_self_of_nonneg σ (le_refl (0 : ℝ))

@[simp]
theorem SubnormalizedState.generalizedFidelity_self
    (ρ : SubnormalizedState a) :
    ρ.generalizedFidelity ρ = 1 := by
  rw [SubnormalizedState.generalizedFidelity_eq]
  rw [psdSqrt_mul_self_of_posSemidef ρ.pos]
  rw [traceNorm_eq_trace_re_of_posSemidef ρ.matrix ρ.pos]
  have hfail :
      Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - ρ.matrix.trace.re)) =
        1 - ρ.matrix.trace.re := by
    rw [← sq]
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (sub_nonneg.mpr ρ.trace_le_one)
  rw [hfail]
  ring

@[simp]
theorem SubnormalizedState.purifiedDistance_self
    (ρ : SubnormalizedState a) :
    ρ.purifiedDistance ρ = 0 := by
  rw [SubnormalizedState.purifiedDistance_eq, SubnormalizedState.generalizedFidelity_self]
  simp

/-- Every subnormalized state lies in its own purified-distance ball for every
nonnegative radius. -/
theorem SubnormalizedState.purifiedBall_self_of_nonneg
    (ρ : SubnormalizedState a) {ε : ℝ} (hε : 0 ≤ ε) :
    ρ.purifiedBall ε ρ := by
  rw [SubnormalizedState.purifiedBall_eq, SubnormalizedState.purifiedDistance_self]
  exact hε

/-- The zero-radius purified-distance ball of a subnormalized state is the
singleton containing the center.

This is Tomamichel's `B^0(ρ) = {ρ}` property for the subnormalized
epsilon ball [Tomamichel2015FiniteResources, calculus.tex:398-411]. -/
theorem SubnormalizedState.purifiedBall_zero_iff_eq (ρ σ : SubnormalizedState a) :
    ρ.purifiedBall 0 σ ↔ ρ = σ := by
  constructor
  · intro hball
    let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
    let σhat : State (Sum PUnit.{u + 1} a) := σ.hatExtension
    have hhat : ρhat.purifiedBall 0 σhat := by
      simpa [ρhat, σhat] using
        (SubnormalizedState.purifiedBall_iff_hatExtension_purifiedBall ρ σ 0).mp hball
    have hhatEq : ρhat = σhat := (State.purifiedBall_zero_iff_eq ρhat σhat).mp hhat
    exact SubnormalizedState.eq_of_hatExtension_eq (by simpa [ρhat, σhat] using hhatEq)
  · intro h
    simpa [h] using SubnormalizedState.purifiedBall_self_of_nonneg σ (le_refl (0 : ℝ))

/-- A lower bound on generalized fidelity gives a subnormalized
purified-distance ball witness. -/
theorem SubnormalizedState.purifiedBall_of_one_sub_generalizedFidelity_le_sq
    (ρ σ : SubnormalizedState a) {ε : ℝ} (hε : 0 ≤ ε)
    (hfid : 1 - ρ.generalizedFidelity σ ≤ ε ^ 2) :
    ρ.purifiedBall ε σ := by
  rw [SubnormalizedState.purifiedBall_eq, SubnormalizedState.purifiedDistance_eq]
  exact (Real.sqrt_le_left hε).mpr hfid

/-- Increasing the generalized fidelity can only shrink purified distance, so
any purified-distance ball transfers along such a fidelity lower bound. -/
theorem SubnormalizedState.purifiedBall_of_generalizedFidelity_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : SubnormalizedState a} {τ υ : SubnormalizedState b} {ε : ℝ}
    (hfid : ρ.generalizedFidelity σ ≤ τ.generalizedFidelity υ)
    (hball : ρ.purifiedBall ε σ) :
    τ.purifiedBall ε υ := by
  rw [SubnormalizedState.purifiedBall_eq, SubnormalizedState.purifiedDistance_eq] at hball ⊢
  exact le_trans (Real.sqrt_le_sqrt (by linarith)) hball

/-- For normalized centers, generalized fidelity comparison is reduced to the
trace-norm fidelity term.  This is the scalar bridge used after blockwise
trace-norm decompositions. -/
theorem SubnormalizedState.generalizedFidelity_le_of_traceNorm_psdSqrt_mul_le_of_trace_one
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : SubnormalizedState a} {τ υ : SubnormalizedState b}
    (hρtrace : ρ.matrix.trace.re = 1)
    (hτtrace : τ.matrix.trace.re = 1)
    (hnorm :
      traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix) ≤
        traceNorm (psdSqrt τ.matrix * psdSqrt υ.matrix)) :
    ρ.generalizedFidelity σ ≤ τ.generalizedFidelity υ := by
  rw [SubnormalizedState.generalizedFidelity_eq, SubnormalizedState.generalizedFidelity_eq]
  rw [hρtrace, hτtrace]
  simp only [sub_self, zero_mul, Real.sqrt_zero, add_zero]
  let x := traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix)
  let y := traceNorm (psdSqrt τ.matrix * psdSqrt υ.matrix)
  change x ^ 2 ≤ y ^ 2
  have hx : 0 ≤ x := by
    simpa [x] using traceNorm_nonneg (psdSqrt ρ.matrix * psdSqrt σ.matrix)
  have hy : 0 ≤ y := by
    simpa [y] using traceNorm_nonneg (psdSqrt τ.matrix * psdSqrt υ.matrix)
  have hxy : x ≤ y := by
    simpa [x, y] using hnorm
  have hprod : 0 ≤ (y - x) * (y + x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hy hx)
  nlinarith

/-- A purification-overlap lower bound for the hat extensions gives the same
lower bound on generalized fidelity of subnormalized states. -/
theorem SubnormalizedState.le_generalizedFidelity_of_hatExtension_purification_overlap
    {r : Type v} [Fintype r] [DecidableEq r]
    (ρ σ : SubnormalizedState a)
    {Ψ Φ : PureVector (Prod r (Sum PUnit.{max u v + 1} a))}
    (hΨ : Ψ.Purifies ρ.hatExtension) (hΦ : Φ.Purifies σ.hatExtension)
    {t : ℝ} (hoverlap : t ≤ Ψ.overlapSq Φ) :
    t ≤ ρ.generalizedFidelity σ := by
  rw [SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension]
  exact le_trans hoverlap
    (PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ)

/-- Purified distance cannot increase after tracing out the second subsystem of
subnormalized bipartite states. -/
theorem SubnormalizedState.purifiedDistance_marginalA_le
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : SubnormalizedState (Prod a b)) :
    ρ.marginalA.purifiedDistance σ.marginalA ≤ ρ.purifiedDistance σ := by
  simpa [SubnormalizedState.marginalA, SubnormalizedState.applyTraceNonincreasingCP]
    using SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP ρ σ
      (MatrixMap.partialTraceB a b) (MatrixMap.partialTraceB_traceNonincreasingCP (a := a) (b := b))

/-- Purified balls are monotone under tracing out the second subsystem of
subnormalized bipartite states. -/
theorem SubnormalizedState.purifiedBall_marginalA_of_purifiedBall
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε σ) :
    ρ.marginalA.purifiedBall ε σ.marginalA :=
  le_trans (SubnormalizedState.purifiedDistance_marginalA_le ρ σ) hball

/-- Purified distance cannot increase after tracing out the first subsystem of
subnormalized bipartite states. -/
theorem SubnormalizedState.purifiedDistance_marginalB_le
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : SubnormalizedState (Prod a b)) :
    ρ.marginalB.purifiedDistance σ.marginalB ≤ ρ.purifiedDistance σ := by
  simpa [SubnormalizedState.marginalB, SubnormalizedState.applyTraceNonincreasingCP]
    using SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP ρ σ
      (MatrixMap.partialTraceA a b) (MatrixMap.partialTraceA_traceNonincreasingCP (a := a) (b := b))

/-- Purified balls are monotone under tracing out the first subsystem of
subnormalized bipartite states. -/
theorem SubnormalizedState.purifiedBall_marginalB_of_purifiedBall
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε σ) :
    ρ.marginalB.purifiedBall ε σ.marginalB :=
  le_trans (SubnormalizedState.purifiedDistance_marginalB_le ρ σ) hball

/-- Purified distance cannot increase under classical diagonal-block
compression. -/
theorem SubnormalizedState.purifiedDistance_blockCompression_le
    {ι : Type*} {β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (i : ι) (ρ σ : SubnormalizedState (Prod ι β)) :
    (ρ.applyTraceNonincreasingCP (MatrixMap.blockCompression (β := β) i)
        (MatrixMap.blockCompression_traceNonincreasingCP (β := β) i)).purifiedDistance
      (σ.applyTraceNonincreasingCP (MatrixMap.blockCompression (β := β) i)
        (MatrixMap.blockCompression_traceNonincreasingCP (β := β) i)) ≤
      ρ.purifiedDistance σ :=
  SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP ρ σ
    (MatrixMap.blockCompression (β := β) i)
    (MatrixMap.blockCompression_traceNonincreasingCP (β := β) i)

/-- The success block of a normalized hat-space state, viewed as a
subnormalized state on the original system. -/
def State.successBlockOfHatState (τ : State (Sum PUnit.{u + 1} a)) :
    SubnormalizedState a :=
  τ.toSubnormalized.applyTraceNonincreasingCP
    (MatrixMap.sumInrCompression (α := a))
    (MatrixMap.sumInrCompression_traceNonincreasingCP (α := a))

@[simp]
theorem State.successBlockOfHatState_matrix (τ : State (Sum PUnit.{u + 1} a)) :
    τ.successBlockOfHatState.matrix =
      (MatrixMap.sumInrCompression (α := a)) τ.matrix :=
  rfl

/-- The success block of the hat extension is the original subnormalized
state. -/
theorem SubnormalizedState.successBlockOf_hatExtension_eq (ρ : SubnormalizedState a) :
    ρ.hatExtension.successBlockOfHatState = ρ := by
  simpa [State.successBlockOfHatState, SubnormalizedState.dropHatExtension]
    using ρ.dropHatExtension_eq

/-- A normalized candidate in the hat-space purified ball compresses to a
subnormalized candidate in the original purified ball. -/
theorem SubnormalizedState.successBlockOfHatState_purifiedBall_of_hat_purifiedBall
    {ρ : SubnormalizedState a} {τ : State (Sum PUnit.{u + 1} a)} {ε : ℝ}
    (hball : ρ.hatExtension.purifiedBall ε τ) :
    ρ.purifiedBall ε τ.successBlockOfHatState := by
  have hsub :
      ρ.hatExtension.toSubnormalized.purifiedBall ε τ.toSubnormalized := by
    change ρ.hatExtension.toSubnormalized.purifiedDistance τ.toSubnormalized ≤ ε
    rw [State.toSubnormalized_purifiedDistance_eq]
    exact hball
  have hcompressed :
      (ρ.hatExtension.toSubnormalized.applyTraceNonincreasingCP
          (MatrixMap.sumInrCompression (α := a))
          (MatrixMap.sumInrCompression_traceNonincreasingCP (α := a))).purifiedBall ε
        τ.successBlockOfHatState := by
    simpa [State.successBlockOfHatState] using
      (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
        (ρ := ρ.hatExtension.toSubnormalized) (σ := τ.toSubnormalized)
        (ε := ε) (MatrixMap.sumInrCompression (α := a))
        (MatrixMap.sumInrCompression_traceNonincreasingCP (α := a)) hsub)
  simpa [State.successBlockOfHatState, SubnormalizedState.dropHatExtension_eq ρ] using
    hcompressed

namespace State

/-- Normalized purified balls are exactly the subnormalized purified balls after
embedding normalized states via `State.toSubnormalized`. -/
theorem purifiedBall_iff_toSubnormalized_purifiedBall (ρ σ : State a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔
      ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized := by
  rw [State.purifiedBall_eq, SubnormalizedState.purifiedBall_eq,
    toSubnormalized_purifiedDistance_eq]

/-! ## Conditional min/max entropy definitions -/

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- The matrix `I_A ⊗ σ_B` used in conditional min/max entropy definitions. -/
def identityTensorStateMatrix (σ : State b) : CMatrix (Prod a b) :=
  Matrix.kronecker (1 : CMatrix a) σ.matrix

/-- Feasibility predicate for the conditional min-entropy order constraint
`ρ_AB ≤ 2^{-λ} • (I_A ⊗ σ_B)` in the local bits convention. -/
def ConditionalMinEntropyFeasible (ρ : State (Prod a b)) (σ : State b) (lam : ℝ) :
    Prop :=
  ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ

@[simp]
theorem ConditionalMinEntropyFeasible_eq (ρ : State (Prod a b)) (σ : State b)
    (lam : ℝ) :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ↔
      ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ :=
  Iff.rfl

/-- Conditional min-entropy as the supremum of feasible exponents.

This is the normalized-state version of the Tomamichel finite-resources
definition; the subnormalized-state generalization is deliberately left to a
later extension. -/
def conditionalMinEntropy (ρ : State (Prod a b)) : ℝ :=
  sSup {lam : ℝ | ∃ σ : State b, ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropy_eq (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy =
      sSup {lam : ℝ | ∃ σ : State b, ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- The candidate value `log₂ F(ρ_AB, I_A ⊗ σ_B)` for conditional max-entropy.

The second argument is positive but not normalized in general, so this uses the
matrix square-root/trace-norm expression directly rather than `State.fidelity`.
The square matches the squared-fidelity convention used elsewhere in QIT. -/
def conditionalMaxEntropyCandidate (ρ : State (Prod a b)) (σ : State b) : ℝ :=
  log2 ((traceNorm (ρ.sqrtMatrix *
    psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2)

/-- Conditional max-entropy as the supremum over normalized `B` states of the
definition-level max-entropy candidate with strictly positive endpoint value.

The positivity guard is the finite-real-valued replacement for the usual
extended-real convention `log 0 = -∞`: Lean's total real logarithm has
`log 0 = 0`, so zero endpoint candidates must not contribute to the supremum. -/
def conditionalMaxEntropy (ρ : State (Prod a b)) : ℝ :=
  sSup {h : ℝ | ∃ σ : State b,
    0 < (traceNorm (ρ.sqrtMatrix *
      psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 ∧
      h = conditionalMaxEntropyCandidate (a := a) ρ σ}

@[simp]
theorem conditionalMaxEntropy_eq (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropy =
      sSup {h : ℝ | ∃ σ : State b,
        0 < (traceNorm (ρ.sqrtMatrix *
          psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 ∧
          h = conditionalMaxEntropyCandidate (a := a) ρ σ} :=
  rfl

/-! ## Smooth conditional min/max entropy -/

/-- Candidate values for smooth conditional min-entropy at smoothing radius `ε`. -/
def SmoothConditionalMinEntropyCandidate (ρ : State (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMinEntropy

@[simp]
theorem SmoothConditionalMinEntropyCandidate_eq (ρ : State (Prod a b)) (ε h : ℝ) :
    SmoothConditionalMinEntropyCandidate (a := a) ρ ε h ↔
      ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
        h = ρ'.conditionalMinEntropy :=
  Iff.rfl

/-- Candidate values for smooth conditional max-entropy at smoothing radius `ε`. -/
def SmoothConditionalMaxEntropyCandidate (ρ : State (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMaxEntropy

@[simp]
theorem SmoothConditionalMaxEntropyCandidate_eq (ρ : State (Prod a b)) (ε h : ℝ) :
    SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h ↔
      ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
        h = ρ'.conditionalMaxEntropy :=
  Iff.rfl

/-- Smooth min-entropy candidates are monotone in the smoothing radius. -/
theorem SmoothConditionalMinEntropyCandidate_mono {ρ : State (Prod a b)} {ε δ h : ℝ}
    (hεδ : ε ≤ δ) :
    SmoothConditionalMinEntropyCandidate (a := a) ρ ε h →
      SmoothConditionalMinEntropyCandidate (a := a) ρ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Smooth max-entropy candidates are monotone in the smoothing radius. -/
theorem SmoothConditionalMaxEntropyCandidate_mono {ρ : State (Prod a b)} {ε δ h : ℝ}
    (hεδ : ε ≤ δ) :
    SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h →
      SmoothConditionalMaxEntropyCandidate (a := a) ρ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Smooth conditional min-entropy as the supremum of min-entropy over the
purified-distance epsilon ball. -/
def smoothConditionalMinEntropy (ρ : State (Prod a b)) (ε : ℝ) : ℝ :=
  sSup {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h}

theorem smoothConditionalMinEntropy_eq_sSup_candidates (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMinEntropy ε =
      sSup {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMinEntropy_eq (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMinEntropy ε =
      sSup {h : ℝ |
        ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMinEntropy} :=
  rfl

/-- Smooth conditional max-entropy as the infimum of max-entropy over the
purified-distance epsilon ball. -/
def smoothConditionalMaxEntropy (ρ : State (Prod a b)) (ε : ℝ) : ℝ :=
  sInf {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h}

theorem smoothConditionalMaxEntropy_eq_sInf_candidates (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMaxEntropy ε =
      sInf {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMaxEntropy_eq (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMaxEntropy ε =
      sInf {h : ℝ |
        ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMaxEntropy} :=
  rfl

/-- Zero-radius smooth conditional min-entropy is the unsmoothed conditional
min-entropy [Tomamichel2015FiniteResources, calculus.tex:418-442]. -/
theorem smoothConditionalMinEntropy_zero (ρ : State (Prod a b)) :
    ρ.smoothConditionalMinEntropy 0 = ρ.conditionalMinEntropy := by
  rw [State.smoothConditionalMinEntropy_eq]
  have hset :
      {h : ℝ | ∃ ρ' : State (Prod a b),
        ρ.purifiedBall 0 ρ' ∧ h = ρ'.conditionalMinEntropy} =
        {ρ.conditionalMinEntropy} := by
    ext h
    constructor
    · rintro ⟨ρ', hball, hh⟩
      rw [Set.mem_singleton_iff]
      have hρ' : ρ = ρ' := (State.purifiedBall_zero_iff_eq ρ ρ').mp hball
      subst ρ'
      simpa using hh
    · intro hh
      rw [Set.mem_singleton_iff] at hh
      exact ⟨ρ, State.purifiedBall_self_of_nonneg ρ (le_refl (0 : ℝ)), hh⟩
  rw [hset]
  exact csSup_singleton ρ.conditionalMinEntropy

/-- Zero-radius smooth conditional max-entropy is the unsmoothed conditional
max-entropy [Tomamichel2015FiniteResources, calculus.tex:418-442]. -/
theorem smoothConditionalMaxEntropy_zero (ρ : State (Prod a b)) :
    ρ.smoothConditionalMaxEntropy 0 = ρ.conditionalMaxEntropy := by
  rw [State.smoothConditionalMaxEntropy_eq]
  have hset :
      {h : ℝ | ∃ ρ' : State (Prod a b),
        ρ.purifiedBall 0 ρ' ∧ h = ρ'.conditionalMaxEntropy} =
        {ρ.conditionalMaxEntropy} := by
    ext h
    constructor
    · rintro ⟨ρ', hball, hh⟩
      rw [Set.mem_singleton_iff]
      have hρ' : ρ = ρ' := (State.purifiedBall_zero_iff_eq ρ ρ').mp hball
      subst ρ'
      simpa using hh
    · intro hh
      rw [Set.mem_singleton_iff] at hh
      exact ⟨ρ, State.purifiedBall_self_of_nonneg ρ (le_refl (0 : ℝ)), hh⟩
  rw [hset]
  exact csInf_singleton ρ.conditionalMaxEntropy

end State

namespace SubnormalizedState

variable {a : Type u} [Fintype a] [DecidableEq a]
variable {b : Type v} [Fintype b] [DecidableEq b]

variable {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]

/-! ## Subnormalized conditioning-register isometries -/

/-- Apply a finite reference isometry to the conditioning/right register of a
subnormalized state on `A × B`. -/
def conditioningIsometryApply
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    SubnormalizedState (Prod a bPlus) :=
  ρ.applyTraceNonincreasingCP
    (MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V))
    (MatrixMap.traceNonincreasingCP_id_kron
      (a := a) (hΦ := MatrixMap.ofReferenceIsometry_traceNonincreasingCP V))

@[simp]
theorem conditioningIsometryApply_matrix
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).matrix = V.applyMatrixRight ρ.matrix := by
  simp [conditioningIsometryApply,
    MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]

@[simp]
theorem conditioningIsometryApply_trace_re
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).matrix.trace.re = ρ.matrix.trace.re := by
  rw [conditioningIsometryApply, applyTraceNonincreasingCP_matrix]
  have hTP := MatrixMap.isTracePreserving_kron (Channel.idChannel a).map
    (MatrixMap.ofReferenceIsometry V)
    (Channel.idChannel a).tracePreserving
    (MatrixMap.ofReferenceIsometry_isTracePreserving V)
  exact congrArg Complex.re (hTP ρ.matrix)

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Apply a finite reference isometry to all of a subnormalized state.  This is
the side-candidate analogue of `conditioningIsometryApply`. -/
def referenceIsometryApply
    (σ : SubnormalizedState b) (V : ReferenceIsometry b c) :
    SubnormalizedState c :=
  σ.applyTraceNonincreasingCP (MatrixMap.ofReferenceIsometry V)
    (MatrixMap.ofReferenceIsometry_traceNonincreasingCP V)

@[simp]
theorem referenceIsometryApply_matrix
    (σ : SubnormalizedState b) (V : ReferenceIsometry b c) :
    (σ.referenceIsometryApply V).matrix = MatrixMap.ofReferenceIsometry V σ.matrix := by
  simp [referenceIsometryApply]

@[simp]
theorem referenceIsometryApply_trace_re
    (σ : SubnormalizedState b) (V : ReferenceIsometry b c) :
    (σ.referenceIsometryApply V).matrix.trace.re = σ.matrix.trace.re := by
  rw [referenceIsometryApply, applyTraceNonincreasingCP_matrix]
  exact congrArg Complex.re (MatrixMap.ofReferenceIsometry_isTracePreserving V σ.matrix)

variable {extra : Type*} [Fintype extra] [DecidableEq extra]

/-- Compress concrete right-summand side padding back to the original side
register. -/
def sumInrCompressedSide
    (σPlus : SubnormalizedState (Sum extra b)) : SubnormalizedState b :=
  σPlus.applyTraceNonincreasingCP
    (MatrixMap.sumInrBlockCompression (extra := extra) (α := b))
    (MatrixMap.sumInrBlockCompression_traceNonincreasingCP (extra := extra) (α := b))

@[simp]
theorem sumInrCompressedSide_matrix
    (σPlus : SubnormalizedState (Sum extra b)) :
    σPlus.sumInrCompressedSide.matrix =
      MatrixMap.sumInrBlockCompression (extra := extra) (α := b) σPlus.matrix :=
  rfl

@[simp]
theorem sumInrCompressedSide_referenceIsometryApply_sumInr_matrix
    (σ : SubnormalizedState b) :
    (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)).sumInrCompressedSide.matrix =
      σ.matrix := by
  ext x y
  rw [sumInrCompressedSide_matrix, referenceIsometryApply_matrix]
  change (MatrixMap.sumInrBlockCompression (extra := extra) (α := b)
      (MatrixMap.ofReferenceIsometry (ReferenceIsometry.sumInr extra b) σ.matrix)) x y =
    σ.matrix x y
  simp [MatrixMap.sumInrBlockCompression, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.sumInr, Matrix.mul_apply]

@[simp]
theorem sumInrCompressedSide_referenceIsometryApply_sumInr
    (σ : SubnormalizedState b) :
    (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)).sumInrCompressedSide =
      σ := by
  exact SubnormalizedState.ext
    (sumInrCompressedSide_referenceIsometryApply_sumInr_matrix (extra := extra) σ)

/-- Compress a concrete `sumInr` conditioning-register padding back to the
original joint register. -/
def conditioningSumInrCompressed
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) :
    SubnormalizedState (Prod a b) :=
  ρPlus.applyTraceNonincreasingCP
    (MatrixMap.kron (Channel.idChannel a).map
      (MatrixMap.sumInrBlockCompression (extra := extra) (α := b)))
    (MatrixMap.traceNonincreasingCP_id_kron (a := a)
      (hΦ := MatrixMap.sumInrBlockCompression_traceNonincreasingCP
        (extra := extra) (α := b)))

@[simp]
theorem conditioningSumInrCompressed_matrix
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) :
    ρPlus.conditioningSumInrCompressed.matrix =
      MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b)) ρPlus.matrix :=
  rfl

@[simp]
theorem conditioningSumInrCompressed_conditioningIsometryApply_sumInr_matrix
    (ρ : SubnormalizedState (Prod a b)) :
    ((ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditioningSumInrCompressed).matrix =
      ρ.matrix := by
  ext x y
  rw [conditioningSumInrCompressed_matrix, conditioningIsometryApply_matrix]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [MatrixMap.sumInrBlockCompression,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.sumInr, Matrix.mul_apply]

@[simp]
theorem conditioningSumInrCompressed_conditioningIsometryApply_sumInr
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditioningSumInrCompressed =
      ρ := by
  exact SubnormalizedState.ext
    (conditioningSumInrCompressed_conditioningIsometryApply_sumInr_matrix
      (extra := extra) ρ)

/-! ## Subnormalized conditional min/max entropy definitions -/

/-- The matrix `I_A ⊗ σ_B` used in subnormalized conditional entropy definitions.

Here `σ_B` is subnormalized, matching
[Tomamichel2015FiniteResources, calculus.tex:81-89] and
[Tomamichel2015FiniteResources, calculus.tex:191-198]. -/
def identityTensorStateMatrix (σ : SubnormalizedState b) : CMatrix (Prod a b) :=
  Matrix.kronecker (1 : CMatrix a) σ.matrix

/-- Feasibility predicate for subnormalized conditional min-entropy in the
local bits convention: `ρ_AB ≤ 2^{-λ} • (I_A ⊗ σ_B)` with
`σ_B ∈ S_≤(B)`. -/
def ConditionalMinEntropyFeasible
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) (lam : ℝ) :
    Prop :=
  ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ

@[simp]
theorem ConditionalMinEntropyFeasible_eq
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) (lam : ℝ) :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ↔
      ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ :=
  Iff.rfl

/-- Subnormalized conditional min-entropy as the supremum of feasible
exponents over subnormalized side-information states. -/
def conditionalMinEntropy (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sSup {lam : ℝ | ∃ σ : SubnormalizedState b,
    ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropy_eq (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropy =
      sSup {lam : ℝ | ∃ σ : SubnormalizedState b,
        ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- The trace-norm squared-fidelity candidate `log₂ F(ρ_AB, I_A ⊗ σ_B)` for
subnormalized conditional max-entropy.

The second matrix `I_A ⊗ σ_B` need not be subnormalized, so this definition uses
the explicit trace-norm square convention rather than `generalizedFidelity`. -/
def conditionalMaxEntropyFidelityCandidate
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) : ℝ :=
  log2 ((traceNorm (psdSqrt ρ.matrix *
    psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2)

/-- Subnormalized conditional max-entropy as the supremum over subnormalized
side-information states of positive squared-fidelity candidates.

The positivity guard avoids assigning finite real content to the usual
extended-real value `log 0 = -∞`. -/
def conditionalMaxEntropy (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sSup {h : ℝ | ∃ σ : SubnormalizedState b,
    0 < (traceNorm (psdSqrt ρ.matrix *
      psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 ∧
      h = conditionalMaxEntropyFidelityCandidate (a := a) ρ σ}

@[simp]
theorem conditionalMaxEntropy_eq (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropy =
      sSup {h : ℝ | ∃ σ : SubnormalizedState b,
        0 < (traceNorm (psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 ∧
          h = conditionalMaxEntropyFidelityCandidate (a := a) ρ σ} :=
  rfl

/-! ## Subnormalized smooth conditional min/max entropy -/

/-- Candidate values for subnormalized smooth conditional min-entropy at
smoothing radius `ε`. -/
def SmoothConditionalMinEntropyCandidate
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (Prod a b),
    ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMinEntropy

@[simp]
theorem SmoothConditionalMinEntropyCandidate_eq
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) :
    SmoothConditionalMinEntropyCandidate (a := a) ρ ε h ↔
      ∃ ρ' : SubnormalizedState (Prod a b),
        ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMinEntropy :=
  Iff.rfl

/-- Candidate values for subnormalized smooth conditional max-entropy at
smoothing radius `ε`. -/
def SmoothConditionalMaxEntropyCandidate
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (Prod a b),
    ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMaxEntropy

@[simp]
theorem SmoothConditionalMaxEntropyCandidate_eq
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) :
    SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h ↔
      ∃ ρ' : SubnormalizedState (Prod a b),
        ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMaxEntropy :=
  Iff.rfl

/-- Subnormalized smooth min-entropy candidates are monotone in the smoothing
radius. -/
theorem SmoothConditionalMinEntropyCandidate_mono
    {ρ : SubnormalizedState (Prod a b)} {ε δ h : ℝ} (hεδ : ε ≤ δ) :
    SmoothConditionalMinEntropyCandidate (a := a) ρ ε h →
      SmoothConditionalMinEntropyCandidate (a := a) ρ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Smooth min-entropy candidates migrate when the smoothing center is moved.
The smoothing radius increases by the purified distance between the old and
new centers. -/
theorem SmoothConditionalMinEntropyCandidate_center_migration
    {ρ η : SubnormalizedState (Prod a b)} {ε δ h : ℝ}
    (hcenter : η.purifiedDistance ρ ≤ δ) :
    SmoothConditionalMinEntropyCandidate (a := a) η ε h →
      SmoothConditionalMinEntropyCandidate (a := a) ρ (ε + δ) h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', SubnormalizedState.purifiedBall_center_migration hcenter hball, hh⟩

/-- Subnormalized smooth max-entropy candidates are monotone in the smoothing
radius. -/
theorem SmoothConditionalMaxEntropyCandidate_mono
    {ρ : SubnormalizedState (Prod a b)} {ε δ h : ℝ} (hεδ : ε ≤ δ) :
    SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h →
      SmoothConditionalMaxEntropyCandidate (a := a) ρ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Subnormalized smooth conditional min-entropy as the supremum of
min-entropy over the subnormalized purified-distance epsilon ball. -/
def smoothConditionalMinEntropy (ρ : SubnormalizedState (Prod a b)) (ε : ℝ) : ℝ :=
  sSup {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h}

theorem smoothConditionalMinEntropy_eq_sSup_candidates
    (ρ : SubnormalizedState (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMinEntropy ε =
      sSup {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMinEntropy_eq
    (ρ : SubnormalizedState (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMinEntropy ε =
      sSup {h : ℝ |
        ∃ ρ' : SubnormalizedState (Prod a b),
          ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMinEntropy} :=
  rfl

/-- Subnormalized smooth conditional max-entropy as the infimum of
max-entropy over the subnormalized purified-distance epsilon ball. -/
def smoothConditionalMaxEntropy (ρ : SubnormalizedState (Prod a b)) (ε : ℝ) : ℝ :=
  sInf {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h}

theorem smoothConditionalMaxEntropy_eq_sInf_candidates
    (ρ : SubnormalizedState (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMaxEntropy ε =
      sInf {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMaxEntropy_eq
    (ρ : SubnormalizedState (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMaxEntropy ε =
      sInf {h : ℝ |
        ∃ ρ' : SubnormalizedState (Prod a b),
          ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMaxEntropy} :=
  rfl

/-- Zero-radius subnormalized smooth conditional min-entropy is the unsmoothed
conditional min-entropy [Tomamichel2015FiniteResources, calculus.tex:418-442]. -/
theorem smoothConditionalMinEntropy_zero (ρ : SubnormalizedState (Prod a b)) :
    ρ.smoothConditionalMinEntropy 0 = ρ.conditionalMinEntropy := by
  rw [SubnormalizedState.smoothConditionalMinEntropy_eq]
  have hset :
      {h : ℝ | ∃ ρ' : SubnormalizedState (Prod a b),
        ρ.purifiedBall 0 ρ' ∧ h = ρ'.conditionalMinEntropy} =
        {ρ.conditionalMinEntropy} := by
    ext h
    constructor
    · rintro ⟨ρ', hball, hh⟩
      rw [Set.mem_singleton_iff]
      have hρ' : ρ = ρ' :=
        (SubnormalizedState.purifiedBall_zero_iff_eq ρ ρ').mp hball
      subst ρ'
      simpa using hh
    · intro hh
      rw [Set.mem_singleton_iff] at hh
      exact ⟨ρ, SubnormalizedState.purifiedBall_self_of_nonneg ρ (le_refl (0 : ℝ)), hh⟩
  rw [hset]
  exact csSup_singleton ρ.conditionalMinEntropy

/-- Zero-radius subnormalized smooth conditional max-entropy is the unsmoothed
conditional max-entropy [Tomamichel2015FiniteResources, calculus.tex:418-442]. -/
theorem smoothConditionalMaxEntropy_zero (ρ : SubnormalizedState (Prod a b)) :
    ρ.smoothConditionalMaxEntropy 0 = ρ.conditionalMaxEntropy := by
  rw [SubnormalizedState.smoothConditionalMaxEntropy_eq]
  have hset :
      {h : ℝ | ∃ ρ' : SubnormalizedState (Prod a b),
        ρ.purifiedBall 0 ρ' ∧ h = ρ'.conditionalMaxEntropy} =
        {ρ.conditionalMaxEntropy} := by
    ext h
    constructor
    · rintro ⟨ρ', hball, hh⟩
      rw [Set.mem_singleton_iff]
      have hρ' : ρ = ρ' :=
        (SubnormalizedState.purifiedBall_zero_iff_eq ρ ρ').mp hball
      subst ρ'
      simpa using hh
    · intro hh
      rw [Set.mem_singleton_iff] at hh
      exact ⟨ρ, SubnormalizedState.purifiedBall_self_of_nonneg ρ (le_refl (0 : ℝ)), hh⟩
  rw [hset]
  exact csInf_singleton ρ.conditionalMaxEntropy

/-! ## Subnormalized pure-marginal pairing and smooth-duality bridges -/

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Scale a normalized state by a real weight in `[0,1]`, yielding a
subnormalized state. This is the local smooth-entropy version of the scaled
pure-state carrier used by the subnormalized duality route. -/
def ofStateScale (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState a where
  matrix := t • ρ.matrix
  pos := Matrix.PosSemidef.smul ρ.pos ht0
  trace_le_one := by
    rw [Matrix.trace_smul, ρ.trace_eq_one]
    simpa [Complex.real_smul] using ht1

@[simp]
theorem ofStateScale_matrix (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix = t • ρ.matrix :=
  rfl

@[simp]
theorem ofStateScale_trace (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix.trace = (t : ℂ) := by
  rw [ofStateScale_matrix, Matrix.trace_smul, ρ.trace_eq_one]
  simp [Complex.real_smul]

@[simp]
theorem ofStateScale_trace_re (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix.trace.re = t := by
  rw [ofStateScale_trace]
  simp

theorem ofStateScale_normalize_trace_eq
    (ρ : SubnormalizedState a) (hρ : 0 < ρ.matrix.trace.re) :
    SubnormalizedState.ofStateScale (ρ.normalize hρ.ne')
        ρ.matrix.trace.re hρ.le ρ.trace_le_one = ρ := by
  apply SubnormalizedState.ext
  rw [SubnormalizedState.ofStateScale_matrix, SubnormalizedState.normalize_matrix]
  ext i j
  have htrC : ((ρ.matrix.trace.re : ℂ) ≠ 0) := by
    exact_mod_cast hρ.ne'
  simp
  field_simp [htrC]

omit [Fintype a] in
@[simp]
theorem identityTensorStateMatrix_ofStateScale
    (σ : State b) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    identityTensorStateMatrix (a := a) (ofStateScale σ t ht0 ht1) =
      t • State.identityTensorStateMatrix (a := a) σ := by
  ext i j
  simp [identityTensorStateMatrix, State.identityTensorStateMatrix, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Complex.real_smul]
  ring

/-- The `AB` marginal of a scaled pure tripartite state on left-associated
`ABC`. -/
def abMarginalFromScaledTripartitePure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (Prod a b) :=
  ofStateScale ψ.state.marginalAB t ht0 ht1

@[simp]
theorem abMarginalFromScaledTripartitePure_matrix
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).matrix = t • ψ.state.marginalAB.matrix :=
  rfl

/-- The `AC` marginal of a scaled pure tripartite state on left-associated
`ABC`. -/
def acMarginalFromScaledTripartitePure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (Prod a c) :=
  ofStateScale ψ.state.marginalAC t ht0 ht1

@[simp]
theorem acMarginalFromScaledTripartitePure_matrix
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).matrix = t • ψ.state.marginalAC.matrix :=
  rfl

/-- Two subnormalized bipartite states are complementary pure marginals when
they are the `AB` and `AC` marginals of the same scaled normalized pure
tripartite state.  This fixed-register relation is the candidate relation that
the later unsmoothed duality leaf is expected to consume; arbitrary smoothing
candidates generally require enlarged references. -/
def ComplementaryPureMarginalRel
    (ρAB : SubnormalizedState (Prod a b)) (ρAC : SubnormalizedState (Prod a c)) : Prop :=
  ∃ (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1),
    ρAB = abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1 ∧
    ρAC = acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1

/-- A scaled pure tripartite state gives complementary subnormalized `AB` and
`AC` marginals. -/
theorem complementaryPureMarginalRel_of_scaled_pure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ComplementaryPureMarginalRel (a := a) (b := b) (c := c)
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c) ψ t ht.le ht1)
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c) ψ t ht.le ht1) := by
  exact ⟨ψ, t, ht, ht1, rfl, rfl⟩

/-! ## Subnormalized embedded purification-ball transport -/

/-- The hatted `AB` target used to normalize subnormalized `AB` candidates. -/
abbrev ABHat (a : Type u) (b : Type v) := Sum PUnit.{max u v + 1} (Prod a b)

/-- The hatted `AC` target used to normalize subnormalized `AC` candidates. -/
abbrev ACHat (a : Type u) (c : Type w) := Sum PUnit.{max u w + 1} (Prod a c)

private theorem abHatSuccessRestrictedAmp_trace_re
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ABHat a b))) :
    (rankOneMatrix (fun x : Prod (Prod a b) R => Φ.amp (x.2, Sum.inr x.1))).trace.re =
      (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re := by
  classical
  simp [State.successBlockOfHatState, State.marginalB, partialTraceA,
    MatrixMap.sumInrCompression_apply, State.toSubnormalized_matrix,
    PureVector.state_matrix, rankOneMatrix_apply, Matrix.trace, Fintype.sum_prod_type]

private def pureVectorNormalize {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) : PureVector α where
  amp := fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x
  trace_rankOne_eq_one := by
    classical
    let t : ℝ := (rankOneMatrix v).trace.re
    have htpos : 0 < t := hpos
    have ht_nonneg : 0 ≤ t := le_of_lt htpos
    have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
    have htrace_im : (rankOneMatrix v).trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).2.symm
    have htrace_complex : (rankOneMatrix v).trace = (t : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using htrace_im
    have hcoeff :
        (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    calc
      (rankOneMatrix
          (fun x => ((((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x))).trace =
          (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (rankOneMatrix v).trace) := by
            simp [rankOneMatrix_trace, dotProduct, t, Finset.mul_sum, mul_assoc,
              mul_left_comm, mul_comm]
      _ = (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) := by
            rw [htrace_complex]
      _ = 1 := hcoeff

@[simp]
private theorem pureVectorNormalize_amp {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) :
    (pureVectorNormalize v hpos).amp =
      fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x :=
  rfl

private def abHatSuccessRestrictedPureVector
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ABHat a b)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    PureVector (Prod (Prod a b) R) :=
  let v : Prod (Prod a b) R → ℂ := fun x => Φ.amp (x.2, Sum.inr x.1)
  pureVectorNormalize v (by
    simpa [v] using abHatSuccessRestrictedAmp_trace_re (a := a) (b := b) Φ ▸ htr)

private theorem abHatSuccessRestrictedPureVector_ab_marginal
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ABHat a b)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    Φ.state.marginalB.successBlockOfHatState =
      abMarginalFromScaledTripartitePure (a := a) (b := b) (c := R)
        (abHatSuccessRestrictedPureVector (a := a) (b := b) Φ htr)
        (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re htr.le
        Φ.state.marginalB.successBlockOfHatState.trace_le_one := by
  classical
  let t : ℝ := (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re
  let c : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
  have hvtrace :
      ((fun x : Prod (Prod a b) R => Φ.amp (x.2, Sum.inr x.1)) ⬝ᵥ
        fun i => (starRingEnd ℂ) (Φ.amp (i.2, Sum.inr i.1))).re = t := by
    simpa [rankOneMatrix_trace, t] using
      abHatSuccessRestrictedAmp_trace_re (a := a) (b := b) Φ
  have htpos : 0 < t := htr
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  have hcoeff : (t : ℂ) * c * c = 1 := by
    have hcoeffR : t * (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = 1 := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    dsimp [c]
    exact_mod_cast hcoeffR
  have hscale (z w : ℂ) : (t : ℂ) * (c * z * star (c * w)) = z * star w := by
    calc
      (t : ℂ) * (c * z * star (c * w)) = ((t : ℂ) * c * c) * (z * star w) := by
        simp [c]
        ring
      _ = z * star w := by simp [hcoeff]
  apply SubnormalizedState.ext
  ext x y
  simp [State.successBlockOfHatState, abMarginalFromScaledTripartitePure, ofStateScale,
    State.marginalB, State.marginalAB, State.marginalA, partialTraceA, partialTraceB,
    MatrixMap.sumInrCompression_apply, State.toSubnormalized_matrix,
    PureVector.state_matrix, rankOneMatrix_apply, abHatSuccessRestrictedPureVector,
    Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  simpa [t, c, hvtrace] using
    (hscale (Φ.amp (r, Sum.inr x)) (Φ.amp (r, Sum.inr y))).symm

private theorem abHatSuccessRestrictedPureVector_ac_marginal
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ABHat a b)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    SubnormalizedState.applyTraceNonincreasingCP
        Φ.state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := R) (α := a) (β := b))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP (r := R) (α := a) (β := b)) =
      acMarginalFromScaledTripartitePure (a := a) (b := b) (c := R)
        (abHatSuccessRestrictedPureVector (a := a) (b := b) Φ htr)
        (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re htr.le
        Φ.state.marginalB.successBlockOfHatState.trace_le_one := by
  classical
  let t : ℝ := (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re
  let c : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
  have hvtrace :
      ((fun x : Prod (Prod a b) R => Φ.amp (x.2, Sum.inr x.1)) ⬝ᵥ
        fun i => (starRingEnd ℂ) (Φ.amp (i.2, Sum.inr i.1))).re = t := by
    simpa [rankOneMatrix_trace, t] using
      abHatSuccessRestrictedAmp_trace_re (a := a) (b := b) Φ
  have htpos : 0 < t := htr
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  have hcoeff : (t : ℂ) * c * c = 1 := by
    have hcoeffR : t * (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = 1 := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    dsimp [c]
    exact_mod_cast hcoeffR
  have hscale (z w : ℂ) : (t : ℂ) * (c * z * star (c * w)) = z * star w := by
    calc
      (t : ℂ) * (c * z * star (c * w)) = ((t : ℂ) * c * c) * (z * star w) := by
        simp [c]
        ring
      _ = z * star w := by simp [hcoeff]
  apply SubnormalizedState.ext
  ext x y
  rcases x with ⟨xA, xR⟩
  rcases y with ⟨yA, yR⟩
  simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
    MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
    acMarginalFromScaledTripartitePure, ofStateScale, State.marginalAC_matrix,
    PureVector.state_matrix, rankOneMatrix_apply, abHatSuccessRestrictedPureVector,
    Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b' _hb'
  simpa [t, c, hvtrace] using
    (hscale (Φ.amp (xR, Sum.inr (xA, b'))) (Φ.amp (yR, Sum.inr (yA, b')))).symm

/-- A hatted pure vector with positive success mass gives complementary
subnormalized pure marginals after extracting the success `AB` block and
discarding the success `B` register on the reference-complement side. -/
private theorem complementaryPureMarginalRel_of_abHat_success
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ABHat a b)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    ComplementaryPureMarginalRel (a := a) (b := b) (c := R)
      Φ.state.marginalB.successBlockOfHatState
      (SubnormalizedState.applyTraceNonincreasingCP
        Φ.state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := R) (α := a) (β := b))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP (r := R) (α := a) (β := b))) := by
  refine ⟨abHatSuccessRestrictedPureVector (a := a) (b := b) Φ htr,
    (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re, htr,
    Φ.state.marginalB.successBlockOfHatState.trace_le_one, ?_, ?_⟩
  · exact abHatSuccessRestrictedPureVector_ab_marginal (a := a) (b := b) Φ htr
  · exact abHatSuccessRestrictedPureVector_ac_marginal (a := a) (b := b) Φ htr

/-- If a pure vector purifies a hatted subnormalized state, its target success
block is the original subnormalized state. -/
private theorem successBlockOf_marginalB_eq_of_purifies_hatExtension
    {R : Type w} [Fintype R] [DecidableEq R]
    {ρ : SubnormalizedState (Prod a b)}
    {Φ : PureVector (Prod R (ABHat a b))}
    (hΦ : Φ.Purifies ρ.hatExtension) :
    Φ.state.marginalB.successBlockOfHatState = ρ := by
  rw [PureVector.purifies_iff] at hΦ
  apply SubnormalizedState.ext
  rw [State.successBlockOfHatState_matrix]
  change (MatrixMap.sumInrCompression (α := Prod a b)) (partialTraceA Φ.state.matrix) =
    ρ.matrix
  rw [hΦ]
  exact congrArg SubnormalizedState.matrix (SubnormalizedState.successBlockOf_hatExtension_eq ρ)

private theorem acHatSuccessRestrictedAmp_trace_re
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ACHat a c))) :
    (rankOneMatrix (fun x : Prod (Prod a R) c => Φ.amp (x.1.2, Sum.inr (x.1.1, x.2)))).trace.re =
      (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re := by
  classical
  simp [State.successBlockOfHatState, State.marginalB, partialTraceA,
    MatrixMap.sumInrCompression_apply, State.toSubnormalized_matrix,
    PureVector.state_matrix, rankOneMatrix_apply, Matrix.trace, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.sum_comm]

private def acHatSuccessRestrictedPureVector
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ACHat a c)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    PureVector (Prod (Prod a R) c) :=
  let v : Prod (Prod a R) c → ℂ := fun x => Φ.amp (x.1.2, Sum.inr (x.1.1, x.2))
  pureVectorNormalize v (by
    simpa [v] using acHatSuccessRestrictedAmp_trace_re (a := a) (c := c) Φ ▸ htr)

private theorem acHatSuccessRestrictedPureVector_ac_marginal
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ACHat a c)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    Φ.state.marginalB.successBlockOfHatState =
      acMarginalFromScaledTripartitePure (a := a) (b := R) (c := c)
        (acHatSuccessRestrictedPureVector (a := a) (c := c) Φ htr)
        (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re htr.le
        Φ.state.marginalB.successBlockOfHatState.trace_le_one := by
  classical
  let t : ℝ := (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re
  let k : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
  have hvtrace :
      ((fun x : Prod (Prod a R) c => Φ.amp (x.1.2, Sum.inr (x.1.1, x.2))) ⬝ᵥ
        fun i => (starRingEnd ℂ) (Φ.amp (i.1.2, Sum.inr (i.1.1, i.2)))).re = t := by
    simpa [rankOneMatrix_trace, t] using
      acHatSuccessRestrictedAmp_trace_re (a := a) (c := c) Φ
  have htpos : 0 < t := htr
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  have hcoeff : (t : ℂ) * k * k = 1 := by
    have hcoeffR : t * (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = 1 := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    dsimp [k]
    exact_mod_cast hcoeffR
  have hscale (z w : ℂ) : (t : ℂ) * (k * z * star (k * w)) = z * star w := by
    calc
      (t : ℂ) * (k * z * star (k * w)) = ((t : ℂ) * k * k) * (z * star w) := by
        simp [k]
        ring
      _ = z * star w := by simp [hcoeff]
  apply SubnormalizedState.ext
  ext x y
  rcases x with ⟨xA, xC⟩
  rcases y with ⟨yA, yC⟩
  simp [State.successBlockOfHatState, acMarginalFromScaledTripartitePure, ofStateScale,
    State.marginalB, State.marginalAC_matrix, partialTraceA,
    MatrixMap.sumInrCompression_apply, State.toSubnormalized_matrix,
    PureVector.state_matrix, rankOneMatrix_apply, acHatSuccessRestrictedPureVector,
    Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  simpa [t, k, hvtrace] using
    (hscale (Φ.amp (r, Sum.inr (xA, xC))) (Φ.amp (r, Sum.inr (yA, yC)))).symm

private theorem acHatSuccessRestrictedPureVector_ab_marginal
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ACHat a c)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    SubnormalizedState.applyTraceNonincreasingCP
        Φ.state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := R) (α := a) (β := c))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP (r := R) (α := a) (β := c)) =
      abMarginalFromScaledTripartitePure (a := a) (b := R) (c := c)
        (acHatSuccessRestrictedPureVector (a := a) (c := c) Φ htr)
        (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re htr.le
        Φ.state.marginalB.successBlockOfHatState.trace_le_one := by
  classical
  let t : ℝ := (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re
  let k : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
  have hvtrace :
      ((fun x : Prod (Prod a R) c => Φ.amp (x.1.2, Sum.inr (x.1.1, x.2))) ⬝ᵥ
        fun i => (starRingEnd ℂ) (Φ.amp (i.1.2, Sum.inr (i.1.1, i.2)))).re = t := by
    simpa [rankOneMatrix_trace, t] using
      acHatSuccessRestrictedAmp_trace_re (a := a) (c := c) Φ
  have htpos : 0 < t := htr
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  have hcoeff : (t : ℂ) * k * k = 1 := by
    have hcoeffR : t * (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = 1 := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    dsimp [k]
    exact_mod_cast hcoeffR
  have hscale (z w : ℂ) : (t : ℂ) * (k * z * star (k * w)) = z * star w := by
    calc
      (t : ℂ) * (k * z * star (k * w)) = ((t : ℂ) * k * k) * (z * star w) := by
        simp [k]
        ring
      _ = z * star w := by simp [hcoeff]
  apply SubnormalizedState.ext
  ext x y
  rcases x with ⟨xA, xR⟩
  rcases y with ⟨yA, yR⟩
  simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
    MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
    abMarginalFromScaledTripartitePure, ofStateScale, State.marginalAB,
    State.marginalA, partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    acHatSuccessRestrictedPureVector, Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c' _hc'
  simpa [t, k, hvtrace] using
    (hscale (Φ.amp (xR, Sum.inr (xA, c'))) (Φ.amp (yR, Sum.inr (yA, c')))).symm

/-- A hatted pure vector with positive success mass gives complementary
subnormalized pure marginals after extracting the success `AC` block and
discarding the success `C` register on the reference-complement side. -/
private theorem complementaryPureMarginalRel_of_acHat_success
    {R : Type w} [Fintype R] [DecidableEq R]
    (Φ : PureVector (Prod R (ACHat a c)))
    (htr : 0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re) :
    ComplementaryPureMarginalRel (a := a) (b := R) (c := c)
      (SubnormalizedState.applyTraceNonincreasingCP
        Φ.state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := R) (α := a) (β := c))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP (r := R) (α := a) (β := c)))
      Φ.state.marginalB.successBlockOfHatState := by
  refine ⟨acHatSuccessRestrictedPureVector (a := a) (c := c) Φ htr,
    (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re, htr,
    Φ.state.marginalB.successBlockOfHatState.trace_le_one, ?_, ?_⟩
  · exact acHatSuccessRestrictedPureVector_ab_marginal (a := a) (c := c) Φ htr
  · exact acHatSuccessRestrictedPureVector_ac_marginal (a := a) (c := c) Φ htr

/-- Failure-aware enlarged complementary reference for `AB → AC⁺` transport. -/
abbrev ACPlusReference (a : Type u) (b : Type v) (c : Type w) := Sum (ABHat a b) c

/-- Failure-aware enlarged complementary reference for `AC → AB⁺` transport. -/
abbrev ABPlusReference (a : Type u) (b : Type v) (c : Type w) := Sum (ACHat a c) b

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
theorem card_abHat_le_acPlusReference :
    Fintype.card (ABHat a b) ≤ Fintype.card (ACPlusReference a b c) := by
  simp [ABHat, ACPlusReference, Fintype.card_sum]

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
theorem card_acHat_le_abPlusReference :
    Fintype.card (ACHat a c) ≤ Fintype.card (ABPlusReference a b c) := by
  simp [ACHat, ABPlusReference, Fintype.card_sum]

/-- Canonical hatted scaled-pure amplitude for the `AB` target.  The success
branch stores the original `ABC` pure vector in the right `C` summand of the
enlarged reference; the hat failure mass is stored in the left failure
summand. -/
def abHatCanonicalScaledPureAmp
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) :
    Prod (ACPlusReference a b c) (ABHat a b) → ℂ
  | (Sum.inl (Sum.inl _), Sum.inl _) => ((Real.sqrt (1 - t) : ℝ) : ℂ)
  | (Sum.inr z, Sum.inr (x, y)) => ((Real.sqrt t : ℝ) : ℂ) * ψ.amp ((x, y), z)
  | _ => 0

private theorem abHatCanonicalScaledPureAmp_partialTraceA
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    partialTraceA
        (rankOneMatrix (abHatCanonicalScaledPureAmp (a := a) (b := b) (c := c) ψ t)) =
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).hatExtension.matrix := by
  classical
  have hABtrace :
      (trace (partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp))).re = 1 := by
    have hABtraceC :
        (trace (partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp))) = 1 := by
      simpa [State.marginalAB, State.marginalA, PureVector.state_matrix] using
        ψ.state.marginalAB.trace_eq_one
    simpa using congrArg Complex.re hABtraceC
  ext x y
  cases x with
  | inl xf =>
      cases y with
      | inl yf =>
          rw [SubnormalizedState.hatExtension_matrix]
          simp only [partialTraceA, rankOneMatrix_apply, abHatCanonicalScaledPureAmp]
          rw [SubnormalizedState.hatExtensionMatrix_fail_fail]
          simp [SubnormalizedState.hatFailureMass, abMarginalFromScaledTripartitePure,
            hABtrace]
          rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (sub_nonneg.mpr ht1)]
          norm_num
      | inr ysuccess =>
          rcases ysuccess with ⟨yA, yB⟩
          simp [partialTraceA, rankOneMatrix_apply, abHatCanonicalScaledPureAmp,
            SubnormalizedState.hatExtensionMatrix]
  | inr xsuccess =>
      rcases xsuccess with ⟨xA, xB⟩
      cases y with
      | inl yf =>
          simp [partialTraceA, rankOneMatrix_apply, abHatCanonicalScaledPureAmp,
            SubnormalizedState.hatExtensionMatrix]
      | inr ysuccess =>
          rcases ysuccess with ⟨yA, yB⟩
          simp [partialTraceA, rankOneMatrix_apply, abHatCanonicalScaledPureAmp,
            SubnormalizedState.hatExtensionMatrix, abMarginalFromScaledTripartitePure,
            State.marginalAB, State.marginalA, partialTraceB, PureVector.state_matrix,
            Complex.real_smul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          calc
            ((Real.sqrt t : ℂ) * ψ.amp ((xA, xB), z) *
                ((Real.sqrt t : ℂ) * star (ψ.amp ((yA, yB), z)))) =
                ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) *
                  (ψ.amp ((xA, xB), z) * star (ψ.amp ((yA, yB), z))) := by
              ring
            _ = (t : ℂ) * (ψ.amp ((xA, xB), z) * star (ψ.amp ((yA, yB), z))) := by
              rw [← Complex.ofReal_mul]
              congr 1
              rw [← sq, Real.sq_sqrt ht0]

/-- Canonical hatted scaled-pure purification for the `AB` target. -/
def abHatCanonicalScaledPure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    PureVector (Prod (ACPlusReference a b c) (ABHat a b)) where
  amp := abHatCanonicalScaledPureAmp (a := a) (b := b) (c := c) ψ t
  trace_rankOne_eq_one := by
    rw [← partialTraceA_trace
      (a := ACPlusReference a b c) (b := ABHat a b)
      (rankOneMatrix (abHatCanonicalScaledPureAmp (a := a) (b := b) (c := c) ψ t))]
    rw [abHatCanonicalScaledPureAmp_partialTraceA (a := a) (b := b) (c := c)
      ψ t ht0 ht1]
    exact (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).hatExtension.trace_eq_one

/-- The canonical hatted scaled-pure vector purifies the hatted scaled `AB`
marginal. -/
theorem abHatCanonicalScaledPure_purifies
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (abHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).Purifies
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).hatExtension := by
  rw [PureVector.purifies_iff, PureVector.state_matrix]
  exact abHatCanonicalScaledPureAmp_partialTraceA (a := a) (b := b) (c := c)
    ψ t ht0 ht1

private theorem abHatCanonicalScaledPure_sumInrTraceDiscard_matrix
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (SubnormalizedState.applyTraceNonincreasingCP
        (abHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := ACPlusReference a b c) (α := a) (β := b))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
          (r := ACPlusReference a b c) (α := a) (β := b))).matrix =
      ((acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).conditioningIsometryApply
            (ReferenceIsometry.sumInr (ABHat a b) c)).matrix := by
  classical
  ext x y
  rcases x with ⟨xA, xR⟩
  rcases y with ⟨yA, yR⟩
  cases xR with
  | inl xHat =>
      cases yR <;>
        simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
          MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
          PureVector.state_matrix, rankOneMatrix_apply, abHatCanonicalScaledPure,
          abHatCanonicalScaledPureAmp, SubnormalizedState.conditioningIsometryApply_matrix,
          acMarginalFromScaledTripartitePure, ReferenceIsometry.applyMatrixRight,
          ReferenceIsometry.rightBlock, ReferenceIsometry.sumInr, Matrix.mul_apply]
  | inr xC =>
      cases yR with
      | inl yHat =>
          simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
            MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
            PureVector.state_matrix, rankOneMatrix_apply, abHatCanonicalScaledPure,
            abHatCanonicalScaledPureAmp, SubnormalizedState.conditioningIsometryApply_matrix,
            acMarginalFromScaledTripartitePure, ReferenceIsometry.applyMatrixRight,
            ReferenceIsometry.rightBlock, ReferenceIsometry.sumInr, Matrix.mul_apply]
      | inr yC =>
          simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
            MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
            PureVector.state_matrix, rankOneMatrix_apply, abHatCanonicalScaledPure,
            abHatCanonicalScaledPureAmp, SubnormalizedState.conditioningIsometryApply_matrix,
            acMarginalFromScaledTripartitePure, State.marginalAC_matrix,
            ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
            ReferenceIsometry.sumInr, Matrix.mul_apply, Complex.real_smul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          calc
            ((Real.sqrt t : ℂ) * ψ.amp ((xA, z), xC) *
                ((Real.sqrt t : ℂ) * star (ψ.amp ((yA, z), yC)))) =
                ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) *
                  (ψ.amp ((xA, z), xC) * star (ψ.amp ((yA, z), yC))) := by
              ring
            _ = (t : ℂ) *
                  (ψ.amp ((xA, z), xC) * star (ψ.amp ((yA, z), yC))) := by
              rw [← Complex.ofReal_mul]
              congr 1
              rw [← sq, Real.sq_sqrt ht0]

/-- The canonical hatted `AB` purification has exactly the scaled `AC` marginal
embedded in the right summand of the enlarged reference after discarding the
success `B` register. -/
theorem abHatCanonicalScaledPure_sumInrTraceDiscard
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState.applyTraceNonincreasingCP
        (abHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := ACPlusReference a b c) (α := a) (β := b))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
          (r := ACPlusReference a b c) (α := a) (β := b)) =
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).conditioningIsometryApply
        (ReferenceIsometry.sumInr (ABHat a b) c) := by
  exact SubnormalizedState.ext
    (abHatCanonicalScaledPure_sumInrTraceDiscard_matrix (a := a) (b := b) (c := c)
      ψ t ht0 ht1)

/-- Existence package for the canonical hatted scaled-pure `AB → AC⁺` base
route. -/
theorem abHatCanonicalScaledPureBridge
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ Φ : PureVector (Prod (ACPlusReference a b c) (ABHat a b)),
      Φ.Purifies
        (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).hatExtension ∧
      SubnormalizedState.applyTraceNonincreasingCP
          Φ.state.toSubnormalized
          (MatrixMap.sumInrTraceDiscard (r := ACPlusReference a b c) (α := a) (β := b))
          (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
            (r := ACPlusReference a b c) (α := a) (β := b)) =
        (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).conditioningIsometryApply
            (ReferenceIsometry.sumInr (ABHat a b) c) := by
  refine ⟨abHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1, ?_, ?_⟩
  · exact abHatCanonicalScaledPure_purifies (a := a) (b := b) (c := c) ψ t ht0 ht1
  · exact abHatCanonicalScaledPure_sumInrTraceDiscard (a := a) (b := b) (c := c)
      ψ t ht0 ht1

/-- Canonical hatted scaled-pure amplitude for the `AC` target.  The success
branch stores the original `ABC` pure vector in the right `B` summand of the
enlarged reference; the hat failure mass is stored in the left failure
summand. -/
def acHatCanonicalScaledPureAmp
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) :
    Prod (ABPlusReference a b c) (ACHat a c) → ℂ
  | (Sum.inl (Sum.inl _), Sum.inl _) => ((Real.sqrt (1 - t) : ℝ) : ℂ)
  | (Sum.inr y, Sum.inr (x, z)) => ((Real.sqrt t : ℝ) : ℂ) * ψ.amp ((x, y), z)
  | _ => 0

private theorem acHatCanonicalScaledPureAmp_partialTraceA
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    partialTraceA
        (rankOneMatrix (acHatCanonicalScaledPureAmp (a := a) (b := b) (c := c) ψ t)) =
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).hatExtension.matrix := by
  classical
  let φ : Prod (Prod a c) b → ℂ := fun x => ψ.amp ((x.1.1, x.2), x.1.2)
  have hACtrace :
      (trace (partialTraceB (a := Prod a c) (b := b) (rankOneMatrix φ))).re = 1 := by
    have hACmatrix :
        partialTraceB (a := Prod a c) (b := b) (rankOneMatrix φ) =
          ψ.state.marginalAC.matrix := by
      ext x y
      simp [φ, State.marginalAC_matrix, partialTraceB,
        rankOneMatrix_apply]
    have hACtraceC :
        trace (partialTraceB (a := Prod a c) (b := b) (rankOneMatrix φ)) = 1 := by
      rw [hACmatrix]
      exact ψ.state.marginalAC.trace_eq_one
    simpa using congrArg Complex.re hACtraceC
  have hACtrace_expanded :
      (trace (fun ac ac' : Prod a c =>
        ∑ z : b, ψ.amp ((ac.1, z), ac.2) * star (ψ.amp ((ac'.1, z), ac'.2)))).re = 1 := by
    simpa [φ, partialTraceB, rankOneMatrix_apply] using hACtrace
  have hACtrace_expanded_starRing :
      (trace (fun ac ac' : Prod a c =>
        ∑ z : b, ψ.amp ((ac.1, z), ac.2) *
          (starRingEnd ℂ) (ψ.amp ((ac'.1, z), ac'.2)))).re = 1 := by
    simpa only [starRingEnd_apply] using hACtrace_expanded
  ext x y
  cases x with
  | inl xf =>
      cases y with
      | inl yf =>
          rw [SubnormalizedState.hatExtension_matrix]
          simp only [partialTraceA, rankOneMatrix_apply, acHatCanonicalScaledPureAmp]
          rw [SubnormalizedState.hatExtensionMatrix_fail_fail]
          simp [SubnormalizedState.hatFailureMass, acMarginalFromScaledTripartitePure]
          rw [hACtrace_expanded_starRing]
          rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (sub_nonneg.mpr ht1)]
          norm_num
      | inr ysuccess =>
          rcases ysuccess with ⟨yA, yC⟩
          simp [partialTraceA, rankOneMatrix_apply, acHatCanonicalScaledPureAmp,
            SubnormalizedState.hatExtensionMatrix]
  | inr xsuccess =>
      rcases xsuccess with ⟨xA, xC⟩
      cases y with
      | inl yf =>
          simp [partialTraceA, rankOneMatrix_apply, acHatCanonicalScaledPureAmp,
            SubnormalizedState.hatExtensionMatrix]
      | inr ysuccess =>
          rcases ysuccess with ⟨yA, yC⟩
          simp [partialTraceA, rankOneMatrix_apply, acHatCanonicalScaledPureAmp,
            SubnormalizedState.hatExtensionMatrix, acMarginalFromScaledTripartitePure,
            State.marginalAC_matrix, Complex.real_smul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro yB hy
          calc
            ((Real.sqrt t : ℂ) * ψ.amp ((xA, yB), xC) *
                ((Real.sqrt t : ℂ) * star (ψ.amp ((yA, yB), yC)))) =
                ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) *
                  (ψ.amp ((xA, yB), xC) * star (ψ.amp ((yA, yB), yC))) := by
              ring
            _ = (t : ℂ) * (ψ.amp ((xA, yB), xC) * star (ψ.amp ((yA, yB), yC))) := by
              rw [← Complex.ofReal_mul]
              congr 1
              rw [← sq, Real.sq_sqrt ht0]

/-- Canonical hatted scaled-pure purification for the `AC` target. -/
def acHatCanonicalScaledPure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    PureVector (Prod (ABPlusReference a b c) (ACHat a c)) where
  amp := acHatCanonicalScaledPureAmp (a := a) (b := b) (c := c) ψ t
  trace_rankOne_eq_one := by
    rw [← partialTraceA_trace
      (a := ABPlusReference a b c) (b := ACHat a c)
      (rankOneMatrix (acHatCanonicalScaledPureAmp (a := a) (b := b) (c := c) ψ t))]
    rw [acHatCanonicalScaledPureAmp_partialTraceA (a := a) (b := b) (c := c)
      ψ t ht0 ht1]
    exact (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).hatExtension.trace_eq_one

/-- The canonical hatted scaled-pure vector purifies the hatted scaled `AC`
marginal. -/
theorem acHatCanonicalScaledPure_purifies
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (acHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).Purifies
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).hatExtension := by
  rw [PureVector.purifies_iff, PureVector.state_matrix]
  exact acHatCanonicalScaledPureAmp_partialTraceA (a := a) (b := b) (c := c)
    ψ t ht0 ht1

private theorem acHatCanonicalScaledPure_sumInrTraceDiscard_matrix
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (SubnormalizedState.applyTraceNonincreasingCP
        (acHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := ABPlusReference a b c) (α := a) (β := c))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
          (r := ABPlusReference a b c) (α := a) (β := c))).matrix =
      ((abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).conditioningIsometryApply
            (ReferenceIsometry.sumInr (ACHat a c) b)).matrix := by
  classical
  ext x y
  rcases x with ⟨xA, xR⟩
  rcases y with ⟨yA, yR⟩
  cases xR with
  | inl xHat =>
      cases yR <;>
        simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
          MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
          PureVector.state_matrix, rankOneMatrix_apply, acHatCanonicalScaledPure,
          acHatCanonicalScaledPureAmp, SubnormalizedState.conditioningIsometryApply_matrix,
          abMarginalFromScaledTripartitePure, ReferenceIsometry.applyMatrixRight,
          ReferenceIsometry.rightBlock, ReferenceIsometry.sumInr, Matrix.mul_apply]
  | inr xB =>
      cases yR with
      | inl yHat =>
          simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
            MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
            PureVector.state_matrix, rankOneMatrix_apply, acHatCanonicalScaledPure,
            acHatCanonicalScaledPureAmp, SubnormalizedState.conditioningIsometryApply_matrix,
            abMarginalFromScaledTripartitePure, ReferenceIsometry.applyMatrixRight,
            ReferenceIsometry.rightBlock, ReferenceIsometry.sumInr, Matrix.mul_apply]
      | inr yB =>
          simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
            MatrixMap.sumInrTraceDiscard_apply, State.toSubnormalized_matrix,
            PureVector.state_matrix, rankOneMatrix_apply, acHatCanonicalScaledPure,
            acHatCanonicalScaledPureAmp, SubnormalizedState.conditioningIsometryApply_matrix,
            abMarginalFromScaledTripartitePure, State.marginalAB, State.marginalA,
            partialTraceB, ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
            ReferenceIsometry.sumInr, Matrix.mul_apply, Complex.real_smul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          calc
            ((Real.sqrt t : ℂ) * ψ.amp ((xA, xB), z) *
                ((Real.sqrt t : ℂ) * star (ψ.amp ((yA, yB), z)))) =
                ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) *
                  (ψ.amp ((xA, xB), z) * star (ψ.amp ((yA, yB), z))) := by
              ring
            _ = (t : ℂ) * (ψ.amp ((xA, xB), z) * star (ψ.amp ((yA, yB), z))) := by
              rw [← Complex.ofReal_mul]
              congr 1
              rw [← sq, Real.sq_sqrt ht0]

/-- The canonical hatted `AC` purification has exactly the scaled `AB` marginal
embedded in the right summand of the enlarged reference after discarding the
success `C` register. -/
theorem acHatCanonicalScaledPure_sumInrTraceDiscard
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState.applyTraceNonincreasingCP
        (acHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).state.toSubnormalized
        (MatrixMap.sumInrTraceDiscard (r := ABPlusReference a b c) (α := a) (β := c))
        (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
          (r := ABPlusReference a b c) (α := a) (β := c)) =
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).conditioningIsometryApply
        (ReferenceIsometry.sumInr (ACHat a c) b) := by
  exact SubnormalizedState.ext
    (acHatCanonicalScaledPure_sumInrTraceDiscard_matrix (a := a) (b := b) (c := c)
      ψ t ht0 ht1)

/-- Existence package for the canonical hatted scaled-pure `AC → AB⁺` base
route. -/
theorem acHatCanonicalScaledPureBridge
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ Φ : PureVector (Prod (ABPlusReference a b c) (ACHat a c)),
      Φ.Purifies
        (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).hatExtension ∧
      SubnormalizedState.applyTraceNonincreasingCP
          Φ.state.toSubnormalized
          (MatrixMap.sumInrTraceDiscard (r := ABPlusReference a b c) (α := a) (β := c))
          (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
            (r := ABPlusReference a b c) (α := a) (β := c)) =
        (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
          ψ t ht0 ht1).conditioningIsometryApply
            (ReferenceIsometry.sumInr (ACHat a c) b) := by
  refine ⟨acHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1, ?_, ?_⟩
  · exact acHatCanonicalScaledPure_purifies (a := a) (b := b) (c := c) ψ t ht0 ht1
  · exact acHatCanonicalScaledPure_sumInrTraceDiscard (a := a) (b := b) (c := c)
      ψ t ht0 ht1

/-- The canonical enlarged-reference purification of the hatted scaled `AB`
marginal.  The reference has enough room for both the hat failure branch and the
original `C` system. -/
def abHatBasePurificationFromScaledPure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    PureVector (Prod (ACPlusReference a b c) (ABHat a b)) :=
  abHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1

/-- The canonical enlarged-reference purification really purifies the hatted
scaled `AB` marginal. -/
theorem abHatBasePurificationFromScaledPure_purifies
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (abHatBasePurificationFromScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).Purifies
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).hatExtension :=
  abHatCanonicalScaledPure_purifies (a := a) (b := b) (c := c) ψ t ht0 ht1

/-- The canonical enlarged-reference purification of the hatted scaled `AC`
marginal.  The reference has enough room for both the hat failure branch and the
original `B` system. -/
def acHatBasePurificationFromScaledPure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    PureVector (Prod (ABPlusReference a b c) (ACHat a c)) :=
  acHatCanonicalScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1

/-- The canonical enlarged-reference purification really purifies the hatted
scaled `AC` marginal. -/
theorem acHatBasePurificationFromScaledPure_purifies
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (acHatBasePurificationFromScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1).Purifies
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).hatExtension :=
  acHatCanonicalScaledPure_purifies (a := a) (b := b) (c := c) ψ t ht0 ht1

/-- The `AC⁺` base complement obtained by keeping the success `A` block and
discarding the original `B` register from the hatted `AB` purification. -/
def embeddedACPlusBaseFromScaledPure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (Prod a (ACPlusReference a b c)) :=
  (abHatBasePurificationFromScaledPure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).state.toSubnormalized.applyTraceNonincreasingCP
    (MatrixMap.sumInrTraceDiscard (r := ACPlusReference a b c) (α := a) (β := b))
    (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
      (r := ACPlusReference a b c) (α := a) (β := b))

/-- The `AB⁺` base complement obtained by keeping the success `A` block and
discarding the original `C` register from the hatted `AC` purification. -/
def embeddedABPlusBaseFromScaledPure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (Prod a (ABPlusReference a b c)) :=
  (acHatBasePurificationFromScaledPure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).state.toSubnormalized.applyTraceNonincreasingCP
    (MatrixMap.sumInrTraceDiscard (r := ABPlusReference a b c) (α := a) (β := c))
    (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
      (r := ABPlusReference a b c) (α := a) (β := c))

/-- With the canonical hatted base, the embedded `AC⁺` base is exactly the
right-summand padding of the scaled `AC` marginal. -/
theorem embeddedACPlusBaseFromScaledPure_eq_conditioningIsometryApply_sumInr
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    embeddedACPlusBaseFromScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1 =
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).conditioningIsometryApply
          (ReferenceIsometry.sumInr (ABHat a b) c) := by
  simpa [embeddedACPlusBaseFromScaledPure, abHatBasePurificationFromScaledPure] using
    (abHatCanonicalScaledPure_sumInrTraceDiscard (a := a) (b := b) (c := c)
      ψ t ht0 ht1)

/-- With the canonical hatted base, the embedded `AB⁺` base is exactly the
right-summand padding of the scaled `AB` marginal. -/
theorem embeddedABPlusBaseFromScaledPure_eq_conditioningIsometryApply_sumInr
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    embeddedABPlusBaseFromScaledPure (a := a) (b := b) (c := c) ψ t ht0 ht1 =
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).conditioningIsometryApply
          (ReferenceIsometry.sumInr (ACHat a c) b) := by
  simpa [embeddedABPlusBaseFromScaledPure, acHatBasePurificationFromScaledPure] using
    (acHatCanonicalScaledPure_sumInrTraceDiscard (a := a) (b := b) (c := c)
      ψ t ht0 ht1)

/-- A fixed-register subnormalized `AB` smooth candidate has an embedded
failure-aware `AC⁺` complementary candidate. -/
def EmbeddedABToACSmoothCandidate
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ε : ℝ) (ρAB' : SubnormalizedState (Prod a b)) : Prop :=
  ∃ Φ : PureVector (Prod (ACPlusReference a b c) (ABHat a b)),
    Φ.Purifies ρAB'.hatExtension ∧
      (embeddedACPlusBaseFromScaledPure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε
        (Φ.state.toSubnormalized.applyTraceNonincreasingCP
          (MatrixMap.sumInrTraceDiscard (r := ACPlusReference a b c) (α := a) (β := b))
          (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
            (r := ACPlusReference a b c) (α := a) (β := b)))

/-- A fixed-register subnormalized `AC` smooth candidate has an embedded
failure-aware `AB⁺` complementary candidate. -/
def EmbeddedACToABSmoothCandidate
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ε : ℝ) (ρAC' : SubnormalizedState (Prod a c)) : Prop :=
  ∃ Φ : PureVector (Prod (ABPlusReference a b c) (ACHat a c)),
    Φ.Purifies ρAC'.hatExtension ∧
      (embeddedABPlusBaseFromScaledPure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε
        (Φ.state.toSubnormalized.applyTraceNonincreasingCP
          (MatrixMap.sumInrTraceDiscard (r := ABPlusReference a b c) (α := a) (β := c))
          (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
            (r := ABPlusReference a b c) (α := a) (β := c)))

/-- Embedded subnormalized purification-ball transport for both smoothing
directions.  The complementary outputs live on enlarged references carrying the
hat failure branch, not on the original fixed `B/C` registers. -/
def EmbeddedSmoothConditionalMinMaxPairing
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ε : ℝ) : Prop :=
  (∀ ρAB' : SubnormalizedState (Prod a b),
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρAB' →
        EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c)
          ψ t ht0 ht1 ε ρAB') ∧
    (∀ ρAC' : SubnormalizedState (Prod a c),
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρAC' →
        EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c)
          ψ t ht0 ht1 ε ρAC')

private theorem embeddedABToAC_of_scaled_pure_purifiedBall
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {ε : ℝ} {ρAB' : SubnormalizedState (Prod a b)}
    (hball :
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρAB') :
    EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε ρAB' := by
  classical
  let ρAB := abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c) ψ t ht0 ht1
  let Ψbase := abHatBasePurificationFromScaledPure (a := a) (b := b) (c := c)
    ψ t ht0 ht1
  have hΨ : Ψbase.Purifies ρAB.hatExtension := by
    simpa [ρAB, Ψbase] using
      abHatBasePurificationFromScaledPure_purifies (a := a) (b := b) (c := c)
        ψ t ht0 ht1
  have hhat : ρAB.hatExtension.purifiedBall ε ρAB'.hatExtension := by
    exact (SubnormalizedState.purifiedBall_iff_hatExtension_purifiedBall
      ρAB ρAB' ε).mp hball
  have hcard : Fintype.card (ABHat a b) ≤ Fintype.card (ACPlusReference a b c) :=
    card_abHat_le_acPlusReference (a := a) (b := b) (c := c)
  obtain ⟨Φ, hΦ, hoverlap⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := Ψbase) (ρ := ρAB.hatExtension) (σ := ρAB'.hatExtension)
      hΨ hcard
  refine ⟨Φ, hΦ, ?_⟩
  have hF :
      ρAB.hatExtension.squaredFidelity ρAB'.hatExtension ≤
        Ψbase.state.squaredFidelity Φ.state := by
    have hbound := PureVector.overlapSq_le_state_squaredFidelity Ψbase Φ
    rwa [hoverlap] at hbound
  have hfull : Ψbase.state.purifiedBall ε Φ.state :=
    State.purifiedBall_of_squaredFidelity_le hF hhat
  have hsub :
      Ψbase.state.toSubnormalized.purifiedBall ε Φ.state.toSubnormalized :=
    (State.purifiedBall_iff_toSubnormalized_purifiedBall Ψbase.state Φ.state ε).mp hfull
  simpa [EmbeddedABToACSmoothCandidate, embeddedACPlusBaseFromScaledPure, Ψbase] using
    (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := Ψbase.state.toSubnormalized) (σ := Φ.state.toSubnormalized)
      (ε := ε)
      (MatrixMap.sumInrTraceDiscard (r := ACPlusReference a b c) (α := a) (β := b))
      (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
        (r := ACPlusReference a b c) (α := a) (β := b))
      hsub)

private theorem embeddedACToAB_of_scaled_pure_purifiedBall
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {ε : ℝ} {ρAC' : SubnormalizedState (Prod a c)}
    (hball :
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρAC') :
    EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε ρAC' := by
  classical
  let ρAC := acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c) ψ t ht0 ht1
  let Ψbase := acHatBasePurificationFromScaledPure (a := a) (b := b) (c := c)
    ψ t ht0 ht1
  have hΨ : Ψbase.Purifies ρAC.hatExtension := by
    simpa [ρAC, Ψbase] using
      acHatBasePurificationFromScaledPure_purifies (a := a) (b := b) (c := c)
        ψ t ht0 ht1
  have hhat : ρAC.hatExtension.purifiedBall ε ρAC'.hatExtension := by
    exact (SubnormalizedState.purifiedBall_iff_hatExtension_purifiedBall
      ρAC ρAC' ε).mp hball
  have hcard : Fintype.card (ACHat a c) ≤ Fintype.card (ABPlusReference a b c) :=
    card_acHat_le_abPlusReference (a := a) (b := b) (c := c)
  obtain ⟨Φ, hΦ, hoverlap⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := Ψbase) (ρ := ρAC.hatExtension) (σ := ρAC'.hatExtension)
      hΨ hcard
  refine ⟨Φ, hΦ, ?_⟩
  have hF :
      ρAC.hatExtension.squaredFidelity ρAC'.hatExtension ≤
        Ψbase.state.squaredFidelity Φ.state := by
    have hbound := PureVector.overlapSq_le_state_squaredFidelity Ψbase Φ
    rwa [hoverlap] at hbound
  have hfull : Ψbase.state.purifiedBall ε Φ.state :=
    State.purifiedBall_of_squaredFidelity_le hF hhat
  have hsub :
      Ψbase.state.toSubnormalized.purifiedBall ε Φ.state.toSubnormalized :=
    (State.purifiedBall_iff_toSubnormalized_purifiedBall Ψbase.state Φ.state ε).mp hfull
  simpa [EmbeddedACToABSmoothCandidate, embeddedABPlusBaseFromScaledPure, Ψbase] using
    (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := Ψbase.state.toSubnormalized) (σ := Φ.state.toSubnormalized)
      (ε := ε)
      (MatrixMap.sumInrTraceDiscard (r := ABPlusReference a b c) (α := a) (β := c))
      (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
        (r := ABPlusReference a b c) (α := a) (β := c))
      hsub)

/-- A scaled pure tripartite state transports every fixed-register
subnormalized smoothing candidate to an embedded failure-aware complementary
candidate, in both directions. -/
theorem embeddedSmoothConditionalMinMaxPairing_of_scaled_pure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ε : ℝ) :
    EmbeddedSmoothConditionalMinMaxPairing (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε := by
  constructor
  · intro ρAB' hball
    exact embeddedABToAC_of_scaled_pure_purifiedBall
      (a := a) (b := b) (c := c) ψ t ht0 ht1 hball
  · intro ρAC' hball
    exact embeddedACToAB_of_scaled_pure_purifiedBall
      (a := a) (b := b) (c := c) ψ t ht0 ht1 hball

/-- Project the `AB → AC⁺` direction from embedded subnormalized
purification-ball transport. -/
theorem EmbeddedSmoothConditionalMinMaxPairing.ab_to_ac_of_purifiedBall
    {ψ : PureVector (Prod (Prod a b) c)} {t ε : ℝ} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}
    (hpair : EmbeddedSmoothConditionalMinMaxPairing (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε)
    (ρAB' : SubnormalizedState (Prod a b))
    (hball :
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρAB') :
    EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε ρAB' :=
  hpair.1 ρAB' hball

/-- Project the `AC → AB⁺` direction from embedded subnormalized
purification-ball transport. -/
theorem EmbeddedSmoothConditionalMinMaxPairing.ac_to_ab_of_purifiedBall
    {ψ : PureVector (Prod (Prod a b) c)} {t ε : ℝ} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}
    (hpair : EmbeddedSmoothConditionalMinMaxPairing (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε)
    (ρAC' : SubnormalizedState (Prod a c))
    (hball :
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρAC') :
    EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε ρAC' :=
  hpair.2 ρAC' hball

/-- An embedded `AB → AC⁺` subnormalized candidate gives an enlarged
complementary pure-marginal relation after extracting the hatted success block. -/
theorem EmbeddedABToACSmoothCandidate.exists_complementaryPureMarginalRel
    {ψ : PureVector (Prod (Prod a b) c)} {t ε : ℝ} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}
    {ρAB' : SubnormalizedState (Prod a b)}
    (h : EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε ρAB')
    (hρ : 0 < ρAB'.matrix.trace.re) :
    ∃ ρACPlus' : SubnormalizedState (Prod a (ACPlusReference a b c)),
      (embeddedACPlusBaseFromScaledPure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρACPlus' ∧
      ComplementaryPureMarginalRel (a := a) (b := b) (c := ACPlusReference a b c)
        ρAB' ρACPlus' := by
  rcases h with ⟨Φ, hΦ, hball⟩
  let ρACPlus' : SubnormalizedState (Prod a (ACPlusReference a b c)) :=
    Φ.state.toSubnormalized.applyTraceNonincreasingCP
      (MatrixMap.sumInrTraceDiscard (r := ACPlusReference a b c) (α := a) (β := b))
      (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
        (r := ACPlusReference a b c) (α := a) (β := b))
  refine ⟨ρACPlus', hball, ?_⟩
  have hsuccess :
      Φ.state.marginalB.successBlockOfHatState = ρAB' :=
    successBlockOf_marginalB_eq_of_purifies_hatExtension
      (a := a) (b := b) (R := ACPlusReference a b c) hΦ
  have htr :
      0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re := by
    rwa [hsuccess]
  simpa [ρACPlus', hsuccess] using
    (complementaryPureMarginalRel_of_abHat_success
      (a := a) (b := b) (R := ACPlusReference a b c) Φ htr)

/-- An embedded `AC → AB⁺` subnormalized candidate gives an enlarged
complementary pure-marginal relation after extracting the hatted success block. -/
theorem EmbeddedACToABSmoothCandidate.exists_complementaryPureMarginalRel
    {ψ : PureVector (Prod (Prod a b) c)} {t ε : ℝ} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}
    {ρAC' : SubnormalizedState (Prod a c)}
    (h : EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε ρAC')
    (hρ : 0 < ρAC'.matrix.trace.re) :
    ∃ ρABPlus' : SubnormalizedState (Prod a (ABPlusReference a b c)),
      (embeddedABPlusBaseFromScaledPure (a := a) (b := b) (c := c)
        ψ t ht0 ht1).purifiedBall ε ρABPlus' ∧
      ComplementaryPureMarginalRel (a := a) (b := ABPlusReference a b c) (c := c)
        ρABPlus' ρAC' := by
  rcases h with ⟨Φ, hΦ, hball⟩
  let ρABPlus' : SubnormalizedState (Prod a (ABPlusReference a b c)) :=
    Φ.state.toSubnormalized.applyTraceNonincreasingCP
      (MatrixMap.sumInrTraceDiscard (r := ABPlusReference a b c) (α := a) (β := c))
      (MatrixMap.sumInrTraceDiscard_traceNonincreasingCP
        (r := ABPlusReference a b c) (α := a) (β := c))
  refine ⟨ρABPlus', hball, ?_⟩
  have hsuccess :
      Φ.state.marginalB.successBlockOfHatState = ρAC' :=
    successBlockOf_marginalB_eq_of_purifies_hatExtension
      (a := a) (b := c) (R := ABPlusReference a b c) hΦ
  have htr :
      0 < (Φ.state.marginalB.successBlockOfHatState.matrix.trace).re := by
    rwa [hsuccess]
  simpa [ρABPlus', hsuccess] using
    (complementaryPureMarginalRel_of_acHat_success
      (a := a) (c := c) (R := ABPlusReference a b c) Φ htr)

/-- Candidate-level relation needed to turn a subnormalized purification-level
min/max duality proof into the smooth entropy equality. -/
def SmoothConditionalMinMaxCandidateDuality
    (ρAB : SubnormalizedState (Prod a b)) (ρAC : SubnormalizedState (Prod a c))
    (ε : ℝ) : Prop :=
  ∀ h : ℝ,
    SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h ↔
      SmoothConditionalMinEntropyCandidate (a := a) ρAC ε (-h)

@[simp]
theorem SmoothConditionalMinMaxCandidateDuality_eq
    (ρAB : SubnormalizedState (Prod a b)) (ρAC : SubnormalizedState (Prod a c))
    (ε : ℝ) :
    SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε ↔
      ∀ h : ℝ,
        SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h ↔
          SmoothConditionalMinEntropyCandidate (a := a) ρAC ε (-h) :=
  Iff.rfl

/-- Witness-level form of the subnormalized purified-smoothing min/max
duality route.  The entropy equality on each related pair is supplied as a
separate unsmoothed input; this predicate records only the
transport-plus-entropy handoff. -/
def SmoothConditionalMinMaxWitnessDuality
    (ρAB : SubnormalizedState (Prod a b)) (ρAC : SubnormalizedState (Prod a c))
    (ε : ℝ) : Prop :=
  (∀ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' →
      ∃ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' ∧
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) ∧
    (∀ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' →
      ∃ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' ∧
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy)

@[simp]
theorem SmoothConditionalMinMaxWitnessDuality_eq
    (ρAB : SubnormalizedState (Prod a b)) (ρAC : SubnormalizedState (Prod a c))
    (ε : ℝ) :
    SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε ↔
      (∀ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' →
          ∃ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' ∧
            ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) ∧
        (∀ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' →
          ∃ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' ∧
            ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) :=
  Iff.rfl

/-- Relation-parametric pairing of subnormalized smoothed `AB` and `AC`
candidates.  This records the fixed-register transport property once it is
available from a separate purification-lifting argument; it does not assert
that every fixed reference can purify every smoothed candidate. -/
def SmoothConditionalMinMaxPairing
    (ρAB : SubnormalizedState (Prod a b)) (ρAC : SubnormalizedState (Prod a c))
    (ε : ℝ)
    (Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop) :
    Prop :=
  (∀ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' →
      ∃ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC') ∧
    (∀ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' →
      ∃ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' ∧ Rel ρAB' ρAC')

@[simp]
theorem SmoothConditionalMinMaxPairing_eq
    (ρAB : SubnormalizedState (Prod a b)) (ρAC : SubnormalizedState (Prod a c))
    (ε : ℝ)
    (Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop) :
    SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel ↔
      (∀ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' →
          ∃ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC') ∧
        (∀ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' →
          ∃ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' ∧
            Rel ρAB' ρAC') :=
  Iff.rfl

/-- Package externally supplied fixed-register subnormalized purified-ball
transport directions as a relation-parametric smooth min/max pairing. -/
theorem smoothConditionalMinMaxPairing_of_transports
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)}
    {ε : ℝ}
    {Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop}
    (hABToAC :
      ∀ ρAB' : SubnormalizedState (Prod a b), ρAB.purifiedBall ε ρAB' →
        ∃ ρAC' : SubnormalizedState (Prod a c),
          ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC')
    (hACToAB :
      ∀ ρAC' : SubnormalizedState (Prod a c), ρAC.purifiedBall ε ρAC' →
        ∃ ρAB' : SubnormalizedState (Prod a b),
          ρAB.purifiedBall ε ρAB' ∧ Rel ρAB' ρAC') :
    SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel :=
  ⟨hABToAC, hACToAB⟩

/-- Project the externally supplied `AB → AC` direction from a fixed-register
subnormalized purified-ball pairing. -/
theorem SmoothConditionalMinMaxPairing.ab_to_ac_of_purifiedBall
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)}
    {ε : ℝ}
    {Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (ρAB' : SubnormalizedState (Prod a b)) (hball : ρAB.purifiedBall ε ρAB') :
    ∃ ρAC' : SubnormalizedState (Prod a c),
      ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC' :=
  hpair.1 ρAB' hball

/-- Project the externally supplied `AC → AB` direction from a fixed-register
subnormalized purified-ball pairing. -/
theorem SmoothConditionalMinMaxPairing.ac_to_ab_of_purifiedBall
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)}
    {ε : ℝ}
    {Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (ρAC' : SubnormalizedState (Prod a c)) (hball : ρAC.purifiedBall ε ρAC') :
    ∃ ρAB' : SubnormalizedState (Prod a b),
      ρAB.purifiedBall ε ρAB' ∧ Rel ρAB' ρAC' :=
  hpair.2 ρAC' hball

/-- Unsmoothed subnormalized min/max entropy duality on each related pair of
candidate states.  This is the relation-parametric input consumed by the
smooth witness bridge. -/
def ConditionalMinMaxEntropyDualOn
    (Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop) : Prop :=
  ∀ ρAB' : SubnormalizedState (Prod a b), ∀ ρAC' : SubnormalizedState (Prod a c),
    Rel ρAB' ρAC' → ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy

@[simp]
theorem ConditionalMinMaxEntropyDualOn_eq
    (Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop) :
    ConditionalMinMaxEntropyDualOn (a := a) Rel ↔
      ∀ ρAB' : SubnormalizedState (Prod a b), ∀ ρAC' : SubnormalizedState (Prod a c),
        Rel ρAB' ρAC' → ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy :=
  Iff.rfl

/-- Pairing transport plus unsmoothed pairwise duality gives the
subnormalized witness-level smooth min/max duality predicate. -/
theorem SmoothConditionalMinMaxWitnessDuality.of_pairing_of_entropy_duality
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)}
    {ε : ℝ}
    {Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (hdual : ConditionalMinMaxEntropyDualOn (a := a) Rel) :
    SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε := by
  constructor
  · intro ρAB' hballAB
    obtain ⟨ρAC', hballAC, hrel⟩ := hpair.1 ρAB' hballAB
    exact ⟨ρAC', hballAC, hdual ρAB' ρAC' hrel⟩
  · intro ρAC' hballAC
    obtain ⟨ρAB', hballAB, hrel⟩ := hpair.2 ρAC' hballAC
    exact ⟨ρAB', hballAB, hdual ρAB' ρAC' hrel⟩

/-- A subnormalized witness-level smoothing duality gives the candidate-set
duality needed by the order-theoretic bridge. -/
theorem SmoothConditionalMinMaxCandidateDuality.of_witness_duality
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)}
    {ε : ℝ}
    (hwit : SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε) :
    SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε := by
  intro h
  constructor
  · rintro ⟨ρAB', hballAB, hh⟩
    obtain ⟨ρAC', hballAC, hentropy⟩ := hwit.1 ρAB' hballAB
    refine ⟨ρAC', hballAC, ?_⟩
    rw [hh, hentropy, neg_neg]
  · rintro ⟨ρAC', hballAC, hh⟩
    obtain ⟨ρAB', hballAB, hentropy⟩ := hwit.2 ρAC' hballAC
    refine ⟨ρAB', hballAB, ?_⟩
    rw [hentropy, ← hh, neg_neg]

/-- Order-theoretic subnormalized smooth min/max duality bridge.

Once the max-candidate set for `ρAB` is exactly the pointwise negation of the
min-candidate set for `ρAC`, the smooth max entropy is the negative smooth min
entropy. This is the `sInf`/`sSup` handoff; purification-ball transport and
unsmoothed endpoint duality supply the candidate relation separately. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_duality
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)} {ε : ℝ}
    (hdual : SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε := by
  let maxSet : Set ℝ :=
    {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h}
  let minSet : Set ℝ :=
    {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρAC ε h}
  have hset : maxSet = -minSet := by
    ext h
    simp only [maxSet, minSet, Set.mem_setOf_eq, Set.mem_neg]
    exact hdual h
  calc
    ρAB.smoothConditionalMaxEntropy ε = sInf maxSet := rfl
    _ = sInf (-minSet) := by rw [hset]
    _ = -sSup minSet := Real.sInf_neg minSet
    _ = -ρAC.smoothConditionalMinEntropy ε := rfl

/-- Composed subnormalized smooth min/max duality bridge from witness-level
smoothing duality. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_witness_duality
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)} {ε : ℝ}
    (hwit : SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε :=
  smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_duality
    (SmoothConditionalMinMaxCandidateDuality.of_witness_duality hwit)

/-- Order-theoretic subnormalized smooth min/max bridge for the one-sided
candidate inequalities produced by enlarged-reference transport followed by
compression. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_bounds
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)} {ε : ℝ}
    (hmaxNonempty :
      ({h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h}).Nonempty)
    (hminNonempty :
      ({h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρAC ε h}).Nonempty)
    (hmaxBddBelow :
      BddBelow {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h})
    (hminBddAbove :
      BddAbove {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρAC ε h})
    (hforward :
      ∀ h : ℝ, SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h →
        ∃ m : ℝ, SmoothConditionalMinEntropyCandidate (a := a) ρAC ε m ∧ -h ≤ m)
    (hreverse :
      ∀ m : ℝ, SmoothConditionalMinEntropyCandidate (a := a) ρAC ε m →
        ∃ h : ℝ, SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h ∧ h ≤ -m) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε := by
  let maxSet : Set ℝ :=
    {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h}
  let minSet : Set ℝ :=
    {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρAC ε h}
  have hge : -sSup minSet ≤ sInf maxSet := by
    refine le_csInf hmaxNonempty ?_
    intro h hh
    obtain ⟨m, hm, hhm⟩ := hforward h hh
    have hm_le : m ≤ sSup minSet := le_csSup hminBddAbove hm
    linarith
  have hle : sInf maxSet ≤ -sSup minSet := by
    have hsup_le : sSup minSet ≤ -sInf maxSet := by
      refine csSup_le hminNonempty ?_
      intro m hm
      obtain ⟨h, hh, hhm⟩ := hreverse m hm
      have hinf_le : sInf maxSet ≤ h := csInf_le hmaxBddBelow hh
      linarith
    linarith
  exact le_antisymm hle hge

/-- Subnormalized smooth min/max duality from a relation-parametric
fixed-register pairing and unsmoothed pairwise duality. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_pairing
    {ρAB : SubnormalizedState (Prod a b)} {ρAC : SubnormalizedState (Prod a c)} {ε : ℝ}
    {Rel : SubnormalizedState (Prod a b) → SubnormalizedState (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (hdual : ConditionalMinMaxEntropyDualOn (a := a) Rel) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε :=
  smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_witness_duality
    (SmoothConditionalMinMaxWitnessDuality.of_pairing_of_entropy_duality hpair hdual)

end SubnormalizedState

namespace State

/-! ## Normalized/subnormalized entropy-definition bridges -/

omit [Fintype a] in
/-- The subnormalized side-information tensor matrix agrees with the normalized
one after embedding the side state with `State.toSubnormalized`. -/
theorem toSubnormalized_identityTensorStateMatrix_eq
    {b : Type v} [Fintype b] [DecidableEq b] (σ : State b) :
    SubnormalizedState.identityTensorStateMatrix (a := a) σ.toSubnormalized =
      identityTensorStateMatrix (a := a) σ :=
  rfl

/-- The subnormalized min-entropy feasibility predicate restricts to the
normalized feasibility predicate on embedded normalized states. -/
theorem toSubnormalized_ConditionalMinEntropyFeasible_iff
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State (Prod a b)) (σ : State b) (lam : ℝ) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := a)
        ρ.toSubnormalized σ.toSubnormalized lam ↔
      ConditionalMinEntropyFeasible (a := a) ρ σ lam :=
  Iff.rfl

/-- The subnormalized max-entropy squared-fidelity candidate agrees with the
normalized candidate on embedded normalized states. -/
theorem toSubnormalized_conditionalMaxEntropyFidelityCandidate_eq
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State (Prod a b)) (σ : State b) :
    SubnormalizedState.conditionalMaxEntropyFidelityCandidate (a := a)
        ρ.toSubnormalized σ.toSubnormalized =
      conditionalMaxEntropyCandidate (a := a) ρ σ :=
  rfl

/-- A normalized smooth min-entropy candidate embeds as a subnormalized smooth
min-entropy candidate when the candidate state is explicitly converted with
`State.toSubnormalized`. -/
theorem toSubnormalized_SmoothConditionalMinEntropyCandidate_of
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ ρ' : State (Prod a b)} {ε h : ℝ}
    (hball : ρ.purifiedBall ε ρ')
    (hh : h = ρ'.toSubnormalized.conditionalMinEntropy) :
    SubnormalizedState.SmoothConditionalMinEntropyCandidate (a := a)
      ρ.toSubnormalized ε h := by
  exact ⟨ρ'.toSubnormalized,
    (purifiedBall_iff_toSubnormalized_purifiedBall ρ ρ' ε).mp hball, hh⟩

/-- A normalized smooth max-entropy candidate embeds as a subnormalized smooth
max-entropy candidate when the candidate state is explicitly converted with
`State.toSubnormalized`. -/
theorem toSubnormalized_SmoothConditionalMaxEntropyCandidate_of
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ ρ' : State (Prod a b)} {ε h : ℝ}
    (hball : ρ.purifiedBall ε ρ')
    (hh : h = ρ'.toSubnormalized.conditionalMaxEntropy) :
    SubnormalizedState.SmoothConditionalMaxEntropyCandidate (a := a)
      ρ.toSubnormalized ε h := by
  exact ⟨ρ'.toSubnormalized,
    (purifiedBall_iff_toSubnormalized_purifiedBall ρ ρ' ε).mp hball, hh⟩

variable {b : Type v} [Fintype b] [DecidableEq b]
variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Candidate-level relation needed to turn a purification-level min/max
duality proof into the smooth entropy equality.

For every max-entropy candidate of `ρAB`, the corresponding negated value is a
min-entropy candidate of `ρAC`, and conversely. The source-shaped proof of this
predicate requires the purification-ball lifting and unsmoothed min/max duality
machinery; the theorem below isolates the order-theoretic `sInf`/`sSup` step. -/
def SmoothConditionalMinMaxCandidateDuality
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) : Prop :=
  ∀ h : ℝ,
    SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h ↔
      SmoothConditionalMinEntropyCandidate (a := a) ρAC ε (-h)

@[simp]
theorem SmoothConditionalMinMaxCandidateDuality_eq
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) :
    SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε ↔
      ∀ h : ℝ,
        SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h ↔
          SmoothConditionalMinEntropyCandidate (a := a) ρAC ε (-h) :=
  Iff.rfl

/-- Witness-level form of the purified-smoothing min/max duality route.

The first projection says every smoothed `AB` candidate has a smoothed `AC`
counterpart with unsmoothed `Hmax(AB') = -Hmin(AC')`; the second projection is
the converse direction. This predicate packages the mathematical handoff from
purification-ball lifting and unsmoothed min/max duality. -/
def SmoothConditionalMinMaxWitnessDuality
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) : Prop :=
  (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
      ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) ∧
    (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
      ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy)

@[simp]
theorem SmoothConditionalMinMaxWitnessDuality_eq
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) :
    SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε ↔
      (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
          ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧
            ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) ∧
        (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
          ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧
            ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) :=
  Iff.rfl

/-- Relation-parametric pairing of smoothed `AB` and `AC` candidates.

The relation is intended to express that two candidate states arise as
complementary marginals of compatible nearby purifications, while this predicate
only records the bidirectional smoothing transport property. -/
def SmoothConditionalMinMaxPairing
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ)
    (Rel : State (Prod a b) → State (Prod a c) → Prop) : Prop :=
  (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
      ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC') ∧
    (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
      ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧ Rel ρAB' ρAC')

@[simp]
theorem SmoothConditionalMinMaxPairing_eq
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ)
    (Rel : State (Prod a b) → State (Prod a c) → Prop) :
    SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel ↔
      (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
          ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC') ∧
        (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
          ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧ Rel ρAB' ρAC') :=
  Iff.rfl

/-- Unsmoothed min/max entropy duality on each related pair of candidate states. -/
def ConditionalMinMaxEntropyDualOn
    (Rel : State (Prod a b) → State (Prod a c) → Prop) : Prop :=
  ∀ ρAB' : State (Prod a b), ∀ ρAC' : State (Prod a c), Rel ρAB' ρAC' →
    ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy

@[simp]
theorem ConditionalMinMaxEntropyDualOn_eq
    (Rel : State (Prod a b) → State (Prod a c) → Prop) :
    ConditionalMinMaxEntropyDualOn (a := a) Rel ↔
      ∀ ρAB' : State (Prod a b), ∀ ρAC' : State (Prod a c), Rel ρAB' ρAC' →
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy :=
  Iff.rfl

/-- Pairing transport plus unsmoothed pairwise duality gives the witness-level
smooth min/max duality predicate. -/
theorem SmoothConditionalMinMaxWitnessDuality.of_pairing_of_entropy_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    {Rel : State (Prod a b) → State (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (hdual : ConditionalMinMaxEntropyDualOn (a := a) Rel) :
    SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε := by
  constructor
  · intro ρAB' hballAB
    obtain ⟨ρAC', hballAC, hrel⟩ := hpair.1 ρAB' hballAB
    exact ⟨ρAC', hballAC, hdual ρAB' ρAC' hrel⟩
  · intro ρAC' hballAC
    obtain ⟨ρAB', hballAB, hrel⟩ := hpair.2 ρAC' hballAC
    exact ⟨ρAB', hballAB, hdual ρAB' ρAC' hrel⟩

/-- A witness-level smoothing duality immediately gives the candidate-set
duality needed by the order-theoretic bridge. -/
theorem SmoothConditionalMinMaxCandidateDuality.of_witness_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    (hwit : SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε) :
    SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε := by
  intro h
  constructor
  · rintro ⟨ρAB', hballAB, hh⟩
    obtain ⟨ρAC', hballAC, hentropy⟩ := hwit.1 ρAB' hballAB
    refine ⟨ρAC', hballAC, ?_⟩
    rw [hh, hentropy, neg_neg]
  · rintro ⟨ρAC', hballAC, hh⟩
    obtain ⟨ρAB', hballAB, hentropy⟩ := hwit.2 ρAC' hballAC
    refine ⟨ρAB', hballAB, ?_⟩
    rw [hentropy, ← hh, neg_neg]

/-- Order-theoretic smooth min/max duality bridge.

Once the max-candidate set for `ρAB` is exactly the pointwise negation of the
min-candidate set for `ρAC`, the smooth max entropy is the negative smooth min
entropy. This proves the `sInf`/`sSup` part of the purified-smoothing duality
route; the source-level purification theorem supplies the candidate relation. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    (hdual : SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε := by
  let maxSet : Set ℝ := {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h}
  let minSet : Set ℝ := {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρAC ε h}
  have hset : maxSet = -minSet := by
    ext h
    simp only [maxSet, minSet, Set.mem_setOf_eq, Set.mem_neg]
    exact hdual h
  calc
    ρAB.smoothConditionalMaxEntropy ε = sInf maxSet := rfl
    _ = sInf (-minSet) := by rw [hset]
    _ = -sSup minSet := Real.sInf_neg minSet
    _ = -ρAC.smoothConditionalMinEntropy ε := rfl

/-- Composed smooth min/max duality bridge from witness-level smoothing
duality. This is the exact handoff point for purification-ball lifting and
unsmoothed min/max duality. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_witness_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    (hwit : SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε :=
  smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_duality
    (SmoothConditionalMinMaxCandidateDuality.of_witness_duality hwit)

/-- Smooth min/max duality from a relation-parametric pairing and unsmoothed
pairwise duality. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_pairing
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    {Rel : State (Prod a b) → State (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (hdual : ConditionalMinMaxEntropyDualOn (a := a) Rel) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε :=
  smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_witness_duality
    (SmoothConditionalMinMaxWitnessDuality.of_pairing_of_entropy_duality hpair hdual)

end State

namespace Ensemble

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

/-- The score of a POVM trying to guess the classical label of an ensemble.

For a normalized cq ensemble `E = {p_x, ρ_B(x)}` and POVM `M`, this is
`∑ x p_x Pr[M outputs x | ρ_B(x)]`. -/
def cqGuessingScore (E : Ensemble ι b) (M : POVM ι b) : ℝ≥0 :=
  ∑ outcome, E.probs outcome * M.prob (E.states outcome) outcome

@[simp]
theorem cqGuessingScore_eq (E : Ensemble ι b) (M : POVM ι b) :
    E.cqGuessingScore M =
      ∑ outcome, E.probs outcome * M.prob (E.states outcome) outcome :=
  rfl

/-- Guessing scores are nonnegative after coercion to real numbers. -/
theorem cqGuessingScore_nonneg (E : Ensemble ι b) (M : POVM ι b) :
    0 ≤ ((E.cqGuessingScore M : ℝ≥0) : ℝ) :=
  NNReal.coe_nonneg _

/-- Supremum-style guessing probability over all finite POVMs with outcomes
matching the classical labels of the ensemble. -/
def cqGuessingProbability (E : Ensemble ι b) : ℝ :=
  sSup {score : ℝ | ∃ M : POVM ι b,
    score = ((E.cqGuessingScore M : ℝ≥0) : ℝ)}

@[simp]
theorem cqGuessingProbability_eq (E : Ensemble ι b) :
    E.cqGuessingProbability =
      sSup {score : ℝ | ∃ M : POVM ι b,
        score = ((E.cqGuessingScore M : ℝ≥0) : ℝ)} :=
  rfl

end Ensemble

end

/-!
The full Tomamichel subnormalized-state theory, min/max duality, the SDP
optimality proof for guessing probability, and the uncertainty-relation proof
are recorded as downstream source-backed theorem targets.
-/

end QIT
