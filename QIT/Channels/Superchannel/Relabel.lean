/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.Superchannel
public import QIT.Channels.CompleteAdmissibility.Transport

/-!
# Physical wire relabeling of superchannels

Independent equivalences on the input and output wires induce a deterministic
superchannel. Its ancillary extension relabels only the physical wires, with
both spectator wires unchanged. All physical and ancillary universe levels
are independent, and empty finite systems are included.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT.HigherOrder

universe u v w x y z

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Relabel the input and output factors of an input-first Choi matrix.
This is the matrix reindexing equivalence, viewed as a linear map. -/
def relabelSupermap (e : a ≃ c) (f : b ≃ d) : MatrixMap (a × b) (c × d) :=
  (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr e f)
    (Equiv.prodCongr e f)).toLinearMap

/-- Physical relabeling is simultaneous row and column reindexing; it
introduces neither a transpose nor complex conjugation. -/
@[simp] theorem relabelSupermap_apply (e : a ≃ c) (f : b ≃ d)
    (J : CMatrix (a × b)) :
    relabelSupermap e f J =
      J.submatrix (Equiv.prodCongr e.symm f.symm) (Equiv.prodCongr e.symm f.symm) := rfl

/-- Pulling a Choi matrix back along physical equivalences and then applying
their forward relabeling recovers the original matrix exactly. -/
@[simp] theorem relabelSupermap_submatrix (e : a ≃ c) (f : b ≃ d)
    (J : CMatrix (c × d)) :
    relabelSupermap e f
      (J.submatrix (Equiv.prodCongr e f) (Equiv.prodCongr e f)) = J := by
  ext p q
  simp [Matrix.submatrix_apply, Prod.map]

/-- Unfolding the existing ancillary extension shows that physical wire
relabeling leaves both independently typed spectator wires untouched. -/
theorem ancillaryExtension_relabel (e : a ≃ c) (f : b ≃ d)
    {r : Type y} {s : Type z}
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (J : CMatrix ((a × r) × (b × s))) :
    ancillaryExtension (relabelSupermap e f) J =
      J.submatrix
        (Equiv.prodCongr (Equiv.prodCongr e.symm (Equiv.refl r))
          (Equiv.prodCongr f.symm (Equiv.refl s)))
        (Equiv.prodCongr (Equiv.prodCongr e.symm (Equiv.refl r))
          (Equiv.prodCongr f.symm (Equiv.refl s))) := rfl

/-- Independent physical wire relabeling preserves deterministic
superchannel admissibility. The proof uses the existing channel-preservation
characterization and invariance of partial trace under finite equivalences. -/
theorem isDeterministicSuperchannel_relabel (e : a ≃ c) (f : b ≃ d) :
    IsDeterministicSuperchannel.{u,v,w,x,y,z} (relabelSupermap e f) := by
  apply (isDeterministicSuperchannel_iff_channels _).mpr
  intro r s _ _ _ _ N
  constructor
  · change (MatrixMap.choi (ancillaryAction (relabelSupermap e f) N.map)).PosSemidef
    rw [choi_ancillaryAction, ancillaryExtension_relabel]
    exact N.completelyPositive.submatrix _
  · rw [MatrixMap.isTracePreserving_iff_partialTraceB_choi,
      choi_ancillaryAction, ancillaryExtension_relabel,
      partialTraceB_submatrix_prodEquiv,
      (MatrixMap.isTracePreserving_iff_partialTraceB_choi N.map).mp N.tracePreserving,
      Matrix.submatrix_one_equiv]

end

end QIT.HigherOrder
