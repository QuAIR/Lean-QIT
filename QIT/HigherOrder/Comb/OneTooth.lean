/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HigherOrder.Comb.Admissible
public import QIT.Channels.CompleteAdmissibility.Transport

/-!
# One-tooth combs with boundary spectators

A deterministic one-tooth comb is a channel Choi operator
[Chiribella2009Networks, comblong-pub.tex:1425-1433]. The same statement
holds after attaching independent input and output spectators: the boundary
equivalences only relabel the two channel factors. This module proves the
bridge to the channel predicate used by complete superchannel admissibility.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder MatrixOrder

universe u

namespace QIT.HigherOrder.Comb

variable {A B : Fin 1 → Type u}
  [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
  (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Joint normalization of a one-tooth comb is exactly positivity and the
channel output-trace identity. The spectators need not have equal dimensions
or be inhabited. -/
theorem extendedNormalized_one_iff
    (J : CMatrix (((∀ j, A j) × r) × ((∀ j, B j) × s))) :
    ExtendedNormalized A B r s J ↔ J.PosSemidef ∧ partialTraceB J = 1 := by
  rw [ExtendedNormalized, normalized_one_iff]
  simp only [boundaryEquiv, Matrix.posSemidef_submatrix_equiv,
    partialTraceB_submatrix_prodEquiv]
  apply and_congr_right
  intro _
  constructor
  · intro h
    ext p q
    have he := congrFun (congrFun h ((boundaryInputEquiv A r).symm p))
      ((boundaryInputEquiv A r).symm q)
    simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply, Matrix.one_apply,
      (boundaryInputEquiv A r).symm.injective.eq_iff] using he
  · intro h
    rw [h, Matrix.submatrix_one_equiv]

/-- The one-tooth boundary predicate is the channel predicate supplied to the
generic complete-preservation API. -/
theorem extendedNormalized_one_iff_channelPredicate
    (J : CMatrix (((∀ j, A j) × r) × ((∀ j, B j) × s))) :
    ExtendedNormalized A B r s J ↔ channelPredicate r s J :=
  extendedNormalized_one_iff r s J

end QIT.HigherOrder.Comb
