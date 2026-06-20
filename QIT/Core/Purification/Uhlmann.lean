/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Information.Fidelity
public import QIT.Core.Purification.Canonical
public import QIT.Core.Purification.ReferenceUnitary
public import QIT.Core.TraceNorm.Variational

/-!
# Uhlmann theorem for canonical purifications

This module proves the canonical-purification Uhlmann route registered from
[Wilde2011Qst, qit-notes.tex:15060-15093] and the overlap-to-trace calculation
from [Wilde2011Qst, qit-notes.tex:15114-15127].  It uses the local
`State.squaredFidelity` convention and the trace-norm variational bridge from
`QIT.Core.TraceNorm.Variational`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The canonical-purification overlap after a reference unitary is the trace
of `√ρ * √σ * Uᵀ`. -/
theorem canonicalPurification_overlap_applyReferenceUnitary_eq_trace
    (ρ σ : State a) (U : ReferenceUnitary a) :
    ρ.canonicalPurification.overlap (U.applyPureVector σ.canonicalPurification) =
      (ρ.sqrtMatrix * σ.sqrtMatrix * Matrix.transpose U.matrix).trace := by
  classical
  simp [PureVector.overlap, State.canonicalPurification, State.canonicalPurificationAmp,
    ReferenceUnitary.applyPureVector, ReferenceUnitary.toReferenceIsometry,
    ReferenceIsometry.applyPureVector, ReferenceIsometry.applyAmp, Matrix.trace,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose, Finset.mul_sum, mul_assoc,
    ρ.sqrtMatrix_isHermitian.apply]
  conv_lhs =>
    rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [mul_comm]

/-- Squared canonical-purification overlaps unfold to the squared trace
expression used by the trace-norm variational bridge. -/
theorem canonicalPurification_overlapSq_applyReferenceUnitary_eq_normSq_trace
    (ρ σ : State a) (U : ReferenceUnitary a) :
    ρ.canonicalPurification.overlapSq (U.applyPureVector σ.canonicalPurification) =
      Complex.normSq ((ρ.sqrtMatrix * σ.sqrtMatrix * Matrix.transpose U.matrix).trace) := by
  rw [PureVector.overlapSq_eq_normSq]
  rw [canonicalPurification_overlap_applyReferenceUnitary_eq_trace]

/-- Canonical-purification form of Uhlmann's theorem: squared fidelity is
attained by some reference unitary and bounds every reference-unitary overlap. -/
theorem exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity
    (ρ σ : State a) :
    ∃ U : ReferenceUnitary a,
      ρ.squaredFidelity σ =
        ρ.canonicalPurification.overlapSq (U.applyPureVector σ.canonicalPurification) ∧
      ∀ V : ReferenceUnitary a,
        ρ.canonicalPurification.overlapSq (V.applyPureVector σ.canonicalPurification) ≤
          ρ.squaredFidelity σ := by
  classical
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_referenceUnitary_sq (ρ.sqrtMatrix * σ.sqrtMatrix)
  refine ⟨U, ?_, ?_⟩
  · rw [canonicalPurification_overlapSq_applyReferenceUnitary_eq_normSq_trace, hU,
      State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  · intro V
    rw [canonicalPurification_overlapSq_applyReferenceUnitary_eq_normSq_trace,
      State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
    exact traceNorm_variational_referenceUnitary_sq_le (ρ.sqrtMatrix * σ.sqrtMatrix) V

end State

end

end QIT
