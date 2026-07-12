/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.States.Schatten
public import Mathlib.Data.EReal.Basic

/-!
# Trace-log quantum relative entropy

Low-level definitions for the ordinary/Umegaki relative entropy with the
support convention: the trace-log branch is used on supported inputs, and
`+infty` otherwise.

This module intentionally contains only the definitions and immediate branch
facts.  The right-limit bridge from sandwiched Renyi and the data-processing
proofs live in `QIT.Information.Entropy.RelativeEntropyDPI`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QIT

universe u

noncomputable section

noncomputable local instance cMatrixCStarAlgebraForRelativeEntropyTraceLog
    {n : Type*} [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Finite trace-log branch of PSD-reference quantum relative entropy.

The branch is written on the positive spectral support of the PSD reference.
The compressed reference is positive definite there, so `psdLog` is the usual
functional-calculus logarithm on the source-supported domain. -/
noncomputable def relativeEntropyPSDReferenceTraceLogFinite
    (rho : State a) (sigma : CMatrix a) (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) : Real := by
  classical
  let rhoC : State (psdSupportIndex sigma hSigma) :=
    psdSupportCompressedState rho hSigma hSupport
  let sigmaC : CMatrix (psdSupportIndex sigma hSigma) :=
    psdSupportCompress sigma hSigma sigma
  have hSigmaC : sigmaC.PosDef := by
    simpa [sigmaC] using psdSupportCompressedState_reference_posDef hSigma
  exact
    -rhoC.vonNeumann -
      ((rhoC.matrix * psdLog sigmaC hSigmaC).trace.re / Real.log 2)

/-- Source-facing extended-real trace-log PSD-reference relative entropy.

This is the Khatri--Wilde/Tomamichel support convention: the trace-log finite
branch is used when `rho` is supported by `sigma`; otherwise the value is
`+infty`. -/
noncomputable def relativeEntropyPSDReferenceTraceLogE
    (rho : State a) (sigma : CMatrix a) (hSigma : sigma.PosSemidef) : EReal := by
  classical
  exact
    if hSupport : Matrix.Supports rho.matrix sigma then
      (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal)
    else
      (⊤ : EReal)

@[simp]
theorem relativeEntropyPSDReferenceTraceLogE_eq_top_of_not_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : ¬ Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogE rho sigma hSigma = (⊤ : EReal) := by
  simp [relativeEntropyPSDReferenceTraceLogE, hSupport]

@[simp]
theorem relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogE rho sigma hSigma =
      (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal) := by
  simp [relativeEntropyPSDReferenceTraceLogE, hSupport]

end State

variable {a : Type u} [Fintype a] [DecidableEq a]

omit [DecidableEq a] in
theorem supports_real_smul_left
    {M N : CMatrix a} (c : ℝ) (hM : Matrix.Supports M N) :
    Matrix.Supports (c • M) N := by
  intro v hv
  simp [Matrix.smul_mulVec, hM v hv]

/-- Finite branch of Tomamichel's source-domain quantum divergence.

For a nonzero PSD operator `rho` supported by the PSD reference `sigma`, this is
the source trace-normalized value.  It is implemented through the normalized
state `rho / Tr rho` plus the trace-scaling correction, avoiding a separate
singular matrix-log API while keeping the same mathematical value. -/
def relativeEntropyPSDTraceLogFinite
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) (hSupport : Matrix.Supports rho sigma) : ℝ := by
  classical
  let hRhoTr : 0 < rho.trace.re :=
    State.posSemidef_trace_pos_of_ne_zero hRho hRho_ne
  let rhoNorm : State a := State.normalizePSD rho hRho hRhoTr.ne'
  have hSupportNorm : Matrix.Supports rhoNorm.matrix sigma := by
    simpa [rhoNorm, State.normalizePSD] using
      supports_real_smul_left ((rho.trace.re)⁻¹ : ℝ) hSupport
  exact
    log2 rho.trace.re +
      State.relativeEntropyPSDReferenceTraceLogFinite
        rhoNorm sigma hSigma hSupportNorm

/-- Source-exact extended-real quantum divergence for nonzero PSD operators.

This matches Tomamichel's Definition `df:rel`: the finite trace-log branch is
used when `rho` is supported by `sigma`, and the value is `+infty` otherwise. -/
def relativeEntropyPSDTraceLogE
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) : EReal := by
  classical
  exact
    if hSupport : Matrix.Supports rho sigma then
      (relativeEntropyPSDTraceLogFinite rho sigma hRho hRho_ne hSigma hSupport : EReal)
    else
      (⊤ : EReal)

@[simp]
theorem relativeEntropyPSDTraceLogE_eq_top_of_not_supports
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) (hSupport : ¬ Matrix.Supports rho sigma) :
    relativeEntropyPSDTraceLogE rho sigma hRho hRho_ne hSigma = (⊤ : EReal) := by
  simp [relativeEntropyPSDTraceLogE, hSupport]

@[simp]
theorem relativeEntropyPSDTraceLogE_eq_coe_of_supports
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) (hSupport : Matrix.Supports rho sigma) :
    relativeEntropyPSDTraceLogE rho sigma hRho hRho_ne hSigma =
      (relativeEntropyPSDTraceLogFinite rho sigma hRho hRho_ne hSigma hSupport : EReal) := by
  simp [relativeEntropyPSDTraceLogE, hSupport]

theorem relativeEntropyPSDTraceLogFinite_state_eq
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDTraceLogFinite
        rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma hSupport =
      State.relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport := by
  simp [relativeEntropyPSDTraceLogFinite, State.normalizePSD_self, rho.trace_re_eq_one, log2]

/-- The source-exact PSD-operator definition specializes to the existing
normalized-state PSD-reference API used by the DPI theorems. -/
theorem relativeEntropyPSDTraceLogE_state_eq
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef) :
    relativeEntropyPSDTraceLogE rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma =
      State.relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  classical
  by_cases hSupport : Matrix.Supports rho.matrix sigma
  · rw [relativeEntropyPSDTraceLogE_eq_coe_of_supports
        rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma hSupport,
      State.relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports rho hSigma hSupport,
      relativeEntropyPSDTraceLogFinite_state_eq rho hSigma hSupport]
  · rw [relativeEntropyPSDTraceLogE_eq_top_of_not_supports
        rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma hSupport,
      State.relativeEntropyPSDReferenceTraceLogE_eq_top_of_not_supports rho hSigma hSupport]

end

end QIT
