/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State

/-!
# Positive semidefinite square roots

This module provides the local QIT wrapper around mathlib's matrix continuous
functional calculus square root. The API is the state-geometry dependency used
by canonical purification, matching the registered source route where the
canonical purification is built from the unique positive semidefinite square
root of a density operator [Wilde2011Qst, qit-notes.tex:10238-10290] and
[Gour2024Resources, BookQRT.tex:2051-2069].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The positive semidefinite square root of a finite complex matrix. -/
def psdSqrt (M : CMatrix a) : CMatrix a :=
  CFC.sqrt M

/-- The square root returned by `psdSqrt` is positive semidefinite. -/
theorem psdSqrt_pos (M : CMatrix a) :
    (psdSqrt M).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)

/-- The square root returned by `psdSqrt` is Hermitian. -/
theorem psdSqrt_isHermitian (M : CMatrix a) :
    (psdSqrt M).IsHermitian :=
  (psdSqrt_pos M).isHermitian

/-- `psdSqrt M` squares back to a positive semidefinite matrix `M`. -/
theorem psdSqrt_mul_self_of_posSemidef {M : CMatrix a} (hM : M.PosSemidef) :
    psdSqrt M * psdSqrt M = M := by
  simpa [psdSqrt, sq] using (CFC.sq_sqrt M hM.nonneg)

namespace State

/-- The positive semidefinite square-root matrix of a density state. -/
def sqrtMatrix (rho : State a) : CMatrix a :=
  psdSqrt rho.matrix

/-- A state's square-root matrix is positive semidefinite. -/
theorem sqrtMatrix_pos (rho : State a) :
    rho.sqrtMatrix.PosSemidef :=
  psdSqrt_pos rho.matrix

/-- A state's square-root matrix is Hermitian. -/
theorem sqrtMatrix_isHermitian (rho : State a) :
    rho.sqrtMatrix.IsHermitian :=
  psdSqrt_isHermitian rho.matrix

/-- A state's square-root matrix squares back to the state's density matrix. -/
@[simp]
theorem sqrtMatrix_mul_self (rho : State a) :
    rho.sqrtMatrix * rho.sqrtMatrix = rho.matrix :=
  psdSqrt_mul_self_of_posSemidef rho.pos

end State

end

end QIT
