/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Information.Entropy

/-!
# Trace distance

Definition-level trace norm and trace distance API for finite-dimensional
matrices and density states. The source gate is registered under
`m5-trace-norm-definition-and-singular-values` and
`m5-trace-distance-definition-and-bounds`.

This module intentionally records only locally provable facts. Spectral trace
norm formulas, triangle inequalities, state upper bounds, and Fuchs-van de
Graaf remain downstream proof obligations.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The CFC square root of the zero matrix is zero. -/
@[simp]
theorem psdSqrt_zero : psdSqrt (0 : CMatrix a) = 0 := by
  simp [psdSqrt]

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg (M : CMatrix a) : 0 ≤ traceNorm M := by
  rw [traceNorm]
  have h : 0 ≤ (psdSqrt (Matrix.conjTranspose M * M)).trace :=
    Matrix.PosSemidef.trace_nonneg (psdSqrt_pos (Matrix.conjTranspose M * M))
  have hre := (Complex.nonneg_iff.mp h).1
  simpa using hre

/-- The zero matrix has trace norm zero. -/
@[simp]
theorem traceNorm_zero : traceNorm (0 : CMatrix a) = 0 := by
  simp [traceNorm]

/-- The trace norm is invariant under negation. -/
@[simp]
theorem traceNorm_neg (M : CMatrix a) : traceNorm (-M) = traceNorm M := by
  simp [traceNorm]

/-- Trace distance between finite-dimensional complex matrices. -/
def traceDistance (M N : CMatrix a) : ℝ :=
  traceNorm (M - N)

/-- Normalized trace distance, using the QIT convention `1 / 2 * ‖M - N‖₁`. -/
def normalizedTraceDistance (M N : CMatrix a) : ℝ :=
  (1 / 2 : ℝ) * traceDistance M N

@[simp]
theorem traceDistance_eq_traceNorm_sub (M N : CMatrix a) :
    traceDistance M N = traceNorm (M - N) :=
  rfl

/-- Trace distance is nonnegative. -/
theorem traceDistance_nonneg (M N : CMatrix a) : 0 ≤ traceDistance M N :=
  traceNorm_nonneg (M - N)

@[simp]
theorem traceDistance_self (M : CMatrix a) : traceDistance M M = 0 := by
  simp [traceDistance]

/-- Trace distance is symmetric. -/
theorem traceDistance_comm (M N : CMatrix a) : traceDistance M N = traceDistance N M := by
  calc
    traceDistance M N = traceNorm (M - N) := rfl
    _ = traceNorm (-(M - N)) := by rw [traceNorm_neg]
    _ = traceDistance N M := by simp [traceDistance, sub_eq_add_neg]

@[simp]
theorem normalizedTraceDistance_eq (M N : CMatrix a) :
    normalizedTraceDistance M N = (1 / 2 : ℝ) * traceDistance M N :=
  rfl

/-- Normalized trace distance is nonnegative. -/
theorem normalizedTraceDistance_nonneg (M N : CMatrix a) :
    0 ≤ normalizedTraceDistance M N :=
  mul_nonneg (by norm_num) (traceDistance_nonneg M N)

@[simp]
theorem normalizedTraceDistance_self (M : CMatrix a) :
    normalizedTraceDistance M M = 0 := by
  simp [normalizedTraceDistance]

/-- Normalized trace distance is symmetric. -/
theorem normalizedTraceDistance_comm (M N : CMatrix a) :
    normalizedTraceDistance M N = normalizedTraceDistance N M := by
  rw [normalizedTraceDistance, normalizedTraceDistance, traceDistance_comm]

namespace State

/-- Trace distance between density states, defined through their matrices. -/
def traceDistance (rho sigma : State a) : ℝ :=
  QIT.traceDistance rho.matrix sigma.matrix

/-- Normalized trace distance between density states. -/
def normalizedTraceDistance (rho sigma : State a) : ℝ :=
  QIT.normalizedTraceDistance rho.matrix sigma.matrix

@[simp]
theorem traceDistance_eq_matrix (rho sigma : State a) :
    rho.traceDistance sigma = QIT.traceDistance rho.matrix sigma.matrix :=
  rfl

theorem traceDistance_nonneg (rho sigma : State a) : 0 ≤ rho.traceDistance sigma :=
  QIT.traceDistance_nonneg rho.matrix sigma.matrix

@[simp]
theorem traceDistance_self (rho : State a) : rho.traceDistance rho = 0 := by
  simp [State.traceDistance]

theorem traceDistance_comm (rho sigma : State a) :
    rho.traceDistance sigma = sigma.traceDistance rho :=
  QIT.traceDistance_comm rho.matrix sigma.matrix

@[simp]
theorem normalizedTraceDistance_eq_matrix (rho sigma : State a) :
    rho.normalizedTraceDistance sigma =
      QIT.normalizedTraceDistance rho.matrix sigma.matrix :=
  rfl

theorem normalizedTraceDistance_nonneg (rho sigma : State a) :
    0 ≤ rho.normalizedTraceDistance sigma :=
  QIT.normalizedTraceDistance_nonneg rho.matrix sigma.matrix

@[simp]
theorem normalizedTraceDistance_self (rho : State a) :
    rho.normalizedTraceDistance rho = 0 := by
  simp [State.normalizedTraceDistance]

theorem normalizedTraceDistance_comm (rho sigma : State a) :
    rho.normalizedTraceDistance sigma = sigma.normalizedTraceDistance rho :=
  QIT.normalizedTraceDistance_comm rho.matrix sigma.matrix

end State

end

end QIT
