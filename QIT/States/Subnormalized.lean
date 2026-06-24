/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import QIT.States.TraceNorm.Distance

/-!
# Subnormalized finite-dimensional states

This module provides the finite-dimensional subnormalized-state carrier needed
by the smooth-entropy, AEP, and decoupling proof routes. A subnormalized state is
a positive semidefinite matrix with trace at most one. The metric layer below
follows the registered generalized-fidelity and purified-distance source
claims [Tomamichel2015FiniteResources, metric.tex:390-416] and
[Tomamichel2015FiniteResources, metric.tex:512-513].

The API is intentionally infrastructure-only: smooth min/max duality and AEP
inequalities live in downstream information-theoretic modules.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

/-- A finite-dimensional subnormalized density state. -/
structure SubnormalizedState (a : Type u) [Fintype a] [DecidableEq a] where
  matrix : CMatrix a
  pos : matrix.PosSemidef
  trace_le_one : matrix.trace.re ≤ 1

namespace SubnormalizedState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Subnormalized states are equal when their matrices are equal. -/
@[ext]
theorem ext {ρ σ : SubnormalizedState a} (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- The density matrix of a subnormalized state is Hermitian. -/
theorem isHermitian (ρ : SubnormalizedState a) : ρ.matrix.IsHermitian :=
  ρ.pos.isHermitian

/-- The trace of a subnormalized state is nonnegative. -/
theorem trace_nonneg (ρ : SubnormalizedState a) : 0 ≤ ρ.matrix.trace.re :=
  (Matrix.PosSemidef.trace_nonneg ρ.pos).1

/-- The trace of a subnormalized state is real. -/
theorem trace_im_zero (ρ : SubnormalizedState a) : ρ.matrix.trace.im = 0 :=
  (Matrix.PosSemidef.trace_nonneg ρ.pos).2.symm

/-- The trace of a subnormalized state lies in the real unit interval. -/
theorem trace_mem_Icc (ρ : SubnormalizedState a) :
    ρ.matrix.trace.re ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ρ.trace_nonneg, ρ.trace_le_one⟩

/-- Product of subnormalized states as a Kronecker product. -/
def prod (ρ : SubnormalizedState a) (σ : SubnormalizedState b) :
    SubnormalizedState (Prod a b) where
  matrix := Matrix.kronecker ρ.matrix σ.matrix
  pos := ρ.pos.kronecker σ.pos
  trace_le_one := by
    change ((Matrix.kroneckerMap (fun x y => x * y) ρ.matrix σ.matrix).trace).re ≤ 1
    rw [Matrix.trace_kronecker]
    rw [Complex.mul_re, ρ.trace_im_zero, σ.trace_im_zero]
    nlinarith [ρ.trace_nonneg, σ.trace_nonneg, ρ.trace_le_one, σ.trace_le_one]

/-- `Tr_A` of a product subnormalized state leaves the second factor scaled by
the trace of the first. -/
theorem partialTraceA_prod (ρ : SubnormalizedState a) (σ : SubnormalizedState b) :
    partialTraceA (a := a) (b := b) (ρ.prod σ).matrix =
      matrixScale ρ.matrix.trace σ.matrix := by
  rw [prod, partialTraceA_kronecker]

/-- `Tr_B` of a product subnormalized state leaves the first factor scaled by
the trace of the second. -/
theorem partialTraceB_prod (ρ : SubnormalizedState a) (σ : SubnormalizedState b) :
    partialTraceB (a := a) (b := b) (ρ.prod σ).matrix =
      matrixScale σ.matrix.trace ρ.matrix := by
  rw [prod, partialTraceB_kronecker]

/-- Marginal subnormalized state on the first subsystem. -/
def marginalA (ρ : SubnormalizedState (Prod a b)) : SubnormalizedState a where
  matrix := partialTraceB (a := a) (b := b) ρ.matrix
  pos := partialTraceB_posSemidef ρ.pos
  trace_le_one := by
    rw [partialTraceB_trace]
    exact ρ.trace_le_one

/-- Marginal subnormalized state on the second subsystem. -/
def marginalB (ρ : SubnormalizedState (Prod a b)) : SubnormalizedState b where
  matrix := partialTraceA (a := a) (b := b) ρ.matrix
  pos := partialTraceA_posSemidef ρ.pos
  trace_le_one := by
    rw [partialTraceA_trace]
    exact ρ.trace_le_one

@[simp]
theorem marginalA_matrix (ρ : SubnormalizedState (Prod a b)) :
    ρ.marginalA.matrix = partialTraceB (a := a) (b := b) ρ.matrix := rfl

@[simp]
theorem marginalB_matrix (ρ : SubnormalizedState (Prod a b)) :
    ρ.marginalB.matrix = partialTraceA (a := a) (b := b) ρ.matrix := rfl

/-- Generalized fidelity for finite-dimensional subnormalized states, following
the squared convention used by the Tomamichel purified-distance route. -/
def generalizedFidelity (ρ σ : SubnormalizedState a) : ℝ :=
  (traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix) +
    Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re))) ^ 2

@[simp]
theorem generalizedFidelity_eq (ρ σ : SubnormalizedState a) :
    ρ.generalizedFidelity σ =
      (traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix) +
        Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re))) ^ 2 :=
  rfl

/-- Purified distance for finite-dimensional subnormalized states,
`P(ρ,σ) = sqrt(1 - F_*(ρ,σ))`. -/
def purifiedDistance (ρ σ : SubnormalizedState a) : ℝ :=
  Real.sqrt (1 - ρ.generalizedFidelity σ)

@[simp]
theorem purifiedDistance_eq (ρ σ : SubnormalizedState a) :
    ρ.purifiedDistance σ = Real.sqrt (1 - ρ.generalizedFidelity σ) :=
  rfl

/-- Closed purified-distance epsilon ball around a subnormalized state. -/
def purifiedBall (ρ : SubnormalizedState a) (ε : ℝ) (σ : SubnormalizedState a) : Prop :=
  ρ.purifiedDistance σ ≤ ε

@[simp]
theorem purifiedBall_eq (ρ σ : SubnormalizedState a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔ ρ.purifiedDistance σ ≤ ε :=
  Iff.rfl

/-- Purified-distance balls are monotone in the smoothing radius. -/
theorem purifiedBall_mono {ρ σ : SubnormalizedState a} {ε δ : ℝ} (hεδ : ε ≤ δ) :
    ρ.purifiedBall ε σ → ρ.purifiedBall δ σ := by
  intro hball
  exact le_trans hball hεδ

end SubnormalizedState

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- View a normalized density state as a subnormalized state. -/
def toSubnormalized (ρ : State a) : SubnormalizedState a where
  matrix := ρ.matrix
  pos := ρ.pos
  trace_le_one := by
    rw [ρ.trace_eq_one]
    norm_num

@[simp]
theorem toSubnormalized_matrix (ρ : State a) :
    ρ.toSubnormalized.matrix = ρ.matrix := rfl

@[simp]
theorem toSubnormalized_trace (ρ : State a) :
    ρ.toSubnormalized.matrix.trace = 1 :=
  ρ.trace_eq_one

end State

end

end QIT
