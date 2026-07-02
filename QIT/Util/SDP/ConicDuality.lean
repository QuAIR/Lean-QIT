/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Convex.Cone.Dual

/-!
# Conic / SDP duality (PR-B foundation)

A reusable `ConeProgram` structure for conic linear programming over a
`ProperCone`, with primal/dual value sets and the pointwise weak duality
inequality (the mathematical core: every primal value ≤ every dual value).

Source: Boyd–Vandenberghe, *Convex Optimization*, §5.9.
-/

@[expose] public section

namespace QIT.SDP

universe u v

/-- A conic linear program: maximize `⟨c, x⟩` subject to `A x = b`, `x ∈ K`. -/
structure ConeProgram (E : Type u) (F : Type v) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] where
  K : ProperCone ℝ E
  A : E →ₗ[ℝ] F
  b : F
  c : E →ₗ[ℝ] ℝ

namespace ConeProgram

variable {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable (P : ConeProgram E F)

/-- Primal feasibility: `x ∈ K` and `A x = b`. -/
def IsPrimalFeasible (x : E) : Prop := x ∈ P.K ∧ P.A x = P.b

/-- The primal value set: `{⟨c, x⟩ | x feasible}`. -/
def primalValueSet : Set ℝ := {v | ∃ x, P.IsPrimalFeasible x ∧ v = P.c x}

/-- Dual feasibility: `Aᴴy - c ∈ K*`, i.e., `∀ x ∈ K, 0 ≤ y(Ax) - cx`. -/
def IsDualFeasible (y : F →ₗ[ℝ] ℝ) : Prop :=
  ∀ x ∈ P.K, 0 ≤ (LinearMap.comp y P.A) x - P.c x

/-- The dual value set: `{⟨b, y⟩ | y dual-feasible}`. -/
def dualValueSet : Set ℝ :=
  {v | ∃ y : F →ₗ[ℝ] ℝ, P.IsDualFeasible y ∧ v = y P.b}

/-- Pointwise weak duality: every primal value ≤ every dual value. -/
theorem weak_duality_pointwise {x : E} (hx : P.IsPrimalFeasible x)
    {y : F →ₗ[ℝ] ℝ} (hy : P.IsDualFeasible y) : P.c x ≤ y P.b := by
  have hkey : 0 ≤ (LinearMap.comp y P.A) x - P.c x := hy x hx.1
  rw [show (LinearMap.comp y P.A) x = y (P.A x) from rfl] at hkey
  rw [hx.2] at hkey
  linarith

/-- Strong duality target: under Slater's condition, primal opt = dual opt. -/
def strong_duality : Prop :=
  (∃ x, P.IsPrimalFeasible x) →  -- TODO: strengthen to Slater once interior is available
  sSup P.primalValueSet = sInf P.dualValueSet

end ConeProgram

end QIT.SDP
