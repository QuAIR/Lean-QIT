/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix

/-!
# Finite POVMs

A positive operator-valued measure (POVM) on a finite-dimensional system is a
finite family of positive semidefinite effects summing to the identity,
following the discrete-outcome POVM definitions and measurement-map route in
[Tomamichel2015FiniteResources, prelim.tex:303-311,813-817].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {x : Type u} {a : Type v}
variable [Fintype x] [Fintype a] [DecidableEq a]

/-- A finite discrete POVM with outcomes indexed by `x`. -/
structure POVM (x : Type u) (a : Type v) [Fintype x] [Fintype a] [DecidableEq a] where
  /-- The POVM effect for outcome `x`. -/
  effects : x → CMatrix a
  /-- Each effect is positive semidefinite. -/
  pos : ∀ y, (effects y).PosSemidef
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ y, effects y = 1

namespace POVM

variable (M : POVM x a)

/-- The POVM effects sum to the identity matrix. -/
@[simp]
theorem sum_effects : ∑ y, M.effects y = 1 := M.sum_eq_one

end POVM

end

end QIT
