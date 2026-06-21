/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Measurement

/-!
# Finite projective measurements

A finite projective measurement is a finite family of mutually orthogonal
Hermitian idempotent effects summing to the identity.  This is the local PVM
surface needed for the POVM-to-projective realization route, following the
projective-measurement/Naimark reduction recorded in
[ColadangeloGohScarani2016SelfTesting, all_pure_v2.tex:124-128] and
[MayersYao2003SelfTesting, mayers-yao-2003-self-testing.tex:307-325].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {y : Type u} {a : Type v}
variable [Fintype y] [Fintype a] [DecidableEq a]

/--
A finite projective measurement (PVM) with outcomes indexed by `y`.

The fields keep projectivity explicit: each effect is Hermitian and
idempotent, distinct effects are orthogonal, and all effects sum to identity.
-/
structure ProjectiveMeasurement (y : Type u) (a : Type v)
    [Fintype y] [Fintype a] [DecidableEq a] where
  /-- The projection associated with an outcome. -/
  effects : y → CMatrix a
  /-- Each effect is Hermitian. -/
  isHermitian : ∀ outcome, (effects outcome).IsHermitian
  /-- Each effect is idempotent. -/
  idempotent : ∀ outcome, effects outcome * effects outcome = effects outcome
  /-- Distinct effects are mutually orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → effects i * effects j = 0
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ outcome, effects outcome = 1

namespace ProjectiveMeasurement

variable (P : ProjectiveMeasurement y a)

/-- A projective measurement's effects sum to the identity matrix. -/
@[simp]
theorem sum_effects : ∑ outcome, P.effects outcome = 1 :=
  P.sum_eq_one

/-- Each projective effect is positive semidefinite. -/
theorem effect_posSemidef (outcome : y) :
    (P.effects outcome).PosSemidef := by
  have hpsd :
      (Matrix.conjTranspose (P.effects outcome) * P.effects outcome).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self (P.effects outcome)
  rw [P.isHermitian outcome, P.idempotent outcome] at hpsd
  exact hpsd

/-- The square of a projective effect is positive semidefinite. -/
theorem effect_mul_self_posSemidef (outcome : y) :
    (P.effects outcome * P.effects outcome).PosSemidef := by
  rw [P.idempotent outcome]
  exact P.effect_posSemidef outcome

/-- A finite projective measurement is a finite POVM. -/
def toPOVM : POVM y a where
  effects := P.effects
  pos := P.effect_posSemidef
  sum_eq_one := P.sum_eq_one

/-- The POVM associated to a projective measurement has the same effects. -/
@[simp]
theorem toPOVM_effects (outcome : y) :
    P.toPOVM.effects outcome = P.effects outcome :=
  rfl

/-- The POVM associated to a projective measurement has the same completeness law. -/
@[simp]
theorem toPOVM_sum_effects :
    ∑ outcome, P.toPOVM.effects outcome = 1 := by
  simp [toPOVM]

end ProjectiveMeasurement

end

end QIT
