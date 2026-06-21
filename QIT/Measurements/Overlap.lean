/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Measurements.Projective

/-!
# Measurement overlap for two projective measurements

The overlap constant `c = max_{i,j} Tr(P_i Q_j)` for two finite projective
measurements on the same system. For rank-one measurements this specializes to
the Maassen-Uffink overlap `max_{x,y} |<phi_x | vartheta_y>|^2`.

Source: Tomamichel2015FiniteResources, `apps.tex` (Eq. `eq:defc`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {x : Type u} {y : Type v} {a : Type w}
variable [Fintype x] [Fintype y] [Fintype a] [DecidableEq a]
variable (P : ProjectiveMeasurement x a) (Q : ProjectiveMeasurement y a)

namespace ProjectiveMeasurement

/-- `Tr(P_i Q_j) >= 0` for projective effects.

Proved via the idempotent congruence `Tr(P_i Q_j) = Tr(P_i Q_j P_i)` with
`P_i Q_j P_i` positive semidefinite (congruence of the PSD `Q_j` by the
Hermitian `P_i`); no matrix square root is needed because `P_i` is idempotent. -/
theorem effect_mul_effect_trace_re_nonneg (i : x) (j : y) :
    0 ≤ ((P.effects i * Q.effects j).trace).re := by
  have hPSD : (P.effects i * Q.effects j * P.effects i).PosSemidef := by
    have h := (Q.effect_posSemidef j).mul_mul_conjTranspose_same (P.effects i)
    rwa [P.isHermitian i] at h
  have hEq : (P.effects i * Q.effects j * P.effects i).trace =
      (P.effects i * Q.effects j).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, P.idempotent i]
  rw [← hEq]
  exact (Matrix.PosSemidef.trace_nonneg hPSD).1

/-- The measurement overlap `c = max_{i,j} Tr(P_i Q_j)` as a nonnegative real.

Specializes to `max_{x,y} |<phi_x|vartheta_y>|^2` when both measurements are
rank-one (orthonormal-basis) measurements. -/
def measurementOverlap : ℝ≥0 :=
  (Finset.univ : Finset x).sup fun i =>
    (Finset.univ : Finset y).sup fun j =>
      ⟨((P.effects i * Q.effects j).trace).re,
        effect_mul_effect_trace_re_nonneg P Q i j⟩

/-- The measurement overlap is nonnegative. -/
theorem measurementOverlap_nonneg : 0 ≤ P.measurementOverlap Q :=
  bot_le

/-- The overlap unfolds to the nested finite supremum of `Tr(P_i Q_j)`. -/
@[simp]
theorem measurementOverlap_eq :
    P.measurementOverlap Q =
      (Finset.univ : Finset x).sup fun i =>
        (Finset.univ : Finset y).sup fun j =>
          ⟨((P.effects i * Q.effects j).trace).re,
            effect_mul_effect_trace_re_nonneg P Q i j⟩ :=
  rfl

end ProjectiveMeasurement

end

end QIT
