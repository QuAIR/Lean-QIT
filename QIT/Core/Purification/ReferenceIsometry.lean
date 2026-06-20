/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Purification.Predicate

/-!
# Reference-system isometries

This module fixes the matrix convention for an isometry acting only on a
purifying reference register. The source-system convention follows the
purification equivalence route registered from [Wilde2011Qst,
qit-notes.tex:10320-10338] and [Gour2024Resources, BookQRT.tex:2051-2069]:
two purifications of the same target state are compared by an isometry on the
reference system.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

/-- A matrix isometry from reference system `r₁` into reference system `r₂`.

The matrix has rows indexed by the output reference and columns indexed by the
input reference; the convention is `Vᴴ * V = 1`. -/
structure ReferenceIsometry (r₁ : Type u) (r₂ : Type v)
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂] where
  matrix : Matrix r₂ r₁ Complex
  isometry : Matrix.conjTranspose matrix * matrix = 1

namespace ReferenceIsometry

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

variable (V : ReferenceIsometry r₁ r₂)

/-- Entrywise orthonormal-column form of `Vᴴ * V = 1`. -/
theorem sum_mul_star (i j : r₁) :
    (Finset.univ.sum fun k : r₂ => V.matrix k i * star (V.matrix k j)) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun V.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, eq_comm, mul_comm] using h

/-- The reference-indexed block of a bipartite matrix at fixed target entries. -/
def targetBlock (X : CMatrix (Prod r₁ a)) (x y : a) : CMatrix r₁ :=
  fun i j => X (i, x) (j, y)

/-- Apply a reference isometry to the reference side of a bipartite matrix. -/
def applyMatrix (X : CMatrix (Prod r₁ a)) : CMatrix (Prod r₂ a) :=
  fun x y => (V.matrix * targetBlock X x.2 y.2 * Matrix.conjTranspose V.matrix) x.1 y.1

/-- Apply a reference isometry to the reference side of a bipartite amplitude. -/
def applyAmp (ψ : Prod r₁ a -> Complex) : Prod r₂ a -> Complex :=
  fun x => V.matrix.mulVec (fun i : r₁ => ψ (i, x.2)) x.1

/-- Applying a reference isometry to amplitudes matches conjugating the rank-one matrix. -/
theorem rankOne_applyAmp (ψ : Prod r₁ a -> Complex) :
    rankOneMatrix (V.applyAmp ψ) = V.applyMatrix (rankOneMatrix ψ) := by
  ext x y
  simp [rankOneMatrix, applyAmp, applyMatrix, targetBlock, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Conjugating a reference block by an isometry preserves its trace. -/
theorem trace_apply_block (B : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix).trace = B.trace := by
  rw [Matrix.trace_mul_cycle, V.isometry, Matrix.one_mul]

/-- Applying a reference isometry does not change the target marginal. -/
theorem partialTraceA_applyMatrix (X : CMatrix (Prod r₁ a)) :
    partialTraceA (a := r₂) (b := a) (V.applyMatrix X) =
      partialTraceA (a := r₁) (b := a) X := by
  ext x y
  exact V.trace_apply_block (targetBlock X x y)

/-- Apply a reference isometry to a bipartite pure vector. -/
def applyPureVector [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod r₁ a)) :
    PureVector (Prod r₂ a) where
  amp := V.applyAmp Ψ.amp
  trace_rankOne_eq_one := by
    have h := congrArg Matrix.trace (V.partialTraceA_applyMatrix (rankOneMatrix Ψ.amp))
    rw [partialTraceA_trace, partialTraceA_trace] at h
    rw [V.rankOne_applyAmp Ψ.amp, h, Ψ.trace_rankOne_eq_one]

/-- The amplitude of `applyPureVector` unfolds to `applyAmp`. -/
theorem applyPureVector_amp [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod r₁ a)) :
    (V.applyPureVector Ψ).amp = V.applyAmp Ψ.amp :=
  rfl

/-- A reference isometry preserves the target state purified by a pure vector. -/
theorem applyPureVector_purifies [Fintype a] [DecidableEq a]
    {Ψ : PureVector (Prod r₁ a)} {ρ : State a} (hΨ : Ψ.Purifies ρ) :
    (V.applyPureVector Ψ).Purifies ρ := by
  rw [PureVector.purifies_iff]
  rw [PureVector.state_matrix]
  change partialTraceA (a := r₂) (b := a) (rankOneMatrix (V.applyAmp Ψ.amp)) = ρ.matrix
  rw [V.rankOne_applyAmp]
  rw [V.partialTraceA_applyMatrix]
  exact hΨ

end ReferenceIsometry

end

end QIT
