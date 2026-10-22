/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.Util.Matrix

/-!
# Positive matrix compressions

Summing amplitudes over a finite family gives a rectangular matrix congruence;
summing only matching row/column indices gives a sum of positive submatrices.
Neither operation requires inhabited index types or injective configuration maps.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
universe u v w
namespace QIT.HigherOrder.Comb

variable {A : Type u} {B : Type v} {Z : Type w}

/-- Sum independently over the row and column configurations. Repeated images
of `f` retain their multiplicity, as required for amplitude contraction. -/
def sumCompression [Fintype Z] (f : B → Z → A) (M : CMatrix A) : CMatrix B :=
  fun b b' => ∑ z, ∑ z', M (f b z) (f b' z')

/-- Sum over the same configuration in the row and column. -/
def diagonalSum [Fintype Z] (f : B → Z → A) (M : CMatrix A) : CMatrix B :=
  fun b b' => ∑ z, M (f b z) (f b' z)

/-- Independent row/column summation preserves positivity by rectangular
congruence. No injectivity or inhabitance hypothesis is needed. -/
theorem sumCompression_posSemidef [Fintype A] [Fintype B] [Fintype Z]
    (f : B → Z → A) {M : CMatrix A} (hM : M.PosSemidef) :
    (sumCompression f M).PosSemidef := by
  classical
  let L : Z → Matrix A B ℂ := fun z a b => if a = f b z then 1 else 0
  have hTerm (z z' : Z) : (L z)ᴴ * M * L z' =
      (fun b b' => M (f b z) (f b' z')) := by
    ext b b'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [L]
  have hEq : sumCompression f M = (∑ z, L z)ᴴ * M * (∑ z, L z) := by
    simp only [Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum, hTerm]
    ext b b'
    simp only [sumCompression, Matrix.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    change _ = (∑ z', (fun b b' => M (f b z') (f b' z) : CMatrix B)) b b'
    exact (Matrix.sum_apply b b' Finset.univ
      (fun z' => (fun b b' => M (f b z') (f b' z) : CMatrix B))).symm
  rw [hEq]
  exact hM.conjTranspose_mul_mul_same _

/-- Diagonal summation preserves positivity as a finite sum of submatrices.
The original and remaining configuration types need not be finite. -/
theorem diagonalSum_posSemidef [Fintype Z]
    (f : B → Z → A) {M : CMatrix A} (hM : M.PosSemidef) :
    (diagonalSum f M).PosSemidef := by
  have hEq : diagonalSum f M = ∑ z, M.submatrix (fun b => f b z) (fun b => f b z) := by
    ext b b'
    simp [diagonalSum, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hEq]
  exact Matrix.posSemidef_sum Finset.univ fun z _ => hM.submatrix (fun b => f b z)

end QIT.HigherOrder.Comb
end
