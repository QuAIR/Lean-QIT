/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Two-by-two block matrix helpers

Small wrappers for the `Sum`-indexed `2 × 2` block decomposition used by the
positive/negative spectral split in trace-norm arguments.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

universe u v

noncomputable section

variable {α : Type u} {β : Type v}

/-- The upper-left block of a matrix indexed by `α ⊕ β`. -/
def sumBlock11 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix α α ℂ :=
  M.submatrix Sum.inl Sum.inl

/-- The upper-right block of a matrix indexed by `α ⊕ β`. -/
def sumBlock12 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix α β ℂ :=
  M.submatrix Sum.inl Sum.inr

/-- The lower-left block of a matrix indexed by `α ⊕ β`. -/
def sumBlock21 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix β α ℂ :=
  M.submatrix Sum.inr Sum.inl

/-- The lower-right block of a matrix indexed by `α ⊕ β`. -/
def sumBlock22 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix β β ℂ :=
  M.submatrix Sum.inr Sum.inr

/-- Embed a matrix as the upper-left block of a `Sum`-indexed block matrix. -/
def sumBlockEmbed11 (A : Matrix α α ℂ) : Matrix (Sum α β) (Sum α β) ℂ :=
  Matrix.fromBlocks A 0 0 0

@[simp]
theorem sumBlock11_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i j : α) :
    sumBlock11 M i j = M (Sum.inl i) (Sum.inl j) :=
  rfl

@[simp]
theorem sumBlock12_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i : α) (j : β) :
    sumBlock12 M i j = M (Sum.inl i) (Sum.inr j) :=
  rfl

@[simp]
theorem sumBlock21_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i : β) (j : α) :
    sumBlock21 M i j = M (Sum.inr i) (Sum.inl j) :=
  rfl

@[simp]
theorem sumBlock22_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i j : β) :
    sumBlock22 M i j = M (Sum.inr i) (Sum.inr j) :=
  rfl

@[simp]
theorem sumBlockEmbed11_apply_inl_inl (A : Matrix α α ℂ) (i j : α) :
    sumBlockEmbed11 (β := β) A (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
theorem sumBlockEmbed11_apply_inl_inr (A : Matrix α α ℂ) (i : α) (j : β) :
    sumBlockEmbed11 (β := β) A (Sum.inl i) (Sum.inr j) = 0 := by
  simp [sumBlockEmbed11]

@[simp]
theorem sumBlockEmbed11_apply_inr_inl (A : Matrix α α ℂ) (i : β) (j : α) :
    sumBlockEmbed11 (β := β) A (Sum.inr i) (Sum.inl j) = 0 := by
  simp [sumBlockEmbed11]

@[simp]
theorem sumBlockEmbed11_apply_inr_inr (A : Matrix α α ℂ) (i j : β) :
    sumBlockEmbed11 (β := β) A (Sum.inr i) (Sum.inr j) = 0 := by
  simp [sumBlockEmbed11]

/-- Embedding in the upper-left block preserves trace. -/
theorem trace_sumBlockEmbed11 [Fintype α] [Fintype β] (A : Matrix α α ℂ) :
    (sumBlockEmbed11 (β := β) A).trace = A.trace := by
  simp [sumBlockEmbed11, Matrix.trace]

/-- Reassemble a `Sum`-indexed matrix from its four blocks. -/
theorem fromBlocks_sumBlocks (M : Matrix (Sum α β) (Sum α β) ℂ) :
    Matrix.fromBlocks (sumBlock11 M) (sumBlock12 M) (sumBlock21 M) (sumBlock22 M) = M := by
  ext (_ | _) (_ | _) <;> rfl

/-- The upper-left block of a positive semidefinite block matrix is positive semidefinite. -/
theorem sumBlock11_posSemidef {M : Matrix (Sum α β) (Sum α β) ℂ}
    (hM : M.PosSemidef) :
    (sumBlock11 M).PosSemidef :=
  hM.submatrix Sum.inl

/-- The lower-right block of a positive semidefinite block matrix is positive semidefinite. -/
theorem sumBlock22_posSemidef {M : Matrix (Sum α β) (Sum α β) ℂ}
    (hM : M.PosSemidef) :
    (sumBlock22 M).PosSemidef :=
  hM.submatrix Sum.inr

/-- Off-diagonal blocks of a Hermitian block matrix are adjoints. -/
theorem sumBlock21_eq_conjTranspose_sumBlock12_of_isHermitian
    {M : Matrix (Sum α β) (Sum α β) ℂ} (hM : M.IsHermitian) :
    sumBlock21 M = (sumBlock12 M)ᴴ := by
  rw [Matrix.IsHermitian] at hM
  ext i j
  have h := congrArg (fun N : Matrix (Sum α β) (Sum α β) ℂ =>
    N (Sum.inr i) (Sum.inl j)) hM
  simpa [sumBlock21, sumBlock12, Matrix.conjTranspose_apply] using h.symm

end

end Matrix
