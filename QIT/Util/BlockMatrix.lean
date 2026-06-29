/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import QIT.States.TraceNorm.Distance
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
theorem sumBlock11_fromBlocks (A : Matrix α α ℂ) (B : Matrix α β ℂ)
    (C : Matrix β α ℂ) (D : Matrix β β ℂ) :
    sumBlock11 (Matrix.fromBlocks A B C D) = A := by
  ext i j
  rfl

@[simp]
theorem sumBlock22_fromBlocks (A : Matrix α α ℂ) (B : Matrix α β ℂ)
    (C : Matrix β α ℂ) (D : Matrix β β ℂ) :
    sumBlock22 (Matrix.fromBlocks A B C D) = D := by
  ext i j
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

/-- The trace of a block-diagonal `Sum` matrix is the sum of the diagonal-block
traces. -/
theorem trace_fromBlocks_diagonal [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (D : Matrix β β ℂ) :
    (Matrix.fromBlocks A 0 0 D).trace = A.trace + D.trace := by
  classical
  simp [Matrix.trace]

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

/-- A block-diagonal matrix with positive semidefinite diagonal blocks is
positive semidefinite. -/
theorem fromBlocks_diagonal_posSemidef [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} {D : Matrix β β ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.IsHermitian.ext_iff.mp hA.isHermitian,
        Matrix.IsHermitian.ext_iff.mp hD.isHermitian]
  · intro x
    let xl : α → ℂ := fun i => x (Sum.inl i)
    let xr : β → ℂ := fun i => x (Sum.inr i)
    have hleft : 0 ≤ star xl ⬝ᵥ A.mulVec xl :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 xl
    have hright : 0 ≤ star xr ⬝ᵥ D.mulVec xr :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hD).2 xr
    have hsum : 0 ≤ star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr :=
      add_nonneg hleft hright
    have hquad :
        star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D).mulVec x =
          star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_fromBlocks, Matrix.dotProduct_block]
      simp [Matrix.dotProduct_mulVec, xl, xr]
      change
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr =
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr
      rfl
    simpa [hquad] using hsum

/-- The positive square root of a block-diagonal positive semidefinite matrix is
the block diagonal of the positive square roots. -/
theorem fromBlocks_diagonal_psdSqrt [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} {D : Matrix β β ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    QIT.psdSqrt (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ) =
      Matrix.fromBlocks (QIT.psdSqrt A) 0 0 (QIT.psdSqrt D) := by
  classical
  let S : Matrix (Sum α β) (Sum α β) ℂ :=
    Matrix.fromBlocks (QIT.psdSqrt A) 0 0 (QIT.psdSqrt D)
  have hSpos : S.PosSemidef := by
    dsimp [S]
    exact fromBlocks_diagonal_posSemidef (QIT.psdSqrt_pos A) (QIT.psdSqrt_pos D)
  have hSsq : S * S = (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ) := by
    dsimp [S]
    rw [Matrix.fromBlocks_multiply]
    simp [QIT.psdSqrt_mul_self_of_posSemidef hA,
      QIT.psdSqrt_mul_self_of_posSemidef hD]
  simpa [QIT.psdSqrt, S] using
    (CFC.sqrt_unique (a := (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ))
      (b := S) hSsq hSpos.nonneg)

/-- The trace norm of a block-diagonal matrix is the sum of the trace norms of
the diagonal blocks. -/
theorem traceNorm_fromBlocks_diagonal [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    QIT.traceNorm (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ) =
      QIT.traceNorm X + QIT.traceNorm Y := by
  classical
  have hgram :
      (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ)ᴴ *
          (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ) =
        Matrix.fromBlocks (Xᴴ * X) 0 0 (Yᴴ * Y) := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp
  rw [QIT.traceNorm, hgram,
    fromBlocks_diagonal_psdSqrt (Matrix.posSemidef_conjTranspose_mul_self X)
      (Matrix.posSemidef_conjTranspose_mul_self Y),
    trace_fromBlocks_diagonal]
  simp [QIT.traceNorm]

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
