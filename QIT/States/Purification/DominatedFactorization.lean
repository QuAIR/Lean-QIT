/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.GramFactorization
public import QIT.Util.Matrix.PosSqrt
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Effects for dominated Gram operators

A positive operator dominated by a Gram matrix can be obtained by inserting a
positive contraction into any given Gram factor. The construction splits the
operator into its outcome and complement square roots and compares the resulting
purification with the given Gram factor. Zero columns ensure sufficient reference
dimension without imposing rank, invertibility, or nonempty-index assumptions.

This is a derived finite-matrix primitive for the flagged-ensemble construction in
[Chiribella2009Networks, comblong-pub.tex:1125-1133]; the flagged-ensemble proof
is given in the same file at lines 1202-1217. Its purification comparison
uses `ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq`, backed
by [Wilde2011Qst, qit-notes.tex:10320-10338], and the positive square-root identities
from `QIT.Util.Matrix.PosSqrt`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
namespace QIT

universe u v

noncomputable section

private theorem gram_fromCols {a b c : Type*} [Fintype b] [Fintype c]
    (X : Matrix a b ℂ) (Y : Matrix a c ℂ) :
    Matrix.fromCols X Y * (Matrix.fromCols X Y).conjTranspose =
      X * X.conjTranspose + Y * Y.conjTranspose := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]

/-- Every positive operator dominated by `A * Aᴴ` is obtained from an effect on
`A`'s column space. The statement includes singular matrices and empty index types.

The effect comes from the first block of a reference isometry between the given
Gram factor and the outcome/complement square-root factor. This is the two-outcome
matrix form of the flagged-purification primitive described in the module header. -/
theorem exists_effect_of_le_gram {a : Type u} {m : Type v}
    [Fintype a] [DecidableEq a] [Fintype m] [DecidableEq m]
    (A : Matrix a m ℂ) (R : CMatrix a) (hR : R.PosSemidef)
    (hRS : R ≤ A * A.conjTranspose) :
    ∃ F : CMatrix m, F.PosSemidef ∧ F ≤ 1 ∧ A * F * A.conjTranspose = R := by
  classical
  let B : Matrix a (a ⊕ (a ⊕ m)) ℂ :=
    Matrix.fromCols (psdSqrt R)
      (Matrix.fromCols (psdSqrt (A * A.conjTranspose - R)) (0 : Matrix a m ℂ))
  have hGram : A * A.conjTranspose = B * B.conjTranspose := by
    dsimp [B]
    rw [gram_fromCols, gram_fromCols, (psdSqrt_isHermitian R).eq,
      (psdSqrt_isHermitian (A * A.conjTranspose - R)).eq,
      psdSqrt_mul_self_of_posSemidef hR,
      psdSqrt_mul_self_of_posSemidef (Matrix.le_iff.mp hRS)]
    simp
  have hcard : Fintype.card m ≤ Fintype.card (a ⊕ (a ⊕ m)) := by
    simp only [Fintype.card_sum]
    omega
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq A B hGram hcard
  let W := V.matrix.transpose
  let C : Matrix m a ℂ := W.toCols₁
  let D : Matrix m (a ⊕ m) ℂ := W.toCols₂
  have hW : Matrix.fromCols C D = W := Matrix.fromCols_toCols W
  have hWW : W * W.conjTranspose = 1 := by
    ext i j
    simpa [Matrix.mul_apply, W, Matrix.conjTranspose_apply, Matrix.one_apply] using V.sum_mul_star i j
  have hCD : C * C.conjTranspose + D * D.conjTranspose = 1 := by
    rw [← gram_fromCols, hW, hWW]
  have hAC : A * C = psdSqrt R := by
    have h := congrArg Matrix.toCols₁ hV
    change B.toCols₁ = (A * W).toCols₁ at h
    rw [← hW, Matrix.mul_fromCols] at h
    exact h.symm
  refine ⟨C * C.conjTranspose, Matrix.posSemidef_self_mul_conjTranspose C, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    have hsub : 1 - C * C.conjTranspose = D * D.conjTranspose := by
      rw [← hCD]
      abel
    rw [hsub]
    exact Matrix.posSemidef_self_mul_conjTranspose D
  · calc
      A * (C * C.conjTranspose) * A.conjTranspose =
          (A * C) * (A * C).conjTranspose := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = R := by
        rw [hAC, (psdSqrt_isHermitian R).eq, psdSqrt_mul_self_of_posSemidef hR]

/-- A positive operator dominated by `S` is a square-root sandwich of an effect.
This specialization of `exists_effect_of_le_gram` applies even when `S` is singular. -/
theorem exists_effect_of_le {a : Type u} [Fintype a] [DecidableEq a]
    (R S : CMatrix a) (hR : R.PosSemidef) (hS : S.PosSemidef) (hRS : R ≤ S) :
    ∃ F : CMatrix a, F.PosSemidef ∧ F ≤ 1 ∧ psdSqrt S * F * psdSqrt S = R := by
  have hGram : psdSqrt S * (psdSqrt S).conjTranspose = S := by
    rw [(psdSqrt_isHermitian S).eq, psdSqrt_mul_self_of_posSemidef hS]
  obtain ⟨F, hF, hF1, hFR⟩ :=
    exists_effect_of_le_gram (psdSqrt S) R hR (hGram.symm ▸ hRS)
  exact ⟨F, hF, hF1, by simpa only [(psdSqrt_isHermitian S).eq] using hFR⟩

end

end QIT
