/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Realization
public import QIT.Util.Matrix.PosSqrt
public import QIT.States.Purification.DominatedFactorization
/-!
# Dominated outcomes on the terminal memory of a comb

Every positive operator dominated by the Choi matrix of a given memory chain
is obtained by measuring an effect on that chain's final memory. The construction
uses a rectangular Gram factorization and covers singular Choi matrices and
empty finite systems, without an inverse or a minimal-memory assumption.

The outcome map is explicitly the partial trace after applying `I ⊗ √F` to the
chain's coherent isometry. With the input-first Choi convention its matrix is
`A * F.transpose * A.conjTranspose`; the transpose is essential over complex
scalars. An effect and its complement recover the original chain map.

This is the single dominated-outcome step of probabilistic network realization
[Chiribella2009Networks, comblong-pub.tex:1125-1133], applied to the domination
definition [Chiribella2009Networks, comblong-pub.tex:1425-1433]. A simultaneous
finite-outcome projective measurement is a separate construction.
-/

@[expose] public section
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
universe u
namespace QIT.HigherOrder
namespace MemoryChain
variable {n : Nat} {I O E : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- The rectangular Kraus amplitude of the given chain, with final memory as column index. -/
def choiAmplitude (c : MemoryChain I O E) :
    Matrix (Comb.Space I O) (E (Fin.last n)) ℂ :=
  fun p e => c.kraus e p.2 p.1

/-- The chain Choi matrix is the Gram matrix of its final-memory amplitude. -/
theorem choiAmplitude_gram (c : MemoryChain I O E) :
    c.choiAmplitude * c.choiAmplitude.conjTranspose = MatrixMap.choi c.chainMap := by
  ext p q
  simp only [choiAmplitude, chainMap, MatrixMap.choi_ofKraus, Matrix.sum_apply,
    Matrix.vecMulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rfl

/-- Kraus operators obtained by applying the positive square root of a terminal-memory effect. -/
def terminalEffectKraus (c : MemoryChain I O E) (F : CMatrix (E (Fin.last n)))
    (k : E (Fin.last n)) : Matrix (∀ j, O j) (∀ j, I j) ℂ :=
  fun o i => (c.choiAmplitude * (psdSqrt F).transpose) (i, o) k

/-- The output operation after filtering the final memory by `√F` and discarding it. -/
def terminalEffectMap (c : MemoryChain I O E) (F : CMatrix (E (Fin.last n))) :
    MatrixMap (∀ j, I j) (∀ j, O j) := MatrixMap.ofKraus (c.terminalEffectKraus F)

/-- The physical terminal-memory effect enters the input-first Choi formula transposed. -/
theorem terminalEffectMap_choi (c : MemoryChain I O E) (F : CMatrix (E (Fin.last n)))
    (hF : F.PosSemidef) :
    MatrixMap.choi (c.terminalEffectMap F) = c.choiAmplitude * F.transpose *
      c.choiAmplitude.conjTranspose := by
  have hgram : MatrixMap.choi (c.terminalEffectMap F) =
      (c.choiAmplitude * (psdSqrt F).transpose) *
        (c.choiAmplitude * (psdSqrt F).transpose).conjTranspose := by
    ext p q
    simp only [terminalEffectMap, terminalEffectKraus, MatrixMap.choi_ofKraus,
      Matrix.sum_apply, Matrix.vecMulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rfl
  have hs : (psdSqrt F).transpose * ((psdSqrt F).transpose).conjTranspose = F.transpose := by
    rw [Matrix.transpose_conjTranspose, ← Matrix.conjTranspose_transpose, (psdSqrt_isHermitian F).eq,
      ← Matrix.transpose_mul, psdSqrt_mul_self_of_posSemidef hF]
  rw [hgram, Matrix.conjTranspose_mul]
  calc
    _ = c.choiAmplitude * ((psdSqrt F).transpose *
      ((psdSqrt F).transpose).conjTranspose) * c.choiAmplitude.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hs]


/-- The outcome Kraus operators are exactly the slices of `(I ⊗ √F)` applied to the original coherent isometry. -/
theorem terminalEffectKraus_eq_filter (c : MemoryChain I O E)
    (F : CMatrix (E (Fin.last n))) (k : E (Fin.last n))
    (o : ∀ j, O j) (i : ∀ j, I j) :
    c.terminalEffectKraus F k o i =
      (Matrix.kronecker (1 : CMatrix (∀ j, O j)) (psdSqrt F) *
        c.coherentIsometry.matrix) (o, k) i := by
  have hfilter {α β γ : Type u} [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β] (S : CMatrix β)
      (W : Matrix (α × β) γ ℂ) (x : α) (y : β) (z : γ) :
      (Matrix.kronecker (1 : CMatrix α) S * W) (x, y) z =
        ∑ j, S y j * W (x, j) z := by
    rw [Matrix.mul_apply]
    simp [Fintype.sum_prod_type, Matrix.one_apply]
  calc
    c.terminalEffectKraus F k o i =
        ∑ e, psdSqrt F k e * c.coherentIsometry.matrix (o, e) i := by
      change (c.choiAmplitude * (psdSqrt F).transpose) (i, o) k = _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro e _
      change c.kraus e o i * psdSqrt F k e = psdSqrt F k e * c.kraus e o i
      exact mul_comm _ _
    _ = _ := (hfilter (psdSqrt F) c.coherentIsometry.matrix o k i).symm

/-- The outcome is physically a filter on the given chain’s final memory followed by partial trace. -/
theorem terminalEffectMap_eq_partialTrace (c : MemoryChain I O E)
    (F : CMatrix (E (Fin.last n))) (X : CMatrix (∀ j, I j)) :
    c.terminalEffectMap F X =
      partialTraceB ((Matrix.kronecker (1 : CMatrix (∀ j, O j)) (psdSqrt F) *
        c.coherentIsometry.matrix) * X *
        (Matrix.kronecker (1 : CMatrix (∀ j, O j)) (psdSqrt F) *
          c.coherentIsometry.matrix).conjTranspose) := by
  let V := Matrix.kronecker (1 : CMatrix (∀ j, O j)) (psdSqrt F) *
    c.coherentIsometry.matrix
  have hk (k : E (Fin.last n)) (o : ∀ j, O j) (i : ∀ j, I j) :
      c.terminalEffectKraus F k o i = V (o, k) i :=
    terminalEffectKraus_eq_filter c F k o i
  change (MatrixMap.ofKraus (c.terminalEffectKraus F)) X = partialTraceB (V * X * V.conjTranspose)
  ext o p
  change (∑ e, c.terminalEffectKraus F e * X * (c.terminalEffectKraus F e).conjTranspose) o p = _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceB, hk]

/-- A terminal-memory effect produces a Choi operator dominated by the original chain. -/
theorem terminalEffectMap_choi_le (c : MemoryChain I O E)
    (F : CMatrix (E (Fin.last n))) (hF : F.PosSemidef) (hF1 : F ≤ 1) :
    MatrixMap.choi (c.terminalEffectMap F) ≤ MatrixMap.choi c.chainMap := by
  rw [terminalEffectMap_choi c F hF, ← choiAmplitude_gram]
  apply Matrix.le_iff.mpr
  have ht : (1 - F.transpose).PosSemidef := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_one] using
      (Matrix.le_iff.mp hF1).transpose
  have h := ht.mul_mul_conjTranspose_same c.choiAmplitude
  simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul] using h

/-- A positive terminal-memory contraction defines a completely positive, trace-nonincreasing operation. -/
theorem terminalEffectMap_operation (c : MemoryChain I O E)
    (F : CMatrix (E (Fin.last n))) (hF : F.PosSemidef) (hF1 : F ≤ 1) :
    MatrixMap.TraceNonincreasingCP (c.terminalEffectMap F) := by
  apply (MatrixMap.traceNonincreasingCP_iff_choi _).mpr
  refine ⟨MatrixMap.ofKraus_completelyPositive _, ?_⟩
  have h := partialTraceB_mono (c.terminalEffectMap_choi_le F hF hF1)
  have ht := (MatrixMap.isTracePreserving_iff_partialTraceB_choi c.chainMap).mp
    c.chainMap_isTracePreserving
  exact h.trans ht.le


/-- Every dominated positive Choi outcome is realized on the final memory of this same chain, including singular totals. -/
theorem exists_terminalEffect_of_le (c : MemoryChain I O E)
    (R : CMatrix (Comb.Space I O)) (hR : R.PosSemidef)
    (hRS : R ≤ MatrixMap.choi c.chainMap) :
    ∃ F : CMatrix (E (Fin.last n)), F.PosSemidef ∧ F ≤ 1 ∧
      MatrixMap.choi (c.terminalEffectMap F) = R := by
  obtain ⟨G, hG, hG1, hAGR⟩ := exists_effect_of_le_gram c.choiAmplitude R hR
    (by simpa only [c.choiAmplitude_gram] using hRS)
  refine ⟨G.transpose, hG.transpose, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    simpa only [Matrix.transpose_sub, Matrix.transpose_one] using
      (Matrix.le_iff.mp hG1).transpose
  · rw [terminalEffectMap_choi _ _ hG.transpose, Matrix.transpose_transpose]
    exact hAGR

/-- The zero effect gives the zero operation. -/
theorem terminalEffectMap_zero (c : MemoryChain I O E) : c.terminalEffectMap 0 = 0 := by
  apply MatrixMap.choi_inj
  rw [c.terminalEffectMap_choi 0 Matrix.PosSemidef.zero]
  change _ = 0
  simp

/-- The identity effect recovers the original chain map. -/
theorem terminalEffectMap_one (c : MemoryChain I O E) : c.terminalEffectMap 1 = c.chainMap := by
  apply MatrixMap.choi_inj
  rw [c.terminalEffectMap_choi 1 Matrix.PosSemidef.one]
  simpa using c.choiAmplitude_gram

/-- An effect and its complement sum to the original chain map. -/
theorem terminalEffectMap_add_complement (c : MemoryChain I O E)
    (F : CMatrix (E (Fin.last n))) (hF : F.PosSemidef) (hF1 : F ≤ 1) :
    c.terminalEffectMap F + c.terminalEffectMap (1 - F) = c.chainMap := by
  apply MatrixMap.choi_inj
  change MatrixMap.choi (c.terminalEffectMap F) +
    MatrixMap.choi (c.terminalEffectMap (1 - F)) = MatrixMap.choi c.chainMap
  rw [c.terminalEffectMap_choi F hF,
    c.terminalEffectMap_choi (1 - F) (Matrix.le_iff.mp hF1),
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul]
  have h := c.choiAmplitude_gram
  rw [← h]
  abel

end MemoryChain
namespace Comb
variable {n : Nat} {I O : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- A dominated positive operator is realized by a terminal-memory effect on a realization of its specified normalized total. -/
theorem Normalized.exists_memory_effect {S R : CMatrix (Space I O)}
    (hS : Normalized I O S) (hR : R.PosSemidef) (hRS : R ≤ S) :
    ∃ (d : Fin (n + 1) → Nat) (c : MemoryChain I O (fun j => Memory.{u} (d j)))
      (F : CMatrix (Memory.{u} (d (Fin.last n)))),
      MatrixMap.choi c.chainMap = S ∧ F.PosSemidef ∧ F ≤ 1 ∧
        MatrixMap.choi (c.terminalEffectMap F) = R := by
  obtain ⟨d, c, hc, _⟩ := hS.exists_memoryChain_with_empty
  obtain ⟨F, hF, hF1, hFR⟩ := c.exists_terminalEffect_of_le R hR (by simpa only [hc] using hRS)
  exact ⟨d, c, F, hc, hF, hF1, hFR⟩

/-- Every probabilistic comb admits a single-outcome realization by an effect on a finite memory chain. -/
theorem IsProbabilistic.exists_memory_effect {R : CMatrix (Space I O)}
    (hR : IsProbabilistic I O R) :
    ∃ (d : Fin (n + 1) → Nat) (c : MemoryChain I O (fun j => Memory.{u} (d j)))
      (F : CMatrix (Memory.{u} (d (Fin.last n)))),
      F.PosSemidef ∧ F ≤ 1 ∧ MatrixMap.choi (c.terminalEffectMap F) = R := by
  obtain ⟨hpos, S, hS, hRS⟩ := hR
  obtain ⟨d, c, F, _, hF, hF1, hFR⟩ := hS.exists_memory_effect hpos hRS
  exact ⟨d, c, F, hF, hF1, hFR⟩

end Comb
end QIT.HigherOrder
