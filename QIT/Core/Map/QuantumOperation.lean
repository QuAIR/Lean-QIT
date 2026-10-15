/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Map.ChoiCharacterization
public import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# Finite quantum operations

The existing trace-nonincreasing CP interface is promoted from the diamond-norm
layer without changing its meaning. No normalization or nonempty-system
assumption is imposed. The Choi convention is input × output, so the operation
bound traces the second factor. The transpose in trace pairing is essential.

The bound is derived from the source Choi trace-preserving characterization in
[Chiribella2009Networks, comblong-pub.tex:204-209] and PSD trace duality.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
namespace QIT
namespace MatrixMap
universe u v w
noncomputable section
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A finite matrix map is trace nonincreasing on positive semidefinite inputs
when it never increases the real trace of a PSD matrix. -/
def IsTraceNonincreasing (Φ : MatrixMap a b) : Prop :=
  ∀ X : CMatrix a, X.PosSemidef → (Φ X).trace.re ≤ X.trace.re

omit [DecidableEq a] [DecidableEq b] in theorem krausAdjoint_posSemidef
    {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) {E : CMatrix b} (hE : E.PosSemidef) :
    (krausAdjoint K E).PosSemidef := by
  unfold krausAdjoint
  exact Matrix.posSemidef_sum Finset.univ fun k _ => by
    simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using hE.mul_mul_conjTranspose_same (Matrix.conjTranspose (K k))

/-- `krausAdjoint` of the unit is bounded by the unit for a trace-nonincreasing
Kraus map. -/
theorem krausAdjoint_one_le_of_traceNonincreasing
    {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ)
    (hTNI : IsTraceNonincreasing (ofKraus K)) :
    krausAdjoint K (1 : CMatrix b) ≤ 1 := by
  rw [Matrix.le_iff]
  refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg ?_).2 ?_
  · exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      (krausAdjoint_posSemidef K Matrix.PosSemidef.one).isHermitian
  · intro A hA
    have hle := hTNI A hA
    have hdual :
        (((ofKraus K) A) * (1 : CMatrix b)).trace =
          (A * krausAdjoint K (1 : CMatrix b)).trace :=
      ofKraus_trace_duality K A (1 : CMatrix b)
    rw [Matrix.mul_one] at hdual
    have htrace :
        ((A * ((1 : CMatrix a) - krausAdjoint K (1 : CMatrix b))).trace).re =
          A.trace.re - ((A * krausAdjoint K (1 : CMatrix b)).trace).re := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm]
    rw [htrace]
    rw [← hdual]
    exact sub_nonneg.mpr hle

/-- Minimal finite-dimensional trace-nonincreasing completely positive map
interface used by CKR extraction maps. -/
structure TraceNonincreasingCP (Φ : MatrixMap a b) : Prop where
  completelyPositive : IsCompletelyPositive Φ
  traceNonincreasing : IsTraceNonincreasing Φ

theorem TraceNonincreasingCP.mapsPositive {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    ∀ X : CMatrix a, X.PosSemidef → (Φ X).PosSemidef :=
  isCompletelyPositive_mapsPositive Φ hΦ.completelyPositive

noncomputable def TraceNonincreasingCP.kraus {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) : (a × b) → Matrix b a ℂ :=
  Classical.choose (exists_kraus_of_choi_psd Φ hΦ.completelyPositive)

theorem TraceNonincreasingCP.ofKraus_kraus {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    ofKraus hΦ.kraus = Φ :=
  (Classical.choose_spec (exists_kraus_of_choi_psd Φ hΦ.completelyPositive)).symm

theorem ofKraus_tracePreserving_of_krausAdjoint_one {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1) :
    IsTracePreserving (ofKraus K) := by
  intro X
  have hdual := ofKraus_trace_duality K X (1 : CMatrix b)
  rw [Matrix.mul_one] at hdual
  rw [hK, Matrix.mul_one] at hdual
  exact hdual

/-- Kraus-form matrix maps are completely positive. -/
theorem ofKraus_isCompletelyPositive {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) :
    IsCompletelyPositive (ofKraus K) := by
  rw [IsCompletelyPositive, choi_ofKraus]
  exact Matrix.posSemidef_sum Finset.univ fun k _ =>
    Matrix.posSemidef_vecMulVec_self_star _

/-- Trace-preserving CP maps are trace-nonincreasing CP maps. -/
theorem traceNonincreasingCP_of_tracePreserving {Φ : MatrixMap a b}
    (hCP : IsCompletelyPositive Φ) (hTP : IsTracePreserving Φ) :
    TraceNonincreasingCP Φ where
  completelyPositive := hCP
  traceNonincreasing := by
    intro X _hX
    rw [hTP X]

/-- Sequential composition of quantum operations is a quantum operation. -/
theorem TraceNonincreasingCP.comp {c : Type w} [Fintype c] [DecidableEq c]
    {Ψ : MatrixMap b c} {Φ : MatrixMap a b}
    (hΨ : TraceNonincreasingCP Ψ) (hΦ : TraceNonincreasingCP Φ) :
    TraceNonincreasingCP (Ψ.comp Φ) where
  completelyPositive := isCompletelyPositive_comp Ψ Φ hΨ.completelyPositive hΦ.completelyPositive
  traceNonincreasing X hX :=
    (hΨ.traceNonincreasing (Φ X) (hΦ.mapsPositive X hX)).trans (hΦ.traceNonincreasing X hX)

/-- The zero operation is allowed, including on empty finite systems. -/
theorem traceNonincreasingCP_zero : TraceNonincreasingCP (0 : MatrixMap a b) where
  completelyPositive := by
    change (choi (0 : MatrixMap a b)).PosSemidef
    have h : choi (0 : MatrixMap a b) = 0 := by ext i j; simp [choi]
    rw [h]
    exact Matrix.PosSemidef.zero
  traceNonincreasing X hX := by
    simpa using (Complex.le_def.mp hX.trace_nonneg).1

/-- Trace action in the input-first Choi convention. -/
theorem trace_map_eq_trace_mul_partialTraceB_choi_transpose
    (Φ : MatrixMap a b) (X : CMatrix a) :
    (Φ X).trace = (X * (QIT.partialTraceB (choi Φ)).transpose).trace := by
  rw [trace_map_eq_sum_single]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    partialTraceB_choi_apply]

/-- For CP maps, trace nonincrease is exactly the output-marginal bound.
This is the inequality version of the source Choi trace formula. -/
theorem isTraceNonincreasing_iff_partialTraceB_choi
    (Φ : MatrixMap a b) (hCP : IsCompletelyPositive Φ) :
    IsTraceNonincreasing Φ ↔ QIT.partialTraceB (choi Φ) ≤ 1 := by
  have hH := (QIT.partialTraceB_posSemidef hCP).transpose.isHermitian
  have htranspose : QIT.partialTraceB (choi Φ) ≤ 1 ↔
      (QIT.partialTraceB (choi Φ)).transpose ≤ 1 := by
    simp only [Matrix.le_iff]
    constructor <;> intro h
    · simpa only [Matrix.transpose_sub, Matrix.transpose_one] using h.transpose
    · simpa only [Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose] using h.transpose
  rw [htranspose, Matrix.le_iff,
    cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg
      (Matrix.isHermitian_one.sub hH)]
  constructor
  · intro h X hX
    have hx := h X hX
    rw [trace_map_eq_trace_mul_partialTraceB_choi_transpose] at hx
    rw [Matrix.trace_mul_comm]
    simpa [Matrix.mul_sub, Matrix.trace_sub] using sub_nonneg.mpr hx
  · intro h X hX
    have hx := h X hX
    rw [Matrix.trace_mul_comm] at hx
    have bound : 0 ≤ X.trace.re -
        (X * (QIT.partialTraceB (choi Φ)).transpose).trace.re := by
      simpa [Matrix.mul_sub, Matrix.trace_sub] using hx
    rw [trace_map_eq_trace_mul_partialTraceB_choi_transpose]
    exact sub_nonneg.mp bound

/-- A quantum operation is precisely a positive Choi matrix whose output
partial trace is bounded by the identity. -/
theorem traceNonincreasingCP_iff_choi (Φ : MatrixMap a b) :
    TraceNonincreasingCP Φ ↔ (choi Φ).PosSemidef ∧
      QIT.partialTraceB (choi Φ) ≤ 1 := by
  constructor
  · intro h
    exact ⟨h.completelyPositive,
      (isTraceNonincreasing_iff_partialTraceB_choi Φ h.completelyPositive).mp
        h.traceNonincreasing⟩
  · rintro ⟨hCP, hbound⟩
    exact ⟨hCP, (isTraceNonincreasing_iff_partialTraceB_choi Φ hCP).mpr hbound⟩

end
end MatrixMap
end QIT
