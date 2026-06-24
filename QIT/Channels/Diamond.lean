/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.Core.SDP.HermitianPSDTraceDuality
public import QIT.States.TraceNorm.PositivePart
public import QIT.States.TraceNorm.Variational

/-!
# Source-shaped diamond trace distance for finite channels

This module supplies the finite-dimensional channel-difference and
diamond-distance-shaped API needed by the post-selection route.  The numerical
quantity is specialized to the finite-dimensional source statement: the
reference system is a copy of the input system, matching the CKR observation
that the supremum in the diamond norm is attained at input dimension.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x

noncomputable section

namespace MatrixMap

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- Difference of two channel maps, as a linear map between matrix spaces. -/
def channelDifference (Φ Ψ : Channel a b) : MatrixMap a b :=
  Φ.map - Ψ.map

@[simp]
theorem channelDifference_apply (Φ Ψ : Channel a b) (X : CMatrix a) :
    channelDifference Φ Ψ X = Φ.map X - Ψ.map X :=
  rfl

/-- Normalized trace action of a linear matrix map on one input matrix. -/
def normalizedTraceAction (Δ : MatrixMap a b) (X : CMatrix a) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (Δ X)

/-- Finite-ancilla normalized trace action of `Δ ⊗ id_r` on a state. -/
def ancillaNormalizedTraceAction (Δ : MatrixMap a b) (ω : State (Prod a r)) : ℝ :=
  normalizedTraceAction (kron Δ (Channel.idChannel r).map) ω.matrix

/-- A finite matrix map is trace nonincreasing on positive semidefinite inputs
when it never increases the real trace of a PSD matrix. -/
def IsTraceNonincreasing (Φ : MatrixMap a b) : Prop :=
  ∀ X : CMatrix a, X.PosSemidef → (Φ X).trace.re ≤ X.trace.re

/-- Minimal finite-dimensional trace-nonincreasing completely positive map
interface used by CKR extraction maps. -/
structure TraceNonincreasingCP (Φ : MatrixMap a b) : Prop where
  completelyPositive : IsCompletelyPositive Φ
  traceNonincreasing : IsTraceNonincreasing Φ

theorem TraceNonincreasingCP.mapsPositive {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    ∀ X : CMatrix a, X.PosSemidef → (Φ X).PosSemidef :=
  isCompletelyPositive_mapsPositive Φ hΦ.completelyPositive

/-- Trace-preserving CP maps are trace-nonincreasing CP maps. -/
theorem traceNonincreasingCP_of_tracePreserving {Φ : MatrixMap a b}
    (hCP : IsCompletelyPositive Φ) (hTP : IsTracePreserving Φ) :
    TraceNonincreasingCP Φ where
  completelyPositive := hCP
  traceNonincreasing := by
    intro X _hX
    rw [hTP X]

theorem kron_comp_apply {c : Type w} {d : Type x} {e : Type u} {f : Type v}
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    (Φ₁ : MatrixMap a b) (Ψ₁ : MatrixMap c d)
    (Φ₂ : MatrixMap e a) (Ψ₂ : MatrixMap f c) (X : CMatrix (Prod e f)) :
    kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) X) =
      kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) X := by
  ext bd bd'
  rw [map_eq_sum_single (kron Φ₂ Ψ₂) X]
  simp_rw [map_sum]
  simp_rw [map_smul]
  simp only [Matrix.sum_apply]
  rw [map_eq_sum_single (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂)) X]
  simp only [Matrix.sum_apply]
  change
    (∑ ef : Prod e f, ∑ ef' : Prod e f,
      (X ef ef' • (kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) (Matrix.single ef ef' 1)))) bd bd') =
    (∑ ef : Prod e f, ∑ ef' : Prod e f,
      (X ef ef' • (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) (Matrix.single ef ef' 1))) bd bd')
  refine Finset.sum_congr rfl fun ef _ => ?_
  refine Finset.sum_congr rfl fun ef' _ => ?_
  simp only [Matrix.smul_apply]
  congr 1
  cases ef with
  | mk e0 f0 =>
  cases ef' with
  | mk e1 f1 =>
  rw [single_prod_eq_kronecker_single]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rfl

/-- Slice formula for a matrix-map tensored with an identity channel.  The
`(b,r),(b',r')` entry of `(Φ ⊗ id)(X)` is obtained by applying `Φ` to the
`r,r'` reference slice of `X`. -/
theorem kron_idChannel_apply_slice {r : Type w} [Fintype r] [DecidableEq r]
    (Φ : MatrixMap a b) (X : CMatrix (Prod a r)) (br br' : Prod b r) :
    MatrixMap.kron Φ (Channel.idChannel r).map X br br' =
      Φ (fun i i' => X (i, br.2) (i', br'.2)) br.1 br'.1 := by
  classical
  rw [map_eq_sum_single Φ (fun i i' => X (i, br.2) (i', br'.2))]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp only [MatrixMap.kron, Channel.idChannel, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one,
    Matrix.single]
  rw [Finset.sum_eq_single br.2]
  · rw [Finset.sum_eq_single br'.2]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hnot
      simp at hnot
  · intro y _ hy
    have hy' : y ≠ br.2 := hy
    simp [hy']
  · intro hnot
    simp at hnot

/-- Slice formula for an identity channel tensored with a matrix-map.  The
`(a,d),(a',d')` entry of `(id ⊗ Φ)(X)` is obtained by applying `Φ` to the
`a,a'` input slice of `X`. -/
theorem kron_idChannel_left_apply_slice {c : Type w} {d : Type x}
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (Φ : MatrixMap c d) (X : CMatrix (Prod a c)) (ad ad' : Prod a d) :
    MatrixMap.kron (Channel.idChannel a).map Φ X ad ad' =
      Φ (fun j j' => X (ad.1, j) (ad'.1, j')) ad.2 ad'.2 := by
  classical
  rw [map_eq_sum_single (MatrixMap.kron (Channel.idChannel a).map Φ) X]
  rw [map_eq_sum_single Φ (fun j j' => X (ad.1, j) (ad'.1, j'))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ ac : Prod a c, ∑ ac' : Prod a c,
      (X ac ac' •
        (MatrixMap.kron (Channel.idChannel a).map Φ
          (Matrix.single ac ac' (1 : Complex)))) ad ad') =
      ∑ ac : Prod a c, ∑ ac' : Prod a c,
        X ac ac' *
          ((if ac.1 = ad.1 ∧ ac'.1 = ad'.1 then (1 : Complex) else 0) *
            (Φ (Matrix.single ac.2 ac'.2 (1 : Complex)) ad.2 ad'.2)) := by
        refine Finset.sum_congr rfl fun ac _ => ?_
        refine Finset.sum_congr rfl fun ac' _ => ?_
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [single_prod_eq_kronecker_single]
        rw [MatrixMap.kron_apply_kronecker]
        simp [Channel.idChannel, MatrixMap.ofKraus, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.single]
    _ = ∑ j : c, ∑ j' : c,
        X (ad.1, j) (ad'.1, j') *
          (Φ (Matrix.single j j' (1 : Complex)) ad.2 ad'.2) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single ad.1]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_eq_single ad'.1]
          · simp
          · intro i' _ hi'
            apply Finset.sum_eq_zero
            intro j' _
            have hne : i' ≠ ad'.1 := hi'
            simp [hne]
          · intro hnot
            simp at hnot
        · intro i _ hi
          apply Finset.sum_eq_zero
          intro j _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_eq_zero
          intro i' _
          apply Finset.sum_eq_zero
          intro j' _
          have hne : i ≠ ad.1 := hi
          simp [hne]
        · intro hnot
          simp at hnot
    _ = ∑ j : c, ∑ j' : c,
        (X (ad.1, j) (ad'.1, j') •
          Φ (Matrix.single j j' (1 : Complex))) ad.2 ad'.2 := by
        simp [Matrix.smul_apply]

/-- A map on the right tensor factor commutes with tracing out the left factor. -/
theorem partialTraceA_kron_idChannel_left
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (Φ : MatrixMap c d) (X : CMatrix (Prod a c)) :
    partialTraceA (a := a) (b := d)
        (MatrixMap.kron (Channel.idChannel a).map Φ X) =
      Φ (partialTraceA (a := a) (b := c) X) := by
  ext j j'
  simp only [partialTraceA]
  have hpt :
      partialTraceA (a := a) (b := c) X =
        ∑ i : a, (fun x y => X (i, x) (i, y)) := by
    ext x y
    simp [partialTraceA]
  rw [hpt]
  have hmap :
      Φ (∑ i : a, (fun x y => X (i, x) (i, y))) =
        ∑ i : a, Φ (fun x y => X (i, x) (i, y)) := by
    rw [map_sum]
  have hmap_entry := congrFun (congrFun hmap j) j'
  calc
    (∑ i : a,
        MatrixMap.kron (Channel.idChannel a).map Φ X (i, j) (i, j')) =
        ∑ i : a, Φ (fun x y => X (i, x) (i, y)) j j' := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [MatrixMap.kron_idChannel_left_apply_slice]
    _ = (∑ i : a, Φ (fun x y => X (i, x) (i, y))) j j' := by
          simp only [Matrix.sum_apply]
    _ = Φ (∑ i : a, fun x y => X (i, x) (i, y)) j j' :=
          hmap_entry.symm

/-- A matrix map on the left/input factor commutes with an isometry acting on
the right/reference factor. -/
theorem kron_idChannel_apply_applyMatrixRight
    {r₁ : Type w} {r₂ : Type x}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (Φ : MatrixMap a b) (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix (Prod a r₁)) :
    MatrixMap.kron Φ (Channel.idChannel r₂).map (V.applyMatrixRight X) =
      V.applyMatrixRight (MatrixMap.kron Φ (Channel.idChannel r₁).map X) := by
  ext br br'
  rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice :
      (fun i i' => V.applyMatrixRight X (i, br.2) (i', br'.2)) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix br.2 x * star (V.matrix br'.2 y)) •
            (fun i i' => X (i, x) (i', y)) := by
    ext i i'
    simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      Matrix.mul_apply, Finset.sum_mul, mul_assoc, mul_comm]
  rw [hslice]
  have hmap :
      Φ (∑ y : r₁, ∑ x : r₁,
          (V.matrix br.2 x * star (V.matrix br'.2 y)) •
            (fun i i' => X (i, x) (i', y))) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix br.2 x * star (V.matrix br'.2 y)) •
            Φ (fun i i' => X (i, x) (i', y)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact LinearMap.map_smul Φ (V.matrix br.2 x * star (V.matrix br'.2 y))
      (fun i i' => X (i, x) (i', y))
  have hmapEntry := congrFun (congrFun hmap br.1) br'.1
  calc
    Φ (∑ y : r₁, ∑ x : r₁,
        (V.matrix br.2 x * star (V.matrix br'.2 y)) •
          (fun i i' => X (i, x) (i', y))) br.1 br'.1
        = (∑ y : r₁, ∑ x : r₁,
            (V.matrix br.2 x * star (V.matrix br'.2 y)) •
              Φ (fun i i' => X (i, x) (i', y))) br.1 br'.1 := hmapEntry
    _ = V.applyMatrixRight (MatrixMap.kron Φ (Channel.idChannel r₁).map X) br br' := by
      simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
        Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        MatrixMap.kron_idChannel_apply_slice, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

private theorem trace_kron_id_left_eq_trace_apply_partialTraceA
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (Φ : MatrixMap c d) (X : CMatrix (Prod a c)) :
    (MatrixMap.kron (Channel.idChannel a).map Φ X).trace =
      (Φ (partialTraceA (a := a) (b := c) X)).trace := by
  classical
  rw [trace_map_eq_sum_single (MatrixMap.kron (Channel.idChannel a).map Φ) X]
  rw [trace_map_eq_sum_single Φ (partialTraceA (a := a) (b := c) X)]
  calc
    (∑ ac : Prod a c, ∑ ac' : Prod a c,
        X ac ac' *
          (MatrixMap.kron (Channel.idChannel a).map Φ
            (Matrix.single ac ac' (1 : Complex))).trace) =
        ∑ ac : Prod a c, ∑ ac' : Prod a c,
          X ac ac' *
            ((if ac.1 = ac'.1 then (1 : Complex) else 0) *
              (Φ (Matrix.single ac.2 ac'.2 (1 : Complex))).trace) := by
          refine Finset.sum_congr rfl fun ac _ => ?_
          refine Finset.sum_congr rfl fun ac' _ => ?_
          rw [MatrixMap.trace_kron_single]
          rw [(Channel.idChannel a).tracePreserving]
          rw [trace_single_one]
    _ =
        ∑ j : c, ∑ j' : c,
          (partialTraceA (a := a) (b := c) X) j j' *
            (Φ (Matrix.single j j' (1 : Complex))).trace := by
          calc
            (∑ ac : Prod a c, ∑ ac' : Prod a c,
              X ac ac' *
                ((if ac.1 = ac'.1 then (1 : Complex) else 0) *
                  (Φ (Matrix.single ac.2 ac'.2 (1 : Complex))).trace)) =
              ∑ i : a, ∑ j : c, ∑ j' : c,
                X (i, j) (i, j') *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                rw [Fintype.sum_prod_type]
                refine Finset.sum_congr rfl fun i _ => ?_
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Fintype.sum_prod_type]
                rw [Finset.sum_eq_single i]
                · simp
                · intro i' _ hi'
                  apply Finset.sum_eq_zero
                  intro j' _
                  have hne : i ≠ i' := hi'.symm
                  simp [hne]
                · intro hnot
                  simp at hnot
            _ = ∑ j : c, ∑ i : a, ∑ j' : c,
                X (i, j) (i, j') *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                rw [Finset.sum_comm]
            _ = ∑ j : c, ∑ j' : c, ∑ i : a,
                X (i, j) (i, j') *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.sum_comm]
            _ = ∑ j : c, ∑ j' : c,
                (∑ i : a, X (i, j) (i, j')) *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                refine Finset.sum_congr rfl fun j _ => ?_
                refine Finset.sum_congr rfl fun j' _ => ?_
                rw [Finset.sum_mul]
            _ = ∑ j : c, ∑ j' : c,
                (partialTraceA (a := a) (b := c) X) j j' *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                simp [partialTraceA]

/-- Tensoring a trace-nonincreasing CP map on the right with an identity map on
the left is trace-nonincreasing CP. -/
theorem traceNonincreasingCP_id_kron
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    {Φ : MatrixMap c d} (hΦ : TraceNonincreasingCP Φ) :
    TraceNonincreasingCP (MatrixMap.kron (Channel.idChannel a).map Φ) where
  completelyPositive :=
    MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map Φ
      (Channel.idChannel a).completelyPositive hΦ.completelyPositive
  traceNonincreasing := by
    intro X hX
    rw [trace_kron_id_left_eq_trace_apply_partialTraceA]
    have hpt : (partialTraceA (a := a) (b := c) X).PosSemidef :=
      partialTraceA_posSemidef hX
    have hle := hΦ.traceNonincreasing (partialTraceA (a := a) (b := c) X) hpt
    have htrace := partialTraceA_trace (a := a) (b := c) X
    linarith [congrArg Complex.re htrace]

private theorem traceNorm_sub_le_trace_add_of_posSemidef
    (A B : CMatrix a) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm (A - B) ≤ A.trace.re + B.trace.re := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (A - B)
  have hA_le : Complex.abs ((A * (U : CMatrix a)).trace) ≤ A.trace.re :=
    posSemidef_trace_mul_unitary_abs_le_trace_re A hA U
  have hB_le : Complex.abs ((B * (U : CMatrix a)).trace) ≤ B.trace.re :=
    posSemidef_trace_mul_unitary_abs_le_trace_re B hB U
  have htri :
      Complex.abs (((A - B) * (U : CMatrix a)).trace) ≤
        Complex.abs ((A * (U : CMatrix a)).trace) +
          Complex.abs ((B * (U : CMatrix a)).trace) := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
    simpa [Complex.abs] using norm_sub_le ((A * (U : CMatrix a)).trace)
      ((B * (U : CMatrix a)).trace)
  calc
    traceNorm (A - B) = Complex.abs (((A - B) * (U : CMatrix a)).trace) := hU.symm
    _ ≤ Complex.abs ((A * (U : CMatrix a)).trace) +
          Complex.abs ((B * (U : CMatrix a)).trace) := htri
    _ ≤ A.trace.re + B.trace.re := add_le_add hA_le hB_le

private theorem negPart_trace_eq_posPart_trace_of_trace_zero (H : CMatrix a)
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    (H⁻).trace.re = (H⁺).trace.re := by
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have htrace : (H⁺).trace - (H⁻).trace = 0 := by
    rw [← Matrix.trace_sub, hdecomp, htr]
  have hre := congrArg Complex.re htrace
  simp at hre
  linarith

/-- Trace-nonincreasing CP maps contract the trace norm of Hermitian trace-zero
inputs.  This is the finite-dimensional CKR extraction-map norm contraction
used by the post-selection route. -/
theorem traceNorm_apply_le_of_traceNonincreasingCP {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) {H : CMatrix a}
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    traceNorm (Φ H) ≤ traceNorm H := by
  classical
  have hpos : H⁺.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)
  have hneg : H⁻.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hmap_pos : (Φ H⁺).PosSemidef := hΦ.mapsPositive H⁺ hpos
  have hmap_neg : (Φ H⁻).PosSemidef := hΦ.mapsPositive H⁻ hneg
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have hmap :
      Φ H = Φ H⁺ - Φ H⁻ := by
    calc
      Φ H = Φ (H⁺ - H⁻) := by rw [hdecomp]
      _ = Φ H⁺ - Φ H⁻ := by rw [map_sub]
  have htrace_le :
      (Φ H⁺).trace.re + (Φ H⁻).trace.re ≤
        (H⁺).trace.re + (H⁻).trace.re :=
    add_le_add (hΦ.traceNonincreasing H⁺ hpos)
      (hΦ.traceNonincreasing H⁻ hneg)
  have hneg_trace := negPart_trace_eq_posPart_trace_of_trace_zero H hH htr
  have hnormH := traceNorm_eq_two_posPart_trace_re_of_trace_zero H hH htr
  calc
    traceNorm (Φ H) = traceNorm (Φ H⁺ - Φ H⁻) := by rw [hmap]
    _ ≤ (Φ H⁺).trace.re + (Φ H⁻).trace.re :=
      traceNorm_sub_le_trace_add_of_posSemidef (Φ H⁺) (Φ H⁻) hmap_pos hmap_neg
    _ ≤ (H⁺).trace.re + (H⁻).trace.re := htrace_le
    _ = 2 * (H⁺).trace.re := by rw [hneg_trace]; ring
    _ = traceNorm H := hnormH.symm

/-- Normalized trace-action wrapper for trace-nonincreasing CP maps on
Hermitian trace-zero inputs. -/
theorem normalizedTraceAction_apply_le_of_traceNonincreasingCP {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) {H : CMatrix a}
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    normalizedTraceAction Φ H ≤ (1 / 2 : ℝ) * traceNorm H := by
  unfold normalizedTraceAction
  exact mul_le_mul_of_nonneg_left
    (traceNorm_apply_le_of_traceNonincreasingCP hΦ hH htr) (by norm_num)

section BlockCompression

variable {ι : Type x} {β : Type w} [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

/-- Compress a matrix on a classical-labelled system to the diagonal block
with label `i`.

This is the finite matrix-map version of applying the projection
`|i⟩⟨i| ⊗ I` and discarding the classical label. -/
def blockCompression (i : ι) : MatrixMap (Prod ι β) β where
  toFun X := fun x y => X (i, x) (i, y)
  map_add' X Y := by ext x y; rfl
  map_smul' c X := by ext x y; rfl

@[simp]
theorem blockCompression_apply (i : ι) (X : CMatrix (Prod ι β)) :
    blockCompression (β := β) i X = fun x y => X (i, x) (i, y) := rfl

private theorem choi_blockCompression (i : ι) :
    MatrixMap.choi (blockCompression (β := β) i) =
      Matrix.vecMulVec
        (fun x : Prod (Prod ι β) β =>
          if x.1.1 = i ∧ x.1.2 = x.2 then (1 : ℂ) else 0)
        (fun x : Prod (Prod ι β) β =>
          star (if x.1.1 = i ∧ x.1.2 = x.2 then (1 : ℂ) else 0)) := by
  ext x y
  rcases x with ⟨⟨xi, xb⟩, xo⟩
  rcases y with ⟨⟨yi, yb⟩, yo⟩
  simp [MatrixMap.choi, blockCompression, Matrix.single, Matrix.vecMulVec]
  by_cases hxi : xi = i <;> by_cases hxb : xb = xo <;>
    by_cases hyi : yi = i <;> by_cases hyb : yb = yo <;>
      simp [hxi, hxb, hyi, hyb]

theorem blockCompression_completelyPositive (i : ι) :
    IsCompletelyPositive (blockCompression (β := β) i) := by
  rw [MatrixMap.IsCompletelyPositive, choi_blockCompression]
  exact Matrix.posSemidef_vecMulVec_self_star _

private theorem blockCompression_trace_re_le (i : ι) {X : CMatrix (Prod ι β)}
    (hX : X.PosSemidef) :
    ((blockCompression (β := β) i X).trace).re ≤ X.trace.re := by
  simp only [blockCompression_apply, Matrix.trace]
  calc
    (∑ x : β, X (i, x) (i, x)).re = ∑ x : β, (X (i, x) (i, x)).re := by
      simp
    _ ≤ ∑ z : Prod ι β, (X z z).re := by
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum (s := (Finset.univ : Finset ι))
        (f := fun j : ι => ∑ y : β, (X (j, y) (j, y)).re)
        (fun j _ => by
          exact Finset.sum_nonneg fun y _ =>
            (Complex.nonneg_iff.mp (hX.diag_nonneg (i := (j, y)))).1)
        (Finset.mem_univ i)
    _ = (∑ z : Prod ι β, X z z).re := by simp

/-- Classical diagonal-block compression is trace-nonincreasing completely
positive. -/
theorem blockCompression_traceNonincreasingCP (i : ι) :
    TraceNonincreasingCP (blockCompression (β := β) i) where
  completelyPositive := blockCompression_completelyPositive (β := β) i
  traceNonincreasing := by
    intro X hX
    exact blockCompression_trace_re_le (β := β) i hX

end BlockCompression

/-- Kronecker product of matrix maps is linear in the left map. -/
theorem kron_sub_left (Φ Ψ : MatrixMap a b) (Γ : MatrixMap r r) :
    kron (Φ - Ψ) Γ = kron Φ Γ - kron Ψ Γ := by
  apply LinearMap.ext
  intro X
  ext br br'
  simp [kron, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem channelDifference_kron_id_apply_eq_output_sub
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix =
      ((Φ.prod (Channel.idChannel r)).applyState ω).matrix -
        ((Ψ.prod (Channel.idChannel r)).applyState ω).matrix := by
  change MatrixMap.kron (Φ.map - Ψ.map) (Channel.idChannel r).map ω.matrix =
      MatrixMap.kron Φ.map (Channel.idChannel r).map ω.matrix -
        MatrixMap.kron Ψ.map (Channel.idChannel r).map ω.matrix
  rw [MatrixMap.kron_sub_left]
  rfl

theorem channelDifference_kron_id_apply_isHermitian
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
      (Channel.idChannel r).map ω.matrix).IsHermitian := by
  rw [channelDifference_kron_id_apply_eq_output_sub]
  exact ((Φ.prod (Channel.idChannel r)).applyState ω).pos.isHermitian.sub
    ((Ψ.prod (Channel.idChannel r)).applyState ω).pos.isHermitian

theorem channelDifference_kron_id_apply_trace_eq_zero
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
      (Channel.idChannel r).map ω.matrix).trace = 0 := by
  rw [channelDifference_kron_id_apply_eq_output_sub]
  rw [Matrix.trace_sub]
  rw [((Φ.prod (Channel.idChannel r)).applyState ω).trace_eq_one]
  rw [((Ψ.prod (Channel.idChannel r)).applyState ω).trace_eq_one]
  simp

/-- Rewriting helper for pure-state CKR reductions: applying a right-reference
isometry before a channel difference is the same as applying it after the
channel difference. -/
theorem channelDifference_kron_id_apply_applyPureVectorRight
    {r₁ : Type w} {r₂ : Type x}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (Φ Ψ : Channel a b) (V : ReferenceIsometry r₁ r₂)
    (Ω : PureVector (Prod a r₁)) :
    MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r₂).map
        (V.applyPureVectorRight Ω).state.matrix =
      V.applyMatrixRight
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r₁).map
          Ω.state.matrix) := by
  rw [ReferenceIsometry.rankOne_applyPureVectorRight]
  rw [MatrixMap.kron_idChannel_apply_applyMatrixRight]

section ReferenceIsometryChannel

variable {r₁ : Type w} {r₂ : Type x}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- The channel induced by an isometry on a finite reference system. -/
def ofReferenceIsometry (V : ReferenceIsometry r₁ r₂) : MatrixMap r₁ r₂ :=
  MatrixMap.ofKraus (fun _ : Unit => V.matrix)

@[simp]
theorem ofReferenceIsometry_apply (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix r₁) :
    ofReferenceIsometry V X =
      V.matrix * X * Matrix.conjTranspose V.matrix := by
  simp [ofReferenceIsometry, MatrixMap.ofKraus]

theorem ofReferenceIsometry_isCompletelyPositive
    (V : ReferenceIsometry r₁ r₂) :
    IsCompletelyPositive (ofReferenceIsometry V) := by
  rw [ofReferenceIsometry, IsCompletelyPositive, choi_ofKraus]
  exact Matrix.posSemidef_sum Finset.univ (fun _ _ =>
    Matrix.posSemidef_vecMulVec_self_star
      (fun x : Prod r₁ r₂ => V.matrix x.2 x.1))

theorem ofReferenceIsometry_isTracePreserving
    (V : ReferenceIsometry r₁ r₂) :
    IsTracePreserving (ofReferenceIsometry V) := by
  intro X
  rw [ofReferenceIsometry_apply]
  exact V.trace_apply_block X

theorem ofReferenceIsometry_traceNonincreasingCP
    (V : ReferenceIsometry r₁ r₂) :
    TraceNonincreasingCP (ofReferenceIsometry V) :=
  traceNonincreasingCP_of_tracePreserving
    (ofReferenceIsometry_isCompletelyPositive V)
    (ofReferenceIsometry_isTracePreserving V)

theorem kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod a r₁)) :
    MatrixMap.kron (Channel.idChannel a).map (ofReferenceIsometry V) X =
      V.applyMatrixRight X := by
  ext x y
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  change ofReferenceIsometry V (ReferenceIsometry.rightBlock X x.1 y.1) x.2 y.2 =
    (V.matrix * ReferenceIsometry.rightBlock X x.1 y.1 *
      Matrix.conjTranspose V.matrix) x.2 y.2
  rw [ofReferenceIsometry_apply]

/-- A right-reference isometry does not increase the trace norm of Hermitian
trace-zero matrices.  This rectangular version is routed through the
trace-nonincreasing CP contraction for the isometry channel. -/
theorem traceNorm_applyMatrixRight_le_of_isHermitian_trace_zero
    (V : ReferenceIsometry r₁ r₂) {X : CMatrix (Prod a r₁)}
    (hX : X.IsHermitian) (htr : X.trace = 0) :
    traceNorm (V.applyMatrixRight X) ≤ traceNorm X := by
  rw [← kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight (a := a) V X]
  exact traceNorm_apply_le_of_traceNonincreasingCP
    (traceNonincreasingCP_id_kron
      (a := a) (hΦ := ofReferenceIsometry_traceNonincreasingCP V))
    hX htr

end ReferenceIsometryChannel

variable {κ : Type x} [Fintype κ]

private def krausAdjoint (K : κ → Matrix b a ℂ) (E : CMatrix b) : CMatrix a :=
  ∑ k : κ, Matrix.conjTranspose (K k) * E * K k

private theorem ofKraus_trace_duality
    (K : κ → Matrix b a ℂ) (X : CMatrix a) (E : CMatrix b) :
    (((ofKraus K) X) * E).trace = (X * krausAdjoint K E).trace := by
  simp [ofKraus, krausAdjoint, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  let Kk : Matrix b a ℂ := K k
  let KkH : Matrix a b ℂ := Matrix.conjTranspose Kk
  calc
    ((K k * X * Matrix.conjTranspose (K k)) * E).trace =
        ((Kk * X * KkH) * E).trace := by rfl
    _ = (E * (Kk * X * KkH)).trace := by rw [Matrix.trace_mul_comm]
    _ = ((E * Kk) * (X * KkH)).trace := by
          simp only [Matrix.mul_assoc]
    _ = ((X * KkH) * (E * Kk)).trace := by rw [Matrix.trace_mul_comm]
    _ = (X * (KkH * E * Kk)).trace := by
          simp only [Matrix.mul_assoc]
    _ = (X * (Matrix.conjTranspose (K k) * E * K k)).trace := by rfl

omit [DecidableEq a] [DecidableEq b] in
private theorem krausAdjoint_posSemidef
    (K : κ → Matrix b a ℂ) (E : CMatrix b) (hE : E.PosSemidef) :
    (krausAdjoint K E).PosSemidef := by
  unfold krausAdjoint
  exact Matrix.posSemidef_sum Finset.univ fun k _ => by
    simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using hE.mul_mul_conjTranspose_same (Matrix.conjTranspose (K k))

private theorem krausAdjoint_one_of_tracePreserving
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K)) :
    krausAdjoint K (1 : CMatrix b) = 1 := by
  apply Matrix.ext
  intro i j
  let X : CMatrix a := Matrix.single j i (1 : ℂ)
  have htrace := hTP X
  have hdual :
      (((ofKraus K) X) * (1 : CMatrix b)).trace =
        (X * krausAdjoint K (1 : CMatrix b)).trace :=
    ofKraus_trace_duality K X (1 : CMatrix b)
  rw [Matrix.mul_one] at hdual
  rw [hdual] at htrace
  have hsingle_trace :
      (X * krausAdjoint K (1 : CMatrix b)).trace =
        (krausAdjoint K (1 : CMatrix b)) i j := by
    simp [X, Matrix.trace_single_mul]
  have hXtrace : X.trace = if j = i then (1 : ℂ) else 0 := by
    by_cases hji : j = i
    · subst hji
      simp [X, Matrix.trace, Matrix.single]
    · have hij : i ≠ j := by
        intro hij
        exact hji hij.symm
      simp [X, Matrix.trace, Matrix.single, hji, hij]
  have hOne : (1 : CMatrix a) i j = if j = i then (1 : ℂ) else 0 := by
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : i ≠ j := by
        intro hij
        exact hji hij.symm
      simp [hji, hij]
  calc
    krausAdjoint K (1 : CMatrix b) i j =
        (X * krausAdjoint K (1 : CMatrix b)).trace := hsingle_trace.symm
    _ = X.trace := htrace
    _ = (1 : CMatrix a) i j := by rw [hXtrace, hOne]

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
private theorem krausAdjoint_sub (K : κ → Matrix b a ℂ) (E F : CMatrix b) :
    krausAdjoint K (E - F) = krausAdjoint K E - krausAdjoint K F := by
  ext i j
  simp [krausAdjoint, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

private theorem krausAdjoint_effect
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K))
    {E : CMatrix b} (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    (krausAdjoint K E).PosSemidef ∧ krausAdjoint K E ≤ 1 := by
  refine ⟨krausAdjoint_posSemidef K E hEpos, ?_⟩
  rw [Matrix.le_iff]
  have hcomp : (1 - E).PosSemidef := by
    rwa [← Matrix.le_iff]
  have hcompAdj : (krausAdjoint K (1 - E)).PosSemidef :=
    krausAdjoint_posSemidef K (1 - E) hcomp
  have hone := krausAdjoint_one_of_tracePreserving K hTP
  have hsub := krausAdjoint_sub K (1 : CMatrix b) E
  rw [hone] at hsub
  rwa [← hsub]

/-- Scalar-output effect functional `X ↦ Tr(XE)`.

The Kraus form uses `sqrt(E)` so complete positivity is immediate when `E` is
positive semidefinite.  This is the finite matrix-map form of the extraction
functional used in CKR `extractpart` [ChristandlKoenigRenner2008Postselection,
christandl-koenig-renner-2008-postselection.tex:319-357]. -/
def traceEffectToUnit (E : CMatrix a) : MatrixMap a PUnit :=
  MatrixMap.ofKraus (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)

private theorem traceEffectToUnit_krausAdjoint_one_of_posSemidef
    {E : CMatrix a} (hE : E.PosSemidef) :
    krausAdjoint (a := a) (b := PUnit)
      (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)
      (1 : CMatrix PUnit) = E := by
  let K : a → Matrix PUnit a ℂ := fun k => fun (_ : PUnit) (i : a) =>
    (psdSqrt E) k i
  let S : CMatrix a := psdSqrt E
  have hSsq : S * S = E := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef hE
  have hS : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian E
  ext i j
  calc
    krausAdjoint K (1 : CMatrix PUnit) i j =
        ∑ k : a, star (S k i) * S k j := by
          simp [krausAdjoint, K, S, Matrix.sum_apply, Matrix.mul_apply]
    _ = ∑ k : a, S i k * S k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hstar : star (S k i) = S i k := by
            simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS i) k
          simp [hstar]
    _ = (S * S) i j := by simp [Matrix.mul_apply]
    _ = E i j := by rw [hSsq]

theorem traceEffectToUnit_apply_of_posSemidef {E X : CMatrix a}
    (hE : E.PosSemidef) :
    traceEffectToUnit E X = fun _ _ : PUnit => (X * E).trace := by
  ext u v
  cases u
  cases v
  have hdual := ofKraus_trace_duality
    (a := a) (b := PUnit)
    (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i) X
    (1 : CMatrix PUnit)
  have hAdj := traceEffectToUnit_krausAdjoint_one_of_posSemidef (a := a) hE
  rw [traceEffectToUnit]
  have hleft :
      (((MatrixMap.ofKraus
          (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)) X) *
          (1 : CMatrix PUnit)).trace =
        ((MatrixMap.ofKraus
          (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)) X).trace := by
    rw [Matrix.mul_one]
  rw [hleft] at hdual
  rw [hAdj] at hdual
  simpa [Matrix.trace] using hdual

/-- Effect functionals are trace-nonincreasing CP when `0 ≤ E ≤ 1`. -/
theorem traceEffectToUnit_traceNonincreasingCP {E : CMatrix a}
    (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    TraceNonincreasingCP (traceEffectToUnit E) where
  completelyPositive := by
    rw [traceEffectToUnit, IsCompletelyPositive, choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.posSemidef_vecMulVec_self_star _
  traceNonincreasing := by
    intro X hX
    rw [traceEffectToUnit_apply_of_posSemidef hEpos]
    have hcomp : (1 - E).PosSemidef := by
      rwa [← Matrix.le_iff]
    have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcomp
    have hcalc :
        ((X * (1 - E)).trace).re = X.trace.re - ((X * E).trace).re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one]
      simp
    have hle : ((X * E).trace).re ≤ X.trace.re := by
      linarith
    simpa [Matrix.trace] using hle

end MatrixMap

namespace Channel

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- The map underlying a CPTP channel is trace-nonincreasing CP. -/
theorem traceNonincreasingCP_map (Φ : Channel a b) :
    MatrixMap.TraceNonincreasingCP Φ.map :=
  MatrixMap.traceNonincreasingCP_of_tracePreserving Φ.completelyPositive Φ.tracePreserving

theorem traceNonincreasingCP_kron_id (K : Channel b b) :
    MatrixMap.TraceNonincreasingCP (MatrixMap.kron K.map (Channel.idChannel r).map) := by
  simpa [Channel.prod] using traceNonincreasingCP_map (K.prod (Channel.idChannel r))

/-- CPTP channels contract normalized trace distance between finite states.

The proof uses only the trace-norm positive-part variational characterization:
pull back the output positive spectral projector along a Kraus representation
of the channel, observe that the pullback is again an effect, and compare with
the input positive part. -/
theorem normalizedTraceDistance_applyState_le
    (Φ : Channel a b) (ρ σ : State a) :
    (Φ.applyState ρ).normalizedTraceDistance (Φ.applyState σ) ≤
      ρ.normalizedTraceDistance σ := by
  classical
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  let HIn : CMatrix a := ρ.matrix - σ.matrix
  let HOut : CMatrix b := (Φ.applyState ρ).matrix - (Φ.applyState σ).matrix
  let hHIn : HIn.IsHermitian := ρ.pos.isHermitian.sub σ.pos.isHermitian
  let hHOut : HOut.IsHermitian :=
    (Φ.applyState ρ).pos.isHermitian.sub (Φ.applyState σ).pos.isHermitian
  let P : CMatrix b := positiveSpectralProjector HOut hHOut
  have hPpos : P.PosSemidef := positiveSpectralProjector_posSemidef HOut hHOut
  have hPle : P ≤ 1 := positiveSpectralProjector_le_one HOut hHOut
  have hTPK : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  let E : CMatrix a := MatrixMap.krausAdjoint K P
  have hEeffect : E.PosSemidef ∧ E ≤ 1 := by
    simpa [E] using MatrixMap.krausAdjoint_effect K hTPK hPpos hPle
  have hHOut_eq : HOut = MatrixMap.ofKraus K HIn := by
    simp [HOut, HIn, Channel.applyState, hK, map_sub]
  have hscore_out :
      ((HOut * P).trace).re = (HOut⁺).trace.re := by
    simpa [P] using positiveSpectralProjector_score_eq_posPart_trace HOut hHOut
  have hdual :
      ((HOut * P).trace).re = ((HIn * E).trace).re := by
    rw [hHOut_eq]
    simpa [E] using congrArg Complex.re (MatrixMap.ofKraus_trace_duality K HIn P)
  have hinput_bound :
      ((HIn * E).trace).re ≤ (HIn⁺).trace.re :=
    hermitian_trace_mul_effect_le_posPart_trace HIn E hHIn hEeffect.1 hEeffect.2
  rw [State.normalizedTraceDistance_eq_posPart_trace,
    State.normalizedTraceDistance_eq_posPart_trace]
  calc
    (HOut⁺).trace.re = ((HOut * P).trace).re := hscore_out.symm
    _ = ((HIn * E).trace).re := hdual
    _ ≤ (HIn⁺).trace.re := hinput_bound

/-- Finite-reference trace-distance bound for a pair of channels. -/
def AncillaTraceDistanceBound (Φ Ψ : Channel a b) (ε : ℝ) : Prop :=
  ∀ ω : State (Prod a r),
    ((Φ.prod (idChannel r)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (idChannel r)).applyState ω) ≤ ε

/-- The finite-reference trace distance is the normalized trace action of the
channel-difference map tensored with the reference identity. -/
theorem ancillaChannelTraceDistance_eq_channelDifferenceAction
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    ((Φ.prod (idChannel r)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (idChannel r)).applyState ω) =
        MatrixMap.ancillaNormalizedTraceAction
          (MatrixMap.channelDifference Φ Ψ) ω := by
  change
    (1 / 2 : ℝ) *
        traceNorm (((Φ.prod (idChannel r)).map ω.matrix) -
          ((Ψ.prod (idChannel r)).map ω.matrix)) =
      (1 / 2 : ℝ) *
        traceNorm ((MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
          (idChannel r).map) ω.matrix)
  congr 1
  change
    traceNorm (((MatrixMap.kron Φ.map (idChannel r).map) ω.matrix) -
        ((MatrixMap.kron Ψ.map (idChannel r).map) ω.matrix)) =
      traceNorm ((MatrixMap.kron (Φ.map - Ψ.map) (idChannel r).map) ω.matrix)
  rw [MatrixMap.kron_sub_left]
  rfl

/-- Source-shaped finite-dimensional diamond trace distance between channels.

The CKR post-selection source defines the diamond norm using an ancilla identity
and notes that, in finite dimension, the reference dimension may be chosen equal
to the input dimension.  This API records exactly that source-shaped numeric
quantity rather than a general Banach-space `cb` norm. -/
def diamondTraceDistance [Nonempty a] (Φ Ψ : Channel a b) : ℝ :=
  sSup (Set.range fun ω : State (Prod a a) =>
    ((Φ.prod (idChannel a)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (idChannel a)).applyState ω))

private def basisState (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] : State α where
  matrix := Matrix.single (Classical.choice (inferInstance : Nonempty α))
    (Classical.choice (inferInstance : Nonempty α)) 1
  pos := posSemidef_single (Classical.choice (inferInstance : Nonempty α))
  trace_eq_one := by
    simp [Matrix.trace, Matrix.single]

private theorem state_prod_self_nonempty [Nonempty a] :
    Nonempty (State (Prod a a)) :=
  ⟨basisState (Prod a a)⟩

/-- A pointwise bound on the input-reference trace distance bounds the
source-shaped diamond trace distance. -/
theorem diamondTraceDistance_le_of_inputReferenceBound [Nonempty a]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : ∀ ω : State (Prod a a),
      ((Φ.prod (idChannel a)).applyState ω).normalizedTraceDistance
        ((Ψ.prod (idChannel a)).applyState ω) ≤ ε) :
    diamondTraceDistance Φ Ψ ≤ ε := by
  unfold diamondTraceDistance
  haveI : Nonempty (State (Prod a a)) := state_prod_self_nonempty (a := a)
  exact csSup_le (Set.range_nonempty _) fun y hy => by
    rcases hy with ⟨ω, rfl⟩
    exact h ω

/-- A finite-ancilla bound for the input reference copy bounds the source-shaped
diamond trace distance. -/
theorem diamondTraceDistance_le_of_ancillaBound [Nonempty a]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : AncillaTraceDistanceBound (a := a) (b := b) (r := a) Φ Ψ ε) :
    diamondTraceDistance Φ Ψ ≤ ε :=
  diamondTraceDistance_le_of_inputReferenceBound h

end Channel

end

end QIT
