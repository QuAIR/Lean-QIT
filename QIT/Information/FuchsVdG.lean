/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Fidelity
public import QIT.States.TraceNorm.Distance
public import QIT.States.Purification.Uhlmann
import QIT.States.TraceNorm.Spectral
import QIT.HypothesisTesting.Audenaert
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Fuchs--van de Graaf inequality

## Lower bound `1 - F(ρ,σ) ≤ (1/2)·‖ρ-σ‖₁`

We use the already-formalized Audenaert trace inequality at `s = 1/2`:
`Re Tr(√ρ√σ) ≥ 1 - (1/2)‖ρ-σ‖₁`, then bound
`Re Tr(√ρ√σ) ≤ ‖√ρ√σ‖₁ = F(ρ,σ)` by the trace-norm variational theorem.

## Upper bound `(1/2)·‖ρ-σ‖₁ ≤ √(1 - F²)`

Requires Uhlmann's fidelity-maximisation (`QIT.States.Purification.Uhlmann`, proved),
trace-distance contraction under partial trace, and the pure-state formula
`‖|ψ⟩⟨ψ|-|φ⟩⟨φ|‖₁ = 2·√(1 - |⟨ψ|φ⟩|²)`.  Registered as
`m7-s0b-fuchs-vdG-upper`.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

open scoped ComplexOrder MatrixOrder

variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem traceNorm_eq_singularValues_support_sum (M : CMatrix a) :
    traceNorm M = M.toEuclideanLin.singularValues.sum (fun _ x => x) := by
  rw [traceNorm_eq_singularValueSum, traceNormSingularValueSum_eq_linearMap_singularValues]
  let sv := M.toEuclideanLin.singularValues
  change (∑ i ∈ Finset.range (Fintype.card a), sv i) = sv.sum (fun _ x => x)
  rw [Finsupp.sum]
  have hsupport : sv.support =
      Finset.range (Module.finrank ℂ (LinearMap.range M.toEuclideanLin)) := by
    simp [sv]
  rw [hsupport]
  let r := Module.finrank ℂ (LinearMap.range M.toEuclideanLin)
  let n := Fintype.card a
  have hrn : r ≤ n := by
    simpa [r, n, finrank_euclideanSpace] using
      (Submodule.finrank_le (LinearMap.range M.toEuclideanLin))
  exact (Finset.sum_subset
    (by intro i hi; exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hrn))
    (by
      intro i _ hi_small
      have hri : r ≤ i := le_of_not_gt (by simpa [r] using hi_small)
      change M.toEuclideanLin.singularValues i = 0
      exact (M.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).2 hri)).symm

private theorem singularValues_sum_sq_eq_trace_conjTranspose_mul_self (M : CMatrix a) :
    (∑ i ∈ Finset.range (Fintype.card a), M.toEuclideanLin.singularValues i ^ 2) =
      ((star M * M).trace).re := by
  let H : CMatrix a := star M * M
  have htrace : H.trace.re = ∑ i, (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i := by
    have h := (Matrix.isHermitian_conjTranspose_mul_self M).trace_eq_sum_eigenvalues
    exact (congrArg Complex.re h).trans (by simp)
  rw [htrace]
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  intro i
  rw [LinearMap.sq_singularValues_fin]
  exact eigenvalues_conjTranspose_mul_self_eq_adjoint_comp M i

private theorem singularValues_support_sum_sq_eq_trace_conjTranspose_mul_self (M : CMatrix a) :
    M.toEuclideanLin.singularValues.sum (fun _ x => x ^ 2) =
      ((star M * M).trace).re := by
  rw [← singularValues_sum_sq_eq_trace_conjTranspose_mul_self M]
  let sv := M.toEuclideanLin.singularValues
  change sv.sum (fun _ x => x ^ 2) = ∑ i ∈ Finset.range (Fintype.card a), sv i ^ 2
  rw [Finsupp.sum]
  have hsupport : sv.support =
      Finset.range (Module.finrank ℂ (LinearMap.range M.toEuclideanLin)) := by
    simp [sv]
  rw [hsupport]
  let r := Module.finrank ℂ (LinearMap.range M.toEuclideanLin)
  let n := Fintype.card a
  have hrn : r ≤ n := by
    simpa [r, n, finrank_euclideanSpace] using
      (Submodule.finrank_le (LinearMap.range M.toEuclideanLin))
  exact Finset.sum_subset
    (by intro i hi; exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hrn))
    (by
      intro i _ hi_small
      have hri : r ≤ i := le_of_not_gt (by simpa [r] using hi_small)
      have hz : sv i = 0 := by
        change M.toEuclideanLin.singularValues i = 0
        exact (M.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).2 hri
      rw [hz]
      norm_num)

private theorem traceNorm_sq_le_finrank_range_mul_hilbertSchmidt (M : CMatrix a) :
    traceNorm M ^ 2 ≤
      (Module.finrank ℂ (LinearMap.range M.toEuclideanLin) : ℝ) * ((star M * M).trace).re := by
  let sv := M.toEuclideanLin.singularValues
  have htraceNorm : traceNorm M = sv.sum (fun _ x => x) := by
    simpa [sv] using traceNorm_eq_singularValues_support_sum M
  have hsqsum : sv.sum (fun _ x => x ^ 2) = ((star M * M).trace).re := by
    simpa [sv] using singularValues_support_sum_sq_eq_trace_conjTranspose_mul_self M
  rw [htraceNorm, ← hsqsum]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := sv.support)
    (R := ℝ)
    (r := fun i : ℕ => sv i)
    (f := fun _ : ℕ => (1 : ℝ))
    (g := fun i : ℕ => sv i ^ 2)
    (fun _ _ => by norm_num)
    (fun i _ => sq_nonneg (sv i))
    (fun i _ => by simp)
  have hcard : (sv.support.card : ℝ) =
      Module.finrank ℂ (LinearMap.range M.toEuclideanLin) := by
    have h := M.toEuclideanLin.card_support_singularValues
    exact_mod_cast h
  simpa [Finsupp.sum, hcard] using hcs

private theorem partialTraceA_mul_kronecker_one
    {b : Type v} [Fintype b] (X : CMatrix (Prod a b)) (U : CMatrix b) :
    partialTraceA (a := a) (b := b) (X * Matrix.kronecker (1 : CMatrix a) U) =
      partialTraceA (a := a) (b := b) X * U := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq a] in
private theorem partialTraceA_sub
    {b : Type v} [Fintype b] (X Y : CMatrix (Prod a b)) :
    partialTraceA (a := a) (b := b) (X - Y) =
      partialTraceA (a := a) (b := b) X - partialTraceA (a := a) (b := b) Y := by
  ext j j'
  simp [partialTraceA, Finset.sum_sub_distrib]

private theorem partialTraceA_mul_trace_eq_trace_mul_kronecker_one
    {b : Type v} [Fintype b] (X : CMatrix (Prod a b)) (U : CMatrix b) :
    ((partialTraceA (a := a) (b := b) X) * U).trace =
      (X * Matrix.kronecker (1 : CMatrix a) U).trace := by
  rw [← partialTraceA_mul_kronecker_one X U]
  exact partialTraceA_trace (a := a) (b := b)
    (X * Matrix.kronecker (1 : CMatrix a) U)

private theorem kronecker_one_mem_unitaryGroup
    {b : Type v} [Fintype b] [DecidableEq b] (U : Matrix.unitaryGroup b ℂ) :
    Matrix.kronecker (1 : CMatrix a) (U : CMatrix b) ∈
      Matrix.unitaryGroup (Prod a b) ℂ := by
  let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
  simpa using Matrix.kronecker_mem_unitary I.2 U.2

/-- Trace norm is contractive under tracing out the first subsystem. -/
theorem traceNorm_partialTraceA_le
    {b : Type v} [Fintype b] [DecidableEq b] (X : CMatrix (Prod a b)) :
    traceNorm (partialTraceA (a := a) (b := b) X) ≤ traceNorm X := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace
    (partialTraceA (a := a) (b := b) X)
  let Ubig : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (1 : CMatrix a) (U : CMatrix b), kronecker_one_mem_unitaryGroup U⟩
  calc
    traceNorm (partialTraceA (a := a) (b := b) X)
        = Complex.abs (((partialTraceA (a := a) (b := b) X) * (U : CMatrix b)).trace) :=
          hU.symm
    _ = Complex.abs ((X * (Ubig : CMatrix (Prod a b))).trace) := by
          congr 1
          simpa [Ubig] using partialTraceA_mul_trace_eq_trace_mul_kronecker_one X
            (U : CMatrix b)
    _ ≤ traceNorm X := traceNorm_variational_unitary_abs_trace_le X Ubig

namespace PureVector

private theorem rankOneMatrix_mul_trace_re_eq_overlapSq (ψ φ : PureVector a) :
    (rankOneMatrix ψ.amp * rankOneMatrix φ.amp).trace.re = ψ.overlapSq φ := by
  have htrace : (rankOneMatrix ψ.amp * rankOneMatrix φ.amp).trace =
      ψ.overlap φ * star (ψ.overlap φ) := by
    let C : ℂ := ψ.overlap φ
    change (Matrix.vecMulVec ψ.amp (fun i => star (ψ.amp i)) *
        Matrix.vecMulVec φ.amp (fun i => star (φ.amp i))).trace = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ x, ψ.amp x * (C * star (φ.amp x))) = C * star C
    calc
      (∑ x, ψ.amp x * (C * star (φ.amp x))) =
          ∑ x, C * (star (φ.amp x) * ψ.amp x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
      _ = C * (∑ x, star (φ.amp x) * ψ.amp x) := by
            simp [Finset.mul_sum]
      _ = C * star C := by
            congr 1
            simp [C, PureVector.overlap, mul_comm]
  rw [htrace, PureVector.overlapSq_eq_normSq]
  simp [Complex.normSq]

/-- Squared pure-state overlaps are symmetric. -/
theorem overlapSq_comm (ψ φ : PureVector a) :
    φ.overlapSq ψ = ψ.overlapSq φ := by
  have hover : φ.overlap ψ = star (ψ.overlap φ) := by
    simp [PureVector.overlap, mul_comm]
  rw [PureVector.overlapSq_eq_normSq, PureVector.overlapSq_eq_normSq, hover]
  simp

/--
The Hilbert--Schmidt square of the difference of two pure states is determined
by their squared overlap.

This is the algebraic core used by the pure-state branch of the
Fuchs--van de Graaf upper-bound route.
-/
theorem state_sub_state_sq_trace_re_eq_two_mul_one_sub_overlapSq (ψ φ : PureVector a) :
    (((ψ.state.matrix - φ.state.matrix) *
        (ψ.state.matrix - φ.state.matrix)).trace).re =
      2 * (1 - ψ.overlapSq φ) := by
  have hψψ : (ψ.state.matrix * ψ.state.matrix).trace.re = 1 := by
    rw [PureVector.state_matrix_mul_self, ψ.state.trace_eq_one]
    norm_num
  have hφφ : (φ.state.matrix * φ.state.matrix).trace.re = 1 := by
    rw [PureVector.state_matrix_mul_self, φ.state.trace_eq_one]
    norm_num
  have hψφ : (ψ.state.matrix * φ.state.matrix).trace.re = ψ.overlapSq φ := by
    simpa [PureVector.state_matrix] using rankOneMatrix_mul_trace_re_eq_overlapSq ψ φ
  have hφψ : (φ.state.matrix * ψ.state.matrix).trace.re = ψ.overlapSq φ := by
    have h := rankOneMatrix_mul_trace_re_eq_overlapSq φ ψ
    simpa [PureVector.state_matrix, overlapSq_comm ψ φ] using h
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_re]
  rw [hψψ, hφφ, hψφ, hφψ]
  ring

private theorem state_sub_state_toEuclideanLin_mem_span
    (ψ φ : PureVector a) (x : EuclideanSpace ℂ a) :
    (ψ.state.matrix - φ.state.matrix).toEuclideanLin x ∈
      Submodule.span ℂ
        ({WithLp.toLp 2 ψ.amp, WithLp.toLp 2 φ.amp} : Set (EuclideanSpace ℂ a)) := by
  let cψ : ℂ := ∑ j, star (ψ.amp j) * x j
  let cφ : ℂ := ∑ j, star (φ.amp j) * x j
  have hx : (ψ.state.matrix - φ.state.matrix).toEuclideanLin x =
      cψ • WithLp.toLp 2 ψ.amp - cφ • WithLp.toLp 2 φ.amp := by
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.mulVec, dotProduct,
      PureVector.state_matrix, rankOneMatrix_apply, cψ, cφ, Finset.mul_sum, mul_comm,
      mul_left_comm]
  rw [hx]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ cψ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ cφ (Submodule.subset_span (by simp)))

private theorem state_sub_state_toEuclideanLin_finrank_range_le_two (ψ φ : PureVector a) :
    Module.finrank ℂ
      (LinearMap.range (ψ.state.matrix - φ.state.matrix).toEuclideanLin) ≤ 2 := by
  let s : Finset (EuclideanSpace ℂ a) :=
    {WithLp.toLp 2 ψ.amp, WithLp.toLp 2 φ.amp}
  let S : Submodule ℂ (EuclideanSpace ℂ a) := Submodule.span ℂ (s : Set _)
  have hle : LinearMap.range (ψ.state.matrix - φ.state.matrix).toEuclideanLin ≤ S := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simpa [S, s] using state_sub_state_toEuclideanLin_mem_span ψ φ x
  have hfin : Module.finrank ℂ S ≤ s.card := by
    simpa [S] using finrank_span_finset_le_card (R := ℂ) s
  have hcard : s.card ≤ 2 := by
    simpa [s] using
      (Finset.card_le_two (a := WithLp.toLp 2 ψ.amp) (b := WithLp.toLp 2 φ.amp))
  exact (Submodule.finrank_mono hle).trans (hfin.trans hcard)

/--
Pure-state trace distance is bounded by the usual root-overlap expression.

This is the hard algebraic ingredient for the Fuchs--van de Graaf upper
bound after Uhlmann's theorem reduces the general case to purifications.
-/
theorem normalizedTraceDistance_le_sqrt_one_sub_overlapSq (ψ φ : PureVector a) :
    ψ.state.normalizedTraceDistance φ.state ≤
      Real.sqrt (1 - ψ.overlapSq φ) := by
  let D : CMatrix a := ψ.state.matrix - φ.state.matrix
  have hDherm : D.IsHermitian := ψ.state.pos.isHermitian.sub φ.state.pos.isHermitian
  have hstar : star D = D := hDherm.eq
  have hhs : ((star D * D).trace).re = 2 * (1 - ψ.overlapSq φ) := by
    rw [hstar]
    exact state_sub_state_sq_trace_re_eq_two_mul_one_sub_overlapSq ψ φ
  have htrace_nonneg : 0 ≤ ((star D * D).trace).re :=
    (Matrix.PosSemidef.trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self D)).1
  have hoverlap_nonneg : 0 ≤ 1 - ψ.overlapSq φ := by
    rw [hhs] at htrace_nonneg
    nlinarith
  have hsq_traceNorm : traceNorm D ^ 2 ≤ 4 * (1 - ψ.overlapSq φ) := by
    have hrank : (Module.finrank ℂ (LinearMap.range D.toEuclideanLin) : ℝ) ≤ 2 := by
      exact_mod_cast state_sub_state_toEuclideanLin_finrank_range_le_two ψ φ
    have hmain := traceNorm_sq_le_finrank_range_mul_hilbertSchmidt D
    calc
      traceNorm D ^ 2
          ≤ (Module.finrank ℂ (LinearMap.range D.toEuclideanLin) : ℝ) *
              ((star D * D).trace).re := hmain
      _ ≤ 2 * ((star D * D).trace).re := by
          exact mul_le_mul_of_nonneg_right hrank htrace_nonneg
      _ = 4 * (1 - ψ.overlapSq φ) := by
          rw [hhs]
          ring
  have hsq_normDist : ((1 / 2 : ℝ) * traceNorm D) ^ 2 ≤ 1 - ψ.overlapSq φ := by
    nlinarith
  rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq]
  change (1 / 2 : ℝ) * traceDistance ψ.state.matrix φ.state.matrix ≤
      Real.sqrt (1 - ψ.overlapSq φ)
  rw [traceDistance]
  change (1 / 2 : ℝ) * traceNorm D ≤ Real.sqrt (1 - ψ.overlapSq φ)
  exact Real.le_sqrt_of_sq_le hsq_normDist

end PureVector

namespace State

private theorem audenaert_half_ge_one_sub_normalizedTraceDistance (ρ σ : State a) :
    ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re ≥
      1 - ρ.normalizedTraceDistance σ := by
  have hAud := audenaertTraceInequality (a := a) (s := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) ρ.pos σ.pos
  have hpowρ : CFC.rpow ρ.matrix (1 / 2 : ℝ) = ρ.sqrtMatrix := by
    simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
  have hpowσ : CFC.rpow σ.matrix (1 - (1 / 2 : ℝ)) = σ.sqrtMatrix := by
    norm_num
    simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
  have hAud' :
      ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re ≥
        ((ρ.matrix + σ.matrix - CFC.abs (ρ.matrix - σ.matrix)).trace).re / 2 := by
    rw [hpowρ, hpowσ] at hAud
    exact hAud
  have hnorm : traceNorm (ρ.matrix - σ.matrix) =
      (CFC.abs (ρ.matrix - σ.matrix)).trace.re := by
    rfl
  have hrhs :
      ((ρ.matrix + σ.matrix - CFC.abs (ρ.matrix - σ.matrix)).trace).re / 2 =
        1 - ρ.normalizedTraceDistance σ := by
    rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq]
    simp [QIT.traceDistance]
    rw [hnorm]
    simp [ρ.trace_eq_one, σ.trace_eq_one]
    ring
  exact hrhs ▸ hAud'

private theorem trace_re_sqrt_mul_sqrt_le_fidelity (ρ σ : State a) :
    ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re ≤ ρ.fidelity σ := by
  calc
    ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re
        ≤ Complex.abs ((ρ.sqrtMatrix * σ.sqrtMatrix).trace) := Complex.re_le_norm _
    _ = Complex.abs (((ρ.sqrtMatrix * σ.sqrtMatrix) * (1 : CMatrix a)).trace) := by
          simp
    _ ≤ traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix) := by
          simpa using traceNorm_variational_unitary_abs_trace_le
            (ρ.sqrtMatrix * σ.sqrtMatrix) (1 : Matrix.unitaryGroup a ℂ)
    _ = ρ.fidelity σ := rfl

/--
Fuchs--van de Graaf lower bound, using the local root-fidelity convention.

This proof uses Audenaert's finite-dimensional trace inequality at `s = 1/2`
to get `Re Tr(√ρ√σ) ≥ 1 - D(ρ,σ)`, then bounds that real trace by root
fidelity through the trace-norm variational theorem.
-/
theorem fuchs_van_de_graaf_lower (ρ σ : State a) :
    1 - ρ.fidelity σ ≤ ρ.normalizedTraceDistance σ := by
  have hAud := audenaert_half_ge_one_sub_normalizedTraceDistance ρ σ
  have hF := trace_re_sqrt_mul_sqrt_le_fidelity ρ σ
  linarith

/--
Fuchs--van de Graaf upper bound, using the local root-fidelity convention.

The proof is non-circular: Uhlmann chooses purifications attaining squared
fidelity, trace norm contracts under the reference partial trace, and the
remaining pure-state estimate is `PureVector.normalizedTraceDistance_le_sqrt_one_sub_overlapSq`.
-/
theorem fuchs_van_de_graaf_upper (ρ σ : State a) :
    ρ.normalizedTraceDistance σ ≤ Real.sqrt (1 - ρ.squaredFidelity σ) := by
  classical
  obtain ⟨U, hUeq, _⟩ :=
    State.exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity ρ σ
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  let Φ : PureVector (Prod a a) := U.applyPureVector σ.canonicalPurification
  let D : CMatrix (Prod a a) := Ψ.state.matrix - Φ.state.matrix
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  have hΦ : Φ.Purifies σ := by
    simpa [Φ] using U.toReferenceIsometry.applyPureVector_purifies σ.canonicalPurification_purifies
  have hdiff :
      ρ.matrix - σ.matrix = partialTraceA (a := a) (b := a) D := by
    change ρ.matrix - σ.matrix =
      partialTraceA (a := a) (b := a) (Ψ.state.matrix - Φ.state.matrix)
    rw [partialTraceA_sub, PureVector.partialTraceA_state_matrix_eq_of_purifies hΨ,
      PureVector.partialTraceA_state_matrix_eq_of_purifies hΦ]
  calc
    ρ.normalizedTraceDistance σ =
        (1 / 2 : ℝ) * traceNorm (ρ.matrix - σ.matrix) := by
          simp [State.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceDistance]
    _ = (1 / 2 : ℝ) * traceNorm (partialTraceA (a := a) (b := a) D) := by
          rw [hdiff]
    _ ≤ (1 / 2 : ℝ) * traceNorm D := by
          exact mul_le_mul_of_nonneg_left (traceNorm_partialTraceA_le D) (by norm_num)
    _ = Ψ.state.normalizedTraceDistance Φ.state := by
          simp [State.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceDistance, D]
    _ ≤ Real.sqrt (1 - Ψ.overlapSq Φ) :=
          PureVector.normalizedTraceDistance_le_sqrt_one_sub_overlapSq Ψ Φ
    _ = Real.sqrt (1 - ρ.squaredFidelity σ) := by
          rw [hUeq]

/-- Fuchs--van de Graaf inequalities, packaged together. -/
theorem fuchs_van_de_graaf (ρ σ : State a) :
    (1 - ρ.fidelity σ ≤ ρ.normalizedTraceDistance σ) ∧
      ρ.normalizedTraceDistance σ ≤ Real.sqrt (1 - ρ.squaredFidelity σ) :=
  ⟨fuchs_van_de_graaf_lower ρ σ, fuchs_van_de_graaf_upper ρ σ⟩

end State

end

end QIT
