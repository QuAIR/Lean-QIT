/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.Distance
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Spectral trace-norm bridge

This module proves the finite-dimensional bridge from the local trace-norm
definition `Tr sqrt(Mᴴ * M)` to the singular-value sum used by the trace-norm
variational route. The source claim is registered as
`m5-trace-norm-definition-and-singular-values`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Finite singular-value sum for a square complex matrix, expressed through
the local matrix spectral convention for `Mᴴ * M`. This is the same ordering as
`M.toEuclideanLin.singularValues`; see
`traceNormSingularValueSum_eq_linearMap_singularValues`. -/
def traceNormSingularValueSum (M : CMatrix a) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)

/-- The operator `Mᴴ * M` is the matrix representative of
`M.toEuclideanLin.adjoint.comp M.toEuclideanLin`. -/
theorem toEuclideanLin_conjTranspose_mul_self_eq_adjoint_comp (M : CMatrix a) :
    M.toEuclideanLin.adjoint.comp M.toEuclideanLin =
      (Mᴴ * M).toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint M]
  rw [Matrix.toLpLin_mul]

/-- The matrix eigenvalues used to define the local singular-value sum agree
with the eigenvalues underlying mathlib's `LinearMap.singularValues`. -/
theorem eigenvalues_conjTranspose_mul_self_eq_adjoint_comp (M : CMatrix a) (i : a) :
    (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i =
      (M.toEuclideanLin.isSymmetric_adjoint_comp_self).eigenvalues
        (n := Fintype.card a) (by simp)
        ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
  let hA : ((Mᴴ * M).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_conjTranspose_mul_self M)
  have hvals :
      hA.eigenvalues (n := Fintype.card a) (by simp) =
        (M.toEuclideanLin.isSymmetric_adjoint_comp_self).eigenvalues
          (n := Fintype.card a) (by simp) := by
    rw [(LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff hA (by simp)
      M.toEuclideanLin.isSymmetric_adjoint_comp_self (by simp)).2]
    rw [toEuclideanLin_conjTranspose_mul_self_eq_adjoint_comp M]
  simpa [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀, hA] using
    congrFun hvals ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

/-- The local singular-value sum is the finite sum of mathlib singular values
of the Euclidean linear map represented by `M`. -/
theorem traceNormSingularValueSum_eq_linearMap_singularValues (M : CMatrix a) :
    traceNormSingularValueSum M =
      (Finset.range (Fintype.card a)).sum fun i => M.toEuclideanLin.singularValues i := by
  rw [traceNormSingularValueSum, ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  intro i
  let hA : ((Mᴴ * M).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_conjTranspose_mul_self M)
  have hvals :
      hA.eigenvalues (n := Fintype.card a) (by simp) =
        (M.toEuclideanLin.isSymmetric_adjoint_comp_self).eigenvalues
          (n := Fintype.card a) (by simp) := by
    rw [(LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff hA (by simp)
      M.toEuclideanLin.isSymmetric_adjoint_comp_self (by simp)).2]
    rw [toEuclideanLin_conjTranspose_mul_self_eq_adjoint_comp M]
  rw [LinearMap.singularValues_fin (T := M.toEuclideanLin) (hn := by simp)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)]
  simpa [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀, hA] using
    congrArg Real.sqrt (congrFun hvals ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i))

/-- The CFC square-root trace unfolds to the finite sum of square roots of the
eigenvalues of `Mᴴ * M`. -/
theorem psdSqrt_conjTranspose_mul_self_trace_eq_singularValueSum (M : CMatrix a) :
    (psdSqrt (Mᴴ * M)).trace =
      ∑ i, ((Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i) : ℝ) : ℂ) := by
  have hpsd : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  rw [psdSqrt]
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ (Mᴴ * M), hpsd.1.cfc_eq]
  simp only [Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    Matrix.trace_diagonal]
  simp only [Function.comp_apply, Real.coe_sqrt, Real.coe_toNNReal']
  simp [hpsd.eigenvalues_nonneg]

/-- The local trace norm equals the finite singular-value sum. -/
theorem traceNorm_eq_singularValueSum (M : CMatrix a) :
    traceNorm M = traceNormSingularValueSum M := by
  rw [traceNorm, traceNormSingularValueSum]
  have htrace := psdSqrt_conjTranspose_mul_self_trace_eq_singularValueSum M
  rw [htrace]
  simp

/-- The local trace norm equals the sum over the nonzero singular-value
support of the represented Euclidean linear map. -/
theorem traceNorm_eq_singularValues_support_sum (M : CMatrix a) :
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

/-- The squared singular values sum to the Hilbert-Schmidt trace
`Re Tr(Mᴴ * M)`. -/
theorem singularValues_sum_sq_eq_trace_conjTranspose_mul_self (M : CMatrix a) :
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

/-- The support sum of squared singular values is the Hilbert-Schmidt trace
`Re Tr(Mᴴ * M)`. -/
theorem singularValues_support_sum_sq_eq_trace_conjTranspose_mul_self (M : CMatrix a) :
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

/-- Cauchy-Schwarz bridge from the trace norm to the Hilbert-Schmidt trace,
with rank measured by the Euclidean-linear range dimension. -/
theorem traceNorm_sq_le_finrank_range_mul_hilbertSchmidt (M : CMatrix a) :
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

end

end QIT
