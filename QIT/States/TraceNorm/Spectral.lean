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

end

end QIT
