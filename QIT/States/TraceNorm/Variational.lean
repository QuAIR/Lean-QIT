/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.GramFactorization
public import QIT.States.Purification.ReferenceUnitary
public import QIT.States.TraceNorm.Spectral
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Trace-norm variational witness

This module proves the finite-dimensional trace-norm variational route:
existence of an attaining matrix unitary, the universal upper bound for every
matrix unitary, and the `ReferenceUnitary` squared repackaging used downstream
by the Uhlmann leaf.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace Complex

/-- Local source-shaped notation for the complex modulus. Mathlib's canonical
API uses `‖z‖`; the source and backlog state the variational theorem with
`|z|`, so this thin alias keeps the public theorem close to the source. -/
noncomputable abbrev abs (z : ℂ) : ℝ :=
  ‖z‖

end Complex

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem complex_normSq_le_sq_of_abs_le {z : ℂ} {r : ℝ}
    (h : Complex.abs z ≤ r) :
    Complex.normSq z ≤ r ^ 2 := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hnorm : ‖z‖ ≤ r := h
  have hr : 0 ≤ r := hz.trans hnorm
  rw [Complex.normSq_eq_norm_sq]
  exact (sq_le_sq₀ hz hr).2 hnorm

private theorem transpose_referenceIsometry_matrix_mem_unitary
    (V : ReferenceIsometry a a) :
    Matrix.transpose V.matrix ∈ Matrix.unitaryGroup a ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have h := congrFun (congrFun V.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose, Matrix.one_apply,
    Finset.mul_sum, mul_comm, eq_comm] using h

private theorem trace_diagonal_mul_eq_sum (d : a → ℂ) (U : CMatrix a) :
    (Matrix.diagonal d * U).trace = ∑ i, d i * U i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

private theorem posSemidef_trace_mul_unitary_abs_le_trace_re
    (P : CMatrix a) (hP : P.PosSemidef) (U : Matrix.unitaryGroup a ℂ) :
    Complex.abs ((P * (U : CMatrix a)).trace) ≤ P.trace.re := by
  classical
  let E : Matrix.unitaryGroup a ℂ := hP.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ))
  let U' : Matrix.unitaryGroup a ℂ := E⁻¹ * U * E
  have hPdiag : P = (E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [E, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hP.1.spectral_theorem
  have htrace :
      (P * (U : CMatrix a)).trace = (D * (U' : CMatrix a)).trace := by
    calc
      (P * (U : CMatrix a)).trace =
          (((E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ)) * U).trace := by
            simp [hPdiag]
      _ = ((E : CMatrix a) * D * ((E⁻¹ : Matrix.unitaryGroup a ℂ) * U)).trace := by
            simp [Matrix.mul_assoc]
      _ = (((E⁻¹ : Matrix.unitaryGroup a ℂ) * U) * (E : CMatrix a) * D).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (D * (U' : CMatrix a)).trace := by
            rw [Matrix.trace_mul_comm]
            simp [U', Matrix.mul_assoc]
  have hdiag :
      (D * (U' : CMatrix a)).trace =
        ∑ i, ((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i := by
    simpa [D] using trace_diagonal_mul_eq_sum
      (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ)) (U' : CMatrix a)
  have hsum_abs :
      Complex.abs ((D * (U' : CMatrix a)).trace) ≤
        ∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ := by
    rw [hdiag]
    simpa [Complex.abs] using
      (norm_sum_le (s := Finset.univ)
        (f := fun i => ((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i))
  have hterm :
      (fun i => ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖) ≤
        fun i => hP.1.eigenvalues i := by
    intro i
    have hlambda : 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg i
    have hentry : ‖(U' : CMatrix a) i i‖ ≤ (1 : ℝ) :=
      entry_norm_bound_of_unitary (show (U' : CMatrix a) ∈ Matrix.unitaryGroup a ℂ from U'.2) i i
    calc
      ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ =
          hP.1.eigenvalues i * ‖(U' : CMatrix a) i i‖ := by
            simp [abs_of_nonneg hlambda]
      _ ≤ hP.1.eigenvalues i * 1 :=
            mul_le_mul_of_nonneg_left hentry hlambda
      _ = hP.1.eigenvalues i := by simp
  have hsum_le : (∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖) ≤
      ∑ i, hP.1.eigenvalues i := by
    exact Finset.sum_le_sum fun i _ => hterm i
  have htrace_sum : P.trace.re = ∑ i, hP.1.eigenvalues i := by
    have h := hP.1.trace_eq_sum_eigenvalues
    exact (congrArg Complex.re h).trans (by simp)
  calc
    Complex.abs ((P * (U : CMatrix a)).trace) =
        Complex.abs ((D * (U' : CMatrix a)).trace) := by rw [htrace]
    _ ≤ ∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ := hsum_abs
    _ ≤ ∑ i, hP.1.eigenvalues i := hsum_le
    _ = P.trace.re := htrace_sum.symm

/-- The unitary-attainment half of the finite-dimensional trace-norm
variational characterization: there is a unitary matrix attaining
`|Tr(MU)| = ‖M‖₁`. -/
theorem traceNorm_variational_exists_unitary_abs_trace (M : CMatrix a) :
    ∃ U : Matrix.unitaryGroup a ℂ,
      Complex.abs ((M * (U : Matrix a a ℂ)).trace) = traceNorm M := by
  classical
  let P : CMatrix a := psdSqrt (Mᴴ * M)
  have hP_hm : P.IsHermitian := psdSqrt_isHermitian (Mᴴ * M)
  have hP_sq : P * P = Mᴴ * M :=
    psdSqrt_mul_self_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self M)
  have hGram : P * Pᴴ = Mᴴ * (Mᴴ)ᴴ := by
    rw [hP_hm.eq, hP_sq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := P) (B := Mᴴ) hGram (Nat.le_refl _)
  let W : Matrix a a ℂ := Matrix.transpose V.matrix
  have hW_unit : W ∈ Matrix.unitaryGroup a ℂ := by
    simpa [W] using transpose_referenceIsometry_matrix_mem_unitary V
  refine ⟨⟨W, hW_unit⟩, ?_⟩
  have hM : M = Wᴴ * P := by
    have h := congrArg Matrix.conjTranspose hV
    simpa [W, hP_hm.eq, Matrix.conjTranspose_mul] using h
  have htrace : (M * W).trace = P.trace := by
    calc
      (M * W).trace = (Wᴴ * P * W).trace := by simp [hM, Matrix.mul_assoc]
      _ = (W * Wᴴ * P).trace := by
        rw [Matrix.trace_mul_cycle]
      _ = P.trace := by
        change ((W * star W) * P).trace = P.trace
        rw [(Matrix.mem_unitaryGroup_iff.mp hW_unit)]
        simp
  have hP_trace_nonneg : 0 ≤ P.trace :=
    Matrix.PosSemidef.trace_nonneg (psdSqrt_pos (Mᴴ * M))
  calc
    Complex.abs ((M * W).trace) = Complex.abs P.trace := by rw [htrace]
    _ = traceNorm M := by
      have hnorm : Complex.abs P.trace = P.trace.re := by
        have hcoe := Complex.eq_coe_norm_of_nonneg hP_trace_nonneg
        have hre : P.trace.re = ‖P.trace‖ := by
          exact (congrArg Complex.re hcoe).trans (by simp)
        exact hre.symm
      simpa [P, traceNorm] using hnorm

/-- The universal upper-bound half of the finite-dimensional trace-norm
variational characterization: every unitary matrix gives
`|Tr(MU)| ≤ ‖M‖₁`. -/
theorem traceNorm_variational_unitary_abs_trace_le
    (M : CMatrix a) (U : Matrix.unitaryGroup a ℂ) :
    Complex.abs ((M * (U : Matrix a a ℂ)).trace) ≤ traceNorm M := by
  classical
  let P : CMatrix a := psdSqrt (Mᴴ * M)
  have hP_hm : P.IsHermitian := psdSqrt_isHermitian (Mᴴ * M)
  have hP_sq : P * P = Mᴴ * M :=
    psdSqrt_mul_self_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self M)
  have hGram : P * Pᴴ = Mᴴ * (Mᴴ)ᴴ := by
    rw [hP_hm.eq, hP_sq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := P) (B := Mᴴ) hGram (Nat.le_refl _)
  let W : Matrix.unitaryGroup a ℂ :=
    ⟨Matrix.transpose V.matrix, transpose_referenceIsometry_matrix_mem_unitary V⟩
  have hM : M = (W : CMatrix a)ᴴ * P := by
    have h := congrArg Matrix.conjTranspose hV
    simpa [W, hP_hm.eq, Matrix.conjTranspose_mul] using h
  let Z : Matrix.unitaryGroup a ℂ := U * W⁻¹
  have htrace : (M * (U : CMatrix a)).trace = (P * (Z : CMatrix a)).trace := by
    calc
      (M * (U : CMatrix a)).trace = ((W : CMatrix a)ᴴ * P * U).trace := by
        simp [hM, Matrix.mul_assoc]
      _ = (P * ((U : CMatrix a) * star (W : CMatrix a))).trace := by
        rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
        simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = (P * (Z : CMatrix a)).trace := by
        simp [Z]
  have hP_trace_abs_le :=
    posSemidef_trace_mul_unitary_abs_le_trace_re P (psdSqrt_pos (Mᴴ * M)) Z
  calc
    Complex.abs ((M * (U : CMatrix a)).trace) =
        Complex.abs ((P * (Z : CMatrix a)).trace) := by rw [htrace]
    _ ≤ P.trace.re := hP_trace_abs_le
    _ = traceNorm M := by rfl

/-- Matrix-level packaging of the finite-dimensional trace-norm variational
characterization: an attaining unitary exists and every unitary is bounded by
the trace norm. -/
theorem traceNorm_eq_max_unitary_abs_trace (M : CMatrix a) :
    (∃ U : Matrix.unitaryGroup a ℂ,
      Complex.abs ((M * (U : Matrix a a ℂ)).trace) = traceNorm M) ∧
      ∀ U : Matrix.unitaryGroup a ℂ,
        Complex.abs ((M * (U : Matrix a a ℂ)).trace) ≤ traceNorm M :=
  ⟨traceNorm_variational_exists_unitary_abs_trace M,
    traceNorm_variational_unitary_abs_trace_le M⟩

/-- The trace-norm variational maximum can be attained by a `ReferenceUnitary`
in the transposed matrix convention used by the Uhlmann route. -/
theorem traceNorm_variational_exists_referenceUnitary_sq (M : CMatrix a) :
    ∃ U : ReferenceUnitary a,
      Complex.normSq ((M * Matrix.transpose U.matrix).trace) = (traceNorm M) ^ 2 := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace M
  let V : ReferenceUnitary a := ⟨Matrix.UnitaryGroup.transpose U⟩
  refine ⟨V, ?_⟩
  have hAbs :
      Complex.abs ((M * Matrix.transpose V.matrix).trace) = traceNorm M := by
    simpa [V] using hU
  simp [Complex.normSq_eq_norm_sq, hAbs]

/-- Every `ReferenceUnitary` gives a squared trace expression bounded by the
squared trace norm, in the transposed matrix convention used downstream. -/
theorem traceNorm_variational_referenceUnitary_sq_le
    (M : CMatrix a) (U : ReferenceUnitary a) :
    Complex.normSq ((M * Matrix.transpose U.matrix).trace) ≤ (traceNorm M) ^ 2 := by
  classical
  have hAbs :
      Complex.abs ((M * Matrix.transpose U.matrix).trace) ≤ traceNorm M := by
    simpa using traceNorm_variational_unitary_abs_trace_le M
      (Matrix.UnitaryGroup.transpose U.matrix)
  exact complex_normSq_le_sq_of_abs_le hAbs

end

end QIT
