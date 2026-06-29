/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Order properties of the positive semidefinite square root

The square root is operator monotone on positive semidefinite matrices: for
`A ≤ B` (both Hermitian) one has `psdSqrt A ≤ psdSqrt B`. This is the
continuous-functional-calculus image of the scalar monotonicity of `Real.sqrt`,
reached through mathlib's C⋆-algebra monotonicity lemma `CFC.sqrt_le_sqrt`.

To access the C⋆-algebra-level monotonicity lemmas on a finite complex matrix we
register the canonical (L2-operator-norm) `NonUnitalCStarAlgebra` structure on
`Matrix n n ℂ`. Mathlib exposes this norm behind the `Matrix.Norms.L2Operator`
scope rather than committing to a single global matrix norm; we declare the
composite instance here so that the continuous-functional-calculus order lemmas
apply to `CMatrix`. The structure is sound for finite matrices: the eigenbasis
continuous functional calculus already registered on `Matrix` is continuous in
any Hausdorff topology, hence is a valid calculus for the operator-norm algebra.
[Wilde2011Qst, qit-notes.tex:29562-29630] -/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open scoped Matrix.Norms.L2Operator

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The canonical non-unital C⋆-algebra structure on a finite complex matrix,
carried by the L2-operator norm. Mathlib keeps this behind the
`Matrix.Norms.L2Operator` scope to avoid choosing a global matrix norm; we
declare the composite instance here so that continuous-functional-calculus
order lemmas (`CFC.sqrt_le_sqrt`, operator monotonicity of `CFC.rpow`) apply to
`CMatrix`. -/
noncomputable instance instCMatrixNonUnitalCStarAlgebra (n : Type u)
    [Fintype n] [DecidableEq n] : NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

/-- Operator monotonicity of the square root: `A ≤ B` implies
`psdSqrt A ≤ psdSqrt B`. -/
theorem psdSqrt_le_psdSqrt_of_le {A B : CMatrix a} (hAB : A ≤ B) :
    psdSqrt A ≤ psdSqrt B := by
  show CFC.sqrt A ≤ CFC.sqrt B
  exact CFC.sqrt_le_sqrt _ _ hAB

/-- For a positive semidefinite matrix `S` with `S ≤ 1`, one has `S ≤ psdSqrt S`:
in the eigenbasis of `S` (with eigenvalues `λ ∈ [0,1]`), `psdSqrt S - S` is the
diagonal matrix `diag(√λ - λ)`, and `√λ - λ = √λ (1 - √λ) ≥ 0` since
`√λ ∈ [0,1]`. This is the `S ≤ S^{1/2}` half of the operator-monotone chain
`S ≤ √S ≤ √(S+T)` used in the Hayashi--Nagaoka argument and in the
`(1 - √Λ)² ≤ 1 - Λ` operator inequality of the gentle-operator lemma.
[Wilde2011Qst, qit-notes.tex:29562-29630] -/
theorem posSemidef_le_psdSqrt_of_le_one {S : CMatrix a}
    (hS : S.PosSemidef) (hS1 : S ≤ 1) : S ≤ psdSqrt S := by
  classical
  rw [Matrix.le_iff]
  -- Diagonalize `S = U D U†` with `D = diag(λ)`, eigenvalues `λ ∈ [0,1]`.
  let U : CMatrix a := hS.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => (hS.isHermitian.eigenvalues i : ℂ))
  have hSdiag : S = U * D * star U := by
    simpa [U, D, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hS.isHermitian.spectral_theorem
  have hUstarU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hS.isHermitian.eigenvectorUnitary]
  have hRdiag : psdSqrt S = U *
      Matrix.diagonal (fun i => (↑((hS.isHermitian.eigenvalues i) ^ ((1:ℝ)/2) : ℝ) : ℂ)) * star U := by
    show CFC.sqrt S = _
    rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real (a := S) (y := (1:ℝ)/2)
        (Matrix.nonneg_iff_posSemidef.mpr hS),
      Matrix.IsHermitian.cfc_eq hS.isHermitian, Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def]
    rfl
  -- Eigenvalues lie in [0,1]: `≥ 0` (PSD), `≤ 1` (from `S ≤ 1`).
  have hDle1 : ∀ i, hS.isHermitian.eigenvalues i ≤ 1 := by
    intro i
    have hsub : (1 - S).PosSemidef := by simpa [Matrix.le_iff] using hS1
    have hconj_eq : star U * (1 - S) * U = 1 - D := by
      rw [hSdiag]
      calc star U * (1 - (U * D * star U)) * U
          = star U * U - (star U * U) * D * (star U * U) := by noncomm_ring
        _ = 1 - D := by rw [hUstarU]; simp
    have hconj : (star U * (1 - S) * U).PosSemidef := by
      rw [Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
        IsUnit (U : CMatrix a))]
      exact hsub
    have hdiag_nonneg : 0 ≤ (1 - D) i i := by
      rw [← hconj_eq]; exact Matrix.PosSemidef.diag_nonneg hconj (i := i)
    have hdiag : (1 - D) i i = (1:ℂ) - hS.isHermitian.eigenvalues i := by simp [D]
    have hcomplex : (hS.isHermitian.eigenvalues i : ℂ) ≤ 1 := by
      simpa [hdiag, sub_nonneg] using hdiag_nonneg
    exact_mod_cast hcomplex
  set Rsqrt : CMatrix a :=
    Matrix.diagonal (fun i => (↑((hS.isHermitian.eigenvalues i) ^ ((1:ℝ)/2) : ℝ) : ℂ))
  have hsub : psdSqrt S - S = U * (Rsqrt - D) * star U := by
    rw [hRdiag, hSdiag]; noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  -- `Rsqrt - D` is PSD diagonal with entries `√λ - λ ≥ 0` for `λ ∈ [0,1]`.
  have hRD_diag : Rsqrt - D = Matrix.diagonal (fun i =>
      (↑((hS.isHermitian.eigenvalues i) ^ ((1:ℝ)/2) - hS.isHermitian.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Rsqrt, D]
    · simp [Rsqrt, D, Matrix.diagonal, hij]
  rw [hRD_diag, Matrix.posSemidef_diagonal_iff]
  intro i
  have hnn : 0 ≤ hS.isHermitian.eigenvalues i := hS.eigenvalues_nonneg i
  have hle : hS.isHermitian.eigenvalues i ≤ 1 := hDle1 i
  -- `λ^(1/2) = √λ`, and `√λ - λ = √λ (1 - √λ) ≥ 0` since `√λ ∈ [0,1]`.
  have hrpow_sqrt : hS.isHermitian.eigenvalues i ^ ((1:ℝ)/2) =
      Real.sqrt (hS.isHermitian.eigenvalues i) := by
    rw [Real.sqrt_eq_rpow]
  have hsqlt : Real.sqrt (hS.isHermitian.eigenvalues i) ≤ 1 :=
    Real.sqrt_le_one.mpr hle
  have hsge0 : 0 ≤ Real.sqrt (hS.isHermitian.eigenvalues i) := Real.sqrt_nonneg _
  have : 0 ≤ hS.isHermitian.eigenvalues i ^ ((1:ℝ)/2) - hS.isHermitian.eigenvalues i := by
    rw [hrpow_sqrt]
    have hsq : Real.sqrt (hS.isHermitian.eigenvalues i) *
        Real.sqrt (hS.isHermitian.eigenvalues i) = hS.isHermitian.eigenvalues i :=
      Real.mul_self_sqrt hnn
    nlinarith [hsge0, hsqlt, hsq, hnn, hle]
  exact_mod_cast this

end

end QIT
