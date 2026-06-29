/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite-dimensional Schatten `p`-norm kernels

This module introduces the PSD matrix power-trace expression, the associated
spectral Schatten `p`-norm expression, and the finite-dimensional PSD trace
Holder upper bounds used by the one-shot Renyi proof route.

The reverse-Holder and support-domination side of the route is handled by
separate negative-power infrastructure.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix Polynomial

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

omit [DecidableEq a] in
theorem partialTraceB_leftKroneckerOne_mul
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    partialTraceB (a := a) (b := b) (Matrix.kronecker U (1 : CMatrix b) * X) =
      U * partialTraceB (a := a) (b := b) X := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq a] in
theorem partialTraceB_mul_leftKroneckerOne
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    partialTraceB (a := a) (b := b) (X * Matrix.kronecker U (1 : CMatrix b)) =
      partialTraceB (a := a) (b := b) X * U := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem partialTraceB_left_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ) :
    partialTraceB (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
      star (U : CMatrix a) * partialTraceB (a := a) (b := b) X *
        (U : CMatrix a) := by
  have hstar :
      star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
        Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (U : CMatrix a) (1 : CMatrix b)
  rw [hstar]
  calc
    partialTraceB (a := a) (b := b)
        ((Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) * X) *
          Matrix.kronecker (U : CMatrix a) (1 : CMatrix b))
        =
          partialTraceB (a := a) (b := b)
            (Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) * X) *
            (U : CMatrix a) := by
            rw [partialTraceB_mul_leftKroneckerOne]
    _ = (star (U : CMatrix a) * partialTraceB (a := a) (b := b) X) *
          (U : CMatrix a) := by
            rw [partialTraceB_leftKroneckerOne_mul]
    _ = star (U : CMatrix a) * partialTraceB (a := a) (b := b) X *
          (U : CMatrix a) := by
            rw [Matrix.mul_assoc]

theorem partialTraceB_right_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : Matrix.unitaryGroup b ℂ) :
    partialTraceB (a := a) (b := b)
        (star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
      partialTraceB (a := a) (b := b) X := by
  classical
  ext i i'
  have hstar :
      star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
        Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (1 : CMatrix a) (V : CMatrix b)
  rw [hstar]
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm, mul_comm]
  have hunit : (V : CMatrix b) * star (V : CMatrix b) = 1 :=
    Unitary.coe_mul_star_self V
  have hrow : ∀ x₁ x₂ : b,
      (∑ x, (V : CMatrix b) x₁ x * star ((V : CMatrix b) x₂ x)) =
        if x₁ = x₂ then 1 else 0 := by
    intro x₁ x₂
    have h := congrFun (congrFun hunit x₁) x₂
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  calc
    ∑ x, ∑ x_1, ∑ x_2,
        X (i, x_2) (i', x_1) *
          ((V : CMatrix b) x_1 x * star ((V : CMatrix b) x_2 x))
        =
      ∑ x_1, ∑ x_2, ∑ x,
        X (i, x_2) (i', x_1) *
          ((V : CMatrix b) x_1 x * star ((V : CMatrix b) x_2 x)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x_1 _ => ?_
        rw [Finset.sum_comm]
    _ =
      ∑ x_1, ∑ x_2,
        X (i, x_2) (i', x_1) *
          (∑ x, (V : CMatrix b) x_1 x * star ((V : CMatrix b) x_2 x)) := by
        simp [Finset.mul_sum]
    _ = ∑ x_1, ∑ x_2,
        X (i, x_2) (i', x_1) * (if x_1 = x_2 then 1 else 0) := by
        simp_rw [hrow]
    _ = ∑ j, X (i, j) (i', j) := by
        simp

theorem partialTraceA_rightKroneckerOne_mul
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : CMatrix b) :
    partialTraceA (a := a) (b := b) (Matrix.kronecker (1 : CMatrix a) V * X) =
      V * partialTraceA (a := a) (b := b) X := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem partialTraceA_mul_rightKroneckerOne
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : CMatrix b) :
    partialTraceA (a := a) (b := b) (X * Matrix.kronecker (1 : CMatrix a) V) =
      partialTraceA (a := a) (b := b) X * V := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem partialTraceA_right_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : Matrix.unitaryGroup b ℂ) :
    partialTraceA (a := a) (b := b)
        (star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
      star (V : CMatrix b) * partialTraceA (a := a) (b := b) X *
        (V : CMatrix b) := by
  have hstar :
      star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
        Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (1 : CMatrix a) (V : CMatrix b)
  rw [hstar]
  calc
    partialTraceA (a := a) (b := b)
        ((Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) * X) *
          Matrix.kronecker (1 : CMatrix a) (V : CMatrix b))
        =
          partialTraceA (a := a) (b := b)
            (Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) * X) *
            (V : CMatrix b) := by
            rw [partialTraceA_mul_rightKroneckerOne]
    _ = (star (V : CMatrix b) * partialTraceA (a := a) (b := b) X) *
          (V : CMatrix b) := by
            rw [partialTraceA_rightKroneckerOne_mul]
    _ = star (V : CMatrix b) * partialTraceA (a := a) (b := b) X *
          (V : CMatrix b) := by
            rw [Matrix.mul_assoc]

theorem partialTraceA_left_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ) :
    partialTraceA (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
      partialTraceA (a := a) (b := b) X := by
  classical
  ext j j'
  have hstar :
      star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
        Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (U : CMatrix a) (1 : CMatrix b)
  rw [hstar]
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm, mul_comm]
  have hunit : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have hrow : ∀ x₁ x₂ : a,
      (∑ x, (U : CMatrix a) x₁ x * star ((U : CMatrix a) x₂ x)) =
        if x₁ = x₂ then 1 else 0 := by
    intro x₁ x₂
    have h := congrFun (congrFun hunit x₁) x₂
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  calc
    ∑ x, ∑ x_1, ∑ x_2,
        X (x_2, j) (x_1, j') *
          ((U : CMatrix a) x_1 x * star ((U : CMatrix a) x_2 x))
        =
      ∑ x_1, ∑ x_2, ∑ x,
        X (x_2, j) (x_1, j') *
          ((U : CMatrix a) x_1 x * star ((U : CMatrix a) x_2 x)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x_1 _ => ?_
        rw [Finset.sum_comm]
    _ =
      ∑ x_1, ∑ x_2,
        X (x_2, j) (x_1, j') *
          (∑ x, (U : CMatrix a) x_1 x * star ((U : CMatrix a) x_2 x)) := by
        simp [Finset.mul_sum]
    _ = ∑ x_1, ∑ x_2,
        X (x_2, j) (x_1, j') * (if x_1 = x_2 then 1 else 0) := by
        simp_rw [hrow]
    _ = ∑ i, X (i, j) (i, j') := by
        simp

theorem partialTraceB_local_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ)
    (V : Matrix.unitaryGroup b ℂ) :
    partialTraceB (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) =
      star (U : CMatrix a) * partialTraceB (a := a) (b := b) X *
        (U : CMatrix a) := by
  let K : CMatrix (Prod a b) := Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)
  let L : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)
  have hfactor :
      Matrix.kronecker (U : CMatrix a) (V : CMatrix b) = K * L := by
    simpa using
      (Matrix.mul_kronecker_mul (U : CMatrix a) (1 : CMatrix a)
        (1 : CMatrix b) (V : CMatrix b))
  rw [hfactor]
  have houter :
      partialTraceB (a := a) (b := b) (star (K * L) * X * (K * L)) =
        partialTraceB (a := a) (b := b) (star K * X * K) := by
    rw [star_mul]
    simpa [K, L, Matrix.mul_assoc] using
      partialTraceB_right_unitary_conj (a := a) (b := b) (star K * X * K) V
  rw [houter]
  simpa [K] using partialTraceB_left_unitary_conj (a := a) (b := b) X U

theorem partialTraceA_local_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ)
    (V : Matrix.unitaryGroup b ℂ) :
    partialTraceA (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) =
      star (V : CMatrix b) * partialTraceA (a := a) (b := b) X *
        (V : CMatrix b) := by
  let K : CMatrix (Prod a b) := Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)
  let L : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)
  have hfactor :
      Matrix.kronecker (U : CMatrix a) (V : CMatrix b) = K * L := by
    simpa using
      (Matrix.mul_kronecker_mul (U : CMatrix a) (1 : CMatrix a)
        (1 : CMatrix b) (V : CMatrix b))
  rw [hfactor]
  have houter :
      partialTraceA (a := a) (b := b) (star (K * L) * X * (K * L)) =
        star (V : CMatrix b) *
          partialTraceA (a := a) (b := b) (star K * X * K) *
            (V : CMatrix b) := by
    rw [star_mul]
    simpa [K, L, Matrix.mul_assoc] using
      partialTraceA_right_unitary_conj (a := a) (b := b) (star K * X * K) V
  rw [houter]
  rw [partialTraceA_left_unitary_conj (a := a) (b := b) X U]

theorem kronecker_mem_unitaryGroup
    {b : Type v} [Fintype b] [DecidableEq b]
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    Matrix.kronecker (U : CMatrix a) (V : CMatrix b) ∈
      Matrix.unitaryGroup (Prod a b) ℂ := by
  exact kronecker_mem_unitary U.2 V.2

namespace Matrix

/-- Support domination for finite matrices, represented as kernel inclusion:
`M` is supported by `N` when every vector killed by `N` is also killed by
`M`.  For PSD matrices this is the finite-dimensional `M << N` condition
used in the reverse-Holder variational formula. -/
def Supports (M N : CMatrix a) : Prop :=
  ∀ v : a → ℂ, N.mulVec v = 0 → M.mulVec v = 0

omit [DecidableEq a] in
theorem Supports.refl (M : CMatrix a) : Supports M M :=
  fun _ h => h

/-- Support domination is transitive. -/
theorem Supports.trans {M N P : CMatrix a}
    (hMN : Supports M N) (hNP : Supports N P) :
    Supports M P :=
  fun v hPv => hMN v (hNP v hPv)

/-- Entrywise support domination for real diagonal matrices. -/
theorem Supports.diagonal_of_real_zero_imp_zero {d e : a → ℝ}
    (h : ∀ i, e i = 0 → d i = 0) :
    Supports
      (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a)
      (Matrix.diagonal fun i => ((e i : ℝ) : ℂ) : CMatrix a) := by
  intro v hv
  ext i
  have hi := congrFun hv i
  by_cases he : e i = 0
  · simp [Matrix.mulVec, dotProduct, Matrix.diagonal, h i he]
  · have heC : ((e i : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast he
    have hvi : v i = 0 := by
      simpa [Matrix.mulVec, dotProduct, Matrix.diagonal, heC] using hi
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal, hvi]

/-- Support domination is invariant under simultaneous unitary conjugation. -/
theorem Supports.unitary_conj {M N : CMatrix a} (h : Supports M N)
    (U : Matrix.unitaryGroup a ℂ) :
    Supports
      ((U : CMatrix a) * M * star (U : CMatrix a))
      ((U : CMatrix a) * N * star (U : CMatrix a)) := by
  intro v hv
  have hleft := congrArg (fun w => star (U : CMatrix a) *ᵥ w) hv
  have hN : N *ᵥ (star (U : CMatrix a) *ᵥ v) = 0 := by
    have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
      Unitary.coe_star_mul_self U
    have hmat : star (U : CMatrix a) * ((U : CMatrix a) * N * star (U : CMatrix a)) =
        N * star (U : CMatrix a) := by
      calc
        star (U : CMatrix a) * ((U : CMatrix a) * N * star (U : CMatrix a))
            = (star (U : CMatrix a) * ((U : CMatrix a) * N)) *
                star (U : CMatrix a) := by noncomm_ring
        _ = ((star (U : CMatrix a) * (U : CMatrix a)) * N) *
                star (U : CMatrix a) := by rw [← Matrix.mul_assoc]
        _ = N * star (U : CMatrix a) := by rw [hUU, Matrix.one_mul]
    simpa [Matrix.mulVec_mulVec, hmat] using hleft
  have hM : M *ᵥ (star (U : CMatrix a) *ᵥ v) = 0 :=
    h (star (U : CMatrix a) *ᵥ v) hN
  have hright := congrArg (fun w => (U : CMatrix a) *ᵥ w) hM
  have hUU : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have hmat : (U : CMatrix a) * (M * star (U : CMatrix a)) =
      (U : CMatrix a) * M * star (U : CMatrix a) := by
    rw [Matrix.mul_assoc]
  simpa [Matrix.mulVec_mulVec, hmat, hUU] using hright

end Matrix

/-- Each row of a finite unitary matrix has squared entry norms summing to one. -/
theorem unitary_row_normSq_sum (U : Matrix.unitaryGroup a ℂ) (i : a) :
    ∑ j, Complex.normSq ((U : CMatrix a) i j) = 1 := by
  have hunit : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    exact Unitary.coe_mul_star_self U
  have hij := congrFun (congrFun hunit i) i
  have hre := congrArg Complex.re hij
  simpa [Matrix.mul_apply, Matrix.one_apply, Complex.normSq_eq_conj_mul_self,
    mul_comm] using hre

/-- Each column of a finite unitary matrix has squared entry norms summing to one. -/
theorem unitary_col_normSq_sum (U : Matrix.unitaryGroup a ℂ) (j : a) :
    ∑ i, Complex.normSq ((U : CMatrix a) i j) = 1 := by
  have hunit : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    exact Unitary.coe_star_mul_self U
  have hij := congrFun (congrFun hunit j) j
  have hre := congrArg Complex.re hij
  simpa [Matrix.mul_apply, Matrix.one_apply, Complex.normSq_eq_conj_mul_self,
    mul_comm] using hre

/-- A PSD matrix diagonal entry is the convex spectral average determined by
the corresponding eigenvector-unitary row. -/
theorem posSemidef_diagonal_re_eq_eigenvalue_weighted_sum
    {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    (B i i).re =
      ∑ j, hB.isHermitian.eigenvalues j *
        Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hB.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun j => ((hB.isHermitian.eigenvalues j : ℝ) : ℂ))
  have hBdiag : B = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hB.isHermitian.spectral_theorem
  have hentry := congrFun (congrFun hBdiag i) i
  have hre := congrArg Complex.re hentry
  simpa [U, D, Matrix.mul_apply, Matrix.diagonal, Complex.normSq_eq_conj_mul_self,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hre

/-- Diagonal entries of a PSD matrix are nonnegative in real part. -/
theorem posSemidef_diagonal_re_nonneg {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    0 ≤ (B i i).re := by
  rw [posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (hB.eigenvalues_nonneg j) (Complex.normSq_nonneg _)

/-- Trace pairing with a PSD left factor, expanded in that factor's eigenbasis. -/
theorem posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
    {M B : CMatrix a} (hM : M.PosSemidef) :
    ((M * B).trace).re =
      ∑ i, hM.isHermitian.eigenvalues i *
        ((star (hM.isHermitian.eigenvectorUnitary : CMatrix a) * B *
          (hM.isHermitian.eigenvectorUnitary : CMatrix a)) i i).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hM.isHermitian.eigenvalues i : ℝ) : ℂ))
  let B' : CMatrix a := star (U : CMatrix a) * B * (U : CMatrix a)
  have hMdiag : M = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hM.isHermitian.spectral_theorem
  have htrace :
      (M * B).trace = (D * B').trace := by
    calc
      (M * B).trace =
          (((U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ)) * B).trace := by
            rw [hMdiag]
      _ = (((U : CMatrix a) * (D * (star (U : CMatrix a) * B)))).trace := by
            rw [Matrix.mul_assoc]
            simp [Matrix.mul_assoc]
      _ = ((D * (star (U : CMatrix a) * B)) * (U : CMatrix a)).trace := by
            exact Matrix.trace_mul_comm (U : CMatrix a)
              (D * (star (U : CMatrix a) * B))
      _ = (D * B').trace := by
            simp [B', Matrix.mul_assoc]
  have hdiag :
      (D * B').trace =
        ∑ i, ((hM.isHermitian.eigenvalues i : ℝ) : ℂ) * B' i i := by
    simp [D, Matrix.trace, Matrix.diagonal_mul]
  have hre := congrArg Complex.re (htrace.trans hdiag)
  simpa [U, B', Complex.mul_re] using hre

/-- Jensen bound for PSD diagonal entries: the `q`-power of a diagonal entry is
bounded by the matching convex combination of spectral `q`-powers. -/
theorem posSemidef_diagonal_re_rpow_le_eigenvalue_weighted_rpow
    {B : CMatrix a} (hB : B.PosSemidef) {q : ℝ} (hq : 1 ≤ q) (i : a) :
    (B i i).re ^ q ≤
      ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        hB.isHermitian.eigenvalues j ^ q := by
  classical
  let w : a → ℝ := fun j =>
    Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)
  let evals : a → ℝ := fun j => hB.isHermitian.eigenvalues j
  have hw_nonneg : ∀ j ∈ (Finset.univ : Finset a), 0 ≤ w j := by
    intro j _
    exact Complex.normSq_nonneg _
  have hw_sum : ∑ j ∈ (Finset.univ : Finset a), w j = 1 := by
    simpa [w] using unitary_row_normSq_sum hB.isHermitian.eigenvectorUnitary i
  have hevals_mem : ∀ j ∈ (Finset.univ : Finset a), evals j ∈ Set.Ici (0 : ℝ) := by
    intro j _
    exact hB.eigenvalues_nonneg j
  have hjensen :=
    (convexOn_rpow hq).map_sum_le
      (t := (Finset.univ : Finset a)) (w := w) (p := evals)
      hw_nonneg hw_sum hevals_mem
  have hdiag :
      (B i i).re = ∑ j ∈ (Finset.univ : Finset a), w j * evals j := by
    simpa [w, evals, mul_comm] using
      posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i
  rw [hdiag]
  simpa [w, evals, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Concave Jensen bound for PSD diagonal entries in the range `0 ≤ p ≤ 1`:
the spectral `p`-power average of a diagonal entry is bounded by the
`p`-power of that diagonal entry. -/
theorem eigenvalue_weighted_rpow_le_posSemidef_diagonal_re_rpow
    {B : CMatrix a} (hB : B.PosSemidef) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : a) :
    (∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        hB.isHermitian.eigenvalues j ^ p) ≤
      (B i i).re ^ p := by
  classical
  let w : a → ℝ := fun j =>
    Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)
  let evals : a → ℝ := fun j => hB.isHermitian.eigenvalues j
  have hw_nonneg : ∀ j ∈ (Finset.univ : Finset a), 0 ≤ w j := by
    intro j _
    exact Complex.normSq_nonneg _
  have hw_sum : ∑ j ∈ (Finset.univ : Finset a), w j = 1 := by
    simpa [w] using unitary_row_normSq_sum hB.isHermitian.eigenvectorUnitary i
  have hevals_mem : ∀ j ∈ (Finset.univ : Finset a), evals j ∈ Set.Ici (0 : ℝ) := by
    intro j _
    exact hB.eigenvalues_nonneg j
  have hjensen :=
    (Real.concaveOn_rpow hp0 hp1).le_map_sum
      (t := (Finset.univ : Finset a)) (w := w) (p := evals)
      hw_nonneg hw_sum hevals_mem
  have hdiag :
      (B i i).re = ∑ j ∈ (Finset.univ : Finset a), w j * evals j := by
    simpa [w, evals, mul_comm] using
      posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i
  rw [hdiag]
  simpa [w, evals, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Real powers of positive semidefinite matrices are positive semidefinite. -/
theorem cMatrix_rpow_posSemidef {s : ℝ} {A : CMatrix a}
    (_hA : A.PosSemidef) :
    (CFC.rpow A s).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := s))

/-- Power-of-power reduction for PSD matrices and nonnegative exponents. -/
theorem cMatrix_rpow_rpow_of_nonneg {A : CMatrix a} (hA : A.PosSemidef)
    {r t s : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (hrt : r * t = s) :
    CFC.rpow (CFC.rpow A r) t = CFC.rpow A s := by
  rw [show CFC.rpow (CFC.rpow A r) t = CFC.rpow A (r * t) by
    exact CFC.rpow_rpow_of_exponent_nonneg A r t hr ht
      (Matrix.nonneg_iff_posSemidef.mpr hA)]
  rw [hrt]

/-- The real spectrum of a real diagonal complex matrix is its diagonal range. -/
theorem spectrum_real_diagonal_ofReal
    (d : a → ℝ) :
    spectrum ℝ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) = Set.range d := by
  ext r
  rw [← spectrum.algebraMap_mem_iff ℂ]
  change (r : ℂ) ∈ spectrum ℂ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) ↔
    r ∈ Set.range d
  rw [spectrum_diagonal]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Complex.ofReal_injective hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- Polynomial functional calculus is entrywise on real diagonal matrices. -/
theorem aeval_diagonal_ofReal
    (d : a → ℝ) (p : Polynomial ℝ) :
    aeval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) p =
      Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  let dC : a → ℂ := fun i => (d i : ℂ)
  change aeval (Matrix.diagonal dC) p =
    Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ))
  rw [show Matrix.diagonal dC = Matrix.diagonalAlgHom (R := ℝ) dC by rfl]
  rw [Polynomial.aeval_algHom (Matrix.diagonalAlgHom (R := ℝ)) dC]
  rw [Polynomial.aeval_pi]
  ext i j
  by_cases h : i = j
  · subst j
    simpa [Matrix.diagonal, dC, Polynomial.aeval_def] using
      (Polynomial.eval₂_at_apply (p := p) (algebraMap ℝ ℂ) (d i))
  · simp [Matrix.diagonal, h]

/-- Continuous functional calculus is entrywise on real diagonal matrices. -/
theorem cfc_diagonal_ofReal
    (d : a → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) =
      Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  obtain ⟨p, hp⟩ :=
    (Polynomial.exists_eval_eq_iff d (fun i => f (d i))).mpr (by
      intro i j hij
      simp [hij])
  calc
    cfc f (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) =
        cfc p.eval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) := by
      apply cfc_congr
      intro x hx
      rw [spectrum_real_diagonal_ofReal d] at hx
      rcases hx with ⟨i, rfl⟩
      exact (hp i).symm
    _ = aeval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) p := by
      exact cfc_polynomial (q := p)
        (a := (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a))
        (ha := by
          rw [isSelfAdjoint_iff, star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
          ext i j
          by_cases h : i = j
          · subst j
            simp
          · simp [Matrix.diagonal, h])
    _ = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
      rw [aeval_diagonal_ofReal d p]
      ext i j
      by_cases h : i = j
      · subst j
        simp [hp i]
      · simp [Matrix.diagonal, h]

/-- Real powers of nonnegative real diagonal matrices are entrywise powers. -/
theorem cMatrix_rpow_diagonal_ofReal
    (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) (s : ℝ) :
    CFC.rpow (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) s =
      Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) := by
  change ((Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) ^ s) =
    Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))
  have hnonneg : 0 ≤ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) :=
    Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (d i : ℂ)
        exact_mod_cast hd i))
  rw [CFC.rpow_eq_cfc_real (a := (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a))
    (y := s) hnonneg]
  exact cfc_diagonal_ofReal d (fun x => x ^ s)

/-- The real spectrum of a unitary conjugate of a real diagonal complex matrix
is still the diagonal range. -/
theorem spectrum_real_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) :
    spectrum ℝ
      ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) = Set.range d := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  have hspec :
      spectrum ℝ
        ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) =
          spectrum ℝ D := by
    exact AlgEquiv.spectrum_eq
      ((Unitary.conjStarAlgAut ℂ (CMatrix a) U).restrictScalars ℝ) D
  calc
    spectrum ℝ
      ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) =
        spectrum ℝ ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) := by
          simp [D, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
    _ = spectrum ℝ D := hspec
    _ = Set.range d := spectrum_real_diagonal_ofReal d

/-- Polynomial functional calculus is transported by a fixed unitary
conjugation on real diagonal matrices. -/
theorem aeval_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) (p : Polynomial ℝ) :
    aeval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) p =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  have hmap :
      (Unitary.conjStarAlgAut ℂ (CMatrix a) U)
        (aeval D p) =
        aeval ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) p := by
    simpa using
      (Polynomial.aeval_algHom_apply
        ((Unitary.conjStarAlgAut ℂ (CMatrix a) U).restrictScalars ℝ)
          D p).symm
  have hdiag := aeval_diagonal_ofReal d p
  calc
    aeval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) p =
        aeval ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) p := by
          simp [D, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
    _ = (Unitary.conjStarAlgAut ℂ (CMatrix a) U) (aeval D p) := hmap.symm
    _ = (Unitary.conjStarAlgAut ℂ (CMatrix a) U)
          (Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ))) := by
          rw [hdiag]
    _ = (U : CMatrix a) *
        Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
          simp [Unitary.conjStarAlgAut_apply]

/-- Continuous functional calculus, in finite-dimensional matrix form, is
entrywise on a real diagonal matrix after a fixed unitary conjugation.  The
proof uses polynomial interpolation on the finite spectrum, so it is valid for
functions such as negative real powers at zero-spectrum points. -/
theorem cfc_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) (f : ℝ → ℝ) :
    cfc f ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
  classical
  obtain ⟨p, hp⟩ :=
    (Polynomial.exists_eval_eq_iff d (fun i => f (d i))).mpr (by
      intro i j hij
      simp [hij])
  calc
    cfc f ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) =
        cfc p.eval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
          star (U : CMatrix a)) := by
      apply cfc_congr
      intro x hx
      rw [spectrum_real_unitary_conj_diagonal_ofReal U d] at hx
      rcases hx with ⟨i, rfl⟩
      exact (hp i).symm
    _ = aeval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
          star (U : CMatrix a)) p := by
      exact cfc_polynomial (q := p)
        (a := ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
          star (U : CMatrix a)))
        (ha := by
          let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
          have hDself : star D = D := by
            ext i j
            by_cases h : i = j
            · subst j
              simp [D, Matrix.diagonal]
            · have hji : j ≠ i := Ne.symm h
              simp [D, Matrix.diagonal, h, hji]
          rw [isSelfAdjoint_iff]
          change star ((U : CMatrix a) * D * star (U : CMatrix a)) =
            (U : CMatrix a) * D * star (U : CMatrix a)
          calc
            star ((U : CMatrix a) * D * star (U : CMatrix a))
                = star (star (U : CMatrix a)) * star D * star (U : CMatrix a) := by
                  simp [star_mul, Matrix.mul_assoc]
            _ = (U : CMatrix a) * D * star (U : CMatrix a) := by
                  rw [hDself]
                  simp)
    _ = (U : CMatrix a) *
        Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
      rw [aeval_unitary_conj_diagonal_ofReal U d p]
      ext i j
      simp [hp]

/-- Real powers of a unitary conjugate of a nonnegative real diagonal matrix
are computed in the same diagonalizing basis for every real exponent. -/
theorem cMatrix_rpow_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) (s : ℝ) :
    CFC.rpow ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) s =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
  change (((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) ^ s) =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) *
        star (U : CMatrix a)
  have hdiag : (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
      intro i
      change (0 : ℂ) ≤ (d i : ℂ)
      exact_mod_cast hd i)
  have hnonneg :
      0 ≤ ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) :=
    Matrix.nonneg_iff_posSemidef.mpr
      (hdiag.mul_mul_conjTranspose_same (U : CMatrix a))
  rw [CFC.rpow_eq_cfc_real
    (a := ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
      star (U : CMatrix a))) (y := s) hnonneg]
  exact cfc_unitary_conj_diagonal_ofReal U d (fun x => x ^ s)

/-- Trace of a unitary conjugate of a real diagonal matrix. -/
theorem trace_unitary_conj_diagonal_ofReal_re
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) :
    (((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)).trace).re = ∑ i, d i := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have htrace :
      (((U : CMatrix a) * D * star (U : CMatrix a)).trace) =
        D.trace := by
    calc
      (((U : CMatrix a) * D * star (U : CMatrix a)).trace)
          = (star (U : CMatrix a) * ((U : CMatrix a) * D)).trace := by
              exact Matrix.trace_mul_comm ((U : CMatrix a) * D) (star (U : CMatrix a))
      _ = D.trace := by
              rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  rw [htrace]
  simp [D, Matrix.trace_diagonal]

/-- Trace pairing of two real diagonal matrices conjugated by the same unitary. -/
theorem trace_mul_unitary_conj_diagonal_ofReal_re
    (U : Matrix.unitaryGroup a ℂ) (d e : a → ℝ) :
    ((((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) *
      ((U : CMatrix a) * (Matrix.diagonal fun i => (e i : ℂ)) *
        star (U : CMatrix a))).trace).re = ∑ i, d i * e i := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  let E : CMatrix a := Matrix.diagonal fun i => (e i : ℂ)
  have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hprod :
      ((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((U : CMatrix a) * E * star (U : CMatrix a)) =
          (U : CMatrix a) * (D * E) * star (U : CMatrix a) := by
    calc
      ((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((U : CMatrix a) * E * star (U : CMatrix a))
          = (U : CMatrix a) * D * (star (U : CMatrix a) * (U : CMatrix a)) *
              E * star (U : CMatrix a) := by noncomm_ring
      _ = (U : CMatrix a) * (D * E) * star (U : CMatrix a) := by
              rw [hUU]
              noncomm_ring
  calc
    ((((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) *
      ((U : CMatrix a) * (Matrix.diagonal fun i => (e i : ℂ)) *
        star (U : CMatrix a))).trace).re
        = (((U : CMatrix a) * (D * E) * star (U : CMatrix a)).trace).re := by
            rw [hprod]
    _ = ∑ i, d i * e i := by
            have hDE :
                D * E = Matrix.diagonal (fun i => (((d i * e i : ℝ)) : ℂ)) := by
              dsimp [D, E]
              rw [Matrix.diagonal_mul_diagonal]
              ext i j
              simp [Complex.ofReal_mul]
            rw [hDE]
            simpa using trace_unitary_conj_diagonal_ofReal_re U (fun i => d i * e i)

/-- Real powers of a PSD matrix are diagonalized by the same eigenbasis, with
entrywise real powers of the eigenvalues. -/
theorem cMatrix_rpow_eq_eigenbasis_diagonal
    {A : CMatrix a} (hA : A.PosSemidef) (s : ℝ) :
    CFC.rpow A s =
      (hA.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)) *
          star (hA.isHermitian.eigenvectorUnitary : CMatrix a) := by
  change A ^ s =
      (hA.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)) *
          star (hA.isHermitian.eigenvectorUnitary : CMatrix a)
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s)
    (ha := Matrix.nonneg_iff_posSemidef.mpr hA)]
  rw [hA.isHermitian.cfc_eq]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]

/-- Positive real powers do not enlarge the support of a PSD matrix. In the
finite-dimensional kernel-inclusion convention, `A^α` is supported by `A`
for every `0 < α`. -/
theorem cMatrix_rpow_supports_self
    {A : CMatrix a} (hA : A.PosSemidef) {α : ℝ} (hα : 0 < α) :
    Matrix.Supports (CFC.rpow A α) A := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hA.isHermitian.eigenvalues i
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact hA.eigenvalues_nonneg i
  have hdiagSupport :
      Matrix.Supports
        (Matrix.diagonal fun i => ((d i ^ α : ℝ) : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a) := by
    apply Matrix.Supports.diagonal_of_real_zero_imp_zero
    intro i hi
    simp [hi, Real.zero_rpow (ne_of_gt hα)]
  have hconj := Matrix.Supports.unitary_conj hdiagSupport U
  have hpow :
      CFC.rpow A α =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i ^ α : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    simpa [U, d] using cMatrix_rpow_eq_eigenbasis_diagonal hA α
  have hAdiag :
      A =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hA.isHermitian.spectral_theorem
  rw [hpow, hAdiag]
  exact hconj

/-- A positive semidefinite matrix with a zero diagonal entry has zero row and
column at that index. -/
theorem PosSemidef.zero_diag_zero_row_col
    {A : CMatrix a} (hA : A.PosSemidef) {i : a} (hii : A i i = 0) (j : a) :
    A i j = 0 ∧ A j i = 0 := by
  classical
  set e : a → ℂ := Pi.single i 1 with he
  have hei : e i = (1 : ℂ) := by
    rw [he, Pi.single_apply, if_pos rfl]
  have hek : ∀ k, k ≠ i → e k = 0 := fun k hk => by
    rw [he, Pi.single_apply, if_neg hk]
  have hmulVec : Matrix.mulVec A e = fun k => A k i := by
    ext k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro m _ hm
      simp [hek m hm]
    · simp [hei]
  have hform : dotProduct (star e) (Matrix.mulVec A e) = A i i := by
    rw [hmulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro k _ hk
      simp [hek k hk]
    · simp [hei]
  have hcol : Matrix.mulVec A e = 0 :=
    (hA.dotProduct_mulVec_zero_iff e).mp (by rw [hform, hii])
  have hji : A j i = 0 := by
    have h1 : (fun k => A k i) j = 0 := by
      rw [← hmulVec, hcol]
      simp
    exact h1
  refine ⟨?_, hji⟩
  have hherm : star A = A := hA.isHermitian.eq
  have hij : A i j = star (A j i) := by
    rw [show A i j = star A i j from by rw [hherm], Matrix.star_apply A i j]
  rw [hij, hji, star_zero]

/-- For a positive semidefinite matrix, a diagonal entry with zero real part is
zero as a complex number. -/
theorem PosSemidef.diag_eq_zero_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosSemidef) {i : a} (hii : (A i i).re = 0) :
    A i i = 0 := by
  have hself : star (A i i) = A i i := by
    have h := congrFun (congrFun hA.isHermitian.eq i) i
    simpa [Matrix.star_apply] using h
  apply Complex.ext
  · simpa using hii
  · have him : -(A i i).im = (A i i).im := by
      simpa using congrArg Complex.im hself
    have him_zero : (A i i).im = 0 := by
      nlinarith [him]
    simpa using him_zero

/-- A PSD matrix whose diagonal entries vanish wherever a nonnegative diagonal
support vanishes is supported by that diagonal matrix. -/
theorem Matrix.Supports.of_posSemidef_diagonal
    {M : CMatrix a} (hM : M.PosSemidef) {d : a → ℝ} (_hd : ∀ i, 0 ≤ d i)
    (hzero : ∀ i, d i = 0 → M i i = 0) :
    Matrix.Supports M
      (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a) := by
  intro v hv
  ext k
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _hj
  by_cases hdj : d j = 0
  · have hcol : M k j = 0 :=
      (PosSemidef.zero_diag_zero_row_col hM (hzero j hdj) k).2
    simp [hcol]
  · have hdjC : ((d j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdj
    have hvj : v j = 0 := by
      have hjv := congrFun hv j
      simpa [Matrix.mulVec, dotProduct, Matrix.diagonal, hdjC] using hjv
    simp [hvj]

namespace State

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- A bipartite density matrix is supported on the tensor product of the
supports of its two marginals. This is the finite-dimensional support fact
used to discharge the PSD-domain Petz trace positivity for barred mutual
information. -/
theorem matrix_supports_prod_marginals (ρ : State (Prod a b)) :
    Matrix.Supports ρ.matrix (ρ.marginalA.prod ρ.marginalB).matrix := by
  classical
  let ρA : State a := ρ.marginalA
  let ρB : State b := ρ.marginalB
  let UA : Matrix.unitaryGroup a ℂ := ρA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ := ρB.pos.isHermitian.eigenvectorUnitary
  let UAB : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      kronecker_mem_unitaryGroup UA UB⟩
  let M' : CMatrix (Prod a b) := star (UAB : CMatrix (Prod a b)) * ρ.matrix * UAB
  let dA : a → ℝ := fun i => ρA.pos.isHermitian.eigenvalues i
  let dB : b → ℝ := fun j => ρB.pos.isHermitian.eigenvalues j
  let d : Prod a b → ℝ := fun x => dA x.1 * dB x.2
  have hdA_nonneg : ∀ i, 0 ≤ dA i := by
    intro i
    exact ρA.pos.eigenvalues_nonneg i
  have hdB_nonneg : ∀ j, 0 ≤ dB j := by
    intro j
    exact ρB.pos.eigenvalues_nonneg j
  have hd_nonneg : ∀ x, 0 ≤ d x := by
    intro x
    exact mul_nonneg (hdA_nonneg x.1) (hdB_nonneg x.2)
  have hM'pos : M'.PosSemidef := by
    simpa [M', Matrix.star_eq_conjTranspose] using
      ρ.pos.conjTranspose_mul_mul_same (UAB : CMatrix (Prod a b))
  have hptB :
      partialTraceB (a := a) (b := b) M' =
        Matrix.diagonal fun i => ((dA i : ℝ) : ℂ) := by
    have hloc := partialTraceB_local_unitary_conj (a := a) (b := b) ρ.matrix UA UB
    have hdiag :
        star (UA : CMatrix a) * ρA.matrix * (UA : CMatrix a) =
          Matrix.diagonal fun i => ((dA i : ℝ) : ℂ) := by
      have hspec := ρA.pos.isHermitian.spectral_theorem
      -- The spectral theorem is `ρA = UA * D * UAᴴ`; conjugating by `UAᴴ`
      -- gives the diagonal eigenvalue matrix.
      have hρA :
          ρA.matrix =
            (UA : CMatrix a) * (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
              star (UA : CMatrix a) := by
        simpa [UA, dA, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
          using hspec
      calc
        star (UA : CMatrix a) * ρA.matrix * (UA : CMatrix a)
            = star (UA : CMatrix a) *
                ((UA : CMatrix a) * (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
                  star (UA : CMatrix a)) * (UA : CMatrix a) := by
                rw [hρA]
        _ = (star (UA : CMatrix a) * (UA : CMatrix a)) *
              (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
                (star (UA : CMatrix a) * (UA : CMatrix a)) := by
                noncomm_ring
        _ = Matrix.diagonal fun i => ((dA i : ℝ) : ℂ) := by
                rw [Unitary.coe_star_mul_self]
                simp
    simpa [M', UAB, ρA, State.marginalA_matrix] using hloc.trans hdiag
  have hptA :
      partialTraceA (a := a) (b := b) M' =
        Matrix.diagonal fun j => ((dB j : ℝ) : ℂ) := by
    have hloc := partialTraceA_local_unitary_conj (a := a) (b := b) ρ.matrix UA UB
    have hdiag :
        star (UB : CMatrix b) * ρB.matrix * (UB : CMatrix b) =
          Matrix.diagonal fun j => ((dB j : ℝ) : ℂ) := by
      have hspec := ρB.pos.isHermitian.spectral_theorem
      have hρB :
          ρB.matrix =
            (UB : CMatrix b) * (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
              star (UB : CMatrix b) := by
        simpa [UB, dB, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
          using hspec
      calc
        star (UB : CMatrix b) * ρB.matrix * (UB : CMatrix b)
            = star (UB : CMatrix b) *
                ((UB : CMatrix b) * (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
                  star (UB : CMatrix b)) * (UB : CMatrix b) := by
                rw [hρB]
        _ = (star (UB : CMatrix b) * (UB : CMatrix b)) *
              (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
                (star (UB : CMatrix b) * (UB : CMatrix b)) := by
                noncomm_ring
        _ = Matrix.diagonal fun j => ((dB j : ℝ) : ℂ) := by
                rw [Unitary.coe_star_mul_self]
                simp
    simpa [M', UAB, ρB, State.marginalB_matrix] using hloc.trans hdiag
  have hzero : ∀ x : Prod a b, d x = 0 → M' x x = 0 := by
    intro x hdx
    rcases x with ⟨i, j⟩
    have hcases : dA i = 0 ∨ dB j = 0 := by
      exact mul_eq_zero.mp hdx
    have hdiag_re_zero : (M' (i, j) (i, j)).re = 0 := by
      rcases hcases with hAi | hBj
      · have hsum_complex := congrFun (congrFun hptB i) i
        have hsum_re := congrArg Complex.re hsum_complex
        have hsum_zero : (∑ k : b, (M' (i, k) (i, k)).re) = 0 := by
          simpa [partialTraceB, Matrix.diagonal, dA, hAi] using hsum_re
        have hnonneg : ∀ k ∈ (Finset.univ : Finset b), 0 ≤ (M' (i, k) (i, k)).re := by
          intro k _
          exact posSemidef_diagonal_re_nonneg hM'pos (i, k)
        have hle :
            (M' (i, j) (i, j)).re ≤
              ∑ k : b, (M' (i, k) (i, k)).re :=
          Finset.single_le_sum hnonneg (Finset.mem_univ j)
        exact le_antisymm (by simpa [hsum_zero] using hle)
          (posSemidef_diagonal_re_nonneg hM'pos (i, j))
      · have hsum_complex := congrFun (congrFun hptA j) j
        have hsum_re := congrArg Complex.re hsum_complex
        have hsum_zero : (∑ k : a, (M' (k, j) (k, j)).re) = 0 := by
          simpa [partialTraceA, Matrix.diagonal, dB, hBj] using hsum_re
        have hnonneg : ∀ k ∈ (Finset.univ : Finset a), 0 ≤ (M' (k, j) (k, j)).re := by
          intro k _
          exact posSemidef_diagonal_re_nonneg hM'pos (k, j)
        have hle :
            (M' (i, j) (i, j)).re ≤
              ∑ k : a, (M' (k, j) (k, j)).re :=
          Finset.single_le_sum hnonneg (Finset.mem_univ i)
        exact le_antisymm (by simpa [hsum_zero] using hle)
          (posSemidef_diagonal_re_nonneg hM'pos (i, j))
    exact PosSemidef.diag_eq_zero_of_re_eq_zero hM'pos hdiag_re_zero
  have hdiagSupport :
      Matrix.Supports M'
        (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ) : CMatrix (Prod a b)) :=
    Matrix.Supports.of_posSemidef_diagonal hM'pos hd_nonneg hzero
  have hconj := Matrix.Supports.unitary_conj hdiagSupport UAB
  have hMback :
      (UAB : CMatrix (Prod a b)) * M' * star (UAB : CMatrix (Prod a b)) =
        ρ.matrix := by
    have hUU : (UAB : CMatrix (Prod a b)) * star (UAB : CMatrix (Prod a b)) = 1 := by
      exact Unitary.coe_mul_star_self UAB
    change (UAB : CMatrix (Prod a b)) *
        (star (UAB : CMatrix (Prod a b)) * ρ.matrix * (UAB : CMatrix (Prod a b))) *
          star (UAB : CMatrix (Prod a b)) = ρ.matrix
    calc
      (UAB : CMatrix (Prod a b)) *
          (star (UAB : CMatrix (Prod a b)) * ρ.matrix * (UAB : CMatrix (Prod a b))) *
            star (UAB : CMatrix (Prod a b))
          =
            ((UAB : CMatrix (Prod a b)) * star (UAB : CMatrix (Prod a b))) *
              ρ.matrix *
                ((UAB : CMatrix (Prod a b)) * star (UAB : CMatrix (Prod a b))) := by
              noncomm_ring
      _ = ρ.matrix := by
              rw [hUU]
              simp
  have hNback :
      (UAB : CMatrix (Prod a b)) *
          (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ)) *
          star (UAB : CMatrix (Prod a b)) =
        (ρA.prod ρB).matrix := by
    have hA :
        ρA.matrix =
          (UA : CMatrix a) * (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
            star (UA : CMatrix a) := by
      simpa [UA, dA, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
        using ρA.pos.isHermitian.spectral_theorem
    have hB :
        ρB.matrix =
          (UB : CMatrix b) * (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
            star (UB : CMatrix b) := by
      simpa [UB, dB, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
        using ρB.pos.isHermitian.spectral_theorem
    let DA : CMatrix a := Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)
    let DB : CMatrix b := Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)
    have hD :
        (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ) : CMatrix (Prod a b)) =
          Matrix.kronecker DA DB := by
      ext x y
      by_cases hxy : x = y
      · subst y
        simp [DA, DB, d, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.diagonal]
      · have hneq : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
          by_cases h1 : x.1 = y.1
          · right
            intro h2
            exact hxy (Prod.ext h1 h2)
          · left
            exact h1
        rcases hneq with hneqA | hneqB
        · simp [DA, DB, d, Matrix.kronecker, Matrix.kroneckerMap_apply,
            Matrix.diagonal, hxy, hneqA]
        · simp [DA, DB, d, Matrix.kronecker, Matrix.kroneckerMap_apply,
            Matrix.diagonal, hxy, hneqB]
    have hUAB :
        (UAB : CMatrix (Prod a b)) =
          Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := rfl
    have hstarUAB :
        star (UAB : CMatrix (Prod a b)) =
          Matrix.kronecker (star (UA : CMatrix a)) (star (UB : CMatrix b)) := by
      simpa [UAB, Matrix.star_eq_conjTranspose] using
        Matrix.conjTranspose_kronecker (UA : CMatrix a) (UB : CMatrix b)
    change (UAB : CMatrix (Prod a b)) *
          (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ)) *
          star (UAB : CMatrix (Prod a b)) =
        Matrix.kronecker ρA.matrix ρB.matrix
    rw [hD, hUAB, hstarUAB]
    change (Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) *
          Matrix.kronecker DA DB) *
          Matrix.kronecker (star (UA : CMatrix a)) (star (UB : CMatrix b)) =
        Matrix.kronecker ρA.matrix ρB.matrix
    rw [hA, hB]
    simp [DA, DB, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  simpa [hMback, hNback, ρA, ρB] using hconj

/-- Positive real powers of a bipartite density matrix are supported on the
tensor product of the supports of its two marginals. -/
theorem rpow_matrix_supports_prod_marginals
    (ρ : State (Prod a b)) {α : ℝ} (hα : 0 < α) :
    Matrix.Supports (CFC.rpow ρ.matrix α) (ρ.marginalA.prod ρ.marginalB).matrix :=
  (cMatrix_rpow_supports_self ρ.pos hα).trans ρ.matrix_supports_prod_marginals

end State

/-- Unitary conjugation preserves positive semidefiniteness. -/
theorem posSemidef_unitary_conj {A : CMatrix a} (hA : A.PosSemidef)
    (U : Matrix.unitaryGroup a ℂ) :
    (star (U : CMatrix a) * A * (U : CMatrix a)).PosSemidef := by
  simpa [Matrix.mul_assoc] using hA.conjTranspose_mul_mul_same (U : CMatrix a)

/-- Real powers commute with inverse unitary conjugation on PSD matrices. -/
theorem cMatrix_rpow_unitary_conj {A : CMatrix a} (hA : A.PosSemidef)
    (U : Matrix.unitaryGroup a ℂ) {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (star (U : CMatrix a) * A * (U : CMatrix a)) s =
      star (U : CMatrix a) * CFC.rpow A s * (U : CMatrix a) := by
  change (star (U : CMatrix a) * A * (U : CMatrix a)) ^ s =
    star (U : CMatrix a) * (A ^ s) * (U : CMatrix a)
  have hmap_nonneg : 0 ≤ star (U : CMatrix a) * A * (U : CMatrix a) :=
    Matrix.nonneg_iff_posSemidef.mpr (posSemidef_unitary_conj hA U)
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.rpow_eq_cfc_real (a := star (U : CMatrix a) * A * (U : CMatrix a))
    (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [Unitary.conjStarAlgAut_symm_apply] using
    (StarAlgHomClass.map_cfc
      ((Unitary.conjStarAlgAut ℂ (CMatrix a) U).symm)
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix a => star (U : CMatrix a) * A * (U : CMatrix a)
        fun_prop)).symm

/-- The `p`-power trace of a positive semidefinite matrix, `Tr A^p`, as a real
number.  The PSD hypothesis is a parameter so downstream theorem statements
carry their domain explicitly. -/
def psdTracePower (A : CMatrix a) (_hA : A.PosSemidef) (p : ℝ) : ℝ :=
  (CFC.rpow A p).trace.re

/-- PSD power traces unfold to the sum of eigenvalue powers. -/
theorem psdTracePower_eq_sum_eigenvalues_rpow
    (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    psdTracePower A hA p = ∑ i, hA.isHermitian.eigenvalues i ^ p := by
  rw [psdTracePower]
  change (Matrix.trace (A ^ p)).re = ∑ i, hA.isHermitian.eigenvalues i ^ p
  rw [CFC.rpow_eq_cfc_real (a := A) (y := p)
    (ha := Matrix.nonneg_iff_posSemidef.mpr hA)]
  rw [hA.isHermitian.cfc_eq]
  simp only [Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp_apply]

/-- PSD power traces are invariant under unitary conjugation. -/
theorem psdTracePower_unitary_conj
    (U : Matrix.unitaryGroup a ℂ) {A : CMatrix a} (hA : A.PosSemidef)
    {p : ℝ} (hp : 0 ≤ p) :
    psdTracePower (star (U : CMatrix a) * A * (U : CMatrix a))
      (posSemidef_unitary_conj hA U) p =
      psdTracePower A hA p := by
  rw [psdTracePower, psdTracePower, cMatrix_rpow_unitary_conj hA U hp]
  rw [Matrix.trace_mul_cycle]
  simp

/-- PSD power traces of nonnegative real diagonal matrices are entrywise
power sums. -/
theorem psdTracePower_diagonal_ofReal
    (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) (p : ℝ) :
    psdTracePower (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a)
      (Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (d i : ℂ)
        exact_mod_cast hd i)) p =
      ∑ i, d i ^ p := by
  rw [psdTracePower, cMatrix_rpow_diagonal_ofReal d hd p, Matrix.trace_diagonal]
  simp

/-- PSD power traces are bounded by the sum of diagonal `p`-powers in the
concave range `0 ≤ p ≤ 1`. -/
theorem psdTracePower_le_posSemidef_sum_diagonal_re_rpow
    {B : CMatrix a} (hB : B.PosSemidef) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    psdTracePower B hB p ≤ ∑ i, (B i i).re ^ p := by
  classical
  have hpoint :
      ∀ i, (∑ j,
        Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
          hB.isHermitian.eigenvalues j ^ p) ≤ (B i i).re ^ p :=
    fun i => eigenvalue_weighted_rpow_le_posSemidef_diagonal_re_rpow hB hp0 hp1 i
  have hdouble :
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ p) =
        ∑ j, hB.isHermitian.eigenvalues j ^ p := by
    calc
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ p)
          = ∑ j, ∑ i,
              Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
                hB.isHermitian.eigenvalues j ^ p := by
              rw [Finset.sum_comm]
      _ = ∑ j,
              (∑ i, Complex.normSq
                ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)) *
                hB.isHermitian.eigenvalues j ^ p := by
              simp [Finset.sum_mul]
      _ = ∑ j, hB.isHermitian.eigenvalues j ^ p := by
              simp_rw [unitary_col_normSq_sum hB.isHermitian.eigenvectorUnitary]
              simp
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  rw [← hdouble]
  exact Finset.sum_le_sum fun i _ => hpoint i

/-- Trace pairing with a PSD right factor power, expanded in that factor's
eigenbasis. -/
theorem trace_mul_cMatrix_rpow_eq_conjugate_diag_sum
    (M : CMatrix a) {N : CMatrix a} (hN : N.PosSemidef) (s : ℝ) :
    ((M * CFC.rpow N s).trace).re =
      ∑ i,
        ((star (hN.isHermitian.eigenvectorUnitary : CMatrix a) * M *
          (hN.isHermitian.eigenvectorUnitary : CMatrix a)) i i).re *
            hN.isHermitian.eigenvalues i ^ s := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hN.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
  have hpow : CFC.rpow N s = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D] using cMatrix_rpow_eq_eigenbasis_diagonal hN s
  have htrace :
      (M * CFC.rpow N s).trace =
        ((star (U : CMatrix a) * M * (U : CMatrix a)) * D).trace := by
    rw [hpow]
    calc
      (M * ((U : CMatrix a) * D * star (U : CMatrix a))).trace
          = (((M * (U : CMatrix a)) * D) * star (U : CMatrix a)).trace := by
              noncomm_ring
      _ = (star (U : CMatrix a) * ((M * (U : CMatrix a)) * D)).trace := by
              exact Matrix.trace_mul_comm (((M * (U : CMatrix a)) * D))
                (star (U : CMatrix a))
      _ = ((star (U : CMatrix a) * M * (U : CMatrix a)) * D).trace := by
              noncomm_ring
  have hdiag :
      (((star (U : CMatrix a) * M * (U : CMatrix a)) * D).trace).re =
        ∑ i,
          ((star (U : CMatrix a) * M * (U : CMatrix a)) i i).re *
            hN.isHermitian.eigenvalues i ^ s := by
    simp [D, Matrix.trace, Matrix.diagonal, Matrix.mul_apply, Complex.mul_re]
  rw [htrace, hdiag]

/-- Kernel support domination forces zero diagonal entries of the supported
matrix in zero-eigenvalue directions of the supporting PSD matrix. -/
theorem supports_conjugate_diagonal_re_eq_zero
    {M N : CMatrix a} (hN : N.PosSemidef) (hSupport : Matrix.Supports M N)
    {i : a} (hi : hN.isHermitian.eigenvalues i = 0) :
    ((star (hN.isHermitian.eigenvectorUnitary : CMatrix a) * M *
      (hN.isHermitian.eigenvectorUnitary : CMatrix a)) i i).re = 0 := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let v : a → ℂ := ⇑(hN.isHermitian.eigenvectorBasis i)
  have hNv : N.mulVec v = 0 := by
    have h := hN.isHermitian.mulVec_eigenvectorBasis i
    rw [hi] at h
    simpa [v] using h
  have hMv : M.mulVec v = 0 := hSupport v hNv
  have hMU : ∀ k, (M * (U : CMatrix a)) k i = 0 := by
    intro k
    have hk := congrFun hMv k
    simpa [v, U, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using hk
  have hentry :
      (star (U : CMatrix a) * M * (U : CMatrix a)) i i = 0 := by
    rw [Matrix.mul_assoc]
    simp [Matrix.mul_apply, hMU]
  simpa [U] using congrArg Complex.re hentry

/-- Schur-Horn/Jensen control of diagonal `q`-powers by the spectral
`q`-power trace for PSD matrices. -/
theorem posSemidef_sum_diagonal_re_rpow_le_psdTracePower
    {B : CMatrix a} (hB : B.PosSemidef) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i, (B i i).re ^ q) ≤ psdTracePower B hB q := by
  classical
  have hpoint :
      ∀ i, (B i i).re ^ q ≤
        ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
          hB.isHermitian.eigenvalues j ^ q :=
    fun i => posSemidef_diagonal_re_rpow_le_eigenvalue_weighted_rpow hB hq i
  have hsum_le :
      (∑ i, (B i i).re ^ q) ≤
        ∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ q :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hdouble :
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ q) =
        ∑ j, hB.isHermitian.eigenvalues j ^ q := by
    calc
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ q)
          = ∑ j, ∑ i,
              Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
                hB.isHermitian.eigenvalues j ^ q := by
              rw [Finset.sum_comm]
      _ = ∑ j,
              (∑ i, Complex.normSq
                ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)) *
                hB.isHermitian.eigenvalues j ^ q := by
              simp [Finset.sum_mul]
      _ = ∑ j, hB.isHermitian.eigenvalues j ^ q := by
              simp_rw [unitary_col_normSq_sum hB.isHermitian.eigenvectorUnitary]
              simp
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  exact hsum_le.trans_eq hdouble

@[simp]
theorem psdTracePower_eq (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    psdTracePower A hA p = (CFC.rpow A p).trace.re :=
  rfl

/-- PSD power traces are nonnegative. -/
theorem psdTracePower_nonneg (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    0 ≤ psdTracePower A hA p :=
  (Matrix.PosSemidef.trace_nonneg (cMatrix_rpow_posSemidef (A := A) (s := p) hA)).1

/-- A nonzero PSD matrix has strictly positive `p`-power trace. -/
theorem psdTracePower_pos_of_ne_zero
    (A : CMatrix a) (hA : A.PosSemidef) {p : ℝ}
    (hAne : A ≠ 0) :
    0 < psdTracePower A hA p := by
  classical
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  have hexists : ∃ i, hA.isHermitian.eigenvalues i ≠ 0 := by
    by_contra hno
    have hzero : hA.isHermitian.eigenvalues = 0 := by
      funext i
      exact not_not.mp (by
        intro hi
        exact hno ⟨i, hi⟩)
    exact hAne ((hA.isHermitian.eigenvalues_eq_zero_iff).mp hzero)
  rcases hexists with ⟨i, hi⟩
  exact Finset.sum_pos' (fun j _ =>
      Real.rpow_nonneg (hA.eigenvalues_nonneg j) p)
    ⟨i, Finset.mem_univ i,
      Real.rpow_pos_of_pos (lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)) p⟩

/-- If a nonzero PSD matrix is supported on a PSD matrix, then pairing it
with any real power of the supporting matrix has strictly positive trace. -/
theorem trace_mul_cMatrix_rpow_pos_of_support
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hMne : M ≠ 0) (hSupport : Matrix.Supports M N)
    (s : ℝ) :
    0 < ((M * CFC.rpow N s).trace).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  let x : a → ℝ := fun i => (M' i i).re
  let w : a → ℝ := fun i => hN.isHermitian.eigenvalues i
  have hM' : M'.PosSemidef := by
    simpa [M'] using posSemidef_unitary_conj hM U
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    exact posSemidef_diagonal_re_nonneg hM' i
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    exact hN.eigenvalues_nonneg i
  have hsumx_pos : 0 < ∑ i, x i := by
    have htraceM_pos : 0 < M.trace.re := by
      have hpow := psdTracePower_pos_of_ne_zero M hM (p := 1) hMne
      simpa [psdTracePower, CFC.rpow_one M
        (ha := Matrix.nonneg_iff_posSemidef.mpr hM)] using hpow
    have htraceM' : M'.trace = M.trace := by
      calc
        M'.trace = (((star (U : CMatrix a) * M) * (U : CMatrix a))).trace := by
          simp [M', Matrix.mul_assoc]
        _ = (((U : CMatrix a) * (star (U : CMatrix a) * M))).trace := by
          exact Matrix.trace_mul_comm (star (U : CMatrix a) * M) (U : CMatrix a)
        _ = (((U : CMatrix a) * star (U : CMatrix a)) * M).trace := by
          rw [Matrix.mul_assoc]
        _ = M.trace := by
          have hUU : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
            exact Unitary.coe_mul_star_self U
          rw [hUU, Matrix.one_mul]
    have hsumx : ∑ i, x i = M.trace.re := by
      calc
        ∑ i, x i = M'.trace.re := by
          simp [x, Matrix.trace]
        _ = M.trace.re := by
          rw [htraceM']
    rw [hsumx]
    exact htraceM_pos
  have hexists : ∃ i, 0 < x i := by
    by_contra hno
    have hx_zero : ∀ i, x i = 0 := by
      intro i
      exact le_antisymm (not_lt.mp (by
        intro hxi
        exact hno ⟨i, hxi⟩)) (hx_nonneg i)
    have hsum_zero : ∑ i, x i = 0 := by
      simp [hx_zero]
    linarith
  rcases hexists with ⟨i, hxi_pos⟩
  have hwi_ne : w i ≠ 0 := by
    intro hwi
    have hxi_zero :
        x i = 0 := by
      simpa [x, w, M', U] using
        supports_conjugate_diagonal_re_eq_zero (M := M) (N := N) hN hSupport
          (i := i) hwi
    linarith
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi_ne)
  have hterm_pos : 0 < x i * w i ^ s :=
    mul_pos hxi_pos (Real.rpow_pos_of_pos hwi_pos s)
  have hsum_pos : 0 < ∑ i, x i * w i ^ s := by
    exact Finset.sum_pos'
      (fun j _ => mul_nonneg (hx_nonneg j)
        (Real.rpow_nonneg (hw_nonneg j) s))
      ⟨i, Finset.mem_univ i, hterm_pos⟩
  have htrace :
      ((M * CFC.rpow N s).trace).re =
        ∑ i, x i * w i ^ s := by
    simpa [x, w, M', U] using
      trace_mul_cMatrix_rpow_eq_conjugate_diag_sum (M := M) (N := N) hN s
  rw [htrace]
  exact hsum_pos

/-- The first power trace is the ordinary trace. -/
@[simp]
theorem psdTracePower_one (A : CMatrix a) (hA : A.PosSemidef) :
    psdTracePower A hA (1 : ℝ) = A.trace.re := by
  simp [psdTracePower, CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)]

/-- The spectral Schatten `p`-norm expression `(Tr A^p)^(1/p)` for PSD
matrices.  This is the quantity that the Holder variational theorem identifies
with an optimization over normalized positive side states. -/
def psdSchattenPNorm (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) : ℝ :=
  Real.rpow (psdTracePower A hA p) (1 / p)

@[simp]
theorem psdSchattenPNorm_eq (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    psdSchattenPNorm A hA p =
      Real.rpow ((CFC.rpow A p).trace.re) (1 / p) :=
  rfl

/-- PSD Schatten `p`-norm expressions are nonnegative. -/
theorem psdSchattenPNorm_nonneg (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    0 ≤ psdSchattenPNorm A hA p :=
  Real.rpow_nonneg (psdTracePower_nonneg A hA p) _

/-- At `p = 1`, the PSD Schatten expression is the real trace. -/
@[simp]
theorem psdSchattenPNorm_one (A : CMatrix a) (hA : A.PosSemidef) :
    psdSchattenPNorm A hA (1 : ℝ) = A.trace.re := by
  rw [psdSchattenPNorm, psdTracePower_one]
  simp [Real.rpow_one]

/-- Finite scalar reverse Holder inequality in the normalized-weight form used
by the PSD reverse-Holder proof. -/
theorem real_sum_rpow_one_div_le_reverse_holder {ι : Type*} [Fintype ι]
    {x w : ι → ℝ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hx : ∀ i, 0 ≤ x i)
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hsupp : ∀ i, w i = 0 → x i = 0) :
    (∑ i, x i ^ p) ^ (1 / p) ≤
      ∑ i, x i * w i ^ (1 - 1 / p) := by
  classical
  let z : ι → ℝ := fun i => if h : w i = 0 then 0 else x i / (w i ^ (1 / p))
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    dsimp [z]
    split_ifs with _h
    · exact le_rfl
    · exact div_nonneg (hx i) (Real.rpow_nonneg (hw i) _)
  have hz_mem : ∀ i ∈ (Finset.univ : Finset ι), z i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact hz_nonneg i
  have hconc := (Real.concaveOn_rpow (p := p) (le_of_lt hp0) (le_of_lt hp1)).le_map_sum
      (t := (Finset.univ : Finset ι)) (w := w) (p := z)
      (by intro i _; exact hw i)
      (by simpa using hwsum)
      hz_mem
  have hzsum :
      (∑ i ∈ (Finset.univ : Finset ι), w i • z i) =
        ∑ i, x i * w i ^ (1 - 1 / p) := by
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hw0 : w i = 0
    · simp [z, hw0, hsupp i hw0]
    · have hwpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hw0)
      calc
        w i * z i
            = w i * (x i / w i ^ (1 / p)) := by simp [z, hw0]
        _ = x i * (w i / w i ^ (1 / p)) := by ring
        _ = x i * (w i ^ (1 : ℝ) / w i ^ (1 / p)) := by rw [Real.rpow_one]
        _ = x i * (w i ^ (1 - 1 / p)) := by
          rw [← Real.rpow_sub hwpos]
  have hpower_sum :
      (∑ i ∈ (Finset.univ : Finset ι), w i • (z i ^ p)) =
        ∑ i, x i ^ p := by
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hw0 : w i = 0
    · simp [z, hw0, hsupp i hw0, Real.zero_rpow (ne_of_gt hp0)]
    · have hwpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hw0)
      have hxnonneg := hx i
      have hwpow_nonneg : 0 ≤ w i ^ (1 / p) := Real.rpow_nonneg (hw i) _
      calc
        w i * z i ^ p
            = w i * (x i / w i ^ (1 / p)) ^ p := by simp [z, hw0]
        _ = w i * (x i ^ p / (w i ^ (1 / p)) ^ p) := by
              rw [Real.div_rpow hxnonneg hwpow_nonneg]
        _ = w i * (x i ^ p / w i) := by
              rw [← Real.rpow_mul hwpos.le]
              have hp_ne : p ≠ 0 := ne_of_gt hp0
              rw [one_div_mul_cancel hp_ne, Real.rpow_one]
        _ = x i ^ p := by
              field_simp [hw0]
  have hpow_le :
      ∑ i, x i ^ p ≤
        (∑ i, x i * w i ^ (1 - 1 / p)) ^ p := by
    rw [hpower_sum, hzsum] at hconc
    simpa using hconc
  have hleft_nonneg : 0 ≤ ∑ i, x i ^ p := by
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hx i) p
  have hright_nonneg : 0 ≤ ∑ i, x i * w i ^ (1 - 1 / p) := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hx i) (Real.rpow_nonneg (hw i) _)
  have hleftnorm_nonneg : 0 ≤ (∑ i, x i ^ p) ^ (1 / p) :=
    Real.rpow_nonneg hleft_nonneg _
  have hpow_goal :
      ((∑ i, x i ^ p) ^ (1 / p)) ^ p ≤
        (∑ i, x i * w i ^ (1 - 1 / p)) ^ p := by
    rw [one_div]
    rw [Real.rpow_inv_rpow hleft_nonneg (ne_of_gt hp0)]
    simpa [one_div] using hpow_le
  exact (Real.rpow_le_rpow_iff hleftnorm_nonneg hright_nonneg hp0).mp hpow_goal

/-- The normalized reverse-Holder candidate `wᵢ = xᵢ^p / ∑ⱼ xⱼ^p`
attains the scalar lower bound.  The proof treats `xᵢ = 0` explicitly, which
is essential because the reverse exponent `1 - 1 / p` is negative when
`0 < p < 1`. -/
theorem real_sum_reverse_holder_optimizer_value {ι : Type*} [Fintype ι]
    {x : ι → ℝ} {p : ℝ}
    (hp0 : 0 < p) (hx : ∀ i, 0 ≤ x i)
    (hSpos : 0 < ∑ i, x i ^ p) :
    (∑ i, x i * (x i ^ p / (∑ j, x j ^ p)) ^ (1 - 1 / p)) =
      (∑ i, x i ^ p) ^ (1 / p) := by
  classical
  let S : ℝ := ∑ i, x i ^ p
  let r : ℝ := 1 - 1 / p
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hSpos' : 0 < S := by simpa [S] using hSpos
  have hr_mul : p * r = p - 1 := by
    dsimp [r]
    field_simp [hp_ne]
  have hpow_mul : 1 + p * r = p := by
    rw [hr_mul]
    ring
  have hterm : ∀ i, x i * (x i ^ p / S) ^ r = x i ^ p / S ^ r := by
    intro i
    have hxpow_nonneg : 0 ≤ x i ^ p := Real.rpow_nonneg (hx i) p
    calc
      x i * (x i ^ p / S) ^ r
          = x i * ((x i ^ p) ^ r / S ^ r) := by
              rw [Real.div_rpow hxpow_nonneg hSpos'.le r]
      _ = x i * (x i ^ (p * r) / S ^ r) := by
              rw [← Real.rpow_mul (hx i)]
      _ = (x i * x i ^ (p * r)) / S ^ r := by ring
      _ = x i ^ p / S ^ r := by
              congr 1
              by_cases hzero : x i = 0
              · simp [hzero, Real.zero_rpow hp_ne]
              · have hxpos : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hzero)
                calc
                  x i * x i ^ (p * r)
                      = x i ^ (1 : ℝ) * x i ^ (p * r) := by rw [Real.rpow_one]
                  _ = x i ^ (1 + p * r) := by
                        rw [← Real.rpow_add hxpos]
                  _ = x i ^ p := by rw [hpow_mul]
  calc
    (∑ i, x i * (x i ^ p / (∑ j, x j ^ p)) ^ (1 - 1 / p))
        = ∑ i, x i ^ p / S ^ r := by
            apply Finset.sum_congr rfl
            intro i _
            simpa [S, r] using hterm i
    _ = S / S ^ r := by
            simp [S, Finset.sum_div]
    _ = S ^ (1 / p) := by
            calc
              S / S ^ r = S ^ (1 : ℝ) / S ^ r := by rw [Real.rpow_one]
              _ = S ^ (1 - r) := by rw [Real.rpow_sub hSpos' 1 r]
              _ = S ^ (1 / p) := by
                    congr 1
                    dsimp [r]
                    ring

/-- Noncommutative Holder upper bound for PSD trace pairings, expressed with
PSD spectral Schatten expressions.  If the right factor has normalized
`q`-power trace, the real trace pairing is bounded by the left factor's
Schatten `p` expression. -/
theorem posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
    {M B : CMatrix a} (hM : M.PosSemidef) (hB : B.PosSemidef)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 1 ≤ q)
    (hBq : psdTracePower B hB q ≤ 1) :
    ((M * B).trace).re ≤ psdSchattenPNorm M hM p := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let B' : CMatrix a := star (U : CMatrix a) * B * (U : CMatrix a)
  have hB' : B'.PosSemidef := by
    simpa [B'] using posSemidef_unitary_conj hB U
  have htrace :
      ((M * B).trace).re =
        ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * (B' i i).re := by
    simpa [U, B'] using
      posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum (M := M) (B := B) hM
  have hholder :
      ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * (B' i i).re ≤
        (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) *
          (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := (Finset.univ : Finset a))
      (f := fun i => hM.isHermitian.eigenvalues i)
      (g := fun i => (B' i i).re)
      hpq
      (fun i _ => hM.eigenvalues_nonneg i)
      (fun i _ => posSemidef_diagonal_re_nonneg hB' i)
  have hMnorm :
      (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) =
        psdSchattenPNorm M hM p := by
    rw [psdSchattenPNorm, psdTracePower_eq_sum_eigenvalues_rpow]
    simp
  have hBpower_conj :
      psdTracePower B' hB' q = psdTracePower B hB q := by
    dsimp [B']
    exact psdTracePower_unitary_conj U hB (p := q) (le_of_lt hpq.symm.pos)
  have hBdiag_sum_le_one :
      ∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q ≤ 1 := by
    have hdiag_le := posSemidef_sum_diagonal_re_rpow_le_psdTracePower hB' hq
    have hpower_le : psdTracePower B' hB' q ≤ 1 := by
      rw [hBpower_conj]
      exact hBq
    have hdiag_le' :
        ∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q ≤ psdTracePower B' hB' q := by
      simpa using hdiag_le
    exact hdiag_le'.trans hpower_le
  have hBdiag_sum_nonneg :
      0 ≤ ∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q := by
    exact Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (posSemidef_diagonal_re_nonneg hB' i) q
  have hBnorm_le :
      (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) ≤ 1 :=
    Real.rpow_le_one hBdiag_sum_nonneg hBdiag_sum_le_one hpq.symm.one_div_nonneg
  calc
    ((M * B).trace).re =
        ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * (B' i i).re := htrace
    _ ≤ (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) *
          (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) := hholder
    _ = psdSchattenPNorm M hM p *
          (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) := by
            rw [hMnorm]
    _ ≤ psdSchattenPNorm M hM p * 1 :=
          mul_le_mul_of_nonneg_left hBnorm_le (psdSchattenPNorm_nonneg M hM p)
    _ = psdSchattenPNorm M hM p := by rw [mul_one]

/-- Source-shaped PSD trace Holder upper bound for the positive-power side of
the variational formula.  The exponent is written as `r = 1 / q`, where `p` and
`q` are Holder conjugates; equivalently `r = 1 - 1 / p`. -/
theorem psd_trace_rpow_holder_variational_upper
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hNtr : N.trace.re = 1)
    {p q r : ℝ} (hpq : p.HolderConjugate q) (hr : r = 1 / q) :
    ((M * CFC.rpow N r).trace).re ≤ psdSchattenPNorm M hM p := by
  let B : CMatrix a := CFC.rpow N r
  have hB : B.PosSemidef := cMatrix_rpow_posSemidef (A := N) (s := r) hN
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact hpq.symm.one_div_nonneg
  have hq_nonneg : 0 ≤ q := le_of_lt hpq.symm.pos
  have hrq : r * q = 1 := by
    rw [hr]
    exact one_div_mul_cancel hpq.symm.ne_zero
  have hpow : CFC.rpow B q = N := by
    dsimp [B]
    change (N ^ r) ^ q = N
    rw [CFC.rpow_rpow_of_exponent_nonneg N r q hr_nonneg hq_nonneg
      (Matrix.nonneg_iff_posSemidef.mpr hN)]
    rw [hrq]
    simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
  have hBq_eq : psdTracePower B hB q = 1 := by
    rw [psdTracePower, hpow, hNtr]
  have hBq : psdTracePower B hB q ≤ 1 := le_of_eq hBq_eq
  simpa [B] using
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (M := M) (B := B) hM hB hpq (le_of_lt hpq.symm.lt) hBq

/-- Source-shaped PSD trace reverse-Holder lower bound for the
`0 < p < 1` side of Tomamichel's Schatten variational formula.  The
support hypothesis is the finite-dimensional kernel-inclusion form of
`M << N`, and `r = 1 - 1 / p` is negative in this range. -/
theorem psd_trace_rpow_reverse_holder_variational
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hNtr : N.trace.re = 1)
    (hSupport : Matrix.Supports M N)
    {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr : r = 1 - 1 / p) :
    psdSchattenPNorm M hM p ≤ ((M * CFC.rpow N r).trace).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  let x : a → ℝ := fun i => (M' i i).re
  let w : a → ℝ := fun i => hN.isHermitian.eigenvalues i
  have hM' : M'.PosSemidef := by
    simpa [M'] using posSemidef_unitary_conj hM U
  have hx : ∀ i, 0 ≤ x i := by
    intro i
    exact posSemidef_diagonal_re_nonneg hM' i
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact hN.eigenvalues_nonneg i
  have hwsum : ∑ i, w i = 1 := by
    have htrace := congrArg Complex.re hN.isHermitian.trace_eq_sum_eigenvalues
    simpa [w, hNtr] using htrace.symm
  have hsupp : ∀ i, w i = 0 → x i = 0 := by
    intro i hi
    simpa [x, w, M', U] using
      supports_conjugate_diagonal_re_eq_zero (M := M) (N := N) hN hSupport
        (i := i) hi
  have hscalar :
      (∑ i, x i ^ p) ^ (1 / p) ≤
        ∑ i, x i * w i ^ (1 - 1 / p) :=
    real_sum_rpow_one_div_le_reverse_holder hp0 hp1 hx hw hwsum hsupp
  have htrace :
      ((M * CFC.rpow N r).trace).re =
        ∑ i, x i * w i ^ r := by
    simpa [x, w, M', U] using
      trace_mul_cMatrix_rpow_eq_conjugate_diag_sum (N := N) M hN r
  have hscalar_r :
      (∑ i, x i ^ p) ^ (1 / p) ≤
        ∑ i, x i * w i ^ r := by
    simpa [hr, x, w] using hscalar
  have htracePower_conj :
      psdTracePower M' hM' p = psdTracePower M hM p := by
    simpa [M'] using psdTracePower_unitary_conj U hM (p := p) (le_of_lt hp0)
  have hdiag_bound : psdTracePower M' hM' p ≤ ∑ i, x i ^ p := by
    simpa [x] using
      psdTracePower_le_posSemidef_sum_diagonal_re_rpow hM'
        (p := p) (le_of_lt hp0) (le_of_lt hp1)
  have hnorm_bound :
      psdSchattenPNorm M hM p ≤ (∑ i, x i ^ p) ^ (1 / p) := by
    rw [psdSchattenPNorm]
    rw [← htracePower_conj]
    exact Real.rpow_le_rpow
      (psdTracePower_nonneg M' hM' p) hdiag_bound (one_div_nonneg.mpr (le_of_lt hp0))
  calc
    psdSchattenPNorm M hM p ≤ (∑ i, x i ^ p) ^ (1 / p) := hnorm_bound
    _ ≤ ∑ i, x i * w i ^ r := hscalar_r
    _ = ((M * CFC.rpow N r).trace).re := htrace.symm

/-- Reverse-Holder normalized PSD side-state objective values for a fixed
PSD matrix and exponent parameter. -/
def psdTraceReverseHolderStateValueSet (M : CMatrix a) (p : ℝ) : Set ℝ :=
  {x | ∃ N : CMatrix a, ∃ _hN : N.PosSemidef,
    N.trace.re = 1 ∧ Matrix.Supports M N ∧
      x = ((M * CFC.rpow N (1 - 1 / p)).trace).re}

/-- Every normalized PSD side-state value in the reverse-Holder optimization
is bounded below by the PSD Schatten `p` expression. -/
theorem psdTraceReverseHolderStateValueSet_lowerBound
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    psdSchattenPNorm M hM p ∈
      lowerBounds (psdTraceReverseHolderStateValueSet M p) := by
  intro x hx
  rcases hx with ⟨N, hN, hNtr, hSupport, rfl⟩
  exact psd_trace_rpow_reverse_holder_variational
    (M := M) (N := N) hM hN hNtr hSupport hp0 hp1 rfl

/-- Infimum lower-bound form of the reverse-Holder variational inequality. -/
theorem psdTraceReverseHolderStateValueSet_le_sInf
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hne : (psdTraceReverseHolderStateValueSet M p).Nonempty) :
    psdSchattenPNorm M hM p ≤ sInf (psdTraceReverseHolderStateValueSet M p) :=
  le_csInf hne (psdTraceReverseHolderStateValueSet_lowerBound hM hp0 hp1)

/-- A side-state value attaining the Schatten expression is a genuine
minimizer of the reverse-Holder normalized PSD optimization.  This separates
the reusable support/negative-power lower bound from the later construction of
an optimizer in the full conditional-Renyi route. -/
theorem psdTraceReverseHolderStateValueSet_isLeast_of_mem
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hmem : psdSchattenPNorm M hM p ∈ psdTraceReverseHolderStateValueSet M p) :
    IsLeast (psdTraceReverseHolderStateValueSet M p) (psdSchattenPNorm M hM p) :=
  ⟨hmem, psdTraceReverseHolderStateValueSet_lowerBound hM hp0 hp1⟩

/-- The normalized PSD optimizer for the reverse-Holder side when
`Tr M^p > 0`, written in an eigenbasis of `M`. -/
def psdTraceReverseHolderOptimizer
    (M : CMatrix a) (hM : M.PosSemidef) (p : ℝ) : CMatrix a :=
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let S : ℝ := psdTracePower M hM p
  (U : CMatrix a) *
    Matrix.diagonal
      (fun i => (((hM.isHermitian.eigenvalues i ^ p) / S : ℝ) : ℂ)) *
    star (U : CMatrix a)

/-- The reverse-Holder optimizer attains the Schatten expression whenever
`Tr M^p` is strictly positive. -/
theorem psdTraceReverseHolderOptimizer_mem
    {M : CMatrix a} (hM : M.PosSemidef)
    {p : ℝ} (hp0 : 0 < p)
    (hSpos : 0 < psdTracePower M hM p) :
    psdSchattenPNorm M hM p ∈ psdTraceReverseHolderStateValueSet M p := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hM.isHermitian.eigenvalues i
  let S : ℝ := psdTracePower M hM p
  let n : a → ℝ := fun i => d i ^ p / S
  let N : CMatrix a := (U : CMatrix a) *
    Matrix.diagonal (fun i => ((n i : ℝ) : ℂ)) * star (U : CMatrix a)
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact hM.eigenvalues_nonneg i
  have hSsum : S = ∑ i, d i ^ p := by
    simpa [S, d] using psdTracePower_eq_sum_eigenvalues_rpow M hM p
  have hSposS : 0 < S := by
    simpa [S] using hSpos
  have hSpos_sum : 0 < ∑ i, d i ^ p := by
    simpa [hSsum] using hSposS
  have hn_nonneg : ∀ i, 0 ≤ n i := by
    intro i
    exact div_nonneg (Real.rpow_nonneg (hd i) p) (le_of_lt hSpos)
  have hN : N.PosSemidef := by
    have hdiag : (Matrix.diagonal fun i => ((n i : ℝ) : ℂ) : CMatrix a).PosSemidef :=
      Matrix.PosSemidef.diagonal (d := fun i => ((n i : ℝ) : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ ((n i : ℝ) : ℂ)
        exact_mod_cast hn_nonneg i)
    simpa [N] using hdiag.mul_mul_conjTranspose_same (U : CMatrix a)
  have hNtr : N.trace.re = 1 := by
    calc
      N.trace.re = ∑ i, n i := by
        simpa [N] using trace_unitary_conj_diagonal_ofReal_re U n
      _ = (∑ i, d i ^ p) / S := by
        simp [n, Finset.sum_div]
      _ = 1 := by
        rw [← hSsum]
        exact div_self (ne_of_gt hSpos)
  have hMdiag :
      M = (U : CMatrix a) * (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hM.isHermitian.spectral_theorem
  have hSupport : Matrix.Supports M N := by
    have hdiagSupport :
        Matrix.Supports
          (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => ((n i : ℝ) : ℂ) : CMatrix a) := by
      apply Matrix.Supports.diagonal_of_real_zero_imp_zero
      intro i hi
      have hnum : d i ^ p = 0 := by
        have hS_ne : S ≠ 0 := ne_of_gt hSpos
        exact (div_eq_zero_iff.mp hi).resolve_right hS_ne
      exact (Real.rpow_eq_zero (hd i) (ne_of_gt hp0)).mp hnum
    have hconj := Matrix.Supports.unitary_conj hdiagSupport U
    simpa [N, hMdiag] using hconj
  let r : ℝ := 1 - 1 / p
  have hNpow :
      CFC.rpow N r =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((n i ^ r : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    simpa [N] using cMatrix_rpow_unitary_conj_diagonal_ofReal U n hn_nonneg r
  have htrace :
      ((M * CFC.rpow N r).trace).re = ∑ i, d i * n i ^ r := by
    rw [hMdiag, hNpow]
    simpa using trace_mul_unitary_conj_diagonal_ofReal_re U d (fun i => n i ^ r)
  have hscalar :
      ∑ i, d i * n i ^ r = (∑ i, d i ^ p) ^ (1 / p) := by
    have hn_eq : ∀ i, n i = d i ^ p / (∑ j, d j ^ p) := by
      intro i
      simp [n, hSsum]
    calc
      ∑ i, d i * n i ^ r =
          ∑ i, d i * (d i ^ p / (∑ j, d j ^ p)) ^ r := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hn_eq i]
      _ = (∑ i, d i ^ p) ^ (1 / p) := by
            simpa [r] using
              real_sum_reverse_holder_optimizer_value (ι := a) (x := d) hp0 hd hSpos_sum
  have hnorm :
      psdSchattenPNorm M hM p = (∑ i, d i ^ p) ^ (1 / p) := by
    rw [psdSchattenPNorm, psdTracePower_eq_sum_eigenvalues_rpow]
    simp [d]
  refine ⟨N, hN, hNtr, hSupport, ?_⟩
  calc
    psdSchattenPNorm M hM p = (∑ i, d i ^ p) ^ (1 / p) := hnorm
    _ = ∑ i, d i * n i ^ r := hscalar.symm
    _ = ((M * CFC.rpow N (1 - 1 / p)).trace).re := by
      simpa [r] using htrace.symm

/-- Exact reverse-Holder variational formula as a minimum, in the nonzero
power-trace case. -/
theorem psdTraceReverseHolderStateValueSet_isLeast_of_tracePower_pos
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hSpos : 0 < psdTracePower M hM p) :
    IsLeast (psdTraceReverseHolderStateValueSet M p) (psdSchattenPNorm M hM p) :=
  psdTraceReverseHolderStateValueSet_isLeast_of_mem hM hp0 hp1
    (psdTraceReverseHolderOptimizer_mem hM hp0 hSpos)

/-- Exact `sInf` form of the reverse-Holder variational formula in the nonzero
power-trace case. -/
theorem psdTraceReverseHolderStateValueSet_sInf_eq_of_tracePower_pos
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hSpos : 0 < psdTracePower M hM p) :
    sInf (psdTraceReverseHolderStateValueSet M p) = psdSchattenPNorm M hM p :=
  (psdTraceReverseHolderStateValueSet_isLeast_of_tracePower_pos
    hM hp0 hp1 hSpos).csInf_eq

/-- Exact reverse-Holder variational formula as a minimum for nonzero PSD
matrices. -/
theorem psdTraceReverseHolderStateValueSet_isLeast_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hMne : M ≠ 0) :
    IsLeast (psdTraceReverseHolderStateValueSet M p) (psdSchattenPNorm M hM p) :=
  psdTraceReverseHolderStateValueSet_isLeast_of_tracePower_pos hM hp0 hp1
    (psdTracePower_pos_of_ne_zero M hM hMne)

/-- Exact `sInf` form of the reverse-Holder variational formula for nonzero
PSD matrices. -/
theorem psdTraceReverseHolderStateValueSet_sInf_eq_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hMne : M ≠ 0) :
    sInf (psdTraceReverseHolderStateValueSet M p) = psdSchattenPNorm M hM p :=
  (psdTraceReverseHolderStateValueSet_isLeast_of_ne_zero
    hM hp0 hp1 hMne).csInf_eq

/-- PSD `q`-unit-ball trace values paired with a fixed PSD matrix. -/
def psdTraceHolderUnitBallValueSet (M : CMatrix a) (q : ℝ) : Set ℝ :=
  {x | ∃ B : CMatrix a, ∃ hB : B.PosSemidef,
    psdTracePower B hB q ≤ 1 ∧ x = ((M * B).trace).re}

/-- Finite-dimensional PSD trace Holder variational formula over the PSD
`q`-unit ball.  This is the matrix core behind the `p ≥ 1` side of
Tomamichel's Schatten Holder variational lemma. -/
theorem psdTraceHolderUnitBall_isGreatest
    {M : CMatrix a} (hM : M.PosSemidef) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    IsGreatest (psdTraceHolderUnitBallValueSet M q) (psdSchattenPNorm M hM p) := by
  classical
  constructor
  · let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
    let f : a → ℝ≥0 := fun i => ⟨hM.isHermitian.eigenvalues i, hM.eigenvalues_nonneg i⟩
    rcases (NNReal.isGreatest_Lp (s := (Finset.univ : Finset a)) f hpq).1 with
      ⟨g, hg, hval⟩
    let d : a → ℝ := fun i => (g i : ℝ)
    let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
    have hd : ∀ i, 0 ≤ d i := fun i => (g i).2
    have hD : D.PosSemidef := by
      dsimp [D, d]
      exact Matrix.PosSemidef.diagonal (d := fun i => ((g i : ℝ) : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ ((g i : ℝ) : ℂ)
        exact_mod_cast (g i).2)
    let B : CMatrix a := (U : CMatrix a) * D * star (U : CMatrix a)
    have hB : B.PosSemidef := by
      simpa [B] using hD.mul_mul_conjTranspose_same (U : CMatrix a)
    have hUBU : star (U : CMatrix a) * B * (U : CMatrix a) = D := by
      have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
        Unitary.coe_star_mul_self U
      calc
        star (U : CMatrix a) * B * (U : CMatrix a)
            = (star (U : CMatrix a) * (U : CMatrix a)) * D *
                (star (U : CMatrix a) * (U : CMatrix a)) := by
                dsimp [B]
                noncomm_ring
        _ = D := by simp [hUU]
    have hBpower_eq_Dpower :
        psdTracePower B hB q = psdTracePower D hD q := by
      rw [psdTracePower, psdTracePower]
      have htrace :
          (CFC.rpow D q).trace.re = (CFC.rpow B q).trace.re := by
        rw [← hUBU]
        rw [cMatrix_rpow_unitary_conj hB U (le_of_lt hpq.symm.pos)]
        rw [Matrix.trace_mul_cycle]
        simp
      exact htrace.symm
    have hDpower :
        psdTracePower D hD q = ∑ i, d i ^ q := by
      dsimp [D]
      simpa [d] using psdTracePower_diagonal_ofReal (a := a) d hd q
    have hgNN : ∑ i ∈ (Finset.univ : Finset a), g i ^ q ≤ 1 := by
      simpa using hg
    have hgR : (∑ i ∈ (Finset.univ : Finset a), d i ^ q) ≤ 1 := by
      have hgR0 :
          ((∑ i ∈ (Finset.univ : Finset a), g i ^ q : ℝ≥0) : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast hgNN
      simpa [d] using hgR0
    have hBq : psdTracePower B hB q ≤ 1 := by
      rw [hBpower_eq_Dpower, hDpower]
      simpa using hgR
    have htraceB :
        ((M * B).trace).re = ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * d i := by
      rw [posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
        (M := M) (B := B) hM]
      change (∑ i, hM.isHermitian.eigenvalues i *
          ((star (U : CMatrix a) * B * (U : CMatrix a)) i i).re) =
        ∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i
      rw [hUBU]
      simp [D]
    have hvalR :
        (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i) =
          psdSchattenPNorm M hM p := by
      have hval_coe := congrArg (fun x : ℝ≥0 => (x : ℝ)) hval
      have hvalR0 :
          (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i) =
            (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) := by
        simpa [f, d] using hval_coe
      calc
        (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i)
            = (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^
                (1 / p) := hvalR0
        _ = psdSchattenPNorm M hM p := by
            rw [psdSchattenPNorm, psdTracePower_eq_sum_eigenvalues_rpow]
            simp
    refine ⟨B, hB, hBq, ?_⟩
    rw [htraceB, hvalR]
  · intro x hx
    rcases hx with ⟨B, hB, hBq, rfl⟩
    exact posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (M := M) (B := B) hM hB hpq (le_of_lt hpq.symm.lt) hBq

/-- Supremum form of the PSD trace Holder variational formula. -/
theorem psdTraceHolderUnitBall_sSup_eq
    {M : CMatrix a} (hM : M.PosSemidef) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    sSup (psdTraceHolderUnitBallValueSet M q) = psdSchattenPNorm M hM p :=
  (psdTraceHolderUnitBall_isGreatest hM hpq).csSup_eq

end

end QIT
