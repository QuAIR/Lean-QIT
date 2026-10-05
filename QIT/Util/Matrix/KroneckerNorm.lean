/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix.JointDiagonalization

/-!
# Operator norm of a Kronecker product

The complex matrix L2 operator norm is multiplicative under Kronecker products.
Hermitian diagonalization supplies the square-matrix calculation; Gram matrices
extend it to arbitrary rectangular matrices, including empty index types.
Unitary invariance is provided by the imported `QIT.norm_conjStarAlgAut`.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

private theorem norm_prod_function_mul
    {m n : Type*} [Fintype m] [Fintype n] (f : m → ℂ) (g : n → ℂ) :
    ‖fun i : m × n => f i.1 * g i.2‖ = ‖f‖ * ‖g‖ := by
  let F := fun i : m × n => f i.1 * g i.2
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg f) (norm_nonneg g))).mpr
    intro i
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm f i.1) (norm_le_pi_norm g i.2)
      (norm_nonneg _) (norm_nonneg _)
  · have h (i : m) : ‖f i‖ * ‖g‖ ≤ ‖F‖ := by
      rw [← norm_smul]
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg F)).mpr
      intro j
      exact norm_le_pi_norm F (i, j)
    have h' : ‖(‖g‖ : ℝ) • f‖ ≤ ‖F‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg F)).mpr
      intro i
      simpa only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (norm_nonneg g),
        mul_comm] using h i
    simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg g), mul_comm] using h'

private theorem hermitian_norm_kronecker
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖Matrix.kronecker A B‖ = ‖A‖ * ‖B‖ := by
  let U : unitary (Matrix (m × n) (m × n) ℂ) :=
    ⟨Matrix.kronecker (hA.eigenvectorUnitary : Matrix m m ℂ)
      (hB.eigenvectorUnitary : Matrix n n ℂ),
      Matrix.kronecker_mem_unitary hA.eigenvectorUnitary.2 hB.eigenvectorUnitary.2⟩
  have hdiag : Unitary.conjStarAlgAut ℂ _ (star U) (Matrix.kronecker A B) =
      Matrix.kronecker (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)))
        (Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ))) := by
    rw [Unitary.conjStarAlgAut_star_apply]
    change (Matrix.kronecker (hA.eigenvectorUnitary : Matrix m m ℂ)
      (hB.eigenvectorUnitary : Matrix n n ℂ))ᴴ * Matrix.kronecker A B *
      Matrix.kronecker (hA.eigenvectorUnitary : Matrix m m ℂ)
        (hB.eigenvectorUnitary : Matrix n n ℂ) = _
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.kronecker, RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using
      congrArg₂ Matrix.kronecker hA.conjStarAlgAut_star_eigenvectorUnitary
        hB.conjStarAlgAut_star_eigenvectorUnitary
  have hnormA := norm_conjStarAlgAut (star hA.eigenvectorUnitary) A
  have hnormB := norm_conjStarAlgAut (star hB.eigenvectorUnitary) B
  rw [hA.conjStarAlgAut_star_eigenvectorUnitary, Matrix.l2_opNorm_diagonal] at hnormA
  rw [hB.conjStarAlgAut_star_eigenvectorUnitary, Matrix.l2_opNorm_diagonal] at hnormB
  calc
    ‖Matrix.kronecker A B‖ = ‖Unitary.conjStarAlgAut ℂ _ (star U)
        (Matrix.kronecker A B)‖ := (norm_conjStarAlgAut _ _).symm
    _ = ‖fun i : m × n => (hA.eigenvalues i.1 : ℂ) * (hB.eigenvalues i.2 : ℂ)‖ := by
      rw [hdiag, Matrix.kronecker, Matrix.diagonal_kronecker_diagonal,
        Matrix.l2_opNorm_diagonal]
    _ = ‖A‖ * ‖B‖ := by
      rw [norm_prod_function_mul (fun i => (hA.eigenvalues i : ℂ))
        (fun i => (hB.eigenvalues i : ℂ)), ← hnormA, ← hnormB]
      rfl

/-- The L2 operator norm of a Kronecker product is the product of the norms.
The matrices may be rectangular, with arbitrary finite row and column types;
no nonempty-index assumption is needed. -/
theorem matrix_l2_opNorm_kronecker
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    ‖Matrix.kronecker A B‖ = ‖A‖ * ‖B‖ := by
  have h := hermitian_norm_kronecker (Aᴴ * A) (Bᴴ * B)
    (Matrix.isHermitian_conjTranspose_mul_self A)
    (Matrix.isHermitian_conjTranspose_mul_self B)
  have hGram : (Matrix.kronecker A B)ᴴ * Matrix.kronecker A B =
      Matrix.kronecker (Aᴴ * A) (Bᴴ * B) := by
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
  rw [← hGram, Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.l2_opNorm_conjTranspose_mul_self] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg B))).mp
  nlinarith only [h]

end

end QIT
