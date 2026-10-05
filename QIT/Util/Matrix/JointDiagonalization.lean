/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Joint diagonalization of commuting Hermitian matrix families

For a pairwise commuting family of Hermitian matrices this module constructs an
explicit unitary change of basis that diagonalizes every member simultaneously,
together with the real joint eigenvalues, the linear-combination and
polynomial-evaluation transfer, and (over `ℂ`) the operator-norm bound for
polynomials of linear combinations.

The bridge starts from mathlib's linear-map-level joint eigenspace decomposition
(`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`). The decomposition is
restricted to the finite type of realized joint eigenvalue signatures
(`jointSpectrum`), which is what allows the `DirectSum.IsInternal`
orthonormal-basis machinery to apply; the matrix-level packaging then follows
the template of `Matrix.IsHermitian.eigenvectorUnitary`.

## Main declarations

* `jointSpectrum`, `fintypeJointSpectrum`: the finite type of realized joint
  eigenvalue signatures of a family of endomorphisms (finiteness needs no
  symmetry or commutativity hypotheses; the commuting symmetric specialization
  enters with the decomposition theorems below).
* `jointMatrixBasis`, `jointMatrixEigenvalues`: a common eigenvector
  orthonormal basis and the real joint eigenvalues.
* `jointUnitary`, `star_jointUnitary_mul_mul`: the diagonalizing unitary and
  the joint diagonalization theorem `star U * A i * U = diagonal ...`.
* `conjStarAlgAut_star_jointUnitary_sum`,
  `conjStarAlgAut_star_jointUnitary_aeval`: the same unitary diagonalizes
  linear combinations, and polynomial evaluation transfers to pointwise
  evaluation on the joint eigenvalues.
* `norm_aeval_linearCombination_le`: over `ℂ`, the operator norm of a
  polynomial of a linear combination is bounded by its values on the joint
  eigenvalues.
-/

@[expose] public section

open scoped Matrix Function ComplexConjugate Matrix.Norms.L2Operator

namespace QIT

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The finite joint spectrum and the restricted decomposition -/

/-- The joint spectrum of a family of endomorphisms: eigenvalue signatures whose joint
eigenspace is nonzero. -/
def jointSpectrum (T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)) : Type _ :=
  { χ : ι → 𝕜 // (⨅ j, Module.End.eigenspace (T j) (χ j)) ≠ ⊥ }

/-- Decidable equality on the joint spectrum (classical). -/
noncomputable instance decEqJointSpectrum (T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)) :
    DecidableEq (jointSpectrum T) := Classical.decEq _

/-- Component `j` of a joint spectral signature is an eigenvalue of `T j`. -/
def jointSpectrum.toEigenvalues {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (χ : jointSpectrum T) (j : ι) : Module.End.Eigenvalues (T j) :=
  ⟨χ.1 j, by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp χ.2
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨(Submodule.mem_iInf _).mp hv j, hv0⟩⟩

omit [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] in
/-- The component map from joint signatures to per-operator eigenvalues is injective. -/
theorem jointSpectrum.toEigenvalues_injective {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)} :
    Function.Injective (fun χ : jointSpectrum T => fun j => χ.toEigenvalues j) := by
  intro χ₁ χ₂ h
  apply Subtype.ext
  funext j
  exact congr_arg Subtype.val (congr_fun h j)

/-- The joint spectrum of a finite family on a finite-dimensional space is finite. -/
noncomputable instance fintypeJointSpectrum {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)} :
    Fintype (jointSpectrum T) :=
  Fintype.ofInjective _ jointSpectrum.toEigenvalues_injective

/-- The joint eigenspace attached to a joint spectral signature. -/
def jointEigenspace (T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m))
    (χ : jointSpectrum T) : Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  ⨅ j, Module.End.eigenspace (T j) (χ.1 j)

omit [DecidableEq m] [Fintype ι] [DecidableEq ι] in
/-- The joint eigenspaces over the joint spectrum span the whole space. -/
theorem jointEigenspace_iSup_eq_top {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) :
    (⨆ χ, jointEigenspace T χ) = ⊤ := by
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  rw [← top_le_iff] at htop ⊢
  refine htop.trans ?_
  apply iSup_le
  intro χ
  by_cases hχ : (⨅ j, Module.End.eigenspace (T j) (χ j)) = ⊥
  · rw [hχ]
    exact bot_le
  · exact le_iSup (fun χ' : jointSpectrum T => ⨅ j, Module.End.eigenspace (T j) (χ'.1 j)) ⟨χ, hχ⟩

omit [DecidableEq m] [Fintype ι] [DecidableEq ι] in
/-- The joint eigenspaces form an orthogonal family. -/
theorem jointEigenspace_orthogonal {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) :
    OrthogonalFamily 𝕜 (fun χ => jointEigenspace T χ)
      (fun χ => (jointEigenspace T χ).subtypeₗᵢ) :=
  (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT).comp Subtype.coe_injective

omit [DecidableEq m] in
/-- The joint eigenspaces over the joint spectrum form an internal direct sum. -/
theorem jointEigenspace_isInternal {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) :
    DirectSum.IsInternal (jointEigenspace T) := by
  rw [(jointEigenspace_orthogonal hT).isInternal_iff, Submodule.orthogonal_eq_bot_iff]
  exact jointEigenspace_iSup_eq_top hT hC

/-! ### The joint eigenvector basis and real joint eigenvalues -/

/-- An orthonormal basis of joint eigenvectors, indexed by `Fin (Fintype.card m)`. -/
noncomputable def jointEigenvectorBasisFin {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) :
    OrthonormalBasis (Fin (Fintype.card m)) 𝕜 (EuclideanSpace 𝕜 m) :=
  (jointEigenspace_isInternal hT hC).subordinateOrthonormalBasis
    (finrank_euclideanSpace (𝕜 := 𝕜)) (jointEigenspace_orthogonal hT)

/-- The joint eigenvalue signature of the `a`-th basis vector. -/
noncomputable def jointSignature {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (a : Fin (Fintype.card m)) :
    ι → 𝕜 :=
  ((jointEigenspace_isInternal hT hC).subordinateOrthonormalBasisIndex
    (finrank_euclideanSpace (𝕜 := 𝕜)) a (jointEigenspace_orthogonal hT)).1

omit [DecidableEq m] in
/-- The `a`-th basis vector lies in the joint eigenspace of its signature. -/
theorem jointEigenvectorBasis_mem {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (a : Fin (Fintype.card m)) :
    jointEigenvectorBasisFin hT hC a ∈
      ⨅ j, Module.End.eigenspace (T j) (jointSignature hT hC a j) :=
  (jointEigenspace_isInternal hT hC).subordinateOrthonormalBasis_subordinate
    (finrank_euclideanSpace (𝕜 := 𝕜)) a (jointEigenspace_orthogonal hT)

omit [DecidableEq m] in
/-- Each basis vector is a joint eigenvector, with eigenvalues given by the signature. -/
theorem jointEigenvectorBasis_apply {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (i : ι)
    (a : Fin (Fintype.card m)) :
    T i (jointEigenvectorBasisFin hT hC a) =
      (jointSignature hT hC a i) • jointEigenvectorBasisFin hT hC a :=
  Module.End.mem_eigenspace_iff.mp
    ((Submodule.mem_iInf _).mp (jointEigenvectorBasis_mem hT hC a) i)

omit [DecidableEq m] in
/-- Joint eigenvalues of symmetric operators are self-conjugate. -/
theorem jointSignature_conj {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (i : ι)
    (a : Fin (Fintype.card m)) :
    conj (jointSignature hT hC a i) = jointSignature hT hC a i := by
  apply (hT i).conj_eigenvalue_eq_self
  apply Module.End.hasEigenvalue_of_hasEigenvector
  exact ⟨by rw [Module.End.mem_eigenspace_iff]; exact jointEigenvectorBasis_apply hT hC i a,
    (jointEigenvectorBasisFin hT hC).orthonormal.ne_zero a⟩

/-- The real joint eigenvalue of the `i`-th operator on the `a`-th basis vector. -/
noncomputable def jointEigenvalues {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (i : ι)
    (a : Fin (Fintype.card m)) : ℝ :=
  RCLike.re (jointSignature hT hC a i)

omit [DecidableEq m] in
/-- The signature is the coercion of the real joint eigenvalues. -/
theorem jointSignature_eq_ofReal {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (i : ι)
    (a : Fin (Fintype.card m)) :
    jointSignature hT hC a i = (jointEigenvalues hT hC i a : 𝕜) :=
  (RCLike.conj_eq_iff_re.mp (jointSignature_conj hT hC i a)).symm

omit [DecidableEq m] in
/-- `ofReal`-scalar form of the joint eigenvector equation. -/
theorem jointEigenvectorBasis_apply_real {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (i : ι)
    (a : Fin (Fintype.card m)) :
    T i (jointEigenvectorBasisFin hT hC a) =
      (jointEigenvalues hT hC i a : 𝕜) • jointEigenvectorBasisFin hT hC a := by
  rw [← jointSignature_eq_ofReal hT hC i a]
  exact jointEigenvectorBasis_apply hT hC i a

/-- An orthonormal basis of joint eigenvectors, indexed by the matrix index type. -/
noncomputable def jointEigenvectorBasis {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) :
    OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m) :=
  (jointEigenvectorBasisFin hT hC).reindex (Fintype.equivOfCardEq (Fintype.card_fin _))

/-- The joint signature, reindexed by `m`. -/
noncomputable def jointSignatureM {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (a : m) : ι → 𝕜 :=
  jointSignature hT hC ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm a)

/-- The real joint eigenvalues, reindexed by `m`. -/
noncomputable def jointEigenvaluesM {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (i : ι) (a : m) : ℝ :=
  jointEigenvalues hT hC i ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm a)

omit [DecidableEq m] in
/-- Joint eigenvector equation for the reindexed basis. -/
theorem jointEigenvectorBasis_apply' {T : ι → Module.End 𝕜 (EuclideanSpace 𝕜 m)}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Commute on T)) (i : ι) (a : m) :
    T i (jointEigenvectorBasis hT hC a) =
      (jointEigenvaluesM hT hC i a : 𝕜) • jointEigenvectorBasis hT hC a := by
  have h := jointEigenvectorBasis_apply_real hT hC i
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm a)
  rw [← OrthonormalBasis.reindex_apply] at h
  exact h

/-! ### Matrix-level bridges and the packaged basis -/

/-- Conjugation to `EuclideanSpace` preserves commutation. -/
theorem commute_toEuclideanLin {X Y : Matrix m m 𝕜} (h : Commute X Y) :
    Commute X.toEuclideanLin Y.toEuclideanLin :=
  h.map (Matrix.toLpLinAlgEquiv (n := m) (R := 𝕜) 2)

omit [Fintype ι] [DecidableEq ι] in
/-- A pairwise commuting family of matrices maps to one of endomorphisms. -/
theorem pairwise_commute_toEuclideanLin {A : ι → Matrix m m 𝕜}
    (hAc : Pairwise (Commute on A)) :
    Pairwise (Commute on fun i => (A i).toEuclideanLin) :=
  fun _ _ hij => commute_toEuclideanLin (hAc hij)

/-- The joint eigenvector basis of a commuting Hermitian matrix family. -/
noncomputable def jointMatrixBasis {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) :
    OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m) :=
  jointEigenvectorBasis (fun i => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hAh i))
    (pairwise_commute_toEuclideanLin hAc)

/-- The real joint eigenvalues of a commuting Hermitian matrix family. -/
noncomputable def jointMatrixEigenvalues {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (i : ι) (a : m) : ℝ :=
  jointEigenvaluesM (fun i => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hAh i))
    (pairwise_commute_toEuclideanLin hAc) i a

/-! ### The unitary packaging and the diagonalization theorem -/

/-- The change-of-basis matrix whose columns are the joint eigenvectors. -/
noncomputable def jointUnitaryMat {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) : Matrix m m 𝕜 :=
  (EuclideanSpace.basisFun m 𝕜).toBasis.toMatrix (jointMatrixBasis hAh hAc).toBasis

/-- The change-of-basis matrix is unitary. -/
theorem jointUnitaryMat_mem {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) :
    jointUnitaryMat hAh hAc ∈ Matrix.unitaryGroup m 𝕜 :=
  (EuclideanSpace.basisFun m 𝕜).toMatrix_orthonormalBasis_mem_unitary (jointMatrixBasis hAh hAc)

/-- The joint-diagonalizing unitary. -/
noncomputable def jointUnitary {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) :
    Matrix.unitaryGroup m 𝕜 :=
  ⟨jointUnitaryMat hAh hAc, jointUnitaryMat_mem hAh hAc⟩

/-- Entry characterization of the joint unitary. -/
theorem jointUnitary_apply {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (i j : m) :
    (jointUnitary hAh hAc : Matrix m m 𝕜) i j = ⇑(jointMatrixBasis hAh hAc j) i := rfl

/-- The columns of the joint unitary are the joint eigenvectors. -/
theorem jointUnitary_col_eq {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (j : m) :
    Matrix.col (jointUnitary hAh hAc : Matrix m m 𝕜) j = ⇑(jointMatrixBasis hAh hAc j) := rfl

/-- The joint unitary maps the `j`-th standard vector to the `j`-th joint eigenvector. -/
theorem jointUnitary_mulVec {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (j : m) :
    (jointUnitary hAh hAc : Matrix m m 𝕜) *ᵥ Pi.single j 1 = ⇑(jointMatrixBasis hAh hAc j) := by
  simp_rw [Matrix.mulVec_single_one, jointUnitary_col_eq]

/-- The adjoint of the joint unitary maps the `j`-th joint eigenvector back to the
`j`-th standard vector. -/
theorem star_jointUnitary_mulVec {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (j : m) :
    (star (jointUnitary hAh hAc : Matrix m m 𝕜)) *ᵥ ⇑(jointMatrixBasis hAh hAc j) =
      Pi.single j 1 := by
  rw [← jointUnitary_mulVec, Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]

/-- The joint eigenvector equation in `mulVec` form. -/
theorem mulVec_jointMatrixBasis {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (i : ι) (a : m) :
    (A i) *ᵥ ⇑(jointMatrixBasis hAh hAc a) =
      (jointMatrixEigenvalues hAh hAc i a) • ⇑(jointMatrixBasis hAh hAc a) := by
  simpa only [jointMatrixBasis, jointMatrixEigenvalues, Matrix.toLpLin_apply, WithLp.ofLp_smul,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
    congr(⇑$(jointEigenvectorBasis_apply'
      (fun i => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hAh i))
      (pairwise_commute_toEuclideanLin hAc) i a))

/-- **Joint diagonalization**, conjugation form: one unitary diagonalizes every member. -/
theorem conjStarAlgAut_star_jointUnitary {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (i : ι) :
    Unitary.conjStarAlgAut 𝕜 _ (star (jointUnitary hAh hAc)) (A i) =
      Matrix.diagonal (RCLike.ofReal ∘ jointMatrixEigenvalues hAh hAc i) := by
  apply Matrix.toEuclideanLin.injective <| (EuclideanSpace.basisFun m 𝕜).toBasis.ext fun a ↦ ?_
  simp only [Unitary.conjStarAlgAut_star_apply, Matrix.toLpLin_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← Matrix.mulVec_mulVec,
    jointUnitary_mulVec, ← Matrix.mulVec_mulVec, mulVec_jointMatrixBasis,
    Matrix.diagonal_mulVec_single, Matrix.mulVec_smul, star_jointUnitary_mulVec,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul, PiLp.toLp_single,
    Function.comp_apply, mul_one]
  apply PiLp.ext fun j ↦ ?_
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- **Joint diagonalization**, matrix form. -/
theorem star_jointUnitary_mul_mul {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (i : ι) :
    (star (jointUnitary hAh hAc : Matrix m m 𝕜)) * A i * (jointUnitary hAh hAc : Matrix m m 𝕜) =
      Matrix.diagonal (RCLike.ofReal ∘ jointMatrixEigenvalues hAh hAc i) :=
  (Unitary.conjStarAlgAut_star_apply (S := 𝕜) (jointUnitary hAh hAc) (A i)).symm.trans
    (conjStarAlgAut_star_jointUnitary hAh hAc i)

/-- **Spectral form**: each member is the unitary conjugate of its eigenvalue diagonal. -/
theorem joint_spectral_theorem {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (i : ι) :
    A i = Unitary.conjStarAlgAut 𝕜 _ (jointUnitary hAh hAc)
      (Matrix.diagonal (RCLike.ofReal ∘ jointMatrixEigenvalues hAh hAc i)) := by
  rw [← conjStarAlgAut_star_jointUnitary hAh hAc i, ← Unitary.conjStarAlgAut_mul_apply]
  simp

/-- Existence form for consumers: a common diagonalizing unitary exists. -/
theorem exists_joint_unitary_diagonal {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) :
    ∃ U : Matrix.unitaryGroup m 𝕜, ∀ i, ∃ d : m → ℝ,
      (star (U : Matrix m m 𝕜)) * A i * (U : Matrix m m 𝕜) =
        Matrix.diagonal (RCLike.ofReal ∘ d) :=
  ⟨jointUnitary hAh hAc, fun i =>
    ⟨jointMatrixEigenvalues hAh hAc i, star_jointUnitary_mul_mul hAh hAc i⟩⟩

/-- Existence of a common eigenvector orthonormal basis (consumer form). -/
theorem exists_joint_eigenvectorBasis {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) :
    ∃ B : OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m),
      ∀ i a, ∃ r : ℝ, (A i) *ᵥ ⇑(B a) = r • ⇑(B a) :=
  ⟨jointMatrixBasis hAh hAc, fun i a =>
    ⟨jointMatrixEigenvalues hAh hAc i a, mulVec_jointMatrixBasis hAh hAc i a⟩⟩

/-! ### Linearity and polynomial-evaluation transfer

The joint unitary also diagonalizes every linear combination of the family, and polynomial
evaluation on a combination is pointwise polynomial evaluation on the joint eigenvalues. -/

/-- The same unitary diagonalizes linear combinations, with eigenvalues the
corresponding combinations. -/
theorem conjStarAlgAut_star_jointUnitary_sum {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (c : ι → 𝕜) :
    Unitary.conjStarAlgAut 𝕜 (Matrix m m 𝕜) (star (jointUnitary hAh hAc)) (∑ i, c i • A i) =
      Matrix.diagonal (fun a => ∑ i, c i * (jointMatrixEigenvalues hAh hAc i a : 𝕜)) := by
  have step1 :
      Unitary.conjStarAlgAut 𝕜 (Matrix m m 𝕜) (star (jointUnitary hAh hAc)) (∑ i, c i • A i) =
        ∑ i, c i •
          Unitary.conjStarAlgAut 𝕜 (Matrix m m 𝕜) (star (jointUnitary hAh hAc)) (A i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have step2 : ∑ i, c i •
        Unitary.conjStarAlgAut 𝕜 (Matrix m m 𝕜) (star (jointUnitary hAh hAc)) (A i) =
      ∑ i, c i • Matrix.diagonal (RCLike.ofReal ∘ jointMatrixEigenvalues hAh hAc i) :=
    Finset.sum_congr rfl fun i _ => by rw [conjStarAlgAut_star_jointUnitary hAh hAc i]
  have step3 : ∑ i, c i • Matrix.diagonal (RCLike.ofReal ∘ jointMatrixEigenvalues hAh hAc i) =
      ∑ i, Matrix.diagonal (fun a => c i * (jointMatrixEigenvalues hAh hAc i a : 𝕜)) :=
    Finset.sum_congr rfl fun i _ => (Matrix.diagonal_smul _ _).symm
  have step4 : ∑ i, Matrix.diagonal (fun a => c i * (jointMatrixEigenvalues hAh hAc i a : 𝕜)) =
      Matrix.diagonal (fun a => ∑ i, c i * (jointMatrixEigenvalues hAh hAc i a : 𝕜)) := by
    have hstep : (Matrix.diagonal (fun a => ∑ i ∈ Finset.univ, c i *
          (jointMatrixEigenvalues hAh hAc i a : 𝕜)) : Matrix m m 𝕜) =
        Matrix.diagonalAlgHom (R := 𝕜) (n := m) (α := 𝕜)
          (∑ i ∈ Finset.univ, fun a => c i * (jointMatrixEigenvalues hAh hAc i a : 𝕜)) := by
      show Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext a
      rw [Finset.sum_apply]
    rw [hstep, map_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  exact step1.trans (step2.trans (step3.trans step4))

/-- Polynomial evaluation commutes with the diagonal embedding. -/
theorem aeval_diagonal (v : m → 𝕜) (p : Polynomial 𝕜) :
    Polynomial.aeval (Matrix.diagonal v) p =
      Matrix.diagonal (fun a => Polynomial.aeval (v a) p) := by
  rw [show (Matrix.diagonal v : Matrix m m 𝕜) =
      Matrix.diagonalAlgHom (R := 𝕜) (n := m) (α := 𝕜) v from rfl]
  rw [Polynomial.aeval_algHom_apply]
  show Matrix.diagonal (Polynomial.aeval v p) = _
  congr with a
  exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom 𝕜 (fun _ : m => 𝕜) a) v p).symm

/-- **Polynomial-evaluation transfer**: the joint unitary evaluates a polynomial on the
eigenvalues of a linear combination. -/
theorem conjStarAlgAut_star_jointUnitary_aeval {A : ι → Matrix m m 𝕜}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (c : ι → 𝕜)
    (p : Polynomial 𝕜) :
    Unitary.conjStarAlgAut 𝕜 (Matrix m m 𝕜) (star (jointUnitary hAh hAc))
        (Polynomial.aeval (∑ i, c i • A i) p) =
      Matrix.diagonal
        (fun a => Polynomial.aeval (∑ i, c i * (jointMatrixEigenvalues hAh hAc i a : 𝕜)) p) := by
  rw [← Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut 𝕜 (Matrix m m 𝕜) (star (jointUnitary hAh hAc)))]
  rw [conjStarAlgAut_star_jointUnitary_sum hAh hAc c, aeval_diagonal]

/-! ### Operator-norm bounds over the complex numbers

Over `ℂ`, the operator norm of a polynomial of a linear combination is the supremum norm of
the polynomial evaluated on the joint eigenvalues. -/

/-- The operator-norm C⋆-algebra structure on complex matrices (local to this file). -/
noncomputable local instance complexMatrixCStarAlgebra {n : Type*} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where

/-- Unitary conjugation is norm-preserving on matrices. -/
theorem norm_conjStarAlgAut (U : unitary (Matrix m m ℂ)) (M : Matrix m m ℂ) :
    ‖Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) U M‖ = ‖M‖ :=
  have hU : Isometry (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) U) :=
    NonUnitalStarAlgHom.isometry _ (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) U).injective
  hU.norm_map_of_map_zero (map_zero _) _

/-- The operator norm of a polynomial of a linear combination is the sup norm of the
polynomial evaluated on the joint eigenvalues. -/
theorem norm_aeval_linearCombination_eq {A : ι → Matrix m m ℂ}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (c : ι → ℂ)
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval (∑ i, c i • A i) p‖ =
      ‖fun a => Polynomial.aeval (∑ i, c i * (jointMatrixEigenvalues hAh hAc i a : ℂ)) p‖ := by
  have h1 : ‖Polynomial.aeval (∑ i, c i • A i) p‖ =
      ‖Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) (star (jointUnitary hAh hAc))
        (Polynomial.aeval (∑ i, c i • A i) p)‖ :=
    (norm_conjStarAlgAut (star (jointUnitary hAh hAc)) _).symm
  rw [conjStarAlgAut_star_jointUnitary_aeval hAh hAc c p, Matrix.l2_opNorm_diagonal] at h1
  exact h1

/-- Bound form: the norm is at most any uniform bound of the values on joint eigenvalues. -/
theorem norm_aeval_linearCombination_le {A : ι → Matrix m m ℂ}
    (hAh : ∀ i, (A i).IsHermitian) (hAc : Pairwise (Commute on A)) (c : ι → ℂ)
    (p : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ a, ‖Polynomial.aeval (∑ i, c i * (jointMatrixEigenvalues hAh hAc i a : ℂ)) p‖ ≤ r) :
    ‖Polynomial.aeval (∑ i, c i • A i) p‖ ≤ r := by
  rw [norm_aeval_linearCombination_eq hAh hAc c p]
  exact (pi_norm_le_iff_of_nonneg hr).mpr h

end

end QIT
