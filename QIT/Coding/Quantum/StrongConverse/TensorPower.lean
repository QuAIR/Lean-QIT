/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.Stinespring
public import QIT.Coding.Quantum.PolyApprox.TensorNorm

/-!
# Tensor blocks for the quantum strong converse

The Stinespring tensor power groups all receiver wires and all environment
wires. Its image is the tensor power of the single-use image projector
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:506-508].
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

universe u v w

namespace ReferenceIsometry

variable {a : Type u} {b : Type v} {e : Type w}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype e] [DecidableEq e]

/-- The Stinespring tensor power with receiver and environment wires grouped. -/
def tensorPowerBipartite (V : ReferenceIsometry a (b × e)) (n : ℕ) :
    ReferenceIsometry (TensorPower a n) (TensorPower b n × TensorPower e n) where
  matrix := (V.tensorPower n).matrix.submatrix (tensorPowerProdEquiv b e n).symm id
  isometry := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      (V.tensorPower n).isometry, Matrix.submatrix_id_id]

/-- The image projector commutes with taking tensor powers. -/
theorem tensorPower_imageProjector (V : ReferenceIsometry a b) (n : ℕ) :
    (V.tensorPower n).imageProjector = TensorPower.tensorPowMatrix V.imageProjector n := by
  induction n with
  | zero =>
      ext x y
      change (∑ _ : TensorPower a 0, (1 : ℂ) * star 1) = 1
      simp only [star_one, mul_one, Finset.sum_const]
      change Fintype.card PUnit.{u + 1} • (1 : ℂ) = 1
      rw [Fintype.card_punit, one_nsmul]
  | succ n ih =>
      change (V.matrix.kronecker (V.tensorPower n).matrix) *
        (V.matrix.kronecker (V.tensorPower n).matrix)ᴴ = _
      rw [show (V.matrix.kronecker (V.tensorPower n).matrix)ᴴ =
        V.matrixᴴ.kronecker (V.tensorPower n).matrixᴴ from
          Matrix.conjTranspose_kronecker V.matrix (V.tensorPower n).matrix]
      rw [show V.matrix.kronecker (V.tensorPower n).matrix *
          V.matrixᴴ.kronecker (V.tensorPower n).matrixᴴ =
          (V.matrix * V.matrixᴴ).kronecker
            ((V.tensorPower n).matrix * (V.tensorPower n).matrixᴴ) from
          (Matrix.mul_kronecker_mul _ _ _ _).symm]
      exact congrArg (Matrix.kronecker V.imageProjector) ih

/-- Grouping the output registers reindexes the tensor image projector. -/
theorem tensorPowerBipartite_imageProjector (V : ReferenceIsometry a (b × e)) (n : ℕ) :
    (V.tensorPowerBipartite n).imageProjector =
      WireFam.matReindex (tensorPowerProdEquiv b e n)
        (TensorPower.tensorPowMatrix V.imageProjector n) := by
  unfold imageProjector tensorPowerBipartite
  rw [Matrix.conjTranspose_submatrix]
  change (V.tensorPower n).matrix.submatrix _ (Equiv.refl _) *
    (V.tensorPower n).matrixᴴ.submatrix (Equiv.refl _) _ = _
  rw [Matrix.submatrix_mul_equiv]
  exact congrArg (WireFam.matReindex (tensorPowerProdEquiv b e n))
    (V.tensorPower_imageProjector n)

/-- The block image projector on function-indexed receiver and environment wires. -/
theorem tensorPowerBipartite_imageProjector_reindex
    (V : ReferenceIsometry a (b × e)) (n : ℕ) :
    WireFam.matReindex ((tensorPowerEquiv (a := b) n).prodCongr
      (tensorPowerEquiv (a := e) n)) (V.tensorPowerBipartite n).imageProjector =
      TensorPower.tensorPowMatrixPair V.imageProjector n := by
  rw [tensorPowerBipartite_imageProjector]
  exact TensorPower.matReindex_tensorPowerProdEquiv_tensorPowMatrix _ _

private theorem outputChannel_single_apply (V : ReferenceIsometry a (b × e))
    (x y : a) (i j : b) :
    V.outputChannel.map (Matrix.single x y (1 : ℂ)) i j =
      ∑ k, V.matrix (i, k) x * star (V.matrix (j, k) y) := by
  rw [outputChannel_map]
  simp [partialTraceB, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and]

private theorem tensorPowerBipartite_outputChannel_single
    (V : ReferenceIsometry a (b × e)) (n : ℕ)
    (x y : TensorPower a n) (i j : TensorPower b n) :
    (V.tensorPowerBipartite n).outputChannel.map (Matrix.single x y (1 : ℂ)) i j =
      (V.outputChannel.tensorPower n).map (Matrix.single x y (1 : ℂ)) i j := by
  induction n with
  | zero =>
      cases x
      cases y
      cases i
      cases j
      refine (outputChannel_single_apply _ _ _ _ _).trans ?_
      change (∑ _ : TensorPower e 0, (1 : ℂ) * star 1) = 1
      simp only [star_one, mul_one, Finset.sum_const]
      change Fintype.card PUnit.{w + 1} • (1 : ℂ) = 1
      rw [Fintype.card_punit, one_nsmul]
  | succ n ih =>
      rcases x with ⟨x, xs⟩
      rcases y with ⟨y, ys⟩
      rcases i with ⟨i, is⟩
      rcases j with ⟨j, js⟩
      change _ = (V.outputChannel.prod (V.outputChannel.tensorPower n)).map
        (Matrix.single (x, xs) (y, ys) (1 : ℂ)) (i, is) (j, js)
      rw [single_prod_eq_kronecker_single, Channel.prod_map_kronecker]
      change _ = V.outputChannel.map (Matrix.single x y (1 : ℂ)) i j *
        (V.outputChannel.tensorPower n).map (Matrix.single xs ys (1 : ℂ)) is js
      rw [← ih]
      refine (outputChannel_single_apply _ _ _ _ _).trans ?_
      rw [outputChannel_single_apply, outputChannel_single_apply]
      change (∑ k : e × TensorPower e n,
        (V.matrix (i, k.1) x * (V.tensorPowerBipartite n).matrix (is, k.2) xs) *
          star (V.matrix (j, k.1) y * (V.tensorPowerBipartite n).matrix (js, k.2) ys)) = _
      simp only [star_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- The grouped Stinespring tensor power realizes the tensor-power channel on
all matrices, including inputs entangled across channel uses. -/
theorem tensorPowerBipartite_outputChannel (V : ReferenceIsometry a (b × e)) (n : ℕ) :
    (V.tensorPowerBipartite n).outputChannel = V.outputChannel.tensorPower n := by
  have hm : (V.tensorPowerBipartite n).outputChannel.map =
      (V.outputChannel.tensorPower n).map := by
    apply LinearMap.ext
    intro X
    rw [MatrixMap.map_eq_sum_single, MatrixMap.map_eq_sum_single]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    ext i j
    exact tensorPowerBipartite_outputChannel_single V n x y i j
  cases h₁ : (V.tensorPowerBipartite n).outputChannel
  cases h₂ : V.outputChannel.tensorPower n
  simp only [h₁, h₂] at hm
  cases hm
  rfl

end ReferenceIsometry

section LocalNorm

variable {b e b' e' : Type u}
  [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
  [Fintype b'] [DecidableEq b'] [Fintype e'] [DecidableEq e']

private theorem piNorm_matReindex_prodCongr_le (f : b ≃ b') (g : e ≃ e')
    (T : CMatrix (b × e)) :
    piNorm (WireFam.matReindex (f.prodCongr g) T) ≤ piNorm T := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d, hd⟩ := exists_piNormDecomposition_cost_le_add T hε
  have hs : (∑ j, Matrix.kronecker (WireFam.matReindex f (d.left j))
      (WireFam.matReindex g (d.right j))) = WireFam.matReindex (f.prodCongr g) T := by
    conv_rhs => rw [← d.sum_eq]
    simp only [← WireFam.matReindex_kronecker_prodCongr]
    ext x y
    simp [Matrix.sum_apply]
  rw [← hs]
  refine (piNorm_le_sum_norm_mul_norm _ _).trans ?_
  simp only [show ∀ X : CMatrix b, ‖WireFam.matReindex f X‖ = ‖X‖ from
    QuantumPolyApprox.matrix_reindex_norm f,
    show ∀ X : CMatrix e, ‖WireFam.matReindex g X‖ = ‖X‖ from
    QuantumPolyApprox.matrix_reindex_norm g]
  exact hd

/-- Local changes of basis labels preserve the projective tensor norm.
Positive decomposition slack avoids any assumption that the infimum is attained. -/
theorem piNorm_matReindex_prodCongr (f : b ≃ b') (g : e ≃ e')
    (T : CMatrix (b × e)) :
    piNorm (WireFam.matReindex (f.prodCongr g) T) = piNorm T := by
  apply le_antisymm (piNorm_matReindex_prodCongr_le f g T)
  have h := piNorm_matReindex_prodCongr_le f.symm g.symm
    (WireFam.matReindex (f.prodCongr g) T)
  have hi : WireFam.matReindex (f.symm.prodCongr g.symm)
      (WireFam.matReindex (f.prodCongr g) T) = T := by
    ext ⟨x, x'⟩ ⟨y, y'⟩
    simp
  rwa [hi] at h

end LocalNorm

end

end QIT
