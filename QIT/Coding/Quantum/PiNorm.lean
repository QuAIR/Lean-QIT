/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import QIT.Util.Matrix.KroneckerNorm
public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.RingTheory.MatrixAlgebra

/-!
# Projective tensor norm of bipartite matrices

The local matrix factors carry the L2 operator norm. Finite Kronecker
decompositions give the projective norm through an infimum of their costs
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:376-383].
The working interfaces use arbitrary positive slack rather than attainment
of that infimum. The two factor index types live in a common universe;
either factor may be empty.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator TensorProduct

namespace QIT

noncomputable section

universe u

variable {b e : Type u}

/-- A finite Kronecker decomposition of a bipartite matrix. The number of
terms may be zero; no minimizing property is included. -/
structure PiNormDecomposition (Z : CMatrix (b × e)) where
  length : ℕ
  left : Fin length → CMatrix b
  right : Fin length → CMatrix e
  sum_eq : ∑ j, Matrix.kronecker (left j) (right j) = Z

section TensorRepresentation

variable (b e : Type u)
/-- The two local matrix spaces, indexed by a disjoint pair of singletons. -/
abbrev MatrixPiFactor : Unit ⊕ Unit → Type _ := Sum.elim (fun _ => CMatrix b) (fun _ => CMatrix e)
/-- Each tensor factor carries the L2 operator norm. -/
@[reducible] instance matrixPiFactorNormed [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]
    (i : Unit ⊕ Unit) : NormedAddCommGroup (MatrixPiFactor b e i) := by
  cases i <;> exact Matrix.instL2OpNormedAddCommGroup
/-- The canonical complex normed-space structure on each local matrix space. -/
@[reducible] instance matrixPiFactorSpace [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]
    (i : Unit ⊕ Unit) : NormedSpace ℂ (MatrixPiFactor b e i) := by
  cases i <;> exact Matrix.instL2OpNormedSpace
variable [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]
/-- The Mathlib tensor representation of bipartite matrices. -/
abbrev MatrixPiTensor := PiTensorProduct ℂ (MatrixPiFactor b e)
/-- The canonical linear equivalence from the two-factor tensor to a bipartite matrix. -/
def matrixPiTensorEquiv : MatrixPiTensor b e ≃ₗ[ℂ] CMatrix (b × e) :=
  (PiTensorProduct.tmulEquivDep ℂ (MatrixPiFactor b e)).symm ≪≫ₗ
    TensorProduct.congr (PiTensorProduct.subsingletonEquiv ())
      (PiTensorProduct.subsingletonEquiv ()) ≪≫ₗ kroneckerLinearEquiv b b e e ℂ
variable {b e}
/-- A pure tensor represents the Kronecker product of its two factors. -/
theorem matrixPiTensorEquiv_tprod (f : ∀ i, MatrixPiFactor b e i) :
    matrixPiTensorEquiv b e (PiTensorProduct.tprod ℂ f) =
      Matrix.kronecker (f (.inl ())) (f (.inr ())) := by
  change kroneckerLinearEquiv b b e e ℂ
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv ())
      (PiTensorProduct.subsingletonEquiv ())
      ((PiTensorProduct.tmulEquivDep ℂ (MatrixPiFactor b e)).symm
        (PiTensorProduct.tprod ℂ f))) = _
  rw [PiTensorProduct.tmulEquivDep_symm_apply]
  simp only [TensorProduct.congr_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

end TensorRepresentation

variable [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]

/-- The sum of products of local operator norms in a finite decomposition. -/
def PiNormDecomposition.cost {Z : CMatrix (b × e)} (d : PiNormDecomposition Z) : ℝ :=
  ∑ j, ‖d.left j‖ * ‖d.right j‖

/-- Every decomposition has nonnegative cost. -/
theorem PiNormDecomposition.cost_nonneg {Z : CMatrix (b × e)}
    (d : PiNormDecomposition Z) : 0 ≤ d.cost :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- A decomposition cost dominates the bipartite operator norm. -/
theorem PiNormDecomposition.norm_le_cost {Z : CMatrix (b × e)}
    (d : PiNormDecomposition Z) : ‖Z‖ ≤ d.cost := by
  calc
    ‖Z‖ = ‖∑ j, Matrix.kronecker (d.left j) (d.right j)‖ :=
      congrArg norm d.sum_eq.symm
    _ ≤ ∑ j, ‖Matrix.kronecker (d.left j) (d.right j)‖ := norm_sum_le _ _
    _ = d.cost := by simp_rw [matrix_l2_opNorm_kronecker]; rfl

/-- The projective tensor norm induced by the two local L2 operator norms,
as an infimum over finite Kronecker decomposition costs
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:376-383]. -/
def piNorm (Z : CMatrix (b × e)) : ℝ :=
  sInf (Set.range (fun d : PiNormDecomposition Z => d.cost))

/-- The projective tensor norm is nonnegative. -/
theorem piNorm_nonneg (Z : CMatrix (b × e)) : 0 ≤ piNorm Z := by
  apply Real.sInf_nonneg
  rintro _ ⟨d, rfl⟩
  exact d.cost_nonneg

/-- Any explicit finite decomposition gives an upper bound. -/
theorem piNorm_le_cost {Z : CMatrix (b × e)} (d : PiNormDecomposition Z) :
    piNorm Z ≤ d.cost := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨d, rfl⟩; exact d.cost_nonneg⟩
  · exact ⟨d, rfl⟩

/-- The zero matrix has zero projective tensor norm. -/
@[simp] theorem piNorm_zero : piNorm (0 : CMatrix (b × e)) = 0 := by
  apply le_antisymm _ (piNorm_nonneg _)
  let d : PiNormDecomposition (0 : CMatrix (b × e)) :=
    ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  simpa [PiNormDecomposition.cost, d] using piNorm_le_cost d

private def decompositionOfLift {x : MatrixPiTensor b e} (p : x.lifts) :
    PiNormDecomposition (matrixPiTensorEquiv b e x) where
  length := p.val.toList.length
  left j := (p.val.toList.get j).1 • (p.val.toList.get j).2 (.inl ())
  right j := (p.val.toList.get j).2 (.inr ())
  sum_eq := by
    have hp := (PiTensorProduct.mem_lifts_iff x p.val).mp p.property
    have hm := congrArg (matrixPiTensorEquiv b e) hp
    rw [← List.sum_map_hom] at hm
    rw [← List.ofFn_get p.val.toList, List.map_ofFn, List.sum_ofFn] at hm
    simp only [Function.comp_apply, map_smul, matrixPiTensorEquiv_tprod] at hm
    calc
      _ = ∑ j, (p.val.toList.get j).1 • Matrix.kronecker
          ((p.val.toList.get j).2 (.inl ())) ((p.val.toList.get j).2 (.inr ())) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Matrix.smul_kronecker _ _ _
      _ = _ := hm
private theorem decompositionOfLift_cost {x : MatrixPiTensor b e} (p : x.lifts) :
    (decompositionOfLift p).cost = PiTensorProduct.projectiveSeminormAux p.val := by
  rw [PiTensorProduct.projectiveSeminormAux, ← List.ofFn_get p.val.toList,
    List.map_ofFn, List.sum_ofFn]
  unfold PiNormDecomposition.cost decompositionOfLift
  apply Finset.sum_congr rfl
  intro j _
  change ‖(p.val.toList.get j).1 • ((p.val.toList.get j).2 (.inl ()) : CMatrix b)‖ *
    ‖(p.val.toList.get j).2 (.inr ())‖ = _
  have h := norm_smul (p.val.toList.get j).1
    ((p.val.toList.get j).2 (.inl ()) : CMatrix b)
  rw [h]
  simp only [Function.comp_apply, Fintype.prod_sum_type, Fintype.prod_unique]
  exact mul_assoc _ _ _
/-- Every bipartite matrix admits a finite Kronecker decomposition. -/
theorem nonempty_piNormDecomposition (Z : CMatrix (b × e)) :
    Nonempty (PiNormDecomposition Z) := by
  obtain ⟨p, hp⟩ := PiTensorProduct.nonempty_lifts ((matrixPiTensorEquiv b e).symm Z)
  exact ⟨(matrixPiTensorEquiv b e).apply_symm_apply Z ▸ decompositionOfLift ⟨p, hp⟩⟩

private theorem piNorm_costs_nonempty (Z : CMatrix (b × e)) :
    (Set.range fun d : PiNormDecomposition Z => d.cost).Nonempty := by
  have := nonempty_piNormDecomposition Z
  exact Set.range_nonempty _

/-- The projective tensor norm dominates the bipartite operator norm. -/
theorem norm_le_piNorm (Z : CMatrix (b × e)) : ‖Z‖ ≤ piNorm Z := by
  apply le_csInf (piNorm_costs_nonempty Z)
  rintro _ ⟨d, rfl⟩
  exact d.norm_le_cost

/-- The projective tensor norm vanishes exactly on the zero matrix. -/
@[simp] theorem piNorm_eq_zero {Z : CMatrix (b × e)} : piNorm Z = 0 ↔ Z = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm (h ▸ norm_le_piNorm Z) (norm_nonneg Z))
  · rintro rfl
    exact piNorm_zero

private theorem projectiveSeminorm_symm_kronecker_le (X : CMatrix b) (Y : CMatrix e) :
    PiTensorProduct.projectiveSeminorm ((matrixPiTensorEquiv b e).symm
      (Matrix.kronecker X Y)) ≤ ‖X‖ * ‖Y‖ := by
  let f : ∀ i, MatrixPiFactor b e i := fun | .inl _ => X | .inr _ => Y
  have hf : (matrixPiTensorEquiv b e).symm (Matrix.kronecker X Y) =
      PiTensorProduct.tprod ℂ f := by
    apply (matrixPiTensorEquiv b e).injective
    rw [LinearEquiv.apply_symm_apply, matrixPiTensorEquiv_tprod]
  rw [hf]
  -- mathlib v4.34 restated `projectiveSeminorm_tprod_le` with the instance norm
  -- (new `fast_instance%` chain), so `convert … using 1` no longer closes the
  -- coe↔norm gap; route through a transitive refinement instead.
  refine le_trans (PiTensorProduct.projectiveSeminorm_tprod_le f) ?_
  simp only [Fintype.prod_sum_type, Fintype.prod_unique]
  rfl

/-- The matrix infimum is precisely Mathlib's projective seminorm under the
canonical tensor equivalence. No minimizer is used in this identification. -/
theorem piNorm_eq_projectiveSeminorm (Z : CMatrix (b × e)) :
    piNorm Z = PiTensorProduct.projectiveSeminorm ((matrixPiTensorEquiv b e).symm Z) := by
  apply le_antisymm
  · change piNorm Z ≤ ⨅ p : ((matrixPiTensorEquiv b e).symm Z).lifts,
      PiTensorProduct.projectiveSeminormAux p.val
    apply le_ciInf
    intro p
    have h := piNorm_le_cost (decompositionOfLift p)
    rw [decompositionOfLift_cost, LinearEquiv.apply_symm_apply] at h
    exact h
  · apply le_csInf (piNorm_costs_nonempty Z)
    rintro _ ⟨d, rfl⟩
    conv_lhs => rw [← d.sum_eq, map_sum]
    calc
      _ ≤ ∑ j, PiTensorProduct.projectiveSeminorm
          ((matrixPiTensorEquiv b e).symm (Matrix.kronecker (d.left j) (d.right j))) :=
        Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
      _ ≤ d.cost := Finset.sum_le_sum fun j _ =>
        projectiveSeminorm_symm_kronecker_le (d.left j) (d.right j)

/-- The triangle inequality for the matrix projective norm. -/
theorem piNorm_add_le (X Y : CMatrix (b × e)) : piNorm (X + Y) ≤ piNorm X + piNorm Y := by
  simp only [piNorm_eq_projectiveSeminorm, map_add]
  exact map_add_le_add _ _ _
/-- Absolute homogeneity for complex scalar multiplication. -/
theorem piNorm_smul (c : ℂ) (Z : CMatrix (b × e)) : piNorm (c • Z) = ‖c‖ * piNorm Z := by
  simp only [piNorm_eq_projectiveSeminorm, map_smul, map_smul_eq_mul]
/-- The projective norm of a finite sum is bounded by the sum of projective norms. -/
theorem piNorm_sum_le {ι : Type*} (s : Finset ι) (Z : ι → CMatrix (b × e)) :
    piNorm (∑ i ∈ s, Z i) ≤ ∑ i ∈ s, piNorm (Z i) :=
  Finset.le_sum_of_subadditive _ piNorm_zero.le piNorm_add_le s Z
/-- The projective norm is a cross norm for the local L2 operator norms. -/
theorem piNorm_kronecker (X : CMatrix b) (Y : CMatrix e) :
    piNorm (Matrix.kronecker X Y) = ‖X‖ * ‖Y‖ := by
  apply le_antisymm
  · let d : PiNormDecomposition (Matrix.kronecker X Y) :=
      ⟨1, fun _ => X, fun _ => Y, by simp⟩
    simpa [PiNormDecomposition.cost, d] using piNorm_le_cost d
  · simpa only [matrix_l2_opNorm_kronecker] using norm_le_piNorm (Matrix.kronecker X Y)
/-- Any finite Kronecker expansion bounds the projective norm by its cost. -/
theorem piNorm_le_sum_norm_mul_norm {ι : Type*} [Fintype ι]
    (X : ι → CMatrix b) (Y : ι → CMatrix e) :
    piNorm (∑ j, Matrix.kronecker (X j) (Y j)) ≤ ∑ j, ‖X j‖ * ‖Y j‖ := by
  simpa only [piNorm_kronecker] using piNorm_sum_le Finset.univ (fun j => Matrix.kronecker (X j) (Y j))
/-- A strict projective-norm budget admits a finite decomposition below that budget. -/
theorem exists_piNormDecomposition_cost_lt (Z : CMatrix (b × e)) {Γ : ℝ}
    (hΓ : piNorm Z < Γ) : ∃ d : PiNormDecomposition Z, d.cost < Γ := by
  have := nonempty_piNormDecomposition Z
  obtain ⟨c, ⟨d, rfl⟩, hd⟩ := exists_lt_of_csInf_lt
    (Set.range_nonempty (fun d : PiNormDecomposition Z => d.cost)) hΓ
  exact ⟨d, hd⟩
/-- Every positive slack admits a finite decomposition within that slack of the infimum. -/
theorem exists_piNormDecomposition_cost_le_add (Z : CMatrix (b × e)) {ε : ℝ}
    (hε : 0 < ε) : ∃ d : PiNormDecomposition Z, d.cost ≤ piNorm Z + ε := by
  obtain ⟨d, hd⟩ := exists_piNormDecomposition_cost_lt Z (lt_add_of_pos_right _ hε)
  exact ⟨d, hd.le⟩
/-- Two-way epsilon-slack characterization of a projective-norm upper bound.
This replaces compactness-based attainment without assuming a minimizer
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:376-383]. -/
theorem piNorm_le_iff_forall_pos_exists_cost_le (Z : CMatrix (b × e)) (Γ : ℝ) :
    piNorm Z ≤ Γ ↔ ∀ ε > 0, ∃ d : PiNormDecomposition Z, d.cost ≤ Γ + ε := by
  constructor
  · intro h ε hε
    obtain ⟨d, hd⟩ := exists_piNormDecomposition_cost_le_add Z hε
    exact ⟨d, hd.trans (_root_.add_le_add h le_rfl)⟩
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨d, hd⟩ := h ε hε
    exact (piNorm_le_cost d).trans hd
section DimensionBound

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
private def coordinateEmbedding (f : n → m) : Matrix m n ℂ :=
  fun i j => if i = f j then 1 else 0
omit [Fintype n] in
private theorem coordinateEmbedding_gram (f : n → m) (hf : Function.Injective f) :
    (coordinateEmbedding f)ᴴ * coordinateEmbedding f = 1 := by
  ext i j
  simp [coordinateEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    hf.eq_iff, eq_comm]
private theorem matrix_one_norm_le : ‖(1 : CMatrix n)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by simp)
private theorem coordinateEmbedding_norm_le (f : n → m) (hf : Function.Injective f) :
    ‖coordinateEmbedding f‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (coordinateEmbedding f)
  rw [coordinateEmbedding_gram f hf] at h
  have h1 := matrix_one_norm_le (n := n)
  nlinarith [norm_nonneg (coordinateEmbedding f)]
omit [Fintype n] [DecidableEq n] in
private theorem compression_eq (f g : n → m) (Z : CMatrix m) :
    (coordinateEmbedding f)ᴴ * Z * coordinateEmbedding g = Z.submatrix f g := by
  ext i j
  simp [coordinateEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]
private theorem submatrix_norm_le (f g : n → m) (hf : Function.Injective f)
    (hg : Function.Injective g) (Z : CMatrix m) : ‖Z.submatrix f g‖ ≤ ‖Z‖ := by
  rw [← compression_eq]
  calc
    _ ≤ (‖(coordinateEmbedding f)ᴴ‖ * ‖Z‖) * ‖coordinateEmbedding g‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * ‖Z‖) * 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      gcongr
      · exact coordinateEmbedding_norm_le f hf
      · exact coordinateEmbedding_norm_le g hg
    _ = _ := by ring
private theorem matrix_single_norm_le (i j : n) :
    ‖(Matrix.single i j 1 : CMatrix n)‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (Matrix.single i j (1 : ℂ))
  simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same,
    one_mul] at h
  have he : (Matrix.single j j 1 : CMatrix n) = Matrix.diagonal (Pi.single j 1) := by
    ext a b
    simp [Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
    grind
  rw [he, Matrix.l2_opNorm_diagonal] at h
  have hv : ‖(Pi.single j 1 : n → ℂ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    by_cases h : k = j <;> simp [h]
  nlinarith [norm_nonneg (Matrix.single i j (1 : ℂ))]
/-- The left matrix-unit expansion gives the squared left-dimension bound
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:385-390]. -/
theorem piNorm_le_card_left_sq_mul_norm (Z : CMatrix (b × e)) :
    piNorm Z ≤ (Fintype.card b : ℝ) ^ 2 * ‖Z‖ := by
  have hexp : (∑ ij : b × b, Matrix.kronecker (Matrix.single ij.1 ij.2 1)
      (Z.submatrix (fun k => (ij.1, k)) (fun k => (ij.2, k)))) = Z := by
    ext ⟨i,a⟩ ⟨j,c⟩
    simp [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.single_apply, Matrix.submatrix_apply, ite_and]
  calc
    piNorm Z = piNorm (∑ ij : b × b, Matrix.kronecker (Matrix.single ij.1 ij.2 1)
        (Z.submatrix (fun k => (ij.1,k)) (fun k => (ij.2,k)))) := congrArg piNorm hexp.symm
    _ ≤ ∑ ij : b × b, ‖(Matrix.single ij.1 ij.2 1 : CMatrix b)‖ *
        ‖Z.submatrix (fun k => (ij.1,k)) (fun k => (ij.2,k))‖ := piNorm_le_sum_norm_mul_norm _ _
    _ ≤ ∑ _ij : b × b, ‖Z‖ := by
      apply Finset.sum_le_sum
      intro ij _
      calc
        _ ≤ 1 * ‖Z‖ := by
          gcongr
          · exact matrix_single_norm_le _ _
          · exact submatrix_norm_le _ _ (fun _ _ h => Prod.mk.inj h |>.2)
              (fun _ _ h => Prod.mk.inj h |>.2) Z
        _ = _ := one_mul _
    _ = _ := by simp [pow_two, mul_assoc]
/-- The right matrix-unit expansion gives the squared right-dimension bound
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:385-390]. -/
theorem piNorm_le_card_right_sq_mul_norm (Z : CMatrix (b × e)) :
    piNorm Z ≤ (Fintype.card e : ℝ) ^ 2 * ‖Z‖ := by
  have hexp : (∑ ij : e × e, Matrix.kronecker
      (Z.submatrix (fun k => (k,ij.1)) (fun k => (k,ij.2)))
      (Matrix.single ij.1 ij.2 1)) = Z := by
    ext ⟨i,a⟩ ⟨j,c⟩
    simp [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.single_apply, Matrix.submatrix_apply, ite_and]
  calc
    piNorm Z = piNorm (∑ ij : e × e, Matrix.kronecker
        (Z.submatrix (fun k => (k,ij.1)) (fun k => (k,ij.2)))
        (Matrix.single ij.1 ij.2 1)) := congrArg piNorm hexp.symm
    _ ≤ ∑ ij : e × e, ‖Z.submatrix (fun k => (k,ij.1)) (fun k => (k,ij.2))‖ *
        ‖(Matrix.single ij.1 ij.2 1 : CMatrix e)‖ := piNorm_le_sum_norm_mul_norm _ _
    _ ≤ ∑ _ij : e × e, ‖Z‖ := by
      apply Finset.sum_le_sum
      intro ij _
      calc
        _ ≤ ‖Z‖ * 1 := by
          gcongr
          · exact submatrix_norm_le _ _ (fun _ _ h => Prod.mk.inj h |>.1)
              (fun _ _ h => Prod.mk.inj h |>.1) Z
          · exact matrix_single_norm_le _ _
        _ = _ := mul_one _
    _ = _ := by simp [pow_two, mul_assoc]
/-- Lemma 2: the projective tensor norm is at most the smaller squared local
dimension times the operator norm, for every bipartite matrix
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:385-390]. -/
theorem piNorm_le_min_card_sq_mul_norm (Z : CMatrix (b × e)) :
    piNorm Z ≤ min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2) * ‖Z‖ := by
  rw [min_mul_of_nonneg _ _ (norm_nonneg Z)]
  exact le_min (piNorm_le_card_left_sq_mul_norm Z) (piNorm_le_card_right_sq_mul_norm Z)
end DimensionBound

private theorem normalized_matrix_norm_le (X : CMatrix b) :
    ‖NormedSpace.normalize X‖ ≤ 1 := by
  by_cases h : X = 0
  · simp [h]
  · exact (NormedSpace.norm_normalize h).le
private theorem normalized_kronecker (X : CMatrix b) (Y : CMatrix e) :
    (‖X‖ * ‖Y‖) • Matrix.kronecker (NormedSpace.normalize X) (NormedSpace.normalize Y) =
      Matrix.kronecker X Y := by
  calc
    _ = ‖X‖ • (‖Y‖ • Matrix.kronecker (NormedSpace.normalize X) (NormedSpace.normalize Y)) :=
      mul_smul _ _ _
    _ = ‖X‖ • Matrix.kronecker (NormedSpace.normalize X) (‖Y‖ • NormedSpace.normalize Y) :=
      congrArg (fun T : CMatrix (b × e) => ‖X‖ • T)
        (Matrix.kronecker_smul ‖Y‖ (NormedSpace.normalize X) (NormedSpace.normalize Y)).symm
    _ = Matrix.kronecker (‖X‖ • NormedSpace.normalize X) (‖Y‖ • NormedSpace.normalize Y) :=
      (Matrix.smul_kronecker ‖X‖ (NormedSpace.normalize X) _).symm
    _ = _ := by rw [NormedSpace.norm_smul_normalize, NormedSpace.norm_smul_normalize]
/-- A strict projective-norm budget yields a convex combination of Kronecker
products of contractions, scaled by that budget. A zero term absorbs unused
weight; no optimal decomposition is required
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:376-383]. -/
theorem exists_convex_kronecker_of_piNorm_lt (Z : CMatrix (b × e)) {Γ : ℝ}
    (hΓ : piNorm Z < Γ) :
    ∃ (m : ℕ) (p : Fin m → ℝ) (X : Fin m → CMatrix b) (Y : Fin m → CMatrix e),
      (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
      (∀ j, ‖X j‖ ≤ 1) ∧ (∀ j, ‖Y j‖ ≤ 1) ∧
      Z = Γ • ∑ j, p j • Matrix.kronecker (X j) (Y j) := by
  have hpos : 0 < Γ := (piNorm_nonneg Z).trans_lt hΓ
  obtain ⟨d, hd⟩ := exists_piNormDecomposition_cost_lt Z hΓ
  let p : Fin (d.length + 1) → ℝ :=
    Fin.cases (1 - d.cost / Γ) (fun j => (‖d.left j‖ * ‖d.right j‖) / Γ)
  let X : Fin (d.length + 1) → CMatrix b :=
    Fin.cases 0 (fun j => NormedSpace.normalize (d.left j))
  let Y : Fin (d.length + 1) → CMatrix e :=
    Fin.cases 0 (fun j => NormedSpace.normalize (d.right j))
  refine ⟨d.length + 1, p, X, Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · dsimp [p]
      exact sub_nonneg.mpr ((div_le_one hpos).mpr hd.le)
    · exact div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpos.le
  · simp only [p, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      ← Finset.sum_div, PiNormDecomposition.cost]
    ring
  · intro j
    exact Fin.cases (by simp [X]) (fun i => normalized_matrix_norm_le (d.left i)) j
  · intro j
    exact Fin.cases (by simp [Y]) (fun i => normalized_matrix_norm_le (d.right i)) j
  · simp only [p, X, Y, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    have hz : Matrix.kronecker (0 : CMatrix b) (0 : CMatrix e) = 0 :=
      Matrix.zero_kronecker _
    rw [hz, smul_zero, zero_add, Finset.smul_sum]
    conv_rhs =>
      arg 2
      ext j
      rw [smul_smul, mul_div_cancel₀ _ hpos.ne', normalized_kronecker]
    exact d.sum_eq.symm
end

end QIT
