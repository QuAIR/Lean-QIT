/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.PolyApprox.Basic

/-!
# Tensor norm bounds for local complementary projectors

Finite Kronecker decompositions and positive slack give the product bound used in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530].
The single-register estimate uses the dimension bound at lines 385-390.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section
universe u
variable {b e : Type u} [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]

private theorem le_piNorm_mul_of_cost {Z : CMatrix (b × e)} {a c : ℝ}
    (hc : 0 ≤ c) (h : ∀ d : PiNormDecomposition Z, a ≤ d.cost * c) :
    a ≤ piNorm Z * c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc1 : 0 < c + 1 := by positivity
  obtain ⟨d, hd⟩ := exists_piNormDecomposition_cost_le_add Z (div_pos hε hc1)
  have hslack : ε / (c + 1) * c ≤ ε := by
    calc
      _ ≤ ε / (c + 1) * (c + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hε.le hc1.le)
      _ = ε := div_mul_cancel₀ _ hc1.ne'
  calc
    a ≤ d.cost * c := h d
    _ ≤ (piNorm Z + ε / (c + 1)) * c := mul_le_mul_of_nonneg_right hd hc
    _ ≤ piNorm Z * c + ε := by nlinarith

private theorem piNorm_mul_le_costs {X Y : CMatrix (b × e)}
    (dx : PiNormDecomposition X) (dy : PiNormDecomposition Y) :
    piNorm (X * Y) ≤ dx.cost * dy.cost := by
  conv_lhs => rw [← dx.sum_eq, ← dy.sum_eq, Finset.sum_mul]
  calc
    _ ≤ ∑ i, piNorm (Matrix.kronecker (dx.left i) (dx.right i) *
        ∑ j, Matrix.kronecker (dy.left j) (dy.right j)) := piNorm_sum_le _ _
    _ ≤ ∑ i, ∑ j, (‖dx.left i‖ * ‖dy.left j‖) *
        (‖dx.right i‖ * ‖dy.right j‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.mul_sum]
      refine (piNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have heq : Matrix.kronecker (dx.left i) (dx.right i) *
          Matrix.kronecker (dy.left j) (dy.right j) =
          Matrix.kronecker (dx.left i * dy.left j) (dx.right i * dy.right j) :=
        (Matrix.mul_kronecker_mul _ _ _ _).symm
      rw [heq, piNorm_kronecker]
      exact mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = dx.cost * dy.cost := by
      simp only [PiNormDecomposition.cost]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Submultiplicativity of the projective norm, without assuming that its
infimum is attained. -/
theorem piNorm_mul_le (X Y : CMatrix (b × e)) :
    piNorm (X * Y) ≤ piNorm X * piNorm Y := by
  apply le_piNorm_mul_of_cost (piNorm_nonneg Y)
  intro dx
  rw [mul_comm dx.cost]
  apply le_piNorm_mul_of_cost dx.cost_nonneg
  intro dy
  simpa only [mul_comm dy.cost] using piNorm_mul_le_costs dx dy

namespace QuantumPolyApprox

noncomputable local instance complexMatrixCStarAlgebra {ι : Type*}
    [Fintype ι] [DecidableEq ι] : CStarAlgebra (CMatrix ι) where

/-- Relabeling a finite matrix preserves its L2 operator norm, including
empty carriers. This also transports tensor-block approximation bounds. -/
theorem matrix_reindex_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι ≃ κ) (M : CMatrix ι) :
    ‖Matrix.reindex f f M‖ = ‖M‖ := by
  let fstar : CMatrix ι ≃⋆ₐ[ℂ] CMatrix κ :=
    { Matrix.reindexAlgEquiv ℂ ℂ f with
      map_star' := fun _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Isometry fstar := NonUnitalStarAlgHom.isometry _ fstar.injective
  exact hf.norm_map_of_map_zero (map_zero _) M

private theorem liftAt_norm_le {n : ℕ} {a : Type u} [Fintype a] [DecidableEq a]
    (i : Fin (n + 1)) (M : CMatrix a) :
    ‖WireFam.liftAt (fun _ : Fin (n + 1) => a) i M‖ ≤ ‖M‖ := by
  unfold WireFam.liftAt WireFam.matReindex
  rw [show (Matrix.reindex (WireFam.extractAt (fun _ : Fin (n + 1) => a) i)
      (WireFam.extractAt (fun _ : Fin (n + 1) => a) i)).symm =
      Matrix.reindex (WireFam.extractAt (fun _ : Fin (n + 1) => a) i).symm
        (WireFam.extractAt (fun _ : Fin (n + 1) => a) i).symm from rfl,
    matrix_reindex_norm]
  change ‖Matrix.kronecker M (1 : CMatrix (Fin n → a))‖ ≤ ‖M‖
  rw [matrix_l2_opNorm_kronecker]
  simpa using mul_le_mul_of_nonneg_left
    (IsStarProjection.norm_le (1 : CMatrix (Fin n → a)) (IsStarProjection.one _)) (norm_nonneg M)

/-- Regrouping a single-register Kronecker product gives the Kronecker
product of the two local lifts. -/
theorem pairReindex_liftAt_kronecker {n : ℕ} (i : Fin (n + 1))
    (X : CMatrix b) (Y : CMatrix e) :
    pairReindex (n + 1)
        (WireFam.liftAt (fun _ : Fin (n + 1) => b × e) i (Matrix.kronecker X Y)) =
      Matrix.kronecker (WireFam.liftAt (fun _ : Fin (n + 1) => b) i X)
        (WireFam.liftAt (fun _ : Fin (n + 1) => e) i Y) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  change WireFam.liftAt (fun _ : Fin (n + 1) => b × e) i (Matrix.kronecker X Y)
    (fun k => (x k, y k)) (fun k => (x' k, y' k)) = _
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, WireFam.liftAt_apply_prod]
  have hp : (∏ j : Fin n,
      if (x (i.succAbove j), y (i.succAbove j)) =
        (x' (i.succAbove j), y' (i.succAbove j)) then (1 : ℂ) else 0) =
      (∏ j : Fin n, if x (i.succAbove j) = x' (i.succAbove j) then (1 : ℂ) else 0) *
      (∏ j : Fin n, if y (i.succAbove j) = y' (i.succAbove j) then (1 : ℂ) else 0) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hx : x (i.succAbove j) = x' (i.succAbove j) <;>
      by_cases hy : y (i.succAbove j) = y' (i.succAbove j) <;> simp [hx, hy]
  rw [hp]
  ring

/-- Lifting a bipartite matrix to one register contracts its projective norm.
This includes empty local index types. -/
theorem piNorm_pairReindex_liftAt_le {n : ℕ} (i : Fin (n + 1))
    (Z : CMatrix (b × e)) :
    piNorm (pairReindex (n + 1)
      (WireFam.liftAt (fun _ : Fin (n + 1) => b × e) i Z)) ≤ piNorm Z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d, hd⟩ := exists_piNormDecomposition_cost_le_add Z hε
  have heq : pairReindex (n + 1)
      (WireFam.liftAt (fun _ : Fin (n + 1) => b × e) i Z) =
      ∑ j, Matrix.kronecker
        (WireFam.liftAt (fun _ : Fin (n + 1) => b) i (d.left j))
        (WireFam.liftAt (fun _ : Fin (n + 1) => e) i (d.right j)) := by
    conv_lhs => rw [← d.sum_eq]
    have hsum : WireFam.liftAt (fun _ : Fin (n + 1) => b × e) i
        (∑ j, Matrix.kronecker (d.left j) (d.right j)) =
        ∑ j, WireFam.liftAt (fun _ : Fin (n + 1) => b × e) i
          (Matrix.kronecker (d.left j) (d.right j)) := by
      ext x y
      simp only [WireFam.liftAt_apply, Matrix.sum_apply, Finset.sum_mul]
    rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun j _ => pairReindex_liftAt_kronecker i _ _
  rw [heq]
  refine (piNorm_le_sum_norm_mul_norm _ _).trans (le_trans ?_ hd)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul (liftAt_norm_le i _) (liftAt_norm_le i _) (norm_nonneg _)
    (norm_nonneg _)

/-- Each local complementary projector has the single-use dimension bound
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:385-390]. -/
theorem piNorm_localDefect_le {n : ℕ} (P : CMatrix (b × e))
    (hP : P.IsHermitian) (hP2 : P * P = P) (i : Fin (n + 1)) :
    piNorm (localDefect P i) ≤
      min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2) := by
  have hproj : IsStarProjection P := ⟨hP2, hP⟩
  have hn : ‖1 - P‖ ≤ 1 := hproj.one_sub.norm_le _
  unfold localDefect
  rw [WireFam.deltaAt_eq_liftAt_one_sub]
  calc
    _ ≤ piNorm (1 - P) := piNorm_pairReindex_liftAt_le i _
    _ ≤ min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2) * ‖1 - P‖ :=
      piNorm_le_min_card_sq_mul_norm _
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left hn (le_min (sq_nonneg _) (sq_nonneg _))

/-- The projective norm of the bipartite identity is at most one, including
empty local index types. -/
theorem piNorm_one_le : piNorm (1 : CMatrix (b × e)) ≤ 1 := by
  have h : Matrix.kronecker (1 : CMatrix b) (1 : CMatrix e) = 1 :=
    Matrix.one_kronecker_one
  rw [← h, piNorm_kronecker]
  simpa using mul_le_mul
    (IsStarProjection.norm_le (1 : CMatrix b) (IsStarProjection.one _))
    (IsStarProjection.norm_le (1 : CMatrix e) (IsStarProjection.one _)) (norm_nonneg _)
    (show (0 : ℝ) ≤ 1 by norm_num)

/-- A product over selected complementary registers costs at most one
single-use dimension factor per selected register. -/
theorem piNorm_noncommProd_localDefect_le {n : ℕ} (P : CMatrix (b × e))
    (hP : P.IsHermitian) (hP2 : P * P = P) (s : Finset (Fin (n + 1)))
    (hcomm : (s : Set (Fin (n + 1))).Pairwise (Function.onFun Commute (localDefect P))) :
    piNorm (s.noncommProd (localDefect P) hcomm) ≤
      (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simpa using (piNorm_one_le (b := Fin (n + 1) → b) (e := Fin (n + 1) → e))
  | @insert i s hi ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Finset.card_insert_of_notMem hi,
      pow_succ']
    exact (piNorm_mul_le _ _).trans
      (mul_le_mul (piNorm_localDefect_le P hP hP2 i) (ih _) (piNorm_nonneg _)
        (le_min (sq_nonneg _) (sq_nonneg _)))

end QuantumPolyApprox
end
end QIT
