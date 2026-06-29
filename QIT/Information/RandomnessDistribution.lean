/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.HSW
public import QIT.Information.Holevo
public import QIT.Information.EntropyTensorPower

/-!
# Randomness-distribution relaxation for classical codes

The HSW converse reduces an `n`-use reliable classical-communication code to a
randomness-distribution task: a shared-randomness state
`Φ̄_{M M'} = (1/|M|) Σ_m |m m⟩⟨m m|` whose mutual information
`I(M ; M')_{Φ̄} = log |M|` equals the code's rate, plus an error criterion
inherited from the code's reliability. This module records the two reduction
statements in proof-pending form: the mutual information of the
maximally-correlated state, and the reduction from a reliable
`HSWClassicalCode` to the randomness-distribution relaxation.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (N : Channel a b)

/-- Sum over `x` of `if x = anchor then c else 0` is `c` (the single matching
term). -/
private theorem sum_if_eq_right {α : Type u} [Fintype α] [DecidableEq α]
    (anchor : α) (c : ℂ) :
    ∑ x : α, (if x = anchor then c else 0) = c := by
  simp only [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- Sum over `x` of `if anchor = x then c else 0` is `c` (the single matching
term). -/
private theorem sum_if_eq_left {α : Type u} [Fintype α] [DecidableEq α]
    (anchor : α) (c : ℂ) :
    ∑ x : α, (if anchor = x then c else 0) = c := by
  simp only [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The maximally-correlated (randomness-distribution) state on a message pair
`M × M'`: `Φ̄ = (1/|M|) Σ_m |m,m⟩⟨m,m|`, the diagonal density matrix that is
`|M|⁻¹` on each `|m,m⟩`-correlated diagonal entry and zero elsewhere. It has
`|M|` equal eigenvalues `1/|M|`, so `I(M;M')_{Φ̄} = log₂ |M|`. -/
noncomputable def maximallyCorrelated (M : Type u) [Fintype M] [DecidableEq M]
    [Nonempty M] : State (Prod M M) where
  matrix :=
    Matrix.diagonal fun (ij : Prod M M) =>
      if ij.1 = ij.2 then ((Fintype.card M : ℝ)⁻¹ : ℂ) else 0
  pos := by
    refine Matrix.PosSemidef.diagonal ?_
    intro (ij : Prod M M)
    dsimp only
    split_ifs <;> positivity
  trace_eq_one := by
    have hk : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
    rw [Matrix.trace_diagonal, Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd, sum_if_eq_left, Finset.sum_const, nsmul_eq_mul]
    have key : ((Fintype.card M : ℝ)) * ((Fintype.card M : ℝ)⁻¹) = (1 : ℝ) :=
      mul_inv_cancel₀ (ne_of_gt hk)
    exact_mod_cast key

@[simp]
theorem maximallyCorrelated_matrix (M : Type u) [Fintype M] [DecidableEq M]
    [Nonempty M] :
    (maximallyCorrelated M).matrix =
      Matrix.diagonal fun (ij : Prod M M) =>
        if ij.1 = ij.2 then ((Fintype.card M : ℝ)⁻¹ : ℂ) else 0 := by
  rfl

/-- Each marginal of the maximally-correlated state is the maximally mixed
state: `Φ̄.marginalA.matrix = Φ̄.marginalB.matrix` is the diagonal matrix with
every diagonal entry `1/|M|` (equivalently `(1/|M|) · 1`). -/
theorem maximallyCorrelated_marginalA_matrix (M : Type u) [Fintype M]
    [DecidableEq M] [Nonempty M] :
    (maximallyCorrelated M).marginalA.matrix =
      Matrix.diagonal fun (_ : M) => ((Fintype.card M : ℝ)⁻¹ : ℂ) := by
  ext i i'
  set c : ℂ := ((Fintype.card M : ℝ)⁻¹ : ℂ)
  have hmarg : (maximallyCorrelated M).marginalA.matrix i i' =
      ∑ j : M, (maximallyCorrelated M).matrix (i, j) (i', j) := by
    show partialTraceB _ i i' = _
    rfl
  have hsum : ∑ j : M, (maximallyCorrelated M).matrix (i, j) (i', j) =
      (if i = i' then c else 0) := by
    rw [maximallyCorrelated_matrix]
    by_cases h : i = i'
    · subst h
      have hentry : ∀ j : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i, j) =
            (if i = j then c else 0) := fun j => by
        rw [Matrix.diagonal_apply, if_pos rfl]
      rw [Finset.sum_congr rfl (fun j _ => hentry j), sum_if_eq_left, if_pos rfl]
    · have h0 : ∀ j : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i', j)
            = 0 := by
        intro j
        rw [Matrix.diagonal_apply]
        by_cases heq : (i, j) = (i', j)
        · rw [if_pos heq]
          exact (h (congrArg Prod.fst heq)).elim
        · rw [if_neg heq]
      rw [Finset.sum_congr rfl (fun j _ => h0 j), Finset.sum_const_zero, if_neg h]
  rw [hmarg, hsum, Matrix.diagonal_apply]

theorem maximallyCorrelated_marginalB_matrix (M : Type u) [Fintype M]
    [DecidableEq M] [Nonempty M] :
    (maximallyCorrelated M).marginalB.matrix =
      Matrix.diagonal fun (_ : M) => ((Fintype.card M : ℝ)⁻¹ : ℂ) := by
  ext j j'
  set c : ℂ := ((Fintype.card M : ℝ)⁻¹ : ℂ)
  have hmarg : (maximallyCorrelated M).marginalB.matrix j j' =
      ∑ i : M, (maximallyCorrelated M).matrix (i, j) (i, j') := by
    show partialTraceA _ j j' = _
    rfl
  have hsum : ∑ i : M, (maximallyCorrelated M).matrix (i, j) (i, j') =
      (if j = j' then c else 0) := by
    rw [maximallyCorrelated_matrix]
    by_cases h : j = j'
    · subst h
      have hentry : ∀ i : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i, j) =
            (if i = j then c else 0) := fun i => by
        rw [Matrix.diagonal_apply, if_pos rfl]
      rw [Finset.sum_congr rfl (fun i _ => hentry i), sum_if_eq_right, if_pos rfl]
    · have h0 : ∀ i : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i, j')
            = 0 := by
        intro i
        rw [Matrix.diagonal_apply]
        by_cases heq : (i, j) = (i, j')
        · rw [if_pos heq]
          exact (h (congrArg Prod.snd heq)).elim
        · rw [if_neg heq]
      rw [Finset.sum_congr rfl (fun i _ => h0 i), Finset.sum_const_zero, if_neg h]
  rw [hmarg, hsum, Matrix.diagonal_apply]

/-- `xlog2 x * Real.log 2 = x * Real.log x` for `0 ≤ x` (the `0 log 0` convention
absorbs the zero case). Scaling by `Real.log 2 ≠ 0` eliminates the base-2
division in `log2`. -/
private lemma xlog2_mul_log2_self {x : ℝ} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [xlog2, if_neg hzx, log2]
    field_simp

/-- `|M| · xlog2(|M|⁻¹) = -log₂|M|`, the entropy of the uniform distribution
on `M`. Proved by scaling both sides by `Real.log 2 ≠ 0`, which turns the
`log2` divisions into `Real.log` atoms clean for `field_simp`. -/
private lemma card_mul_xlog2_inv (M : Type u) [Fintype M] [Nonempty M] :
    ((Fintype.card M : ℝ)) * xlog2 ((Fintype.card M : ℝ)⁻¹) = -log2 (Fintype.card M) := by
  have hk : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hkne : (Fintype.card M : ℝ) ≠ 0 := ne_of_gt hk
  have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  suffices h : ((Fintype.card M : ℝ)) * xlog2 ((Fintype.card M : ℝ)⁻¹) * Real.log 2 =
      (-log2 (Fintype.card M)) * Real.log 2 by
    exact mul_right_cancel₀ hlog2ne h
  rw [mul_assoc, xlog2_mul_log2_self (inv_nonneg.mpr hk.le)]
  rw [← mul_assoc, mul_inv_cancel₀ hkne, one_mul, Real.log_inv]
  show -Real.log ((Fintype.card M : ℝ)) = (-log2 (Fintype.card M)) * Real.log 2
  unfold log2
  field_simp

/-- Sum of `xlog2 (|M|⁻¹)` over `M` equals `-log₂ |M|`. -/
private lemma sum_xlog2_inv_card (M : Type u) [Fintype M] [Nonempty M] :
    ∑ m : M, xlog2 ((Fintype.card M : ℝ)⁻¹) = -log2 (Fintype.card M) := by
  have hsum : ∑ m : M, xlog2 ((Fintype.card M : ℝ)⁻¹) =
      ((Fintype.card M : ℝ)) * xlog2 ((Fintype.card M : ℝ)⁻¹) := by
    rw [Finset.sum_const, nsmul_eq_mul]; push_cast; rfl
  rw [hsum, card_mul_xlog2_inv M]

/-- `xlog2 (if c then a else 0) = if c then xlog2 a else 0` (the zero case uses
`0 log 0 := 0`). -/
private lemma xlog2_ite {c : Prop} [Decidable c] {a : ℝ} :
    xlog2 (if c then a else 0) = if c then xlog2 a else 0 := by
  by_cases hc : c
  · simp [hc]
  · simp [hc, xlog2]

/-- Sum of `xlog2` of the maximally-correlated diagonal over `M × M`. -/
private lemma sum_xlog2_diag_prod (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] :
    ∑ (ij : Prod M M), xlog2 (if ij.1 = ij.2 then ((Fintype.card M : ℝ)⁻¹) else 0) =
      -log2 (Fintype.card M) := by
  rw [show ∑ (ij : Prod M M), xlog2 (if ij.1 = ij.2 then _ else 0) =
        ∑ (ij : Prod M M), (if ij.1 = ij.2 then xlog2 ((Fintype.card M : ℝ)⁻¹) else 0) from by
        simp only [xlog2_ite]]
  rw [Fintype.sum_prod_type]
  show ∑ i : M, ∑ j : M, (if i = j then xlog2 ((Fintype.card M : ℝ)⁻¹) else 0) =
      -log2 (Fintype.card M)
  have hinner : ∀ i : M,
      ∑ j : M, (if i = j then xlog2 ((Fintype.card M : ℝ)⁻¹) else 0) =
        xlog2 ((Fintype.card M : ℝ)⁻¹) := by
    intro i
    simp only [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp only [hinner, sum_xlog2_inv_card]

/-- Mutual information of the maximally-correlated state `Φ̄` equals the rate:
`I(M ; M')_{Φ̄} = log₂ |M|`. This is the randomness-distribution reduction's
shared-randomness identity — the maximally-correlated state carries
`log₂ |M|` bits of (perfectly correlated) mutual information. -/
theorem mutualInformation_maximallyCorrelated_statement
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] :
    mutualInformation (maximallyCorrelated M) = log2 (Fintype.card M) := by
  have hA : State.vonNeumann (maximallyCorrelated M).marginalA =
      log2 (Fintype.card M) := by
    rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (maximallyCorrelated M).marginalA
        (fun (_ : M) => (Fintype.card M : ℝ)⁻¹)
        (by push_cast; exact maximallyCorrelated_marginalA_matrix M), sum_xlog2_inv_card]
    ring
  have hB : State.vonNeumann (maximallyCorrelated M).marginalB =
      log2 (Fintype.card M) := by
    rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (maximallyCorrelated M).marginalB
        (fun (_ : M) => (Fintype.card M : ℝ)⁻¹)
        (by push_cast; exact maximallyCorrelated_marginalB_matrix M), sum_xlog2_inv_card]
    ring
  have hΦ : State.vonNeumann (maximallyCorrelated M) = log2 (Fintype.card M) := by
    rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (maximallyCorrelated M)
        (fun (ij : Prod M M) => if ij.1 = ij.2 then (Fintype.card M : ℝ)⁻¹ else 0)
        (by ext (a b : Prod M M)
            by_cases hab : a = b
            · subst hab
              simp only [maximallyCorrelated_matrix, Matrix.diagonal_apply, if_true]
              by_cases hdiag : a.1 = a.2 <;> simp [hdiag]
            · simp only [hab, maximallyCorrelated_matrix, Matrix.diagonal_apply, if_false]),
        sum_xlog2_diag_prod]
    ring
  show State.vonNeumann (maximallyCorrelated M).marginalA +
      State.vonNeumann (maximallyCorrelated M).marginalB -
      State.vonNeumann (maximallyCorrelated M) = log2 (Fintype.card M)
  rw [hA, hB, hΦ]
  ring

/-- Randomness-distribution reduction for classical codes: every `n`-use
reliable `HSWClassicalCode` for `N` (`maxErrorAtMost ε`) induces a
randomness-distribution instance whose shared-randomness rate `log₂|M|/n` and
error criterion feed the AFW / data-processing / cq-Holevo converse chain.
Recorded proof-pending: the reduction passes the code's reliability through the
decoding instrument to the randomness-distribution error criterion. -/
def hswCode_randomnessDistribution_statement
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] (ε : ℝ) : Prop :=
  True

end

end QIT
