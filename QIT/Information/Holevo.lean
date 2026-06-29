/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy
public import QIT.Classical.Ensemble
public import QIT.Classical.CQState
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Complex.BigOperators

/-!
# Holevo information and bound

The Holevo information chi(E) of an ensemble and the dimension bound
chi <= log2(dim B).

[Wilde2011Qst, qit-notes.tex:19441-19448].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

/-- Quantum mutual information I(X;B) of a bipartite state. -/
def mutualInformation [DecidableEq ι] (ρ : State (Prod ι a)) : ℝ :=
  State.vonNeumann ρ.marginalA + State.vonNeumann ρ.marginalB
    - State.vonNeumann ρ

namespace Ensemble

/-- The Holevo information chi(E) of an ensemble. -/
def holevoInformation (E : Ensemble ι a) : ℝ :=
  State.vonNeumann E.averageState
    - ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i)

/-- The Holevo information is the entropy of the average state minus the
average entropy. -/
theorem holevoInformation_def (E : Ensemble ι a) :
    E.holevoInformation =
      State.vonNeumann E.averageState
        - ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i) := by
  rfl

/-- Nonnegativity of Holevo information is equivalent to the entropy-concavity
inequality for a finite ensemble. -/
theorem holevoInformation_nonneg_iff_vonNeumann_average_ge_sum (E : Ensemble ι a) :
    0 ≤ E.holevoInformation ↔
      (∑ i, (E.probs i).toReal * State.vonNeumann (E.states i))
        ≤ State.vonNeumann E.averageState := by
  rw [holevoInformation_def]
  exact sub_nonneg

end Ensemble

/-- Eigenvalues of a PSD trace-1 state sum to 1 (real). -/
private lemma state_eigenvalue_sum (ρ : State a) :
    ∑ i, ρ.pos.isHermitian.eigenvalues i = 1 := by
  have hc : (∑ i, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 := by
    exact ρ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
  exact Complex.ofReal_injective (by simpa using hc)

/-- Each eigenvalue of a PSD trace-1 state is at most 1. -/
private lemma state_eigenvalue_le_one (ρ : State a) (i : a) :
    ρ.pos.isHermitian.eigenvalues i ≤ 1 := by
  have hnonneg (j : a) : 0 ≤ ρ.pos.isHermitian.eigenvalues j :=
    ρ.pos.eigenvalues_nonneg j
  have hsum : ∑ j, ρ.pos.isHermitian.eigenvalues j = 1 :=
    state_eigenvalue_sum ρ
  calc ρ.pos.isHermitian.eigenvalues i
      ≤ ρ.pos.isHermitian.eigenvalues i
        + ∑ j ∈ Finset.univ.erase i, ρ.pos.isHermitian.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
    _ = ∑ j, ρ.pos.isHermitian.eigenvalues j :=
          by
            rw [add_comm]
            exact Finset.sum_erase_add (s := Finset.univ)
              (f := fun j => ρ.pos.isHermitian.eigenvalues j) (Finset.mem_univ i)
    _ = 1 := hsum

/-- For x >= 0, x * Real.log x >= x - 1. -/
private lemma xlog_self_ge_sub_one {x : ℝ} (hx : 0 ≤ x) :
    x * Real.log x ≥ x - 1 := by
  rcases lt_or_eq_of_le hx with h | h
  · have hl := Real.one_sub_inv_le_log_of_pos h
    nlinarith [hl, mul_inv_cancel₀ (ne_of_gt h)]
  · rw [← h]
    norm_num

namespace State

/-- Von Neumann entropy is nonnegative: S(rho) >= 0. -/
theorem vonNeumann_nonneg (ρ : State a) : 0 ≤ vonNeumann ρ := by
  let hH : ρ.matrix.IsHermitian := ρ.pos.isHermitian
  have hnonneg (i : a) : 0 ≤ hH.eigenvalues i := ρ.pos.eigenvalues_nonneg i
  have hle1 (i : a) : hH.eigenvalues i ≤ 1 := state_eigenvalue_le_one ρ i
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  by_cases hl : hH.eigenvalues i = 0
  · simp only [xlog2, if_pos hl]
    exact le_rfl
  · simp only [xlog2, if_neg hl]
    have hpos : 0 < hH.eigenvalues i := lt_of_le_of_ne (hnonneg i) (Ne.symm hl)
    have hlog2le : log2 (hH.eigenvalues i) ≤ 0 := by
      unfold log2
      exact div_nonpos_of_nonpos_of_nonneg
        (Real.log_nonpos (hnonneg i) (hle1 i)) (le_of_lt (Real.log_pos one_lt_two))
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) hlog2le

/-- Von Neumann entropy is bounded by log2(dim).

S(rho) <= log2(Fintype.card a).
-/
theorem vonNeumann_le_log_card (ρ : State a) :
    vonNeumann ρ ≤ log2 (Fintype.card a) := by
  let hH : ρ.matrix.IsHermitian := ρ.pos.isHermitian
  have hnonneg (i : a) : 0 ≤ hH.eigenvalues i := ρ.pos.eigenvalues_nonneg i
  have hsum : ∑ i, hH.eigenvalues i = 1 := state_eigenvalue_sum ρ
  have hcard_pos : 0 < Fintype.card a := by
    by_contra hcard
    have hcard_zero : Fintype.card a = 0 := Nat.eq_zero_of_not_pos hcard
    haveI : IsEmpty a := Fintype.card_eq_zero_iff.mp hcard_zero
    have hsum_zero : ∑ i, hH.eigenvalues i = 0 := by simp
    have : (0 : ℝ) = 1 := hsum_zero.symm.trans hsum
    norm_num at this
  have hnreal : (0 : ℝ) < Fintype.card a := Nat.cast_pos.mpr hcard_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- Key identity: xlog2(x) * Real.log 2 = x * Real.log x for x >= 0
  have hxlog2_mul (x : ℝ) (hx : 0 ≤ x) : xlog2 x * Real.log 2 = x * Real.log x := by
    by_cases h : x = 0
    · simp [xlog2, h]
    · simp only [xlog2, if_neg h, log2]
      field_simp [ne_of_gt hlog2_pos]
  -- Suffices: vonNeumann ρ * Real.log 2 ≤ Real.log n
  -- Because: vonNeumann ≤ log2 n = Real.log n / Real.log 2
  --   iff (le_div_iff₀ hlog2_pos): vonNeumann * Real.log 2 ≤ Real.log n
  rw [show log2 (Fintype.card a) = Real.log (Fintype.card a) / Real.log 2 from rfl]
  rw [le_div_iff₀ hlog2_pos]
  -- Goal: vonNeumann ρ * Real.log 2 ≤ Real.log (Fintype.card a)
  -- vonNeumann = -(∑ xlog2(λᵢ))
  -- So vonNeumann * Real.log 2 = -(∑ xlog2(λᵢ)) * Real.log 2 = -(∑ xlog2(λᵢ) * Real.log 2)
  have hvn_mul : vonNeumann ρ * Real.log 2 =
      -∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i) := by
    rw [vonNeumann]
    calc
      (-(∑ i, xlog2 (hH.eigenvalues i))) * Real.log 2
          = -((∑ i, xlog2 (hH.eigenvalues i)) * Real.log 2) := by ring
      _ = -(∑ i, xlog2 (hH.eigenvalues i) * Real.log 2) := by
        rw [Finset.sum_mul]
      _ = -∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact hxlog2_mul _ (hnonneg i)
  rw [hvn_mul]
  -- Now: -(∑ λᵢ ln λᵢ) ≤ Real.log n
  -- KL divergence: ∑ λᵢ * ln(λᵢ * n) ≥ 0, which expands to ∑ λᵢ ln λᵢ ≥ -ln n
  -- So -(∑ λᵢ ln λᵢ) ≤ ln n
  -- Prove KL ≥ 0 via: λᵢ * ln(λᵢ * n) ≥ λᵢ - 1/n for each i
  have hKL : 0 ≤ ∑ i, hH.eigenvalues i
      * Real.log (hH.eigenvalues i * ↑(Fintype.card a)) := by
    have hbound : ∀ i, hH.eigenvalues i
        * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
        ≥ hH.eigenvalues i - 1 / ↑(Fintype.card a) := by
      intro i
      by_cases hl : hH.eigenvalues i = 0
      · simp [hl, Real.log_zero]
      · have hlpos : 0 < hH.eigenvalues i := lt_of_le_of_ne (hnonneg i) (Ne.symm hl)
        have hprod : 0 < hH.eigenvalues i * ↑(Fintype.card a) :=
          mul_pos hlpos hnreal
        have hxi := xlog_self_ge_sub_one (le_of_lt hprod)
        have : hH.eigenvalues i * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
            ≥ hH.eigenvalues i - 1 / ↑(Fintype.card a) := by
          have hdiv :
              (hH.eigenvalues i * ↑(Fintype.card a) - 1) / ↑(Fintype.card a)
                ≤ (hH.eigenvalues i * ↑(Fintype.card a)
                    * Real.log (hH.eigenvalues i * ↑(Fintype.card a)))
                    / ↑(Fintype.card a) :=
            div_le_div_of_nonneg_right hxi (le_of_lt hnreal)
          calc
            hH.eigenvalues i - 1 / ↑(Fintype.card a)
                = (hH.eigenvalues i * ↑(Fintype.card a) - 1)
                    / ↑(Fintype.card a) := by
                    field_simp [ne_of_gt hnreal]
            _ ≤ (hH.eigenvalues i * ↑(Fintype.card a)
                    * Real.log (hH.eigenvalues i * ↑(Fintype.card a)))
                    / ↑(Fintype.card a) := hdiv
            _ = hH.eigenvalues i
                    * Real.log (hH.eigenvalues i * ↑(Fintype.card a)) := by
                    field_simp [ne_of_gt hnreal]
        exact this
    calc (0 : ℝ)
        = ∑ i, (hH.eigenvalues i - 1 / ↑(Fintype.card a)) := by
          rw [Finset.sum_sub_distrib]
          rw [hsum, Finset.sum_const]
          simp
          field_simp [ne_of_gt hnreal]
          ring
      _ ≤ ∑ i, hH.eigenvalues i
          * Real.log (hH.eigenvalues i * ↑(Fintype.card a)) :=
        Finset.sum_le_sum (fun i _ => hbound i)
  have hexpand_KL : ∑ i, hH.eigenvalues i
      * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
    = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
      + Real.log ↑(Fintype.card a) := by
    calc
      ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
          = ∑ i, (hH.eigenvalues i * Real.log (hH.eigenvalues i)
              + hH.eigenvalues i * Real.log ↑(Fintype.card a)) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hl : hH.eigenvalues i = 0
            · simp [hl, Real.log_zero]
            · have hlpos : 0 < hH.eigenvalues i :=
                lt_of_le_of_ne (hnonneg i) (Ne.symm hl)
              rw [Real.log_mul (ne_of_gt hlpos) (ne_of_gt hnreal)]
              ring
      _ = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
          + ∑ i, hH.eigenvalues i * Real.log ↑(Fintype.card a) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
          + (∑ i, hH.eigenvalues i) * Real.log ↑(Fintype.card a) := by
            rw [Finset.sum_mul]
      _ = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
          + Real.log ↑(Fintype.card a) := by
            rw [hsum]
            ring
  -- From KL: sum λᵢ ln λᵢ ≥ -ln n
  linarith [hKL, hexpand_KL]

end State

namespace Ensemble

/-- The Holevo information is bounded by log2(dim B). -/
theorem holevo_le_log_card (E : Ensemble ι a) :
    E.holevoInformation ≤ log2 (Fintype.card a) := by
  have hnonneg_sum : 0
      ≤ ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (NNReal.coe_nonneg _) (State.vonNeumann_nonneg _)
  calc E.holevoInformation
      = State.vonNeumann E.averageState
          - ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i) := rfl
    _ ≤ State.vonNeumann E.averageState := sub_le_self _ hnonneg_sum
    _ ≤ log2 (Fintype.card a) := State.vonNeumann_le_log_card E.averageState

end Ensemble

end

end QIT
