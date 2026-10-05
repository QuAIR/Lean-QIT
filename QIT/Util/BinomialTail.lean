/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial tail bound by binary entropy

The weighted binomial theorem bounds the sum of binomial coefficients up to
half the row by binary entropy in bits
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:584-589].
-/

@[expose] public section

open scoped BigOperators

namespace QIT

/-- The lower binomial tail is bounded by `2^(n h(D/n))`, where `h` is binary
entropy in bits. The statement includes `D = 0` and `n = 0`.
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:584-589]. -/
theorem sum_choose_le_two_rpow_binEntropy {n D : ℕ} (hD : 2 * D ≤ n) :
    (∑ s ∈ Finset.range (D + 1), (n.choose s : ℝ)) ≤
      (2 : ℝ) ^ ((n : ℝ) * (Real.binEntropy ((D : ℝ) / (n : ℝ)) / Real.log 2)) := by
  by_cases hzero : D = 0
  · subst D
    simp
  have hDn : D ≤ n := by omega
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let t := (D : ℝ) / (n : ℝ)
  have ht : 0 < t := div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hzero)) hn
  have hhalf : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ hn).mpr
    have : (2 : ℝ) * D ≤ n := by exact_mod_cast hD
    linarith
  have hu : 0 < 1 - t := by linarith
  have htu : t ≤ 1 - t := by linarith
  have hweight (s : ℕ) (hs : s ≤ D) :
      t ^ D * (1 - t) ^ (n - D) ≤ t ^ s * (1 - t) ^ (n - s) := by
    calc
      t ^ D * (1 - t) ^ (n - D) =
          t ^ s * t ^ (D - s) * (1 - t) ^ (n - D) := by
        rw [← pow_add, Nat.add_sub_of_le hs]
      _ ≤ t ^ s * (1 - t) ^ (D - s) * (1 - t) ^ (n - D) := by
        gcongr
      _ = t ^ s * (1 - t) ^ (n - s) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
  have hsum : (∑ s ∈ Finset.range (D + 1), (n.choose s : ℝ)) *
      (t ^ D * (1 - t) ^ (n - D)) ≤ 1 := by
    calc
      _ = ∑ s ∈ Finset.range (D + 1), (n.choose s : ℝ) *
          (t ^ D * (1 - t) ^ (n - D)) := by rw [Finset.sum_mul]
      _ ≤ ∑ s ∈ Finset.range (D + 1), (n.choose s : ℝ) *
          (t ^ s * (1 - t) ^ (n - s)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (hweight s (by simpa using hs)) (by positivity)
      _ ≤ ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) *
          (t ^ s * (1 - t) ^ (n - s)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.add_le_add_right hDn 1)
        · intro s _ _
          positivity
      _ = 1 := by
        simp_rw [mul_comm (n.choose _ : ℝ)]
        rw [← add_pow]
        simp
  have hnt : (n : ℝ) * t = D := by dsimp [t]; field_simp
  have hnu : (n : ℝ) * (1 - t) = (n : ℝ) - D := by nlinarith [hnt]
  have hw : 0 < t ^ D * (1 - t) ^ (n - D) :=
    mul_pos (pow_pos ht _) (pow_pos hu _)
  have hlog : Real.log (t ^ D * (1 - t) ^ (n - D)) =
      -(n : ℝ) * Real.binEntropy t := by
    rw [Real.log_mul (pow_pos ht _).ne' (pow_pos hu _).ne',
      Real.log_pow, Real.log_pow, Nat.cast_sub hDn, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.negMulLog, Real.negMulLog]
    calc
      _ = -((n : ℝ) * t) * (-Real.log t) -
          ((n : ℝ) * (1 - t)) * (-Real.log (1 - t)) := by rw [hnt, hnu]; ring
      _ = _ := by ring
  have hendpoint : t ^ D * (1 - t) ^ (n - D) =
      Real.exp (-(n : ℝ) * Real.binEntropy t) := by
    rw [← hlog, Real.exp_log hw]
  have hbound : (∑ s ∈ Finset.range (D + 1), (n.choose s : ℝ)) ≤
      Real.exp ((n : ℝ) * Real.binEntropy t) := by
    rw [hendpoint, neg_mul, Real.exp_neg] at hsum
    simpa only [mul_inv_le_iff₀ (Real.exp_pos _), one_mul] using hsum
  change _ ≤ (2 : ℝ) ^ ((n : ℝ) * (Real.binEntropy t / Real.log 2))
  rw [Real.rpow_def_of_pos (by norm_num)]
  convert hbound using 1
  congr 1
  field_simp

end QIT
