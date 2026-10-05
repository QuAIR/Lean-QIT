/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.PolyApprox.Basic
public import QIT.Util.BinomialTail

/-!
# The polynomial approximation budget

Newton coefficient control and the binomial tail estimate give the explicit
budget in [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530].
The coefficient and tail ingredients are those of
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:547-552] and
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:584-589].
-/

@[expose] public section

namespace QIT.QuantumPolyApprox

open Finset

/-- Nonnegative dimension factors give nonnegative projective-norm budgets. -/
theorem approximationGamma_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (n D : ℕ) :
    0 ≤ approximationGamma κ n D :=
  mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hκ) _)
    (Real.rpow_nonneg (by norm_num) _)

/-- The weighted lower binomial tail has the exact entropy budget of Lemma 3. -/
theorem weighted_binomial_sum_le_gamma {n D : ℕ} {κ : ℝ}
    (hκ : 1 ≤ 2 * κ) (hD : 2 * D ≤ n) :
    (∑ s ∈ range (D + 1), (n.choose s : ℝ) * (2 * κ)^s) ≤
      approximationGamma κ n D := by
  have htail := sum_choose_le_two_rpow_binEntropy hD
  rw [← binaryEntropy_eq_binEntropy_div_log_two] at htail
  calc
    _ ≤ ∑ s ∈ range (D + 1), (n.choose s : ℝ) * (2 * κ)^D := by
      apply sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hκ (Nat.le_of_lt_succ (mem_range.mp hs))) (Nat.cast_nonneg _)
    _ = (2 * κ)^D * ∑ s ∈ range (D + 1), (n.choose s : ℝ) := by
      rw [← sum_mul, mul_comm]
    _ ≤ approximationGamma κ n D := by
      exact mul_le_mul_of_nonneg_left htail (pow_nonneg (by linarith) _)

/-- The coefficient-weighted subset estimate is bounded by the same budget. -/
theorem newton_weighted_sum_le_gamma (p : Polynomial ℝ) {n D : ℕ} {κ : ℝ}
    (hκ : 1 ≤ 2 * κ) (hD : 2 * D ≤ n)
    (hp : ∀ k : ℕ, k ≤ n → |p.eval (k : ℝ)| ≤ 1) :
    (∑ s ∈ range (D + 1), |newtonCoefficient p s| * (n.choose s : ℝ) * κ^s) ≤
      approximationGamma κ n D := by
  have hκ0 : 0 ≤ κ := by linarith
  apply le_trans _ (weighted_binomial_sum_le_gamma hκ hD)
  apply sum_le_sum
  intro s hs
  have hsD : s ≤ D := Nat.le_of_lt_succ (mem_range.mp hs)
  have hDn : D ≤ n := by omega
  have ha := abs_newtonCoefficient_le_two_pow p s
    (fun k hk => hp k (hk.trans (hsD.trans hDn)))
  calc
    _ ≤ (2 : ℝ)^s * (n.choose s : ℝ) * κ^s := by
      gcongr
    _ = (n.choose s : ℝ) * (2 * κ)^s := by rw [mul_pow]; ring

/-- The exponential error is positive, including at the totalized zero denominator. -/
theorem approximationError_pos (c : ℝ) (n D : ℕ) : 0 < approximationError c n D :=
  Real.rpow_pos_of_pos (by norm_num) _

end QIT.QuantumPolyApprox
