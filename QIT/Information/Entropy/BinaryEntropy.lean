/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.AlickiFannesWinter
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Binary entropy in bits and nats

Conversion and order properties of the existing `QIT.binaryEntropy` definition.
The conversion uses the same totalized logarithm convention as `Real.binEntropy`;
monotonicity is restricted to the left half of the probability interval.
-/

@[expose] public section

namespace QIT

/-- Binary entropy in bits is natural-log binary entropy divided by `log 2`. -/
theorem binaryEntropy_eq_binEntropy_div_log_two (p : ℝ) :
    binaryEntropy p = Real.binEntropy p / Real.log 2 := by
  rw [binaryEntropy, xlog2_eq_mul_log2, xlog2_eq_mul_log2,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [log2, Real.negMulLog]
  ring

/-- Binary entropy in bits is monotone on the closed interval `[0, 1/2]`. -/
theorem binaryEntropy_monotoneOn :
    MonotoneOn binaryEntropy (Set.Icc 0 (1 / 2)) := by
  have h : MonotoneOn Real.binEntropy (Set.Icc 0 (1 / 2)) := by
    simpa only [one_div] using Real.binEntropy_strictMonoOn.monotoneOn
  intro p hp q hq hpq
  rw [binaryEntropy_eq_binEntropy_div_log_two, binaryEntropy_eq_binEntropy_div_log_two]
  exact div_le_div_of_nonneg_right (h hp hq hpq) (Real.log_pos one_lt_two).le

/-- Binary entropy in bits is at most one, including the totalized values
outside the probability interval. -/
theorem binaryEntropy_le_one (p : ℝ) : binaryEntropy p ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log_two]
  exact (div_le_one (Real.log_pos one_lt_two)).mpr Real.binEntropy_le_log_two

end QIT
