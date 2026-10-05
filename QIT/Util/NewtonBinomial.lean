/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Binomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Newton expansion in the binomial polynomial basis

Real polynomials have a finite Newton expansion whose coefficients are signed
binomial sums of their integer-grid values
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:535-546].
The triangle inequality gives the coefficient bound on a bounded grid
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:547-552].
-/

@[expose] public section

open Polynomial Finset
open scoped BigOperators

namespace QIT

/-- The polynomial `x ↦ binom(x,s)`, normalized by `s!`.
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:535-546]. -/
noncomputable def binomialPolynomial (s : ℕ) : Polynomial ℝ := Ring.choose X s

/-- The Newton coefficient obtained from the integer grid up to `s`.
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:535-546]. -/
noncomputable def newtonCoefficient (p : Polynomial ℝ) (s : ℕ) : ℝ :=
  ∑ k ∈ range (s + 1), (-1 : ℝ) ^ (s - k) * (s.choose k : ℝ) * p.eval (k : ℝ)

/-- Evaluation transports the binomial polynomial to the binomial operation in a real algebra. -/
theorem aeval_binomialPolynomial_eq_choose {A : Type*} [Ring A] [Algebra ℝ A]
    [BinomialRing A] (x : A) (s : ℕ) :
    aeval x (binomialPolynomial s) = Ring.choose x s := by
  simpa [binomialPolynomial] using Ring.map_choose (aeval x) (X : ℝ[X]) s

/-- On natural inputs the binomial polynomial is the ordinary binomial coefficient. -/
@[simp] theorem binomialPolynomial_eval_natCast (k s : ℕ) :
    (binomialPolynomial s).eval (k : ℝ) = (k.choose s : ℝ) := by
  simpa [binomialPolynomial, Ring.choose_natCast] using
    Ring.map_choose (evalRingHom (k : ℝ)) (X : ℝ[X]) s

/-- The binomial polynomial is the descending Pochhammer polynomial divided by `s!`. -/
theorem binomialPolynomial_eq_inv_factorial_smul (s : ℕ) :
    binomialPolynomial s = (s.factorial : ℝ)⁻¹ • descPochhammer ℝ s := by
  apply Polynomial.funext
  intro x
  have h := Ring.map_choose (evalRingHom x) (X : ℝ[X]) s
  simp only [coe_evalRingHom, eval_X] at h
  rw [binomialPolynomial, h, Ring.choose_eq_smul, eval_smul]
  congr 1
  rw [← aeval_eq_smeval, aeval_def,
    ← descPochhammer_map (Int.castRingHom ℝ), eval_map]
  rfl

/-- The binomial polynomial has exactly the expected degree, including at `s = 0`. -/
@[simp] theorem binomialPolynomial_natDegree (s : ℕ) :
    (binomialPolynomial s).natDegree = s := by
  rw [binomialPolynomial_eq_inv_factorial_smul, natDegree_smul,
    descPochhammer_natDegree]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))

/-- Newton coefficients are the iterated unit forward differences at zero. -/
theorem newtonCoefficient_eq_fwdDiff (p : Polynomial ℝ) (s : ℕ) :
    newtonCoefficient p s = (fwdDiff (1 : ℝ))^[s] p.eval 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [newtonCoefficient, zsmul_eq_mul]

/-- Forward differences vanish above the polynomial degree. -/
theorem newtonCoefficient_eq_zero_of_natDegree_lt (p : Polynomial ℝ) (s : ℕ)
    (h : p.natDegree < s) : newtonCoefficient p s = 0 := by
  rw [newtonCoefficient_eq_fwdDiff, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h]
  rfl

/-- Expansion of a degree-at-most-`D` polynomial in the binomial basis.
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:535-546]. -/
theorem newton_binomial_expansion (p : Polynomial ℝ) (D : ℕ) (hD : p.natDegree ≤ D) :
    p = ∑ s ∈ range (D + 1), C (newtonCoefficient p s) * binomialPolynomial s := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono
  rintro x ⟨n, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_mul, eval_C,
    binomialPolynomial_eval_natCast]
  have hn := shift_eq_sum_fwdDiff_iter (1 : ℝ) p.eval n 0
  simp only [nsmul_eq_mul, mul_one, zero_add, ← newtonCoefficient_eq_fwdDiff] at hn
  rw [hn]
  simp_rw [mul_comm (n.choose _ : ℝ)]
  rcases le_total n D with hnD | hDn
  · apply sum_subset (range_mono (Nat.add_le_add_right hnD 1))
    intro s hs hsn
    have hns : n < s := by simpa using hsn
    rw [Nat.choose_eq_zero_of_lt hns, Nat.cast_zero, mul_zero]
  · symm
    apply sum_subset (range_mono (Nat.add_le_add_right hDn 1))
    intro s hs hsD
    have hDs : D < s := by simpa using hsD
    rw [newtonCoefficient_eq_zero_of_natDegree_lt p s (lt_of_le_of_lt hD hDs), zero_mul]

/-- A unit bound on the integer grid gives the coefficient bound `2^s`.
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:547-552]. -/
theorem abs_newtonCoefficient_le_two_pow (p : Polynomial ℝ) (s : ℕ)
    (h : ∀ k ≤ s, |p.eval (k : ℝ)| ≤ 1) :
    |newtonCoefficient p s| ≤ (2 : ℝ)^s := by
  calc
    |newtonCoefficient p s| ≤
        ∑ k ∈ range (s + 1), |(-1 : ℝ) ^ (s - k) * (s.choose k : ℝ) * p.eval (k : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (s + 1), (s.choose k : ℝ) := by
      apply sum_le_sum
      intro k hk
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (s.choose k : ℝ) from Nat.cast_nonneg _)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (h k (by simpa using hk))
    _ = (2 : ℝ)^s := by exact_mod_cast Nat.sum_range_choose s

end QIT
