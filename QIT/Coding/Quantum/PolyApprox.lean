/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.PolyApprox.Scalar
public import QIT.Coding.Quantum.PolyApprox.Operator
public import QIT.Coding.Quantum.PolyApprox.TensorNorm

/-!
# Polynomial projector approximation

The polynomial route to tensor-power projector approximation, conditional on
an explicit scalar NOR witness
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530].
Newton expansion and the subset identity control the projective norm, without
assuming that an infimal decomposition cost is attained.
-/

@[expose] public section

namespace QIT.QuantumPolyApprox

noncomputable section

open Finset Polynomial
open scoped QIT.Matrix Matrix.Norms.L2Operator

universe u
variable {b e : Type u} [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]

private theorem piNorm_aeval_le_of_choose_bound (p : Polynomial ℝ) (M : CMatrix (b × e))
    {n D : ℕ} {κ : ℝ} (hdegree : p.natDegree ≤ D)
    (hκ : 1 ≤ 2 * κ) (hD : 2 * D ≤ n)
    (hp : ∀ k : ℕ, k ≤ n → |p.eval (k : ℝ)| ≤ 1)
    (hchoose : ∀ s ≤ D, piNorm (Ring.choose M s) ≤ (n.choose s : ℝ) * κ^s) :
    piNorm (aeval M p) ≤ approximationGamma κ n D := by
  have hrepr : aeval M p =
      ∑ s ∈ range (D + 1), (newtonCoefficient p s : ℂ) • Ring.choose M s := by
    conv_lhs => rw [newton_binomial_expansion p D hdegree]
    simp only [map_sum, map_mul, aeval_C, aeval_binomialPolynomial_eq_choose]
    congr 1
    funext s
    rw [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]
    exact RCLike.real_smul_eq_coe_smul _ _
  rw [hrepr]
  calc
    _ ≤ ∑ s ∈ range (D + 1), piNorm ((newtonCoefficient p s : ℂ) • Ring.choose M s) :=
      piNorm_sum_le _ _
    _ = ∑ s ∈ range (D + 1), |newtonCoefficient p s| * piNorm (Ring.choose M s) := by
      simp only [piNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ s ∈ range (D + 1), |newtonCoefficient p s| * (n.choose s : ℝ) * κ^s := by
      apply sum_le_sum
      intro s hs
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (hchoose s (Nat.le_of_lt_succ (mem_range.mp hs))) (abs_nonneg _)
    _ ≤ approximationGamma κ n D := newton_weighted_sum_le_gamma p hκ hD hp

/-- Each binomial term in the counting operator has its subset-count budget. -/
theorem piNorm_choose_countingOperator_le (P : CMatrix (b × e))
    (hPh : P.IsHermitian) (hPi : P * P = P) (n s : ℕ) :
    piNorm (Ring.choose (countingOperator P (n + 1)) s) ≤
      ((n + 1).choose s : ℝ) *
        (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2))^s := by
  classical
  rw [choose_countingOperator_eq_sum_noncommProd P hPi]
  refine (piNorm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ S ∈ ((univ : Finset (Fin (n + 1))).powersetCard s).attach,
        (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2))^s := by
      apply sum_le_sum
      intro S _
      have hs := (mem_powersetCard.mp S.property).2
      simpa only [hs] using piNorm_noncommProd_localDefect_le P hPh hPi S.val
        (fun i _ j _ _ => localDefect_comm P i j)
    _ = _ := by simp [card_powersetCard, nsmul_eq_mul]

/-- A grid-bounded polynomial of low degree has the projective-norm budget
from [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:568-583]. -/
theorem piNorm_projectorApproximation_le [Nonempty b] [Nonempty e]
    (P : CMatrix (b × e)) (hPh : P.IsHermitian) (hPi : P * P = P)
    (p : Polynomial ℝ) (n D : ℕ) (hdegree : p.natDegree ≤ D) (hD : 2 * D ≤ n + 1)
    (hp : ∀ k : ℕ, k ≤ n + 1 → |p.eval (k : ℝ)| ≤ 1) :
    piNorm (projectorApproximation p P (n + 1)) ≤
      approximationGamma (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) (n + 1) D := by
  have hb : (1 : ℝ) ≤ Fintype.card b := by exact_mod_cast Fintype.card_pos (α := b)
  have he : (1 : ℝ) ≤ Fintype.card e := by exact_mod_cast Fintype.card_pos (α := e)
  have hκ : 1 ≤ 2 * min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2) := by
    have hmin : (1 : ℝ) ≤ min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2) :=
      le_min (by nlinarith) (by nlinarith)
    linarith
  exact piNorm_aeval_le_of_choose_bound p (countingOperator P (n + 1)) hdegree hκ hD hp
    (fun s _ => piNorm_choose_countingOperator_le P hPh hPi n s)

/-- Lemma 3, with scalar NOR approximation as the only external witness.
The approximating operator is the displayed real polynomial of the counting
operator, and the projective norm uses the receiver/environment bipartition
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530].
The two finite factor types share a universe, as in `piNorm`; empty factors
are included. The inequalities `3 ≤ D` and `2 * D ≤ n` retain the source range. -/
theorem lemma3_of_sherstovNOR {c : ℝ} (w : SherstovNORWitness c)
    (P : CMatrix (b × e)) (hPh : P.IsHermitian) (hPi : P * P = P)
    {n D : ℕ} (hD : 3 ≤ D) (hn : 2 * D ≤ n) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      projectorApproximation p P n * TensorPower.tensorPowMatrixPair P n =
        TensorPower.tensorPowMatrixPair P n ∧
      TensorPower.tensorPowMatrixPair P n * projectorApproximation p P n =
        TensorPower.tensorPowMatrixPair P n ∧
      ‖projectorApproximation p P n - TensorPower.tensorPowMatrixPair P n‖ ≤
        approximationError c n D ∧
      piNorm (projectorApproximation p P n) ≤
        approximationGamma (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) n D := by
  obtain ⟨p, hdegree, hp0, herror, hgrid⟩ := w.polynomial n D hD (by omega)
  cases n with
  | zero => omega
  | succ n =>
    refine ⟨p, hdegree, projectorApproximation_mul_tensorPow hPh hPi p hp0 n,
      tensorPow_mul_projectorApproximation hPh hPi p hp0 n,
      norm_projectorApproximation_sub_le hPh hPi p hp0 n
        (approximationError_pos c (n + 1) D).le herror, ?_⟩
    have hempty (h : projectorApproximation p P (n + 1) = 0) :
        piNorm (projectorApproximation p P (n + 1)) ≤
          approximationGamma (min ((Fintype.card b : ℝ)^2)
            ((Fintype.card e : ℝ)^2)) (n + 1) D := by
      rw [h, piNorm_zero]
      exact approximationGamma_nonneg (le_min (sq_nonneg _) (sq_nonneg _)) _ _
    cases isEmpty_or_nonempty b with
    | inl hb => exact hempty (Subsingleton.elim _ _)
    | inr hb =>
      cases isEmpty_or_nonempty e with
      | inl he => exact hempty (Subsingleton.elim _ _)
      | inr he => exact piNorm_projectorApproximation_le P hPh hPi p n D hdegree hn hgrid

/-- Operator-only consumer form of the conditional polynomial approximation.
It exposes exactly the support, error, and projective-norm data used in the
exponential-converse assembly. -/
theorem exists_projectorApproximation_of_sherstovNOR {c : ℝ} (w : SherstovNORWitness c)
    (P : CMatrix (b × e)) (hPh : P.IsHermitian) (hPi : P * P = P)
    {n D : ℕ} (hD : 3 ≤ D) (hn : 2 * D ≤ n) :
    ∃ T : CMatrix ((Fin n → b) × (Fin n → e)),
      T * TensorPower.tensorPowMatrixPair P n = TensorPower.tensorPowMatrixPair P n ∧
      TensorPower.tensorPowMatrixPair P n * T = TensorPower.tensorPowMatrixPair P n ∧
      ‖T - TensorPower.tensorPowMatrixPair P n‖ ≤ approximationError c n D ∧
      piNorm T ≤ approximationGamma
        (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) n D := by
  obtain ⟨p, _, hr, hl, herr, hnorm⟩ := lemma3_of_sherstovNOR w P hPh hPi hD hn
  exact ⟨projectorApproximation p P n, hr, hl, herr, hnorm⟩

end

end QIT.QuantumPolyApprox
