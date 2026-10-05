/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.PolyApprox.Scalar
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Parameters for the exponential quantum strong converse

The explicit entropy cost and exponent choice in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:610-614].
All logarithms and binary entropies are in bits.
-/

@[expose] public section

namespace QIT.QuantumStrongConverse

noncomputable section

open Filter Set
open scoped Topology

/-- The entropy and dimension cost per channel use. -/
def entropyCost (κ θ : ℝ) : ℝ := binaryEntropy θ + θ * log2 (2 * κ)

/-- The intermediate exponent, before halving it for the strict final bound. -/
def exponent (c κ r r₀ θ : ℝ) : ℝ :=
  min (c * θ ^ 2 / 4) ((r - r₀) / 2 - entropyCost κ θ)

/-- A positive rate gap admits a small positive fractional degree. -/
theorem exists_theta (κ : ℝ) {gap : ℝ} (hgap : 0 < gap) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ 2 * entropyCost κ θ < gap := by
  have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun θ => 2 * entropyCost κ θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [entropyCost] using
      (tendsto_binaryEntropy_nhdsWithin_zero_right.add (hid.mul_const (log2 (2 * κ)))).const_mul 2
  have hsmall := hlim.eventually (gt_mem_nhds hgap)
  have hhalf : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), θ < 1 / 2 :=
    hid.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hpos : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  obtain ⟨θ, hθ, hh, hg⟩ := (hpos.and (hhalf.and hsmall)).exists
  exact ⟨θ, hθ, hh, hg⟩

/-- Both terms of the explicit minimum are strictly positive. -/
theorem exponent_pos {c κ r r₀ θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hgap : 2 * entropyCost κ θ < r - r₀) : 0 < exponent c κ r r₀ θ := by
  unfold exponent
  exact lt_min (by positivity) (by linarith)

/-- The exponent choice leaves a positive linear margin over the weak-converse rate. -/
theorem exponent_rate_margin (c κ r r₀ θ : ℝ) :
    r₀ + exponent c κ r r₀ θ ≤ r - exponent c κ r r₀ θ - 2 * entropyCost κ θ := by
  have h := min_le_right (c * θ ^ 2 / 4) ((r - r₀) / 2 - entropyCost κ θ)
  change exponent c κ r r₀ θ ≤ _ at h
  linarith

/-- The floor degree is admissible once the fractional blocklength is at
least four [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:616-635]. -/
theorem floor_degree_bounds {θ : ℝ} (hθ : 0 < θ) (hh : θ < 1 / 2) {n : ℕ}
    (hlarge : 4 ≤ θ * (n : ℝ)) :
    0 < n ∧ 3 ≤ ⌊θ * (n : ℝ)⌋₊ ∧ 2 * ⌊θ * (n : ℝ)⌋₊ ≤ n ∧
      θ * (n : ℝ) / 2 ≤ (⌊θ * (n : ℝ)⌋₊ : ℝ) := by
  have hn : 0 < n := by
    by_contra! h
    have he : n = 0 := Nat.eq_zero_of_le_zero h
    subst n
    norm_num at hlarge
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor := Nat.floor_le (by positivity : 0 ≤ θ * (n : ℝ))
  refine ⟨hn, Nat.le_floor (by norm_num; linarith), ?_, ?_⟩
  · have hreal : 2 * (⌊θ * (n : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hreal
  · have hnear := Nat.lt_floor_add_one (θ * (n : ℝ))
    linarith

/-- The projective-norm budget is positive in every block dimension. -/
theorem approximationGamma_pos {κ : ℝ} (hκ : 0 < κ) (n D : ℕ) :
    0 < QuantumPolyApprox.approximationGamma κ n D := by
  unfold QuantumPolyApprox.approximationGamma
  positivity

/-- Entropy monotonicity controls the logarithmic budget for degrees below
`θ n`, with `θ ≤ 1/2`. This is the estimate in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:616-635]. -/
theorem log_approximationGamma_le {κ θ : ℝ} {n D : ℕ} (hκ : 1 ≤ κ)
    (hθ : 0 ≤ θ) (hh : θ ≤ 1 / 2) (hn : 0 < n) (hD : (D : ℝ) ≤ θ * (n : ℝ)) :
    log2 (QuantumPolyApprox.approximationGamma κ n D) ≤
      (n : ℝ) * entropyCost κ θ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < 2 * κ := by linarith
  have hlog : 0 ≤ log2 (2 * κ) := by
    simpa only [log2_one] using
      log2_mono_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ 2 * κ)
  have hratio : (D : ℝ) / n ≤ θ := (div_le_iff₀ hn').mpr hD
  have he := binaryEntropy_monotoneOn
    ⟨by positivity, hratio.trans hh⟩ ⟨hθ, hh⟩ hratio
  have he' := mul_le_mul_of_nonneg_left he hn'.le
  have hd' := mul_le_mul_of_nonneg_right hD hlog
  rw [QuantumPolyApprox.approximationGamma, log2_pow_mul_two_rpow hk]
  unfold entropyCost
  nlinarith

/-- The lower floor estimate gives the first term of the explicit exponent. -/
theorem approximationError_le {c θ a : ℝ} {n D : ℕ} (hc : 0 < c) (hθ : 0 < θ)
    (hn : 0 < n) (hD : θ * (n : ℝ) / 2 ≤ (D : ℝ)) (ha : a ≤ c * θ ^ 2 / 4) :
    QuantumPolyApprox.approximationError c n D ≤ (2 : ℝ) ^ (-a * (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ θ * (n : ℝ) / 2) hD 2
  have hb : (n : ℝ) * (c * θ ^ 2 / 4) ≤ c * (D : ℝ) ^ 2 / n := by
    rw [le_div_iff₀ hn']
    nlinarith [mul_le_mul_of_nonneg_left hs hc.le]
  have ha' := mul_le_mul_of_nonneg_left ha hn'.le
  unfold QuantumPolyApprox.approximationError
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  simp only [neg_mul, neg_div]
  linarith

/-- A single eventual threshold provides the floor range, smoothing error,
and full one-shot logarithmic penalty, independently of the code. -/
theorem eventually_parameter_bounds {a θ ε : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 4 ≤ θ * (n : ℝ) ∧
      (2 : ℝ) ^ (-(a / 2) * (n : ℝ)) ≤ ε / 2 ∧
      4 * log2 (2 / ε) + 1 < (n : ℝ) * a := by
  have hlinear : Tendsto (fun n : ℕ => θ * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hθ tendsto_natCast_atTop_atTop
  have hmargin : Tendsto (fun n : ℕ => (n : ℝ) * a) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const ha
  have hbase : (2 : ℝ) ^ (-(a / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hdecay : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(a / 2) * (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [two_rpow_neg_mul_nat] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num) _) hbase
  exact (hlinear.eventually_ge_atTop 4).and
    ((hdecay.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).mono
      (fun _ h => h.le) |>.and (hmargin.eventually_gt_atTop (4 * log2 (2 / ε) + 1)))

/-- A code above the intermediate exponential tail meets the smoothing
condition of Theorem 2; the fidelity here is squared fidelity. -/
theorem exponential_error_le_smoothing {a ε F : ℝ} {n : ℕ} (hε : 0 < ε)
    (hsmall : (2 : ℝ) ^ (-(a / 2) * (n : ℝ)) ≤ ε / 2)
    (hF : (2 : ℝ) ^ (-a * (n : ℝ)) < F) :
    (2 : ℝ) ^ (-a * (n : ℝ)) ≤ ε * Real.sqrt F / 2 := by
  have hFpos : 0 < F := (Real.rpow_pos_of_pos (by norm_num) _).trans hF
  have hsquare : ((2 : ℝ) ^ (-(a / 2) * (n : ℝ))) ^ 2 =
      (2 : ℝ) ^ (-a * (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have hroot : (2 : ℝ) ^ (-(a / 2) * (n : ℝ)) ≤ Real.sqrt F := by
    nlinarith [Real.sq_sqrt hFpos.le, Real.sqrt_nonneg F,
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(a / 2) * (n : ℝ))]
  calc
    _ = (2 : ℝ) ^ (-(a / 2) * (n : ℝ)) * (2 : ℝ) ^ (-(a / 2) * (n : ℝ)) := by
      rw [← hsquare, pow_two]
    _ ≤ (ε / 2) * Real.sqrt F := mul_le_mul hsmall hroot (by positivity) (by positivity)
    _ = _ := by ring

end

end QIT.QuantumStrongConverse
