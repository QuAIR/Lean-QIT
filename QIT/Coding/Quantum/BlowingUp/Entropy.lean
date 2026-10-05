/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.PiNorm
public import QIT.Util.Matrix.FilteredMarginal
public import QIT.OneShot.SmoothEndpoint.Companion

/-!
# Entropy estimates for quantum blowing-up

Projective decompositions and marginal bounds used in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419].
Strict projective budgets are removed before applying an achievability witness.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open scoped Topology

namespace QIT

noncomputable section

universe u

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq b] in
/-- Left multiplication on the retained register commutes with partial trace. -/
theorem partialTraceA_kronecker_one_mul (X : CMatrix (a × b)) (Y : CMatrix b) :
    partialTraceA (Matrix.kronecker (1 : CMatrix a) Y * X) = Y * partialTraceA X := by
  have h := congrArg Matrix.conjTranspose
    (partialTraceA_mul_kronecker_one_right Xᴴ Yᴴ)
  simpa only [partialTraceA_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose] using h

omit [DecidableEq b] in
/-- Congruence on the retained register commutes with partial trace. -/
theorem partialTraceA_kronecker_one_conjugation (X : CMatrix (a × b)) (Y : CMatrix b) :
    partialTraceA (Matrix.kronecker (1 : CMatrix a) Y * X *
      Matrix.kronecker (1 : CMatrix a) Yᴴ) = Y * partialTraceA X * Yᴴ := by
  rw [partialTraceA_mul_kronecker_one_right, partialTraceA_kronecker_one_mul]

/-- A spectral-norm contraction has a Gram matrix bounded by the identity. -/
theorem cMatrix_conjTranspose_mul_le_one_of_norm_le_one
    (X : CMatrix a) (hX : ‖X‖ ≤ 1) : Xᴴ * X ≤ 1 := by
  have hn : ‖Xᴴ * X‖ ≤ (1 : ℝ) := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    nlinarith [norm_nonneg X]
  simpa using (cMatrix_norm_le_iff_le_smul_one _
    (Matrix.posSemidef_conjTranspose_mul_self X) 1 zero_le_one).mp hn

/-- The receiver contraction can be removed before bounding the environment
congruence [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem partialTraceA_kronecker_contraction_le
    (S : CMatrix (a × b)) (X : CMatrix a) (Y : CMatrix b)
    (hS : S.PosSemidef) (hX : ‖X‖ ≤ 1) :
    partialTraceA (Matrix.kronecker X Y * S * (Matrix.kronecker X Y)ᴴ) ≤
      Y * partialTraceA S * Yᴴ := by
  let L := Matrix.kronecker (1 : CMatrix a) Y
  have h := partialTraceA_contraction_le (L * S * Lᴴ) X
    (hS.mul_mul_conjTranspose_same L)
    (cMatrix_conjTranspose_mul_le_one_of_norm_le_one X hX)
  have hleft : Matrix.kronecker X (1 : CMatrix b) * (L * S * Lᴴ) *
      Matrix.kronecker Xᴴ (1 : CMatrix b) =
      Matrix.kronecker X Y * S * (Matrix.kronecker X Y)ᴴ := by
    simp only [L, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul]
    simp only [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul]
  rw [hleft] at h
  have hLstar : Lᴴ = Matrix.kronecker (1 : CMatrix a) Yᴴ := by
    simp [L, Matrix.kronecker, Matrix.conjTranspose_kronecker]
  rw [hLstar] at h
  change _ ≤ partialTraceA (Matrix.kronecker (1 : CMatrix a) Y * S *
    Matrix.kronecker (1 : CMatrix a) Yᴴ) at h
  rwa [partialTraceA_kronecker_one_conjugation] at h

/-- A contraction cannot increase the trace of a positive side operator. -/
theorem trace_conjugation_le_of_norm_le_one
    (τ Y : CMatrix b) (hτ : τ.PosSemidef) (hY : ‖Y‖ ≤ 1) :
    (Y * τ * Yᴴ).trace.re ≤ τ.trace.re := by
  have h := cMatrix_trace_mul_le_of_le_posSemidef_right hτ
    (cMatrix_conjTranspose_mul_le_one_of_norm_le_one Y hY)
  rw [Matrix.trace_mul_cycle]
  simpa only [Matrix.one_mul] using h

/-- Convex Kronecker filtering admits a sum of environment congruences as a
marginal upper bound
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem partialTraceA_convex_kronecker_filter_le
    {ι : Type*} [Fintype ι]
    (v : a × b → ℂ) (p : ι → ℝ) (X : ι → CMatrix a) (Y : ι → CMatrix b)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (hX : ∀ j, ‖X j‖ ≤ 1) :
    partialTraceA (rankOneMatrix (∑ j,
      (p j : ℂ) • (Matrix.kronecker (X j) (Y j)).mulVec v)) ≤
      ∑ j, (p j : ℂ) • (Y j * partialTraceA (rankOneMatrix v) * (Y j)ᴴ) := by
  have h := partialTraceA_mono (rankOneMatrix_convex_sum_le p
    (fun j => (Matrix.kronecker (X j) (Y j)).mulVec v) hp hs)
  have hsum : partialTraceA (∑ j, (p j : ℂ) •
      rankOneMatrix ((Matrix.kronecker (X j) (Y j)).mulVec v)) =
      ∑ j, (p j : ℂ) • partialTraceA
        (rankOneMatrix ((Matrix.kronecker (X j) (Y j)).mulVec v)) := by
    ext i k
    simp only [partialTraceA, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => (Finset.mul_sum _ _ _).symm)
  rw [hsum] at h
  refine h.trans (Finset.sum_le_sum (fun j _ => ?_))
  apply cMatrix_ofReal_smul_le_smul (hp j)
  rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  exact partialTraceA_kronecker_contraction_le _ _ _ (rankOneMatrix_pos v) (hX j)

namespace QuantumBlowingUp

variable {r e : Type u} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e]

/-- Convex environment conjugations preserve positivity and do not increase
the trace when every factor is a contraction. -/
theorem convex_environment_side_operator
    {ι : Type*} [Fintype ι] (τ : CMatrix e) (hτ : τ.PosSemidef)
    (p : ι → ℝ) (Y : ι → CMatrix e)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (hY : ∀ j, ‖Y j‖ ≤ 1) :
    (∑ j, (p j : ℂ) • (Y j * τ * (Y j)ᴴ)).PosSemidef ∧
      (∑ j, (p j : ℂ) • (Y j * τ * (Y j)ᴴ)).trace.re ≤ τ.trace.re := by
  constructor
  · exact Matrix.posSemidef_sum _ (fun j _ =>
      (hτ.mul_mul_conjTranspose_same (Y j)).smul (by exact_mod_cast hp j))
  · simp only [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      ∑ j, p j * (Y j * τ * (Y j)ᴴ).trace.re ≤ ∑ j, p j * τ.trace.re :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (trace_conjugation_le_of_norm_le_one τ (Y j) hτ (hY j)) (hp j))
      _ = τ.trace.re := by rw [← Finset.sum_mul, hs, one_mul]

/-- A dominated marginal remains dominated by the convex environment side
operator after product filtering
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem convex_filter_marginal_le
    {ι : Type*} [Fintype ι]
    (v : b × (r × e) → ℂ) (τ : CMatrix e)
    (hdom : partialTraceA (rankOneMatrix v) ≤ Matrix.kronecker (1 : CMatrix r) τ)
    (p : ι → ℝ) (X : ι → CMatrix b) (Y : ι → CMatrix e)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (hX : ∀ j, ‖X j‖ ≤ 1) :
    partialTraceA (rankOneMatrix (∑ j, (p j : ℂ) •
      (Matrix.kronecker (X j) (Matrix.kronecker (1 : CMatrix r) (Y j))).mulVec v)) ≤
      Matrix.kronecker (1 : CMatrix r) (∑ j, (p j : ℂ) • (Y j * τ * (Y j)ᴴ)) := by
  have h := partialTraceA_convex_kronecker_filter_le v p X
    (fun j => Matrix.kronecker (1 : CMatrix r) (Y j)) hp hs hX
  have hj (j : ι) :
      Matrix.kronecker (1 : CMatrix r) (Y j) * partialTraceA (rankOneMatrix v) *
        (Matrix.kronecker (1 : CMatrix r) (Y j))ᴴ ≤
      Matrix.kronecker (1 : CMatrix r) (Y j * τ * (Y j)ᴴ) := by
    have hc := (Matrix.le_iff.mp hdom).mul_mul_conjTranspose_same
      (Matrix.kronecker (1 : CMatrix r) (Y j))
    rw [Matrix.mul_sub, Matrix.sub_mul] at hc
    have heq : Matrix.kronecker (1 : CMatrix r) (Y j) *
        Matrix.kronecker (1 : CMatrix r) τ *
        (Matrix.kronecker (1 : CMatrix r) (Y j))ᴴ =
        Matrix.kronecker (1 : CMatrix r) (Y j * τ * (Y j)ᴴ) := by
      simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rw [heq] at hc
    exact Matrix.le_iff.mpr hc
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    cMatrix_ofReal_smul_le_smul (hp j) (hj j))
  refine h.trans (hsum.trans_eq ?_)
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Swap the reference and receiver while retaining the environment. -/
def referenceReceiverSwap (r b e : Type u) : r × (b × e) ≃ b × (r × e) :=
  (Equiv.prodAssoc r b e).symm.trans
    ((Equiv.prodCongr (Equiv.prodComm r b) (Equiv.refl e)).trans
      (Equiv.prodAssoc b r e))

/-- A receiver-environment operator extended by an untouched reference, on
the carrier where the receiver can be discarded by `partialTraceA`. -/
def receiverEnvironmentLift (r : Type u) [Fintype r] [DecidableEq r]
    (T : CMatrix (b × e)) : CMatrix (b × (r × e)) :=
  WireFam.matReindex (referenceReceiverSwap r b e)
    (Matrix.kronecker (1 : CMatrix r) T)

omit [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e] in
/-- Product operators retain the untouched reference identity. -/
theorem receiverEnvironmentLift_kronecker (X : CMatrix b) (Y : CMatrix e) :
    receiverEnvironmentLift r (Matrix.kronecker X Y) =
      Matrix.kronecker X (Matrix.kronecker (1 : CMatrix r) Y) := by
  ext i j
  change (1 : CMatrix r) i.2.1 j.2.1 * (X i.1 j.1 * Y i.2.2 j.2.2) =
    X i.1 j.1 * ((1 : CMatrix r) i.2.1 j.2.1 * Y i.2.2 j.2.2)
  ring

omit [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e] in
/-- The extension respects real scaling. -/
theorem receiverEnvironmentLift_smul (c : ℝ) (T : CMatrix (b × e)) :
    receiverEnvironmentLift r (c • T) = c • receiverEnvironmentLift r T := by
  ext i j
  simp [receiverEnvironmentLift, WireFam.matReindex_apply,
    Matrix.smul_apply, Complex.real_smul, mul_left_comm]

omit [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e] in
/-- The extension respects finite sums. -/
theorem receiverEnvironmentLift_sum {ι : Type*} [Fintype ι]
    (T : ι → CMatrix (b × e)) :
    receiverEnvironmentLift r (∑ j, T j) = ∑ j, receiverEnvironmentLift r (T j) := by
  ext i j
  simp [receiverEnvironmentLift, WireFam.matReindex_apply,
    Matrix.sum_apply, Finset.mul_sum]

omit [Fintype a] [DecidableEq a] in
/-- A real amplitude scaling squares in the corresponding rank-one matrix. -/
theorem rankOneMatrix_ofReal_smul (c : ℝ) (v : a → ℂ) :
    rankOneMatrix ((c : ℂ) • v) = ((c ^ 2 : ℝ) : ℂ) • rankOneMatrix v := by
  ext i j
  simp only [rankOneMatrix_apply, Pi.smul_apply, smul_eq_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_apply, Complex.ofReal_pow]
  ring

/-- A strict projective budget produces a positive environment side operator
with the squared-budget trace bound. No optimal decomposition is assumed
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem exists_side_operator_of_piNorm_lt
    (T : CMatrix (b × e)) (v : b × (r × e) → ℂ)
    (τ : CMatrix e) (hτ : τ.PosSemidef)
    (hdom : partialTraceA (rankOneMatrix v) ≤ Matrix.kronecker (1 : CMatrix r) τ)
    {Γ : ℝ} (hΓ : piNorm T < Γ) :
    ∃ σ : CMatrix e, σ.PosSemidef ∧
      partialTraceA (rankOneMatrix ((receiverEnvironmentLift r T).mulVec v)) ≤
        Matrix.kronecker (1 : CMatrix r) σ ∧
      σ.trace.re ≤ Γ ^ 2 * τ.trace.re := by
  obtain ⟨m, p, X, Y, hp, hs, hX, hY, hT⟩ :=
    exists_convex_kronecker_of_piNorm_lt T hΓ
  let S := ∑ j, (p j : ℂ) • (Y j * τ * (Y j)ᴴ)
  have hS := convex_environment_side_operator τ hτ p Y hp hs hY
  have hvec : (receiverEnvironmentLift r T).mulVec v =
      (Γ : ℂ) • ∑ j, (p j : ℂ) •
        (Matrix.kronecker (X j) (Matrix.kronecker (1 : CMatrix r) (Y j))).mulVec v := by
    rw [hT, receiverEnvironmentLift_smul, receiverEnvironmentLift_sum]
    simp_rw [receiverEnvironmentLift_smul, receiverEnvironmentLift_kronecker]
    simp only [Matrix.smul_mulVec, Matrix.sum_mulVec]
    ext i
    simp [Complex.real_smul]
  refine ⟨((Γ ^ 2 : ℝ) : ℂ) • S,
    hS.1.smul (by exact_mod_cast sq_nonneg Γ), ?_, ?_⟩
  · rw [hvec, rankOneMatrix_ofReal_smul, partialTraceA_smul]
    have h := cMatrix_ofReal_smul_le_smul (sq_nonneg Γ)
      (convex_filter_marginal_le v τ hdom p X Y hp hs hX)
    simpa only [S, Matrix.kronecker, Matrix.kronecker_smul] using h
  · rw [Matrix.trace_smul]
    simpa only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left hS.2 (sq_nonneg Γ)

/-- A closed projective budget bounds the min-entropy scale of a normalized
filtered marginal. Positive budget slack is removed by continuity, before any
code-existence witness is invoked
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem conditionalMinEntropyScale_filtered_le
    (T : CMatrix (b × e)) (v : b × (r × e) → ℂ)
    (τ : CMatrix e) (hτ : τ.PosSemidef)
    (hdom : partialTraceA (rankOneMatrix v) ≤ Matrix.kronecker (1 : CMatrix r) τ)
    (ρ : State (r × e)) {d Γ : ℝ} (hd : 0 < d) (hΓ : piNorm T ≤ Γ)
    (hρ : ρ.matrix = ((d⁻¹ : ℝ) : ℂ) •
      partialTraceA (rankOneMatrix ((receiverEnvironmentLift r T).mulVec v))) :
    ρ.toSubnormalized.conditionalMinEntropyScale ≤ Γ ^ 2 * τ.trace.re / d := by
  have hbudget (s : ℝ) (hs : 0 < s) :
      ρ.toSubnormalized.conditionalMinEntropyScale ≤ (Γ + s) ^ 2 * τ.trace.re / d := by
    obtain ⟨σ, hσ, hσdom, hσtrace⟩ :=
      exists_side_operator_of_piNorm_lt T v τ hτ hdom (lt_add_of_le_of_pos hΓ hs)
    have hfeas : SubnormalizedState.ConditionalMinEntropyScaleFeasible
        ρ.toSubnormalized (((d⁻¹ : ℝ) : ℂ) • σ) := by
      refine ⟨hσ.smul (by exact_mod_cast inv_nonneg.mpr hd.le), ?_⟩
      change ρ.matrix ≤ _
      rw [hρ]
      simpa only [Matrix.kronecker, Matrix.kronecker_smul] using
        cMatrix_ofReal_smul_le_smul (inv_nonneg.mpr hd.le) hσdom
    have hinf : ρ.toSubnormalized.conditionalMinEntropyScale ≤
        (((d⁻¹ : ℝ) : ℂ) • σ).trace.re := by
      rw [SubnormalizedState.conditionalMinEntropyScale_eq_sInf_scaleValueSet]
      exact csInf_le ρ.toSubnormalized.conditionalMinEntropyScaleValueSet_bddBelow
        ⟨((d⁻¹ : ℝ) : ℂ) • σ, hfeas, rfl⟩
    have htr := mul_le_mul_of_nonneg_left hσtrace (inv_nonneg.mpr hd.le)
    have heq : (((d⁻¹ : ℝ) : ℂ) • σ).trace.re = d⁻¹ * σ.trace.re := by
      simp [Matrix.trace_smul, Complex.mul_re]
    rw [heq] at hinf
    calc
      _ ≤ d⁻¹ * ((Γ + s) ^ 2 * τ.trace.re) := hinf.trans htr
      _ = _ := by ring
  have hcont : Continuous (fun s : ℝ => (Γ + s) ^ 2 * τ.trace.re / d) := by fun_prop
  have hlim : Filter.Tendsto (fun s : ℝ => (Γ + s) ^ 2 * τ.trace.re / d)
      (𝓝[>] (0 : ℝ)) (𝓝 (Γ ^ 2 * τ.trace.re / d)) := by
    simpa only [add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hbudget s hs

/-- A scale bound gives the logarithmic entropy estimate used in blowing-up.
The center is normalized, so the finite entropy branch is justified
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem conditionalMinEntropy_ge_of_scale_le
    (ρ : State (r × e)) {M lam Γ : ℝ}
    (hM : 0 < M) (hlam : 0 < lam) (hΓ : 0 < Γ)
    (hscale : ρ.toSubnormalized.conditionalMinEntropyScale ≤ Γ ^ 2 / (M * lam)) :
    log2 M + log2 lam - 2 * log2 Γ ≤ ρ.conditionalMinEntropy := by
  let : Nonempty r := ⟨(Classical.choice ρ.nonempty).1⟩
  let : Nonempty e := ⟨(Classical.choice ρ.nonempty).2⟩
  have htrace : 0 < ρ.toSubnormalized.matrix.trace.re := by
    simp only [State.toSubnormalized_trace, Complex.one_re, zero_lt_one]
  have hpos := SubnormalizedState.conditionalMinEntropyScale_pos_of_trace_pos htrace
  rw [← State.toSubnormalized_conditionalMinEntropyRaw_eq,
    SubnormalizedState.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos _ htrace]
  have h := neg_log2_antitone_of_pos hpos hscale
  have heq : -log2 (Γ ^ 2 / (M * lam)) = log2 M + log2 lam - 2 * log2 Γ := by
    unfold log2
    rw [Real.log_div (pow_ne_zero 2 hΓ.ne') (mul_ne_zero hM.ne' hlam.ne'),
      Real.log_pow, Real.log_mul hM.ne' hlam.ne']
    ring
  rwa [heq] at h

/-- The filtered marginal has the required unsmoothed min-entropy; all
projective slack has already been removed
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem conditionalMinEntropy_filtered_ge
    (T : CMatrix (b × e)) (v : b × (r × e) → ℂ)
    (τ : CMatrix e) (hτ : τ.PosSemidef)
    (hdom : partialTraceA (rankOneMatrix v) ≤ Matrix.kronecker (1 : CMatrix r) τ)
    (ρ : State (r × e)) {d M lam Γ : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hlam : 0 < lam) (hΓ : 0 < Γ)
    (hpi : piNorm T ≤ Γ) (hdlam : lam ^ 2 ≤ d) (htr : τ.trace.re = lam / M)
    (hρ : ρ.matrix = ((d⁻¹ : ℝ) : ℂ) •
      partialTraceA (rankOneMatrix ((receiverEnvironmentLift r T).mulVec v))) :
    log2 M + log2 lam - 2 * log2 Γ ≤ ρ.conditionalMinEntropy := by
  apply conditionalMinEntropy_ge_of_scale_le ρ hM hlam hΓ
  have hscale := conditionalMinEntropyScale_filtered_le T v τ hτ hdom ρ hd hpi hρ
  rw [htr] at hscale
  have hdiv : lam / d ≤ 1 / lam := by
    apply (div_le_div_iff₀ hd hlam).mpr
    simpa only [one_mul, pow_two] using hdlam
  calc
    _ ≤ Γ ^ 2 * (lam / M) / d := hscale
    _ = (Γ ^ 2 / M) * (lam / d) := by ring
    _ ≤ (Γ ^ 2 / M) * (1 / lam) :=
      mul_le_mul_of_nonneg_left hdiv (div_nonneg (sq_nonneg Γ) hM.le)
    _ = _ := by ring

/-- A normalized candidate in the purified-distance ball yields a lower bound
on the source-facing smooth entropy, whose optimization also allows
subnormalized candidates
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:275-287]. -/
theorem smoothConditionalMinEntropy_ge_of_normalized_candidate
    (ρ σ : State (r × e)) {ε H : ℝ} (hε : 0 ≤ ε) (hε₁ : ε < 1)
    (hdist : ρ.purifiedDistance σ ≤ ε) (hH : H ≤ σ.conditionalMinEntropy) :
    H ≤ ρ.smoothConditionalMinEntropy ε hε hε₁ := by
  let : Nonempty r := ⟨(Classical.choice ρ.nonempty).1⟩
  let : Nonempty e := ⟨(Classical.choice ρ.nonempty).2⟩
  apply hH.trans
  have hball : ρ.purifiedBall ε σ := hdist
  have hcand := State.toSubnormalized_SmoothConditionalMinEntropyCandidate_of
    hball (State.toSubnormalized_conditionalMinEntropyRaw_eq σ).symm
  exact SubnormalizedState.le_smoothConditionalMinEntropy_of_candidate_of_lt_sqrt_trace
    hε (ρ.epsilon_lt_sqrt_toSubnormalized_trace hε₁) hcand

end QuantumBlowingUp

end

end QIT
