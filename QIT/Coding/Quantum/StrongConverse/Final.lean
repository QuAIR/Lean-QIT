/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.StrongConverse.Parameters
public import QIT.Coding.Quantum.StrongConverse.FiniteBlock

/-!
# Exponential strong converse for quantum capacity

Theorem 1, conditional on the explicit one-shot, scalar NOR, and weak-converse
witnesses [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:137-144].
The assembly retains the explicit exponent from
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:610-614]
and the logarithmic penalty from
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:616-635].
-/

@[expose] public section

namespace QIT.Channel

noncomputable section

open QuantumStrongConverse QuantumPolyApprox Filter

universe u

variable {a b e : Type u} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

/-- The intermediate exponential bound with the source's explicit exponent.
The fractional degree is fixed independently of the blocklength and code.
Only the three stated external witnesses are used. -/
theorem eventually_fidelity_le_of_weakConverse [Nonempty b] [Nonempty e]
    (N : Channel a b) (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N)
    (hFact1 : ∀ n, 0 < n →
      (N.tensorPower n).HasOneShotQuantumAchievability (V.tensorPowerBipartite n))
    {c q R R₀ θ : ℝ} (hFact2 : SherstovNORWitness c)
    (hFact3 : N.HasQuantumWeakConverseAt q) (hq : q < R₀)
    (hθ : 0 < θ) (hh : θ < 1 / 2)
    (hgap : 2 * entropyCost
      (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) θ < R - R₀) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ (r t : Type u) [Fintype r] [DecidableEq r] [Nonempty r]
        [Fintype t] [DecidableEq t],
      ∀ C : EntanglementGenerationCode (N.tensorPower n) r t,
        R ≤ C.rate n → C.fidelity ≤ (2 : ℝ) ^
          (-exponent c (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2))
            R R₀ θ * (n : ℝ)) := by
  let κ : ℝ := min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)
  let A := exponent c κ R R₀ θ
  have hκ : 1 ≤ κ := by
    have hb : (1 : ℝ) ≤ Fintype.card b := by exact_mod_cast Fintype.card_pos (α := b)
    have he : (1 : ℝ) ≤ Fintype.card e := by exact_mod_cast Fintype.card_pos (α := e)
    exact le_min (by nlinarith) (by nlinarith)
  have hA : 0 < A := exponent_pos hFact2.pos hθ hgap
  obtain ⟨ε, hε, hε₁, n₀, hweak⟩ := hFact3 R₀ hq
  obtain ⟨n₁, hlarge⟩ := eventually_atTop.mp (eventually_parameter_bounds hA hθ hε)
  refine ⟨max n₀ n₁, ?_⟩
  intro n hn hnpos r t _ _ _ _ _ C hrate
  obtain ⟨hdegree, hsmall, hpenalty⟩ := hlarge n ((le_max_right _ _).trans hn)
  obtain ⟨_, hD, hDn, hDlow⟩ := floor_degree_bounds hθ hh hdegree
  let D := ⌊θ * (n : ℝ)⌋₊
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  change C.fidelity ≤ (2 : ℝ) ^ (-A * (n : ℝ))
  by_contra! hf
  have hfpos : 0 < C.fidelity := (Real.rpow_pos_of_pos (by norm_num) _).trans hf
  have herr : approximationError c n D ≤ ε * Real.sqrt C.fidelity / 2 :=
    (approximationError_le hFact2.pos hθ hnpos hDlow (min_le_left _ _)).trans
      (exponential_error_le_smoothing hε hsmall hf)
  have hΓ : 0 < approximationGamma κ n D := approximationGamma_pos (by linarith) n D
  obtain ⟨m, imF, imD, imN, C', hfid, hcode⟩ :=
    C.exists_transmissionCode_tensorPower_of_sherstovNOR V hV hFact2 (hFact1 n hnpos)
      hD hDn hfpos hΓ hε hε₁ herr
  have hupper := hweak n ((le_max_left _ _).trans hn) hnpos m C' hfid
  have hlogF : -A * (n : ℝ) < log2 C.fidelity := by
    by_contra! h
    exact (not_le_of_gt hf) ((log2_le_iff_le_two_rpow hfpos).mp h)
  have hlogΓ := log_approximationGamma_le hκ hθ.le hh.le hnpos
    (Nat.floor_le (by positivity : 0 ≤ θ * (n : ℝ)))
  change R ≤ log2 (C.dimension : ℝ) / (n : ℝ) at hrate
  have hlogM := (le_div_iff₀ hn').mp hrate
  have hmargin := mul_le_mul_of_nonneg_left (exponent_rate_margin c κ R R₀ θ) hn'.le
  change (n : ℝ) * (R₀ + A) ≤ (n : ℝ) * (R - A - 2 * entropyCost κ θ) at hmargin
  change log2 (C.dimension : ℝ) + log2 C.fidelity - 2 * log2 (approximationGamma κ n D) -
    4 * log2 (2 / ε) - 1 ≤ log2 (Fintype.card m : ℝ) at hcode
  change log2 (approximationGamma κ n D) ≤ (n : ℝ) * entropyCost κ θ at hlogΓ
  nlinarith

/-- Exponential strong converse above any threshold admitting the explicit
weak-converse witness. One-shot achievability is supplied for each positive
blocklength, with a fixed single-use Stinespring realization; scalar NOR
approximation is the other external input. No capacity identity is assumed. -/
theorem theorem1At_of_weakConverse
    (N : Channel a b) (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N)
    (hFact1 : ∀ n, 0 < n →
      (N.tensorPower n).HasOneShotQuantumAchievability (V.tensorPowerBipartite n))
    {c q : ℝ} (hFact2 : SherstovNORWitness c)
    (hFact3 : N.HasQuantumWeakConverseAt q) :
    N.HasExponentialQuantumStrongConverseAt q := by
  cases isEmpty_or_nonempty a with
  | inl ha =>
      intro γ _
      refine ⟨1, by norm_num, 1, ?_⟩
      intro n _ hn r t _ _ _ _ _ C _
      cases n with
      | zero => omega
      | succ n =>
          obtain ⟨x⟩ := C.encodedState.nonempty
          exact isEmptyElim x.2.1
  | inr ha =>
      have : Nonempty (b × e) :=
        ((Channel.ofReferenceIsometry V).applyState (State.maximallyMixed a)).nonempty
      have : Nonempty b := Nonempty.map Prod.fst (inferInstance : Nonempty (b × e))
      have : Nonempty e := Nonempty.map Prod.snd (inferInstance : Nonempty (b × e))
      intro γ hγ
      let κ : ℝ := min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)
      obtain ⟨θ, hθ, hh, hgap⟩ := exists_theta κ
        (by linarith : 0 < (q + γ) - (q + γ / 2))
      let A := exponent c κ (q + γ) (q + γ / 2) θ
      have hA : 0 < A := exponent_pos hFact2.pos hθ hgap
      obtain ⟨n₀, hbound⟩ := N.eventually_fidelity_le_of_weakConverse V hV hFact1
        hFact2 hFact3 (by linarith : q < q + γ / 2) hθ hh hgap
      refine ⟨A / 2, by positivity, n₀, ?_⟩
      intro n hn hnpos r t _ _ _ _ _ C hrate
      have hb := hbound n hn hnpos r t C hrate
      refine hb.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_)
      change -A * (n : ℝ) < -(A / 2) * (n : ℝ)
      have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
      nlinarith

/-- Theorem 1 at operational quantum capacity, conditional on Facts 1, 2,
and 3. For every positive rate gap there is a positive exponent, uniform
over all sufficiently long mixed-input entanglement-generation codes
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:137-144].
The weak converse is an explicit hypothesis, not a capacity/coherent-
information identification. -/
theorem theorem1_of_weakConverse
    (N : Channel a b) (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N)
    (hFact1 : ∀ n, 0 < n →
      (N.tensorPower n).HasOneShotQuantumAchievability (V.tensorPowerBipartite n))
    {c : ℝ} (hFact2 : SherstovNORWitness c)
    (hFact3 : N.HasQuantumWeakConverseAt N.quantumCapacity) :
    N.HasExponentialQuantumStrongConverse :=
  N.theorem1At_of_weakConverse V hV hFact1 hFact2 hFact3

end

end QIT.Channel
