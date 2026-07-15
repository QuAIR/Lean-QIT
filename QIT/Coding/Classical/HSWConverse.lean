/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.HSW
public import QIT.Coding.Classical.Holevo
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.Entropy.MutualInformationDPI
public import QIT.Coding.Classical.RandomnessDistribution
public import QIT.Information.AlickiFannesWinter

/-!
# HSW converse: regularized Holevo upper-bounds classical capacity

The converse half of the HSW theorem: every operationally achievable
classical communication rate for a quantum channel `N` is bounded above by the
regularized Holevo information `χ_reg(N)`. The chain reduces a reliable `n`-use
classical code to a randomness-distribution relaxation, then chains three
estimates: Alicki–Fannes–Winter (AFW) continuity of (conditional) entropy, the
quantum data-processing inequality for mutual information, and the
classical-quantum Holevo supremum bound.

The finite-block chain is stated against explicit interfaces for the source
ingredients that are not part of this leaf: the Fano/randomness-distribution
reduction and the cq Holevo identity. Mutual-information data processing is
available as a proved local-channel theorem and re-exported here in the
one-sided form used by the HSW converse.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe uIn uOut uEnsemble uMessage uAux uAuxOut

noncomputable section

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (N : Channel a b)

/-- Local cardinality of the recursive tensor-power label type.  This mirrors
the private HSW helper so the converse module can state its dimension bound
self-containedly. -/
private theorem hswConverse_tensorPower_card (α : Type uAux) [Fintype α] (n : ℕ) :
    Fintype.card (TensorPower α n) = (Fintype.card α) ^ n := by
  induction n with
  | zero =>
      simp [TensorPower]
  | succ n ih =>
      change Fintype.card (Prod α (TensorPower α n)) = Fintype.card α ^ (n + 1)
      rw [Fintype.card_prod, ih, Nat.pow_succ]
      ring

private theorem hswConverse_tensorPower_card_real (α : Type uAux) [Fintype α] (n : ℕ) :
    (Fintype.card (TensorPower α n) : ℝ) = (Fintype.card α : ℝ) ^ n := by
  exact_mod_cast hswConverse_tensorPower_card α n

private theorem hswConverse_tensorPower_nonempty (α : Type uAux) [Nonempty α] :
    (n : ℕ) → Nonempty (TensorPower α n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 => ⟨(Classical.choice (inferInstance : Nonempty α),
      Classical.choice (hswConverse_tensorPower_nonempty α n))⟩

private theorem hswConverse_log2_pow_nat (x : ℝ) (n : ℕ) :
    log2 (x ^ n) = (n : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow]
  ring

/-- The mutual information of the classical-quantum state associated with an
ensemble is exactly the ensemble's Holevo information. -/
theorem cqState_mutualInformation_eq_holevoInformation {ι : Type uEnsemble}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    mutualInformation E.cqState = E.holevoInformation := by
  unfold mutualInformation Ensemble.holevoInformation
  rw [cqState_marginalA_vonNeumann E]
  rw [Ensemble.cqState_marginalB_eq_averageState E]
  rw [cqState_vonNeumann E]
  ring

/-- Alicki–Fannes–Winter continuity interface for conditional von Neumann
entropy in the project normalized trace-distance convention. This is the
source-shaped hypothesis interface used by HSW-style arguments; the AFW theorem
itself is tracked by the entropy/continuity category. -/
def alickiFannesWinter_statement
    {c : Type uAux} [Fintype c] [DecidableEq c]
    (ρ σ : State (Prod a c)) (ε : ℝ) : Prop :=
  0 ≤ ε →
    ρ.normalizedTraceDistance σ ≤ ε →
      ε ≤ 1 →
        |ρ.conditionalEntropy - σ.conditionalEntropy| ≤
          2 * ε * log2 (Fintype.card a : ℝ) +
            (1 + ε) * binaryEntropy (ε / (1 + ε))

/-- Quantum data-processing inequality for the von-Neumann mutual information:
applying a CPTP map to one subsystem cannot increase mutual information,
`I(A ; N(B))_ρ ≤ I(A ; B)_ρ`. -/
theorem mutualInformation_dataProcessing_statement
    {c : Type uAux} {d : Type uAuxOut}
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (ρ : State (Prod a c)) (Φ : Channel c d) :
    mutualInformation ρ ≥
      mutualInformation (((Channel.idChannel a).prod Φ).applyState ρ) := by
  simpa using
    mutualInformation_dataProcessing_local_channels_ge ρ (Channel.idChannel a) Φ

/-- Classical-quantum Holevo supremum bound: the mutual information of any cq
state `Σ_x p(x) |x⟩⟨x| ⊗ σ_x` is at most the Holevo information
`χ = S(Σ p σ_x) − Σ p S(σ_x)`. This is the source-facing interface consumed
by the HSW converse chain; the cq entropy identity can later prove this
interface directly. -/
def cqHolevo_upperBound_statement
    {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    {out : Type uAux} [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) : Prop :=
  mutualInformation E.cqState ≤ E.holevoInformation

/-- Proved cq-Holevo upper bound, obtained from the exact cq mutual-information
identity `I(X;B) = χ({p_x, ρ_x})`. This closes the HSW converse cq identity
interface used downstream. -/
theorem cqHolevo_upperBound
    {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    {out : Type uAux} [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) :
    cqHolevo_upperBound_statement E := by
  unfold cqHolevo_upperBound_statement
  rw [cqState_mutualInformation_eq_holevoInformation E]

/-- The cq output ensemble induced by an `n`-block HSW code contributes a
Holevo value to the `n`-use channel Holevo supremum. -/
theorem uniformOutput_holevoInformation_le_blockHolevoInformation
    (n : ℕ) (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    (uniformEnsemble M C.outputState).holevoInformation ≤
      (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n := by
  let E : Ensemble M (TensorPower a n) := uniformEnsemble M C.encoder
  let E' : Ensemble (ULift.{uEnsemble} M) (TensorPower a n) :=
    E.relabelIndex Equiv.ulift
  have hmem :
      (uniformEnsemble M C.outputState).holevoInformation ∈
        (Channel.holevoInformationValues.{uIn, uOut, max uEnsemble uMessage}
          (N.tensorPower n)) := by
    refine ⟨ULift.{uEnsemble} M, inferInstance, inferInstance, E', ?_⟩
    change (uniformEnsemble M C.outputState).holevoInformation =
      ((N.tensorPower n).outputEnsemble E').holevoInformation
    calc
      (uniformEnsemble M C.outputState).holevoInformation =
          ((N.tensorPower n).outputEnsemble E).holevoInformation := by
        congr 1
      _ = ((N.tensorPower n).outputEnsemble E').holevoInformation := by
        simp [E']
  have hle :
      (uniformEnsemble M C.outputState).holevoInformation ≤
        (Channel.holevoInformation.{uIn, uOut, max uEnsemble uMessage} (N.tensorPower n)) := by
    exact le_csSup (N.tensorPower n).holevoInformationValues_bddAbove hmem
  simpa [Channel.blockHolevoInformation] using hle

/-- Finite-block HSW converse chain in log-message form.

The two hypotheses are exactly the source ingredients outside this leaf:
the randomness-distribution/Fano lower bound and the cq Holevo identity bound.
The conclusion is the finite-block inequality before the asymptotic
regularized-Holevo squeeze. -/
theorem hsw_finiteBlock_converse_log_card
    (n : ℕ) (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) {ε : ℝ}
    (hFano : hswCode_randomnessDistribution_statement N n M ε)
    (hCQ : cqHolevo_upperBound_statement (uniformEnsemble M C.outputState))
    (hC : C.maxErrorAtMost ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) * log2 (Fintype.card M : ℝ) + xlog2 ε + xlog2 (1 - ε) ≤
      (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n := by
  have hlower :
      (1 - ε) * log2 (Fintype.card M : ℝ) + xlog2 ε + xlog2 (1 - ε) ≤
        mutualInformation (cqChannelOutputState N n M C) :=
    hFano C hC hε0 hε1
  have hcq :
      mutualInformation (cqChannelOutputState N n M C) ≤
        (uniformEnsemble M C.outputState).holevoInformation := by
    simpa [cqChannelOutputState] using hCQ
  exact hlower.trans (hcq.trans (uniformOutput_holevoInformation_le_blockHolevoInformation N n M C))

/-- Finite-block HSW converse chain in rate form.  Since the repository defines
the `n = 0` message rate to be zero, this statement assumes `0 < n` and rewrites
`log₂ |M|` as `n` times the operational code rate. -/
theorem hsw_finiteBlock_converse_rate
    (n : ℕ) (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) {ε : ℝ} (hn : 0 < n)
    (hFano : hswCode_randomnessDistribution_statement N n M ε)
    (hCQ : cqHolevo_upperBound_statement (uniformEnsemble M C.outputState))
    (hC : C.maxErrorAtMost ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) * ((n : ℝ) * C.rate) + xlog2 ε + xlog2 (1 - ε) ≤
      (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n := by
  have hlog :
      (n : ℝ) * C.rate = log2 (Fintype.card M : ℝ) := by
    unfold HSWClassicalCode.rate hswMessageRate
    simp [Nat.ne_of_gt hn]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hn)]
  simpa [hlog] using hsw_finiteBlock_converse_log_card N n M C hFano hCQ hC hε0 hε1

/-- Every positive block Holevo rate is bounded by the regularized Holevo
supremum. -/
theorem blockHolevoRate_le_regularizedHolevoInformation [Nonempty a] [Nonempty b]
    {n : ℕ} (hn : 0 < n) :
    (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ) ≤
      (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) := by
  rw [Channel.regularizedHolevoInformation]
  exact le_csSup N.regularizedHolevoRateValues_bddAbove ⟨n, hn, rfl⟩

/-- The output-dimension bound for every positive block Holevo rate. -/
theorem blockHolevoRate_le_log_card [Nonempty a] [Nonempty b]
    {n : ℕ} (hn : 0 < n) :
    (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ) ≤
      log2 (Fintype.card b : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound :
      (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n ≤
        log2 (Fintype.card (QIT.TensorPower b n)) := by
    haveI : Nonempty (QIT.TensorPower a n) := hswConverse_tensorPower_nonempty a n
    unfold Channel.blockHolevoInformation Channel.holevoInformation
    exact csSup_le
      (N.tensorPower n).holevoInformationValues_nonempty
      (fun r hr => (N.tensorPower n).mem_holevoInformationValues_le_log_card hr)
  calc
    (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ)
        ≤ log2 (Fintype.card (QIT.TensorPower b n)) / (n : ℝ) :=
          div_le_div_of_nonneg_right hbound (le_of_lt hnR)
    _ = log2 (Fintype.card b : ℝ) := by
      rw [hswConverse_tensorPower_card_real b n, hswConverse_log2_pow_nat]
      field_simp [ne_of_gt hnR]

/-- Nonnegativity of `log₂ |a|` for a nonempty finite type. -/
private theorem log2_card_nonneg (α : Type uAux) [Fintype α] [Nonempty α] :
    0 ≤ log2 (Fintype.card α : ℝ) := by
  have hcard_pos_nat : 0 < Fintype.card α := Fintype.card_pos_iff.mpr inferInstance
  have hcard_one : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hcard_pos_nat
  unfold log2
  exact div_nonneg (Real.log_nonneg hcard_one) (le_of_lt (Real.log_pos one_lt_two))

/-- Supremum squeeze for the regularized Holevo information.

If every positive slack below `R` is witnessed by some positive block Holevo
rate, then `R` is bounded by the regularized Holevo supremum. This is the
order-theoretic form of the HSW converse limit step. -/
theorem le_regularizedHolevoInformation_of_forall_blockRate_ge_sub [Nonempty a] [Nonempty b]
    {R : ℝ}
    (hblock : ∀ η : ℝ, 0 < η →
      ∃ n : ℕ, 0 < n ∧
        R - η ≤ (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ)) :
    R ≤ (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) := by
  rw [le_iff_forall_pos_lt_add]
  intro η hη
  obtain ⟨n, hn, hR⟩ := hblock (η / 2) (by linarith)
  have hsup :=
    blockHolevoRate_le_regularizedHolevoInformation.{uIn, uOut, uEnsemble, uMessage}
      N hn
  have hRsup :
      R - η / 2 ≤ (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) := hR.trans hsup
  linarith

/-- Code-level supremum squeeze used by the HSW converse.

For every positive slack, suppose there is a block code whose rate is within
that slack below `R`, and whose finite-block converse estimate upper bounds the
same code rate by the corresponding normalized block Holevo information plus
that slack. Then `R` is bounded by the regularized Holevo supremum. -/
theorem le_regularizedHolevoInformation_of_forall_code_blockRate_bound
    [Nonempty a] [Nonempty b] {R : ℝ}
    (hcode : ∀ η : ℝ, 0 < η →
      ∃ n : ℕ, ∃ M : Type uMessage, ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
        ∃ (_ : Nonempty M), ∃ C : HSWClassicalCode N n M,
          0 < n ∧ R - η ≤ C.rate ∧
            C.rate ≤ (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ) + η) :
    R ≤ (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) := by
  refine le_regularizedHolevoInformation_of_forall_blockRate_ge_sub.{
    uIn, uOut, uEnsemble, uMessage} N ?_
  intro η hη
  obtain ⟨n, M, hMF, hMD, hMne, C, hn, hR, hC⟩ := hcode (η / 2) (by linarith)
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  letI : Nonempty M := hMne
  refine ⟨n, hn, ?_⟩
  have hblock :
      R - η / 2 ≤ (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ) + η / 2 :=
    hR.trans hC
  linarith

/-- A scalar bridge from Fano's finite-block form to an additive normalized
block-rate upper bound.

The hypotheses `hsmall_dim` and `hsmall_corr` are the two asymptotic choices in
the HSW converse: make the multiplicative Fano loss small by choosing a small
error tolerance, then make the binary-entropy correction small by taking a
large block length. -/
private theorem rate_le_base_add_of_one_sub_mul_le
    {r x corr ε η L : ℝ}
    (hη : 0 < η)
    (hmain : (1 - ε) * r ≤ x + corr)
    (hxL : x ≤ L)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hsmall_dim : 2 * ε * L ≤ η / 2)
    (hsmall_corr : 2 * corr ≤ η / 2) :
    r ≤ x + η := by
  have hden_pos : 0 < 1 - ε := by linarith
  have hr_div : r ≤ (x + corr) / (1 - ε) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith [hmain]
  have hdecomp :
      (x + corr) / (1 - ε) =
        x + (ε * x + corr) / (1 - ε) := by
    field_simp [ne_of_gt hden_pos]
    ring
  have hA_le : ε * x + corr ≤ ε * L + corr := by
    simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left hxL hε0) corr
  by_cases hA_nonpos : ε * x + corr ≤ 0
  · have htail_nonpos : (ε * x + corr) / (1 - ε) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hA_nonpos hden_pos.le
    calc
      r ≤ (x + corr) / (1 - ε) := hr_div
      _ = x + (ε * x + corr) / (1 - ε) := hdecomp
      _ ≤ x := by linarith
      _ ≤ x + η := by linarith
  · have hA_nonneg : 0 ≤ ε * x + corr := le_of_not_ge hA_nonpos
    have hfactor : 1 ≤ 2 * (1 - ε) := by linarith
    have hA_div_le : (ε * x + corr) / (1 - ε) ≤ 2 * (ε * x + corr) := by
      rw [div_le_iff₀ hden_pos]
      have hmul := mul_le_mul_of_nonneg_right hfactor hA_nonneg
      nlinarith [hmul]
    have htail_small : 2 * (ε * x + corr) ≤ η := by
      have htwoA : 2 * (ε * x + corr) ≤ 2 * (ε * L + corr) := by
        nlinarith [hA_le]
      have hsplit : 2 * (ε * L + corr) = 2 * ε * L + 2 * corr := by ring
      calc
        2 * (ε * x + corr) ≤ 2 * (ε * L + corr) := htwoA
        _ = 2 * ε * L + 2 * corr := hsplit
        _ ≤ η := by linarith
    calc
      r ≤ (x + corr) / (1 - ε) := hr_div
      _ = x + (ε * x + corr) / (1 - ε) := hdecomp
      _ ≤ x + 2 * (ε * x + corr) := by linarith
      _ ≤ x + η := by linarith

/-- A constant divided by the block length is eventually below every positive
threshold.  The statement is deliberately sign-agnostic in the numerator, so it
can be used without separately proving positivity of the constant. -/
theorem exists_nat_const_div_le {A η : ℝ} (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 → A / (n : ℝ) ≤ η := by
  let X : ℝ := A / η
  refine ⟨max 1 (Nat.ceil X), ?_⟩
  intro n hn
  have hceil_le_n : Nat.ceil X ≤ n := (Nat.le_max_right 1 (Nat.ceil X)).trans hn
  have hX_le_n : X ≤ (n : ℝ) :=
    (Nat.le_ceil X).trans (by exact_mod_cast hceil_le_n)
  have hn_one : 1 ≤ n := (Nat.le_max_left 1 (Nat.ceil X)).trans hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_one
  have hA_le : A ≤ (n : ℝ) * η := by
    have hmul := mul_le_mul_of_nonneg_right hX_le_n hη.le
    have hX_mul : X * η = A := by
      dsimp [X]
      field_simp [ne_of_gt hη]
    calc
      A = X * η := hX_mul.symm
      _ ≤ (n : ℝ) * η := hmul
  rw [div_le_iff₀ hn_pos]
  simpa [mul_comm] using hA_le

/-- Convert the finite-block HSW converse inequality into a normalized code-rate
upper bound with an arbitrary additive slack. -/
theorem hsw_finiteBlock_converse_rate_le_blockRate_add
    [Nonempty a] [Nonempty b]
    (n : ℕ) (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) {ε η : ℝ} (hn : 0 < n)
    (hfinite :
      (1 - ε) * ((n : ℝ) * C.rate) + xlog2 ε + xlog2 (1 - ε) ≤
        (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n)
    (hη : 0 < η) (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hsmall_dim : 2 * ε * log2 (Fintype.card b : ℝ) ≤ η / 2)
    (hsmall_entropy :
      2 * (binaryEntropy ε / (n : ℝ)) ≤ η / 2) :
    C.rate ≤ (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ) + η := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hε1 : ε ≤ 1 := by linarith
  have hlogsum :
      xlog2 ε + xlog2 (1 - ε) = -binaryEntropy ε := by
    unfold binaryEntropy
    ring
  have hmul :
      (1 - ε) * ((n : ℝ) * C.rate) ≤
        (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n + binaryEntropy ε := by
    linarith
  have hmain :
      (1 - ε) * C.rate ≤
        (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ) +
          binaryEntropy ε / (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hmul hnR.le
    calc
      (1 - ε) * C.rate =
          ((1 - ε) * ((n : ℝ) * C.rate)) / (n : ℝ) := by
            field_simp [ne_of_gt hnR]
      _ ≤ ((Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n + binaryEntropy ε) /
          (n : ℝ) := hdiv
      _ = (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ) +
          binaryEntropy ε / (n : ℝ) := by
            ring
  exact rate_le_base_add_of_one_sub_mul_le
    (r := C.rate)
    (x := (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n / (n : ℝ))
    (corr := binaryEntropy ε / (n : ℝ))
    (η := η)
    (L := log2 (Fintype.card b : ℝ))
    hη hmain (blockHolevoRate_le_log_card.{uIn, uOut, uEnsemble, uMessage} N hn)
    hε0 hεhalf hsmall_dim hsmall_entropy

namespace Channel

/-- HSW converse for the regularized Holevo information.

Every operationally achievable classical communication rate is upper-bounded
by the regularized Holevo information.  The proof uses the proved
randomness-distribution/Fano reduction, the cq-Holevo identity, and the
finite-block regularized-Holevo squeeze above; it does not depend on the
separate AFW continuity node. -/
theorem hsw_regularizedHolevoInformation_converse
    [Nonempty a] [Nonempty b] (N : Channel a b) :
    (Channel.IsClassicalRateUpperBound.{uIn, uOut, uMessage} N)
      (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) := by
  intro R hAch
  refine le_regularizedHolevoInformation_of_forall_code_blockRate_bound.{
    uIn, uOut, uEnsemble, uMessage} N ?_
  intro η hη
  let L : ℝ := log2 (Fintype.card b : ℝ)
  let ε : ℝ := min (1 / 2) (η / (4 * (L + 1)))
  have hL_nonneg : 0 ≤ L := log2_card_nonneg b
  have hL1_pos : 0 < L + 1 := by linarith
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (div_pos hη (by positivity))
  have hε0 : 0 ≤ ε := le_of_lt hε_pos
  have hεhalf : ε ≤ 1 / 2 := by
    dsimp [ε]
    exact min_le_left _ _
  have hε1 : ε ≤ 1 := by linarith
  have hε_le_budget : ε ≤ η / (4 * (L + 1)) := by
    dsimp [ε]
    exact min_le_right _ _
  have hsmall_dim : 2 * ε * L ≤ η / 2 := by
    have hratio_le : L / (L + 1) ≤ 1 := by
      rw [div_le_one hL1_pos]
      linarith
    calc
      2 * ε * L ≤ 2 * (η / (4 * (L + 1))) * L := by nlinarith
      _ = (η / 2) * (L / (L + 1)) := by
            field_simp [ne_of_gt hL1_pos]
            ring
      _ ≤ η / 2 := by
            simpa [mul_one] using
              mul_le_mul_of_nonneg_left hratio_le (by positivity : 0 ≤ η / 2)
  obtain ⟨Nerr, hNerr⟩ :=
    exists_nat_const_div_le (A := 2 * binaryEntropy ε) (η := η / 2) (by linarith)
  obtain ⟨Nach, hNach⟩ := hAch (η / 2) (by linarith) ε hε_pos
  let n : ℕ := max 1 (max Nerr Nach)
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hn_ge_Nerr : n ≥ Nerr := by
    dsimp [n]
    exact (Nat.le_max_left Nerr Nach).trans (Nat.le_max_right 1 (max Nerr Nach))
  have hn_ge_Nach : n ≥ Nach := by
    dsimp [n]
    exact (Nat.le_max_right Nerr Nach).trans (Nat.le_max_right 1 (max Nerr Nach))
  obtain ⟨M, hMF, hMD, hMne, C, hrate, herr⟩ := hNach n hn_ge_Nach
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  letI : Nonempty M := hMne
  have hsmall_entropy :
      2 * (binaryEntropy ε / (n : ℝ)) ≤ η / 2 := by
    simpa [mul_div_assoc] using hNerr n hn_ge_Nerr
  have hfinite :
      (1 - ε) * ((n : ℝ) * C.rate) + xlog2 ε + xlog2 (1 - ε) ≤
        (Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N) n :=
    hsw_finiteBlock_converse_rate N n M C hn_pos
      (hswCode_randomnessDistribution N n M ε)
      (cqHolevo_upperBound (uniformEnsemble M C.outputState))
      herr hε0 hε1
  refine ⟨n, M, inferInstance, inferInstance, inferInstance, C, hn_pos, ?_, ?_⟩
  · linarith
  · exact hsw_finiteBlock_converse_rate_le_blockRate_add
      N n M C hn_pos hfinite hη hε0 hεhalf hsmall_dim hsmall_entropy

end Channel

/-- HSW converse target: every operationally achievable classical communication
rate for `N` is bounded by the regularized Holevo information.  The finite-block
chain above is the local reusable ingredient for this asymptotic upper bound. -/
def hsw_converse_statement : Prop :=
  (Channel.IsClassicalRateUpperBound.{uIn, uOut, uMessage} N)
    (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N)

end

end QIT
