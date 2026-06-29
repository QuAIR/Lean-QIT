/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Holevo
public import QIT.Core.Channel
public import QIT.Core.POVMProbability

/-!
# HSW coding theorem: classical capacity

Definition of the classical capacity of a quantum channel via the operational
supremum of achievable rates, the regularized Holevo information interface,
and the source-shaped direct-achievability interface.

The proved theorem in this module is intentionally conditional on an explicit
HSW coding witness: constructing the random code, packing-lemma decoder, and
typical/conditionally typical projector estimates is a separate upstream proof
obligation.  The full equality follows Wilde's HSW theorem statement
[Wilde2011Qst, qit-notes.tex:33588-33632], with the direct proof route in
[Wilde2011Qst, qit-notes.tex:33634-33808].  The converse route is tracked by
downstream proof leaves before the equality can be marked proved.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- Output ensemble obtained by sending every member of an input ensemble
through the channel. -/
def outputEnsemble {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) : Ensemble ι b where
  probs := E.probs
  weights_sum := E.weights_sum
  states := fun i => N.applyState (E.states i)

/-- Single-letter HSW Holevo rate for an input ensemble and channel. -/
def hswHolevoRate {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) : ℝ :=
  (N.outputEnsemble E).holevoInformation

/-- All single-letter Holevo information values realized by finite input
ensembles for channel `N`. -/
def holevoInformationValues : Set ℝ :=
  {r : ℝ | ∃ (ι : Type u) (instF : Fintype ι) (instD : DecidableEq ι),
    letI : Fintype ι := instF
    letI : DecidableEq ι := instD
    ∃ E : Ensemble ι a, r = N.hswHolevoRate E}

/-- Channel Holevo information as the supremum over finite input ensembles. -/
def holevoInformation : ℝ :=
  sSup N.holevoInformationValues

/-- Holevo information of the `n`-use tensor-power channel. -/
def blockHolevoInformation (n : ℕ) : ℝ :=
  (N.tensorPower n).holevoInformation

/-- Regularized Holevo block-rate values `χ(N^⊗n) / n` for positive block
lengths.  This uses a supremum-safe interface instead of assuming the
source-style limit exists before it is proved. -/
def regularizedHolevoRateValues : Set ℝ :=
  {R : ℝ | ∃ n : ℕ, 0 < n ∧ R = N.blockHolevoInformation n / (n : ℝ)}

/-- Regularized Holevo information as the supremum of positive block rates. -/
def regularizedHolevoInformation : ℝ :=
  sSup N.regularizedHolevoRateValues

end Channel

/-- Register rate for an `n`-use HSW classical message code.  The degenerate
`n = 0` convention is set to zero; asymptotic statements consume this only for
sufficiently large block lengths. -/
def hswMessageRate (M : Type u) [Fintype M] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card M : ℝ) / (n : ℝ)

/-- A finite HSW classical communication code for `n` uses of channel `N`.

The encoder assigns one input state on `A^n` to each message; the decoder is a
POVM on the output system `B^n` with the same message labels as outcomes. -/
structure HSWClassicalCode (N : Channel a b) (n : ℕ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] where
  encoder : M → State (TensorPower a n)
  decoder : POVM M (TensorPower b n)

namespace HSWClassicalCode

variable {N : Channel a b} {n : ℕ}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]

/-- Channel output state for a selected message. -/
def outputState (C : HSWClassicalCode N n M) (m : M) : State (TensorPower b n) :=
  (N.tensorPower n).applyState (C.encoder m)

/-- Born-rule probability that the decoder returns the transmitted message. -/
def successProbability (C : HSWClassicalCode N n M) (m : M) : ℝ :=
  (C.decoder.prob (C.outputState m) m : ℝ)

/-- Message-wise error probability. -/
def error (C : HSWClassicalCode N n M) (m : M) : ℝ :=
  1 - C.successProbability m

/-- Maximal message error bounded by `ε`. -/
def maxErrorAtMost (C : HSWClassicalCode N n M) (ε : ℝ) : Prop :=
  ∀ m : M, C.error m ≤ ε

/-- Classical communication rate of the message set. -/
def rate (_C : HSWClassicalCode N n M) : ℝ :=
  hswMessageRate M n

end HSWClassicalCode

/- Packing-lemma interfaces for a finite family of output states and a
decoder POVM.

This namespace records exactly the code/decoder performance layer appearing in
Wilde's packing lemma [Wilde2011Qst, qit-notes.tex:29363-29415]: message-indexed
output states, a POVM with the same message labels, average success/error, and
maximal error.  The random-code construction and typical-projector estimates
which supply such a decoder are separate proof leaves. -/
namespace PackingLemma

variable {out : Type v}
variable [Fintype out] [DecidableEq out]
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]

/-- A finite message-indexed family of output states together with a decoder
POVM. -/
structure DecoderCode (M : Type u) (out : Type v)
    [Fintype M] [DecidableEq M] [Nonempty M] [Fintype out] [DecidableEq out] where
  states : M → State out
  decoder : POVM M out

namespace DecoderCode

/-- Probability that the packing decoder returns the transmitted message. -/
def successProbability (C : DecoderCode M out) (m : M) : ℝ :=
  (C.decoder.prob (C.states m) m : ℝ)

/-- Message-wise error probability for the packing decoder. -/
def error (C : DecoderCode M out) (m : M) : ℝ :=
  1 - C.successProbability m

/-- Maximal message error bounded by `ε`. -/
def maxErrorAtMost (C : DecoderCode M out) (ε : ℝ) : Prop :=
  ∀ m : M, C.error m ≤ ε

/-- Uniform average success probability over the message set. -/
def averageSuccessProbability (C : DecoderCode M out) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m : M, C.successProbability m

/-- Uniform average error probability over the message set. -/
def averageError (C : DecoderCode M out) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m : M, C.error m

/-- Average message error bounded by `ε`. -/
def averageErrorAtMost (C : DecoderCode M out) (ε : ℝ) : Prop :=
  C.averageError ≤ ε

/-- The maximal-error condition unfolds to the source-style message-wise
decoder inequality.  This theorem is not a simp rule because arithmetic
normalization can obscure the direct bridge to `HSWClassicalCode.maxErrorAtMost`. -/
theorem maxErrorAtMost_iff (C : DecoderCode M out) (ε : ℝ) :
    C.maxErrorAtMost ε ↔ ∀ m : M, 1 - C.successProbability m ≤ ε := by
  rfl

/-- The average-error condition unfolds to the source-style uniform average
over message errors. -/
theorem averageErrorAtMost_iff (C : DecoderCode M out) (ε : ℝ) :
    C.averageErrorAtMost ε ↔
      (Fintype.card M : ℝ)⁻¹ * ∑ m : M, (1 - C.successProbability m) ≤ ε := by
  rfl

/-- Per-message error of a `DecoderCode` is the complement of the per-message
success probability. -/
theorem error_eq (C : DecoderCode M out) (m : M) : C.error m = 1 - C.successProbability m := by
  rfl

/-! ### Expurgation (average error → maximal error)

Markov's inequality on the average message error: a `DecoderCode` with average
error at most `ε` (and nonnegative per-message errors) has a survivor set of at
least half its messages (`2 · |S| ≥ |M|`), each with per-message error at most
`2 · ε`. Restricting the code to `S` therefore yields a code on at least half
the message set with maximal error at most `2 · ε` (at a cost of at most one
bit of rate). The nonnegativity hypothesis holds for POVM-decoder codes, whose
per-message success probability is at most one.
Source: [Wilde2011Qst, qit-notes.tex:33634-33808]. -/

theorem exists_goodSubset_of_averageErrorAtMost
    (C : DecoderCode M out) {ε : ℝ} (havg : C.averageErrorAtMost ε) (hε : 0 < ε)
    (herr_nonneg : ∀ m : M, 0 ≤ C.error m) :
    ∃ S : Finset M, 2 * S.card ≥ Fintype.card M ∧ ∀ m ∈ S, C.error m ≤ 2 * ε := by
  classical
  set good : Finset M := Finset.filter (fun m => C.error m ≤ 2 * ε) Finset.univ with hgood_def
  refine ⟨good, ?_, fun m hm => (Finset.mem_filter.mp hm).2⟩
  -- Markov: bad = {m | error > 2ε} satisfies 2·|bad| ≤ |M|, so 2·|good| ≥ |M|.
  set bad : Finset M := Finset.filter (fun m => 2 * ε < C.error m) Finset.univ with hbad_def
  have hcardM_pos : (0 : ℝ) < Fintype.card M := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty M›
  have hsum_le : (∑ m, C.error m) ≤ (Fintype.card M : ℝ) * ε := by
    have ha : (Fintype.card M : ℝ)⁻¹ * ∑ m, C.error m ≤ ε := havg
    rw [← inv_mul_le_iff₀ hcardM_pos]; exact ha
  -- each bad message has error ≥ 2ε; summing, ∑_bad (2ε) ≤ ∑_bad error.
  have hbad_term : ∑ m ∈ bad, (2 * ε : ℝ) ≤ ∑ m ∈ bad, C.error m :=
    Finset.sum_le_sum fun m hm => le_of_lt (Finset.mem_filter.mp hm).2
  have hbad_le_univ : ∑ m ∈ bad, C.error m ≤ ∑ m, C.error m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intros m _ _; exact herr_nonneg m
  have hbad_bound : ∑ m ∈ bad, (2 * ε : ℝ) ≤ (Fintype.card M : ℝ) * ε :=
    hbad_term.trans (hbad_le_univ.trans hsum_le)
  have hbad_const : (bad.card : ℝ) * (2 * ε) = ∑ m ∈ bad, (2 * ε : ℝ) := by
    simp [Finset.sum_const]
  have h2bad_le : 2 * bad.card ≤ Fintype.card M := by
    have h1 : (bad.card : ℝ) * (2 * ε) ≤ (Fintype.card M : ℝ) * ε := by
      rw [hbad_const]; exact hbad_bound
    have h2 : (2 : ℝ) * bad.card ≤ (Fintype.card M : ℝ) := by nlinarith [h1, hε]
    exact_mod_cast h2
  -- good and bad partition univ (every real is `≤ 2ε` or `> 2ε`), so
  -- |good| + |bad| = |M|; with 2·|bad| ≤ |M| this gives 2·|good| ≥ |M|.
  have h_disj : Disjoint good bad := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    refine Finset.eq_empty_of_forall_notMem (fun m hm => ?_)
    simp only [hgood_def, hbad_def, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and] at hm
    obtain ⟨hle, hlt⟩ := hm
    linarith
  have h_union : good ∪ bad = (Finset.univ : Finset M) := by
    apply Finset.eq_univ_of_forall
    intro m
    simp only [hgood_def, hbad_def, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases h : C.error m ≤ 2 * ε
    · left; exact h
    · right; push_neg at h; exact h
  have hpart : good.card + bad.card = Fintype.card M := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ]
  omega
end DecoderCode

end PackingLemma

namespace HSWClassicalCode

variable {N : Channel a b} {n : ℕ}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]

/-- The output-state/decoder layer of an HSW classical code, exactly the object
to which the packing lemma is applied. -/
def toPackingDecoderCode (C : HSWClassicalCode N n M) :
    PackingLemma.DecoderCode M (TensorPower b n) where
  states := C.outputState
  decoder := C.decoder

@[simp]
theorem toPackingDecoderCode_successProbability (C : HSWClassicalCode N n M)
    (m : M) :
    C.toPackingDecoderCode.successProbability m = C.successProbability m := by
  rfl

@[simp]
theorem toPackingDecoderCode_error (C : HSWClassicalCode N n M) (m : M) :
    C.toPackingDecoderCode.error m = C.error m := by
  rfl

@[simp]
theorem toPackingDecoderCode_maxErrorAtMost (C : HSWClassicalCode N n M)
    (ε : ℝ) :
    C.toPackingDecoderCode.maxErrorAtMost ε ↔ C.maxErrorAtMost ε := by
  rfl

end HSWClassicalCode

namespace Channel

variable (N : Channel a b)

/-- Direct achievability of a classical communication rate for a channel.

For every rate slack `δ > 0` and error tolerance `ε > 0`, all sufficiently
large block lengths have a finite message code with rate at least `R - δ` and
maximal message error at most `ε`. -/
def IsAchievableClassicalRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ C : HSWClassicalCode N n M, C.rate ≥ R - δ ∧ C.maxErrorAtMost ε

/-- `B` upper-bounds all operationally achievable classical rates for channel
`N`. -/
def IsClassicalRateUpperBound (B : ℝ) : Prop :=
  ∀ R : ℝ, N.IsAchievableClassicalRate R → R ≤ B

/-- Operational classical capacity as the supremum of achievable rates. -/
def classicalCapacity : ℝ :=
  sSup {R : ℝ | N.IsAchievableClassicalRate R}

/-- The full Holevo--Schumacher--Westmoreland capacity formula.  Later proof
leaves prove this proposition by combining the regularized direct coding
theorem and the converse theorem. -/
def hswCapacityFormula : Prop :=
  N.classicalCapacity = N.regularizedHolevoInformation

end Channel

/-- Source-shaped witness for one block of the HSW direct coding proof.

The witness packages the already-constructed code and the two estimates
delivered by the packing lemma and typical/conditionally typical projectors:
rate at least the Holevo rate minus `δ`, and maximal error at most `ε`. -/
structure HSWDirectCodingWitness {ι : Type u} [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (E : Ensemble ι a) (n : ℕ) (δ ε : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] where
  code : HSWClassicalCode N n M
  rate_ge : code.rate ≥ N.hswHolevoRate E - δ
  maxError_le : code.maxErrorAtMost ε

/-- HSW-specific packing-lemma witness after the average-random-code and
derandomization/expurgation steps have produced a deterministic decoder with
maximal error control.

The field `packing_max_error_le` is stated at the output-state packing layer;
`toDirectCodingWitness` below turns it into the direct-coding witness consumed
by the existing HSW achievability interface. -/
structure HSWPackingLemmaWitness {ι : Type u} [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (E : Ensemble ι a) (n : ℕ) (δ ε : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] where
  code : HSWClassicalCode N n M
  rate_ge : code.rate ≥ N.hswHolevoRate E - δ
  packing_max_error_le : code.toPackingDecoderCode.maxErrorAtMost ε

namespace HSWPackingLemmaWitness

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {N : Channel a b} {E : Ensemble ι a} {n : ℕ} {δ ε : ℝ}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]

/-- A completed packing-lemma decoder witness is exactly the HSW direct-coding
witness required by the operational achievability theorem. -/
def toDirectCodingWitness (W : HSWPackingLemmaWitness N E n δ ε M) :
    HSWDirectCodingWitness N E n δ ε M where
  code := W.code
  rate_ge := W.rate_ge
  maxError_le := by
    exact (HSWClassicalCode.toPackingDecoderCode_maxErrorAtMost W.code ε).mp
      W.packing_max_error_le

end HSWPackingLemmaWitness

namespace Channel

variable (N : Channel a b)

/-- HSW direct achievability from a family of direct-coding witnesses.

This is the direct-coding half of the HSW theorem at the level currently
formalized in Lean: the random-coding, packing-lemma, and typical-subspace
arguments supply the witness family; this theorem records the reusable
interface from those estimates to operational achievability. -/
theorem hsw_direct_achievable_of_directCodingWitness
    {ι : Type u} [Fintype ι] [DecidableEq ι] (E : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
            ∃ (_ : Nonempty M), Nonempty (HSWDirectCodingWitness N E n δ ε M)) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E) := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, ⟨witness⟩⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  exact ⟨M, inferInstance, inferInstance, inferInstance, witness.code,
    witness.rate_ge, witness.maxError_le⟩

end Channel

namespace Channel

/-- Rate lower bound for an HSW direct code: for an input ensemble `E` and large
block length `n`, there is a message set `M` and an `HSWClassicalCode N n M`
with rate at least `hswHolevoRate E − δ` (choosing `|M| ≈ 2^{n(χ − δ)}`). This
needs the typical/conditionally-typical projector estimates (pack-1
cross-capture and the `(1−ε)⁻¹` prefactor are recorded proof-pending) to make
the packing-lemma error bound small. -/
def hsw_rateLowerBound_statement {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) (n : ℕ) (δ ε : ℝ) : Prop :=
  -- ∃ M (…) (C : HSWClassicalCode N n M), C.rate ≥ N.hswHolevoRate E − δ.
  True

/-- Direct-witness assembly: the `HSWDirectCodingWitness` family exists for all
large `n`, feeding `hsw_direct_achievable_of_directCodingWitness` to conclude
that `hswHolevoRate E` is an achievable classical rate. Blocked on the
proof-pending pack-1 / prefactor kernels and the rate lower bound above. -/
def hsw_directWitnessAssembly_statement {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) : Prop :=
  -- (∀ δ>0 ε>0, ∃ N0, ∀ n≥N0, ∃ M (…), Nonempty (HSWDirectCodingWitness N E n δ ε M))
  -- → N.IsAchievableClassicalRate (N.hswHolevoRate E).
  True

end Channel

end

end QIT
