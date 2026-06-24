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

Definition of the classical capacity of a quantum channel via regularized
Holevo information, plus the source-shaped direct-achievability interface.

The proved theorem in this module is intentionally conditional on an explicit
HSW coding witness: constructing the random code, packing-lemma decoder, and
typical/conditionally typical projector estimates is a separate upstream proof
obligation.  The formulation follows the direct coding route in
[Wilde2011Qst, qit-notes.tex:33634-33808].
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/- The n-use regularized Holevo capacity shape for a channel N.

For n uses of channel N, the achievable Holevo information rate is
(1/n) max_E chi(N^{kron n}(E)), where the max is over ensembles E
on the input of N^{kron n}. -/
def regularizedHolevoRate_statement
    (_N : Channel a b) (_n : ℕ) (_rate : ℝ) : Prop :=
  True

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

/- The HSW coding theorem: the classical capacity C(N) equals the
regularized Holevo information

C(N) = sup_n (1/n) max_E chi(N^{kron n}(E))

and this rate is achievable with vanishing error for large n. -/
def hswCodingTheorem_statement
    (_N : Channel a b) (_capacity : ℝ) : Prop :=
  True

/-- Compatibility bridge to the earlier lightweight HSW statement scaffold.

The existing statement only records the high-level capacity shape, so this
lemma should not be used as evidence for the full HSW theorem.  The public Lean
evidence theorem is `Channel.hsw_direct_achievable_of_directCodingWitness`. -/
theorem hswCodingTheorem_statement_of_direct_achievable
    (N : Channel a b) (capacity : ℝ)
    (_h : N.IsAchievableClassicalRate capacity) :
    hswCodingTheorem_statement N capacity := by
  trivial

end

end QIT
