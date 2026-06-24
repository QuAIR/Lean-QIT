/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Typicality
public import QIT.Core.Channel
public import QIT.States.TraceNorm.Distance

/-!
# Schumacher direct compression scaffold

This module records the direct-coding interface for Schumacher compression.
The theorem is intentionally conditional on a typical-compression witness:
constructing the spectral typical projector from AEP is a separate upstream
proof obligation.  The formulation follows the direct-coding part of
[Wilde2011Qst, qit-notes.tex:31275-31295].
-/

@[expose] public section

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Register rate for an `n`-block compression register `W`.

For the degenerate `n = 0` block the rate is set to zero; all asymptotic
coding statements consume this only for sufficiently large positive block
lengths. -/
def schumacherRegisterRate (W : Type u) [Fintype W] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card W : ℝ) / (n : ℝ)

/-- A finite-dimensional Schumacher compression code for `n` copies of `ρ`.

The compressed register is `W`; the encoder maps the tensor-power source into
`W`, and the decoder maps `W` back to the original tensor-power system. -/
structure SchumacherCompressionCode (ρ : State a) (n : ℕ)
    (W : Type u) [Fintype W] [DecidableEq W] where
  encoder : Channel (TensorPower a n) W
  decoder : Channel W (TensorPower a n)

namespace SchumacherCompressionCode

variable {ρ : State a} {n : ℕ} {W : Type u} [Fintype W] [DecidableEq W]

/-- Decoded output state of a Schumacher compression code. -/
def outputState (C : SchumacherCompressionCode ρ n W) : State (TensorPower a n) :=
  C.decoder.applyState (C.encoder.applyState (ρ.tensorPower n))

/-- Normalized trace-distance error against the original `n`-fold source. -/
def error (C : SchumacherCompressionCode ρ n W) : ℝ :=
  (C.outputState).normalizedTraceDistance (ρ.tensorPower n)

/-- Register rate of the compressed system. -/
def rate (_C : SchumacherCompressionCode ρ n W) : ℝ :=
  schumacherRegisterRate W n

theorem error_nonneg (C : SchumacherCompressionCode ρ n W) : 0 ≤ C.error :=
  State.normalizedTraceDistance_nonneg _ _

end SchumacherCompressionCode

/-- Source-shaped witness for one block of the direct Schumacher coding proof.

The witness packages the already-constructed typical-subspace compression
code together with the two estimates used by the direct theorem: rate bounded
by `S(ρ)+δ` and normalized trace-distance error bounded by `ε`. -/
structure TypicalCompressionWitness (ρ : State a) (n : ℕ) (δ ε : ℝ)
    (W : Type u) [Fintype W] [DecidableEq W] where
  code : SchumacherCompressionCode ρ n W
  rate_le : code.rate ≤ ρ.schumacherRate + δ
  error_le : code.error ≤ ε

namespace State

/-- Direct achievability of a Schumacher compression rate.

For every rate slack `δ > 0` and error tolerance `ε > 0`, all sufficiently
large block lengths have a finite compression register and a code of rate at
most `R + δ` and error at most `ε`. -/
def IsAchievableSchumacherRate (ρ : State a) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
        ∃ C : SchumacherCompressionCode ρ n W, C.rate ≤ R + δ ∧ C.error ≤ ε

/-- A family of typical-compression witnesses proves the direct achievability
of the Schumacher rate `S(ρ)`.

This is the direct-coding half of Schumacher compression: AEP/spectral
typicality supplies the witness family; this theorem records the reusable
Lean interface from that family to achievability. -/
theorem schumacher_direct_achievable_of_typicalCompressionWitness
    (ρ : State a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
            Nonempty (TypicalCompressionWitness ρ n δ ε W)) :
    ρ.IsAchievableSchumacherRate ρ.schumacherRate := by
  intro δ hδ ε hε
  obtain ⟨N, hN⟩ := h δ hδ ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨W, hWfin, hWdec, ⟨witness⟩⟩ := hN n hn
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, inferInstance, inferInstance, witness.code, witness.rate_le, witness.error_le⟩

/-- Compatibility bridge to the earlier lightweight statement scaffold.

The existing statement only records the rate-side asymptotic shape, so this
lemma should not be used as evidence for the operational theorem.  The public
evidence theorem is `schumacher_direct_achievable_of_typicalCompressionWitness`.
-/
theorem schumacherTheorem_statement_of_direct_achievable
    (ρ : State a) (h : ρ.IsAchievableSchumacherRate ρ.schumacherRate) :
    ρ.schumacherTheorem_statement := by
  intro ε hε δ hδ
  obtain ⟨N, _hN⟩ := h δ hδ ε hε
  refine ⟨N, ?_⟩
  intro n _hn
  exact le_add_of_nonneg_right (le_of_lt hδ)

end State

end

end QIT
