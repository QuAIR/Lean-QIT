/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.Typicality
public import QIT.Core.Channel
public import QIT.States.Purification.Canonical
public import QIT.States.TraceNorm.Distance

/-!
# Schumacher compression code interface

This module records the finite-dimensional compression-code interface for
Schumacher quantum data compression.  The operational fidelity criterion is
the *purification joint trace distance* `jointError`, matching the success
criterion of the Wilde converse route
[Wilde2011Qst, qit-notes.tex:31610-31690].  The direct achievability,
converse, and limit-equality theorems live in sibling modules
`SchumacherDirect`, `SchumacherConverse`, and `SchumacherLimit`.

The earlier A-only marginal fidelity is intentionally not used as the
operational notion: a dephasing channel in the `ρ^{⊗ n}` eigenbasis attains
zero A-marginal error at rate `0 < S(ρ)`, so the A-only criterion does not
support any converse.  The joint (purification) criterion is the one under
which the optimal compression rate equals the von Neumann entropy.
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

/-- Decoded system-side output state of a Schumacher compression code. -/
def outputState (C : SchumacherCompressionCode ρ n W) : State (TensorPower a n) :=
  C.decoder.applyState (C.encoder.applyState (ρ.tensorPower n))

/-- Joint (purification) trace-distance error of a Schumacher code.

This is the operational fidelity criterion for quantum data compression.
Purify the source `ρ` canonically to `φ_{RA}` (system on `marginalB`,
reference `R ≅ A` on `marginalA`), take the `n`-fold bipartite tensor power
`φ_{RA}^{⊗ n}` on `R^{n} A^{n}`, apply the compression map `D ∘ E` to the
system side and the identity channel to the reference, and measure the
normalized trace distance of the resulting joint state `ω_{R^{n}Â^{n}}` from
`φ_{RA}^{⊗ n}`. The tensor-power purification (rather than a single canonical
purification of `ρ^{⊗ n}`) is used so that the quantum mutual information
`I(A^{n};R^{n})` decomposes additively, as required by the Wilde converse
[Wilde2011Qst, qit-notes.tex:31610-31690]. -/
def jointError (C : SchumacherCompressionCode ρ n W) : ℝ :=
  let φ : State (Prod (TensorPower a n) (TensorPower a n)) :=
    (State.canonicalPurification ρ).state.tensorPowerBipartite n
  let N : Channel (TensorPower a n) (TensorPower a n) :=
    C.decoder.comp C.encoder
  let ω : State (Prod (TensorPower a n) (TensorPower a n)) :=
    ((Channel.idChannel (TensorPower a n)).prod N).applyState φ
  ω.normalizedTraceDistance φ

/-- Register rate of the compressed system. -/
def rate (_C : SchumacherCompressionCode ρ n W) : ℝ :=
  schumacherRegisterRate W n

end SchumacherCompressionCode

/-- Source-shaped witness for one block of the direct Schumacher coding proof.

The witness packages an explicit compression code together with the two
estimates used by the direct theorem: register rate bounded by `S(ρ)+δ` and
joint (purification) trace-distance error bounded by `ε`. -/
structure TypicalCompressionWitness (ρ : State a) (n : ℕ) (δ ε : ℝ)
    (W : Type u) [Fintype W] [DecidableEq W] where
  code : SchumacherCompressionCode ρ n W
  rate_le : code.rate ≤ ρ.schumacherRate + δ
  jointError_le : code.jointError ≤ ε

namespace State

/-- Direct achievability of a Schumacher compression rate (joint fidelity).

For every rate slack `δ > 0` and joint-error tolerance `ε > 0`, all
sufficiently large block lengths have a finite compression register and a code
of rate at most `R + δ` and joint error at most `ε`. -/
def IsAchievableSchumacherRate (ρ : State a) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
        ∃ C : SchumacherCompressionCode ρ n W, C.rate ≤ R + δ ∧ C.jointError ≤ ε

/-- A family of joint-fidelity typical-compression witnesses proves the direct
achievability of the Schumacher rate `S(ρ)`.

This is the reusable Lean interface from a witness family to achievability; it
is an internal bridge, not the public direct-achievability node (which
discharges the witness existence unconditionally in `SchumacherDirect`). -/
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
  exact ⟨W, inferInstance, inferInstance, witness.code, witness.rate_le,
    witness.jointError_le⟩

end State

end

end QIT
