/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.Holevo
public import QIT.Core.Channel
public import QIT.States.TraceNorm.Distance

/-!
# State merging / FQSW direct rate API

This module records the operational API for the state-transfer form of state
merging used by the fully quantum Slepian--Wolf (FQSW) route.  The direct
achievability theorem is intentionally conditional on an explicit coding
witness family: the random-decoupling construction and optimality/converse
arguments are separate upstream proof obligations.

The rate convention follows the FQSW source route:
`(1/2) I(A;R)` qubits of communication from Alice to Bob
[AbeyesingheDevetakHaydenWinter2006Mother, fqsw.tex:352-372].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

namespace State

/-- Marginal state on `A × R` from a left-associated tripartite state
`(A × B) × R`.

This is the state whose mutual information gives the FQSW/state-transfer
communication rate. -/
def stateMergingReferenceState (ρ : State (Prod (Prod a b) r)) : State (Prod a r) where
  matrix := fun ar ar' =>
    Finset.univ.sum fun j : b => ρ.matrix ((ar.1, j), ar.2) ((ar'.1, j), ar'.2)
  pos := by
    let block : b → CMatrix (Prod a r) := fun j =>
      ρ.matrix.submatrix
        (fun ar : Prod a r => ((ar.1, j), ar.2))
        (fun ar : Prod a r => ((ar.1, j), ar.2))
    have hsum : (∑ j : b, block j).PosSemidef := by
      classical
      refine Finset.induction_on (s := Finset.univ) ?_ ?_
      · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix (Prod a r)).PosSemidef)
      · intro j s hjs hs
        simpa [Finset.sum_insert hjs, block] using
          (ρ.pos.submatrix (fun ar : Prod a r => ((ar.1, j), ar.2))).add hs
    convert hsum using 1
    ext ar ar'
    simp [block, Matrix.sum_apply]
  trace_eq_one := by
    rw [← ρ.trace_eq_one]
    rw [Matrix.trace]
    change
      (∑ ar : Prod a r, ∑ j : b,
        ρ.matrix ((ar.1, j), ar.2) ((ar.1, j), ar.2)) =
      ∑ x : Prod (Prod a b) r, ρ.matrix x x
    calc
      (∑ ar : Prod a r, ∑ j : b,
          ρ.matrix ((ar.1, j), ar.2) ((ar.1, j), ar.2)) =
          ∑ j : b, ∑ ar : Prod a r,
            ρ.matrix ((ar.1, j), ar.2) ((ar.1, j), ar.2) := by
        rw [Finset.sum_comm]
      _ = ∑ j : b, ∑ i : a, ∑ k : r,
            ρ.matrix ((i, j), k) ((i, j), k) := by
        simp [Fintype.sum_prod_type]
      _ = ∑ i : a, ∑ j : b, ∑ k : r,
            ρ.matrix ((i, j), k) ((i, j), k) := by
        rw [Finset.sum_comm]
      _ = ∑ x : Prod (Prod a b) r, ρ.matrix x x := by
        simp [Fintype.sum_prod_type]

/-- FQSW reference mutual information `I(A;R)` for a tripartite source state. -/
def stateMergingReferenceMutualInformation (ρ : State (Prod (Prod a b) r)) : ℝ :=
  mutualInformation ρ.stateMergingReferenceState

/-- FQSW/state-transfer quantum communication rate `(1/2) I(A;R)`. -/
def stateMergingRate (ρ : State (Prod (Prod a b) r)) : ℝ :=
  (1 / 2 : ℝ) * ρ.stateMergingReferenceMutualInformation

end State

/-- Register rate for an `n`-block state-merging transmitted quantum register.

The degenerate `n = 0` block is assigned rate zero; asymptotic statements use
the quantity only for sufficiently large positive block lengths. -/
def stateMergingQuantumRate (Q : Type u) [Fintype Q] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card Q : ℝ) / (n : ℝ)

/-- A finite-dimensional state-merging/FQSW protocol skeleton for `n` copies
of a tripartite source `ρ`.

The encoder/decoder fields expose the operational systems.  The source-shaped
direct theorem consumes the realized output and target states through the error
field below, leaving the decoupling construction of those states to upstream
proofs. -/
structure StateMergingProtocol (ρ : State (Prod (Prod a b) r)) (n : ℕ)
    (Q : Type u) [Fintype Q] [DecidableEq Q] where
  aliceEncoder : Channel (TensorPower a n) Q
  bobDecoder : Channel (Prod Q (TensorPower b n)) (TensorPower (Prod a b) n)
  outputState : State (TensorPower (Prod (Prod a b) r) n)
  targetState : State (TensorPower (Prod (Prod a b) r) n)

namespace StateMergingProtocol

variable {ρ : State (Prod (Prod a b) r)} {n : ℕ}
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Normalized trace-distance error of a state-merging protocol. -/
def error (C : StateMergingProtocol ρ n Q) : ℝ :=
  C.outputState.normalizedTraceDistance C.targetState

/-- Quantum communication rate of the transmitted register. -/
def rate (_C : StateMergingProtocol ρ n Q) : ℝ :=
  stateMergingQuantumRate Q n

theorem error_nonneg (C : StateMergingProtocol ρ n Q) : 0 ≤ C.error :=
  State.normalizedTraceDistance_nonneg _ _

end StateMergingProtocol

/-- Source-shaped witness for one block of the FQSW/state-merging direct route.

The witness packages a constructed protocol and the two estimates used by the
direct achievability interface: communication rate bounded by
`(1/2) I(A;R) + δ` and normalized trace-distance error bounded by `ε`. -/
structure StateMergingDirectWitness (ρ : State (Prod (Prod a b) r)) (n : ℕ)
    (δ ε : ℝ) (Q : Type u) [Fintype Q] [DecidableEq Q] where
  protocol : StateMergingProtocol ρ n Q
  rate_le : protocol.rate ≤ ρ.stateMergingRate + δ
  error_le : protocol.error ≤ ε

/-- Source-shaped decoupling witness for one block of the FQSW/state-merging
proof route.

The witness records the quantitative estimate supplied by the decoupling and
typicality analysis: the constructed protocol has the desired communication
rate, and its operational error is bounded by an explicit decoupling error
which is itself at most the requested tolerance.  It does not prove the
one-shot Haar decoupling theorem or the typical-subspace estimates. -/
structure StateMergingDecouplingWitness (ρ : State (Prod (Prod a b) r)) (n : ℕ)
    (δ ε : ℝ) (Q : Type u) [Fintype Q] [DecidableEq Q] where
  protocol : StateMergingProtocol ρ n Q
  rate_le : protocol.rate ≤ ρ.stateMergingRate + δ
  decouplingError : ℝ
  protocol_error_le_decouplingError : protocol.error ≤ decouplingError
  decouplingError_le : decouplingError ≤ ε

namespace StateMergingDecouplingWitness

variable {ρ : State (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- A decoupling witness immediately supplies the direct-coding witness used
by the operational achievability theorem. -/
def toDirectWitness (w : StateMergingDecouplingWitness ρ n δ ε Q) :
    StateMergingDirectWitness ρ n δ ε Q where
  protocol := w.protocol
  rate_le := w.rate_le
  error_le := le_trans w.protocol_error_le_decouplingError w.decouplingError_le

end StateMergingDecouplingWitness

namespace State

/-- Direct achievability of a state-merging/FQSW quantum communication rate.

For every rate slack `δ > 0` and error tolerance `ε > 0`, all sufficiently
large block lengths have a finite transmitted quantum register and a protocol
of rate at most `R + δ` and error at most `ε`. -/
def IsAchievableStateMergingRate (ρ : State (Prod (Prod a b) r)) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (Q : Type u), ∃ (_ : Fintype Q), ∃ (_ : DecidableEq Q),
        ∃ C : StateMergingProtocol ρ n Q, C.rate ≤ R + δ ∧ C.error ≤ ε

/-- A family of direct-coding witnesses proves achievability of the FQSW
state-merging rate `(1/2) I(A;R)`.

This theorem is the API closure for the direct route: decoupling supplies the
witness family; this theorem records the reusable Lean interface from those
estimates to the operational achievability predicate. -/
theorem stateMerging_direct_achievable_of_directCodingWitness
    (ρ : State (Prod (Prod a b) r))
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∃ (Q : Type u), ∃ (_ : Fintype Q), ∃ (_ : DecidableEq Q),
            Nonempty (StateMergingDirectWitness ρ n δ ε Q)) :
    ρ.IsAchievableStateMergingRate ρ.stateMergingRate := by
  intro δ hδ ε hε
  obtain ⟨N, hN⟩ := h δ hδ ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨Q, hQfin, hQdec, ⟨witness⟩⟩ := hN n hn
  letI : Fintype Q := hQfin
  letI : DecidableEq Q := hQdec
  exact ⟨Q, inferInstance, inferInstance, witness.protocol,
    witness.rate_le, witness.error_le⟩

/-- A family of decoupling/typicality witnesses proves achievability of the
FQSW state-merging rate `(1/2) I(A;R)`.

This is the Lean closure for the decoupling route to state merging: the
one-shot decoupling theorem and i.i.d. typical-subspace estimates provide the
witness family, while this theorem records the reusable interface from those
estimates to the operational achievability predicate. -/
theorem stateMerging_direct_achievable_of_decouplingWitness
    (ρ : State (Prod (Prod a b) r))
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∃ (Q : Type u), ∃ (_ : Fintype Q), ∃ (_ : DecidableEq Q),
            Nonempty (StateMergingDecouplingWitness ρ n δ ε Q)) :
    ρ.IsAchievableStateMergingRate ρ.stateMergingRate :=
  stateMerging_direct_achievable_of_directCodingWitness ρ (by
    intro δ hδ ε hε
    obtain ⟨N, hN⟩ := h δ hδ ε hε
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨Q, hQfin, hQdec, ⟨witness⟩⟩ := hN n hn
    letI : Fintype Q := hQfin
    letI : DecidableEq Q := hQdec
    exact ⟨Q, inferInstance, inferInstance,
      ⟨witness.toDirectWitness⟩⟩)

end State

end

end QIT
