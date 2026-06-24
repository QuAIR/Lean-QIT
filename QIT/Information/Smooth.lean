/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.CQState
public import QIT.Information.Entropy
public import QIT.Information.Fidelity
public import QIT.Core.POVMProbability
public import QIT.States.Subnormalized
public import Mathlib.Data.Real.Archimedean

/-!
# Smooth min/max entropy

Definition-level normalized-state API for purified-distance smoothing and
smooth conditional min/max entropies. The definitions follow the finite
normalized-state route used in one-shot quantum information: purified distance is
the normalized specialization of [Tomamichel2015FiniteResources,
metric.tex:512-513], conditional min/max entropy follow
[Tomamichel2015FiniteResources, calculus.tex:81-89] and
[Tomamichel2015FiniteResources, calculus.tex:191-198], and smoothing follows
[Tomamichel2015FiniteResources, calculus.tex:418-426].

Lean-QIT records entropy values in bits. Thus the min-entropy order constraint
uses `2^{-λ}` rather than the natural-exponential notation used in the source.
The cq guessing-probability interface follows [Tomamichel2015FiniteResources,
calculus.tex:348-357], but the SDP/duality proof of optimality remains a
downstream proof dependency.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-! ## Purified distance and smoothing balls -/

/-- Purified distance between normalized finite-dimensional states,
`P(ρ,σ) = sqrt(1 - F(ρ,σ)^2)`, using the local squared-fidelity convention. -/
def purifiedDistance (ρ σ : State a) : ℝ :=
  Real.sqrt (1 - ρ.squaredFidelity σ)

@[simp]
theorem purifiedDistance_eq (ρ σ : State a) :
    ρ.purifiedDistance σ = Real.sqrt (1 - ρ.squaredFidelity σ) :=
  rfl

/-- The closed purified-distance epsilon ball around a normalized state. -/
def purifiedBall (ρ : State a) (ε : ℝ) (σ : State a) : Prop :=
  ρ.purifiedDistance σ ≤ ε

@[simp]
theorem purifiedBall_eq (ρ σ : State a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔ ρ.purifiedDistance σ ≤ ε :=
  Iff.rfl

/-- Purified-distance balls are monotone in the smoothing radius. -/
theorem purifiedBall_mono {ρ σ : State a} {ε δ : ℝ} (hεδ : ε ≤ δ) :
    ρ.purifiedBall ε σ → ρ.purifiedBall δ σ := by
  intro hball
  exact le_trans hball hεδ

/-! ## Normalized/subnormalized purified-distance bridge -/

/-- Generalized fidelity reduces to squared fidelity for normalized states. -/
theorem toSubnormalized_generalizedFidelity_eq_squaredFidelity (ρ σ : State a) :
    ρ.toSubnormalized.generalizedFidelity σ.toSubnormalized = ρ.squaredFidelity σ := by
  rw [SubnormalizedState.generalizedFidelity_eq,
    State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  have hρ : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hσ : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  simp [State.sqrtMatrix, hρ, hσ]

/-- The subnormalized purified distance agrees with the normalized one after
embedding normalized states via `State.toSubnormalized`. -/
theorem toSubnormalized_purifiedDistance_eq (ρ σ : State a) :
    ρ.toSubnormalized.purifiedDistance σ.toSubnormalized = ρ.purifiedDistance σ := by
  rw [SubnormalizedState.purifiedDistance_eq, State.purifiedDistance_eq,
    toSubnormalized_generalizedFidelity_eq_squaredFidelity]

/-- Normalized purified balls are exactly the subnormalized purified balls after
embedding normalized states via `State.toSubnormalized`. -/
theorem purifiedBall_iff_toSubnormalized_purifiedBall (ρ σ : State a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔
      ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized := by
  rw [State.purifiedBall_eq, SubnormalizedState.purifiedBall_eq,
    toSubnormalized_purifiedDistance_eq]

/-! ## Conditional min/max entropy definitions -/

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- The matrix `I_A ⊗ σ_B` used in conditional min/max entropy definitions. -/
def identityTensorStateMatrix (σ : State b) : CMatrix (Prod a b) :=
  Matrix.kronecker (1 : CMatrix a) σ.matrix

/-- Feasibility predicate for the conditional min-entropy order constraint
`ρ_AB ≤ 2^{-λ} • (I_A ⊗ σ_B)` in the local bits convention. -/
def ConditionalMinEntropyFeasible (ρ : State (Prod a b)) (σ : State b) (lam : ℝ) :
    Prop :=
  ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ

@[simp]
theorem ConditionalMinEntropyFeasible_eq (ρ : State (Prod a b)) (σ : State b)
    (lam : ℝ) :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ↔
      ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ :=
  Iff.rfl

/-- Conditional min-entropy as the supremum of feasible exponents.

This is the normalized-state version of the Tomamichel finite-resources
definition; the subnormalized-state generalization is deliberately left to a
later extension. -/
def conditionalMinEntropy (ρ : State (Prod a b)) : ℝ :=
  sSup {lam : ℝ | ∃ σ : State b, ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropy_eq (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy =
      sSup {lam : ℝ | ∃ σ : State b, ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- The candidate value `log₂ F(ρ_AB, I_A ⊗ σ_B)` for conditional max-entropy.

The second argument is positive but not normalized in general, so this uses the
matrix square-root/trace-norm expression directly rather than `State.fidelity`.
The square matches the squared-fidelity convention used elsewhere in QIT. -/
def conditionalMaxEntropyCandidate (ρ : State (Prod a b)) (σ : State b) : ℝ :=
  log2 ((traceNorm (ρ.sqrtMatrix *
    psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2)

/-- Conditional max-entropy as the supremum over normalized `B` states of the
definition-level max-entropy candidate. -/
def conditionalMaxEntropy (ρ : State (Prod a b)) : ℝ :=
  sSup {h : ℝ | ∃ σ : State b, h = conditionalMaxEntropyCandidate (a := a) ρ σ}

@[simp]
theorem conditionalMaxEntropy_eq (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropy =
      sSup {h : ℝ | ∃ σ : State b, h = conditionalMaxEntropyCandidate (a := a) ρ σ} :=
  rfl

/-! ## Smooth conditional min/max entropy -/

/-- Candidate values for smooth conditional min-entropy at smoothing radius `ε`. -/
def SmoothConditionalMinEntropyCandidate (ρ : State (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMinEntropy

@[simp]
theorem SmoothConditionalMinEntropyCandidate_eq (ρ : State (Prod a b)) (ε h : ℝ) :
    SmoothConditionalMinEntropyCandidate (a := a) ρ ε h ↔
      ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
        h = ρ'.conditionalMinEntropy :=
  Iff.rfl

/-- Candidate values for smooth conditional max-entropy at smoothing radius `ε`. -/
def SmoothConditionalMaxEntropyCandidate (ρ : State (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧ h = ρ'.conditionalMaxEntropy

@[simp]
theorem SmoothConditionalMaxEntropyCandidate_eq (ρ : State (Prod a b)) (ε h : ℝ) :
    SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h ↔
      ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
        h = ρ'.conditionalMaxEntropy :=
  Iff.rfl

/-- Smooth min-entropy candidates are monotone in the smoothing radius. -/
theorem SmoothConditionalMinEntropyCandidate_mono {ρ : State (Prod a b)} {ε δ h : ℝ}
    (hεδ : ε ≤ δ) :
    SmoothConditionalMinEntropyCandidate (a := a) ρ ε h →
      SmoothConditionalMinEntropyCandidate (a := a) ρ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Smooth max-entropy candidates are monotone in the smoothing radius. -/
theorem SmoothConditionalMaxEntropyCandidate_mono {ρ : State (Prod a b)} {ε δ h : ℝ}
    (hεδ : ε ≤ δ) :
    SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h →
      SmoothConditionalMaxEntropyCandidate (a := a) ρ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Smooth conditional min-entropy as the supremum of min-entropy over the
purified-distance epsilon ball. -/
def smoothConditionalMinEntropy (ρ : State (Prod a b)) (ε : ℝ) : ℝ :=
  sSup {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h}

theorem smoothConditionalMinEntropy_eq_sSup_candidates (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMinEntropy ε =
      sSup {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMinEntropy_eq (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMinEntropy ε =
      sSup {h : ℝ |
        ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMinEntropy} :=
  rfl

/-- Smooth conditional max-entropy as the infimum of max-entropy over the
purified-distance epsilon ball. -/
def smoothConditionalMaxEntropy (ρ : State (Prod a b)) (ε : ℝ) : ℝ :=
  sInf {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h}

theorem smoothConditionalMaxEntropy_eq_sInf_candidates (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMaxEntropy ε =
      sInf {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMaxEntropy_eq (ρ : State (Prod a b)) (ε : ℝ) :
    ρ.smoothConditionalMaxEntropy ε =
      sInf {h : ℝ |
        ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMaxEntropy} :=
  rfl

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Candidate-level relation needed to turn a purification-level min/max
duality proof into the smooth entropy equality.

For every max-entropy candidate of `ρAB`, the corresponding negated value is a
min-entropy candidate of `ρAC`, and conversely. The source-shaped proof of this
predicate requires the purification-ball lifting and unsmoothed min/max duality
machinery; the theorem below isolates the order-theoretic `sInf`/`sSup` step. -/
def SmoothConditionalMinMaxCandidateDuality
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) : Prop :=
  ∀ h : ℝ,
    SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h ↔
      SmoothConditionalMinEntropyCandidate (a := a) ρAC ε (-h)

@[simp]
theorem SmoothConditionalMinMaxCandidateDuality_eq
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) :
    SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε ↔
      ∀ h : ℝ,
        SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h ↔
          SmoothConditionalMinEntropyCandidate (a := a) ρAC ε (-h) :=
  Iff.rfl

/-- Witness-level form of the purified-smoothing min/max duality route.

The first projection says every smoothed `AB` candidate has a smoothed `AC`
counterpart with unsmoothed `Hmax(AB') = -Hmin(AC')`; the second projection is
the converse direction. This predicate packages the mathematical handoff from
purification-ball lifting and unsmoothed min/max duality. -/
def SmoothConditionalMinMaxWitnessDuality
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) : Prop :=
  (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
      ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) ∧
    (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
      ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy)

@[simp]
theorem SmoothConditionalMinMaxWitnessDuality_eq
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ) :
    SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε ↔
      (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
          ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧
            ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) ∧
        (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
          ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧
            ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy) :=
  Iff.rfl

/-- Relation-parametric pairing of smoothed `AB` and `AC` candidates.

The relation is intended to express that two candidate states arise as
complementary marginals of compatible nearby purifications, while this predicate
only records the bidirectional smoothing transport property. -/
def SmoothConditionalMinMaxPairing
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ)
    (Rel : State (Prod a b) → State (Prod a c) → Prop) : Prop :=
  (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
      ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC') ∧
    (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
      ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧ Rel ρAB' ρAC')

@[simp]
theorem SmoothConditionalMinMaxPairing_eq
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c)) (ε : ℝ)
    (Rel : State (Prod a b) → State (Prod a c) → Prop) :
    SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel ↔
      (∀ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' →
          ∃ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' ∧ Rel ρAB' ρAC') ∧
        (∀ ρAC' : State (Prod a c), ρAC.purifiedBall ε ρAC' →
          ∃ ρAB' : State (Prod a b), ρAB.purifiedBall ε ρAB' ∧ Rel ρAB' ρAC') :=
  Iff.rfl

/-- Unsmoothed min/max entropy duality on each related pair of candidate states. -/
def ConditionalMinMaxEntropyDualOn
    (Rel : State (Prod a b) → State (Prod a c) → Prop) : Prop :=
  ∀ ρAB' : State (Prod a b), ∀ ρAC' : State (Prod a c), Rel ρAB' ρAC' →
    ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy

@[simp]
theorem ConditionalMinMaxEntropyDualOn_eq
    (Rel : State (Prod a b) → State (Prod a c) → Prop) :
    ConditionalMinMaxEntropyDualOn (a := a) Rel ↔
      ∀ ρAB' : State (Prod a b), ∀ ρAC' : State (Prod a c), Rel ρAB' ρAC' →
        ρAB'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy :=
  Iff.rfl

/-- Pairing transport plus unsmoothed pairwise duality gives the witness-level
smooth min/max duality predicate. -/
theorem SmoothConditionalMinMaxWitnessDuality.of_pairing_of_entropy_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    {Rel : State (Prod a b) → State (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (hdual : ConditionalMinMaxEntropyDualOn (a := a) Rel) :
    SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε := by
  constructor
  · intro ρAB' hballAB
    obtain ⟨ρAC', hballAC, hrel⟩ := hpair.1 ρAB' hballAB
    exact ⟨ρAC', hballAC, hdual ρAB' ρAC' hrel⟩
  · intro ρAC' hballAC
    obtain ⟨ρAB', hballAB, hrel⟩ := hpair.2 ρAC' hballAC
    exact ⟨ρAB', hballAB, hdual ρAB' ρAC' hrel⟩

/-- A witness-level smoothing duality immediately gives the candidate-set
duality needed by the order-theoretic bridge. -/
theorem SmoothConditionalMinMaxCandidateDuality.of_witness_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    (hwit : SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε) :
    SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε := by
  intro h
  constructor
  · rintro ⟨ρAB', hballAB, hh⟩
    obtain ⟨ρAC', hballAC, hentropy⟩ := hwit.1 ρAB' hballAB
    refine ⟨ρAC', hballAC, ?_⟩
    rw [hh, hentropy, neg_neg]
  · rintro ⟨ρAC', hballAC, hh⟩
    obtain ⟨ρAB', hballAB, hentropy⟩ := hwit.2 ρAC' hballAC
    refine ⟨ρAB', hballAB, ?_⟩
    rw [hentropy, ← hh, neg_neg]

/-- Order-theoretic smooth min/max duality bridge.

Once the max-candidate set for `ρAB` is exactly the pointwise negation of the
min-candidate set for `ρAC`, the smooth max entropy is the negative smooth min
entropy. This proves the `sInf`/`sSup` part of the purified-smoothing duality
route; the source-level purification theorem supplies the candidate relation. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    (hdual : SmoothConditionalMinMaxCandidateDuality (a := a) ρAB ρAC ε) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε := by
  let maxSet : Set ℝ := {h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρAB ε h}
  let minSet : Set ℝ := {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρAC ε h}
  have hset : maxSet = -minSet := by
    ext h
    simp only [maxSet, minSet, Set.mem_setOf_eq, Set.mem_neg]
    exact hdual h
  calc
    ρAB.smoothConditionalMaxEntropy ε = sInf maxSet := rfl
    _ = sInf (-minSet) := by rw [hset]
    _ = -sSup minSet := Real.sInf_neg minSet
    _ = -ρAC.smoothConditionalMinEntropy ε := rfl

/-- Composed smooth min/max duality bridge from witness-level smoothing
duality. This is the exact handoff point for purification-ball lifting and
unsmoothed min/max duality. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_witness_duality
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    (hwit : SmoothConditionalMinMaxWitnessDuality (a := a) ρAB ρAC ε) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε :=
  smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_duality
    (SmoothConditionalMinMaxCandidateDuality.of_witness_duality hwit)

/-- Smooth min/max duality from a relation-parametric pairing and unsmoothed
pairwise duality. -/
theorem smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_pairing
    {ρAB : State (Prod a b)} {ρAC : State (Prod a c)} {ε : ℝ}
    {Rel : State (Prod a b) → State (Prod a c) → Prop}
    (hpair : SmoothConditionalMinMaxPairing (a := a) ρAB ρAC ε Rel)
    (hdual : ConditionalMinMaxEntropyDualOn (a := a) Rel) :
    ρAB.smoothConditionalMaxEntropy ε = -ρAC.smoothConditionalMinEntropy ε :=
  smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_witness_duality
    (SmoothConditionalMinMaxWitnessDuality.of_pairing_of_entropy_duality hpair hdual)

end State

namespace Ensemble

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

/-- The score of a POVM trying to guess the classical label of an ensemble.

For a normalized cq ensemble `E = {p_x, ρ_B(x)}` and POVM `M`, this is
`∑ x p_x Pr[M outputs x | ρ_B(x)]`. -/
def cqGuessingScore (E : Ensemble ι b) (M : POVM ι b) : ℝ≥0 :=
  ∑ outcome, E.probs outcome * M.prob (E.states outcome) outcome

@[simp]
theorem cqGuessingScore_eq (E : Ensemble ι b) (M : POVM ι b) :
    E.cqGuessingScore M =
      ∑ outcome, E.probs outcome * M.prob (E.states outcome) outcome :=
  rfl

/-- Guessing scores are nonnegative after coercion to real numbers. -/
theorem cqGuessingScore_nonneg (E : Ensemble ι b) (M : POVM ι b) :
    0 ≤ ((E.cqGuessingScore M : ℝ≥0) : ℝ) :=
  NNReal.coe_nonneg _

/-- Supremum-style guessing probability over all finite POVMs with outcomes
matching the classical labels of the ensemble. -/
def cqGuessingProbability (E : Ensemble ι b) : ℝ :=
  sSup {score : ℝ | ∃ M : POVM ι b,
    score = ((E.cqGuessingScore M : ℝ≥0) : ℝ)}

@[simp]
theorem cqGuessingProbability_eq (E : Ensemble ι b) :
    E.cqGuessingProbability =
      sSup {score : ℝ | ∃ M : POVM ι b,
        score = ((E.cqGuessingScore M : ℝ≥0) : ℝ)} :=
  rfl

end Ensemble

end

/-!
The full Tomamichel subnormalized-state theory, min/max duality, the SDP
optimality proof for guessing probability, and the uncertainty-relation proof
are recorded as downstream source-backed theorem targets.
-/

end QIT
