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

open scoped ComplexOrder MatrixOrder NNReal

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
