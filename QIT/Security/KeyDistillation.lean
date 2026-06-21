/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.Key

/-!
# Key-distillation security scaffold

Definition-level API for Renner's key-distillation security scaffold, following
the correctness/secrecy decomposition in
[Renner2005QkdSecurity, main.tex:7427-7443] and the distance-from-uniform
definition in [Renner2005QkdSecurity, main.tex:6704-6718].  The API keeps abort
as an explicit classical output and separates correctness from Alice-key
secrecy.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe u v

noncomputable section

variable {κ : Type u} {e : Type v}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype e] [DecidableEq e]

/-- Two retained key outputs disagree exactly when both parties output keys
and the retained key values differ. -/
def keyPairMismatch : KeyOutput κ × KeyOutput κ → Prop
  | (some a, some b) => a ≠ b
  | _ => False

instance keyPairMismatchDecidable :
    DecidablePred (keyPairMismatch : KeyOutput κ × KeyOutput κ → Prop) := by
  intro pair
  classical
  exact Classical.propDecidable _

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem keyPairMismatch_abort_left (out : KeyOutput κ) :
    ¬ keyPairMismatch ((KeyOutput.abort : KeyOutput κ), out) := by
  cases out <;> simp [keyPairMismatch, KeyOutput.abort]

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem keyPairMismatch_abort_right (out : KeyOutput κ) :
    ¬ keyPairMismatch (out, (KeyOutput.abort : KeyOutput κ)) := by
  cases out <;> simp [keyPairMismatch, KeyOutput.abort]

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem keyPairMismatch_key_key (a b : κ) :
    keyPairMismatch (KeyOutput.key a, KeyOutput.key b) ↔ a ≠ b := by
  simp [keyPairMismatch, KeyOutput.key]

/-- Probability of the Renner correctness-bad event: neither side aborts and
the retained keys differ. -/
def keyPairMismatchProbability
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : ℝ :=
  by
    classical
    exact
      ∑ pair : KeyOutput κ × KeyOutput κ,
        if keyPairMismatch pair then (ρ.marginalA.matrix pair pair).re else 0

omit [Nonempty κ] in
@[simp]
theorem keyPairMismatchProbability_eq_sum
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    keyPairMismatchProbability ρ =
      ∑ pair : KeyOutput κ × KeyOutput κ,
        if keyPairMismatch pair then (ρ.marginalA.matrix pair pair).re else 0 :=
  by
    classical
    rfl

/-- Trace out Bob's key output while retaining Alice's key output and the side
information register. -/
def aliceKeySideInfoState
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    State (KeyOutput κ × e) where
  matrix := fun ae ae' =>
    ∑ bob : KeyOutput κ, ρ.matrix ((ae.1, bob), ae.2) ((ae'.1, bob), ae'.2)
  pos := by
    let block : KeyOutput κ → CMatrix (KeyOutput κ × e) := fun bob =>
      ρ.matrix.submatrix
        (fun ae : KeyOutput κ × e => ((ae.1, bob), ae.2))
        (fun ae : KeyOutput κ × e => ((ae.1, bob), ae.2))
    have hsum : (∑ bob : KeyOutput κ, block bob).PosSemidef := by
      classical
      refine Matrix.posSemidef_sum Finset.univ fun bob _ => ?_
      exact ρ.pos.submatrix (fun ae : KeyOutput κ × e => ((ae.1, bob), ae.2))
    convert hsum using 1
    ext ae ae'
    simp [block, Matrix.sum_apply]
  trace_eq_one := by
    rw [← ρ.trace_eq_one]
    rw [Matrix.trace]
    change
      (∑ ae : KeyOutput κ × e, ∑ bob : KeyOutput κ,
        ρ.matrix ((ae.1, bob), ae.2) ((ae.1, bob), ae.2)) =
      ∑ x : (KeyOutput κ × KeyOutput κ) × e, ρ.matrix x x
    calc
      (∑ ae : KeyOutput κ × e, ∑ bob : KeyOutput κ,
          ρ.matrix ((ae.1, bob), ae.2) ((ae.1, bob), ae.2)) =
          ∑ alice : KeyOutput κ, ∑ side : e, ∑ bob : KeyOutput κ,
            ρ.matrix ((alice, bob), side) ((alice, bob), side) := by
        rw [Fintype.sum_prod_type]
      _ =
          ∑ alice : KeyOutput κ, ∑ bob : KeyOutput κ, ∑ side : e,
            ρ.matrix ((alice, bob), side) ((alice, bob), side) := by
        apply Finset.sum_congr rfl
        intro alice _
        rw [Finset.sum_comm]
      _ = ∑ x : (KeyOutput κ × KeyOutput κ) × e, ρ.matrix x x := by
        simp [Fintype.sum_prod_type]

omit [Nonempty κ] in
@[simp]
theorem aliceKeySideInfoState_matrix
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    (aliceKeySideInfoState ρ).matrix =
      fun ae ae' =>
        ∑ bob : KeyOutput κ, ρ.matrix ((ae.1, bob), ae.2) ((ae'.1, bob), ae'.2) :=
  rfl

/-- Correctness of key distillation: the non-abort mismatched-key event has
probability at most `ε`. -/
def IsEpsilonCorrectKey (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : Prop :=
  keyPairMismatchProbability ρ ≤ ε

/-- Secrecy of Alice's retained key against the side-information register. -/
def IsEpsilonSecretAliceKey (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : Prop :=
  IsEpsilonSecretKey ε (aliceKeySideInfoState ρ)

/-- Ideal same-key pair distribution: abort has probability zero and the two
retained key outputs are equal and uniform. -/
def uniformSameKeyPairProb : KeyOutput κ × KeyOutput κ → ℝ≥0
  | (some a, some b) => if a = b then (Fintype.card κ : ℝ≥0)⁻¹ else 0
  | _ => 0

omit [Nonempty κ] in
@[simp]
theorem uniformSameKeyPairProb_abort_left (out : KeyOutput κ) :
    uniformSameKeyPairProb ((KeyOutput.abort : KeyOutput κ), out) = 0 := by
  cases out <;> simp [uniformSameKeyPairProb, KeyOutput.abort]

omit [Nonempty κ] in
@[simp]
theorem uniformSameKeyPairProb_abort_right (out : KeyOutput κ) :
    uniformSameKeyPairProb (out, (KeyOutput.abort : KeyOutput κ)) = 0 := by
  cases out <;> simp [uniformSameKeyPairProb, KeyOutput.abort]

omit [Nonempty κ] in
@[simp]
theorem uniformSameKeyPairProb_key_key (a b : κ) :
    uniformSameKeyPairProb (KeyOutput.key a, KeyOutput.key b) =
      if a = b then (Fintype.card κ : ℝ≥0)⁻¹ else 0 := by
  simp [uniformSameKeyPairProb, KeyOutput.key]

theorem uniformSameKeyPairProb_sum :
    (∑ pair : KeyOutput κ × KeyOutput κ, uniformSameKeyPairProb (κ := κ) pair) = 1 := by
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_option]
  simp [uniformSameKeyPairProb, Fintype.sum_option]

/-- The ideal same-key pair state `ρ_UU`. -/
def uniformSameKeyPairState : State (KeyOutput κ × KeyOutput κ) :=
  Classical.diagonalState (uniformSameKeyPairProb (κ := κ)) uniformSameKeyPairProb_sum

@[simp]
theorem uniformSameKeyPairState_matrix :
    (uniformSameKeyPairState (κ := κ)).matrix =
      Matrix.diagonal fun pair => (uniformSameKeyPairProb (κ := κ) pair : ℂ) :=
  rfl

/-- The ideal key-pair state associated to a real key-pair/side-information
state: a same uniform key pair product with the real side-information
marginal. -/
def idealKeyPairStateFor
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    State ((KeyOutput κ × KeyOutput κ) × e) :=
  (uniformSameKeyPairState (κ := κ)).prod ρ.marginalB

@[simp]
theorem idealKeyPairStateFor_matrix
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    (idealKeyPairStateFor ρ).matrix =
      Matrix.kronecker (uniformSameKeyPairState (κ := κ)).matrix ρ.marginalB.matrix :=
  rfl

/-- Full key-pair security distance to the ideal same-key pair product state. -/
def keyPairSecurityDistance
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : ℝ :=
  ρ.normalizedTraceDistance (idealKeyPairStateFor ρ)

/-- Real-vs-ideal key-pair security predicate. -/
def IsEpsilonSecureKeyPair (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : Prop :=
  keyPairSecurityDistance ρ ≤ ε

/-- Renner's correctness/secrecy split: correctness of the two retained keys
and secrecy of Alice's key. -/
def IsEpsilonCorrectAndSecret (εcorr εsec : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : Prop :=
  IsEpsilonCorrectKey εcorr ρ ∧ IsEpsilonSecretAliceKey εsec ρ

/-- A source-aligned full-security scaffold: correctness and secrecy are
available with errors whose sum is bounded by `ε`.  This is intentionally a
scaffold predicate, not the heavier trace-distance implication theorem. -/
def IsEpsilonFullSecurityScaffold (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : Prop :=
  ∃ εcorr εsec : ℝ,
    εcorr + εsec ≤ ε ∧ IsEpsilonCorrectAndSecret εcorr εsec ρ

omit [Nonempty κ] in
@[simp]
theorem isEpsilonCorrectKey_iff (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    IsEpsilonCorrectKey ε ρ ↔ keyPairMismatchProbability ρ ≤ ε :=
  Iff.rfl

@[simp]
theorem isEpsilonSecretAliceKey_iff (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    IsEpsilonSecretAliceKey ε ρ ↔
      IsEpsilonSecretKey ε (aliceKeySideInfoState ρ) :=
  Iff.rfl

@[simp]
theorem isEpsilonSecureKeyPair_iff (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    IsEpsilonSecureKeyPair ε ρ ↔ keyPairSecurityDistance ρ ≤ ε :=
  Iff.rfl

@[simp]
theorem keyPairSecurityDistance_eq_normalizedTraceDistance
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    keyPairSecurityDistance ρ =
      ρ.normalizedTraceDistance (idealKeyPairStateFor ρ) :=
  rfl

theorem correct_and_secret_of_bounds {εcorr εsec ε : ℝ}
    {ρ : State ((KeyOutput κ × KeyOutput κ) × e)}
    (hsum : εcorr + εsec ≤ ε)
    (hcorr : IsEpsilonCorrectKey εcorr ρ)
    (hsec : IsEpsilonSecretAliceKey εsec ρ) :
    IsEpsilonFullSecurityScaffold ε ρ :=
  ⟨εcorr, εsec, hsum, ⟨hcorr, hsec⟩⟩

namespace KeyDistillation

/-- Public catalog entrypoint for the key-distillation correctness/secrecy
scaffold. -/
public theorem main (εcorr εsec ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    IsEpsilonCorrectKey εcorr ρ →
      IsEpsilonSecretAliceKey εsec ρ →
        εcorr + εsec ≤ ε →
          IsEpsilonFullSecurityScaffold ε ρ := by
  intro hcorr hsec hsum
  exact correct_and_secret_of_bounds hsum hcorr hsec

end KeyDistillation

end

end QIT.Security
