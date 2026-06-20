/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.ClassicalBridge
public import QIT.Core.TraceNorm.Distance
public import Mathlib.Data.Fintype.Option

/-!
# Trace-distance key security predicates

Definition-level API for finite normalized key-security predicates, following
[Renner2005QkdSecurity, main.tex:2488-2514] and
[Renner2005QkdSecurity, main.tex:6704-6718].
-/

@[expose] public section

open scoped NNReal

namespace QIT.Security

universe u v

noncomputable section

/-- A key output is either an explicit abort or a retained key value. -/
abbrev KeyOutput (κ : Type u) := Option κ

namespace KeyOutput

variable {κ : Type u}

/-- The explicit abort output. -/
def abort : KeyOutput κ :=
  none

/-- A retained key output. -/
def key (k : κ) : KeyOutput κ :=
  some k

@[simp]
theorem abort_eq_none : (abort : KeyOutput κ) = none :=
  rfl

@[simp]
theorem key_eq_some (k : κ) : key k = some k :=
  rfl

@[simp]
theorem abort_ne_key (k : κ) : (abort : KeyOutput κ) ≠ key k := by
  simp [abort, key]

@[simp]
theorem key_ne_abort (k : κ) : key k ≠ (abort : KeyOutput κ) := by
  simp [abort, key]

end KeyOutput

variable {κ : Type u} {e : Type v}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype e] [DecidableEq e]

/-- The ideal key-output distribution: abort has weight zero, keys are uniform. -/
def uniformKeyOutputProb : KeyOutput κ -> ℝ≥0
  | none => 0
  | some _ => (Fintype.card κ : ℝ≥0)⁻¹

omit [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem uniformKeyOutputProb_abort :
    uniformKeyOutputProb (κ := κ) KeyOutput.abort = 0 :=
  rfl

omit [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem uniformKeyOutputProb_key (k : κ) :
    uniformKeyOutputProb (κ := κ) (KeyOutput.key k) = (Fintype.card κ : ℝ≥0)⁻¹ :=
  rfl

omit [DecidableEq κ] in
theorem uniformKeyOutputProb_sum :
    (∑ out : KeyOutput κ, uniformKeyOutputProb (κ := κ) out) = 1 := by
  rw [Fintype.sum_option]
  simp [uniformKeyOutputProb]

/-- The ideal uniform key-output state with explicit abort probability zero. -/
def uniformKeyOutputState : State (KeyOutput κ) :=
  Classical.diagonalState (uniformKeyOutputProb (κ := κ)) uniformKeyOutputProb_sum

@[simp]
theorem uniformKeyOutputState_matrix :
    (uniformKeyOutputState (κ := κ)).matrix =
      Matrix.diagonal fun out => (uniformKeyOutputProb (κ := κ) out : ℂ) :=
  rfl

/-- The ideal product of a uniform key output and adversarial side information. -/
def idealKeySideInfoState (σE : State e) : State (KeyOutput κ × e) :=
  (uniformKeyOutputState (κ := κ)).prod σE

@[simp]
theorem idealKeySideInfoState_matrix (σE : State e) :
    (idealKeySideInfoState (κ := κ) σE).matrix =
      Matrix.kronecker (uniformKeyOutputState (κ := κ)).matrix σE.matrix :=
  rfl

/-- The ideal state associated to a real key-side-information state. -/
def idealKeyStateFor (ρ : State (KeyOutput κ × e)) : State (KeyOutput κ × e) :=
  idealKeySideInfoState (κ := κ) ρ.marginalB

@[simp]
theorem idealKeyStateFor_matrix (ρ : State (KeyOutput κ × e)) :
    (idealKeyStateFor ρ).matrix =
      Matrix.kronecker (uniformKeyOutputState (κ := κ)).matrix ρ.marginalB.matrix :=
  rfl

theorem idealKeyStateFor_idealKeySideInfoState (σE : State e) :
    idealKeyStateFor (κ := κ) (idealKeySideInfoState (κ := κ) σE) =
      idealKeySideInfoState (κ := κ) σE := by
  have hm :
      (idealKeySideInfoState (κ := κ) σE).marginalB = σE := by
    apply State.ext
    exact State.partialTraceA_prod (uniformKeyOutputState (κ := κ)) σE
  unfold idealKeyStateFor
  rw [hm]

/-- Renner's distance from uniform `d(ρ_AB | B)`, without the factor `1 / 2`. -/
def distanceFromUniformGiven (ρ : State (KeyOutput κ × e)) : ℝ :=
  ρ.traceDistance (idealKeyStateFor ρ)

@[simp]
theorem distanceFromUniformGiven_eq_traceDistance (ρ : State (KeyOutput κ × e)) :
    distanceFromUniformGiven ρ = ρ.traceDistance (idealKeyStateFor ρ) :=
  rfl

/-- Trace-distance secrecy distance, using the `1 / 2 * ‖real - ideal‖₁` convention. -/
def secrecyDistance (ρ : State (KeyOutput κ × e)) : ℝ :=
  ρ.normalizedTraceDistance (idealKeyStateFor ρ)

@[simp]
theorem secrecyDistance_eq_normalizedTraceDistance (ρ : State (KeyOutput κ × e)) :
    secrecyDistance ρ = ρ.normalizedTraceDistance (idealKeyStateFor ρ) :=
  rfl

/-- A perfect key is exactly the uniform key product with its side information. -/
def IsPerfectKey (ρ : State (KeyOutput κ × e)) : Prop :=
  ρ = idealKeyStateFor ρ

/-- An `ε`-secret key is within normalized trace distance `ε` of the ideal key. -/
def IsEpsilonSecretKey (ε : ℝ) (ρ : State (KeyOutput κ × e)) : Prop :=
  secrecyDistance ρ ≤ ε

@[simp]
theorem isPerfectKey_iff (ρ : State (KeyOutput κ × e)) :
    IsPerfectKey ρ ↔ ρ = idealKeyStateFor ρ :=
  Iff.rfl

@[simp]
theorem isEpsilonSecretKey_iff (ε : ℝ) (ρ : State (KeyOutput κ × e)) :
    IsEpsilonSecretKey ε ρ ↔ secrecyDistance ρ ≤ ε :=
  Iff.rfl

theorem secrecyDistance_ideal (ρ : State (KeyOutput κ × e)) :
    secrecyDistance (idealKeyStateFor ρ) = 0 := by
  rw [show idealKeyStateFor ρ = idealKeySideInfoState (κ := κ) ρ.marginalB from rfl]
  simp [secrecyDistance, idealKeyStateFor_idealKeySideInfoState]

theorem isEpsilonSecretKey_zero_ideal (ρ : State (KeyOutput κ × e)) :
    IsEpsilonSecretKey 0 (idealKeyStateFor ρ) := by
  rw [IsEpsilonSecretKey, secrecyDistance_ideal]

theorem IsPerfectKey.isEpsilonSecretKey_zero {ρ : State (KeyOutput κ × e)}
    (hρ : IsPerfectKey ρ) : IsEpsilonSecretKey 0 ρ := by
  rw [isPerfectKey_iff] at hρ
  rw [hρ]
  exact isEpsilonSecretKey_zero_ideal ρ

namespace ComposableKey

/-- Public catalog entrypoint for the composable trace-distance key-security predicate. -/
public theorem main (ε : ℝ) (ρ : State (KeyOutput κ × e)) :
    IsEpsilonSecretKey ε ρ ↔ secrecyDistance ρ ≤ ε :=
  isEpsilonSecretKey_iff ε ρ

end ComposableKey

end

end QIT.Security
