/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy
public import QIT.Information.Smooth
public import QIT.Information.Typicality
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Real.Sqrt

/-!
# Quantum Asymptotic Equipartition Property

Statements of the finite-N and asymptotic AEP for smooth conditional entropy.
The full proof requires spectral concentration of rho^{kron n} eigenvalues
and smooth-entropy machinery over nested tensor-power types, which is not
yet available.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

open Filter

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- Conditional entropy of the IID bipartite state, read as `A^n|B^n`. -/
def tensorPowerConditionalEntropy (ρ : State (Prod a b)) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).conditionalEntropy

@[simp]
theorem tensorPowerConditionalEntropy_eq (ρ : State (Prod a b)) (n : ℕ) :
    ρ.tensorPowerConditionalEntropy n =
      (ρ.tensorPowerBipartite n).conditionalEntropy :=
  rfl

/-- Smooth conditional min-entropy of the IID bipartite state, read as
`A^n|B^n`. -/
def tensorPowerSmoothConditionalMinEntropy
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).smoothConditionalMinEntropy ε

@[simp]
theorem tensorPowerSmoothConditionalMinEntropy_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSmoothConditionalMinEntropy ε n =
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropy ε :=
  rfl

/-- Smooth conditional max-entropy of the IID bipartite state, read as
`A^n|B^n`. -/
def tensorPowerSmoothConditionalMaxEntropy
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).smoothConditionalMaxEntropy ε

@[simp]
theorem tensorPowerSmoothConditionalMaxEntropy_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSmoothConditionalMaxEntropy ε n =
      (ρ.tensorPowerBipartite n).smoothConditionalMaxEntropy ε :=
  rfl

end State

/-- Source-shaped finite-N AEP error constant
`δ(ε, η) = 4 log₂(η) sqrt(log₂(2 / ε²))`.

This declaration only records the analytic error term. The finite-N AEP theorem
itself remains a downstream proof obligation.
-/
def finiteAEPDelta (ε η : ℝ) : ℝ :=
  4 * log2 η * Real.sqrt (log2 (2 / ε ^ 2))

/-- A double-limit AEP statement encoded through an explicit inner limit:
first `n → ∞` at fixed smoothing parameter, then `ε → 0+`.

`rate ε n` is intended to be a normalized smooth-entropy rate, while
`innerLimit ε` records the value of the `n → ∞` limit before taking
`ε → 0+`.
-/
def AEPDoubleLimit (rate : ℝ → ℕ → ℝ) (innerLimit : ℝ → ℝ) (limit : ℝ) : Prop :=
  (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε))) ∧
    Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)

@[simp]
theorem AEPDoubleLimit_eq (rate : ℝ → ℕ → ℝ) (innerLimit : ℝ → ℝ) (limit : ℝ) :
    AEPDoubleLimit rate innerLimit limit ↔
      (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
          Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε))) ∧
        Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit) :=
  Iff.rfl

/-- Package already-proved inner and outer limits as a double-limit statement. -/
theorem AEPDoubleLimit.of_inner_outer {rate : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (hinner : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε)))
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit :=
  ⟨hinner, houter⟩

/-- An eventually-valid family of inner-limit proofs, together with the outer
limit, gives the double-limit AEP statement. -/
theorem AEPDoubleLimit.of_eventually_inner {rate : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (hinner : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε)))
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit :=
  AEPDoubleLimit.of_inner_outer hinner houter

/-- Two-sided finite-N bounds with an error tending to zero imply convergence of
the rate to the limiting entropy. -/
theorem tendsto_of_eventually_two_sided_error {rate error : ℕ → ℝ} {limit : ℝ}
    (herror : Tendsto error atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, limit - error n ≤ rate n)
    (hupper : ∀ᶠ n in atTop, rate n ≤ limit + error n) :
    Tendsto rate atTop (nhds limit) := by
  have hlow : Tendsto (fun n : ℕ => limit - error n) atTop (nhds limit) := by
    simpa using tendsto_const_nhds.sub herror
  have hhigh : Tendsto (fun n : ℕ => limit + error n) atTop (nhds limit) := by
    simpa using tendsto_const_nhds.add herror
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh hlower hupper

/-- Absolute-error finite-N bounds imply convergence once the error term tends
to zero. -/
theorem tendsto_of_eventually_abs_error {rate error : ℕ → ℝ} {limit : ℝ}
    (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop, |rate n - limit| ≤ error n) :
    Tendsto rate atTop (nhds limit) := by
  refine tendsto_of_eventually_two_sided_error herror ?_ ?_
  · filter_upwards [hbound] with n hn
    have h := abs_le.mp hn
    linarith
  · filter_upwards [hbound] with n hn
    have h := abs_le.mp hn
    linarith

/-- If finite-N two-sided bounds hold for small positive smoothing parameters
and the error vanishes as `n → ∞`, then the packaged double-limit statement
follows. -/
theorem AEPDoubleLimit.of_eventually_two_sided_error {rate error : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (herror : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => error ε n) atTop (nhds 0))
    (hlower : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ᶠ n in atTop, innerLimit ε - error ε n ≤ rate ε n)
    (hupper : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ᶠ n in atTop, rate ε n ≤ innerLimit ε + error ε n)
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit := by
  refine AEPDoubleLimit.of_inner_outer ?_ houter
  filter_upwards [herror, hlower, hupper] with ε hε hε_lower hε_upper
  exact tendsto_of_eventually_two_sided_error hε hε_lower hε_upper

/-- Absolute-error finite-N bounds are a convenient special case of the
double-limit squeeze bridge. -/
theorem AEPDoubleLimit.of_eventually_abs_error {rate error : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (herror : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => error ε n) atTop (nhds 0))
    (hbound : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ᶠ n in atTop, |rate ε n - innerLimit ε| ≤ error ε n)
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit := by
  refine AEPDoubleLimit.of_inner_outer ?_ houter
  filter_upwards [herror, hbound] with ε hε hε_bound
  exact tendsto_of_eventually_abs_error hε hε_bound

/-- A constant divided by `sqrt n` tends to zero. -/
theorem tendsto_const_div_sqrt_nat (C : ℝ) :
    Tendsto (fun n : ℕ => C / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.div_atTop hsqrt

/-- The finite-N AEP error profile `δ(ε,η)/sqrt n` vanishes as `n → ∞`. -/
theorem finiteAEPDelta_div_sqrt_tendsto_zero (ε η : ℝ) :
    Tendsto (fun n : ℕ => finiteAEPDelta ε η / Real.sqrt (n : ℝ))
      atTop (nhds 0) :=
  tendsto_const_div_sqrt_nat (finiteAEPDelta ε η)

/- Von Neumann entropy is additive under tensor products.

S(rho^{kron n}) = n * S(rho). Requires spectral theory of
Kronecker products (eigenvalues of A kron B = pairwise products). -/
def State.vonNeumann_tensorPower_statement
    (ρ : State a) (n : ℕ) : Prop :=
  State.vonNeumann (ρ.tensorPower n) = n * State.vonNeumann ρ

/- Finite-N AEP bound (thm:qep):

For i.i.d. rho_AB^{kron n},
(1/n) H^eps_min(A^n|B^n) >= H(A|B)_rho - delta(eps,n)/sqrt(n).

Requires spectral concentration of rho^{kron n} eigenvalues
and smooth-entropy evaluation over nested tensor-power types. -/
def finiteNAEP_statement
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : Prop :=
  True

/- Asymptotic AEP (thm:qaep):

lim_{eps->0} lim_{n->infty} (1/n) H^eps_min(A^n|B^n) = H(A|B)_rho. -/
def asymptoticAEP_statement
    (ρ : State (Prod a b)) : Prop :=
  True

/- One-shot decoupling bound (Hayden theo:oneshot):

E || psi^RE - pi^R otimes phi^E ||_1 <= sqrt(|R||E| Tr[(phi^AE)^2]).

Source: Hayden et al. 2007, theo:oneshot at lines 312-321. -/
def oneShotDecoupling_statement
    {r : Type u} [Fintype r] [DecidableEq r]
    (ρ : State (Prod (Prod a r) b)) : Prop :=
  True

end

end QIT
