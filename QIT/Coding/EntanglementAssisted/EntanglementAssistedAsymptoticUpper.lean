/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.EntanglementAssistedAsymptotic
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedOneShotUpper
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwichedConverse
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwichedAdditivity
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwichedLimit

/-!
# Asymptotic upper bounds for entanglement-assisted classical communication

This module defines an assembly interface for the Khatri--Wilde asymptotic
upper-bound and strong-converse route
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331].

Sandwiched-Renyi channel mutual-information additivity and the `alpha -> 1`
limit are kept as an explicit input.  Once that input is available, the
theorems below package it into the existing converse witness, ordinary
capacity upper bound, and strong-converse upper-bound interfaces.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- Source-shaped input expected from the sandwiched-Renyi asymptotic
upper-bound route.

The field is exactly the eventual `n`-use log-cardinality estimate consumed by
`entanglementAssisted_converseWitnessFamily_of_logCardUpperBounds`: for every
rate slack and positive reliability threshold, all sufficiently long reliable
codes have message size bounded by `n * (I(N) + eta)`.

This is a proof-dependency interface, not the asymptotic upper-bound theorem by
itself. -/
structure EntanglementAssistedAsymptoticUpperInput where
  logCard_upper :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  log2 (Fintype.card M : ℝ) ≤
                    (n : ℝ) * (N.entanglementAssistedInformation + η)

/-- Source-shaped input expected from the Khatri--Wilde sandwiched-Renyi
asymptotic upper-bound route.

Unlike the compatibility input above, this version uses the source error
range `ε ∈ [0, 1)`.  That is the range in the one-shot upper bounds
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427] and in the
strong-converse argument [KhatriWilde2024Principles,
Chapters/EA_capacity.tex:990-1331]. -/
structure EntanglementAssistedSourceAsymptoticUpperInput where
  logCard_upper :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  log2 (Fintype.card M : ℝ) ≤
                    (n : ℝ) * (N.entanglementAssistedInformation + η)

/-- Convert the Khatri--Wilde block-channel sandwiched-Renyi estimate into the
source-shaped asymptotic upper-bound input.

The hypothesis is the exact handoff expected from the sandwiched-Renyi
additivity plus `α → 1` limit route in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331]: for every
slack and every source error `ε ∈ [0, 1)`, some `α > 1` eventually makes the
one-shot sandwiched upper bound for the block channel `N^{⊗n}` no larger than
`n * (I(N) + η)`.  The proof only reinterprets an `n`-use code as a one-shot
code for the block channel and then applies the already-proved one-shot
Khatri--Wilde upper bound. -/
theorem entanglementAssisted_sourceAsymptoticUpperInput_of_blockSandwichedBounds
    [Nonempty a]
    (hblock :
      ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
        ∃ alpha : ℝ, 1 < alpha ∧
          ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
            (N.tensorPower n).sandwichedRenyiMutualInformationE alpha +
                ((alpha / (alpha - 1) * log2 (1 / (1 - ε)) : ℝ) : EReal) ≤
              ((n : ℝ) * (N.entanglementAssistedInformation + η) : EReal)) :
    N.EntanglementAssistedSourceAsymptoticUpperInput where
  logCard_upper := by
    intro η hη ε hε_nonneg hε_lt_one
    obtain ⟨alpha, halpha, N0, hN0⟩ :=
      hblock η hη ε hε_nonneg hε_lt_one
    refine ⟨N0, ?_⟩
    intro n hn M _hMfin _hMdec _hMnonempty EA _hEAfin _hEAdec EB _hEBfin _hEBdec C hC
    have hblockCode :
        (log2 (Fintype.card M : ℝ) : EReal) ≤
          (N.tensorPower n).sandwichedRenyiMutualInformationE alpha +
            ((alpha / (alpha - 1) * log2 (1 / (1 - ε)) : ℝ) : EReal) :=
      (C.asBlockOneShot).log_card_le_channel_sandwichedRenyiMutualInformationE_add
        hε_nonneg hε_lt_one halpha (C.asBlockOneShot_maxErrorAtMost hC)
    have hE :
        (log2 (Fintype.card M : ℝ) : EReal) ≤
          ((n : ℝ) * (N.entanglementAssistedInformation + η) : EReal) :=
      hblockCode.trans (hN0 n hn)
    exact EReal.coe_le_coe_iff.mp hE

/-- Source-shaped asymptotic upper-bound input from the completed
sandwiched-Renyi additivity and `α → 1+` limit route.

This uses the Khatri--Wilde alpha-to-one channel limit
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907] in the
strong-converse asymptotic step: choose `α > 1` close enough to one so that the
optimized sandwiched channel quantity is within half the requested slack of
`I(N)`, then choose the blocklength large enough that the one-shot error penalty
divided by `n` is within the other half.  The block-channel sandwiched quantity
is reduced using the tensor-power additivity theorem. -/
theorem entanglementAssisted_sourceAsymptoticUpperInput_of_sandwichedLimit
    [Nonempty a] [Nonempty b] :
    N.EntanglementAssistedSourceAsymptoticUpperInput := by
  refine N.entanglementAssisted_sourceAsymptoticUpperInput_of_blockSandwichedBounds ?_
  intro η hη ε hε_nonneg hε_lt_one
  let δ : ℝ := η / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have htarget_lt :
      (N.entanglementAssistedInformation : EReal) <
        ((N.entanglementAssistedInformation + δ : ℝ) : EReal) := by
    exact EReal.coe_lt_coe_iff.mpr (by dsimp [δ]; linarith)
  have hlim := N.sandwichedRenyiMutualInformationE_tendsto_information
  have hα_eventually :
      ∀ᶠ alpha in State.relativeEntropyHighAlphaRightToOne,
        N.sandwichedRenyiMutualInformationE alpha.1 <
          ((N.entanglementAssistedInformation + δ : ℝ) : EReal) := by
    exact (tendsto_order.mp hlim).2
      ((N.entanglementAssistedInformation + δ : ℝ) : EReal) htarget_lt
  haveI : Filter.NeBot State.relativeEntropyHighAlphaRightToOne :=
    State.relativeEntropyHighAlphaRightToOne_neBot
  obtain ⟨alpha, hα_lt⟩ := hα_eventually.exists
  refine ⟨alpha.1, alpha.2, ?_⟩
  let penalty : ℝ :=
    alpha.1 / (alpha.1 - 1) * log2 (1 / (1 - ε))
  have hpenalty_tendsto :
      Tendsto (fun n : ℕ => penalty / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpenalty_eventually :
      ∀ᶠ n : ℕ in atTop, penalty / (n : ℝ) < δ := by
    exact hpenalty_tendsto.eventually (eventually_lt_nhds hδ_pos)
  obtain ⟨Npen, hNpen⟩ := Filter.eventually_atTop.mp hpenalty_eventually
  refine ⟨max 1 Npen, ?_⟩
  intro n hn
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_left 1 Npen) hn)
  have hn_pen : n ≥ Npen :=
    le_trans (Nat.le_max_right 1 Npen) hn
  have hnR_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos
  have hpen_div : penalty / (n : ℝ) < δ := hNpen n hn_pen
  have hpen_le : penalty ≤ (n : ℝ) * δ := by
    simpa [mul_comm] using le_of_lt ((div_lt_iff₀ hnR_pos).mp hpen_div)
  let X : EReal := N.sandwichedRenyiMutualInformationE alpha.1
  let Y : ℝ := N.entanglementAssistedInformation + δ
  have hX_le : X ≤ (Y : EReal) := le_of_lt hα_lt
  have hn_nonneg_E : (0 : EReal) ≤ ((n : ℝ) : EReal) := by
    exact EReal.coe_nonneg.mpr (le_of_lt hnR_pos)
  have hmul_le : ((n : ℝ) : EReal) * X ≤ ((n : ℝ) : EReal) * (Y : EReal) := by
    exact mul_le_mul_of_nonneg_left hX_le hn_nonneg_E
  have htensor :
      (N.tensorPower n).sandwichedRenyiMutualInformationE alpha.1 =
        ((n : ℝ) : EReal) * X := by
    dsimp [X]
    simpa using N.sandwichedRenyiMutualInformationE_tensorPower_eq_n_mul alpha.2 n
  have hreal_tail :
      (n : ℝ) * Y + (n : ℝ) * δ =
        (n : ℝ) * (N.entanglementAssistedInformation + η) := by
    dsimp [Y, δ]
    ring
  calc
    (N.tensorPower n).sandwichedRenyiMutualInformationE alpha.1 +
          ((alpha.1 / (alpha.1 - 1) * log2 (1 / (1 - ε)) : ℝ) : EReal)
        = ((n : ℝ) : EReal) * X + (penalty : EReal) := by
            simp [htensor, penalty]
    _ ≤ ((n : ℝ) : EReal) * (Y : EReal) + (penalty : EReal) := by
            exact add_le_add hmul_le le_rfl
    _ ≤ ((n : ℝ) : EReal) * (Y : EReal) + (((n : ℝ) * δ : ℝ) : EReal) := by
            exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hpen_le)
    _ = ((n : ℝ) * (N.entanglementAssistedInformation + η) : EReal) := by
            rw [← EReal.coe_mul, ← EReal.coe_add, hreal_tail]
            simp [EReal.coe_mul, EReal.coe_add]

/-- The asymptotic upper input gives the standard converse witness family used
by the final capacity-squeeze theorem. -/
theorem entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    EntanglementAssistedConverseWitnessFamily N :=
  N.entanglementAssisted_converseWitnessFamily_of_logCardUpperBounds H.logCard_upper

/-- The source-shaped asymptotic upper input gives the source-consistent
converse witness family used by the KW strong-converse route. -/
theorem entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    EntanglementAssistedSourceConverseWitnessFamily N :=
  N.entanglementAssisted_sourceConverseWitnessFamily_of_logCardUpperBounds H.logCard_upper

/-- Ordinary-rate upper-bound consequence of the asymptotic upper input. -/
theorem entanglementAssistedInformation_isRateUpperBound_of_asymptoticUpperInput
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isUpperBound_of_converseWitness
    (N.entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput H)

/-- Ordinary-rate upper-bound consequence of the source-shaped asymptotic
upper input. -/
theorem entanglementAssistedInformation_isRateUpperBound_of_sourceAsymptoticUpperInput
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isUpperBound_of_sourceConverseWitness
    (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput H)

/-- Strong-converse-rate consequence of the asymptotic upper input. -/
theorem entanglementAssistedInformation_isStrongConverseRate_of_asymptoticUpperInput
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.IsStrongConverseEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isStrongConverseRate_of_converseWitness
    (N.entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput H)

/-- Strong-converse-rate consequence of the source-shaped asymptotic upper
input. -/
theorem entanglementAssistedInformation_isStrongConverseRate_of_sourceAsymptoticUpperInput
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.IsStrongConverseEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isStrongConverseRate_of_sourceConverseWitness
    (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput H)

/-- Capacity upper-bound consequence, separated from the asymptotic upper input
so the dependence on the already-proved lower-bound/achievability route stays
explicit. -/
theorem entanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.entanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.entanglementAssistedClassicalCapacity_le_information_of_converseWitness
    hach (N.entanglementAssisted_converseWitnessFamily_of_asymptoticUpperInput H)

/-- Capacity upper-bound consequence of the source-shaped asymptotic upper
input. -/
theorem entanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.entanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.entanglementAssistedClassicalCapacity_le_information_of_sourceConverseWitness
    hach (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput H)

/-- Strong-converse capacity upper-bound consequence, again keeping the
achievability input explicit for the final capacity squeeze. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.strongConverseEntanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.strongConverseEntanglementAssistedClassicalCapacity_le_information hach
    (N.entanglementAssistedInformation_isStrongConverseRate_of_asymptoticUpperInput H)

/-- Strong-converse capacity upper-bound consequence of the source-shaped
asymptotic upper input. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.strongConverseEntanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.strongConverseEntanglementAssistedClassicalCapacity_le_information hach
    (N.entanglementAssistedInformation_isStrongConverseRate_of_sourceAsymptoticUpperInput H)

/-- Assembly theorem for the asymptotic upper-bound route.

After `EntanglementAssistedAsymptoticUpperInput` is supplied, this theorem
returns the source-facing ordinary upper-bound and strong-converse conclusions,
together with the two capacity inequalities needed by the final capacity
theorem. -/
theorem entanglementAssisted_asymptoticUpperBounds_of_asymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
        N.entanglementAssistedInformation ∧
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation ∧
      N.entanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation := by
  exact
    ⟨N.entanglementAssistedInformation_isRateUpperBound_of_asymptoticUpperInput H,
      N.entanglementAssistedInformation_isStrongConverseRate_of_asymptoticUpperInput H,
      N.entanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
        hach H,
      N.strongConverseEntanglementAssistedClassicalCapacity_le_information_of_asymptoticUpperInput
        hach H⟩

/-- Assembly theorem for the source-shaped asymptotic upper-bound route.

This is the intended handoff target after the sandwiched-Renyi additivity and
`α → 1` input is available. -/
theorem entanglementAssisted_asymptoticUpperBounds_of_sourceAsymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
        N.entanglementAssistedInformation ∧
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation ∧
      N.entanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation := by
  exact
    ⟨N.entanglementAssistedInformation_isRateUpperBound_of_sourceAsymptoticUpperInput H,
      N.entanglementAssistedInformation_isStrongConverseRate_of_sourceAsymptoticUpperInput H,
      N.entanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
        hach H,
      N.strongConverseEntanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
        hach H⟩

/-- Khatri--Wilde asymptotic upper and strong-converse bounds from the completed
sandwiched-Renyi route.

This closes the source-shaped route in Chapters/EA_capacity.tex:1902-1906: the
one-shot upper bound is lifted to all blocklengths, the sandwiched-Renyi channel
quantity is additive and tends to `I(N)` as `α -> 1+`, and the lower-bound
achievability theorem supplies the nonempty achievable-rate set needed for the
capacity inequalities. -/
theorem entanglementAssisted_asymptoticUpperBounds_of_sandwichedLimit
    [Nonempty a] [Nonempty b] :
    N.IsEntanglementAssistedClassicalRateUpperBound
        N.entanglementAssistedInformation ∧
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation ∧
      N.entanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation := by
  exact N.entanglementAssisted_asymptoticUpperBounds_of_sourceAsymptoticUpperInput
    (N.entanglementAssistedInformation_isAchievable_of_oneShotPetzLowerBound)
    (N.entanglementAssisted_sourceAsymptoticUpperInput_of_sandwichedLimit)

/-- Final Khatri--Wilde entanglement-assisted classical communication capacity
identity, assembled from the one-shot Petz lower bound and the sandwiched-Renyi
strong-converse route.

The conclusion is the Lean version of
`C_EA(N) = \widetilde C_EA(N) = I(N)`: both the operational capacity and the
strong-converse capacity are equal to the channel mutual information. -/
theorem entanglementAssisted_capacity_and_strongConverseCapacity_eq_information_of_sandwichedLimit
    [Nonempty a] [Nonempty b] :
    N.entanglementAssistedClassicalCapacity = N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity =
        N.entanglementAssistedInformation := by
  exact N.entanglementAssisted_capacity_and_strongConverseCapacity_eq_information_of_sourceConverseWitness
    (N.entanglementAssistedInformation_isAchievable_of_oneShotPetzLowerBound)
    (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput
      (N.entanglementAssisted_sourceAsymptoticUpperInput_of_sandwichedLimit))

end Channel

end

end QIT
