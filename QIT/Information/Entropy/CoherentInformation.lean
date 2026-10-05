/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.States.MaximallyEntangled
public import QIT.Information.Entropy.Entropy
public import QIT.Util.TensorPower

/-!
# Coherent information

Bipartite coherent information is negative conditional entropy. Channel
coherent information optimizes the output quantity over pure input/reference
states [KhatriWilde2024Principles, Chapters/entropies.tex:8150-8175]. The
reference can be chosen to have the input dimension
[KhatriWilde2024Principles, Chapters/quantum_capacity.tex:642-655].

The regularized quantity uses the supremum of normalized positive-block
values [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:87-95].
It is an information quantity, separate from operational quantum capacity.
No coding theorem, limit formula, or choice of complementary channel is needed
for these definitions.
-/

@[expose] public section

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

namespace State

/-- Coherent information `I(R⟩B) = -H(R|B)` in bits. -/
def coherentInformation (ρ : State (r × b)) : ℝ := -ρ.conditionalEntropy

/-- Coherent information has the output-minus-joint entropy sign convention. -/
theorem coherentInformation_eq (ρ : State (r × b)) :
    ρ.coherentInformation = ρ.marginalB.vonNeumann - ρ.vonNeumann := by
  simp [coherentInformation, conditionalEntropy]

/-- Coherent information is bounded above by the logarithm of the output dimension. -/
theorem coherentInformation_le_log_card (ρ : State (r × b)) :
    ρ.coherentInformation ≤ log2 (Fintype.card b) := by
  rw [coherentInformation_eq]
  exact (sub_le_self _ ρ.vonNeumann_nonneg).trans ρ.marginalB.vonNeumann_le_log_card

end State

namespace Channel

/-- Output coherent information for a pure input/reference state. -/
def coherentInformationFor (N : Channel a b) (ψ : PureVector (r × a)) : ℝ :=
  (((Channel.idChannel r).prod N).applyState ψ.state).coherentInformation

/-- Coherent-information values over an input-sized reference, with unrestricted
pure entanglement between reference and channel input. -/
def coherentInformationValues (N : Channel a b) : Set ℝ :=
  Set.range (fun ψ : PureVector (a × a) => N.coherentInformationFor ψ)

/-- Optimized channel coherent information in bits, following
[KhatriWilde2024Principles, Chapters/quantum_capacity.tex:642-655]. -/
def coherentInformation (N : Channel a b) : ℝ := sSup N.coherentInformationValues

/-- Each coherent-information candidate is bounded by the output dimension. -/
theorem coherentInformationFor_le_log_card (N : Channel a b) (ψ : PureVector (r × a)) :
    N.coherentInformationFor ψ ≤ log2 (Fintype.card b) :=
  State.coherentInformation_le_log_card _

/-- The channel optimization set is bounded above. -/
theorem coherentInformationValues_bddAbove (N : Channel a b) :
    BddAbove N.coherentInformationValues := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  rintro x ⟨ψ, rfl⟩
  exact N.coherentInformationFor_le_log_card ψ

/-- A nonempty input admits a pure input/reference state. -/
theorem coherentInformationValues_nonempty (N : Channel a b) [Nonempty a] :
    N.coherentInformationValues.Nonempty :=
  ⟨_, ⟨PureVector.maximallyEntangled (Equiv.refl a), rfl⟩⟩

/-- Any input-sized pure candidate lies below the optimized quantity. -/
theorem coherentInformationFor_le (N : Channel a b) (ψ : PureVector (a × a)) :
    N.coherentInformationFor ψ ≤ N.coherentInformation :=
  le_csSup N.coherentInformationValues_bddAbove ⟨ψ, rfl⟩

/-- Optimized coherent information is bounded by the output dimension. -/
theorem coherentInformation_le_log_card (N : Channel a b) [Nonempty a] :
    N.coherentInformation ≤ log2 (Fintype.card b) := by
  apply csSup_le N.coherentInformationValues_nonempty
  rintro x ⟨ψ, rfl⟩
  exact N.coherentInformationFor_le_log_card ψ

/-- Normalized coherent-information values of positive tensor-power blocks.
Input states may be entangled across all uses. -/
def regularizedCoherentInformationValues (N : Channel a b) : Set ℝ :=
  {q : ℝ | ∃ n : ℕ, 0 < n ∧ q = (N.tensorPower n).coherentInformation / (n : ℝ)}

/-- The supremum regularization of channel coherent information
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:87-95].
This definition does not assert the LSD equality or convergence to this
supremum of the normalized block sequence. -/
def regularizedCoherentInformation (N : Channel a b) : ℝ :=
  sSup N.regularizedCoherentInformationValues

/-- Positive blocklengths form a nonempty optimization domain. -/
theorem regularizedCoherentInformationValues_nonempty (N : Channel a b) :
    N.regularizedCoherentInformationValues.Nonempty :=
  ⟨_, 1, Nat.zero_lt_one, rfl⟩

/-- Dimension bounds remain uniform after dividing by a positive blocklength. -/
theorem blockCoherentInformationRate_le_log_card (N : Channel a b) [Nonempty a]
    (n : ℕ) (hn : 0 < n) :
    (N.tensorPower n).coherentInformation / (n : ℝ) ≤ log2 (Fintype.card b) := by
  let : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).mpr
  calc
    (N.tensorPower n).coherentInformation ≤ log2 (Fintype.card (QIT.TensorPower b n)) :=
      (N.tensorPower n).coherentInformation_le_log_card
    _ = log2 (Fintype.card b) * (n : ℝ) := by
      rw [tensorPower_card, Nat.cast_pow]
      unfold log2
      rw [Real.log_pow]
      ring

/-- The normalized positive-block rate set is bounded above. -/
theorem regularizedCoherentInformationValues_bddAbove (N : Channel a b) [Nonempty a] :
    BddAbove N.regularizedCoherentInformationValues := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  rintro q ⟨n, hn, rfl⟩
  exact N.blockCoherentInformationRate_le_log_card n hn

/-- A positive-block rate is a lower bound on the supremum regularization. -/
theorem blockCoherentInformationRate_le_regularized (N : Channel a b) [Nonempty a]
    (n : ℕ) (hn : 0 < n) :
    (N.tensorPower n).coherentInformation / (n : ℝ) ≤ N.regularizedCoherentInformation :=
  le_csSup N.regularizedCoherentInformationValues_bddAbove ⟨n, hn, rfl⟩

/-- Regularized coherent information is finite and dimension bounded. -/
theorem regularizedCoherentInformation_le_log_card (N : Channel a b) [Nonempty a] :
    N.regularizedCoherentInformation ≤ log2 (Fintype.card b) := by
  apply csSup_le N.regularizedCoherentInformationValues_nonempty
  rintro q ⟨n, hn, rfl⟩
  exact N.blockCoherentInformationRate_le_log_card n hn

end Channel

end

end QIT
