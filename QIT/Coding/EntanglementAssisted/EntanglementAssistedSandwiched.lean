/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HypothesisTesting.SandwichedComparison
public import QIT.Coding.EntanglementAssisted.EntanglementAssisted

/-!
# Sandwiched-Renyi mutual information for EA communication

This module provides the source-facing definition layer for the sandwiched-Renyi
state and channel mutual information used in the entanglement-assisted classical
communication strong-converse route.

Source alignment:
* [KhatriWilde2024Principles, Chapters/entropies.tex:8065-8074] defines the
  sandwiched-Renyi state and channel mutual information objectives.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1128-1165] gives the
  alternate-expression route that later connects the channel objective to the
  completely bounded `1 -> alpha` norm.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1169-1217] proves
  additivity for the bipartite-state sandwiched-Renyi mutual information.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1220-1277] proves
  channel additivity from the bipartite-state additivity, CB alternate
  expression, and CB multiplicativity.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907] proves the
  `alpha -> 1+` limit through monotonicity, pointwise sandwiched-Renyi
  convergence, and the Mosonyi minimax exchange.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140] and
  [KhatriWilde2024Principles, Chapters/EA_capacity.tex:2152-2240] provide the
  CB norm alternate expression and multiplicativity proof used by channel
  additivity.

The channel additivity theorem and the `alpha -> 1+` channel limit require the
CB `1 -> alpha` alternate expression, CB multiplicativity, and the Mosonyi
minimax/limit exchange.  Those proof layers are intentionally not represented by
placeholder declarations here.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- Candidate sandwiched-Renyi mutual information value for a fixed side
information state `sigmaB`:
`D~_alpha(rho_AB || rho_A tensor sigma_B)`.

This is the state-level candidate appearing before the `inf_sigmaB` in
Khatri--Wilde, `Chapters/entropies.tex:8069-8074`.  It uses the PSD-reference
extended-real divergence from `FrankLieb.lean`, so singular references follow
the source support convention instead of needing artificial full-rank
hypotheses. -/
def sandwichedRenyiMutualInformationCandidateE
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) : EReal :=
  rhoAB.sandwichedRenyiPSDReferenceE
    (rhoAB.marginalA.prod sigmaB).matrix
    (rhoAB.marginalA.prod sigmaB).pos
    alpha

/-- Value set for the state sandwiched-Renyi mutual information
`I~_alpha(A;B)_rho`, before taking the infimum over side-information states. -/
def sandwichedRenyiMutualInformationEValueSet
    (rhoAB : State (Prod a b)) (alpha : ℝ) : Set EReal :=
  Set.range fun sigmaB : State b =>
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha

/-- Extended-real sandwiched-Renyi mutual information of a bipartite state:
`I~_alpha(A;B)_rho = inf_sigmaB D~_alpha(rho_AB || rho_A tensor sigma_B)`. -/
def sandwichedRenyiMutualInformationE
    (rhoAB : State (Prod a b)) (alpha : ℝ) : EReal :=
  sInf (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha)

theorem sandwichedRenyiMutualInformationCandidateE_eq
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      rhoAB.sandwichedRenyiPSDReferenceE
        (rhoAB.marginalA.prod sigmaB).matrix
        (rhoAB.marginalA.prod sigmaB).pos
        alpha := by
  rfl

/-- On the full-rank high-`alpha` branch, the source-facing extended-real
candidate agrees with the repository's real-valued matrix-reference
sandwiched-Renyi divergence. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    (hsigma : sigmaB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (sandwichedRenyiReference rhoAB
        (rhoAB.marginalA.prod sigmaB).matrix
        hrho (State.prod_posDef hA hsigma)
        alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha) : EReal) := by
  rw [sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
  exact sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
    rhoAB hrho (State.prod_posDef hA hsigma)
    alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha)

theorem sandwichedRenyiMutualInformationE_eq_sInf
    (rhoAB : State (Prod a b)) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationE alpha =
      sInf (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha) := by
  rfl

theorem sandwichedRenyiMutualInformationCandidateE_mem_valueSet
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha ∈
      rhoAB.sandwichedRenyiMutualInformationEValueSet alpha := by
  exact ⟨sigmaB, rfl⟩

theorem sandwichedRenyiMutualInformationE_le_candidate
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationE alpha ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  rw [sandwichedRenyiMutualInformationE_eq_sInf]
  exact sInf_le
    (rhoAB.sandwichedRenyiMutualInformationCandidateE_mem_valueSet sigmaB alpha)

/-- The side-information candidate set is nonempty whenever the side system is
inhabited.  This is the order-theoretic precondition for later `sInf` reasoning. -/
theorem sandwichedRenyiMutualInformationEValueSet_nonempty [Nonempty b]
    (rhoAB : State (Prod a b)) (alpha : ℝ) :
    (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
  classical
  let u : b → ℝ≥0 := fun _ => (Fintype.card b : ℝ≥0)⁻¹
  have husum : ∑ i, u i = 1 := by
    simp [u, Finset.sum_const, Fintype.card_ne_zero]
  let sigmaB : State b := Classical.diagonalState u husum
  exact ⟨rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha, ⟨sigmaB, rfl⟩⟩

/-- Optimized state hypothesis-testing mutual information is bounded above by
the optimized sandwiched-Renyi mutual information plus the Khatri--Wilde
comparison penalty.

This lifts `prop:sandwich-to-htre` from relative entropy candidates to the
state mutual-information infimum over side-information states. -/
theorem hypothesisTestingMutualInformationE_le_sandwichedRenyiMutualInformationE_add
    (rhoAB : State (Prod a b)) {epsilon alpha : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (halpha : 1 < alpha) :
    rhoAB.hypothesisTestingMutualInformationE epsilon ≤
      rhoAB.sandwichedRenyiMutualInformationE alpha +
        ((alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal) := by
  classical
  let penalty : ℝ := alpha / (alpha - 1) * log2 (1 / (1 - epsilon))
  let penaltyE : EReal := (penalty : EReal)
  haveI : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  have hsub :
      rhoAB.hypothesisTestingMutualInformationE epsilon - penaltyE ≤
        rhoAB.sandwichedRenyiMutualInformationE alpha := by
    rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
    refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    have hHTcand :
        rhoAB.hypothesisTestingMutualInformationE epsilon ≤
          rhoAB.hypothesisTestingRelativeEntropyE (rhoAB.marginalA.prod sigmaB) epsilon := by
      rw [State.hypothesisTestingMutualInformationE_eq_sInf]
      exact sInf_le ⟨sigmaB, rfl⟩
    have hcmpPSD :
        rhoAB.hypothesisTestingRelativeEntropyPSDE
            (rhoAB.marginalA.prod sigmaB).matrix epsilon ≤
          rhoAB.sandwichedRenyiPSDReferenceE
              (rhoAB.marginalA.prod sigmaB).matrix
              (rhoAB.marginalA.prod sigmaB).pos alpha +
            penaltyE := by
      simpa [penalty, penaltyE] using
        (State.hypothesisTestingRelativeEntropyPSDE_le_sandwichedRenyiPSDReferenceE_add
          (rho := rhoAB)
          (sigma := (rhoAB.marginalA.prod sigmaB).matrix)
          (hsigma := (rhoAB.marginalA.prod sigmaB).pos)
          (epsilon := epsilon) (alpha := alpha)
          hepsilon_nonneg hepsilon_lt_one halpha)
    have hcmp :
        rhoAB.hypothesisTestingRelativeEntropyE (rhoAB.marginalA.prod sigmaB) epsilon ≤
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha + penaltyE := by
      rw [← State.hypothesisTestingRelativeEntropyPSDE_eq_state
        (rho := rhoAB) (epsilon := epsilon)
        (sigma := rhoAB.marginalA.prod sigmaB)]
      simpa [State.sandwichedRenyiMutualInformationCandidateE_eq] using hcmpPSD
    exact EReal.sub_le_of_le_add (hHTcand.trans hcmp)
  have hmain :
      rhoAB.hypothesisTestingMutualInformationE epsilon ≤
        rhoAB.sandwichedRenyiMutualInformationE alpha + penaltyE :=
    (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot penalty))
      (.inl (EReal.coe_ne_top penalty))).mp hsub
  simpa [penalty, penaltyE] using hmain

end State

namespace Channel

variable (N : Channel a b)

/-- Fixed-input channel sandwiched-Renyi mutual information for the
input-reference pure state `psi`. -/
def inputSandwichedRenyiMutualInformationE
    (psi : PureVector (Prod a a)) (alpha : ℝ) : EReal :=
  (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha

/-- Channel sandwiched-Renyi mutual information value set over pure
input-reference states. -/
def sandwichedRenyiMutualInformationEValueSet (alpha : ℝ) : Set EReal :=
  Set.range fun psi : PureVector (Prod a a) =>
    N.inputSandwichedRenyiMutualInformationE psi alpha

/-- Extended-real sandwiched-Renyi mutual information of a channel:
`I~_alpha(N) = sup_psi I~_alpha(R;B)_{(id tensor N)(psi)}`.

This matches Khatri--Wilde, `Chapters/entropies.tex:8065-8074`, with the
reference register chosen as a copy of the channel input system. -/
def sandwichedRenyiMutualInformationE (alpha : ℝ) : EReal :=
  sSup (N.sandwichedRenyiMutualInformationEValueSet alpha)

theorem inputSandwichedRenyiMutualInformationE_eq
    (psi : PureVector (Prod a a)) (alpha : ℝ) :
    N.inputSandwichedRenyiMutualInformationE psi alpha =
      (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha := by
  rfl

theorem sandwichedRenyiMutualInformationE_eq_sSup (alpha : ℝ) :
    N.sandwichedRenyiMutualInformationE alpha =
      sSup (N.sandwichedRenyiMutualInformationEValueSet alpha) := by
  rfl

theorem inputSandwichedRenyiMutualInformationE_mem_valueSet
    (psi : PureVector (Prod a a)) (alpha : ℝ) :
    N.inputSandwichedRenyiMutualInformationE psi alpha ∈
      N.sandwichedRenyiMutualInformationEValueSet alpha := by
  exact ⟨psi, rfl⟩

theorem inputSandwichedRenyiMutualInformationE_le_channel
    (psi : PureVector (Prod a a)) (alpha : ℝ) :
    N.inputSandwichedRenyiMutualInformationE psi alpha ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  rw [sandwichedRenyiMutualInformationE_eq_sSup]
  exact le_sSup (N.inputSandwichedRenyiMutualInformationE_mem_valueSet psi alpha)

/-- The pure-input value set is nonempty whenever the input system is inhabited. -/
theorem sandwichedRenyiMutualInformationEValueSet_nonempty [Nonempty a] (alpha : ℝ) :
    (N.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
  let psi0 : PureVector (Prod a a) := PureVector.basisPureVector
  exact ⟨N.inputSandwichedRenyiMutualInformationE psi0 alpha,
    N.inputSandwichedRenyiMutualInformationE_mem_valueSet psi0 alpha⟩

/-- Channel hypothesis-testing mutual information is bounded above by the
channel sandwiched-Renyi mutual information plus the Khatri--Wilde comparison
penalty.

This is the optimized channel lift of `prop:sandwich-to-htre` used by the
one-shot entanglement-assisted strong-converse route. -/
theorem hypothesisTestingMutualInformationE_le_sandwichedRenyiMutualInformationE_add
    [Nonempty a] {epsilon alpha : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (halpha : 1 < alpha) :
    N.hypothesisTestingMutualInformationE epsilon ≤
      N.sandwichedRenyiMutualInformationE alpha +
        ((alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal) := by
  classical
  let penalty : ℝ := alpha / (alpha - 1) * log2 (1 / (1 - epsilon))
  let penaltyE : EReal := (penalty : EReal)
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  rw [N.hypothesisTestingMutualInformationE_eq_sSup] at hz
  obtain ⟨value, hvalue, hzvalue⟩ :=
    exists_lt_of_lt_csSup
      (Set.range_nonempty
        (fun psi : PureVector (Prod a a) =>
          N.inputHypothesisTestingMutualInformationE psi epsilon))
      hz
  rcases hvalue with ⟨psi, rfl⟩
  have hstate :=
    State.hypothesisTestingMutualInformationE_le_sandwichedRenyiMutualInformationE_add
      (rhoAB := N.hypothesisTestingOutputState psi)
      hepsilon_nonneg hepsilon_lt_one halpha
  have hinput :
      N.inputHypothesisTestingMutualInformationE psi epsilon ≤
        N.inputSandwichedRenyiMutualInformationE psi alpha + penaltyE := by
    simpa [Channel.inputHypothesisTestingMutualInformationE,
      Channel.inputSandwichedRenyiMutualInformationE, penalty, penaltyE] using hstate
  have hchannel :
      N.inputSandwichedRenyiMutualInformationE psi alpha + penaltyE ≤
        N.sandwichedRenyiMutualInformationE alpha + penaltyE :=
    add_le_add (N.inputSandwichedRenyiMutualInformationE_le_channel psi alpha) le_rfl
  exact hzvalue.le.trans (hinput.trans hchannel)

end Channel

end

end QIT
