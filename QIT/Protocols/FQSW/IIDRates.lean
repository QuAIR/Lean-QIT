/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.FQSW.IIDTypical

/-!
# FQSW IID rate and register arithmetic

This file is a dependency-ordered leaf of `QIT.Protocols.FQSW`.  Declaration
names, namespaces, statements, and proof terms are preserved from the original
monolithic module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p u1 v1 w1

noncomputable section

local instance fqswIIDRatesCMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

/-- Scalar denominator bridge for ADHW fqsw.tex lines 1148-1167: the chosen
lower bound on `d_{A₁}` converts the source's `skoro` denominator into the
i.i.d. exponential decay. -/
private theorem fqsw_skoro_bound_le_iid_decay
    (n : ℕ) (I δ Q : ℝ)
    (hQ :
      (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + 2 * δ)) ≤ Q) :
    4 * (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ)) / (Q ^ 2) ≤
      4 * (2 : ℝ) ^ (-(n : ℝ) * δ) := by
  let L : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + 2 * δ))
  let B : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + 4 * δ))
  let A : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hQ_pos : 0 < Q := lt_of_lt_of_le hL_pos (by simpa [L] using hQ)
  have hQ_nonneg : 0 ≤ Q := hQ_pos.le
  have hsq_raw : L ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ hL_nonneg hQ_nonneg).mpr (by simpa [L] using hQ)
  have hL_sq : L ^ 2 = B := by
    dsimp [L, B]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hden : B ≤ Q ^ 2 := by
    simpa [hL_sq] using hsq_raw
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hnum_nonneg : 0 ≤ 4 * A := by nlinarith
  have hdiv :
      (4 * A) / (Q ^ 2) ≤ (4 * A) / B :=
    div_le_div_of_nonneg_left hnum_nonneg hB_pos hden
  have hratio : A / B = (2 : ℝ) ^ (-(n : ℝ) * δ) := by
    dsimp [A, B]
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    4 * (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ)) / (Q ^ 2) =
        (4 * A) / (Q ^ 2) := by rfl
    _ ≤ (4 * A) / B := hdiv
    _ = 4 * (A / B) := by ring
    _ = 4 * (2 : ℝ) ^ (-(n : ℝ) * δ) := by rw [hratio]

/-- Scalar denominator bridge for the rounded finite-register ADHW route: the
lower `A₁` cardinality target `I/2 + 7δ/4` still converts the source `skoro`
denominator into an exponentially decaying i.i.d. tail, now with exponent
`δ / 2`. -/
private theorem fqsw_rounded_skoro_bound_le_iid_decay
    (n : ℕ) (I δ Q : ℝ)
    (hQ :
      (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (7 / 4 : ℝ) * δ)) ≤ Q) :
    4 * (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ)) / (Q ^ 2) ≤
      4 * (2 : ℝ) ^ (-(n : ℝ) * (δ / 2)) := by
  let L : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (7 / 4 : ℝ) * δ))
  let B : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + (7 / 2 : ℝ) * δ))
  let A : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hQ_pos : 0 < Q := lt_of_lt_of_le hL_pos (by simpa [L] using hQ)
  have hQ_nonneg : 0 ≤ Q := hQ_pos.le
  have hsq_raw : L ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ hL_nonneg hQ_nonneg).mpr (by simpa [L] using hQ)
  have hL_sq : L ^ 2 = B := by
    dsimp [L, B]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hden : B ≤ Q ^ 2 := by
    simpa [hL_sq] using hsq_raw
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hnum_nonneg : 0 ≤ 4 * A := by nlinarith
  have hdiv :
      (4 * A) / (Q ^ 2) ≤ (4 * A) / B :=
    div_le_div_of_nonneg_left hnum_nonneg hB_pos hden
  have hratio : A / B = (2 : ℝ) ^ (-(n : ℝ) * (δ / 2)) := by
    dsimp [A, B]
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    4 * (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ)) / (Q ^ 2) =
        (4 * A) / (Q ^ 2) := by rfl
    _ ≤ (4 * A) / B := hdiv
    _ = 4 * (A / B) := by ring
    _ = 4 * (2 : ℝ) ^ (-(n : ℝ) * (δ / 2)) := by rw [hratio]

/-- Mixed-slack scalar denominator bridge for the padded source route: any
source numerator slack up to `7δ / 2` is absorbed by the source lower `A₁`
target and leaves the rounded `δ / 2` fourth-root decay. -/
private theorem fqsw_skoro_bound_le_iid_decay_of_num_slack
    (n : ℕ) (I δ Q c : ℝ)
    (hδ : 0 ≤ δ) (hc : c ≤ (7 / 2 : ℝ))
    (hQ :
      (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + 2 * δ)) ≤ Q) :
    4 * (2 : ℝ) ^ ((n : ℝ) * (I + c * δ)) / (Q ^ 2) ≤
      4 * (2 : ℝ) ^ (-(n : ℝ) * (δ / 2)) := by
  let L : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + 2 * δ))
  let B : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + 4 * δ))
  let A : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + c * δ))
  let C : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + (7 / 2 : ℝ) * δ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hQ_pos : 0 < Q := lt_of_lt_of_le hL_pos (by simpa [L] using hQ)
  have hQ_nonneg : 0 ≤ Q := hQ_pos.le
  have hsq_raw : L ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ hL_nonneg hQ_nonneg).mpr (by simpa [L] using hQ)
  have hL_sq : L ^ 2 = B := by
    dsimp [L, B]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hden : B ≤ Q ^ 2 := by
    simpa [hL_sq] using hsq_raw
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hA_le_C : A ≤ C := by
    dsimp [A, C]
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hexp :
        (n : ℝ) * (I + c * δ) ≤
          (n : ℝ) * (I + (7 / 2 : ℝ) * δ) := by
      exact mul_le_mul_of_nonneg_left (by nlinarith) hn
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hnum_le :
      (4 * A) / (Q ^ 2) ≤ (4 * C) / (Q ^ 2) := by
    have hmul : 4 * A ≤ 4 * C := by nlinarith
    exact div_le_div_of_nonneg_right hmul (sq_nonneg Q)
  have hnum_nonneg : 0 ≤ 4 * C := by nlinarith
  have hdiv :
      (4 * C) / (Q ^ 2) ≤ (4 * C) / B :=
    div_le_div_of_nonneg_left hnum_nonneg hB_pos hden
  have hratio : C / B = (2 : ℝ) ^ (-(n : ℝ) * (δ / 2)) := by
    dsimp [C, B]
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    4 * (2 : ℝ) ^ ((n : ℝ) * (I + c * δ)) / (Q ^ 2) =
        (4 * A) / (Q ^ 2) := by rfl
    _ ≤ (4 * C) / (Q ^ 2) := hnum_le
    _ ≤ (4 * C) / B := hdiv
    _ = 4 * (C / B) := by ring
    _ = 4 * (2 : ℝ) ^ (-(n : ℝ) * (δ / 2)) := by rw [hratio]

/-- ADHW `skoro` bridge, fqsw.tex lines 1148-1167: the source line-1158
one-shot argument bound plus the chosen/lower-bounded `A₁` dimension imply the
simplified i.i.d. one-shot error exponent. -/
theorem adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_skoro_bound
    (ψ : PureVector (Prod (Prod a b) r))
    {a1 : Type u1} {b1 : Type v1} {r1 : Type w1}
    [Fintype a1] [DecidableEq a1]
    [Fintype b1] [DecidableEq b1]
    [Fintype r1] [DecidableEq r1]
    (φ : PureVector (Prod (Prod a1 b1) r1))
    (q : Type x) [Fintype q]
    (n : ℕ) (δ : ℝ)
    (hskoro :
      adhwFQSWOneShotFourthRootArgument φ q ≤
        4 * (2 : ℝ) ^ ((n : ℝ) *
          (mutualInformation ψ.state.coherentTransferReferenceState + 3 * δ)) /
          ((Fintype.card q : ℝ) ^ 2))
    (hcardA1 :
      (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswCommunicationRate + 2 * δ)) ≤
        (Fintype.card q : ℝ)) :
    adhwFQSWOneShotErrorBound φ q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) := by
  let I : ℝ := mutualInformation ψ.state.coherentTransferReferenceState
  have hcard :
      (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + 2 * δ)) ≤
        (Fintype.card q : ℝ) := by
    simpa [I, PureVector.fqswCommunicationRate] using hcardA1
  have hdecay :=
    fqsw_skoro_bound_le_iid_decay
      (n := n) (I := I) (δ := δ) (Q := (Fintype.card q : ℝ)) hcard
  have harg :
      adhwFQSWOneShotFourthRootArgument φ q ≤
        4 * (2 : ℝ) ^ (-(n : ℝ) * δ) := by
    exact hskoro.trans (by simpa [I] using hdecay)
  exact
    adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_fourthRootArgument_le
      φ q n δ harg

/-- Rounded lower `A₁` communication-cardinality target used to construct
finite registers while keeping the public ADHW communication-rate target at
`+2δ`. -/
def adhwFQSWIidCommunicationLogLowerTarget
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * (ψ.fqswCommunicationRate + (7 / 4 : ℝ) * δ)

/-- ADHW source-route communication log target
`n [I(A;R)/2 + 2δ]` from fqsw.tex lines 1164-1178. -/
def adhwFQSWIidCommunicationLogTarget
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * (ψ.fqswCommunicationRate + 2 * δ)

/-- Rounded upper `A₁` communication log target used only to absorb the
finite-register ceiling slack while keeping the source lower target at
`I(A;R)/2 + 2δ`. -/
def adhwFQSWIidRoundedCommunicationLogUpperTarget
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * (ψ.fqswCommunicationRate + (9 / 4 : ℝ) * δ)

/-- Rounded ADHW `skoro` bridge for the finite-register i.i.d. route: the
source line-1158 numerator combines with the restored source lower `A₁` target
`I(A;R)/2 + 2δ`, and for nonnegative `δ` the stronger ADHW `δ / 4` decay
weakens to the legacy rounded `δ / 8` tail. -/
theorem adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_rounded_skoro_bound
    (ψ : PureVector (Prod (Prod a b) r))
    {a1 : Type u1} {b1 : Type v1} {r1 : Type w1}
    [Fintype a1] [DecidableEq a1]
    [Fintype b1] [DecidableEq b1]
    [Fintype r1] [DecidableEq r1]
    (φ : PureVector (Prod (Prod a1 b1) r1))
    (q : Type x) [Fintype q]
    (n : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hskoro :
      adhwFQSWOneShotFourthRootArgument φ q ≤
        4 * (2 : ℝ) ^ ((n : ℝ) *
          (mutualInformation ψ.state.coherentTransferReferenceState + 3 * δ)) /
          ((Fintype.card q : ℝ) ^ 2))
    (hcardA1 :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ ≤
        (Fintype.card q : ℝ)) :
    adhwFQSWOneShotErrorBound φ q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8)) := by
  have hexact :=
    adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_skoro_bound
      ψ φ q n δ hskoro hcardA1
  have htail :
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8)) := by
    have hbase : (1 : ℝ) ≤ 2 := by norm_num
    have hexp :
        -((n : ℝ) * δ / 4) ≤ -((n : ℝ) * δ / 8) := by
      have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      nlinarith
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    nlinarith [Real.sqrt_nonneg 8, hpow]
  exact hexact.trans htail

/-- Mixed-slack rounded ADHW `skoro` bridge for the padded source route.  The
source numerator may use any slack `cδ` with `c ≤ 7/2`; the finite-register
source lower `A₁` target still yields the rounded `δ / 8` one-shot tail. -/
theorem adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_slack_skoro_bound
    (ψ : PureVector (Prod (Prod a b) r))
    {a1 : Type u1} {b1 : Type v1} {r1 : Type w1}
    [Fintype a1] [DecidableEq a1]
    [Fintype b1] [DecidableEq b1]
    [Fintype r1] [DecidableEq r1]
    (φ : PureVector (Prod (Prod a1 b1) r1))
    (q : Type x) [Fintype q]
    (n : ℕ) (δ c : ℝ)
    (hδ : 0 ≤ δ) (hc : c ≤ (7 / 2 : ℝ))
    (hskoro :
      adhwFQSWOneShotFourthRootArgument φ q ≤
        4 * (2 : ℝ) ^ ((n : ℝ) *
          (mutualInformation ψ.state.coherentTransferReferenceState + c * δ)) /
          ((Fintype.card q : ℝ) ^ 2))
    (hcardA1 :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ ≤
        (Fintype.card q : ℝ)) :
    adhwFQSWOneShotErrorBound φ q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8)) := by
  let I : ℝ := mutualInformation ψ.state.coherentTransferReferenceState
  have hcard :
      (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + 2 * δ)) ≤
        (Fintype.card q : ℝ) := by
    simpa [I, adhwFQSWIidCommunicationLogTarget, PureVector.fqswCommunicationRate]
      using hcardA1
  have hdecay :=
    fqsw_skoro_bound_le_iid_decay_of_num_slack
      (n := n) (I := I) (δ := δ) (Q := (Fintype.card q : ℝ))
      (c := c) hδ hc hcard
  have harg :
      adhwFQSWOneShotFourthRootArgument φ q ≤
        4 * (2 : ℝ) ^ (-(n : ℝ) * (δ / 2)) := by
    exact hskoro.trans (by simpa [I] using hdecay)
  have htail :=
    adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_fourthRootArgument_le
      φ q n (δ / 2) harg
  simpa [show -((n : ℝ) * (δ / 2) / 4) = -((n : ℝ) * δ / 8) by ring]
    using htail

/-- Schumacher typical-support isometry, reindexed by a finite equivalence
from an externally named typical register. -/
private def adhwFQSWTypicalSupportIsometryOfEquiv
    {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (ρ : State α) (n : ℕ) (δ : ℝ)
    (E : ι ≃ State.TypicalSubspaceIndex ρ n δ) :
    ReferenceIsometry ι (TensorPower α n) :=
  ({ matrix := State.typicalIsometry ρ n δ
     isometry := State.typicalIsometry_conjTranspose_mul_self ρ n δ } :
    ReferenceIsometry (State.TypicalSubspaceIndex ρ n δ) (TensorPower α n)).comp
      (ReferenceIsometry.ofEquiv E)

/-- The reindexed Schumacher support isometry has the expected typical
projector as its range projection. -/
private theorem adhwFQSWTypicalSupportIsometryOfEquiv_range_projector
    {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (ρ : State α) (n : ℕ) (δ : ℝ)
    (E : ι ≃ State.TypicalSubspaceIndex ρ n δ) :
    (adhwFQSWTypicalSupportIsometryOfEquiv ρ n δ E).matrix *
        Matrix.conjTranspose
          (adhwFQSWTypicalSupportIsometryOfEquiv ρ n δ E).matrix =
      ρ.typicalSubspaceProjector n δ := by
  unfold adhwFQSWTypicalSupportIsometryOfEquiv
  dsimp [ReferenceIsometry.comp]
  let V := State.typicalIsometry ρ n δ
  let U := (ReferenceIsometry.ofEquiv E).matrix
  change (V * U) * Matrix.conjTranspose (V * U) = ρ.typicalSubspaceProjector n δ
  rw [Matrix.conjTranspose_mul]
  calc
    (V * U) * (Matrix.conjTranspose U * Matrix.conjTranspose V) =
        V * (U * Matrix.conjTranspose U) * Matrix.conjTranspose V := by
          simp [Matrix.mul_assoc]
    _ = V * (1 : CMatrix (State.TypicalSubspaceIndex ρ n δ)) *
        Matrix.conjTranspose V := by
          rw [referenceIsometry_ofEquiv_mul_conjTranspose E]
    _ = V * Matrix.conjTranspose V := by simp
    _ = ρ.typicalSubspaceProjector n δ := by
          simpa [V] using State.typicalIsometry_mul_conjTranspose ρ n δ

/-- Padded embedding of the ADHW typical Alice support `A^typ` into
`A₁ × A₂`, replacing the exact factorization assumption in fqsw.tex lines
1140-1147 by an injective finite-dimensional basis embedding. -/
structure ADHWFQSWPaddedAtypEmbedding
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ)
    (atyp : Type p) (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp] [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] where
  atypDimension_eq_projector_rank :
    (Fintype.card atyp : ℝ) =
      (adhwFQSWSystemAState ψ).typicalSubspaceDimension n δ
  supportIsometry : ReferenceIsometry atyp (TensorPower a n)
  supportIsometry_range_projector_eq :
    supportIsometry.matrix * Matrix.conjTranspose supportIsometry.matrix =
      (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ
  embedding : atyp ↪ Prod q e
  paddingSlack : ℕ
  card_add_padding_eq :
    Fintype.card atyp + paddingSlack = Fintype.card (Prod q e)

namespace ADHWFQSWPaddedAtypEmbedding

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ : ℝ}
variable {atyp : Type p} {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp] [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e]

/-- The padded basis embedding as an isometry `A^typ ↪ A₁ × A₂`, the formal
replacement for the exact tensor factorization in ADHW fqsw.tex lines
1140-1147. -/
def isometry (P : ADHWFQSWPaddedAtypEmbedding ψ n δ atyp q e) :
    ReferenceIsometry atyp (Prod q e) :=
  ReferenceIsometry.ofInjective P.embedding P.embedding.injective

/-- Lift a padded one-shot Alice coordinate back into the true typical Alice
support inside `A^n`: first project from `A₁ × A₂` onto the embedded `A^typ`
coordinates, then include the typical support into the full tensor power. -/
def supportLiftMatrix (P : ADHWFQSWPaddedAtypEmbedding ψ n δ atyp q e) :
    Matrix (TensorPower a n) (Prod q e) ℂ :=
  P.supportIsometry.matrix * Matrix.conjTranspose P.isometry.matrix

end ADHWFQSWPaddedAtypEmbedding

/-- The padded Alice lift has range equal to the true `A^n` typical
subspace projector. -/
theorem ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_mul_conjTranspose
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ : ℝ}
    {atyp : Type p} {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n δ atyp q e) :
    P.supportLiftMatrix * Matrix.conjTranspose P.supportLiftMatrix =
      (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ := by
  calc
    P.supportLiftMatrix * Matrix.conjTranspose P.supportLiftMatrix =
        P.supportIsometry.matrix *
          (Matrix.conjTranspose P.isometry.matrix * P.isometry.matrix) *
            Matrix.conjTranspose P.supportIsometry.matrix := by
          simp [ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix, Matrix.conjTranspose_mul,
            Matrix.mul_assoc]
    _ = P.supportIsometry.matrix * Matrix.conjTranspose P.supportIsometry.matrix := by
          rw [P.isometry.isometry]
          simp
    _ = (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ :=
          P.supportIsometry_range_projector_eq

/-- The padded Alice lift has initial projection equal to the embedded
`A^typ` support inside the padded `A₁ × A₂` register. -/
theorem ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_conjTranspose_mul
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ : ℝ}
    {atyp : Type p} {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n δ atyp q e) :
    Matrix.conjTranspose P.supportLiftMatrix * P.supportLiftMatrix =
      P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix := by
  calc
    Matrix.conjTranspose P.supportLiftMatrix * P.supportLiftMatrix =
        P.isometry.matrix *
          (Matrix.conjTranspose P.supportIsometry.matrix * P.supportIsometry.matrix) *
            Matrix.conjTranspose P.isometry.matrix := by
          simp [ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix, Matrix.conjTranspose_mul,
            Matrix.mul_assoc]
    _ = P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix := by
          rw [P.supportIsometry.isometry]
          simp

/-- The padded Alice lift is supported on the embedded `A^typ` coordinates in
the padded `A₁ × A₂` register. -/
theorem ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_mul_initialProjection
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ : ℝ}
    {atyp : Type p} {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n δ atyp q e) :
    P.supportLiftMatrix *
        (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix) =
      P.supportLiftMatrix := by
  calc
    P.supportLiftMatrix *
        (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix) =
        P.supportIsometry.matrix *
          ((Matrix.conjTranspose P.isometry.matrix * P.isometry.matrix) *
            Matrix.conjTranspose P.isometry.matrix) := by
          simp [ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix, Matrix.mul_assoc]
    _ = P.supportLiftMatrix := by
          rw [P.isometry.isometry]
          simp [ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix]

/-- Construct the padded `A^typ ↪ A₁ × A₂` embedding from the rank identity and
the finite cardinality inequality. -/
theorem exists_adhwFQSWPaddedAtypEmbedding
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ)
    (atyp : Type p) (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp] [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (hdim :
      (Fintype.card atyp : ℝ) =
        (adhwFQSWSystemAState ψ).typicalSubspaceDimension n δ)
    (hcard : Fintype.card atyp ≤ Fintype.card (Prod q e)) :
    Nonempty (ADHWFQSWPaddedAtypEmbedding ψ n δ atyp q e) := by
  classical
  let atypIndex : Type u :=
    State.TypicalSubspaceIndex (adhwFQSWSystemAState ψ) n δ
  have hindex :
      (Fintype.card atypIndex : ℝ) =
        (adhwFQSWSystemAState ψ).typicalSubspaceDimension n δ := by
    simpa [atypIndex] using
      State.card_typicalSubspaceIndex (adhwFQSWSystemAState ψ) n δ
  have hcardIndex : Fintype.card atyp = Fintype.card atypIndex := by
    have hreal : (Fintype.card atyp : ℝ) = (Fintype.card atypIndex : ℝ) :=
      hdim.trans hindex.symm
    exact_mod_cast hreal
  let E : atyp ≃ atypIndex := Fintype.equivOfCardEq hcardIndex
  let supportIsometry : ReferenceIsometry atyp (TensorPower a n) :=
    adhwFQSWTypicalSupportIsometryOfEquiv (adhwFQSWSystemAState ψ) n δ E
  have hrangeA :
      supportIsometry.matrix * Matrix.conjTranspose supportIsometry.matrix =
        (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ := by
    simpa [supportIsometry] using
      adhwFQSWTypicalSupportIsometryOfEquiv_range_projector
        (adhwFQSWSystemAState ψ) n δ E
  exact
    ⟨{ atypDimension_eq_projector_rank := hdim
       supportIsometry := supportIsometry
       supportIsometry_range_projector_eq := hrangeA
       embedding := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
       paddingSlack := Fintype.card (Prod q e) - Fintype.card atyp
       card_add_padding_eq := Nat.add_sub_cancel' hcard }⟩

/-- ADHW source-route ebit-yield log lower target
`n [I(A;B)/2 - 3δ]` from fqsw.tex lines 1177-1180. -/
def adhwFQSWIidEbitYieldLogLower
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * (ψ.fqswEbitYieldRate - 3 * δ)

/-- Post-compression trace-norm bound
`2ε + √8 · 2^{-nδ/4}` from ADHW fqsw.tex lines 1168-1175. -/
def adhwFQSWIidPostCompressionTraceErrorBound (ε : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  2 * ε + Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4))

/-- Rounded post-compression trace-norm bound obtained from the finite-register
communication rounding slack. -/
def adhwFQSWIidRoundedPostCompressionTraceErrorBound
    (ε : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  2 * ε + Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))

/-- With positive typicality slack, the ADHW post-compression tail
`2^{-nδ/4}` is eventually small enough that using internal error `ε/4`
gives normalized error at most `ε`. -/
theorem eventually_half_adhwFQSWIidPostCompressionTraceErrorBound_le
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (1 / 2 : ℝ) *
        adhwFQSWIidPostCompressionTraceErrorBound (ε / 4) n δ ≤ ε := by
  set base : ℝ := (2 : ℝ) ^ (-(δ / 4)) with hbase
  have hbase_nonneg : 0 ≤ base := by
    rw [hbase]
    exact Real.rpow_nonneg (by norm_num) _
  have hbase_lt_one : base < 1 := by
    rw [hbase]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbase_tendsto :
      Filter.Tendsto (fun n : ℕ => base ^ n) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt_one
  have htail_eq :
      ∀ n : ℕ, (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) = base ^ n := by
    intro n
    rw [hbase]
    rw [show -((n : ℝ) * δ / 4) = -(δ / 4) * (n : ℝ) by ring]
    rw [Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    rw [Real.rpow_natCast]
  have htail_tendsto :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (-((n : ℝ) * δ / 4)))
        Filter.atTop (nhds (0 : ℝ)) :=
    hbase_tendsto.congr' (Filter.Eventually.of_forall fun n => (htail_eq n).symm)
  have hlim :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) *
            adhwFQSWIidPostCompressionTraceErrorBound (ε / 4) n δ)
        Filter.atTop (nhds (ε / 4)) := by
    have hscaled :
        Filter.Tendsto
          (fun n : ℕ =>
            (1 / 2 : ℝ) *
              (Real.sqrt 8 * ((2 : ℝ) ^ (-((n : ℝ) * δ / 4)))))
          Filter.atTop (nhds (0 : ℝ)) := by
      have hscaled' :
          Filter.Tendsto
            (fun n : ℕ =>
              ((1 / 2 : ℝ) * Real.sqrt 8) *
                ((2 : ℝ) ^ (-((n : ℝ) * δ / 4))))
            Filter.atTop (nhds (0 : ℝ)) := by
        simpa using
          (tendsto_const_nhds (x := ((1 / 2 : ℝ) * Real.sqrt 8))).mul htail_tendsto
      simpa [mul_assoc] using hscaled'
    have hconst :
        Filter.Tendsto (fun _ : ℕ => ε / 4) Filter.atTop (nhds (ε / 4)) :=
      tendsto_const_nhds
    simpa [adhwFQSWIidPostCompressionTraceErrorBound, mul_add, mul_assoc,
      div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using hconst.add hscaled
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        (1 / 2 : ℝ) *
          adhwFQSWIidPostCompressionTraceErrorBound (ε / 4) n δ ≤ ε :=
    hlim.eventually_le_const (by linarith)
  exact Filter.eventually_atTop.mp hevent

/-- The rounded post-compression tail still vanishes exponentially; it is the
original ADHW tail reused at slack `δ / 2`. -/
theorem eventually_half_adhwFQSWIidRoundedPostCompressionTraceErrorBound_le
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (1 / 2 : ℝ) *
        adhwFQSWIidRoundedPostCompressionTraceErrorBound (ε / 4) n δ ≤ ε := by
  obtain ⟨N, hN⟩ :=
    eventually_half_adhwFQSWIidPostCompressionTraceErrorBound_le
      (δ := δ / 2) (ε := ε) (by positivity) hε
  refine ⟨N, ?_⟩
  intro n hn
  have hbound := hN n hn
  have hexp : -((n : ℝ) * (δ / 2) / 4) = -((n : ℝ) * δ / 8) := by ring
  simpa [adhwFQSWIidRoundedPostCompressionTraceErrorBound,
    adhwFQSWIidPostCompressionTraceErrorBound, hexp] using hbound

/-- Base-two logarithm is monotone on positive reals. -/
private theorem log2_mono_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos one_lt_two))

/-- The base-two logarithm inverts positive powers of two. -/
private theorem log2_two_rpow (x : ℝ) :
    log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [show Real.log ((2 : ℝ) ^ x) = x * Real.log 2 by
    exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) x]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

/-- Base-two powers invert `log2` on positive reals. -/
private theorem two_rpow_log2_pos {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ log2 x = x := by
  apply Real.log_injOn_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hx
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  unfold log2
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

/-- Upper cardinality bounds convert into upper base-two log bounds. -/
private theorem log2_le_of_le_two_rpow {x t : ℝ}
    (hx : 0 < x) (hxt : x ≤ (2 : ℝ) ^ t) :
    log2 x ≤ t := by
  have hlog := log2_mono_of_pos hx hxt
  simpa [log2_two_rpow] using hlog

/-- Upper base-two log bounds convert into upper cardinality bounds. -/
theorem le_two_rpow_of_log2_le {x t : ℝ}
    (hx : 0 < x) (hxt : log2 x ≤ t) :
    x ≤ (2 : ℝ) ^ t := by
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le
      (x := (2 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2) hxt
  simpa [two_rpow_log2_pos hx] using hpow

/-- Lower powers-of-two cardinality bounds convert into lower base-two log
bounds. -/
private theorem le_log2_of_two_rpow_le {x y : ℝ}
    (hxy : (2 : ℝ) ^ x ≤ y) :
    x ≤ log2 y := by
  have hlog := log2_mono_of_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x) hxy
  simpa [log2_two_rpow] using hlog

/-- Finite-register rate choice for ADHW fqsw.tex lines 1164-1180.

The source text writes real logarithmic dimensions.  This record is the
rounding interface used by finite Lean registers: `A₁` must still meet the
source lower target, but its finite rounded size is only required to stay below
the separate `+9δ/4` upper target.  `A₂` records the resulting ebit-yield lower
bound. -/
structure ADHWFQSWIidRateChoice
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ)
    (q : Type x) (e : Type y) [Fintype q] [Fintype e] where
  communication_log_le :
    log2 (Fintype.card q : ℝ) ≤
      adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ
  communication_card_lower :
    (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ <=
      (Fintype.card q : ℝ)
  ebitYield_log_ge :
    adhwFQSWIidEbitYieldLogLower ψ n δ ≤ log2 (Fintype.card e : ℝ)

namespace ADHWFQSWIidRateChoice

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ : ℝ}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

/-- Communication-rate rounding lemma for the raw finite `A₁` register used by
the source-route block. -/
theorem communicationLogRate_le (R : ADHWFQSWIidRateChoice ψ n δ q e)
    (hn : 0 < n) :
    log2 (Fintype.card q : ℝ) / (n : ℝ) ≤
      ψ.fqswCommunicationRate + (9 / 4 : ℝ) * δ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [div_le_iff₀ hnR]
  simpa [adhwFQSWIidRoundedCommunicationLogUpperTarget, mul_comm] using
    R.communication_log_le

/-- Communication-rate rounding lemma with the ADHW `+2δ` constant from
fqsw.tex lines 1164-1178, widened only by the finite-register ceiling slack to
`+9δ/4`. -/
theorem communicationRate_le (R : ADHWFQSWIidRateChoice ψ n δ q e)
    (C : FQSWBlockProtocol ψ n q e et) (hn : 0 < n) :
    FQSWBlockProtocol.communicationRate C ≤
      ψ.fqswCommunicationRate + (9 / 4 : ℝ) * δ := by
  unfold FQSWBlockProtocol.communicationRate
  rw [if_neg (Nat.ne_of_gt hn)]
  exact R.communicationLogRate_le hn

/-- Ebit-yield rounding lemma for the raw finite `A₂` register used by the
source-route block. -/
theorem ebitYieldLogRate_ge (R : ADHWFQSWIidRateChoice ψ n δ q e)
    (hn : 0 < n) :
    ψ.fqswEbitYieldRate - 3 * δ ≤ log2 (Fintype.card e : ℝ) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnR]
  simpa [adhwFQSWIidEbitYieldLogLower, mul_comm] using R.ebitYield_log_ge

/-- Ebit-yield rounding lemma with the ADHW `-3δ` constant from fqsw.tex
lines 1177-1180. -/
theorem ebitYieldRate_ge (R : ADHWFQSWIidRateChoice ψ n δ q e)
    (C : FQSWBlockProtocol ψ n q e et) (hn : 0 < n) :
    ψ.fqswEbitYieldRate - 3 * δ ≤ FQSWBlockProtocol.ebitYieldRate C := by
  unfold FQSWBlockProtocol.ebitYieldRate
  rw [if_neg (Nat.ne_of_gt hn)]
  exact R.ebitYieldLogRate_ge hn

end ADHWFQSWIidRateChoice

/-- Construct the finite-register ADHW i.i.d. rate choice from the two rounded
log-dimension inequalities. -/
theorem exists_adhwFQSWIidRateChoice
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ)
    (q : Type x) (e : Type y) [Fintype q] [Fintype e]
    (hcomm :
      log2 (Fintype.card q : ℝ) ≤
        adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ)
    (hcommLower :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ <=
        (Fintype.card q : ℝ))
    (hebit :
      adhwFQSWIidEbitYieldLogLower ψ n δ ≤ log2 (Fintype.card e : ℝ)) :
    Nonempty (ADHWFQSWIidRateChoice ψ n δ q e) :=
  ⟨{ communication_log_le := hcomm
     communication_card_lower := hcommLower
     ebitYield_log_ge := hebit }⟩

/-- Finite `q`/`e` register construction for the rounded ADHW i.i.d. rate
choice: `q` is chosen from the source `+2δ` lower communication-card target,
while the separate rounded `+9δ/4` communication-rate cap absorbs the `+1`
ceiling error once the residual slack `δ / 4` is at least one bit. -/
theorem exists_adhwFQSWIidRateChoice_registers
    (ψ : PureVector (Prod (Prod a b) r)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q), ∃ (_ : Nonempty q),
        ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
          Nonempty (ADHWFQSWIidRateChoice ψ n δ q e) := by
  refine ⟨Nat.ceil (4 / δ), ?_⟩
  intro n hn
  set lower := adhwFQSWIidCommunicationLogTarget ψ n δ
  set upper := adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ
  set qSize : ℕ := Nat.ceil ((2 : ℝ) ^ lower)
  let q : Type x := ULift.{x} (Fin qSize)
  haveI : Fintype q := inferInstance
  haveI : DecidableEq q := inferInstance
  have hqcard : Fintype.card q = qSize := by
    simpa [q] using
      (Fintype.card_congr (Equiv.ulift : ULift.{x} (Fin qSize) ≃ Fin qSize))
  have hpow_lower_pos : 0 < (2 : ℝ) ^ lower :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) lower
  have hqSize_pos : 0 < qSize := by
    exact Nat.ceil_pos.mpr hpow_lower_pos
  haveI : Nonempty q := ⟨ULift.up ⟨0, hqSize_pos⟩⟩
  set eLower := adhwFQSWIidEbitYieldLogLower ψ n δ
  set eSize : ℕ := max 1 (Nat.ceil ((2 : ℝ) ^ eLower))
  let e : Type y := ULift.{y} (Fin eSize)
  haveI : Fintype e := inferInstance
  haveI : DecidableEq e := inferInstance
  have hecard : Fintype.card e = eSize := by
    simpa [e] using
      (Fintype.card_congr (Equiv.ulift : ULift.{y} (Fin eSize) ≃ Fin eSize))
  have heSize_pos : 0 < eSize := by
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  haveI : Nonempty e := ⟨ULift.up ⟨0, heSize_pos⟩⟩
  have hcommLower :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ ≤
        (Fintype.card q : ℝ) := by
    have hceil : (2 : ℝ) ^ lower ≤ (qSize : ℝ) := Nat.le_ceil _
    have hqcardR : (Fintype.card q : ℝ) = (qSize : ℝ) := by
      exact_mod_cast hqcard
    simpa [hqcardR]
      using hceil
  have hgap_ge_one : (1 : ℝ) ≤ (n : ℝ) * δ / 4 := by
    have hceil : 4 / δ ≤ (Nat.ceil (4 / δ) : ℝ) := Nat.le_ceil (4 / δ)
    have hnR : (Nat.ceil (4 / δ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hbound : 4 / δ ≤ (n : ℝ) := hceil.trans hnR
    have hmul := mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ δ / 4)
    have hcancel : (4 / δ) * (δ / 4) = 1 := by
      field_simp [ne_of_gt hδ]
    nlinarith
  have hlower_nonneg : 0 ≤ lower := by
    have hI_nonneg :
        0 ≤ mutualInformation ψ.state.coherentTransferReferenceState :=
      State.mutualInformation_nonneg ψ.state.coherentTransferReferenceState
    have hinner : 0 ≤ ψ.fqswCommunicationRate + 2 * δ := by
      unfold PureVector.fqswCommunicationRate
      nlinarith
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    dsimp [lower, adhwFQSWIidCommunicationLogTarget]
    exact mul_nonneg hn_nonneg hinner
  have hone_le_pow_lower : (1 : ℝ) ≤ (2 : ℝ) ^ lower := by
    calc
      (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (2 : ℝ) ^ lower := by
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlower_nonneg
  have hpow_lower_nonneg : 0 ≤ (2 : ℝ) ^ lower := by
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hupper_eq :
      upper = lower + (n : ℝ) * δ / 4 := by
    dsimp [upper, lower, adhwFQSWIidRoundedCommunicationLogUpperTarget,
      adhwFQSWIidCommunicationLogTarget]
    ring
  have htwo_le_gap_pow : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * δ / 4) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * δ / 4) := by
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hgap_ge_one
  have hcommUpper :
      (Fintype.card q : ℝ) ≤
        (2 : ℝ) ^ adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ := by
    have hceil_lt : (qSize : ℝ) < (2 : ℝ) ^ lower + 1 :=
      Nat.ceil_lt_add_one (le_of_lt hpow_lower_pos)
    have hsum_le_double : (2 : ℝ) ^ lower + 1 ≤ 2 * (2 : ℝ) ^ lower := by
      nlinarith
    have hdouble_le :
        2 * (2 : ℝ) ^ lower ≤ (2 : ℝ) ^ upper := by
      have hmul :=
        mul_le_mul_of_nonneg_right htwo_le_gap_pow hpow_lower_nonneg
      calc
        2 * (2 : ℝ) ^ lower ≤
            ((2 : ℝ) ^ ((n : ℝ) * δ / 4)) * ((2 : ℝ) ^ lower) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        _ = (2 : ℝ) ^ upper := by
            rw [hupper_eq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            ring
    have hcard_lt :
        (Fintype.card q : ℝ) < (2 : ℝ) ^ lower + 1 := by
      have hqcardR : (Fintype.card q : ℝ) = (qSize : ℝ) := by
        exact_mod_cast hqcard
      simpa [hqcardR] using hceil_lt
    exact le_trans (le_of_lt hcard_lt) (hsum_le_double.trans hdouble_le)
  have hq_pos_nat : 0 < Fintype.card q := by
    simpa [hqcard] using hqSize_pos
  have hq_pos : 0 < (Fintype.card q : ℝ) := by
    exact_mod_cast hq_pos_nat
  have hcomm :
      log2 (Fintype.card q : ℝ) ≤
        adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ := by
    have hlog := log2_le_of_le_two_rpow hq_pos hcommUpper
    simpa [upper] using hlog
  have hebit_card :
      (2 : ℝ) ^ adhwFQSWIidEbitYieldLogLower ψ n δ ≤
        (Fintype.card e : ℝ) := by
    have hceil : (2 : ℝ) ^ eLower ≤ (Nat.ceil ((2 : ℝ) ^ eLower) : ℝ) := Nat.le_ceil _
    have hmax :
        ((Nat.ceil ((2 : ℝ) ^ eLower) : ℕ) : ℝ) ≤ (eSize : ℝ) := by
      exact_mod_cast (Nat.le_max_right 1 (Nat.ceil ((2 : ℝ) ^ eLower)))
    have hecardR : (Fintype.card e : ℝ) = (eSize : ℝ) := by
      exact_mod_cast hecard
    exact hceil.trans (by simpa [hecardR] using hmax)
  have he_pos_nat : 0 < Fintype.card e := by
    simpa [hecard] using heSize_pos
  have hebit :
      adhwFQSWIidEbitYieldLogLower ψ n δ ≤ log2 (Fintype.card e : ℝ) := by
    exact le_log2_of_two_rpow_le hebit_card
  refine ⟨q, inferInstance, inferInstance, inferInstance,
    e, inferInstance, inferInstance, inferInstance, ?_⟩
  exact exists_adhwFQSWIidRateChoice ψ n δ q e hcomm hcommLower hebit

/-- Rounded ADHW i.i.d. rate choice together with the tighter `A₂` window
needed to balance the finite cardinality side conditions. -/
structure ADHWFQSWIidBalancedRateChoice
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ)
    (q : Type x) (e : Type y) [Fintype q] [Fintype e] where
  rateChoice : ADHWFQSWIidRateChoice ψ n δ q e
  ebit_card_lower_for_padding :
    (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswEbitYieldRate - δ)) <=
      (Fintype.card e : ℝ)
  ebit_card_upper_for_target :
    (Fintype.card e : ℝ) <=
      (2 : ℝ) ^ ((n : ℝ) * ψ.fqswEbitYieldRate)

/-- Finite `q`/`e` register construction for the balanced ADHW i.i.d. rate
choice: `A₁` keeps the existing rounded communication bounds, while `A₂`
is rounded inside the balanced window
`[2^(n (I(A;B)/2 - δ)), 2^(n I(A;B)/2)]`. -/
theorem exists_adhwFQSWIidBalancedRateChoice_registers
    (ψ : PureVector (Prod (Prod a b) r)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q), ∃ (_ : Nonempty q),
        ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
          Nonempty (ADHWFQSWIidBalancedRateChoice ψ n δ q e) := by
  refine ⟨Nat.ceil (4 / δ), ?_⟩
  intro n hn
  set lower := adhwFQSWIidCommunicationLogTarget ψ n δ
  set upper := adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ
  set qSize : ℕ := Nat.ceil ((2 : ℝ) ^ lower)
  let q : Type x := ULift.{x} (Fin qSize)
  haveI : Fintype q := inferInstance
  haveI : DecidableEq q := inferInstance
  have hqcard : Fintype.card q = qSize := by
    simpa [q] using
      (Fintype.card_congr (Equiv.ulift : ULift.{x} (Fin qSize) ≃ Fin qSize))
  have hpow_lower_pos : 0 < (2 : ℝ) ^ lower :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) lower
  have hqSize_pos : 0 < qSize := by
    exact Nat.ceil_pos.mpr hpow_lower_pos
  haveI : Nonempty q := ⟨ULift.up ⟨0, hqSize_pos⟩⟩
  set eLower := (n : ℝ) * (ψ.fqswEbitYieldRate - δ)
  set eUpper := (n : ℝ) * ψ.fqswEbitYieldRate
  set eSize : ℕ := Nat.ceil ((2 : ℝ) ^ eLower)
  let e : Type y := ULift.{y} (Fin eSize)
  haveI : Fintype e := inferInstance
  haveI : DecidableEq e := inferInstance
  have hecard : Fintype.card e = eSize := by
    simpa [e] using
      (Fintype.card_congr (Equiv.ulift : ULift.{y} (Fin eSize) ≃ Fin eSize))
  have hpow_eLower_pos : 0 < (2 : ℝ) ^ eLower :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) eLower
  have heSize_pos : 0 < eSize := by
    exact Nat.ceil_pos.mpr hpow_eLower_pos
  haveI : Nonempty e := ⟨ULift.up ⟨0, heSize_pos⟩⟩
  have hcommLower :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ ≤
        (Fintype.card q : ℝ) := by
    have hceil : (2 : ℝ) ^ lower ≤ (qSize : ℝ) := Nat.le_ceil _
    have hqcardR : (Fintype.card q : ℝ) = (qSize : ℝ) := by
      exact_mod_cast hqcard
    simpa [hqcardR] using hceil
  have hgap_ge_one : (1 : ℝ) ≤ (n : ℝ) * δ / 4 := by
    have hceil : 4 / δ ≤ (Nat.ceil (4 / δ) : ℝ) := Nat.le_ceil (4 / δ)
    have hnR : (Nat.ceil (4 / δ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hbound : 4 / δ ≤ (n : ℝ) := hceil.trans hnR
    have hmul := mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ δ / 4)
    have hcancel : (4 / δ) * (δ / 4) = 1 := by
      field_simp [ne_of_gt hδ]
    nlinarith
  have hlower_nonneg : 0 ≤ lower := by
    have hI_nonneg :
        0 ≤ mutualInformation ψ.state.coherentTransferReferenceState :=
      State.mutualInformation_nonneg ψ.state.coherentTransferReferenceState
    have hinner : 0 ≤ ψ.fqswCommunicationRate + 2 * δ := by
      unfold PureVector.fqswCommunicationRate
      nlinarith
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    dsimp [lower, adhwFQSWIidCommunicationLogTarget]
    exact mul_nonneg hn_nonneg hinner
  have hone_le_pow_lower : (1 : ℝ) ≤ (2 : ℝ) ^ lower := by
    calc
      (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (2 : ℝ) ^ lower := by
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlower_nonneg
  have hpow_lower_nonneg : 0 ≤ (2 : ℝ) ^ lower := by
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hupper_eq :
      upper = lower + (n : ℝ) * δ / 4 := by
    dsimp [upper, lower, adhwFQSWIidRoundedCommunicationLogUpperTarget,
      adhwFQSWIidCommunicationLogTarget]
    ring
  have htwo_le_gap_pow : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * δ / 4) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * δ / 4) := by
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hgap_ge_one
  have hcommUpper :
      (Fintype.card q : ℝ) ≤
        (2 : ℝ) ^ adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ := by
    have hceil_lt : (qSize : ℝ) < (2 : ℝ) ^ lower + 1 :=
      Nat.ceil_lt_add_one (le_of_lt hpow_lower_pos)
    have hsum_le_double : (2 : ℝ) ^ lower + 1 ≤ 2 * (2 : ℝ) ^ lower := by
      nlinarith
    have hdouble_le :
        2 * (2 : ℝ) ^ lower ≤ (2 : ℝ) ^ upper := by
      have hmul :=
        mul_le_mul_of_nonneg_right htwo_le_gap_pow hpow_lower_nonneg
      calc
        2 * (2 : ℝ) ^ lower ≤
            ((2 : ℝ) ^ ((n : ℝ) * δ / 4)) * ((2 : ℝ) ^ lower) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        _ = (2 : ℝ) ^ upper := by
            rw [hupper_eq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            ring
    have hcard_lt :
        (Fintype.card q : ℝ) < (2 : ℝ) ^ lower + 1 := by
      have hqcardR : (Fintype.card q : ℝ) = (qSize : ℝ) := by
        exact_mod_cast hqcard
      simpa [hqcardR] using hceil_lt
    exact le_trans (le_of_lt hcard_lt) (hsum_le_double.trans hdouble_le)
  have hq_pos_nat : 0 < Fintype.card q := by
    simpa [hqcard] using hqSize_pos
  have hq_pos : 0 < (Fintype.card q : ℝ) := by
    exact_mod_cast hq_pos_nat
  have hcomm :
      log2 (Fintype.card q : ℝ) ≤
        adhwFQSWIidRoundedCommunicationLogUpperTarget ψ n δ := by
    have hlog := log2_le_of_le_two_rpow hq_pos hcommUpper
    simpa [upper] using hlog
  have hebit_card_lower :
      (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswEbitYieldRate - δ)) ≤
        (Fintype.card e : ℝ) := by
    have hceil : (2 : ℝ) ^ eLower ≤ (eSize : ℝ) := Nat.le_ceil _
    have hecardR : (Fintype.card e : ℝ) = (eSize : ℝ) := by
      exact_mod_cast hecard
    simpa [eLower, hecardR] using hceil
  have hEbit_nonneg : 0 ≤ ψ.fqswEbitYieldRate := by
    unfold PureVector.fqswEbitYieldRate
    have hmi_nonneg : 0 ≤ mutualInformation ψ.state.marginalA :=
      State.mutualInformation_nonneg ψ.state.marginalA
    nlinarith
  have heUpper_nonneg : 0 ≤ eUpper := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    dsimp [eUpper]
    exact mul_nonneg hn_nonneg hEbit_nonneg
  have hgap_e_ge_one : (1 : ℝ) ≤ (n : ℝ) * δ := by
    nlinarith
  have heUpper_eq : eUpper = eLower + (n : ℝ) * δ := by
    dsimp [eUpper, eLower]
    ring
  have hebit_card_upper :
      (Fintype.card e : ℝ) <= (2 : ℝ) ^ ((n : ℝ) * ψ.fqswEbitYieldRate) := by
    by_cases hlow_nonpos : eLower ≤ 0
    · have hpow_le_one : (2 : ℝ) ^ eLower ≤ 1 := by
        exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2) hlow_nonpos
      have heSize_eq_one : eSize = 1 := by
        dsimp [eSize]
        refine (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).2 ?_
        constructor
        · simpa using hpow_eLower_pos
        · simpa using hpow_le_one
      have hecard_one : (Fintype.card e : ℝ) = 1 := by
        have hecard_nat : Fintype.card e = 1 := by
          calc
            Fintype.card e = eSize := hecard
            _ = 1 := heSize_eq_one
        exact_mod_cast hecard_nat
      have hone_le_upper : (1 : ℝ) ≤ (2 : ℝ) ^ eUpper := by
        calc
          (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by simp
          _ ≤ (2 : ℝ) ^ eUpper := by
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) heUpper_nonneg
      simpa [hecard_one, eUpper] using hone_le_upper
    · have hlow_pos : 0 < eLower := lt_of_not_ge hlow_nonpos
      have hone_le_pow_eLower : (1 : ℝ) ≤ (2 : ℝ) ^ eLower := by
        calc
          (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by simp
          _ ≤ (2 : ℝ) ^ eLower := by
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlow_pos.le
      have htwo_le_gap_pow : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * δ) := by
        calc
          (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
          _ ≤ (2 : ℝ) ^ ((n : ℝ) * δ) := by
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hgap_e_ge_one
      have hceil_lt : (eSize : ℝ) < (2 : ℝ) ^ eLower + 1 :=
        Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) eLower))
      have hsum_le_double : (2 : ℝ) ^ eLower + 1 ≤ 2 * (2 : ℝ) ^ eLower := by
        nlinarith
      have hpow_eLower_nonneg : 0 ≤ (2 : ℝ) ^ eLower := by
        exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      have hdouble_le :
          2 * (2 : ℝ) ^ eLower ≤ (2 : ℝ) ^ eUpper := by
        have hmul := mul_le_mul_of_nonneg_right htwo_le_gap_pow hpow_eLower_nonneg
        calc
          2 * (2 : ℝ) ^ eLower ≤
              ((2 : ℝ) ^ ((n : ℝ) * δ)) * ((2 : ℝ) ^ eLower) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          _ = (2 : ℝ) ^ eUpper := by
              rw [heUpper_eq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              ring
      have hcard_lt :
          (Fintype.card e : ℝ) < (2 : ℝ) ^ eLower + 1 := by
        have hecardR : (Fintype.card e : ℝ) = (eSize : ℝ) := by
          exact_mod_cast hecard
        simpa [hecardR] using hceil_lt
      have hcard_le_upper : (Fintype.card e : ℝ) ≤ (2 : ℝ) ^ eUpper := by
        exact le_trans (le_of_lt hcard_lt) (hsum_le_double.trans hdouble_le)
      simpa [eUpper] using hcard_le_upper
  have hebit :
      adhwFQSWIidEbitYieldLogLower ψ n δ ≤ log2 (Fintype.card e : ℝ) := by
    have hweaken :
        adhwFQSWIidEbitYieldLogLower ψ n δ ≤
          (n : ℝ) * (ψ.fqswEbitYieldRate - δ) := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      dsimp [adhwFQSWIidEbitYieldLogLower, eLower]
      nlinarith
    exact hweaken.trans (le_log2_of_two_rpow_le hebit_card_lower)
  have hrateChoice :
      Nonempty (ADHWFQSWIidRateChoice ψ n δ q e) :=
    exists_adhwFQSWIidRateChoice ψ n δ q e hcomm hcommLower hebit
  obtain ⟨R⟩ := hrateChoice
  refine ⟨q, inferInstance, inferInstance, inferInstance,
    e, inferInstance, inferInstance, inferInstance, ?_⟩
  exact
    ⟨{ rateChoice := R
       ebit_card_lower_for_padding := by simpa [eLower] using hebit_card_lower
       ebit_card_upper_for_target := by simpa [eUpper] using hebit_card_upper }⟩

/-- Finite Bob typical register matching the simultaneous-typicality `B`
subspace dimension used in the ADHW i.i.d. source route. -/
structure ADHWFQSWIidTypicalBobRegister
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (btyp : Type u1) [Fintype btyp] [DecidableEq btyp] where
  card_eq_projector_rank :
    (Fintype.card btyp : ℝ) =
      (adhwFQSWSystemBState ψ).typicalSubspaceDimension n T.typicalitySlack
  supportIsometry : ReferenceIsometry btyp (TensorPower b n)
  supportIsometry_range_projector_eq :
    supportIsometry.matrix * Matrix.conjTranspose supportIsometry.matrix =
      (adhwFQSWSystemBState ψ).typicalSubspaceProjector n T.typicalitySlack

/-- Finite reference typical register matching the simultaneous-typicality `R`
subspace dimension used in the ADHW i.i.d. source route. -/
structure ADHWFQSWIidTypicalRefRegister
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (rtyp : Type v1) [Fintype rtyp] [DecidableEq rtyp] where
  card_eq_projector_rank :
    (Fintype.card rtyp : ℝ) =
      (adhwFQSWSystemRState ψ).typicalSubspaceDimension n T.typicalitySlack
  supportIsometry : ReferenceIsometry rtyp (TensorPower r n)
  supportIsometry_range_projector_eq :
    supportIsometry.matrix * Matrix.conjTranspose supportIsometry.matrix =
      (adhwFQSWSystemRState ψ).typicalSubspaceProjector n T.typicalitySlack

/-- Construct the finite typical support registers `A^typ`, `B^typ`, and
`R^typ` used in the ADHW i.i.d. source route directly from the existing
Schumacher typical-subspace index types. -/
theorem exists_adhwFQSWIidTypicalSupportRegisters
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε) :
    ∃ (atyp : Type u), ∃ (_ : Fintype atyp), ∃ (_ : DecidableEq atyp),
      ∃ (btyp : Type v), ∃ (_ : Fintype btyp), ∃ (_ : DecidableEq btyp),
        ∃ (rtyp : Type w), ∃ (_ : Fintype rtyp), ∃ (_ : DecidableEq rtyp),
          (Fintype.card atyp : ℝ) =
            (adhwFQSWSystemAState ψ).typicalSubspaceDimension n T.typicalitySlack ∧
          Nonempty (ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp) ∧
          Nonempty (ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) := by
  let atyp : Type u :=
    State.TypicalSubspaceIndex (adhwFQSWSystemAState ψ) n T.typicalitySlack
  let btyp : Type v :=
    State.TypicalSubspaceIndex (adhwFQSWSystemBState ψ) n T.typicalitySlack
  let rtyp : Type w :=
    State.TypicalSubspaceIndex (adhwFQSWSystemRState ψ) n T.typicalitySlack
  refine ⟨atyp, inferInstance, inferInstance,
    btyp, inferInstance, inferInstance,
    rtyp, inferInstance, inferInstance, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [atyp] using
      State.card_typicalSubspaceIndex
        (adhwFQSWSystemAState ψ) n T.typicalitySlack
  · let E : btyp ≃ State.TypicalSubspaceIndex
        (adhwFQSWSystemBState ψ) n T.typicalitySlack := Equiv.refl btyp
    let supportIsometry : ReferenceIsometry btyp (TensorPower b n) :=
      adhwFQSWTypicalSupportIsometryOfEquiv
        (adhwFQSWSystemBState ψ) n T.typicalitySlack E
    have hcardB :
        (Fintype.card btyp : ℝ) =
          (adhwFQSWSystemBState ψ).typicalSubspaceDimension n T.typicalitySlack := by
      simpa [btyp] using
        State.card_typicalSubspaceIndex
          (adhwFQSWSystemBState ψ) n T.typicalitySlack
    have hrangeB :
        supportIsometry.matrix * Matrix.conjTranspose supportIsometry.matrix =
          (adhwFQSWSystemBState ψ).typicalSubspaceProjector n T.typicalitySlack := by
      simpa [btyp, E, supportIsometry] using
        adhwFQSWTypicalSupportIsometryOfEquiv_range_projector
          (adhwFQSWSystemBState ψ) n T.typicalitySlack E
    exact ⟨⟨hcardB, supportIsometry, hrangeB⟩⟩
  · let E : rtyp ≃ State.TypicalSubspaceIndex
        (adhwFQSWSystemRState ψ) n T.typicalitySlack := Equiv.refl rtyp
    let supportIsometry : ReferenceIsometry rtyp (TensorPower r n) :=
      adhwFQSWTypicalSupportIsometryOfEquiv
        (adhwFQSWSystemRState ψ) n T.typicalitySlack E
    have hcardR :
        (Fintype.card rtyp : ℝ) =
          (adhwFQSWSystemRState ψ).typicalSubspaceDimension n T.typicalitySlack := by
      simpa [rtyp] using
        State.card_typicalSubspaceIndex
          (adhwFQSWSystemRState ψ) n T.typicalitySlack
    have hrangeR :
        supportIsometry.matrix * Matrix.conjTranspose supportIsometry.matrix =
          (adhwFQSWSystemRState ψ).typicalSubspaceProjector n T.typicalitySlack := by
      simpa [rtyp, E, supportIsometry] using
        adhwFQSWTypicalSupportIsometryOfEquiv_range_projector
          (adhwFQSWSystemRState ψ) n T.typicalitySlack E
    exact ⟨⟨hcardR, supportIsometry, hrangeR⟩⟩

/-- The true Alice typical support fits inside the padded `A₁ × A₂` register
once `A₁` meets the communication lower target and `A₂` meets the balanced
padding lower target. -/
private theorem adhwFQSWIid_atyp_card_le_padded_of_bounds
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    {atyp : Type p} {q : Type x} {e : Type y}
    [Fintype atyp] [Fintype q] [Fintype e]
    (hatypDim :
      (Fintype.card atyp : ℝ) =
        (adhwFQSWSystemAState ψ).typicalSubspaceDimension n T.typicalitySlack)
    (R : ADHWFQSWIidBalancedRateChoice ψ n δ q e) :
    Fintype.card atyp ≤ Fintype.card (Prod q e) := by
  have hA_upper :
      (Fintype.card atyp : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δ)) := by
    calc
      (Fintype.card atyp : ℝ) =
          (adhwFQSWSystemAState ψ).typicalSubspaceDimension n T.typicalitySlack := hatypDim
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δ)) := T.rankA_upper
  have hexp :
      ((n : ℝ) * (adhwFQSWEntropyA ψ + δ)) =
        adhwFQSWIidCommunicationLogTarget ψ n δ +
          ((n : ℝ) * (ψ.fqswEbitYieldRate - δ)) := by
    unfold adhwFQSWIidCommunicationLogTarget PureVector.fqswCommunicationRate
      PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    ring
  have hproduct_lower :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ *
          (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswEbitYieldRate - δ)) ≤
        (Fintype.card q : ℝ) * (Fintype.card e : ℝ) := by
    exact
      mul_le_mul
        R.rateChoice.communication_card_lower
        R.ebit_card_lower_for_padding
        (by positivity)
        (by positivity)
  have hreal :
      (Fintype.card atyp : ℝ) ≤ (Fintype.card (Prod q e) : ℝ) := by
    calc
      (Fintype.card atyp : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δ)) := hA_upper
      _ =
          (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ *
            (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswEbitYieldRate - δ)) := by
              rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (Fintype.card q : ℝ) * (Fintype.card e : ℝ) := hproduct_lower
      _ = (Fintype.card (Prod q e) : ℝ) := by
            norm_num [Fintype.card_prod]
  exact_mod_cast hreal

/-- Mixed-slack version of the padded Alice cardinality bound.  The typical
projectors use `δtyp`, while the finite `q/e` registers use `δrate`; the
rank window transfers as soon as `δtyp ≤ δrate`. -/
theorem adhwFQSWIid_atyp_card_le_padded_of_mixed_bounds
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε)
    {atyp : Type p} {q : Type x} {e : Type y}
    [Fintype atyp] [Fintype q] [Fintype e]
    (hatypDim :
      (Fintype.card atyp : ℝ) =
        (adhwFQSWSystemAState ψ).typicalSubspaceDimension n T.typicalitySlack)
    (R : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (hδtyp_le_rate : δtyp ≤ δrate) :
    Fintype.card atyp ≤ Fintype.card (Prod q e) := by
  have hA_upper_typ :
      (Fintype.card atyp : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δtyp)) := by
    calc
      (Fintype.card atyp : ℝ) =
          (adhwFQSWSystemAState ψ).typicalSubspaceDimension n T.typicalitySlack := hatypDim
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δtyp)) := T.rankA_upper
  have hA_upper :
      (Fintype.card atyp : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δrate)) := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hexp :
        (n : ℝ) * (adhwFQSWEntropyA ψ + δtyp) ≤
          (n : ℝ) * (adhwFQSWEntropyA ψ + δrate) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hn
    exact hA_upper_typ.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp)
  have hexp :
      ((n : ℝ) * (adhwFQSWEntropyA ψ + δrate)) =
        adhwFQSWIidCommunicationLogTarget ψ n δrate +
          ((n : ℝ) * (ψ.fqswEbitYieldRate - δrate)) := by
    unfold adhwFQSWIidCommunicationLogTarget PureVector.fqswCommunicationRate
      PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    ring
  have hproduct_lower :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δrate *
          (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswEbitYieldRate - δrate)) ≤
        (Fintype.card q : ℝ) * (Fintype.card e : ℝ) := by
    exact
      mul_le_mul
        R.rateChoice.communication_card_lower
        R.ebit_card_lower_for_padding
        (by positivity)
        (by positivity)
  have hreal :
      (Fintype.card atyp : ℝ) ≤ (Fintype.card (Prod q e) : ℝ) := by
    calc
      (Fintype.card atyp : ℝ) ≤
          (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δrate)) := hA_upper
      _ =
          (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δrate *
            (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswEbitYieldRate - δrate)) := by
              rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (Fintype.card q : ℝ) * (Fintype.card e : ℝ) := hproduct_lower
      _ = (Fintype.card (Prod q e) : ℝ) := by
            norm_num [Fintype.card_prod]
  exact_mod_cast hreal

/-- The balanced `A₂` upper window and the existing `A₁` lower target imply
the active ADHW target/reference finite-cardinality side condition. -/
private theorem adhwFQSWIid_target_ref_card_le_of_bounds
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    {btyp : Type u1} {rtyp : Type v1} {q : Type x} {e : Type y}
    [Fintype btyp] [DecidableEq btyp] [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [Fintype e]
    (hbtyp : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (hrtyp : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp)
    (R : ADHWFQSWIidBalancedRateChoice ψ n δ q e) :
    Fintype.card (Prod e rtyp) ≤ Fintype.card (Prod q btyp) := by
  have hleft_upper :
      (Fintype.card (Prod e rtyp) : ℝ) ≤
        (2 : ℝ) ^ (((n : ℝ) * ψ.fqswEbitYieldRate) +
          ((n : ℝ) * (adhwFQSWEntropyR ψ + δ))) := by
    have hrtyp_upper :
        (Fintype.card rtyp : ℝ) ≤
          (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δ)) := by
      calc
        (Fintype.card rtyp : ℝ) =
            (adhwFQSWSystemRState ψ).typicalSubspaceDimension n T.typicalitySlack :=
              hrtyp.card_eq_projector_rank
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δ)) := T.rankR_upper
    calc
      (Fintype.card (Prod e rtyp) : ℝ) =
          (Fintype.card e : ℝ) * (Fintype.card rtyp : ℝ) := by
            norm_num [Fintype.card_prod]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * ψ.fqswEbitYieldRate) *
            (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δ)) := by
              exact
                mul_le_mul
                  R.ebit_card_upper_for_target
                  hrtyp_upper
                  (by positivity)
                  (by positivity)
      _ = (2 : ℝ) ^ (((n : ℝ) * ψ.fqswEbitYieldRate) +
            ((n : ℝ) * (adhwFQSWEntropyR ψ + δ))) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hright_lower :
      (2 : ℝ) ^ (adhwFQSWIidCommunicationLogTarget ψ n δ +
          ((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) ≤
        (Fintype.card (Prod q btyp) : ℝ) := by
    have hbtyp_lower :
        (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δ)) ≤
          (Fintype.card btyp : ℝ) := by
      calc
        (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δ)) ≤
            (adhwFQSWSystemBState ψ).typicalSubspaceDimension n T.typicalitySlack := T.rankB_lower
        _ = (Fintype.card btyp : ℝ) := by
            rw [hbtyp.card_eq_projector_rank]
    calc
      (2 : ℝ) ^ (adhwFQSWIidCommunicationLogTarget ψ n δ +
          ((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) =
          (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ *
            (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δ)) := by
              rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (Fintype.card q : ℝ) * (Fintype.card btyp : ℝ) := by
            exact
              mul_le_mul
                R.rateChoice.communication_card_lower
                hbtyp_lower
                (by positivity)
                (by positivity)
      _ = (Fintype.card (Prod q btyp) : ℝ) := by
            norm_num [Fintype.card_prod]
  have hexp :
      ((n : ℝ) * ψ.fqswEbitYieldRate) +
          ((n : ℝ) * (adhwFQSWEntropyR ψ + δ)) =
        adhwFQSWIidCommunicationLogTarget ψ n δ +
          ((n : ℝ) * (adhwFQSWEntropyB ψ - δ)) := by
    unfold adhwFQSWIidCommunicationLogTarget PureVector.fqswCommunicationRate
      PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    ring
  have hreal :
      (Fintype.card (Prod e rtyp) : ℝ) ≤ (Fintype.card (Prod q btyp) : ℝ) := by
    calc
      (Fintype.card (Prod e rtyp) : ℝ) ≤
          (2 : ℝ) ^ (((n : ℝ) * ψ.fqswEbitYieldRate) +
            ((n : ℝ) * (adhwFQSWEntropyR ψ + δ))) := hleft_upper
      _ = (2 : ℝ) ^ (adhwFQSWIidCommunicationLogTarget ψ n δ +
            ((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by rw [hexp]
      _ ≤ (Fintype.card (Prod q btyp) : ℝ) := hright_lower
  exact_mod_cast hreal

/-- Mixed-slack version of the active `B^typ R^typ` cardinality side
condition.  The `B`/`R` typical ranks use `δtyp`, while `A₁` and `A₂` use the
finite register slack `δrate`. -/
theorem adhwFQSWIid_target_ref_card_le_of_mixed_bounds
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε)
    {btyp : Type u1} {rtyp : Type v1} {q : Type x} {e : Type y}
    [Fintype btyp] [DecidableEq btyp] [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [Fintype e]
    (hbtyp : ADHWFQSWIidTypicalBobRegister ψ n δtyp ε T btyp)
    (hrtyp : ADHWFQSWIidTypicalRefRegister ψ n δtyp ε T rtyp)
    (R : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (hδtyp_le_rate : δtyp ≤ δrate) :
    Fintype.card (Prod e rtyp) ≤ Fintype.card (Prod q btyp) := by
  have hleft_upper :
      (Fintype.card (Prod e rtyp) : ℝ) ≤
        (2 : ℝ) ^ (((n : ℝ) * ψ.fqswEbitYieldRate) +
          ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp))) := by
    have hrtyp_upper :
        (Fintype.card rtyp : ℝ) ≤
          (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp)) := by
      calc
        (Fintype.card rtyp : ℝ) =
            (adhwFQSWSystemRState ψ).typicalSubspaceDimension n T.typicalitySlack :=
              hrtyp.card_eq_projector_rank
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp)) := T.rankR_upper
    calc
      (Fintype.card (Prod e rtyp) : ℝ) =
          (Fintype.card e : ℝ) * (Fintype.card rtyp : ℝ) := by
            norm_num [Fintype.card_prod]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * ψ.fqswEbitYieldRate) *
            (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp)) := by
              exact
                mul_le_mul
                  R.ebit_card_upper_for_target
                  hrtyp_upper
                  (by positivity)
                  (by positivity)
      _ = (2 : ℝ) ^ (((n : ℝ) * ψ.fqswEbitYieldRate) +
            ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp))) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hright_lower :
      (2 : ℝ) ^ (adhwFQSWIidCommunicationLogTarget ψ n δrate +
          ((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp))) ≤
        (Fintype.card (Prod q btyp) : ℝ) := by
    have hbtyp_lower :
        (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp)) ≤
          (Fintype.card btyp : ℝ) := by
      calc
        (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp)) ≤
            (adhwFQSWSystemBState ψ).typicalSubspaceDimension n T.typicalitySlack := T.rankB_lower
        _ = (Fintype.card btyp : ℝ) := by
            rw [hbtyp.card_eq_projector_rank]
    calc
      (2 : ℝ) ^ (adhwFQSWIidCommunicationLogTarget ψ n δrate +
          ((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp))) =
          (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δrate *
            (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp)) := by
              rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (Fintype.card q : ℝ) * (Fintype.card btyp : ℝ) := by
            exact
              mul_le_mul
                R.rateChoice.communication_card_lower
                hbtyp_lower
                (by positivity)
                (by positivity)
      _ = (Fintype.card (Prod q btyp) : ℝ) := by
            norm_num [Fintype.card_prod]
  have hexp_le :
      ((n : ℝ) * ψ.fqswEbitYieldRate) +
          ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp)) ≤
        adhwFQSWIidCommunicationLogTarget ψ n δrate +
          ((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp)) := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    unfold adhwFQSWIidCommunicationLogTarget PureVector.fqswCommunicationRate
      PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    nlinarith
  have hreal :
      (Fintype.card (Prod e rtyp) : ℝ) ≤ (Fintype.card (Prod q btyp) : ℝ) := by
    calc
      (Fintype.card (Prod e rtyp) : ℝ) ≤
          (2 : ℝ) ^ (((n : ℝ) * ψ.fqswEbitYieldRate) +
            ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp))) := hleft_upper
      _ ≤ (2 : ℝ) ^ (adhwFQSWIidCommunicationLogTarget ψ n δrate +
            ((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_le
      _ ≤ (Fintype.card (Prod q btyp) : ℝ) := hright_lower
  exact_mod_cast hreal

/-- Cardinality side conditions for the ADHW i.i.d. one-shot invocation on the
padded Alice register `A₁ × A₂ = q × e`, while `atyp` remains the true typical
Alice support. -/
structure ADHWFQSWIidOneShotCardinalitySideConditions
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1) (q : Type x) (e : Type y)
    [Fintype atyp] [Fintype btyp] [Fintype rtyp] [Fintype q] [Fintype e] where
  target_ref_card_le :
    Fintype.card (Prod e rtyp) <= Fintype.card (Prod q btyp)
  padded_bob_ref_card_le :
    Fintype.card (Prod q btyp) <=
      Fintype.card (Prod (Prod (Prod q e) btyp) e)

/-- Package the rounded `q`/`e` choice with the source-shaped cardinality
inequalities needed to build the padded embedding and one-shot side
conditions. -/
structure ADHWFQSWIidBalancedCardinalityChoice
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] where
  balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δ q e
  atyp_card_le_padded :
    Fintype.card atyp <= Fintype.card (Prod q e)
  target_ref_card_le :
    Fintype.card (Prod e rtyp) <= Fintype.card (Prod q btyp)

namespace ADHWFQSWIidBalancedCardinalityChoice

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ : ℝ}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e]

/-- Compatibility projection for older code that only needs the rounded
finite-register rate choice. -/
theorem rateChoice
    (B : ADHWFQSWIidBalancedCardinalityChoice ψ n δ atyp btyp rtyp q e) :
    ADHWFQSWIidRateChoice ψ n δ q e :=
  B.balancedRateChoice.rateChoice

end ADHWFQSWIidBalancedCardinalityChoice

/-- Build the balanced finite-cardinality choice record from the rounded rate
choice plus the padded-embedding and target/reference inequalities. -/
theorem exists_adhwFQSWIidBalancedCardinalityChoice
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1) (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δ q e)
    (hatyp : Fintype.card atyp <= Fintype.card (Prod q e))
    (htarget : Fintype.card (Prod e rtyp) <= Fintype.card (Prod q btyp)) :
    Nonempty (ADHWFQSWIidBalancedCardinalityChoice ψ n δ atyp btyp rtyp q e) :=
  ⟨{ balancedRateChoice := balancedRateChoice
     atyp_card_le_padded := hatyp
     target_ref_card_le := htarget }⟩

/-- Build the mixed-slack finite-cardinality choice record from simultaneous
typical support data at `δtyp` and balanced finite-register data at `δrate`. -/
theorem exists_adhwFQSWIidBalancedCardinalityChoice_mixed
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δtyp δrate ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1) (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (hatypDim :
      (Fintype.card atyp : ℝ) =
        (adhwFQSWSystemAState ψ).typicalSubspaceDimension n T.typicalitySlack)
    (Btyp : ADHWFQSWIidTypicalBobRegister ψ n δtyp ε T btyp)
    (Rtyp : ADHWFQSWIidTypicalRefRegister ψ n δtyp ε T rtyp)
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (hδtyp_le_rate : δtyp ≤ δrate) :
    Nonempty (ADHWFQSWIidBalancedCardinalityChoice ψ n δrate atyp btyp rtyp q e) := by
  have hatyp :
      Fintype.card atyp ≤ Fintype.card (Prod q e) :=
    adhwFQSWIid_atyp_card_le_padded_of_mixed_bounds
      T hatypDim balancedRateChoice hδtyp_le_rate
  have htarget :
      Fintype.card (Prod e rtyp) ≤ Fintype.card (Prod q btyp) :=
    adhwFQSWIid_target_ref_card_le_of_mixed_bounds
      T Btyp Rtyp balancedRateChoice hδtyp_le_rate
  exact
    exists_adhwFQSWIidBalancedCardinalityChoice
      ψ n δrate atyp btyp rtyp q e balancedRateChoice hatyp htarget

/-- Package the active `B`/`R` cardinality inequality together with the padded
`A₁ B^typ R^typ` side condition used by the one-shot theorem. -/
theorem exists_adhwFQSWIidOneShotCardinalitySideConditions
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1) (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (htarget :
      Fintype.card (Prod e rtyp) <= Fintype.card (Prod q btyp))
    : Nonempty (ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e) := by
  have he_pos : 0 < Fintype.card e := Fintype.card_pos_iff.mpr inferInstance
  have hone_le_ee : 1 ≤ Fintype.card e * Fintype.card e := by
    nlinarith
  have hpadded :
      Fintype.card (Prod q btyp) <=
        Fintype.card (Prod (Prod (Prod q e) btyp) e) := by
    simpa [Fintype.card_prod, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left (Fintype.card q * Fintype.card btyp) hone_le_ee
  exact
    ⟨{ target_ref_card_le := htarget
       padded_bob_ref_card_le := hpadded }⟩

/-- A balanced-cardinality choice supplies the existing padded embedding and
one-shot side-condition records once the `A^typ` dimension identity is fixed. -/
theorem ADHWFQSWIidBalancedCardinalityChoice.to_padded_and_sideConditions
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ δtyp : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (B : ADHWFQSWIidBalancedCardinalityChoice ψ n δ atyp btyp rtyp q e)
    (hatypDim :
      (Fintype.card atyp : ℝ) =
        (adhwFQSWSystemAState ψ).typicalSubspaceDimension n δtyp) :
    ∃ _ : ADHWFQSWPaddedAtypEmbedding ψ n δtyp atyp q e,
      Nonempty (ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e) := by
  obtain ⟨P⟩ :=
    exists_adhwFQSWPaddedAtypEmbedding
      ψ n δtyp atyp q e hatypDim B.atyp_card_le_padded
  refine ⟨P, ?_⟩
  exact
    exists_adhwFQSWIidOneShotCardinalitySideConditions
      atyp btyp rtyp q e B.target_ref_card_le

/-- The padded compressed i.i.d. source reuses the existing ADHW one-shot
Schur/HS/Haar route to assemble the source-component one-shot bound record on
the active `A₁ × A₂ = q × e` split. -/
theorem exists_adhwFQSWIidCompressedOneShotBound
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (compressedOneShotSource :
      PureVector (Prod (Prod (Prod q e) btyp) rtyp))
    (S : ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e) :
    Nonempty
      (ADHWFQSWOneShotBound
        compressedOneShotSource q e (Equiv.refl (Prod q e))) := by
  let split : Prod q e ≃ Prod q e := Equiv.refl (Prod q e)
  obtain ⟨D⟩ :=
    exists_adhwFQSWTraceNormDecouplingBound_of_hilbertSchmidtAverage
      compressedOneShotSource split
      (adhwFQSWProductDecouplingHilbertSchmidtAverage_le compressedOneShotSource split)
  obtain ⟨M⟩ :=
    exists_adhwFQSWMaxMixedA2Estimate_of_hilbertSchmidtAverage
      compressedOneShotSource split
      (adhwFQSWMaxMixedA2HilbertSchmidtAverage_le compressedOneShotSource split)
  obtain ⟨H, _hD, _hM⟩ :=
    exists_adhwFQSWOneShotBound_of_source_component_records
      compressedOneShotSource split D M S.target_ref_card_le S.padded_bob_ref_card_le
  exact ⟨H⟩

/-- Simultaneous typical projectors, finite typical support registers, and a
balanced rounded `A₁`/`A₂` choice eventually assemble the ADHW cardinality
package needed for the finite one-shot invocation. -/
theorem exists_adhwFQSWIidBalancedCardinalityChoice_eventually
    (ψ : PureVector (Prod (Prod a b) r)) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε),
      ∃ (atyp : Type u), ∃ (_ : Fintype atyp), ∃ (_ : DecidableEq atyp),
        ∃ (btyp : Type v), ∃ (_ : Fintype btyp), ∃ (_ : DecidableEq btyp),
          ∃ (rtyp : Type w), ∃ (_ : Fintype rtyp), ∃ (_ : DecidableEq rtyp),
            ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
              ∃ (_ : Nonempty q),
                ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e),
                  ∃ (_ : Nonempty e),
                    (Fintype.card atyp : ℝ) =
                      (adhwFQSWSystemAState ψ).typicalSubspaceDimension
                        n T.typicalitySlack ∧
                    Nonempty (ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp) ∧
                    Nonempty (ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) ∧
                    Nonempty
                      (ADHWFQSWIidBalancedCardinalityChoice
                        ψ n δ atyp btyp rtyp q e) := by
  obtain ⟨NT, hT⟩ := exists_adhwFQSWSimultaneousTypicalProjectors ψ δ ε hδ hε
  obtain ⟨NR, hR⟩ := exists_adhwFQSWIidBalancedRateChoice_registers ψ hδ
  refine ⟨max NT NR, ?_⟩
  intro n hn
  have hnT : n ≥ NT := le_trans (Nat.le_max_left _ _) hn
  have hnR : n ≥ NR := le_trans (Nat.le_max_right _ _) hn
  obtain ⟨T⟩ := hT n hnT
  obtain ⟨q, hqF, hqD, hqN, e, heF, heD, heN, hbalancedRate⟩ := hR n hnR
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨R⟩ := hbalancedRate
  obtain ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
      rtyp, hrtypF, hrtypD, hatypDim, hbtypReg, hrtypReg⟩ :=
    exists_adhwFQSWIidTypicalSupportRegisters ψ n δ ε T
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  obtain ⟨Btyp⟩ := hbtypReg
  obtain ⟨Rtyp⟩ := hrtypReg
  have hatypCard :
      Fintype.card atyp ≤ Fintype.card (Prod q e) :=
    adhwFQSWIid_atyp_card_le_padded_of_bounds T hatypDim R
  have htarget :
      Fintype.card (Prod e rtyp) ≤ Fintype.card (Prod q btyp) :=
    adhwFQSWIid_target_ref_card_le_of_bounds T Btyp Rtyp R
  obtain ⟨B⟩ :=
    exists_adhwFQSWIidBalancedCardinalityChoice
      ψ n δ atyp btyp rtyp q e R hatypCard htarget
  refine ⟨T, atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
    rtyp, hrtypF, hrtypD, q, hqF, hqD, hqN, e, heF, heD, heN, ?_⟩
  exact ⟨hatypDim, ⟨Btyp⟩, ⟨Rtyp⟩, ⟨B⟩⟩

/-- Mixed-slack eventual assembly of simultaneous typical projectors, typical
support registers, balanced `q/e` registers, and the finite-cardinality choice.
The intended final source route instantiates `δtyp = δrate / 4`. -/
theorem exists_adhwFQSWIidBalancedCardinalityChoice_mixed_eventually
    (ψ : PureVector (Prod (Prod a b) r)) {δtyp δrate ε : ℝ}
    (hδtyp : 0 < δtyp) (hδrate : 0 < δrate) (hε : 0 < ε)
    (hδtyp_le_quarter : δtyp ≤ δrate / 4) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε),
      ∃ (atyp : Type u), ∃ (_ : Fintype atyp), ∃ (_ : DecidableEq atyp),
        ∃ (btyp : Type v), ∃ (_ : Fintype btyp), ∃ (_ : DecidableEq btyp),
          ∃ (rtyp : Type w), ∃ (_ : Fintype rtyp), ∃ (_ : DecidableEq rtyp),
            ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
              ∃ (_ : Nonempty q),
                ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e),
                  ∃ (_ : Nonempty e),
                    (Fintype.card atyp : ℝ) =
                      (adhwFQSWSystemAState ψ).typicalSubspaceDimension
                        n T.typicalitySlack ∧
                    Nonempty (ADHWFQSWIidTypicalBobRegister ψ n δtyp ε T btyp) ∧
                    Nonempty (ADHWFQSWIidTypicalRefRegister ψ n δtyp ε T rtyp) ∧
                    Nonempty (ADHWFQSWIidBalancedRateChoice ψ n δrate q e) ∧
                    Nonempty
                      (ADHWFQSWIidBalancedCardinalityChoice
                        ψ n δrate atyp btyp rtyp q e) := by
  obtain ⟨NT, hT⟩ :=
    exists_adhwFQSWSimultaneousTypicalProjectors ψ δtyp ε hδtyp hε
  obtain ⟨NR, hR⟩ := exists_adhwFQSWIidBalancedRateChoice_registers ψ hδrate
  refine ⟨max NT NR, ?_⟩
  intro n hn
  have hnT : n ≥ NT := le_trans (Nat.le_max_left _ _) hn
  have hnR : n ≥ NR := le_trans (Nat.le_max_right _ _) hn
  obtain ⟨T⟩ := hT n hnT
  obtain ⟨q, hqF, hqD, hqN, e, heF, heD, heN, hbalancedRate⟩ := hR n hnR
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨R⟩ := hbalancedRate
  obtain ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
      rtyp, hrtypF, hrtypD, hatypDim, hbtypReg, hrtypReg⟩ :=
    exists_adhwFQSWIidTypicalSupportRegisters ψ n δtyp ε T
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  obtain ⟨Btyp⟩ := hbtypReg
  obtain ⟨Rtyp⟩ := hrtypReg
  have hδtyp_le_rate : δtyp ≤ δrate := by
    have hquarter_le : δrate / 4 ≤ δrate := by nlinarith [hδrate.le]
    exact hδtyp_le_quarter.trans hquarter_le
  obtain ⟨B⟩ :=
    exists_adhwFQSWIidBalancedCardinalityChoice_mixed
      ψ n δtyp δrate ε T atyp btyp rtyp q e
      hatypDim Btyp Rtyp R hδtyp_le_rate
  refine ⟨T, atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
    rtyp, hrtypF, hrtypD, q, hqF, hqD, hqN, e, heF, heD, heN, ?_⟩
  exact ⟨hatypDim, ⟨Btyp⟩, ⟨Rtyp⟩, ⟨R⟩, ⟨B⟩⟩

end

end QIT
