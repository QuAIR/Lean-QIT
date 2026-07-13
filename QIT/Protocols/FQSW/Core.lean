/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.Holevo
public import QIT.States.Purification.ReferenceIsometry
public import QIT.Channels.Diamond

/-!
# FQSW core operational API

This file is a dependency-ordered leaf of `QIT.Protocols.FQSW`.  Declaration
names, namespaces, statements, and proof terms are preserved from the original
monolithic module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p u1 v1 w1

noncomputable section

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

namespace State

/-- Marginal state on `A × R` used by coherent state transfer/FQSW. -/
def coherentTransferReferenceState
    (ρ : State (Prod (Prod a b) r)) : State (Prod a r) where
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

/-- Reference mutual information `I(A;R)` for coherent state transfer/FQSW. -/
def coherentTransferReferenceMutualInformation
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  mutualInformation ρ.coherentTransferReferenceState

/-- Coherent state-transfer quantum communication rate `(1/2) I(A;R)`. -/
def coherentTransferRate (ρ : State (Prod (Prod a b) r)) : ℝ :=
  (1 / 2 : ℝ) * ρ.coherentTransferReferenceMutualInformation

end State

/-- The canonical equivalence adding a right unit tensor factor. -/
def fqswAppendRightUnitEquiv (α : Type u) : α ≃ Prod α PUnit.{u + 1} where
  toFun x := (x, PUnit.unit)
  invFun x := x.1
  left_inv := by intro x; rfl
  right_inv := by intro x; cases x; rfl

/-- Reindexing along the right-unit equivalence is the same state as tensoring
with the unit-system state. -/
theorem state_reindex_fqswAppendRightUnitEquiv_eq_prod_unit
    {α : Type u} [Fintype α] [DecidableEq α] (ρ : State α) :
    ρ.reindex (fqswAppendRightUnitEquiv α) =
      ρ.prod (State.unit : State PUnit.{u + 1}) := by
  apply State.ext
  ext i j
  simp [fqswAppendRightUnitEquiv, State.reindex, State.prod, State.unit,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

/-- Append a fixed right-hand state by first adjoining the unit system and then
preparing the target state on that factor. -/
def fqswAppendStateRight
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : State β) : Channel α (Prod α β) :=
  ((Channel.idChannel α).prod (Channel.prepare (fun _ : PUnit.{u + 1} => τ))).comp
    (Channel.reindex (fqswAppendRightUnitEquiv α))

/-- The append-state channel sends `ρ` to the product state `ρ ⊗ τ`. -/
theorem fqswAppendStateRight_applyState
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : State β) (ρ : State α) :
    (fqswAppendStateRight (α := α) τ).applyState ρ = ρ.prod τ := by
  unfold fqswAppendStateRight
  rw [Channel.applyState_comp, Channel.reindex_applyState]
  rw [state_reindex_fqswAppendRightUnitEquiv_eq_prod_unit]
  rw [Channel.applyState_prod]
  congr
  · apply State.ext
    change (Channel.idChannel α).map ρ.matrix = ρ.matrix
    simp [Channel.idChannel, MatrixMap.ofKraus]
  · apply State.ext
    ext i j
    simp [Channel.applyState, Channel.prepare_map, State.unit]

/-- Appending a fixed right-hand state is a channel, hence it cannot increase
normalized trace distance. -/
theorem fqswProdRight_normalizedTraceDistance_le
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : State α) (τ : State β) :
    (ρ.prod τ).normalizedTraceDistance (σ.prod τ) ≤
      ρ.normalizedTraceDistance σ := by
  let Φ : Channel α (Prod α β) := fqswAppendStateRight τ
  have hρ : Φ.applyState ρ = ρ.prod τ := by
    simpa [Φ] using fqswAppendStateRight_applyState (α := α) τ ρ
  have hσ : Φ.applyState σ = σ.prod τ := by
    simpa [Φ] using fqswAppendStateRight_applyState (α := α) τ σ
  have h := Channel.normalizedTraceDistance_applyState_le Φ ρ σ
  simpa [hρ, hσ] using h

/-- Appending a fixed right-hand state cannot increase the source trace-norm
distance between density matrices. -/
theorem fqswProdRight_traceDistance_le
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : State α) (τ : State β) :
    (ρ.prod τ).traceDistance (σ.prod τ) ≤ ρ.traceDistance σ := by
  have h := fqswProdRight_normalizedTraceDistance_le ρ σ τ
  unfold State.normalizedTraceDistance normalizedTraceDistance at h
  unfold State.traceDistance
  nlinarith

/-- The channel induced by an isometry on a finite system. -/
def fqswChannelOfReferenceIsometry
    {r₁ : Type u} {r₂ : Type v}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) : Channel r₁ r₂ where
  map := MatrixMap.ofReferenceIsometry V
  completelyPositive := MatrixMap.ofReferenceIsometry_isCompletelyPositive V
  tracePreserving := MatrixMap.ofReferenceIsometry_isTracePreserving V
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)

/-- Canonical maximally entangled pure vector associated to a finite basis
equivalence between the two ebit registers. -/
def maximallyEntangledPureVector (pairing : e ≃ et) : PureVector (Prod e et) where
  amp := fun x =>
    if pairing x.1 = x.2 then
      ((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹)
    else
      0
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace]
    have hcard_pos : 0 < (Fintype.card e : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hsqrt_ne : Real.sqrt (Fintype.card e : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 hcard_pos)
    calc
      (fun x : Prod e et =>
          (if pairing x.1 = x.2 then ((Real.sqrt (Fintype.card e : ℝ))⁻¹ : ℂ) else 0)) ⬝ᵥ
          (fun x : Prod e et =>
            star (if pairing x.1 = x.2 then
              ((Real.sqrt (Fintype.card e : ℝ))⁻¹ : ℂ) else 0)) =
          ∑ i : e, ∑ j : et,
            (if pairing i = j then
              (((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹) *
                (((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹))) else 0) := by
        simp [dotProduct, Fintype.sum_prod_type]
      _ = ∑ i : e,
            (((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹) *
              (((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single (pairing i)]
        · simp
        · intro j _ hj
          have hne : pairing i ≠ j := fun h => hj h.symm
          simp [hne]
        · simp
      _ = (Fintype.card e : ℂ) *
            (((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹) *
              (((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹))) := by
        simp
      _ = 1 := by
        have hsqrtC_ne : (Real.sqrt (Fintype.card e : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast hsqrt_ne
        field_simp [hsqrtC_ne]
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
        exact congrArg Complex.ofReal (Real.sq_sqrt hcard_pos.le).symm

/-- Regroup a left-associated tripartite source `(A × B) × R` so Alice's
system is the left factor. -/
def fqswSourceToAliceInputEquiv (a : Type u) (b : Type v) (r : Type w) :
    Prod (Prod a b) r ≃ Prod a (Prod b r) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup a left-associated tripartite source `(A × B) × R` as
`(A × R) × B`, exposing the subsystem complementary to Bob. -/
def fqswSourceToARBEquiv (a : Type u) (b : Type v) (r : Type w) :
    Prod (Prod a b) r ≃ Prod (Prod a r) b where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup Alice's output so Bob's input register `A₁ × B` is the left
factor and the untouched reference `R × A₂` is the right factor. -/
def fqswAliceOutputToBobInputEquiv
    (q : Type x) (e : Type y) (b : Type v) (r : Type w) :
    Prod (Prod q e) (Prod b r) ≃ Prod (Prod q b) (Prod r e) where
  toFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup Alice's one-shot output so the discarded `A₁B` side is separated
from the decoupled `A₂R` side used in ADHW fqsw.tex lines 580-841. -/
def fqswAliceOutputToA2REquiv
    (q : Type x) (e : Type y) (b : Type v) (r : Type w) :
    Prod (Prod q e) (Prod b r) ≃ Prod (Prod q b) (Prod e r) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Apply the source split `A ≃ A₁ × A₂` on the `A` side of the one-shot
`AR` marginal.  This explicit equivalence avoids universe inference issues
from using `Equiv.prodCongr` directly in the FQSW bridge lemmas. -/
def fqswARSplitEquiv (split : a ≃ Prod q e) :
    Prod a r ≃ Prod (Prod q e) r where
  toFun x := (split x.1, x.2)
  invFun x := (split.symm x.1, x.2)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- Regroup a split `AR` marginal from `(A₁ × A₂) × R` into
`A₁ × (A₂ × R)`, the order used by the ADHW decoupling marginal
`σ^{A₂R}` after tracing out `A₁`. -/
def fqswQERToA2REquiv (q : Type x) (e : Type y) (r : Type w) :
    Prod (Prod q e) r ≃ Prod q (Prod e r) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup Bob's output into the final FQSW comparison order:
transferred source against the distilled ebit. -/
def fqswBobOutputToFinalEquiv
    (a : Type u) (b : Type v) (et : Type z) (r : Type w) (e : Type y) :
    Prod (Prod (Prod a b) et) (Prod r e) ≃
      Prod (Prod (Prod a b) r) (Prod e et) where
  toFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e] [Nonempty e] [Fintype et] [DecidableEq et] in
@[simp]
theorem fqswBobOutputToFinalEquiv_apply
    (x : Prod (Prod (Prod a b) et) (Prod r e)) :
    fqswBobOutputToFinalEquiv a b et r e x =
      ((x.1.1, x.2.1), (x.2.2, x.1.2)) :=
  rfl

/-- Regroup the tensor power of a left-associated tripartite system as
`(A^n × B^n) × R^n`. -/
def fqswTensorPowerTripartiteEquiv (a : Type u) (b : Type v) (r : Type w)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] (n : ℕ) :
    TensorPower (Prod (Prod a b) r) n ≃
      Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n) :=
  (tensorPowerProdEquiv (Prod a b) r n).trans
    (Equiv.prodCongr (tensorPowerProdEquiv a b n) (Equiv.refl (TensorPower r n)))

/-- One-shot FQSW protocol data.  The final states are intentionally not
fields: they are computed from the source and the two source operations below. -/
structure FQSWOneShotProtocol (ψ : PureVector (Prod (Prod a b) r))
    (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  aliceIsometry : ReferenceIsometry a (Prod q e)
  bobIsometry : ReferenceIsometry (Prod q b) (Prod (Prod a b) et)
  ebitPairing : e ≃ et

namespace FQSWOneShotProtocol

variable {ψ : PureVector (Prod (Prod a b) r)}
variable (C : FQSWOneShotProtocol ψ q e et)

/-- Computed FQSW output for an explicit source state.  This is the mixed-state
counterpart of `outputPureVector`: Alice applies her isometry, the registers
are regrouped so `A₁B` is Bob's input, Bob applies his isometry, and the final
state is compared in the source order `ABR × A₂B~`. -/
def outputStateOfState (C : FQSWOneShotProtocol ψ q e et)
    (ρ : State (Prod (Prod a b) r)) :
    State (Prod (Prod (Prod a b) r) (Prod e et)) :=
  let ρA : State (Prod a (Prod b r)) :=
    ρ.reindex (fqswSourceToAliceInputEquiv a b r)
  let ρU : State (Prod (Prod q e) (Prod b r)) :=
    ((fqswChannelOfReferenceIsometry C.aliceIsometry).prod
      (Channel.idChannel (Prod b r))).applyState ρA
  let ρBobIn : State (Prod (Prod q b) (Prod r e)) :=
    ρU.reindex (fqswAliceOutputToBobInputEquiv q e b r)
  let ρV : State (Prod (Prod (Prod a b) et) (Prod r e)) :=
    ((fqswChannelOfReferenceIsometry C.bobIsometry).prod
      (Channel.idChannel (Prod r e))).applyState ρBobIn
  ρV.reindex (fqswBobOutputToFinalEquiv a b et r e)

/-- The pure output state obtained by applying Alice's isometry, transmitting
`A₁`, and applying Bob's isometry. -/
def outputPureVector :
    PureVector (Prod (Prod (Prod a b) r) (Prod e et)) :=
  let ψA : PureVector (Prod a (Prod b r)) :=
    ψ.reindex (fqswSourceToAliceInputEquiv a b r)
  let ψU : PureVector (Prod (Prod q e) (Prod b r)) :=
    C.aliceIsometry.applyPureVector ψA
  let ψBobIn : PureVector (Prod (Prod q b) (Prod r e)) :=
    ψU.reindex (fqswAliceOutputToBobInputEquiv q e b r)
  let ψV : PureVector (Prod (Prod (Prod a b) et) (Prod r e)) :=
    C.bobIsometry.applyPureVector ψBobIn
  ψV.reindex (fqswBobOutputToFinalEquiv a b et r e)

/-- Computed FQSW output state. -/
def outputState : State (Prod (Prod (Prod a b) r) (Prod e et)) :=
  C.outputPureVector.state

/-- Source-shaped target: transferred `ABR` source tensor a canonical ebit. -/
def targetState : State (Prod (Prod (Prod a b) r) (Prod e et)) :=
  ψ.state.prod (maximallyEntangledPureVector C.ebitPairing).state

/-- Normalized trace-distance protocol error, matching existing Lean protocol
conventions. -/
def normalizedError : ℝ :=
  C.outputState.normalizedTraceDistance C.targetState

/-- Source trace-norm error `||ρ_out - ρ_target||₁`. -/
def traceNormError : ℝ :=
  traceDistance C.outputState.matrix C.targetState.matrix

/-- Source trace-norm error against `C.targetState` for an explicit source
state argument. -/
def traceNormErrorOfState (C : FQSWOneShotProtocol ψ q e et)
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  traceDistance (C.outputStateOfState ρ).matrix C.targetState.matrix

/-- Number of qubits communicated in the one-shot protocol. -/
def communicationCost (_C : FQSWOneShotProtocol ψ q e et) : ℝ :=
  log2 (Fintype.card q : ℝ)

/-- Number of ebits distilled in the one-shot protocol. -/
def ebitYield (_C : FQSWOneShotProtocol ψ q e et) : ℝ :=
  log2 (Fintype.card e : ℝ)

theorem normalizedError_nonneg : 0 ≤ C.normalizedError :=
  State.normalizedTraceDistance_nonneg _ _

theorem traceNormError_nonneg : 0 ≤ C.traceNormError :=
  traceDistance_nonneg _ _

theorem normalizedError_eq_half_traceNormError :
    C.normalizedError = (1 / 2 : ℝ) * C.traceNormError := by
  rfl

end FQSWOneShotProtocol

/-- Block FQSW protocol, obtained by applying the one-shot semantics to the
grouped IID source `ψ^{⊗n}`. -/
structure FQSWBlockProtocol (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  oneShot :
    FQSWOneShotProtocol
      ((ψ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n))
      q e et

namespace FQSWBlockProtocol

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ}
variable (C : FQSWBlockProtocol ψ n q e et)

def outputState :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  C.oneShot.outputState

def targetState :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  C.oneShot.targetState

def normalizedError : ℝ :=
  C.oneShot.normalizedError

def traceNormError : ℝ :=
  C.oneShot.traceNormError

def outputStateOfState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  FQSWOneShotProtocol.outputStateOfState C.oneShot
    ((ρ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n))

def traceNormErrorOfState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  traceDistance (C.outputStateOfState ρ).matrix C.targetState.matrix

def communicationRate (_C : FQSWBlockProtocol ψ n q e et) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card q : ℝ) / (n : ℝ)

def ebitYieldRate (_C : FQSWBlockProtocol ψ n q e et) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card e : ℝ) / (n : ℝ)

theorem normalizedError_nonneg : 0 ≤ C.normalizedError :=
  C.oneShot.normalizedError_nonneg

theorem traceNormError_nonneg : 0 ≤ C.traceNormError :=
  C.oneShot.traceNormError_nonneg

end FQSWBlockProtocol

/-- A non-operational rate/error certificate retained for the existing IID
source-route calculation.  Unlike `FQSWBlockProtocol`, it does not contain
Alice and Bob operations or a computed output state. -/
structure FQSWRateErrorCertificate
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (q : Type x) (e : Type y) where
  traceNormError : ℝ

namespace FQSWRateErrorCertificate

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ}

/-- Communication rate recorded by an FQSW rate/error certificate. -/
def communicationRate (_S : FQSWRateErrorCertificate ψ n q e) [Fintype q] : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card q : ℝ) / (n : ℝ)

/-- Ebit-yield rate recorded by an FQSW rate/error certificate. -/
def ebitYieldRate (_S : FQSWRateErrorCertificate ψ n q e) [Fintype e] : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card e : ℝ) / (n : ℝ)

/-- Normalized error corresponding to the stored trace-norm error. -/
def normalizedError (S : FQSWRateErrorCertificate ψ n q e) : ℝ :=
  (1 / 2 : ℝ) * S.traceNormError

end FQSWRateErrorCertificate

/-- A compressed-block FQSW protocol scaffold that records Alice's compression
and preprocessing layer before the one-shot FQSW semantics are invoked. -/
structure FQSWCompressedBlockProtocol (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  aliceCompression : ReferenceIsometry (TensorPower a n) (TensorPower a n)
  alicePreprocessing :
    State (Prod (Prod a b) r) → State (Prod (Prod a b) r)
  oneShot : FQSWBlockProtocol ψ n q e et

namespace FQSWCompressedBlockProtocol

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ}
variable (C : FQSWCompressedBlockProtocol ψ n q e et)

/-- Output state for an externally supplied source state.  Alice's
preprocessing is tensor-powered to the block source, Alice's compression
isometry is applied to the block `A^n` register, and the resulting compressed
source is passed through the block one-shot FQSW protocol. -/
def outputStateOfState (C : FQSWCompressedBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  let ρpre := C.alicePreprocessing ρ
  let ρblock : State
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    (ρpre.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n)
  let ρA : State (Prod (TensorPower a n) (Prod (TensorPower b n) (TensorPower r n))) :=
    ρblock.reindex
      (fqswSourceToAliceInputEquiv (TensorPower a n) (TensorPower b n) (TensorPower r n))
  let ρCompressed : State
      (Prod (TensorPower a n) (Prod (TensorPower b n) (TensorPower r n))) :=
    ((fqswChannelOfReferenceIsometry C.aliceCompression).prod
      (Channel.idChannel (Prod (TensorPower b n) (TensorPower r n)))).applyState ρA
  let ρcompressedSource : State
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    ρCompressed.reindex
      (fqswSourceToAliceInputEquiv
        (TensorPower a n) (TensorPower b n) (TensorPower r n)).symm
  FQSWOneShotProtocol.outputStateOfState C.oneShot.oneShot ρcompressedSource

/-- Source-shaped trace-norm error for the compressed block semantics. -/
def traceNormErrorOfState (C : FQSWCompressedBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  traceDistance (C.outputStateOfState ρ).matrix C.oneShot.targetState.matrix

/-- Source-shaped normalized trace-distance error for the compressed block
semantics. -/
def normalizedErrorOfState (C : FQSWCompressedBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  (C.outputStateOfState ρ).normalizedTraceDistance C.oneShot.targetState

theorem normalizedErrorOfState_eq_half_traceNormErrorOfState
    (C : FQSWCompressedBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) :
    C.normalizedErrorOfState ρ =
      (1 / 2 : ℝ) * C.traceNormErrorOfState ρ := by
  rfl

end FQSWCompressedBlockProtocol



namespace PureVector

variable (ψ : PureVector (Prod (Prod a b) r))

/-- FQSW communication rate `(1/2) I(A;R)_ψ`. -/
def fqswCommunicationRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.coherentTransferReferenceState

/-- FQSW ebit-yield rate `(1/2) I(A;B)_ψ`. -/
def fqswEbitYieldRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.marginalA

/-- The asymptotic rate/error certificate reached by the current IID scalar
route.  This predicate is intentionally not the operational FQSW
achievability definition because its witness does not contain a protocol. -/
def HasAsymptoticFQSWRateErrorCertificates : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ εerr : ℝ, 0 < εerr →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
          ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
            ∃ S : FQSWRateErrorCertificate ψ n q e,
              S.communicationRate ≤ ψ.fqswCommunicationRate + δ ∧
                ψ.fqswEbitYieldRate - δ ≤ S.ebitYieldRate ∧
                  S.normalizedError ≤ εerr

/-- Operational FQSW achievability with computed protocols: for every positive
rate slack and error tolerance, all sufficiently large block lengths have an
`FQSWBlockProtocol` whose communication rate is at most `1/2 I(A;R) + δ`,
whose ebit yield is at least `1/2 I(A;B) - δ`, and whose computed normalized
trace-distance error is at most `ε`. -/
def IsAchievableFQSW : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ εerr : ℝ, 0 < εerr →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
          ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
            ∃ (et : Type z), ∃ (_ : Fintype et), ∃ (_ : DecidableEq et),
              ∃ C : FQSWBlockProtocol ψ n q e et,
                C.communicationRate ≤ ψ.fqswCommunicationRate + δ ∧
                  ψ.fqswEbitYieldRate - δ ≤ C.ebitYieldRate ∧
                    C.normalizedError ≤ εerr

end PureVector

end

end QIT
