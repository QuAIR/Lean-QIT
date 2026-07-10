/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.Decoupling
public import QIT.Protocols.StateMerging
public import QIT.Asymptotic.AEP
public import QIT.Coding.Source.SchumacherDirect
public import QIT.States.Geometry.FuchsVdG
public import QIT.States.Purification.Schatten
public import QIT.States.Purification.ReferenceIsometry
public import QIT.Channels.Diamond

/-!
# Fully quantum Slepian--Wolf operational semantics

This module records the source-shaped operational semantics for the FQSW
protocol route of Abeyesinghe--Devetak--Hayden--Winter.  The protocol data are
Alice's isometry, Bob's isometry, and the ebit pairing; output and target states
are computed from those data rather than supplied as free fields.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p u1 v1 w1

noncomputable section

local instance fqswCMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

private instance fqswUnitaryHaarMeasure_isMulRightInvariant {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    MeasureTheory.Measure.IsMulRightInvariant (unitaryHaarMeasure (a := ι)) := by
  haveI : SecondCountableTopology (Matrix.unitaryGroup ι ℂ) := by
    haveI : SecondCountableTopology (Matrix ι ι ℂ) := by
      change SecondCountableTopology (ι → ι → ℂ)
      infer_instance
    change SecondCountableTopology
      ({x // x ∈ (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ))})
    infer_instance
  refine ⟨?_⟩
  intro g
  let K0 : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ) := ⊤
  have hmass : (MeasureTheory.Measure.map (fun U : Matrix.unitaryGroup ι ℂ => U * g)
        (unitaryHaarMeasure (a := ι))) K0 = 1 := by
    rw [MeasureTheory.Measure.map_apply]
    · change (unitaryHaarMeasure (a := ι)) Set.univ = 1
      exact unitaryHaarMeasure_univ (a := ι)
    · exact continuous_mul_const g |>.measurable
    · exact K0.isCompact.measurableSet
  have hhaar := (MeasureTheory.Measure.haarMeasure_eq_iff K0
    (MeasureTheory.Measure.map (fun U : Matrix.unitaryGroup ι ℂ => U * g)
      (unitaryHaarMeasure (a := ι)))).2 hmass
  simpa [unitaryHaarMeasure, K0] using hhaar.symm

private instance fqswUnitaryHaarMeasure_isInvInvariant {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    MeasureTheory.Measure.IsInvInvariant (unitaryHaarMeasure (a := ι)) := by
  haveI : SecondCountableTopology (Matrix.unitaryGroup ι ℂ) := by
    haveI : SecondCountableTopology (Matrix ι ι ℂ) := by
      change SecondCountableTopology (ι → ι → ℂ)
      infer_instance
    change SecondCountableTopology
      ({x // x ∈ (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ))})
    infer_instance
  refine ⟨?_⟩
  let K0 : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ) := ⊤
  have hmass : (unitaryHaarMeasure (a := ι)).inv K0 = 1 := by
    rw [MeasureTheory.Measure.inv_def, MeasureTheory.Measure.map_apply]
    · change (unitaryHaarMeasure (a := ι)) Set.univ = 1
      exact unitaryHaarMeasure_univ (a := ι)
    · exact measurable_inv
    · exact K0.isCompact.measurableSet
  have hhaar := (MeasureTheory.Measure.haarMeasure_eq_iff K0
    (unitaryHaarMeasure (a := ι)).inv).2 hmass
  simpa [unitaryHaarMeasure, K0] using hhaar.symm

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

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

/-- Public FQSW operational surface: the asymptotic predicate only needs the
visible communication register, ebit register, and trace-norm error. -/
structure FQSWOperationalSurface
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (q : Type x) (e : Type y) where
  traceNormError : ℝ

namespace FQSWOperationalSurface

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ}

/-- Communication rate of the public FQSW surface. -/
def communicationRate (_S : FQSWOperationalSurface ψ n q e) [Fintype q] : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card q : ℝ) / (n : ℝ)

/-- Ebit-yield rate of the public FQSW surface. -/
def ebitYieldRate (_S : FQSWOperationalSurface ψ n q e) [Fintype e] : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card e : ℝ) / (n : ℝ)

/-- Normalized error corresponding to the stored trace-norm error. -/
def normalizedError (S : FQSWOperationalSurface ψ n q e) : ℝ :=
  (1 / 2 : ℝ) * S.traceNormError

end FQSWOperationalSurface

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

/-- Alice/reference marginal `ψ^{AR}` used by the ADHW one-shot FQSW proof
route. -/
def adhwFQSWARState (ψ : PureVector (Prod (Prod a b) r)) : State (Prod a r) :=
  ψ.state.stateMergingReferenceState

/-- Alice's source split isometry induced by the source assumption
`A = A₁ × A₂` in ADHW `thm:trueoneShotMother` (fqsw.tex lines 553-568). -/
def adhwFQSWAliceIsometryOfSplit (split : a ≃ Prod q e) :
    ReferenceIsometry a (Prod q e) :=
  ReferenceIsometry.ofEquiv split

/-- Alice's source split followed by a unitary on the split `A₁ × A₂`
register, matching the Haar-random unitary stage in ADHW fqsw.tex
lines 580-841. -/
def adhwFQSWAliceIsometryOfSplitUnitary
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    ReferenceIsometry a (Prod q e) :=
  (ReferenceUnitary.toReferenceIsometry ({ matrix := U } : ReferenceUnitary (Prod q e))).comp
    (adhwFQSWAliceIsometryOfSplit split)

/-- The post-Alice state before Bob's isometry, for a concrete Alice isometry
`U : A → A₁A₂`. -/
def adhwFQSWPostAliceStateOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    State (Prod (Prod q e) (Prod b r)) :=
  let ψA : PureVector (Prod a (Prod b r)) :=
    ψ.reindex (fqswSourceToAliceInputEquiv a b r)
  (U.applyPureVector ψA).state

/-- The post-Alice pure vector regrouped as a purification of the decoupling
marginal `σ^{A₂R}(U)`, with Bob's side `A₁B` as the purifying reference. -/
def adhwFQSWPostAliceA2RPurificationOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    PureVector (Prod (Prod q b) (Prod e r)) :=
  let ψA : PureVector (Prod a (Prod b r)) :=
    ψ.reindex (fqswSourceToAliceInputEquiv a b r)
  (U.applyPureVector ψA).reindex (fqswAliceOutputToA2REquiv q e b r)

/-- The decoupling marginal `σ^{A₂R}(U)` from ADHW fqsw.tex lines 580-841. -/
def adhwFQSWSigmaA2RStateOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) : State (Prod e r) :=
  ((adhwFQSWPostAliceStateOfIsometry ψ U).reindex
    (fqswAliceOutputToA2REquiv q e b r)).marginalB

/-- The regrouped post-Alice pure vector purifies the ADHW decoupling marginal
`σ^{A₂R}(U)`. -/
theorem adhwFQSWPostAliceA2RPurificationOfIsometry_purifies
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U).Purifies
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U) := by
  dsimp [adhwFQSWPostAliceA2RPurificationOfIsometry,
    adhwFQSWSigmaA2RStateOfIsometry, adhwFQSWPostAliceStateOfIsometry]
  exact PureVector.purifies_marginalB _

/-- The `A₂` marginal `σ^{A₂}(U)` in ADHW fqsw.tex lines 767-795. -/
def adhwFQSWSigmaA2StateOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) : State e :=
  (adhwFQSWSigmaA2RStateOfIsometry (q := q) ψ U).marginalA

/-- The reference marginal `σ^R`, unchanged by Alice's isometry in the ADHW
one-shot proof route. -/
def adhwFQSWSigmaRState (ψ : PureVector (Prod (Prod a b) r)) : State r :=
  (adhwFQSWARState ψ).marginalB

/-- If the left subsystem has only one basis element, every bipartite state is
the product of its two marginals. -/
theorem state_matrix_eq_prod_marginals_of_subsingleton_left
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Subsingleton α] (ρ : State (Prod α β)) :
    ρ.matrix = (ρ.marginalA.prod ρ.marginalB).matrix := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  have hxy : xa = ya := Subsingleton.elim _ _
  subst ya
  have hA : ρ.marginalA.matrix xa xa = 1 := by
    have htrace := ρ.marginalA.trace_eq_one
    rw [Matrix.trace] at htrace
    have hsum :
        (∑ x : α, ρ.marginalA.matrix x x) =
          ρ.marginalA.matrix xa xa := by
      apply Finset.sum_eq_single xa
      · intro b _ hb
        exact False.elim (hb (Subsingleton.elim b xa))
      · intro h
        exact False.elim (h (Finset.mem_univ xa))
    have hsum_diag :
        (∑ x : α, Matrix.diag ρ.marginalA.matrix x) =
          ρ.marginalA.matrix xa xa := by
      simpa [Matrix.diag] using hsum
    rw [hsum_diag] at htrace
    exact htrace
  have hB : ρ.marginalB.matrix xb yb = ρ.matrix (xa, xb) (xa, yb) := by
    rw [State.marginalB_matrix]
    simp [partialTraceA]
    exact Finset.sum_eq_single xa
      (by intro b _ hb; exact False.elim (hb (Subsingleton.elim b xa)))
      (by intro h; exact False.elim (h (Finset.mem_univ xa)))
  change ρ.matrix (xa, xb) (xa, yb) =
    ρ.marginalA.matrix xa xa * ρ.marginalB.matrix xb yb
  rw [hA, hB]
  simp

/-- The ADHW notation `σ^R` is the `R` marginal of the original pure source. -/
theorem adhwFQSWSigmaRState_eq_source_marginalB
    (ψ : PureVector (Prod (Prod a b) r)) :
    adhwFQSWSigmaRState ψ = ψ.state.marginalB := by
  apply State.ext
  ext x y
  simp [adhwFQSWSigmaRState, adhwFQSWARState, State.marginalB,
    State.stateMergingReferenceState, partialTraceA, Fintype.sum_prod_type]

/-- Regrouping Alice's post-isometry state into `A₁B × A₂R` and then tracing
down to `R` is the same as tracing the original post-isometry state down to
`BR` and then to `R`.  This is the register-bookkeeping part of the ADHW
one-shot route before the Schur/HS moment calculation. -/
theorem adhwFQSW_marginalB_marginalB_reindex_a2r
    (ρ : State (Prod (Prod q e) (Prod b r))) :
    ((ρ.reindex (fqswAliceOutputToA2REquiv q e b r)).marginalB).marginalB =
      ρ.marginalB.marginalB := by
  apply State.ext
  ext x y
  simp [State.marginalB, State.reindex, fqswAliceOutputToA2REquiv, partialTraceA,
    Fintype.sum_prod_type]
  calc
    (∑ ee : e, ∑ qq : q, ∑ bb : b,
      ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) =
        (∑ qq : q, ∑ ee : e, ∑ bb : b,
          ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          rw [Finset.sum_comm]
    _ = (∑ qq : q, ∑ bb : b, ∑ ee : e,
          ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          apply Finset.sum_congr rfl
          intro qq _
          rw [Finset.sum_comm]
    _ = (∑ bb : b, ∑ qq : q, ∑ ee : e,
          ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          rw [Finset.sum_comm]

/-- Alice's source-to-input reindexing leaves the final reference marginal
as the `R` marginal used in the ADHW FQSW source route. -/
theorem adhwFQSW_sourceInput_marginalB_marginalB
    (ψ : PureVector (Prod (Prod a b) r)) :
    (ψ.reindex (fqswSourceToAliceInputEquiv a b r)).state.marginalB.marginalB =
      adhwFQSWSigmaRState ψ := by
  apply State.ext
  ext x y
  simp [adhwFQSWSigmaRState, adhwFQSWARState, State.marginalB,
    State.stateMergingReferenceState, PureVector.state, fqswSourceToAliceInputEquiv,
    partialTraceA]
  rw [Finset.sum_comm]

/-- Tracing Bob's register after Alice's isometry is the same as applying the
Alice isometry directly to the source `AR` marginal.  This is the register
bridge that lets the ADHW Schur/HS calculation work on `ψ^{AR}` while the
operational protocol is computed from the full pure source `ψ^{ABR}`. -/
theorem adhwFQSWPostAliceStateOfIsometry_stateMergingReference_matrix
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
      (fqswSourceToAliceInputEquiv (Prod q e) b r).symm).stateMergingReferenceState).matrix =
      U.applyMatrix (adhwFQSWARState ψ).matrix := by
  ext x y
  simp [adhwFQSWPostAliceStateOfIsometry, adhwFQSWARState,
    State.stateMergingReferenceState, PureVector.state, State.reindex,
    fqswSourceToAliceInputEquiv, ReferenceIsometry.applyPureVector,
    ReferenceIsometry.applyAmp, ReferenceIsometry.applyMatrix,
    ReferenceIsometry.targetBlock, rankOneMatrix, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ii _
  apply Finset.sum_congr rfl
  intro bb _
  ring

/-- The decoupling marginal `σ^{A₂R}(U)` can be obtained from the post-Alice
`(A₁A₂)R` marginal by regrouping it as `A₁ × (A₂R)` and tracing out `A₁`.
This is the bookkeeping form used by the ADHW one-shot decoupling proof. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_eq_postAliceAR_marginalB
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U =
      ((((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
        (fqswSourceToAliceInputEquiv (Prod q e) b r).symm).stateMergingReferenceState).reindex
          (fqswQERToA2REquiv q e r)).marginalB := by
  apply State.ext
  ext x y
  simp [adhwFQSWSigmaA2RStateOfIsometry, State.stateMergingReferenceState,
    State.marginalB, State.reindex, fqswAliceOutputToA2REquiv,
    fqswSourceToAliceInputEquiv, fqswQERToA2REquiv, partialTraceA,
    Fintype.sum_prod_type]

/-- Matrix form of the ADHW decoupling marginal: `σ^{A₂R}(U)` is the
`A₂R` marginal of the source `AR` state after Alice's split isometry.  This is
the exact bridge from the operational full-source protocol state to the
source's Schur/HS one-shot calculation on `ψ^{AR}`. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_partialTraceA_applyMatrix_AR
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).matrix =
      partialTraceA (a := q) (b := Prod e r)
        ((U.applyMatrix (adhwFQSWARState ψ).matrix).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
  rw [adhwFQSWSigmaA2RStateOfIsometry_eq_postAliceAR_marginalB]
  change partialTraceA (a := q) (b := Prod e r)
      (((((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
        (fqswSourceToAliceInputEquiv (Prod q e) b r).symm).stateMergingReferenceState).matrix).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) = _
  rw [adhwFQSWPostAliceStateOfIsometry_stateMergingReference_matrix]

/-- The reference marginal `σ^R` in the ADHW one-shot proof is independent of
Alice's isometry.  This is the formal source-route bridge that justifies using
a fixed `σ^R` in the product term
`σ^{A₂}(U) ⊗ σ^R`. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_marginalB_eq_sigmaR
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).marginalB =
      adhwFQSWSigmaRState ψ := by
  have hpost :
      (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).marginalB =
        (ψ.reindex (fqswSourceToAliceInputEquiv a b r)).state.marginalB := by
    let Ψ : PureVector (Prod a (Prod b r)) :=
      ψ.reindex (fqswSourceToAliceInputEquiv a b r)
    have hpur : (U.applyPureVector Ψ).Purifies Ψ.state.marginalB := by
      exact U.applyPureVector_purifies (PureVector.purifies_marginalB Ψ)
    apply State.ext
    rw [State.marginalB_matrix]
    exact hpur
  calc
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).marginalB =
        (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).marginalB.marginalB := by
          exact adhwFQSW_marginalB_marginalB_reindex_a2r
            (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U)
    _ = (ψ.reindex (fqswSourceToAliceInputEquiv a b r)).state.marginalB.marginalB := by
          rw [hpost]
    _ = adhwFQSWSigmaRState ψ := by
          exact adhwFQSW_sourceInput_marginalB_marginalB ψ

/-- Local maximally mixed state constructor used by the FQSW source route. -/
def adhwFQSWMaximallyMixedState (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    State α where
  matrix := (((Fintype.card α : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix α)
  pos := by
    have hscalar : (0 : ℂ) ≤ (((Fintype.card α : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card α : ℕ))
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one hscalar
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    have hcard : (Fintype.card α : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    norm_num [hcard]

/-- On a one-point finite system, every state is the local maximally mixed
state. -/
theorem state_matrix_eq_maximallyMixed_of_subsingleton
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α] [Subsingleton α]
    (ρ : State α) :
    ρ.matrix = (adhwFQSWMaximallyMixedState α).matrix := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  have hdiag : ρ.matrix x x = 1 := by
    have htrace := ρ.trace_eq_one
    rw [Matrix.trace] at htrace
    have hsum :
        (∑ z : α, ρ.matrix z z) = ρ.matrix x x := by
      apply Finset.sum_eq_single x
      · intro z _ hz
        exact False.elim (hz (Subsingleton.elim z x))
      · intro h
        exact False.elim (h (Finset.mem_univ x))
    have hsum_diag :
        (∑ z : α, Matrix.diag ρ.matrix z) = ρ.matrix x x := by
      simpa [Matrix.diag] using hsum
    rw [hsum_diag] at htrace
    exact htrace
  have hcard : (Fintype.card α : ℝ) = 1 := by
    exact_mod_cast
      (Fintype.card_eq_one_iff.mpr ⟨x, fun y => Subsingleton.elim y x⟩)
  simp [adhwFQSWMaximallyMixedState, hdiag, hcard]

/-- The `A₂` marginal of the canonical maximally entangled vector is maximally
mixed. -/
theorem maximallyEntangledPureVector_marginalA (pairing : e ≃ et) :
    (maximallyEntangledPureVector pairing).state.marginalA =
      adhwFQSWMaximallyMixedState e := by
  apply State.ext
  ext x y
  have hcard_pos : 0 < (Fintype.card e : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsqrt_ne : (Real.sqrt (Fintype.card e : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hcard_pos))
  have hcoef :
      ((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹ *
          star ((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card e : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [star_inv₀]
    simp
    field_simp [hsqrt_ne]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
    exact congrArg Complex.ofReal (Real.sq_sqrt hcard_pos.le).symm
  have hcoef' :
      ((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (Fintype.card e : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card e : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa using hcoef
  by_cases hxy : x = y
  · subst y
    simp [State.marginalA, partialTraceB,
      maximallyEntangledPureVector, adhwFQSWMaximallyMixedState, hcoef']
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp [State.marginalA, partialTraceB,
      maximallyEntangledPureVector, adhwFQSWMaximallyMixedState, hxy, hyx]

/-- The maximally mixed `I^{A₂}/d_{A₂}` state appearing in the ADHW decoupling
target of fqsw.tex lines 580-841. -/
def adhwFQSWMaximallyMixedA2State (e : Type y)
    [Fintype e] [DecidableEq e] [Nonempty e] : State e :=
  adhwFQSWMaximallyMixedState e

/-- The source-route trace-norm decoupling integrand for a split Alice system
and a concrete unitary on `A₁ × A₂`, matching the quantity controlled by the
Haar-selection step in ADHW fqsw.tex lines 580-841. -/
def adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  traceDistance
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix
    (((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).matrix)

/-- Product-decoupling trace-norm integrand
`||σ^{A₂R}(U) - σ^{A₂}(U) ⊗ σ^R||₁` from ADHW fqsw.tex
lines 580-592 and 806-815. -/
def adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  traceDistance
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix
    (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).matrix)

/-- Max-mixed `A₂` trace-norm integrand
`||σ^{A₂}(U) - I^{A₂}/d_{A₂}||₁` from ADHW fqsw.tex lines
767-795 and 806-815. -/
def adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  traceDistance
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix
    (adhwFQSWMaximallyMixedA2State e).matrix

/-- Hilbert--Schmidt-square version of the product-decoupling integrand in
ADHW fqsw.tex lines 682-747. -/
def adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  hilbertSchmidtSq
    ((adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix -
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
        (adhwFQSWSigmaRState ψ)).matrix))

/-- Hilbert--Schmidt-square version of the max-mixed `A₂` integrand in ADHW
fqsw.tex lines 776-787. -/
def adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  hilbertSchmidtSq
    ((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix -
      (adhwFQSWMaximallyMixedA2State e).matrix)

/-- Source `A` marginal reindexed by the ADHW split `A ≃ A₁ × A₂`. -/
def adhwFQSWASplitMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    CMatrix (Prod q e) :=
  ((adhwFQSWARState ψ).marginalA.matrix).submatrix split.symm split.symm

/-- Source `AR` marginal reindexed by the ADHW split `A ≃ A₁ × A₂`. -/
def adhwFQSWARSplitMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    CMatrix (Prod (Prod q e) r) :=
  ((adhwFQSWARState ψ).matrix).submatrix
    (fqswARSplitEquiv split).symm (fqswARSplitEquiv split).symm

/-- Split form of `ψ^A ⊗ ψ^R` on the `A₁A₂R` register. -/
def adhwFQSWARProductSplitMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    CMatrix (Prod (Prod q e) r) :=
  Matrix.kronecker (adhwFQSWASplitMatrix ψ split) (adhwFQSWSigmaRState ψ).matrix

theorem referenceIsometry_partialTraceB_applyMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (X : CMatrix (Prod α γ)) :
    partialTraceB (a := β) (b := γ) (V.applyMatrix X) =
      V.matrix * partialTraceB (a := α) (b := γ) X *
        Matrix.conjTranspose V.matrix := by
  ext i j
  simp [partialTraceB, ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- Applying a reference isometry to the left/reference side conjugates the
left marginal by that isometry. -/
theorem referenceIsometry_marginalA_applyPureVector
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (Ψ : PureVector (Prod α γ)) :
    (V.applyPureVector Ψ).state.marginalA.matrix =
      V.matrix * Ψ.state.marginalA.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalA_matrix]
  rw [PureVector.state_matrix]
  rw [ReferenceIsometry.applyPureVector_amp]
  rw [V.rankOne_applyAmp]
  rw [referenceIsometry_partialTraceB_applyMatrix]
  rfl

/-- Conjugating a bipartite matrix by a product reference isometry is the same
as applying the right isometry first and then the left isometry. -/
theorem referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (Prod α γ)) :
    Matrix.kronecker V.matrix W.matrix * X *
        Matrix.conjTranspose (Matrix.kronecker V.matrix W.matrix) =
      V.applyMatrix (W.applyMatrixRight X) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.targetBlock, ReferenceIsometry.rightBlock,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_kronecker, Finset.sum_mul, Finset.mul_sum,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]
  apply Finset.sum_congr rfl
  intro _ _
  rw [Finset.sum_comm]

/-- Taking the right marginal after a product reference-isometry conjugation
leaves only the left isometry conjugating the original left marginal. -/
theorem referenceIsometry_prod_partialTraceB_conj
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (Prod α γ)) :
    partialTraceB (a := β) (b := δ)
        (Matrix.kronecker V.matrix W.matrix * X *
          Matrix.conjTranspose (Matrix.kronecker V.matrix W.matrix)) =
      V.matrix * partialTraceB (a := α) (b := γ) X *
        Matrix.conjTranspose V.matrix := by
  rw [referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight]
  rw [referenceIsometry_partialTraceB_applyMatrix]
  rw [W.partialTraceB_applyMatrixRight]

/-- Taking the left marginal after a product reference-isometry conjugation
leaves only the right isometry conjugating the original right marginal. -/
theorem referenceIsometry_prod_partialTraceA_conj
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (Prod α γ)) :
    partialTraceA (a := β) (b := δ)
        (Matrix.kronecker V.matrix W.matrix * X *
          Matrix.conjTranspose (Matrix.kronecker V.matrix W.matrix)) =
      W.matrix * partialTraceA (a := α) (b := γ) X *
        Matrix.conjTranspose W.matrix := by
  rw [referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight]
  rw [V.partialTraceA_applyMatrix]
  rw [W.partialTraceA_applyMatrixRight]

/-- Applying composed reference isometries to a matrix is the same as applying
the right factor first and the left factor second. -/
theorem referenceIsometry_comp_applyMatrix
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (W : ReferenceIsometry β γ) (V : ReferenceIsometry α β)
    (X : CMatrix (Prod α δ)) :
    (W.comp V).applyMatrix X = W.applyMatrix (V.applyMatrix X) := by
  ext x y
  let B : CMatrix α := ReferenceIsometry.targetBlock X x.2 y.2
  change (((W.matrix * V.matrix) * B *
        Matrix.conjTranspose (W.matrix * V.matrix)) x.1 y.1) =
      (W.matrix * (V.matrix * B * Matrix.conjTranspose V.matrix) *
        Matrix.conjTranspose W.matrix) x.1 y.1
  rw [Matrix.conjTranspose_mul]
  simp [Matrix.mul_assoc]

/-- The reference isometry induced by an equivalence is simultaneous matrix
reindexing on the reference register. -/
theorem referenceIsometry_ofEquiv_applyMatrix_eq_submatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (E : α ≃ β) (X : CMatrix (Prod α γ)) :
    (ReferenceIsometry.ofEquiv E).applyMatrix X =
      X.submatrix
        (Equiv.prodCongr E.symm (Equiv.refl γ))
        (Equiv.prodCongr E.symm (Equiv.refl γ)) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply, Matrix.conjTranspose]
  rw [Finset.sum_eq_single (E.symm y.1)]
  · rw [Finset.sum_eq_single (E.symm x.1)]
    · simp [Prod.map]
    · intro z _ hz
      have hxz : x.1 ≠ E z := by
        intro hxz
        exact hz (by simpa [hxz])
      simp [hxz]
    · intro hz
      exact False.elim (hz (Finset.mem_univ _))
  · intro z _ hz
    have hyz : y.1 ≠ E z := by
      intro hyz
      exact hz (by simpa [hyz])
    simp [hyz]
  · intro hz
    exact False.elim (hz (Finset.mem_univ _))

/-- The reference isometry induced by an equivalence is onto its target. -/
theorem referenceIsometry_ofEquiv_mul_conjTranspose
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : α ≃ β) :
    (ReferenceIsometry.ofEquiv E).matrix *
        Matrix.conjTranspose (ReferenceIsometry.ofEquiv E).matrix =
      (1 : CMatrix β) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (E.symm i)]
    · simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose]
    · intro x _ hx
      have hne : i ≠ E x := by
        intro h
        exact hx (by simpa [h])
      simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose, hne]
    · intro h
      exact False.elim (h (Finset.mem_univ (E.symm i)))
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_zero]
    · simp [Matrix.one_apply, hij]
    · intro x _
      by_cases hi : i = E x
      · have hj : j ≠ E x := by
          intro hj
          exact hij (hi.trans hj.symm)
        simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose, hi, hj]
      · simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose, hi]

/-- A product-index finite sum with a delta on the right coordinate collapses
to the fixed right-coordinate slice. -/
theorem fqsw_sum_prod_right_eq
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : α → β → ζ) :
    (∑ x : Prod α β, if b0 = x.2 then f x.1 x.2 else 0) =
      ∑ a : α, f a b0 := by
  rw [Fintype.sum_prod_type]
  simp

/-- A product-index finite sum with the symmetric delta orientation on the
right coordinate collapses to the fixed right-coordinate slice. -/
theorem fqsw_sum_prod_right_eq'
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : α → β → ζ) :
    (∑ x : Prod α β, if x.2 = b0 then f x.1 x.2 else 0) =
      ∑ a : α, f a b0 := by
  rw [Fintype.sum_prod_type]
  simp

/-- Pair-valued variant of `fqsw_sum_prod_right_eq`. -/
theorem fqsw_sum_prod_right_eq_pair
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : Prod α β → ζ) :
    (∑ x : Prod α β, if b0 = x.2 then f x else 0) =
      ∑ a : α, f (a, b0) := by
  rw [Fintype.sum_prod_type]
  simp

/-- Pair-valued variant of `fqsw_sum_prod_right_eq'`. -/
theorem fqsw_sum_prod_right_eq_pair'
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : Prod α β → ζ) :
    (∑ x : Prod α β, if x.2 = b0 then f x else 0) =
      ∑ a : α, f (a, b0) := by
  rw [Fintype.sum_prod_type]
  simp

/-- Applying a reference isometry to the left factor of a bipartite matrix is
conjugation by `V ⊗ I` on the product register. -/
theorem referenceIsometry_applyMatrix_eq_kronecker_one_conj
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (X : CMatrix (Prod α γ)) :
    V.applyMatrix X =
      (Matrix.kronecker V.matrix (1 : CMatrix γ)) * X *
        Matrix.conjTranspose (Matrix.kronecker V.matrix (1 : CMatrix γ)) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.one_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [fqsw_sum_prod_right_eq_pair' (b0 := y.2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [fqsw_sum_prod_right_eq_pair (b0 := x.2)]

theorem fqsw_partialTraceB_partialTraceA_qer_reindex
    {q : Type x} {e : Type y} {r : Type w}
    [Fintype q] [Fintype e] [Fintype r]
    (M : CMatrix (Prod (Prod q e) r)) :
    partialTraceB (a := e) (b := r)
      (partialTraceA (a := q) (b := Prod e r)
        (M.submatrix (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)) =
      partialTraceA (a := q) (b := e)
        (partialTraceB (a := Prod q e) (b := r) M) := by
  ext i j
  simp [partialTraceA, partialTraceB, fqswQERToA2REquiv, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Tracing out `q` after regrouping `(q × e) × r` as `q × (e × r)`
turns a product matrix into the product of the `q`-trace and the untouched
`r` matrix. -/
theorem fqsw_partialTraceA_qer_kronecker
    {q : Type x} {e : Type y} {r : Type w}
    [Fintype q] [Fintype e] [Fintype r]
    (A : CMatrix (Prod q e)) (R : CMatrix r) :
    partialTraceA (a := q) (b := Prod e r)
      ((Matrix.kronecker A R).submatrix
        (fqswQERToA2REquiv q e r).symm
        (fqswQERToA2REquiv q e r).symm) =
      Matrix.kronecker (partialTraceA (a := q) (b := e) A) R := by
  ext i j
  simp [partialTraceA, fqswQERToA2REquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- `Tr_A` is compatible with matrix subtraction. -/
theorem fqsw_partialTraceA_sub
    {α : Type u} {β : Type v} [Fintype α]
    (X Y : CMatrix (Prod α β)) :
    partialTraceA (a := α) (b := β) (X - Y) =
      partialTraceA (a := α) (b := β) X -
        partialTraceA (a := α) (b := β) Y := by
  ext i j
  simp [partialTraceA, Finset.sum_sub_distrib]

/-- Matrix trace is invariant under simultaneous finite equivalence
reindexing. -/
theorem fqsw_trace_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι ≃ κ) (M : CMatrix κ) :
    (M.submatrix E E).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact Fintype.sum_equiv E (fun i => M (E i) (E i)) (fun k => M k k) (fun _ => rfl)

/-- Hermiticity is invariant under simultaneous finite equivalence
reindexing. -/
theorem fqsw_isHermitian_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι ≃ κ)
    {M : CMatrix κ} (hM : M.IsHermitian) :
    (M.submatrix E E).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simpa [Matrix.conjTranspose] using hM.apply (E i) (E j)

/-- Simultaneous finite equivalence reindexing commutes with matrix
multiplication. -/
theorem fqsw_mul_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι ≃ κ)
    (M N : CMatrix κ) :
    (M.submatrix E E) * (N.submatrix E E) =
      (M * N).submatrix E E := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv E
    (fun k : ι => M (E i) (E k) * N (E k) (E j))
    (fun k : κ => M (E i) k * N k (E j))
    (fun _ => rfl)

/-- For Hermitian matrices the Hilbert--Schmidt square is `Tr[M²]`. -/
theorem fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian
    {α : Type*} [Fintype α] [DecidableEq α] (M : CMatrix α)
    (hM : M.IsHermitian) :
    hilbertSchmidtSq M = (M * M).trace.re := by
  unfold hilbertSchmidtSq
  rw [Matrix.star_eq_conjTranspose, hM.eq]

/-- Hilbert--Schmidt square of a Kronecker product factors. -/
theorem fqsw_hilbertSchmidtSq_kronecker
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : CMatrix α) (N : CMatrix β) :
    hilbertSchmidtSq (Matrix.kronecker M N) =
      hilbertSchmidtSq M * hilbertSchmidtSq N := by
  unfold hilbertSchmidtSq
  change ((Matrix.conjTranspose (Matrix.kronecker M N) *
        Matrix.kronecker M N).trace).re =
      ((Matrix.conjTranspose M * M).trace).re *
        ((Matrix.conjTranspose N * N).trace).re
  have hct :
      Matrix.conjTranspose (Matrix.kronecker M N) =
        Matrix.kronecker (Matrix.conjTranspose M) (Matrix.conjTranspose N) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker M N
  have hmul :
      Matrix.kronecker (Matrix.conjTranspose M) (Matrix.conjTranspose N) *
          Matrix.kronecker M N =
        Matrix.kronecker (Matrix.conjTranspose M * M) (Matrix.conjTranspose N * N) := by
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul (Matrix.conjTranspose M) M
        (Matrix.conjTranspose N) N).symm
  rw [hct, hmul]
  have htrace :
      (Matrix.kronecker (Matrix.conjTranspose M * M)
          (Matrix.conjTranspose N * N)).trace =
        (Matrix.conjTranspose M * M).trace *
          (Matrix.conjTranspose N * N).trace := by
    simpa [Matrix.kronecker] using
      Matrix.trace_kronecker (Matrix.conjTranspose M * M)
        (Matrix.conjTranspose N * N)
  rw [htrace]
  have hM_im :
      ((Matrix.conjTranspose M * M).trace).im = 0 := by
    exact (Matrix.PosSemidef.trace_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self M)).2.symm
  have hN_im :
      ((Matrix.conjTranspose N * N).trace).im = 0 := by
    exact (Matrix.PosSemidef.trace_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self N)).2.symm
  simp [Complex.mul_re, hM_im, hN_im]

/-- Hilbert--Schmidt square is invariant under finite equivalence reindexing. -/
theorem fqsw_hilbertSchmidtSq_submatrix_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (E : α ≃ β) (M : CMatrix α) :
    hilbertSchmidtSq (M.submatrix E.symm E.symm) = hilbertSchmidtSq M := by
  unfold hilbertSchmidtSq
  congr 1
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply]
  calc
    (∑ i : β, ∑ k : β, star (M (E.symm k) (E.symm i)) * M (E.symm k) (E.symm i)) =
        ∑ i : α, ∑ k : β, star (M (E.symm k) i) * M (E.symm k) i := by
          exact Fintype.sum_equiv E.symm
            (fun i : β => ∑ k : β,
              star (M (E.symm k) (E.symm i)) * M (E.symm k) (E.symm i))
            (fun i : α => ∑ k : β, star (M (E.symm k) i) * M (E.symm k) i)
            (by intro i; simp)
    _ = ∑ i : α, ∑ k : α, star (M k i) * M k i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Fintype.sum_equiv E.symm
            (fun k : β => star (M (E.symm k) i) * M (E.symm k) i)
            (fun k : α => star (M k i) * M k i)
            (by intro k; simp)

/-- Two-copy Kronecker commutes with matrix adjoint. -/
theorem fqsw_tensorPowerKroneckerTwo_star
    {α : Type*} [Fintype α] [DecidableEq α] (M : CMatrix α) :
    tensorPowerKroneckerTwo (a := α) (star M) =
      star (tensorPowerKroneckerTwo (a := α) M) := by
  ext x y
  simp [tensorPowerKroneckerTwo, Matrix.star_apply]

/-- On two copies, the tensor-power unitary matrix is the explicit Kronecker
square used by the FQSW second-moment calculation. -/
theorem fqsw_unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) :
    (unitaryTensorPowerMatrix U 2 : CMatrix (TensorPower α 2)) =
      tensorPowerKroneckerTwo (a := α) (U : CMatrix α) := by
  ext x y
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod]
  simp [tensorPowerKroneckerTwo]

/-- Operational/source bridge for the ADHW max-mixed calculation: the `A₂`
marginal produced by the split-unitary FQSW definitions is the partial trace
of the split source `A` marginal after conjugating by the Haar unitary. -/
theorem adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_A
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix =
      partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split *
          star (U : CMatrix (Prod q e))) := by
  rw [adhwFQSWSigmaA2StateOfIsometry]
  rw [State.marginalA_matrix]
  rw [adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_partialTraceA_applyMatrix_AR]
  rw [fqsw_partialTraceB_partialTraceA_qer_reindex]
  rw [referenceIsometry_partialTraceB_applyMatrix]
  congr 1
  have hsplit :
      (adhwFQSWAliceIsometryOfSplitUnitary split U).matrix *
          partialTraceB (a := a) (b := r) (adhwFQSWARState ψ).matrix *
          Matrix.conjTranspose (adhwFQSWAliceIsometryOfSplitUnitary split U).matrix =
        (U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split *
          star (U : CMatrix (Prod q e)) := by
    ext i j
    simp [adhwFQSWAliceIsometryOfSplitUnitary, adhwFQSWAliceIsometryOfSplit,
      ReferenceIsometry.comp, ReferenceUnitary.toReferenceIsometry,
      ReferenceIsometry.ofEquiv, adhwFQSWASplitMatrix, State.marginalA,
      partialTraceB, Matrix.mul_apply, Matrix.conjTranspose,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    change
      (∑ x : a, ∑ y : a, ∑ rr : r,
        (U : CMatrix (Prod q e)) i (split y) *
          ((adhwFQSWARState ψ).matrix (y, rr) (x, rr) *
            star ((U : CMatrix (Prod q e)) j (split x)))) =
        (∑ x : Prod q e, ∑ y : Prod q e, ∑ rr : r,
          (U : CMatrix (Prod q e)) i y *
            ((adhwFQSWARState ψ).matrix (split.symm y, rr) (split.symm x, rr) *
              star ((U : CMatrix (Prod q e)) j x)))
    calc
      (∑ x : a, ∑ y : a, ∑ rr : r,
        (U : CMatrix (Prod q e)) i (split y) *
          ((adhwFQSWARState ψ).matrix (y, rr) (x, rr) *
            star ((U : CMatrix (Prod q e)) j (split x)))) =
        ∑ x : Prod q e, ∑ y : a, ∑ rr : r,
          (U : CMatrix (Prod q e)) i (split y) *
            ((adhwFQSWARState ψ).matrix (y, rr) (split.symm x, rr) *
              star ((U : CMatrix (Prod q e)) j x)) := by
          exact Fintype.sum_equiv split
            (fun x : a => ∑ y : a, ∑ rr : r,
              (U : CMatrix (Prod q e)) i (split y) *
                ((adhwFQSWARState ψ).matrix (y, rr) (x, rr) *
                  star ((U : CMatrix (Prod q e)) j (split x))))
            (fun x : Prod q e => ∑ y : a, ∑ rr : r,
              (U : CMatrix (Prod q e)) i (split y) *
                ((adhwFQSWARState ψ).matrix (y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (Prod q e)) j x)))
            (by intro x; simp)
      _ = ∑ x : Prod q e, ∑ y : Prod q e, ∑ rr : r,
          (U : CMatrix (Prod q e)) i y *
            ((adhwFQSWARState ψ).matrix (split.symm y, rr) (split.symm x, rr) *
              star ((U : CMatrix (Prod q e)) j x)) := by
          apply Finset.sum_congr rfl
          intro x _
          refine Fintype.sum_equiv split
            (fun y : a => ∑ rr : r,
              (U : CMatrix (Prod q e)) i (split y) *
                ((adhwFQSWARState ψ).matrix (y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (Prod q e)) j x)))
            (fun y : Prod q e => ∑ rr : r,
              (U : CMatrix (Prod q e)) i y *
                ((adhwFQSWARState ψ).matrix (split.symm y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (Prod q e)) j x)))
            ?_
          intro y
          simp
  exact hsplit

/-- Applying the split-unitary Alice isometry to the source `AR` matrix is the
same as conjugating the split source matrix by `U ⊗ I_R`. -/
theorem adhwFQSWAliceIsometryOfSplitUnitary_applyMatrix_AR_eq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWAliceIsometryOfSplitUnitary split U).applyMatrix
        (adhwFQSWARState ψ).matrix =
      (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
        adhwFQSWARSplitMatrix ψ split *
        star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) := by
  unfold adhwFQSWAliceIsometryOfSplitUnitary adhwFQSWAliceIsometryOfSplit
  rw [referenceIsometry_comp_applyMatrix]
  have hsplit :
      (ReferenceIsometry.ofEquiv split).applyMatrix (adhwFQSWARState ψ).matrix =
        adhwFQSWARSplitMatrix ψ split := by
    rw [referenceIsometry_ofEquiv_applyMatrix_eq_submatrix]
    ext x y
    rfl
  rw [hsplit]
  rw [referenceIsometry_applyMatrix_eq_kronecker_one_conj]
  simp [ReferenceUnitary.toReferenceIsometry, Matrix.star_eq_conjTranspose]

/-- Operational/source bridge for the ADHW product calculation: the `A₂R`
marginal produced by a split-unitary Alice isometry is the `q` partial trace of
the split source `AR` matrix after conjugating Alice's split register by the
Haar unitary. -/
theorem adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_AR_split
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix =
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            adhwFQSWARSplitMatrix ψ split *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
  rw [adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_partialTraceA_applyMatrix_AR]
  rw [adhwFQSWAliceIsometryOfSplitUnitary_applyMatrix_AR_eq]

/-- The product term `σ^{A₂}(U) ⊗ σ^R` is the same `q` partial trace applied
to the conjugated split product matrix `ψ^A ⊗ ψ^R`. -/
theorem adhwFQSWProductA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_ARProduct
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (State.prod
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U))
      (adhwFQSWSigmaRState ψ)).matrix =
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            adhwFQSWARProductSplitMatrix ψ split *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
  let ρA : CMatrix (Prod q e) := adhwFQSWASplitMatrix ψ split
  let ρR : CMatrix r := (adhwFQSWSigmaRState ψ).matrix
  have hconj :
      (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
          adhwFQSWARProductSplitMatrix ψ split *
          star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) =
        Matrix.kronecker
          ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e)))
          ρR := by
    unfold adhwFQSWARProductSplitMatrix ρA ρR
    rw [Matrix.star_eq_conjTranspose]
    have hct :
        Matrix.conjTranspose
            (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) =
          Matrix.kronecker
            (Matrix.conjTranspose (U : CMatrix (Prod q e)))
            (Matrix.conjTranspose (1 : CMatrix r)) := by
      simpa [Matrix.kronecker] using
        Matrix.conjTranspose_kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
    rw [hct, Matrix.conjTranspose_one]
    have hmul_left :
        Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r) *
            Matrix.kronecker (adhwFQSWASplitMatrix ψ split)
              (adhwFQSWSigmaRState ψ).matrix =
          Matrix.kronecker
            ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split)
            ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix) := by
      simpa [Matrix.kronecker] using
        (Matrix.mul_kronecker_mul (U : CMatrix (Prod q e))
          (adhwFQSWASplitMatrix ψ split) (1 : CMatrix r)
          (adhwFQSWSigmaRState ψ).matrix).symm
    rw [hmul_left]
    have hmul_right :
        Matrix.kronecker
            ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split)
            ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix) *
          Matrix.kronecker (Matrix.conjTranspose (U : CMatrix (Prod q e)))
            (1 : CMatrix r) =
        Matrix.kronecker
          (((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split) *
            Matrix.conjTranspose (U : CMatrix (Prod q e)))
          (((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix) *
            (1 : CMatrix r)) := by
      simpa [Matrix.kronecker] using
        (Matrix.mul_kronecker_mul
          ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split)
          (Matrix.conjTranspose (U : CMatrix (Prod q e)))
          ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix)
          (1 : CMatrix r)).symm
    rw [hmul_right]
    simp [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  calc
    (State.prod
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U))
      (adhwFQSWSigmaRState ψ)).matrix =
        Matrix.kronecker
          (partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e))))
          ρR := by
          simp [State.prod, ρA, ρR,
            adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_A]
    _ = partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            adhwFQSWARProductSplitMatrix ψ split *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
          rw [hconj]
          rw [fqsw_partialTraceA_qer_kronecker]

/-- The lifted max-mixed product term
`||σ^{A₂}(U) ⊗ σ^R - I^{A₂}/d_{A₂} ⊗ σ^R||₁` appearing between
the triangle-inequality step and the product-with-state contraction in ADHW
fqsw.tex lines 806-815. -/
def adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  traceDistance
    (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).matrix)
    (((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).matrix)

/-- Raw triangle-inequality form of ADHW fqsw.tex lines 806-810.  This leaves
the product-with-`σ^R` contraction as a separate subsequent lemma. -/
theorem adhwFQSWDecouplingTraceNormIntegrand_le_product_add_liftedMaxMixed
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U +
        adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  let ρ : CMatrix (Prod e r) :=
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix
  let σ : CMatrix (Prod e r) :=
    ((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).matrix
  let τ : CMatrix (Prod e r) :=
    ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).matrix
  have htri := normalizedTraceDistance_triangle ρ σ τ
  unfold normalizedTraceDistance traceDistance at htri
  have h :
      traceNorm (ρ - τ) ≤ traceNorm (ρ - σ) + traceNorm (σ - τ) := by
    nlinarith
  simpa [adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary,
    adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary,
    adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary,
    ρ, σ, τ, alice, traceDistance] using h

/-- Tensoring both `A₂` states with the same `R` state cannot increase the
source trace-norm distance.  This is the ADHW step that turns the lifted
max-mixed comparison into the marginal `A₂` comparison. -/
theorem adhwFQSWLiftedMaxMixedA2TraceNormIntegrand_le_maxMixedA2
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ≤
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  have h := fqswProdRight_traceDistance_le
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice)
    (adhwFQSWMaximallyMixedA2State e)
    (adhwFQSWSigmaRState ψ)
  simpa [adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary,
    adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary, alice] using h

/-- Source-shaped pointwise ADHW triangle comparison: the final decoupling
integrand is bounded by the product-decoupling term plus the `A₂` max-mixed
term. -/
theorem adhwFQSWDecouplingTraceNormIntegrand_le_product_add_maxMixed
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U +
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  have htri :=
    adhwFQSWDecouplingTraceNormIntegrand_le_product_add_liftedMaxMixed ψ split U
  have hlift :=
    adhwFQSWLiftedMaxMixedA2TraceNormIntegrand_le_maxMixedA2 ψ split U
  linarith

/-- The normalized-distance version of the FQSW split-unitary decoupling
condition is exactly half the source trace-norm integrand. -/
theorem adhwFQSWDecoupling_normalizedTraceDistance_eq_half_integrand
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).normalizedTraceDistance
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) =
        (1 / 2 : ℝ) *
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U :=
  rfl

/-- Partial trace over the left tensor factor is continuous as a matrix-valued
finite sum. -/
@[fun_prop]
theorem partialTraceA_continuous_matrix
    {α : Type*} {β : Type*} [Fintype α] [Fintype β] :
    Continuous (fun M : CMatrix (Prod α β) => partialTraceA (a := α) (b := β) M) := by
  refine continuous_pi ?_
  intro j
  refine continuous_pi ?_
  intro j'
  simp only [partialTraceA]
  refine continuous_finsetSum Finset.univ ?_
  intro i _
  exact (continuous_apply (i, j')).comp (continuous_apply (i, j))

/-- Partial trace over the right tensor factor is continuous as a matrix-valued
finite sum. -/
@[fun_prop]
theorem partialTraceB_continuous_matrix
    {α : Type*} {β : Type*} [Fintype α] [Fintype β] :
    Continuous (fun M : CMatrix (Prod α β) => partialTraceB (a := α) (b := β) M) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro i'
  simp only [partialTraceB]
  refine continuous_finsetSum Finset.univ ?_
  intro j _
  exact (continuous_apply (i', j)).comp (continuous_apply (i, j))

/-- The Hilbert--Schmidt square is continuous on finite-dimensional complex
matrices. -/
theorem hilbertSchmidtSq_continuous_matrix
    {α : Type*} [Fintype α] [DecidableEq α] :
    Continuous (fun M : CMatrix α => hilbertSchmidtSq M) := by
  unfold hilbertSchmidtSq
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace ((Continuous.star continuous_id).matrix_mul continuous_id))

/-- Hermitian Hilbert--Schmidt expansion used by ADHW fqsw.tex
Eq. `HSexpand`: `||X - M||₂² = Tr[X²] - 2 Tr[XM] + ||M||₂²`. -/
theorem fqsw_hilbertSchmidtSq_sub_of_isHermitian
    {α : Type*} [Fintype α] [DecidableEq α]
    (X M : CMatrix α) (hX : X.IsHermitian) (hM : M.IsHermitian) :
    hilbertSchmidtSq (X - M) =
      (X * X).trace.re - (2 : ℝ) * (X * M).trace.re + hilbertSchmidtSq M := by
  unfold hilbertSchmidtSq
  simp only [Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_sub]
  rw [hX.eq, hM.eq]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.trace_sub]
  rw [Matrix.trace_sub]
  rw [Matrix.trace_sub]
  have hcomm : (M * X).trace = (X * M).trace := Matrix.trace_mul_comm M X
  rw [hcomm]
  simp [Complex.sub_re]
  ring

/-- Two-copy Kronecker of the identity is the identity, in the recursive
`TensorPower` coordinates used by the Schur/twirl API. -/
theorem fqsw_tensorPowerKroneckerTwo_one
    {α : Type*} [Fintype α] [DecidableEq α] :
    tensorPowerKroneckerTwo (a := α) (1 : CMatrix α) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorPowerKroneckerTwo]
  · have hcoord :
        tensorPowerEquiv (a := α) 2 x 0 ≠ tensorPowerEquiv (a := α) 2 y 0 ∨
          tensorPowerEquiv (a := α) 2 x 1 ≠ tensorPowerEquiv (a := α) 2 y 1 := by
      by_contra h
      push Not at h
      apply hxy
      apply (tensorPowerEquiv (a := α) 2).injective
      funext i
      fin_cases i <;> simp [h]
    rcases hcoord with h0 | h1
    · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, hxy]
    · by_cases h0 :
        tensorPowerEquiv (a := α) 2 x 0 = tensorPowerEquiv (a := α) 2 y 0
      · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, h1, hxy]
      · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, hxy]

private theorem fqsw_tensorPowerProdEquiv_fst_apply
    {α : Type*} {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) (z : TensorPower (Prod α β) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv α β n z).1) i =
      (tensorPowerEquiv n z i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

private theorem fqsw_tensorPowerProdEquiv_snd_apply
    {α : Type*} {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) (z : TensorPower (Prod α β) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv α β n z).2) i =
      (tensorPowerEquiv n z i).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

/-- Two-copy Kronecker for an operator acting only on the left side of a
product register. -/
private theorem fqsw_tensorPowerKroneckerTwo_kronecker_one_tensorPower
    {α : Type*} {β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : CMatrix α) :
    tensorPowerKroneckerTwo (a := Prod α β) (Matrix.kronecker A (1 : CMatrix β)) =
      twoCopySideOperator (a := α) (e := β) (tensorPowerKroneckerTwo (a := α) A)
        (tensorPowerKroneckerTwo (a := β) (1 : CMatrix β)) := by
  ext x y
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.kronecker,
    tensorPowerKroneckerTwo, fqsw_tensorPowerProdEquiv_fst_apply]
  rw [fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 x 0,
    fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 y 0,
    fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 x 1,
    fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 y 1]
  ring

/-- Two-copy Kronecker for `A ⊗ I`, with the identity tensor power simplified. -/
private theorem fqsw_tensorPowerKroneckerTwo_kronecker_one
    {α : Type*} {β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : CMatrix α) :
    tensorPowerKroneckerTwo (a := Prod α β) (Matrix.kronecker A (1 : CMatrix β)) =
      twoCopySideOperator (a := α) (e := β) (tensorPowerKroneckerTwo (a := α) A)
        (1 : CMatrix (TensorPower β 2)) := by
  rw [fqsw_tensorPowerKroneckerTwo_kronecker_one_tensorPower,
    fqsw_tensorPowerKroneckerTwo_one]

/-- Enumerate a two-copy tensor power by its first and second tensor words. -/
private theorem fqsw_sum_tensorPower_twoCopyTensorWord
    {α : Type*} [Fintype α] {β : Type*} [AddCommMonoid β]
    (f : TensorPower α 2 → β) :
    (∑ x : TensorPower α 2, f x) =
      ∑ i : α, ∑ j : α, f (twoCopyTensorWord (a := α) i j) := by
  let E : (α × α) ≃ TensorPower α 2 :=
  { toFun p := twoCopyTensorWord (a := α) p.1 p.2
    invFun x :=
      (tensorPowerEquiv (a := α) 2 x 0, tensorPowerEquiv (a := α) 2 x 1)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro x
      exact (twoCopyTensorWord_coords (a := α) x).symm }
  calc
    (∑ x : TensorPower α 2, f x) =
        ∑ p : α × α, f (E p) := by
          exact (Fintype.sum_equiv E
            (fun p : α × α => f (E p))
            (fun x : TensorPower α 2 => f x)
            (fun _ => rfl)).symm
    _ = ∑ i : α, ∑ j : α, f (twoCopyTensorWord (a := α) i j) := by
          rw [Fintype.sum_prod_type]
          rfl

private theorem fqsw_partialTraceA_flip_entry_sum
    {α : Type*} {β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (ρ : CMatrix (Prod α β))
    (i j : α) (k l : β) :
    (∑ x : α, ∑ x_1 : β, ∑ x_2 : α, ∑ x_3 : β,
      if x_3 = k ∧ x_1 = l then
        if x = i ∧ x_2 = j then
          ρ (i, k) (x, x_1) * ρ (j, l) (x_2, x_3)
        else 0
      else 0) =
      ρ (i, k) (i, l) * ρ (j, l) (j, k) := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro x _ hx
          simp [hx]
        · intro h
          exact False.elim (h (Finset.mem_univ k))
      · intro x _ hx
        simp [hx]
      · intro h
        exact False.elim (h (Finset.mem_univ j))
    · intro x _ hx
      simp [hx]
    · intro h
      exact False.elim (h (Finset.mem_univ l))
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

private theorem fqsw_partialTraceA_flip_entry_sum_prod
    {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (ρ : CMatrix (Prod α (Prod β γ)))
    (i j : α) (k l : β) (s t : γ) :
    (∑ x : α, ∑ x_1 : β, ∑ x_2 : γ, ∑ x_3 : α, ∑ x_4 : β, ∑ x_5 : γ,
      if (x_4 = k ∧ x_5 = s) ∧ x_1 = l ∧ x_2 = t then
        if x = i ∧ x_3 = j then
          ρ (i, (k, s)) (x, (x_1, x_2)) *
            ρ (j, (l, t)) (x_3, (x_4, x_5))
        else 0
      else 0) =
      ρ (i, (k, s)) (i, (l, t)) * ρ (j, (l, t)) (j, (k, s)) := by
  simpa [Fintype.sum_prod_type, and_assoc] using
    fqsw_partialTraceA_flip_entry_sum
      (α := α) (β := Prod β γ) ρ i j (k, s) (l, t)

private theorem fqsw_nested_split_flip_entry_sum
    {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (ρ : CMatrix (Prod (Prod α β) γ))
    (i j : α) (k l : β) (s t : γ) :
    (∑ x : α, ∑ x_1 : β, ∑ x_2 : γ, ∑ x_3 : α, ∑ x_4 : β, ∑ x_5 : γ,
      if x_5 = s ∧ x_2 = t then
        if x_4 = k ∧ x_1 = l then
          if x = i ∧ x_3 = j then
            ρ ((i, k), s) ((x, x_1), x_2) *
              ρ ((j, l), t) ((x_3, x_4), x_5)
          else 0
        else 0
      else 0) =
      ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s) := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single k]
          · rw [Finset.sum_eq_single s]
            · simp
            · intro x _ hx
              simp [hx]
            · intro h
              exact False.elim (h (Finset.mem_univ s))
          · intro x _ hx
            simp [hx]
          · intro h
            exact False.elim (h (Finset.mem_univ k))
        · intro x _ hx
          simp [hx]
        · intro h
          exact False.elim (h (Finset.mem_univ j))
      · intro x _ hx
        simp [hx]
      · intro h
        exact False.elim (h (Finset.mem_univ t))
    · intro x _ hx
      simp [hx]
    · intro h
      exact False.elim (h (Finset.mem_univ l))
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

/-- Tracing out the left factor of the identity on `q × e` gives
`|q| I_e`. -/
theorem fqsw_partialTraceA_one_prod
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [DecidableEq e] :
    partialTraceA (a := q) (b := e) (1 : CMatrix (Prod q e)) =
      ((Fintype.card q : ℂ) • (1 : CMatrix e)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceA]
  · simp [partialTraceA, hij]

/-- Tracing out the right factor of the identity on `q × e` gives
`|e| I_q`. -/
theorem fqsw_partialTraceB_one_prod
    {q : Type x} {e : Type y} [Fintype e] [DecidableEq q] [DecidableEq e] :
    partialTraceB (a := q) (b := e) (1 : CMatrix (Prod q e)) =
      ((Fintype.card e : ℂ) • (1 : CMatrix q)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceB]
  · simp [partialTraceB, hij]

/-- Source trace term
`Tr(I^{A₁A₁'} ⊗ F^{A₂}) = d_{A₁}² d_{A₂}` from ADHW fqsw.tex
lines 656-666. -/
theorem fqsw_twoCopySideOperator_one_swap_trace
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] :
    (twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))).trace =
    ((Fintype.card q : ℂ) * (Fintype.card q : ℂ) * (Fintype.card e : ℂ)) := by
  have h := tensorPowerKroneckerTwo_prod_mul_one_swap_trace
    (a := q) (e := e) (rho := (1 : CMatrix (Prod q e)))
  rw [fqsw_tensorPowerKroneckerTwo_one, Matrix.one_mul] at h
  rw [h]
  rw [fqsw_partialTraceA_one_prod]
  simp [Matrix.trace_smul, Matrix.trace_one]
  ring

/-- Source trace term
`Tr(F^{A₁} ⊗ I^{A₂A₂'}) = d_{A₁} d_{A₂}²` from ADHW fqsw.tex
lines 656-666. -/
theorem fqsw_twoCopySideOperator_swap_one_trace
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] :
    (twoCopySideOperator (a := q) (e := e)
      (tensorPowerSwapMatrix_two (a := q))
      (1 : CMatrix (TensorPower e 2))).trace =
    ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) * (Fintype.card e : ℂ)) := by
  have h := tensorPowerKroneckerTwo_prod_mul_swap_one_trace
    (a := q) (e := e) (rho := (1 : CMatrix (Prod q e)))
  rw [fqsw_tensorPowerKroneckerTwo_one, Matrix.one_mul] at h
  rw [h]
  rw [fqsw_partialTraceB_one_prod]
  simp [Matrix.trace_smul, Matrix.trace_one]
  ring

/-- Matrix entries of the finite-dimensional unitary group are continuous. -/
@[fun_prop, continuity]
theorem unitaryGroup_entry_continuous
    {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    Continuous fun U : Matrix.unitaryGroup α ℂ => (U : CMatrix α) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-- The ADHW decoupling marginal `σ^{A₂R}(U)` is continuous as a matrix-valued
function of the Haar unitary. -/
theorem adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix := by
  refine continuous_matrix ?_
  intro x y
  unfold adhwFQSWSigmaA2RStateOfIsometry
    adhwFQSWPostAliceStateOfIsometry
    adhwFQSWAliceIsometryOfSplitUnitary
    adhwFQSWAliceIsometryOfSplit
    ReferenceIsometry.comp
    ReferenceUnitary.toReferenceIsometry
    ReferenceIsometry.ofEquiv
    ReferenceIsometry.applyPureVector
    ReferenceIsometry.applyAmp
    PureVector.state
    State.reindex
    State.marginalB
    partialTraceA
    rankOneMatrix
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mulVec,
    Matrix.vecMulVec_apply, dotProduct]
  continuity

/-- The ADHW marginal `σ^{A₂}(U)` is continuous as a matrix-valued function of
the Haar unitary. -/
theorem adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix := by
  unfold adhwFQSWSigmaA2StateOfIsometry State.marginalA
  exact partialTraceB_continuous_matrix.comp
    (adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split)

/-- The FQSW split-unitary decoupling integrand is continuous in the Haar
unitary. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary traceDistance
  exact traceNorm_continuous.comp
    ((adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The FQSW split-unitary decoupling integrand is Haar-integrable. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := Prod q e)) :=
  (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The squared FQSW split-unitary decoupling integrand is Haar-integrable. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := Prod q e)) :=
  ((adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The product-decoupling ADHW integrand is continuous in the Haar unitary. -/
theorem adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U := by
  have hsigmaA2R := adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split
  have hprod : Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).prod
          (adhwFQSWSigmaRState ψ)).matrix) := by
    have hsigmaA2 := adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split
    refine continuous_matrix ?_
    intro i j
    simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
    continuity
  unfold adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary traceDistance
  exact traceNorm_continuous.comp (hsigmaA2R.sub hprod)

/-- The squared product-decoupling ADHW integrand is Haar-integrable. -/
theorem adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := Prod q e)) :=
  ((adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The max-mixed `A₂` ADHW integrand is continuous in the Haar unitary. -/
theorem adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary traceDistance
  exact traceNorm_continuous.comp
    ((adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The squared max-mixed `A₂` ADHW integrand is Haar-integrable. -/
theorem adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := Prod q e)) :=
  ((adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The product-decoupling Hilbert--Schmidt integrand is continuous in the
Haar unitary. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  have hsigmaA2R := adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split
  have hprod : Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).prod
          (adhwFQSWSigmaRState ψ)).matrix) := by
    have hsigmaA2 := adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split
    refine continuous_matrix ?_
    intro i j
    simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
    continuity
  unfold adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary
  exact hilbertSchmidtSq_continuous_matrix.comp (hsigmaA2R.sub hprod)

/-- The max-mixed `A₂` Hilbert--Schmidt integrand is continuous in the Haar
unitary. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary
  exact hilbertSchmidtSq_continuous_matrix.comp
    ((adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The product-decoupling Hilbert--Schmidt integrand is Haar-integrable. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := Prod q e)) :=
  (adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The max-mixed `A₂` Hilbert--Schmidt integrand is Haar-integrable. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := Prod q e)) :=
  (adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- ADHW fqsw.tex lines 751-754: pointwise Cauchy--Schwarz bridge from the
product-decoupling trace norm to the Hilbert--Schmidt square on `A₂R`. -/
theorem adhwFQSWProductDecouplingTraceNormSq_le_card_mul_hilbertSchmidt
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
      ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  let Δ : CMatrix (Prod e r) :=
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix -
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
        (adhwFQSWSigmaRState ψ)).matrix)
  have h := traceNorm_sq_le_card_mul_hilbertSchmidtSq Δ
  simpa [adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary,
    adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary,
    traceDistance, Δ, alice, Fintype.card_prod] using h

/-- ADHW fqsw.tex lines 776-780: pointwise Cauchy--Schwarz bridge from the
max-mixed `A₂` trace norm to the Hilbert--Schmidt square on `A₂`. -/
theorem adhwFQSWMaxMixedA2TraceNormSq_le_card_mul_hilbertSchmidt
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
      (Fintype.card e : ℝ) *
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  let Δ : CMatrix e :=
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix -
      (adhwFQSWMaximallyMixedA2State e).matrix
  have h := traceNorm_sq_le_card_mul_hilbertSchmidtSq Δ
  simpa [adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary,
    adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary,
    traceDistance, Δ] using h

/-- Integral form of the ADHW product-decoupling Cauchy--Schwarz tail.  The
remaining source-route task is the exact Hilbert--Schmidt average of
fqsw.tex lines 682-747. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
  have hpoint : ∀ᵐ U : Matrix.unitaryGroup (Prod q e) ℂ
      ∂unitaryHaarMeasure (a := Prod q e),
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
    filter_upwards with U
    exact adhwFQSWProductDecouplingTraceNormSq_le_card_mul_hilbertSchmidt ψ split U
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e) :=
        MeasureTheory.integral_mono_ae
          (adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
          ((adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_integrable
            ψ split).const_mul ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)))
          hpoint
    _ = ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
          rw [MeasureTheory.integral_const_mul]

/-- Integral form of the ADHW max-mixed `A₂` Cauchy--Schwarz tail.  The
remaining source-route task is the exact one-copy `A₂` Hilbert--Schmidt
average from fqsw.tex lines 781-787. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
  have hpoint : ∀ᵐ U : Matrix.unitaryGroup (Prod q e) ℂ
      ∂unitaryHaarMeasure (a := Prod q e),
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
        (Fintype.card e : ℝ) *
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
    filter_upwards with U
    exact adhwFQSWMaxMixedA2TraceNormSq_le_card_mul_hilbertSchmidt ψ split U
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        (Fintype.card e : ℝ) *
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e) :=
        MeasureTheory.integral_mono_ae
          (adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
          ((adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_integrable
            ψ split).const_mul (Fintype.card e : ℝ))
          hpoint
    _ = (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
          rw [MeasureTheory.integral_const_mul]

/-- ADHW fqsw.tex lines 806-815: after the pointwise triangle-inequality
comparison has related the final decoupling integrand to the product-decoupling
and max-mixed integrands, the averaged square is bounded by twice the two
component averaged squares.  The upstream source-route tasks are the pointwise
trace-norm comparison and the two Schur/HS average estimates. -/
theorem adhwFQSWCombinedTraceNormAverageSq_le_two_component_averages
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) +
      2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) := by
  exact integral_sq_le_two_add_two_of_ae_le_add
    (μ := unitaryHaarMeasure (a := Prod q e))
    (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
    (g := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
    (h := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U)
    (by
      filter_upwards with U
      exact traceDistance_nonneg _ _)
    (by
      filter_upwards with U
      exact traceDistance_nonneg _ _)
    (by
      filter_upwards with U
      exact traceDistance_nonneg _ _)
    (by
      filter_upwards with U
      exact adhwFQSWDecouplingTraceNormIntegrand_le_product_add_maxMixed ψ split U)
    (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
    (adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
    (adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)

/-- Finite-sum factorization used by the FQSW product-purification
calculation. -/
theorem fqsw_sum_sum_sum_mul_right
    {ι : Type u} {κ : Type v} {lam : Type w} [Fintype ι] [Fintype κ] [Fintype lam]
    (f : ι → κ → ℂ) (g : lam → ℂ) :
    (∑ i : ι, ∑ j : κ, ∑ k : lam, f i j * g k) =
      (∑ k : lam, g k) * (∑ i : ι, ∑ j : κ, f i j) := by
  calc
    (∑ i : ι, ∑ j : κ, ∑ k : lam, f i j * g k) =
        ∑ i : ι, ∑ j : κ, f i j * (∑ k : lam, g k) := by
      simp [Finset.mul_sum]
    _ = (∑ i : ι, ∑ j : κ, f i j) * (∑ k : lam, g k) := by
      simp [Finset.sum_mul]
    _ = (∑ k : lam, g k) * (∑ i : ι, ∑ j : κ, f i j) := by
      ring

/-- Trace distance is invariant under simultaneous finite reindexing. -/
theorem fqsw_traceDistance_submatrix_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (E : α ≃ β) (M N : CMatrix α) :
    traceDistance (M.submatrix E.symm E.symm) (N.submatrix E.symm E.symm) =
      traceDistance M N := by
  rw [traceDistance, traceDistance]
  have hsub :
      M.submatrix E.symm E.symm - N.submatrix E.symm E.symm =
        (M - N).submatrix E.symm E.symm := by
    ext i j
    rfl
  rw [hsub]
  exact traceNorm_submatrix_equiv E.symm (M - N)

namespace State

/-- Normalized trace distance is invariant under state reindexing. -/
theorem normalizedTraceDistance_reindex_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ σ : State α) (E : α ≃ β) :
    (ρ.reindex E).normalizedTraceDistance (σ.reindex E) =
      ρ.normalizedTraceDistance σ := by
  change (1 / 2 : ℝ) *
      QIT.traceDistance (ρ.matrix.submatrix E.symm E.symm) (σ.matrix.submatrix E.symm E.symm) =
    (1 / 2 : ℝ) * QIT.traceDistance ρ.matrix σ.matrix
  rw [fqsw_traceDistance_submatrix_equiv E ρ.matrix σ.matrix]

end State

/-- Regroup the ideal FQSW target
`ψ^{R\widehat B} ⊗ Φ^{A₂\widetilde B}` as a purification of the decoupling
target on `A₂R`, with `\widehat B\widetilde B` as the reference. -/
def fqswIdealTargetToA2RPurificationEquiv
    (a : Type u) (b : Type v) (r : Type w) (e : Type y) (et : Type z) :
    Prod (Prod (Prod a b) r) (Prod e et) ≃
      Prod (Prod (Prod a b) et) (Prod e r) where
  toFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- The ideal ADHW target, regrouped as a purification of
`I^{A₂}/d_{A₂} ⊗ σ^R`. -/
def adhwFQSWIdealA2RPurification
    (ψ : PureVector (Prod (Prod a b) r)) (pairing : e ≃ et) :
    PureVector (Prod (Prod (Prod a b) et) (Prod e r)) :=
  (ψ.prod (maximallyEntangledPureVector pairing)).reindex
    (fqswIdealTargetToA2RPurificationEquiv a b r e et)

/-- The ideal ADHW target purifies the decoupling target
`I^{A₂}/d_{A₂} ⊗ σ^R`. -/
theorem adhwFQSWIdealA2RPurification_purifies
    (ψ : PureVector (Prod (Prod a b) r)) (pairing : e ≃ et) :
    (adhwFQSWIdealA2RPurification ψ pairing).Purifies
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) := by
  rw [PureVector.purifies_iff]
  ext x y
  simp only [adhwFQSWIdealA2RPurification, fqswIdealTargetToA2RPurificationEquiv,
    PureVector.reindex_state, PureVector.prod_state, State.reindex,
    State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply, partialTraceA,
    adhwFQSWMaximallyMixedA2State,
    adhwFQSWSigmaRState_eq_source_marginalB, State.marginalB,
    Fintype.sum_prod_type]
  have hebit :
      (∑ k : et,
        (maximallyEntangledPureVector pairing).amp (x.1, k) *
          (starRingEnd ℂ) ((maximallyEntangledPureVector pairing).amp (y.1, k))) =
        (adhwFQSWMaximallyMixedState e).matrix x.1 y.1 := by
    have h := congrArg (fun ρ : State e => ρ.matrix x.1 y.1)
      (maximallyEntangledPureVector_marginalA pairing)
    simpa [State.marginalA, partialTraceB, PureVector.state, rankOneMatrix_apply] using h
  exact
    (fqsw_sum_sum_sum_mul_right
      (fun i : a => fun j : b =>
        ψ.amp ((i, j), x.2) * (starRingEnd ℂ) (ψ.amp ((i, j), y.2)))
      (fun k : et =>
        (maximallyEntangledPureVector pairing).amp (x.1, k) *
          (starRingEnd ℂ) ((maximallyEntangledPureVector pairing).amp (y.1, k)))).trans
      (by rw [hebit]; simp [PureVector.state, rankOneMatrix_apply])

/-- Reindexing the computed FQSW output into `A₂R` purification order is the
same pure vector as applying Bob's isometry to the post-Alice purification. -/
theorem fqsw_outputPureVector_reindex_a2r_eq_apply_postAlice
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e))
    (V : ReferenceIsometry (Prod q b) (Prod (Prod a b) et))
    (pairing : e ≃ et) :
    (({ aliceIsometry := U, bobIsometry := V, ebitPairing := pairing } :
        FQSWOneShotProtocol ψ q e et).outputPureVector.reindex
          (fqswIdealTargetToA2RPurificationEquiv a b r e et)) =
      V.applyPureVector
        (adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U) := by
  apply PureVector.ext_amp
  funext x
  simp [FQSWOneShotProtocol.outputPureVector,
    adhwFQSWPostAliceA2RPurificationOfIsometry,
    fqswSourceToAliceInputEquiv, fqswAliceOutputToBobInputEquiv,
    fqswAliceOutputToA2REquiv, fqswBobOutputToFinalEquiv,
    fqswIdealTargetToA2RPurificationEquiv, ReferenceIsometry.applyPureVector,
    ReferenceIsometry.applyAmp, Matrix.mulVec]

/-- Uhlmann assembly for the ADHW one-shot route: a concrete Alice isometry
whose `A₂R` decoupling marginal is close to `I^{A₂}/d_{A₂} ⊗ σ^R` supplies a
computed FQSW one-shot protocol with the corresponding source trace-norm
error bound. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_decoupling
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) (pairing : e ≃ et) (η : ℝ)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) et))
    (hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤ η) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ 2 * Real.sqrt (2 * η) := by
  let post := adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U
  let ideal := adhwFQSWIdealA2RPurification ψ pairing
  let targetState : State (Prod e r) :=
    (adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)
  have hpost : post.Purifies
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U) := by
    simpa [post] using
      (adhwFQSWPostAliceA2RPurificationOfIsometry_purifies
        (q := q) (e := e) ψ U)
  have hideal : ideal.Purifies targetState := by
    simpa [ideal, targetState] using
      (adhwFQSWIdealA2RPurification_purifies ψ pairing)
  obtain ⟨V, hV⟩ :=
    PureVector.exists_referenceIsometry_applyPureVector_normalizedTraceDistance_le_sqrt_two_mul_normalizedTraceDistance
      hpost hideal hcardTarget hcardRef
  let C : FQSWOneShotProtocol ψ q e et :=
    { aliceIsometry := U, bobIsometry := V, ebitPairing := pairing }
  refine ⟨C, ?_⟩
  have hVη :
      (V.applyPureVector post).state.normalizedTraceDistance ideal.state ≤
        Real.sqrt (2 * η) := by
    refine le_trans hV ?_
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdec (by norm_num))
  let E := fqswIdealTargetToA2RPurificationEquiv a b r e et
  have hpure :
      C.outputPureVector.reindex E = V.applyPureVector post := by
    simpa [C, post, E] using
      (fqsw_outputPureVector_reindex_a2r_eq_apply_postAlice ψ U V pairing)
  have hout :
      C.outputState.reindex E = (V.applyPureVector post).state := by
    change C.outputPureVector.state.reindex E = (V.applyPureVector post).state
    exact (PureVector.reindex_state C.outputPureVector E).symm.trans
      (congrArg PureVector.state hpure)
  have htarget :
      C.targetState.reindex E = ideal.state := by
    calc
      C.targetState.reindex E =
          (ψ.prod (maximallyEntangledPureVector pairing)).state.reindex E := by
        simp [C, FQSWOneShotProtocol.targetState, PureVector.prod_state]
      _ = ((ψ.prod (maximallyEntangledPureVector pairing)).reindex E).state := by
        exact (PureVector.reindex_state (ψ.prod (maximallyEntangledPureVector pairing)) E).symm
      _ = ideal.state := by
        simp [ideal, E, adhwFQSWIdealA2RPurification]
  have hnorm_eq :
      C.normalizedError =
        (V.applyPureVector post).state.normalizedTraceDistance ideal.state := by
    rw [FQSWOneShotProtocol.normalizedError]
    rw [← State.normalizedTraceDistance_reindex_equiv C.outputState C.targetState E]
    rw [hout, htarget]
  have hnorm_le : C.normalizedError ≤ Real.sqrt (2 * η) := by
    rw [hnorm_eq]
    exact hVη
  have hhalf := C.normalizedError_eq_half_traceNormError
  have htrace_nonneg := C.traceNormError_nonneg
  nlinarith

/-- Purity `Tr[(ψ^{AR})^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWARPurity (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).matrix)

/-- For a Hermitian PSD matrix, the Hilbert--Schmidt square is its PSD
power trace at `p = 2`. -/
private theorem fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (M : CMatrix α) (hM : M.PosSemidef) :
    hilbertSchmidtSq M = psdTracePower M hM (2 : ℝ) := by
  unfold hilbertSchmidtSq
  rw [psdTracePower_two]
  have hstar : star M = M := by
    simpa [Matrix.star_eq_conjTranspose] using hM.isHermitian.eq
  rw [hstar]

/-- Rectangular reference isometries preserve Hilbert--Schmidt purity under
PSD conjugation. -/
theorem referenceIsometry_hilbertSchmidtSq_conj
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (V : ReferenceIsometry α β) (ρ : State α) :
    hilbertSchmidtSq (V.matrix * ρ.matrix * Matrix.conjTranspose V.matrix) =
      hilbertSchmidtSq ρ.matrix := by
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    (V.matrix * ρ.matrix * Matrix.conjTranspose V.matrix)
    (ρ.pos.mul_mul_conjTranspose_same V.matrix)]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two ρ.matrix ρ.pos]
  exact psdTracePower_isometry_conj V.matrix ρ.pos V.isometry
    (by norm_num : (0 : ℝ) < 2)

/-- The ADHW `AR` purity equals the complementary source `B` purity.  This is
the pure-state Hilbert--Schmidt bridge used to identify the line-1158 source
purity term in ADHW's i.i.d. proof. -/
theorem adhwFQSWARPurity_eq_systemBPurity
    (ψ : PureVector (Prod (Prod a b) r)) :
    adhwFQSWARPurity ψ =
      hilbertSchmidtSq ψ.state.marginalA.marginalB.matrix := by
  let Ω : PureVector (Prod (Prod a r) b) :=
    ψ.reindex (fqswSourceToARBEquiv a b r)
  have hΩA : Ω.state.marginalA = adhwFQSWARState ψ := by
    apply State.ext
    ext i j
    simp [Ω, adhwFQSWARState, State.stateMergingReferenceState,
      fqswSourceToARBEquiv, PureVector.reindex_state, State.reindex,
      State.marginalA, partialTraceB, PureVector.state_matrix, rankOneMatrix_apply]
  have hΩB : Ω.state.marginalB = ψ.state.marginalA.marginalB := by
    apply State.ext
    ext i j
    simp [Ω, fqswSourceToARBEquiv, PureVector.reindex_state, State.reindex,
      State.marginalB, State.marginalA, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type]
  have hdual :=
    PureVector.psdTracePower_marginalA_eq_marginalB
      (Ψ := Ω) (p := (2 : ℝ)) (by norm_num)
  rw [adhwFQSWARPurity]
  rw [← hΩA, ← hΩB]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    Ω.state.marginalA.matrix Ω.state.marginalA.pos]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    Ω.state.marginalB.matrix Ω.state.marginalB.pos]
  simpa [PureVector.state, State.marginalA, State.marginalB] using hdual

/-- Purity `Tr[(ψ^A)^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWAPurity (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).marginalA.matrix)

/-- Purity `Tr[(ψ^R)^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWRPurity (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).marginalB.matrix)

/-- The overlap `Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]` appearing in the exact
Hilbert--Schmidt calculation of ADHW fqsw.tex lines 682-747. -/
def adhwFQSWARProductOverlap (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  ((adhwFQSWARState ψ).matrix *
      ((adhwFQSWARState ψ).marginalA.prod (adhwFQSWARState ψ).marginalB).matrix).trace.re

/-- The overlap term
`Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]` in ADHW fqsw.tex lines 682-747 is nonnegative:
both factors are positive semidefinite states. -/
theorem adhwFQSWARProductOverlap_nonneg
    (ψ : PureVector (Prod (Prod a b) r)) :
    0 ≤ adhwFQSWARProductOverlap ψ := by
  unfold adhwFQSWARProductOverlap
  exact cMatrix_trace_mul_posSemidef_re_nonneg
    (adhwFQSWARState ψ).pos
    (((adhwFQSWARState ψ).marginalA).prod
      ((adhwFQSWARState ψ).marginalB)).pos

/-- The split `A` marginal still has trace one. -/
theorem adhwFQSWASplitMatrix_trace
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (adhwFQSWASplitMatrix ψ split).trace = 1 := by
  unfold adhwFQSWASplitMatrix
  rw [fqsw_trace_submatrix_equiv split.symm]
  exact (adhwFQSWARState ψ).marginalA.trace_eq_one

/-- The split `A` marginal has the same purity as the source `A` marginal. -/
theorem adhwFQSWASplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq (adhwFQSWASplitMatrix ψ split) = adhwFQSWAPurity ψ := by
  unfold adhwFQSWASplitMatrix adhwFQSWAPurity
  rw [fqsw_hilbertSchmidtSq_submatrix_equiv split]

/-- The split `AR` matrix has the same purity as the source `AR` marginal. -/
theorem adhwFQSWARSplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq (adhwFQSWARSplitMatrix ψ split) = adhwFQSWARPurity ψ := by
  unfold adhwFQSWARSplitMatrix adhwFQSWARPurity
  rw [fqsw_hilbertSchmidtSq_submatrix_equiv (fqswARSplitEquiv split)]

/-- The split product matrix is the source product state reindexed by the
ADHW split on Alice's register. -/
theorem adhwFQSWARProductSplitMatrix_eq_source_product_submatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    adhwFQSWARProductSplitMatrix ψ split =
      (((adhwFQSWARState ψ).marginalA.prod
        (adhwFQSWARState ψ).marginalB).matrix).submatrix
        (fqswARSplitEquiv split).symm (fqswARSplitEquiv split).symm := by
  ext x y
  simp [adhwFQSWARProductSplitMatrix, adhwFQSWASplitMatrix,
    adhwFQSWSigmaRState, State.prod, fqswARSplitEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

/-- The split product matrix has Hilbert--Schmidt square
`Tr[(ψ^A)^2] Tr[(ψ^R)^2]`. -/
theorem adhwFQSWARProductSplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq (adhwFQSWARProductSplitMatrix ψ split) =
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
  unfold adhwFQSWARProductSplitMatrix adhwFQSWRPurity adhwFQSWSigmaRState
  rw [fqsw_hilbertSchmidtSq_kronecker]
  rw [adhwFQSWASplitMatrix_hilbertSchmidtSq]

/-- The split overlap is the source overlap
`Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]`. -/
theorem adhwFQSWARProductSplitMatrix_overlap
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (adhwFQSWARSplitMatrix ψ split *
        adhwFQSWARProductSplitMatrix ψ split).trace.re =
      adhwFQSWARProductOverlap ψ := by
  let E : Prod (Prod q e) r ≃ Prod a r :=
    (fqswARSplitEquiv (r := r) split).symm
  have hprod :=
    adhwFQSWARProductSplitMatrix_eq_source_product_submatrix ψ split
  unfold adhwFQSWARProductOverlap adhwFQSWARSplitMatrix
  rw [hprod]
  change (((adhwFQSWARState ψ).matrix.submatrix E E *
        (((adhwFQSWARState ψ).marginalA.prod
          (adhwFQSWARState ψ).marginalB).matrix).submatrix E E).trace).re =
    (((adhwFQSWARState ψ).matrix *
      ((adhwFQSWARState ψ).marginalA.prod
        (adhwFQSWARState ψ).marginalB).matrix).trace).re
  rw [fqsw_mul_submatrix_equiv E]
  rw [fqsw_trace_submatrix_equiv E]

/-- Tracing the split `AR` source matrix over `A₁A₂` recovers the fixed
reference marginal `σ^R`. -/
theorem adhwFQSWARSplitMatrix_partialTraceA
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    partialTraceA (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).matrix := by
  ext i j
  unfold adhwFQSWARSplitMatrix adhwFQSWSigmaRState
  change
    (∑ x : Prod q e,
      (adhwFQSWARState ψ).matrix (split.symm x, i) (split.symm x, j)) =
    ∑ y : a, (adhwFQSWARState ψ).matrix (y, i) (y, j)
  exact Fintype.sum_equiv split.symm
    (fun x : Prod q e =>
      (adhwFQSWARState ψ).matrix (split.symm x, i) (split.symm x, j))
    (fun y : a => (adhwFQSWARState ψ).matrix (y, i) (y, j))
    (fun _ => rfl)

/-- Tracing the split `AR` source matrix over `R` recovers the split
`A₁A₂` source marginal. -/
theorem adhwFQSWARSplitMatrix_partialTraceB
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    partialTraceB (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      adhwFQSWASplitMatrix ψ split := by
  ext i j
  unfold adhwFQSWARSplitMatrix adhwFQSWASplitMatrix
  rw [State.marginalA_matrix]
  rfl

/-- Tracing the split product matrix over `A₁A₂` also recovers the same
reference marginal `σ^R`. -/
theorem adhwFQSWARProductSplitMatrix_partialTraceA
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    partialTraceA (a := Prod q e) (b := r)
        (adhwFQSWARProductSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).matrix := by
  unfold adhwFQSWARProductSplitMatrix
  rw [partialTraceA_kronecker]
  rw [adhwFQSWASplitMatrix_trace]
  exact matrixScale_one (adhwFQSWSigmaRState ψ).matrix

/-- If the split Alice system `A₁ × A₂` is a one-point system, the source
correlation matrix `ψ^{AR} - ψ^A ⊗ ψ^R` is zero. -/
theorem adhwFQSWARCorrelationSplitMatrix_eq_zero_of_subsingleton
    [Subsingleton (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    adhwFQSWARSplitMatrix ψ split -
      adhwFQSWARProductSplitMatrix ψ split = 0 := by
  apply sub_eq_zero.mpr
  let ρsplit : State (Prod (Prod q e) r) :=
    (adhwFQSWARState ψ).reindex (fqswARSplitEquiv split)
  have hprod := state_matrix_eq_prod_marginals_of_subsingleton_left ρsplit
  have hρmatrix : ρsplit.matrix = adhwFQSWARSplitMatrix ψ split := by
    rfl
  have hAmatrix : ρsplit.marginalA.matrix = adhwFQSWASplitMatrix ψ split := by
    rw [State.marginalA_matrix]
    change partialTraceB (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      adhwFQSWASplitMatrix ψ split
    exact adhwFQSWARSplitMatrix_partialTraceB ψ split
  have hBmatrix : ρsplit.marginalB.matrix = (adhwFQSWSigmaRState ψ).matrix := by
    rw [State.marginalB_matrix]
    change partialTraceA (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).matrix
    exact adhwFQSWARSplitMatrix_partialTraceA ψ split
  calc
    adhwFQSWARSplitMatrix ψ split = ρsplit.matrix := hρmatrix.symm
    _ = (ρsplit.marginalA.prod ρsplit.marginalB).matrix := hprod
    _ = adhwFQSWARProductSplitMatrix ψ split := by
      ext x y
      simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
        adhwFQSWARProductSplitMatrix]
      rw [← State.marginalA_matrix ρsplit, hAmatrix]
      rw [← State.marginalB_matrix ρsplit, hBmatrix]

/-- Source ADHW correlation matrix
`ψ^{AR} - ψ^A ⊗ ψ^R`, reindexed by the split, has the source Hilbert--Schmidt
expansion from fqsw.tex lines 682-747. -/
theorem adhwFQSWARCorrelationSplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq
      (adhwFQSWARSplitMatrix ψ split -
        adhwFQSWARProductSplitMatrix ψ split) =
      adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
        adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
  let Rm : CMatrix (Prod (Prod q e) r) := adhwFQSWARSplitMatrix ψ split
  let Pm : CMatrix (Prod (Prod q e) r) := adhwFQSWARProductSplitMatrix ψ split
  have hRm_herm : Rm.IsHermitian := by
    unfold Rm adhwFQSWARSplitMatrix
    exact fqsw_isHermitian_submatrix_equiv (fqswARSplitEquiv split).symm
      (adhwFQSWARState ψ).pos.isHermitian
  have hPm_herm : Pm.IsHermitian := by
    unfold Pm adhwFQSWARProductSplitMatrix
    exact kronecker_isHermitian _ _
      (fqsw_isHermitian_submatrix_equiv split.symm
        (adhwFQSWARState ψ).marginalA.pos.isHermitian)
      (adhwFQSWSigmaRState ψ).pos.isHermitian
  have hRm_sq : (Rm * Rm).trace.re = adhwFQSWARPurity ψ := by
    calc
      (Rm * Rm).trace.re = hilbertSchmidtSq Rm := by
        exact (fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian Rm hRm_herm).symm
      _ = adhwFQSWARPurity ψ := by
        simpa [Rm] using adhwFQSWARSplitMatrix_hilbertSchmidtSq ψ split
  have hPm_sq : hilbertSchmidtSq Pm =
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    simpa [Pm] using adhwFQSWARProductSplitMatrix_hilbertSchmidtSq ψ split
  have hOverlap : (Rm * Pm).trace.re = adhwFQSWARProductOverlap ψ := by
    simpa [Rm, Pm] using adhwFQSWARProductSplitMatrix_overlap ψ split
  rw [show adhwFQSWARSplitMatrix ψ split -
        adhwFQSWARProductSplitMatrix ψ split = Rm - Pm by rfl]
  rw [fqsw_hilbertSchmidtSq_sub_of_isHermitian Rm Pm hRm_herm hPm_herm]
  rw [hRm_sq, hPm_sq, hOverlap]

/-- Schur coefficient `p = (d_A1 + d_A2) / (d_A + 1)` from ADHW fqsw.tex
lines 642-678. -/
def adhwFQSWSchurPCoeff (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ℝ :=
  ((Fintype.card q : ℝ) + (Fintype.card e : ℝ)) /
    (((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) + 1)

/-- Schur coefficient `q = (d_A1 - d_A2) / (d_A - 1)` from ADHW fqsw.tex
lines 642-678. -/
def adhwFQSWSchurQCoeff (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ℝ :=
  ((Fintype.card q : ℝ) - (Fintype.card e : ℝ)) /
    (((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) - 1)

/-- Source Schur coefficient estimate:
`(p + q)/2 ≤ 1/d_{A₂}`. -/
theorem adhwFQSWSchur_half_sum_le_inv_card_e
    (q : Type x) (e : Type y) [Fintype q] [Fintype e]
    [Nonempty q] [Nonempty e] [Nontrivial (Prod q e)] :
    (adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2 ≤
      (1 : ℝ) / (Fintype.card e : ℝ) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_gt : 1 < dq * de := by
    have hnat : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    dsimp [dq, de]
    exact_mod_cast hnat
  have hde_pos : 0 < de := lt_of_lt_of_le zero_lt_one hde_ge_one
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by nlinarith
  have hden_pos' : 0 < de ^ 2 * dq ^ 2 - 1 := by nlinarith
  have hden_ne_norm : -1 + dq ^ 2 * de ^ 2 ≠ 0 := by
    nlinarith
  unfold adhwFQSWSchurPCoeff adhwFQSWSchurQCoeff
  change ((dq + de) / (dq * de + 1) + (dq - de) / (dq * de - 1)) / 2 ≤ 1 / de
  have hsum :
      ((dq + de) / (dq * de + 1) + (dq - de) / (dq * de - 1)) / 2 =
        de * (dq ^ 2 - 1) / ((dq * de) ^ 2 - 1) := by
    field_simp [ne_of_gt (by nlinarith : (0 : ℝ) < dq * de + 1),
      ne_of_gt (by nlinarith : (0 : ℝ) < dq * de - 1),
      ne_of_gt hden_pos, ne_of_gt hden_pos', hden_ne_norm]
    ring_nf
    field_simp [hden_ne_norm]
    ring
  rw [hsum]
  field_simp [ne_of_gt hde_pos, ne_of_gt hden_pos, ne_of_gt hden_pos']
  nlinarith [sq_nonneg de]

/-- Source Schur coefficient estimate:
`(p - q)/2 ≤ 1/d_{A₁}`. -/
theorem adhwFQSWSchur_half_sub_le_inv_card_q
    (q : Type x) (e : Type y) [Fintype q] [Fintype e]
    [Nonempty q] [Nonempty e] [Nontrivial (Prod q e)] :
    (adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2 ≤
      (1 : ℝ) / (Fintype.card q : ℝ) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_gt : 1 < dq * de := by
    have hnat : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    dsimp [dq, de]
    exact_mod_cast hnat
  have hdq_pos : 0 < dq := lt_of_lt_of_le zero_lt_one hdq_ge_one
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by nlinarith
  have hden_pos' : 0 < dq ^ 2 * de ^ 2 - 1 := by nlinarith
  have hden_ne_norm : -1 + dq ^ 2 * de ^ 2 ≠ 0 := by
    nlinarith
  unfold adhwFQSWSchurPCoeff adhwFQSWSchurQCoeff
  change ((dq + de) / (dq * de + 1) - (dq - de) / (dq * de - 1)) / 2 ≤ 1 / dq
  have hsub :
      ((dq + de) / (dq * de + 1) - (dq - de) / (dq * de - 1)) / 2 =
        dq * (de ^ 2 - 1) / ((dq * de) ^ 2 - 1) := by
    field_simp [ne_of_gt (by nlinarith : (0 : ℝ) < dq * de + 1),
      ne_of_gt (by nlinarith : (0 : ℝ) < dq * de - 1),
      ne_of_gt hden_pos, ne_of_gt hden_pos', hden_ne_norm]
    ring_nf
  rw [hsub]
  field_simp [ne_of_gt hdq_pos, ne_of_gt hden_pos, ne_of_gt hden_pos']
  nlinarith [sq_nonneg dq]

/-- In the nontrivial Schur case, the source coefficient `(p-q)/2` is exactly
the Hilbert--Schmidt prefactor appearing in ADHW fqsw.tex lines 722-747. -/
theorem adhwFQSWSchur_half_sub_eq_HS_prefactor
    (q : Type x) (e : Type y) [Fintype q] [Fintype e]
    [Nonempty q] [Nonempty e] [Nontrivial (Prod q e)] :
    (adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2 =
      ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
          (Fintype.card q : ℝ)) /
        ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_gt : 1 < dq * de := by
    have hnat : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    dsimp [dq, de]
    exact_mod_cast hnat
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by nlinarith
  have hden_pos' : 0 < dq ^ 2 * de ^ 2 - 1 := by nlinarith
  have hden_ne_norm : -1 + dq ^ 2 * de ^ 2 ≠ 0 := by
    nlinarith
  unfold adhwFQSWSchurPCoeff adhwFQSWSchurQCoeff
  change ((dq + de) / (dq * de + 1) - (dq - de) / (dq * de - 1)) / 2 =
    (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1)
  field_simp [ne_of_gt (by nlinarith : (0 : ℝ) < dq * de + 1),
    ne_of_gt (by nlinarith : (0 : ℝ) < dq * de - 1),
    ne_of_gt hden_pos, ne_of_gt hden_pos', hden_ne_norm]
  ring_nf

private theorem fqsw_twoCopySideOperator_trace
    (G : CMatrix (TensorPower q 2)) (H : CMatrix (TensorPower e 2)) :
    (twoCopySideOperator (a := q) (e := e) G H).trace = G.trace * H.trace := by
  unfold twoCopySideOperator twoCopyProdReindex
  rw [fqsw_trace_submatrix_equiv (tensorPowerProdEquiv q e 2)]
  exact Matrix.trace_kronecker G H

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
private theorem fqsw_twoCopySideOperator_mul
    (G G' : CMatrix (TensorPower q 2)) (H H' : CMatrix (TensorPower e 2)) :
    twoCopySideOperator (a := q) (e := e) G H *
        twoCopySideOperator (a := q) (e := e) G' H' =
      twoCopySideOperator (a := q) (e := e) (G * G') (H * H') := by
  ext x y
  rw [← twoCopyTensorWord_coords (a := Prod q e) x,
    ← twoCopyTensorWord_coords (a := Prod q e) y]
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.mul_apply, Matrix.kronecker,
    Finset.mul_sum, Finset.sum_mul]
  let X := tensorPowerProdEquiv q e 2 x
  let Y := tensorPowerProdEquiv q e 2 y
  calc
    (∑ z : TensorPower (Prod q e) 2,
      G X.1 ((tensorPowerProdEquiv q e 2 z).1) *
          H X.2 ((tensorPowerProdEquiv q e 2 z).2) *
        (G' ((tensorPowerProdEquiv q e 2 z).1) Y.1 *
          H' ((tensorPowerProdEquiv q e 2 z).2) Y.2)) =
      ∑ p : TensorPower q 2 × TensorPower e 2,
        G X.1 p.1 * H X.2 p.2 * (G' p.1 Y.1 * H' p.2 Y.2) := by
        exact Fintype.sum_equiv (tensorPowerProdEquiv q e 2)
          (fun z : TensorPower (Prod q e) 2 =>
            G X.1 ((tensorPowerProdEquiv q e 2 z).1) *
                H X.2 ((tensorPowerProdEquiv q e 2 z).2) *
              (G' ((tensorPowerProdEquiv q e 2 z).1) Y.1 *
                H' ((tensorPowerProdEquiv q e 2 z).2) Y.2))
          (fun p : TensorPower q 2 × TensorPower e 2 =>
            G X.1 p.1 * H X.2 p.2 * (G' p.1 Y.1 * H' p.2 Y.2))
          (fun _ => rfl)
    _ = ∑ j : TensorPower e 2, ∑ i : TensorPower q 2,
        G X.1 i * G' i Y.1 * (H X.2 j * H' j Y.2) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp [mul_comm, mul_left_comm]

private theorem fqsw_tensorPowerSwapMatrix_two_trace
    {α : Type*} [Fintype α] [DecidableEq α] :
    (tensorPowerSwapMatrix_two (a := α)).trace = (Fintype.card α : ℂ) := by
  calc
    (tensorPowerSwapMatrix_two (a := α)).trace =
        ((1 : CMatrix (TensorPower α 2)) * tensorPowerSwapMatrix_two (a := α)).trace := by
          rw [Matrix.one_mul]
    _ = (tensorPowerKroneckerTwo (a := α) (1 : CMatrix α) *
          tensorPowerSwapMatrix_two (a := α)).trace := by
          rw [fqsw_tensorPowerKroneckerTwo_one]
    _ = (Fintype.card α : ℂ) := by
      have h :=
        tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace
          (a := α) (1 : CMatrix α)
      simpa [Matrix.trace_one] using h

private theorem fqsw_splitObservable_trace :
    (twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))).trace =
      (Fintype.card q : ℂ) ^ 2 * (Fintype.card e : ℂ) := by
  rw [fqsw_twoCopySideOperator_trace]
  rw [Matrix.trace_one, fqsw_tensorPowerSwapMatrix_two_trace (α := e)]
  rw [tensorPower_card]
  rw [Nat.cast_pow]

private theorem fqsw_fullSwap_mul_splitObservable_trace [Nonempty q] :
    (tensorPowerSwapMatrix_two (a := Prod q e) *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrix_two (a := e))).trace =
      (Fintype.card q : ℂ) * (Fintype.card e : ℂ) ^ 2 := by
  rw [tensorPowerSwapMatrix_two_prod_eq_twoCopySideOperator (a := q) (e := e)]
  rw [fqsw_twoCopySideOperator_mul]
  rw [Matrix.mul_one, tensorPowerSwapMatrix_two_sq]
  rw [fqsw_twoCopySideOperator_trace]
  rw [fqsw_tensorPowerSwapMatrix_two_trace (α := q), Matrix.trace_one]
  rw [tensorPower_card]
  rw [Nat.cast_pow]

/-- Trace of the split FQSW observable `I^{q q'} ⊗ F^e` against the symmetric
two-copy projection on `A = q × e`.  This is the numerator source formula
behind ADHW's Schur coefficient `p = (d_q + d_e) / (d_q d_e + 1)`. -/
theorem adhwFQSW_splitObservable_symmetricProjection_trace
    (q : Type x) (e : Type y) [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] :
    (symmetricProjectionMatrix (a := Prod q e) 2 *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrix_two (a := e))).trace =
      ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) *
        ((Fintype.card q : ℂ) + (Fintype.card e : ℂ))) / 2 := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add]
  rw [fqsw_splitObservable_trace, fqsw_fullSwap_mul_splitObservable_trace]
  ring

/-- Trace of the split FQSW observable `I^{q q'} ⊗ F^e` against the
antisymmetric two-copy projection on `A = q × e`.  This is the numerator source
formula behind ADHW's Schur coefficient `q = (d_q - d_e) / (d_q d_e - 1)`. -/
theorem adhwFQSW_splitObservable_antisymmetricProjection_trace
    (q : Type x) (e : Type y) [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] :
    (antisymmetricProjectionMatrix_two (a := Prod q e) *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrix_two (a := e))).trace =
      ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) *
        ((Fintype.card q : ℂ) - (Fintype.card e : ℂ))) / 2 := by
  rw [antisymmetricProjectionMatrix_two]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  rw [fqsw_splitObservable_trace, adhwFQSW_splitObservable_symmetricProjection_trace]
  ring

/-- ADHW fqsw.tex lines 642-678: Schur twirling of the split observable
`I^{A₁A₁'} ⊗ F^{A₂}` on `A = A₁ × A₂`. -/
theorem adhwFQSW_splitObservable_unitaryTwirl_eq
    (q : Type x) (e : Type y) [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (Prod q e)] :
    unitaryTwirl 2
        (twoCopySideOperator (a := q) (e := e)
          (1 : CMatrix (TensorPower q 2))
          (tensorPowerSwapMatrix_two (a := e))) =
      ((adhwFQSWSchurPCoeff q e : ℂ) • symmetricProjectionMatrix (a := Prod q e) 2) +
        ((adhwFQSWSchurQCoeff q e : ℂ) •
          antisymmetricProjectionMatrix_two (a := Prod q e)) := by
  rw [unitaryTwirl_two_eq_symmetric_antisymmetric_trace_decomposition]
  rw [adhwFQSW_splitObservable_symmetricProjection_trace]
  rw [adhwFQSW_splitObservable_antisymmetricProjection_trace]
  rw [symmetricProjectionMatrix_two_trace]
  rw [antisymmetricProjectionMatrix_two_trace]
  have hqe_ne :
      ((Fintype.card q : ℂ) * (Fintype.card e : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero (α := q))
      (by exact_mod_cast Fintype.card_ne_zero (α := e))
  have hqe_add_ne :
      (Fintype.card q : ℂ) * (Fintype.card e : ℂ) + 1 ≠ 0 := by
    have hnat : Fintype.card q * Fintype.card e + 1 ≠ 0 :=
      Nat.succ_ne_zero (Fintype.card q * Fintype.card e)
    exact_mod_cast hnat
  have hqe_sub_ne :
      (Fintype.card q : ℂ) * (Fintype.card e : ℂ) - 1 ≠ 0 := by
    have hgt : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    have hne : Fintype.card q * Fintype.card e ≠ 1 := ne_of_gt hgt
    intro h
    apply hne
    have hcast : ((Fintype.card q * Fintype.card e : ℕ) : ℂ) = 1 := by
      simpa [sub_eq_zero, ← Nat.cast_mul] using h
    exact_mod_cast hcast
  simp [adhwFQSWSchurPCoeff, adhwFQSWSchurQCoeff, Fintype.card_prod]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  field_simp [hqe_ne, hqe_add_ne, hqe_sub_ne]

/-- Trace of a two-copy source operator against
`Π₊^A ⊗ F^R`, the symmetric half of ADHW fqsw.tex lines 708-714. -/
theorem fqsw_twoCopy_symmetricProjection_swap_trace
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ : CMatrix (Prod α β)) :
    (tensorPowerKroneckerTwo (a := Prod α β) ρ *
      twoCopySideOperator (a := α) (e := β)
        (symmetricProjectionMatrix (a := α) 2)
        (tensorPowerSwapMatrix_two (a := β))).trace =
      ((1 : ℂ) / 2) *
        ((partialTraceA (a := α) (b := β) ρ *
            partialTraceA (a := α) (b := β) ρ).trace +
          (ρ * ρ).trace) := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  rw [twoCopySideOperator_smul_left]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [twoCopySideOperator_add_left]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [tensorPowerKroneckerTwo_prod_mul_one_swap_trace]
  rw [tensorPowerKroneckerTwo_prod_mul_full_swap_trace]
  ring

/-- Trace of a two-copy source operator against
`Π₋^A ⊗ F^R`, the antisymmetric half of ADHW fqsw.tex lines 708-714. -/
theorem fqsw_twoCopy_antisymmetricProjection_swap_trace
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ : CMatrix (Prod α β)) :
    (tensorPowerKroneckerTwo (a := Prod α β) ρ *
      twoCopySideOperator (a := α) (e := β)
        (antisymmetricProjectionMatrix_two (a := α))
        (tensorPowerSwapMatrix_two (a := β))).trace =
      ((1 : ℂ) / 2) *
        ((partialTraceA (a := α) (b := β) ρ *
            partialTraceA (a := α) (b := β) ρ).trace -
          (ρ * ρ).trace) := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [twoCopySideOperator_smul_left]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [show twoCopySideOperator (a := α) (e := β)
        ((1 : CMatrix (TensorPower α 2)) - tensorPowerSwapMatrix_two (a := α))
        (tensorPowerSwapMatrix_two (a := β)) =
      twoCopySideOperator (a := α) (e := β)
        (1 : CMatrix (TensorPower α 2))
        (tensorPowerSwapMatrix_two (a := β)) -
      twoCopySideOperator (a := α) (e := β)
        (tensorPowerSwapMatrix_two (a := α))
        (tensorPowerSwapMatrix_two (a := β)) by
    rw [sub_eq_add_neg]
    rw [twoCopySideOperator_add_left]
    rw [show
        -tensorPowerSwapMatrix_two (a := α) =
          ((-1 : ℂ) • tensorPowerSwapMatrix_two (a := α)) by
      ext x y
      simp
      split_ifs <;> simp]
    rw [twoCopySideOperator_smul_left]
    simp [sub_eq_add_neg]]
  rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [tensorPowerKroneckerTwo_prod_mul_one_swap_trace]
  rw [tensorPowerKroneckerTwo_prod_mul_full_swap_trace]
  ring

private noncomputable def fqswTwoCopySideTraceCLM
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ : CMatrix (Prod α β)) (H : CMatrix (TensorPower β 2)) :
    CMatrix (TensorPower α 2) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun G =>
        (tensorPowerKroneckerTwo (a := Prod α β) ρ *
          twoCopySideOperator (a := α) (e := β) G H).trace
       map_add' := by
        intro G G'
        rw [twoCopySideOperator_add_left, Matrix.mul_add, Matrix.trace_add]
       map_smul' := by
        intro c G
        change (tensorPowerKroneckerTwo (a := Prod α β) ρ *
            twoCopySideOperator (a := α) (e := β) ((c : ℂ) • G) H).trace =
          c • (tensorPowerKroneckerTwo (a := Prod α β) ρ *
            twoCopySideOperator (a := α) (e := β) G H).trace
        rw [twoCopySideOperator_smul_left, Matrix.mul_smul, Matrix.trace_smul]
        rfl } :
      CMatrix (TensorPower α 2) →ₗ[ℝ] ℂ)

/-- Integral-side bridge for ADHW fqsw.tex lines 708-712: a scalar
two-copy trace of the Haar integrand is the same scalar trace evaluated on
the two-copy unitary twirl. -/
theorem fqsw_unitaryTwirl_twoCopySide_trace_integral_bridge
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (A : CMatrix (TensorPower α 2)) (ρ : CMatrix (Prod α β))
    (H : CMatrix (TensorPower β 2)) :
    (∫ U : Matrix.unitaryGroup α ℂ,
        (tensorPowerKroneckerTwo (a := Prod α β) ρ *
          twoCopySideOperator (a := α) (e := β)
            (unitaryTwirlIntegrand (a := α) 2 A U) H).trace
        ∂unitaryHaarMeasure (a := α)) =
      (tensorPowerKroneckerTwo (a := Prod α β) ρ *
        twoCopySideOperator (a := α) (e := β)
          (unitaryTwirl 2 A) H).trace := by
  let L := fqswTwoCopySideTraceCLM (α := α) (β := β) ρ H
  have hf : MeasureTheory.Integrable
      (unitaryTwirlIntegrand (a := α) 2 A)
      (unitaryHaarMeasure (a := α)) :=
    unitaryTwirl_integrand_integrable (a := α) 2 A
  change (∫ U : Matrix.unitaryGroup α ℂ,
        L (unitaryTwirlIntegrand (a := α) 2 A U)
        ∂unitaryHaarMeasure (a := α)) =
      L (unitaryTwirl 2 A)
  simpa [L, unitaryTwirl] using
    ((fqswTwoCopySideTraceCLM (α := α) (β := β) ρ H).integral_comp_comm hf)

/-- Trace of a one-system two-copy operator against `Π₊`, used in the
`R = 1` specialization of ADHW fqsw.tex lines 722 and 781-784. -/
theorem fqsw_twoCopy_symmetricProjection_trace
    {α : Type u} [Fintype α] [DecidableEq α] (ρ : CMatrix α) :
    (tensorPowerKroneckerTwo (a := α) ρ *
      symmetricProjectionMatrix (a := α) 2).trace =
      ((1 : ℂ) / 2) * (ρ.trace * ρ.trace + (ρ * ρ).trace) := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.mul_one]
  rw [tensorPowerKroneckerTwo_trace]
  rw [tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace]
  ring

/-- Trace of a one-system two-copy operator against `Π₋`, used in the
`R = 1` specialization of ADHW fqsw.tex lines 722 and 781-784. -/
theorem fqsw_twoCopy_antisymmetricProjection_trace
    {α : Type u} [Fintype α] [DecidableEq α] (ρ : CMatrix α) :
    (tensorPowerKroneckerTwo (a := α) ρ *
      antisymmetricProjectionMatrix_two (a := α)).trace =
      ((1 : ℂ) / 2) * (ρ.trace * ρ.trace - (ρ * ρ).trace) := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [Matrix.mul_one]
  rw [tensorPowerKroneckerTwo_trace]
  rw [tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace]
  ring

/-- ADHW fqsw.tex lines 708-714 after Schur twirling: evaluating the twirled
split observable against a source `AR` matrix gives the `R` and `AR` purity
trace terms with coefficients `(p+q)/2` and `(p-q)/2`. -/
theorem fqsw_splitObservable_unitaryTwirl_swap_trace
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype r] [DecidableEq r] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod (Prod q e) r)) :
    (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
      twoCopySideOperator (a := Prod q e) (e := r)
        (unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e))))
        (tensorPowerSwapMatrix_two (a := r))).trace =
      (((adhwFQSWSchurPCoeff q e : ℂ) + (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (partialTraceA (a := Prod q e) (b := r) ρ *
            partialTraceA (a := Prod q e) (b := r) ρ).trace +
        (((adhwFQSWSchurPCoeff q e : ℂ) - (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (ρ * ρ).trace := by
  rw [adhwFQSW_splitObservable_unitaryTwirl_eq (q := q) (e := e)]
  rw [twoCopySideOperator_add_left]
  rw [twoCopySideOperator_smul_left, twoCopySideOperator_smul_left]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  rw [fqsw_twoCopy_symmetricProjection_swap_trace]
  rw [fqsw_twoCopy_antisymmetricProjection_swap_trace]
  ring

/-- ADHW fqsw.tex lines 722 and 781-784 with trivial reference: the twirled
split observable gives the averaged `A₂` purity trace. -/
theorem fqsw_splitObservable_unitaryTwirl_trace
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod q e)) :
    (tensorPowerKroneckerTwo (a := Prod q e) ρ *
      unitaryTwirl 2
        (twoCopySideOperator (a := q) (e := e)
          (1 : CMatrix (TensorPower q 2))
          (tensorPowerSwapMatrix_two (a := e)))).trace =
      (((adhwFQSWSchurPCoeff q e : ℂ) + (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (ρ.trace * ρ.trace) +
        (((adhwFQSWSchurPCoeff q e : ℂ) - (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (ρ * ρ).trace := by
  rw [adhwFQSW_splitObservable_unitaryTwirl_eq (q := q) (e := e)]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  rw [fqsw_twoCopy_symmetricProjection_trace]
  rw [fqsw_twoCopy_antisymmetricProjection_trace]
  ring

private noncomputable def fqswTraceMulCLM
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ : CMatrix α) : CMatrix α →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => (ρ * A).trace
       map_add' := by
        intro A B
        rw [Matrix.mul_add, Matrix.trace_add]
       map_smul' := by
        intro c A
        change (ρ * ((c : ℂ) • A)).trace = c • (ρ * A).trace
        rw [Matrix.mul_smul, Matrix.trace_smul]
        rfl } :
      CMatrix α →ₗ[ℝ] ℂ)

/-- Integral-side bridge for a scalar two-copy trace against the ordinary
Haar twirl. -/
theorem fqsw_unitaryTwirl_trace_integral_bridge
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (A ρ : CMatrix (TensorPower α 2)) :
    (∫ U : Matrix.unitaryGroup α ℂ,
        (ρ * unitaryTwirlIntegrand (a := α) 2 A U).trace
        ∂unitaryHaarMeasure (a := α)) =
      (ρ * unitaryTwirl 2 A).trace := by
  let L := fqswTraceMulCLM (α := TensorPower α 2) ρ
  have hf : MeasureTheory.Integrable
      (unitaryTwirlIntegrand (a := α) 2 A)
      (unitaryHaarMeasure (a := α)) :=
    unitaryTwirl_integrand_integrable (a := α) 2 A
  change (∫ U : Matrix.unitaryGroup α ℂ,
        L (unitaryTwirlIntegrand (a := α) 2 A U)
        ∂unitaryHaarMeasure (a := α)) =
      L (unitaryTwirl 2 A)
  simpa [L, unitaryTwirl] using
    ((fqswTraceMulCLM (α := TensorPower α 2) ρ).integral_comp_comm hf)

/-- Pointwise one-copy flip trick for ADHW fqsw.tex lines 781-784. -/
theorem fqsw_A2_square_trace_eq_twirl_inv_integrand
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e]
    (ρ : CMatrix (Prod q e)) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) *
      partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))).trace =
      (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirlIntegrand (a := Prod q e) 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e))) U⁻¹).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let U₂ : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) (U : CMatrix (Prod q e))
  let R : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) ρ
  have htensor :
      tensorPowerKroneckerTwo (a := Prod q e)
          ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) =
        U₂ * R * star U₂ := by
    calc
      tensorPowerKroneckerTwo (a := Prod q e)
          ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) =
        tensorPowerKroneckerTwo (a := Prod q e)
            ((U : CMatrix (Prod q e)) * ρ) *
          tensorPowerKroneckerTwo (a := Prod q e) (star (U : CMatrix (Prod q e))) := by
          exact (tensorPowerKroneckerTwo_mul (a := Prod q e)
            ((U : CMatrix (Prod q e)) * ρ) (star (U : CMatrix (Prod q e)))).symm
      _ = (tensorPowerKroneckerTwo (a := Prod q e) (U : CMatrix (Prod q e)) *
            tensorPowerKroneckerTwo (a := Prod q e) ρ) *
          tensorPowerKroneckerTwo (a := Prod q e) (star (U : CMatrix (Prod q e))) := by
          rw [tensorPowerKroneckerTwo_mul (a := Prod q e) (U : CMatrix (Prod q e)) ρ]
      _ = U₂ * R * star U₂ := by
          rw [fqsw_tensorPowerKroneckerTwo_star]
  rw [← tensorPowerKroneckerTwo_prod_mul_one_swap_trace
    (a := q) (e := e)
    (rho := (U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))]
  rw [htensor]
  calc
    ((U₂ * R * star U₂) * A).trace =
        (R * (star U₂ * A * U₂)).trace := by
          have h := Matrix.trace_mul_comm U₂ (R * star U₂ * A)
          simpa [Matrix.mul_assoc] using h
    _ = (R * unitaryTwirlIntegrand (a := Prod q e) 2 A U⁻¹).trace := by
          congr 1
          simp [A, U₂, unitaryTwirlIntegrand,
            fqsw_unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo,
            fqsw_tensorPowerKroneckerTwo_star, Matrix.mul_assoc]
    _ = (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirlIntegrand (a := Prod q e) 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e))) U⁻¹).trace := by
          rfl

/-- Haar-averaged one-copy purity identity from ADHW fqsw.tex lines
781-784. -/
theorem fqsw_A2_square_trace_average_eq
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod q e)) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        (partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) *
          partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))).trace
        ∂unitaryHaarMeasure (a := Prod q e)) =
      (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let R : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) ρ
  let f : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (R * unitaryTwirlIntegrand (a := Prod q e) 2 A U).trace
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        (partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) *
          partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))).trace
        ∂unitaryHaarMeasure (a := Prod q e)) =
      ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U⁻¹
        ∂unitaryHaarMeasure (a := Prod q e) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with U
        simpa [f, R, A] using fqsw_A2_square_trace_eq_twirl_inv_integrand
          (q := q) (e := e) ρ U
    _ = ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U
        ∂unitaryHaarMeasure (a := Prod q e) := by
        rw [MeasureTheory.integral_inv_eq_self (f := f)
          (μ := unitaryHaarMeasure (a := Prod q e))]
    _ = (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))).trace := by
        simpa [f, R, A] using
          fqsw_unitaryTwirl_trace_integral_bridge
            (α := Prod q e) A R

/-- Static flip trick for the `A₂R` marginal after regrouping
`(A₁ × A₂) × R` as `A₁ × (A₂ × R)`.  This is the source-route bridge from the
partial trace square to the two-copy observable
`I^{A₁A₁'} ⊗ F^{A₂} ⊗ F^R`. -/
theorem fqsw_A2R_square_trace_eq_split_observable
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e]
    [Fintype r] [DecidableEq r]
    (ρ : CMatrix (Prod (Prod q e) r)) :
    (partialTraceA (a := q) (b := Prod e r)
        (ρ.submatrix (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) *
      partialTraceA (a := q) (b := Prod e r)
        (ρ.submatrix (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)).trace =
      (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
  let ρ' : CMatrix (Prod q (Prod e r)) :=
    ρ.submatrix (fqswQERToA2REquiv q e r).symm
      (fqswQERToA2REquiv q e r).symm
  calc
    (partialTraceA (a := q) (b := Prod e r) ρ' *
      partialTraceA (a := q) (b := Prod e r) ρ').trace =
        ∑ i : q, ∑ k : e, ∑ s : r, ∑ j : q, ∑ l : e, ∑ t : r,
          ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s) := by
      rw [← tensorPowerKroneckerTwo_prod_mul_one_swap_trace
        (a := q) (e := Prod e r) (rho := ρ')]
      rw [Matrix.trace, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun t _ => ?_
      change
        (tensorPowerKroneckerTwo (a := Prod q (Prod e r)) ρ' *
          twoCopySideOperator (a := q) (e := Prod e r)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := Prod e r)))
          (twoCopyTensorWord (a := Prod q (Prod e r)) (i, (k, s)) (j, (l, t)))
          (twoCopyTensorWord (a := Prod q (Prod e r)) (i, (k, s)) (j, (l, t))) =
        ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s)
      rw [Matrix.mul_apply, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      simp_rw [Fintype.sum_prod_type]
      simpa [ρ', fqswQERToA2REquiv, Matrix.one_apply,
        permEquiv_twoCopySwapPerm_twoCopyTensorWord, twoCopyTensorWord_eq_iff,
        mul_comm, mul_left_comm, mul_assoc] using
          fqsw_partialTraceA_flip_entry_sum_prod
            (α := q) (β := e) (γ := r) ρ' i j k l s t
    _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
      symm
      rw [Matrix.trace, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun t _ => ?_
      change
        (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
          twoCopySideOperator (a := Prod q e) (e := r)
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e)))
            (tensorPowerSwapMatrix_two (a := r)))
          (twoCopyTensorWord (a := Prod (Prod q e) r) ((i, k), s) ((j, l), t))
          (twoCopyTensorWord (a := Prod (Prod q e) r) ((i, k), s) ((j, l), t)) =
        ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s)
      rw [Matrix.mul_apply, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      simp_rw [Fintype.sum_prod_type]
      simpa [Matrix.one_apply, permEquiv_twoCopySwapPerm_twoCopyTensorWord,
        twoCopyTensorWord_eq_iff, mul_comm, mul_left_comm, mul_assoc] using
          fqsw_nested_split_flip_entry_sum
            (α := q) (β := e) (γ := r) ρ i j k l s t

/-- Pointwise `A₂R` flip trick for the split unitary integrand in ADHW
fqsw.tex lines 708-714. -/
theorem fqsw_A2R_square_trace_eq_twirl_inv_integrand
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e]
    [Fintype r] [DecidableEq r]
    (ρ : CMatrix (Prod (Prod q e) r)) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) *
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)).trace =
      (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirlIntegrand (a := Prod q e) 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))) U⁻¹)
          (tensorPowerSwapMatrix_two (a := r))).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let H : CMatrix (TensorPower r 2) := tensorPowerSwapMatrix_two (a := r)
  let K : CMatrix (Prod (Prod q e) r) :=
    Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
  let U₂ : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) (U : CMatrix (Prod q e))
  let K₂ : CMatrix (TensorPower (Prod (Prod q e) r) 2) :=
    tensorPowerKroneckerTwo (a := Prod (Prod q e) r) K
  let R : CMatrix (TensorPower (Prod (Prod q e) r) 2) :=
    tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ
  have htensor :
      tensorPowerKroneckerTwo (a := Prod (Prod q e) r)
          (K * ρ * star K) =
        K₂ * R * star K₂ := by
    calc
      tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (K * ρ * star K) =
          tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (K * ρ) *
            tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (star K) := by
            exact (tensorPowerKroneckerTwo_mul (a := Prod (Prod q e) r)
              (K * ρ) (star K)).symm
      _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) K *
            tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ) *
            tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (star K) := by
            rw [tensorPowerKroneckerTwo_mul (a := Prod (Prod q e) r) K ρ]
      _ = K₂ * R * star K₂ := by
            rw [fqsw_tensorPowerKroneckerTwo_star]
  have hK₂ :
      K₂ = twoCopySideOperator (a := Prod q e) (e := r) U₂
          (1 : CMatrix (TensorPower r 2)) := by
    simpa [K₂, K, U₂] using
      fqsw_tensorPowerKroneckerTwo_kronecker_one
        (α := Prod q e) (β := r) (U : CMatrix (Prod q e))
  have hstarK₂ :
      star K₂ =
        twoCopySideOperator (a := Prod q e) (e := r) (star U₂)
          (1 : CMatrix (TensorPower r 2)) := by
    rw [hK₂]
    ext x y
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      twoCopySideOperator_apply, Matrix.one_apply]
    by_cases hxy :
        ((tensorPowerProdEquiv (Prod q e) r 2) y).2 =
          ((tensorPowerProdEquiv (Prod q e) r 2) x).2
    · have hyx :
          ((tensorPowerProdEquiv (Prod q e) r 2) x).2 =
            ((tensorPowerProdEquiv (Prod q e) r 2) y).2 := hxy.symm
      rw [if_pos hxy, if_pos hyx]
      simp
    · have hyx :
          ¬ ((tensorPowerProdEquiv (Prod q e) r 2) x).2 =
            ((tensorPowerProdEquiv (Prod q e) r 2) y).2 := by
          intro hyx
          exact hxy hyx.symm
      rw [if_neg hxy, if_neg hyx]
      simp
  rw [show
      (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
          ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) =
        K * ρ * star K by rfl]
  rw [fqsw_A2R_square_trace_eq_split_observable
    (q := q) (e := e) (r := r) (ρ := K * ρ * star K)]
  rw [htensor]
  calc
    ((K₂ * R * star K₂) *
        twoCopySideOperator (a := Prod q e) (e := r) A H).trace =
      (R * (star K₂ *
        twoCopySideOperator (a := Prod q e) (e := r) A H * K₂)).trace := by
        have h := Matrix.trace_mul_comm K₂
          (R * star K₂ * twoCopySideOperator (a := Prod q e) (e := r) A H)
        simpa [Matrix.mul_assoc] using h
    _ = (R * twoCopySideOperator (a := Prod q e) (e := r)
        (unitaryTwirlIntegrand (a := Prod q e) 2 A U⁻¹) H).trace := by
        congr 1
        rw [hstarK₂, hK₂]
        rw [fqsw_twoCopySideOperator_mul]
        rw [fqsw_twoCopySideOperator_mul]
        simp [A, H, U₂, unitaryTwirlIntegrand,
          fqsw_unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo,
          fqsw_tensorPowerKroneckerTwo_star, Matrix.mul_assoc]
    _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirlIntegrand (a := Prod q e) 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))) U⁻¹)
          (tensorPowerSwapMatrix_two (a := r))).trace := by
        rfl

/-- Haar-averaged `A₂R` purity identity from ADHW fqsw.tex lines 708-714. -/
theorem fqsw_A2R_square_trace_average_eq
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype r] [DecidableEq r] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod (Prod q e) r)) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      (partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm) *
        partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)).trace
      ∂unitaryHaarMeasure (a := Prod q e)) =
      (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirl 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let H : CMatrix (TensorPower r 2) := tensorPowerSwapMatrix_two (a := r)
  let R : CMatrix (TensorPower (Prod (Prod q e) r) 2) :=
    tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ
  let f : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (R *
      twoCopySideOperator (a := Prod q e) (e := r)
        (unitaryTwirlIntegrand (a := Prod q e) 2 A U) H).trace
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      (partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm) *
        partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)).trace
      ∂unitaryHaarMeasure (a := Prod q e)) =
        ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U⁻¹
          ∂unitaryHaarMeasure (a := Prod q e) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with U
        simpa [f, R, A, H] using
          fqsw_A2R_square_trace_eq_twirl_inv_integrand
            (q := q) (e := e) (r := r) ρ U
    _ = ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U
        ∂unitaryHaarMeasure (a := Prod q e) := by
        rw [MeasureTheory.integral_inv_eq_self (f := f)
          (μ := unitaryHaarMeasure (a := Prod q e))]
    _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirl 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
        simpa [f, R, A, H] using
          fqsw_unitaryTwirl_twoCopySide_trace_integral_bridge
            (α := Prod q e) (β := r) A ρ H

/-- Subtracting the maximally mixed state turns the Hilbert--Schmidt square
into the output purity minus `1/d`. -/
theorem fqsw_hilbertSchmidtSq_sub_maximallyMixedState
    {e : Type y} [Fintype e] [DecidableEq e] [Nonempty e] (ρ : State e) :
    hilbertSchmidtSq (ρ.matrix - (adhwFQSWMaximallyMixedState e).matrix) =
      (ρ.matrix * ρ.matrix).trace.re - (1 / (Fintype.card e : ℝ)) := by
  have hcard_ne : (Fintype.card e : ℝ) ≠ 0 := by positivity
  have hcross :
      (ρ.matrix * (adhwFQSWMaximallyMixedState e).matrix).trace.re =
        1 / (Fintype.card e : ℝ) := by
    simp [adhwFQSWMaximallyMixedState, Matrix.mul_smul, Matrix.trace_smul,
      ρ.trace_eq_one, one_div]
  have hmm :
      hilbertSchmidtSq (adhwFQSWMaximallyMixedState e).matrix =
        1 / (Fintype.card e : ℝ) := by
    unfold hilbertSchmidtSq adhwFQSWMaximallyMixedState
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.trace_smul, Matrix.trace_one, one_div, hcard_ne]
  rw [fqsw_hilbertSchmidtSq_sub_of_isHermitian
    ρ.matrix (adhwFQSWMaximallyMixedState e).matrix
    ρ.pos.isHermitian (adhwFQSWMaximallyMixedState e).pos.isHermitian]
  rw [hcross, hmm]
  ring

/-- Exact Hilbert--Schmidt one-shot expression from ADHW fqsw.tex lines
682-747, written in the repository's source-state notation. -/
def adhwFQSWHSOneShotExact
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ℝ :=
  ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
      (Fintype.card q : ℝ)) /
    ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) *
    (adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

/-- In the one-point split case, the ADHW Hilbert--Schmidt prefactor is zero,
so the exact one-shot expression is zero. -/
theorem adhwFQSWHSOneShotExact_eq_zero_of_subsingleton
    [Nonempty q] [Subsingleton (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) :
    adhwFQSWHSOneShotExact ψ q e = 0 := by
  classical
  let q0 : q := Classical.choice inferInstance
  let e0 : e := Classical.choice inferInstance
  haveI : Subsingleton q :=
    Function.Injective.subsingleton (f := fun x : q => (x, e0))
      (by intro x y h; exact congrArg Prod.fst h)
  haveI : Subsingleton e :=
    Function.Injective.subsingleton (f := fun y : e => (q0, y))
      (by intro x y h; exact congrArg Prod.snd h)
  have hqcard : (Fintype.card q : ℝ) = 1 := by
    exact_mod_cast
      (Fintype.card_eq_one_iff.mpr ⟨q0, fun y => Subsingleton.elim y q0⟩)
  have hecard : (Fintype.card e : ℝ) = 1 := by
    exact_mod_cast
      (Fintype.card_eq_one_iff.mpr ⟨e0, fun y => Subsingleton.elim y e0⟩)
  unfold adhwFQSWHSOneShotExact
  rw [hqcard, hecard]
  norm_num

/-- ADHW fqsw.tex Eq. (actuallyItsSimple): the Schur/HS prefactor is bounded
by `1/d_{A₁}`. -/
theorem adhwFQSW_HS_prefactor_le_inv_card_q
    (q : Type x) (e : Type y) [Fintype q] [Fintype e] [Nonempty q] [Nonempty e] :
    ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
        (Fintype.card q : ℝ)) /
      ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) ≤
      (1 : ℝ) / (Fintype.card q : ℝ) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_pos : 0 < dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_pos : 0 < de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_ge_one : 1 ≤ dq * de := by
    nlinarith
  by_cases hprod_eq : dq * de = 1
  · have hde_eq : de = 1 := by nlinarith
    have hdq_eq : dq = 1 := by nlinarith
    change (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1) ≤ 1 / dq
    rw [hdq_eq, hde_eq]
    norm_num
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by
    have hprod_gt : 1 < dq * de := lt_of_le_of_ne hprod_ge_one (Ne.symm hprod_eq)
    nlinarith
  have hdq_ne : dq ≠ 0 := ne_of_gt hdq_pos
  change (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1) ≤ 1 / dq
  rw [div_le_iff₀ hden_pos]
  have hdq_sq_ge_one : 1 ≤ dq ^ 2 := by
    nlinarith
  rw [one_div, ← div_eq_inv_mul]
  rw [le_div_iff₀ hdq_pos]
  nlinarith

/-- The ADHW HS prefactor is nonnegative. -/
theorem adhwFQSW_HS_prefactor_nonneg
    (q : Type x) (e : Type y) [Fintype q] [Fintype e] [Nonempty q] [Nonempty e] :
    0 ≤ ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
        (Fintype.card q : ℝ)) /
      ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hde_sq_ge_one : 1 ≤ de ^ 2 := by nlinarith
  have hnum_nonneg : 0 ≤ dq * de ^ 2 - dq := by
    nlinarith
  have hden_nonneg : 0 ≤ (dq * de) ^ 2 - 1 := by
    nlinarith [sq_nonneg (dq * de), mul_le_mul hdq_ge_one hde_ge_one (by norm_num) (by nlinarith)]
  change 0 ≤ (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1)
  exact div_nonneg hnum_nonneg hden_nonneg

/-- Trace-norm decoupling square bound from ADHW fqsw.tex lines 580-760. -/
def adhwFQSWTraceNormDecouplingSqBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
      ((Fintype.card q : ℝ) ^ 2)) *
    (adhwFQSWARPurity ψ + adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

/-- Max-mixed `A₂` square bound from ADHW fqsw.tex lines 767-795. -/
def adhwFQSWMaxMixedA2SqBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  ((Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2)) * adhwFQSWAPurity ψ

/-- ADHW fqsw.tex lines 781-787: in the nontrivial Schur case, the
Haar-averaged Hilbert--Schmidt distance of the `A₂` marginal from maximally
mixed is bounded by the source one-copy purity term. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtAverage_le_of_nontrivial
    [Nonempty q] [Nontrivial (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (Fintype.card e : ℝ) *
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  let ρA : CMatrix (Prod q e) := adhwFQSWASplitMatrix ψ split
  let f : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e))) *
      partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e)))).trace
  have hf_cont : Continuous f := by
    unfold f
    continuity
  have hf_int : MeasureTheory.Integrable f (unitaryHaarMeasure (a := Prod q e)) :=
    hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre_integral :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
        ∂unitaryHaarMeasure (a := Prod q e)) =
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U
          ∂unitaryHaarMeasure (a := Prod q e)).re := by
    simpa [f] using (Complex.reCLM.integral_comp_comm hf_int)
  have hρ_trace : ρA.trace = 1 := by
    simpa [ρA] using adhwFQSWASplitMatrix_trace ψ split
  have hρ_herm : ρA.IsHermitian := by
    unfold ρA adhwFQSWASplitMatrix
    exact fqsw_isHermitian_submatrix_equiv split.symm
      (adhwFQSWARState ψ).marginalA.pos.isHermitian
  have hρ_purity : (ρA * ρA).trace.re = adhwFQSWAPurity ψ := by
    calc
      (ρA * ρA).trace.re = hilbertSchmidtSq ρA := by
        exact (fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian ρA hρ_herm).symm
      _ = adhwFQSWAPurity ψ := by
        simpa [ρA] using adhwFQSWASplitMatrix_hilbertSchmidtSq ψ split
  have hcomplex :=
    (fqsw_A2_square_trace_average_eq (q := q) (e := e) ρA).trans
      (fqsw_splitObservable_unitaryTwirl_trace (q := q) (e := e) ρA)
  have hreal := congrArg Complex.re hcomplex
  have haverage_purity :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
        ∂unitaryHaarMeasure (a := Prod q e)) =
        ((adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2) +
          ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
            adhwFQSWAPurity ψ := by
    rw [hre_integral]
    simpa [f, ρA, hρ_trace, hρ_purity, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.div_re] using hreal
  have hhs_point : ∀ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U =
        (f U).re - (1 / (Fintype.card e : ℝ)) := by
    intro U
    let σ : State e :=
      adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)
    have hσ :=
      fqsw_hilbertSchmidtSq_sub_maximallyMixedState (e := e) σ
    simpa [adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary, σ, f, ρA,
      adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_A]
      using hσ
  have hf_re_int : MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ => (f U).re)
      (unitaryHaarMeasure (a := Prod q e)) :=
    Complex.reCLM.integrable_comp hf_int
  have hhs_average :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
          ∂unitaryHaarMeasure (a := Prod q e)) -
          (1 / (Fintype.card e : ℝ)) := by
    calc
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
          ∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
            ((f U).re - (1 / (Fintype.card e : ℝ)))
            ∂unitaryHaarMeasure (a := Prod q e) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with U
            exact hhs_point U
      _ = (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
            ∂unitaryHaarMeasure (a := Prod q e)) -
            (1 / (Fintype.card e : ℝ)) := by
            rw [MeasureTheory.integral_sub hf_re_int (MeasureTheory.integrable_const _)]
            rw [MeasureTheory.integral_const]
            simp [MeasureTheory.measureReal_def]
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  let P : ℝ := adhwFQSWAPurity ψ
  have hP_nonneg : 0 ≤ P := by
    simpa [P, adhwFQSWAPurity] using
      hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalA.matrix)
  have hsum_le :
      (adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2 ≤
        1 / de := by
    simpa [de] using adhwFQSWSchur_half_sum_le_inv_card_e q e
  have hsub_le :
      (adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2 ≤
        1 / dq := by
    simpa [dq] using adhwFQSWSchur_half_sub_le_inv_card_q q e
  have hhs_le :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        (1 / dq) * P := by
    rw [hhs_average, haverage_purity]
    nlinarith [mul_le_mul_of_nonneg_right hsub_le hP_nonneg, hsum_le]
  have hde_nonneg : 0 ≤ de := by
    dsimp [de]
    positivity
  have hcard_a : (Fintype.card a : ℝ) = dq * de := by
    have hnat : Fintype.card a = Fintype.card (Prod q e) :=
      Fintype.card_congr split
    rw [Fintype.card_prod] at hnat
    dsimp [dq, de]
    exact_mod_cast hnat
  have hdq_pos : 0 < dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  unfold adhwFQSWMaxMixedA2SqBound
  change de *
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ((Fintype.card a : ℝ) / dq ^ 2) * P
  calc
    de *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) ≤ de * ((1 / dq) * P) :=
        mul_le_mul_of_nonneg_left hhs_le hde_nonneg
    _ = ((Fintype.card a : ℝ) / dq ^ 2) * P := by
        rw [hcard_a]
        field_simp [ne_of_gt hdq_pos]

/-- Pointwise source-route bridge for ADHW fqsw.tex lines 682-747: the
product-decoupling Hilbert--Schmidt integrand is the `A₂R` marginal of the
conjugated source correlation matrix
`ψ^{AR} - ψ^A ⊗ ψ^R`. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U =
      hilbertSchmidtSq
        (partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              (adhwFQSWARSplitMatrix ψ split -
                adhwFQSWARProductSplitMatrix ψ split) *
              star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)) := by
  let K : CMatrix (Prod (Prod q e) r) :=
    Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
  let Rm : CMatrix (Prod (Prod q e) r) := adhwFQSWARSplitMatrix ψ split
  let Pm : CMatrix (Prod (Prod q e) r) := adhwFQSWARProductSplitMatrix ψ split
  rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary]
  rw [adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_AR_split]
  rw [adhwFQSWProductA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_ARProduct]
  rw [← fqsw_partialTraceA_sub]
  change
    hilbertSchmidtSq
      (partialTraceA (a := q) (b := Prod e r)
        ((K * Rm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm -
          (K * Pm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)) =
      hilbertSchmidtSq
        (partialTraceA (a := q) (b := Prod e r)
          ((K * (Rm - Pm) * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm))
  have hsubmatrix :
      (K * Rm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm -
          (K * Pm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm =
        (K * (Rm - Pm) * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm := by
    ext x y
    simp [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsubmatrix]

/-- ADHW fqsw.tex lines 682-747 in the nontrivial Schur case: the Haar
average of the product-decoupling Hilbert--Schmidt square is exactly the
source one-shot expression. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_eq_of_nontrivial
    [Nonempty q] [Nontrivial (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) =
      adhwFQSWHSOneShotExact ψ q e := by
  let Δ : CMatrix (Prod (Prod q e) r) :=
    adhwFQSWARSplitMatrix ψ split -
      adhwFQSWARProductSplitMatrix ψ split
  let g : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            Δ *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) *
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            Δ *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)).trace
  have hg_cont : Continuous g := by
    unfold g
    continuity
  have hg_int : MeasureTheory.Integrable g (unitaryHaarMeasure (a := Prod q e)) :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre_integral :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (g U).re
        ∂unitaryHaarMeasure (a := Prod q e)) =
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, g U
          ∂unitaryHaarMeasure (a := Prod q e)).re := by
    simpa [g] using (Complex.reCLM.integral_comp_comm hg_int)
  have hRm_herm : (adhwFQSWARSplitMatrix ψ split).IsHermitian := by
    unfold adhwFQSWARSplitMatrix
    exact fqsw_isHermitian_submatrix_equiv (fqswARSplitEquiv split).symm
      (adhwFQSWARState ψ).pos.isHermitian
  have hPm_herm : (adhwFQSWARProductSplitMatrix ψ split).IsHermitian := by
    unfold adhwFQSWARProductSplitMatrix
    exact kronecker_isHermitian _ _
      (fqsw_isHermitian_submatrix_equiv split.symm
        (adhwFQSWARState ψ).marginalA.pos.isHermitian)
      (adhwFQSWSigmaRState ψ).pos.isHermitian
  have hΔ_herm : Δ.IsHermitian := by
    dsimp [Δ]
    exact Matrix.IsHermitian.sub hRm_herm hPm_herm
  have hΔ_trace :
      partialTraceA (a := Prod q e) (b := r) Δ = 0 := by
    dsimp [Δ]
    rw [fqsw_partialTraceA_sub]
    rw [adhwFQSWARSplitMatrix_partialTraceA, adhwFQSWARProductSplitMatrix_partialTraceA]
    simp
  have hΔ_hs :
      (Δ * Δ).trace.re =
        adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    calc
      (Δ * Δ).trace.re = hilbertSchmidtSq Δ := by
        exact (fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian Δ hΔ_herm).symm
      _ = adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
        simpa [Δ] using adhwFQSWARCorrelationSplitMatrix_hilbertSchmidtSq ψ split
  have hpoint : ∀ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U =
        (g U).re := by
    intro U
    let K : CMatrix (Prod (Prod q e) r) :=
      Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
    let M : CMatrix (Prod e r) :=
      partialTraceA (a := q) (b := Prod e r)
        ((K * Δ * star K).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)
    have hconj : (K * Δ * star K).IsHermitian := by
      simpa [K, Matrix.star_eq_conjTranspose] using
        Matrix.isHermitian_mul_mul_conjTranspose K hΔ_herm
    have hsub :
        ((K * Δ * star K).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm).IsHermitian := by
      exact fqsw_isHermitian_submatrix_equiv
        (fqswQERToA2REquiv q e r).symm hconj
    have hM_herm : M.IsHermitian := by
      exact partialTraceA_isHermitian hsub
    rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation]
    rw [fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian M hM_herm]
  have hcomplex :=
    (fqsw_A2R_square_trace_average_eq (q := q) (e := e) (r := r) Δ).trans
      (fqsw_splitObservable_unitaryTwirl_swap_trace (q := q) (e := e) (r := r) Δ)
  have hreal := congrArg Complex.re hcomplex
  have haverage :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
        ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
          (adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
            adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
    calc
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
          ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (g U).re
            ∂unitaryHaarMeasure (a := Prod q e) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with U
          exact hpoint U
      _ = ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
          (adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
            adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
          rw [hre_integral]
          simpa [g, Δ, hΔ_trace, hΔ_hs, Complex.add_re, Complex.sub_re,
            Complex.mul_re, Complex.div_re] using hreal
  rw [haverage]
  unfold adhwFQSWHSOneShotExact
  rw [adhwFQSWSchur_half_sub_eq_HS_prefactor q e]

/-- ADHW fqsw.tex lines 682-747 in the nontrivial Schur case, stated as the
Hilbert--Schmidt average bound consumed by the one-shot assembly. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_le_of_nontrivial
    [Nonempty q] [Nontrivial (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWHSOneShotExact ψ q e := by
  exact le_of_eq (adhwFQSWProductDecouplingHilbertSchmidtAverage_eq_of_nontrivial
    ψ split)

/-- ADHW fqsw.tex lines 682-747, including the degenerate one-point split
case, stated as the Hilbert--Schmidt average bound consumed by the one-shot
assembly. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWHSOneShotExact ψ q e := by
  by_cases hnt : Nontrivial (Prod q e)
  · exact adhwFQSWProductDecouplingHilbertSchmidtAverage_le_of_nontrivial
      ψ split
  · haveI : Subsingleton (Prod q e) :=
      not_nontrivial_iff_subsingleton.mp hnt
    have hΔzero :=
      adhwFQSWARCorrelationSplitMatrix_eq_zero_of_subsingleton ψ split
    have hfun :
        (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U) =
        fun _ => 0 := by
      funext U
      rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation]
      rw [hΔzero]
      let K : CMatrix (Prod (Prod q e) r) :=
        Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
      let M : CMatrix (Prod e r) :=
        partialTraceA (a := q) (b := Prod e r)
          ((K * (0 : CMatrix (Prod (Prod q e) r)) * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)
      change hilbertSchmidtSq M = 0
      have hM : M = 0 := by
        ext x y
        simp [M, K, partialTraceA, Matrix.mul_apply]
      rw [hM]
      simp [hilbertSchmidtSq]
    rw [hfun, MeasureTheory.integral_zero]
    rw [adhwFQSWHSOneShotExact_eq_zero_of_subsingleton (q := q) (e := e) ψ]

/-- ADHW fqsw.tex lines 781-787, including the degenerate one-point split
case, stated as the max-mixed `A₂` Hilbert--Schmidt average bound consumed by
the one-shot assembly. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtAverage_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (Fintype.card e : ℝ) *
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  by_cases hnt : Nontrivial (Prod q e)
  · exact adhwFQSWMaxMixedA2HilbertSchmidtAverage_le_of_nontrivial
      ψ split
  · haveI : Subsingleton (Prod q e) :=
      not_nontrivial_iff_subsingleton.mp hnt
    classical
    let q0 : q := Classical.choice inferInstance
    haveI : Subsingleton e :=
      Function.Injective.subsingleton (f := fun y : e => (q0, y))
        (by intro x y h; exact congrArg Prod.snd h)
    have hfun :
        (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U) =
        fun _ => 0 := by
      funext U
      rw [adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary]
      rw [state_matrix_eq_maximallyMixed_of_subsingleton
        (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
          (adhwFQSWAliceIsometryOfSplitUnitary split U))]
      unfold adhwFQSWMaximallyMixedA2State
      rw [sub_self]
      simp [hilbertSchmidtSq]
    rw [hfun, MeasureTheory.integral_zero, mul_zero]
    change 0 ≤ adhwFQSWMaxMixedA2SqBound ψ q
    unfold adhwFQSWMaxMixedA2SqBound
    exact mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (by
        simpa [adhwFQSWAPurity] using
          hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalA.matrix))

/-- Fourth-root argument in the one-shot FQSW theorem of ADHW fqsw.tex
lines 553-568, assembled from the decoupling and max-mixed estimates in
ADHW fqsw.tex lines 580-841. -/
def adhwFQSWOneShotFourthRootArgument
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  (2 * (Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
      ((Fintype.card q : ℝ) ^ 2)) *
    (adhwFQSWARPurity ψ + 2 * adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

/-- ADHW one-shot FQSW trace-norm error bound from fqsw.tex lines 553-568. -/
def adhwFQSWOneShotErrorBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  2 * Real.sqrt (Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q))

/-- The ADHW one-shot fourth-root argument is nonnegative. -/
theorem adhwFQSWOneShotFourthRootArgument_nonneg
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] :
    0 ≤ adhwFQSWOneShotFourthRootArgument ψ q := by
  have hfactor :
      0 ≤ 2 * (Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
        ((Fintype.card q : ℝ) ^ 2) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hAR : 0 ≤ adhwFQSWARPurity ψ := by
    simpa [adhwFQSWARPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).matrix
  have hA : 0 ≤ adhwFQSWAPurity ψ := by
    simpa [adhwFQSWAPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).marginalA.matrix
  have hR : 0 ≤ adhwFQSWRPurity ψ := by
    simpa [adhwFQSWRPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).marginalB.matrix
  unfold adhwFQSWOneShotFourthRootArgument
  exact mul_nonneg hfactor (by nlinarith)

/-- Scalar fourth-root simplification used by the i.i.d. FQSW bridge. -/
private theorem fqsw_two_sqrt_sqrt_le_sqrt8_mul_of_le_four_mul_fourth
    {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (hxt : x ≤ 4 * t ^ 4) :
    2 * Real.sqrt (Real.sqrt x) ≤ Real.sqrt 8 * t := by
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have hinner :
      Real.sqrt x ≤ 2 * t ^ 2 := by
    have hright_nonneg : 0 ≤ 2 * t ^ 2 := by nlinarith
    have hsq :
        (Real.sqrt x) ^ 2 ≤ (2 * t ^ 2) ^ 2 := by
      rw [Real.sq_sqrt hx]
      have hright_sq : (2 * t ^ 2) ^ 2 = 4 * t ^ 4 := by ring
      rw [hright_sq]
      exact hxt
    exact (sq_le_sq₀ (Real.sqrt_nonneg x) hright_nonneg).mp hsq
  have hleft_nonneg : 0 ≤ 2 * Real.sqrt (Real.sqrt x) := by positivity
  have hright_nonneg : 0 ≤ Real.sqrt 8 * t := by
    exact mul_nonneg (Real.sqrt_nonneg _) ht
  have hsq :
      (2 * Real.sqrt (Real.sqrt x)) ^ 2 ≤ (Real.sqrt 8 * t) ^ 2 := by
    have hs8 : (Real.sqrt 8) ^ 2 = (8 : ℝ) :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
    have hsinner : (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt x :=
      Real.sq_sqrt (Real.sqrt_nonneg x)
    rw [mul_pow, mul_pow, hs8, hsinner]
    nlinarith
  exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mp hsq

/-- If the one-shot fourth-root argument is bounded by the ADHW i.i.d.
exponential tail, then the one-shot error obeys the simplified i.i.d.
exponent. -/
theorem adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_fourthRootArgument_le
    (φ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q]
    (n : ℕ) (δ : ℝ)
    (harg :
      adhwFQSWOneShotFourthRootArgument φ q ≤
        4 * (2 : ℝ) ^ (-(n : ℝ) * δ)) :
    adhwFQSWOneShotErrorBound φ q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) := by
  let X : ℝ := adhwFQSWOneShotFourthRootArgument φ q
  let T : ℝ := (2 : ℝ) ^ (-((n : ℝ) * δ / 4))
  have hX_nonneg : 0 ≤ X := by
    simpa [X] using adhwFQSWOneShotFourthRootArgument_nonneg φ q
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hT_four : T ^ 4 = (2 : ℝ) ^ (-(n : ℝ) * δ) := by
    dsimp [T]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hX_le : X ≤ 4 * T ^ 4 := by
    rw [hT_four]
    simpa [X] using harg
  simpa [adhwFQSWOneShotErrorBound, X, T] using
    fqsw_two_sqrt_sqrt_le_sqrt8_mul_of_le_four_mul_fourth hX_nonneg hT_nonneg hX_le

/-- Product-decoupling trace-norm average from the exact Hilbert--Schmidt
average in ADHW fqsw.tex lines 682-747. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWHSOneShotExact ψ q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e := by
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
            adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
            ∂unitaryHaarMeasure (a := Prod q e)) :=
          adhwFQSWProductDecouplingTraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
            ψ split
    _ ≤ (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e := by
          exact mul_le_mul_of_nonneg_left hHS
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Max-mixed `A₂` trace-norm average from the exact Hilbert--Schmidt
average in ADHW fqsw.tex lines 781-787. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWMaxMixedA2SqBound ψ q) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  exact
    (adhwFQSWMaxMixedA2TraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
      ψ split).trans hHS

/-- ADHW fqsw.tex lines 747-760: after the Hilbert--Schmidt average has been
evaluated, Cauchy--Schwarz and the Schur-prefactor estimate imply the
trace-norm square bound.  This is the algebraic tail of the decoupling proof;
the preceding Schur integral identity is supplied separately. -/
theorem adhwFQSW_traceNormSqBound_of_HSOneShotExact
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    [Fintype q] [Fintype e] [Nonempty q] [Nonempty e] :
    (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e ≤
      adhwFQSWTraceNormDecouplingSqBound ψ q := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  let dr : ℝ := Fintype.card r
  let c : ℝ :=
    (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1)
  let X : ℝ := adhwFQSWARPurity ψ
  let Y : ℝ := adhwFQSWAPurity ψ * adhwFQSWRPurity ψ
  let O : ℝ := adhwFQSWARProductOverlap ψ
  have hc_nonneg : 0 ≤ c := by
    simpa [c, dq, de] using adhwFQSW_HS_prefactor_nonneg q e
  have hc_le : c ≤ 1 / dq := by
    simpa [c, dq, de] using adhwFQSW_HS_prefactor_le_inv_card_q q e
  have hX_nonneg : 0 ≤ X := by
    simpa [X, adhwFQSWARPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).matrix
  have hY_nonneg : 0 ≤ Y := by
    exact mul_nonneg
      (by simpa [Y, adhwFQSWAPurity] using
        hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalA.matrix))
      (by simpa [Y, adhwFQSWRPurity] using
        hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalB.matrix))
  have hO_nonneg : 0 ≤ O := by
    simpa [O] using adhwFQSWARProductOverlap_nonneg ψ
  have hbracket_le : X - 2 * O + Y ≤ X + Y := by
    nlinarith
  have hsum_nonneg : 0 ≤ X + Y := by nlinarith
  have hc_mul :
      c * (X - 2 * O + Y) ≤ (1 / dq) * (X + Y) := by
    calc
      c * (X - 2 * O + Y) ≤ c * (X + Y) :=
        mul_le_mul_of_nonneg_left hbracket_le hc_nonneg
      _ ≤ (1 / dq) * (X + Y) :=
        mul_le_mul_of_nonneg_right hc_le hsum_nonneg
  have hcard_a : (Fintype.card a : ℝ) = dq * de := by
    have hnat : Fintype.card a = Fintype.card (Prod q e) :=
      Fintype.card_congr split
    rw [Fintype.card_prod] at hnat
    dsimp [dq, de]
    exact_mod_cast hnat
  unfold adhwFQSWHSOneShotExact adhwFQSWTraceNormDecouplingSqBound
  change de * dr * (c * (X - 2 * O + Y)) ≤
    ((Fintype.card a : ℝ) * dr / dq ^ 2) * (X + Y)
  rw [hcard_a]
  have hdq_pos : 0 < dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hscale_nonneg : 0 ≤ de * dr := by
    dsimp [de, dr]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hc_mul hscale_nonneg
  convert hscaled using 1 <;> field_simp [ne_of_gt hdq_pos] <;> ring

/-- Source-route Schur twirling record for ADHW fqsw.tex lines 642-678, the
Schur step inside the decoupling proof of fqsw.tex lines 580-841. -/
structure ADHWSchurTwirling
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] where
  pCoeff : ℝ
  qCoeff : ℝ
  pCoeff_eq : pCoeff = adhwFQSWSchurPCoeff q e
  qCoeff_eq : qCoeff = adhwFQSWSchurQCoeff q e

/-- Source-route Hilbert--Schmidt one-shot bound record for ADHW fqsw.tex
lines 680-747. -/
structure ADHWHSOneShotBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] where
  schur : ADHWSchurTwirling ψ q e
  hsAverage : ℝ
  hsAverage_eq : hsAverage = adhwFQSWHSOneShotExact ψ q e

/-- The source Schur-coefficient record is canonical: its fields are the two
coefficients appearing in ADHW fqsw.tex lines 642-678. -/
def adhwFQSWSchurTwirling
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ADHWSchurTwirling ψ q e where
  pCoeff := adhwFQSWSchurPCoeff q e
  qCoeff := adhwFQSWSchurQCoeff q e
  pCoeff_eq := rfl
  qCoeff_eq := rfl

/-- The source Hilbert--Schmidt one-shot expression record is canonical once
the Schur coefficients have been fixed. -/
def adhwFQSWHSOneShotBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ADHWHSOneShotBound ψ q e where
  schur := adhwFQSWSchurTwirling ψ q e
  hsAverage := adhwFQSWHSOneShotExact ψ q e
  hsAverage_eq := rfl

/-- Source-route ADHW trace-norm decoupling record for fqsw.tex lines 580-760,
including the Schur/HS route from fqsw.tex lines 642-747. -/
structure ADHWTraceNormDecouplingBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    (split : a ≃ Prod q e)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  hs : ADHWHSOneShotBound ψ q e
  traceNormAverageSq_le :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWTraceNormDecouplingSqBound ψ q

/-- Source-route max-mixed `A₂` estimate record for ADHW fqsw.tex lines
767-795. -/
structure ADHWMaxMixedA2Estimate
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    (split : a ≃ Prod q e)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  schur : ADHWSchurTwirling ψ q e
  maxMixedAverageSq_le :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWMaxMixedA2SqBound ψ q

/-- Split-specific trace-norm square-average tail for the product-decoupling
component.  The explicit hypothesis is the remaining Schur/HS average bridge
for the split unitary integrand; from that bridge the dimension Cauchy--Schwarz
tail and the ADHW `1/d_{A₁}` prefactor estimate give the public square bound. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWTraceNormDecouplingSqBound ψ q :=
  hHS.trans (adhwFQSW_traceNormSqBound_of_HSOneShotExact ψ split)

/-- Split-specific trace-norm square-average tail for the max-mixed `A₂`
component.  The explicit hypothesis is exactly the remaining Schur/max-mixed
average estimate for the split unitary integrand. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hMaxMixed :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWMaxMixedA2SqBound ψ q :=
  hMaxMixed

/-- Constructor for the split-specific ADHW trace-norm decoupling component
record, once the product-decoupling Schur/HS average bridge is available. -/
theorem exists_adhwFQSWTraceNormDecouplingBound
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e) :
    Nonempty (ADHWTraceNormDecouplingBound ψ q e split) := by
  refine ⟨?_⟩
  exact
    { hs := adhwFQSWHSOneShotBound ψ q e
      traceNormAverageSq_le :=
        adhwFQSWProductDecouplingTraceNormAverageSq_le ψ split hHS }

/-- Constructor for the split-specific ADHW trace-norm decoupling record from
the exact product-decoupling Hilbert--Schmidt average in fqsw.tex lines
682-747. -/
theorem exists_adhwFQSWTraceNormDecouplingBound_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWHSOneShotExact ψ q e) :
    Nonempty (ADHWTraceNormDecouplingBound ψ q e split) := by
  exact exists_adhwFQSWTraceNormDecouplingBound ψ split
    (adhwFQSWProductDecouplingTraceNormAverageSq_le_of_hilbertSchmidtAverage
      ψ split hHS)

/-- Constructor for the split-specific ADHW max-mixed `A₂` component record,
once the max-mixed Schur average estimate is available. -/
theorem exists_adhwFQSWMaxMixedA2Estimate
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hMaxMixed :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q) :
    Nonempty (ADHWMaxMixedA2Estimate ψ q e split) := by
  refine ⟨?_⟩
  exact
    { schur := adhwFQSWSchurTwirling ψ q e
      maxMixedAverageSq_le :=
        adhwFQSWMaxMixedA2TraceNormAverageSq_le ψ split hMaxMixed }

/-- Constructor for the split-specific ADHW max-mixed `A₂` record from the
exact Hilbert--Schmidt average in fqsw.tex lines 781-787. -/
theorem exists_adhwFQSWMaxMixedA2Estimate_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWMaxMixedA2SqBound ψ q) :
    Nonempty (ADHWMaxMixedA2Estimate ψ q e split) := by
  exact exists_adhwFQSWMaxMixedA2Estimate ψ split
    (adhwFQSWMaxMixedA2TraceNormAverageSq_le_of_hilbertSchmidtAverage
      ψ split hHS)

/-- The two source-route component square-average records imply the final ADHW
decoupling square-average bound after the triangle/product-contraction step. -/
theorem adhwFQSWFinalTraceNormAverageSq_le_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q := by
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
        2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
          ∂unitaryHaarMeasure (a := Prod q e)) +
        2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
          ∂unitaryHaarMeasure (a := Prod q e)) :=
      adhwFQSWCombinedTraceNormAverageSq_le_two_component_averages ψ split
    _ ≤ 2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q := by
      nlinarith [D.traceNormAverageSq_le, M.maxMixedAverageSq_le]

/-- The final ADHW trace-norm average is bounded by the square root of its
source component square-average bounds. -/
theorem adhwFQSWFinalTraceNormAverage_le_sqrt_source_bounds
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      Real.sqrt (2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q) := by
  have hL2 :=
    integral_le_sqrt_integral_sq_of_nonneg
      (μ := unitaryHaarMeasure (a := Prod q e))
      (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (by
        filter_upwards with U
        exact traceDistance_nonneg _ _)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
  have hsq := adhwFQSWFinalTraceNormAverageSq_le_component_records ψ split D M
  exact hL2.trans (Real.sqrt_le_sqrt hsq)

/-- Component-record Haar-selection input: if the source algebraic component
bound is below the ADHW fourth-root argument, the averaged final trace-norm
integrand satisfies the one-shot selection radius. -/
theorem adhwFQSWFinalTraceNormAverage_le_oneShotFourthRoot_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) := by
  exact (adhwFQSWFinalTraceNormAverage_le_sqrt_source_bounds ψ split D M).trans
    (Real.sqrt_le_sqrt hsource)

/-- The two source-route square-average component bounds are absorbed by the
single fourth-root argument in ADHW `thm:trueoneShotMother`.  The only
substantive inequality is the trace-one purity lower bound
`1 ≤ d_R Tr[(ψ^R)^2]`, applied to the reference marginal. -/
theorem adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] :
    2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
      2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
        adhwFQSWOneShotFourthRootArgument ψ q := by
  have hR : (1 : ℝ) ≤ (Fintype.card r : ℝ) * adhwFQSWRPurity ψ := by
    simpa [adhwFQSWRPurity] using
      (State.one_le_card_mul_hilbertSchmidtSq_matrix
        (ρ := (adhwFQSWARState ψ).marginalB))
  have hA_nonneg : 0 ≤ adhwFQSWAPurity ψ := by
    exact hilbertSchmidtSq_nonneg _
  have hfactor_nonneg :
      0 ≤ (Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2) := by
    exact div_nonneg
      (by exact_mod_cast Nat.zero_le (Fintype.card a))
      (sq_nonneg _)
  have hmaxMixed_absorbed :
      ((Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2)) *
          adhwFQSWAPurity ψ ≤
        ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
            ((Fintype.card q : ℝ) ^ 2)) *
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    have hmul := mul_le_mul_of_nonneg_left hR hfactor_nonneg
    have hmulA := mul_le_mul_of_nonneg_right hmul hA_nonneg
    convert hmulA using 1 <;> ring
  unfold adhwFQSWTraceNormDecouplingSqBound adhwFQSWMaxMixedA2SqBound
    adhwFQSWOneShotFourthRootArgument
  calc
    2 *
          ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
              (Fintype.card q : ℝ) ^ 2 *
            (adhwFQSWARPurity ψ + adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)) +
        2 * ((Fintype.card a : ℝ) / (Fintype.card q : ℝ) ^ 2 *
            adhwFQSWAPurity ψ) ≤
        2 *
          ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
              (Fintype.card q : ℝ) ^ 2 *
            (adhwFQSWARPurity ψ + adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)) +
          2 * (((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
              ((Fintype.card q : ℝ) ^ 2)) *
            adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
          nlinarith
    _ = 2 * (Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
          (Fintype.card q : ℝ) ^ 2 *
        (adhwFQSWARPurity ψ + 2 * adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
          ring

/-- The ADHW one-shot RHS is nonnegative. -/
theorem adhwFQSWOneShotErrorBound_nonneg
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] :
    0 ≤ adhwFQSWOneShotErrorBound ψ q :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- One-shot ADHW protocol assembly from a selected Alice isometry satisfying
the source decoupling radius.  This is the Uhlmann/protocol part of
`thm:trueoneShotMother` after the Haar-selection step has supplied the
concrete `U`. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) (pairing : e ≃ et)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) et))
    (hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨C, hC⟩ :=
    exists_fqswOneShotProtocol_traceNormError_le_of_decoupling
      ψ U pairing ((1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q))
      hcardTarget hcardRef hdec
  refine ⟨C, hC.trans ?_⟩
  rw [adhwFQSWOneShotErrorBound]
  ring_nf
  exact le_rfl

/-- Source-split one-shot ADHW assembly after Haar selection: once the
source factorization `A = A₁ × A₂` supplies Alice's isometry and the selected
decoupling estimate holds, the concrete FQSW protocol obeys the source
one-shot trace-norm bound. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_split_selected_decoupling
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplit split)).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
    ψ (adhwFQSWAliceIsometryOfSplit split) (Equiv.refl e) hcardTarget hcardRef hdec

/-- Source-split one-shot ADHW assembly from the trace-norm decoupling
integrand used by the Haar-selection step.  This is the bridge from the
selected split-unitary trace-norm estimate to the computed FQSW protocol. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_split_unitary_traceNorm_decoupling
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (htrace :
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  have hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) := by
    rw [adhwFQSWDecoupling_normalizedTraceDistance_eq_half_integrand]
    exact mul_le_mul_of_nonneg_left htrace (by norm_num)
  exact exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
    ψ (adhwFQSWAliceIsometryOfSplitUnitary split U) (Equiv.refl e)
    hcardTarget hcardRef hdec

/-- Haar-selection form of the ADHW one-shot route: an averaged trace-norm
decoupling estimate over unitaries on the split `A₁ × A₂` register selects a
concrete split-unitary FQSW protocol. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_split_unitary_haar_average
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (havg :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨U, hU⟩ :=
    unitaryHaar_exists_le_of_integral_le
      (a := Prod q e)
      (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split) havg
  exact exists_fqswOneShotProtocol_traceNormError_le_of_split_unitary_traceNorm_decoupling
    ψ split U hcardTarget hcardRef hU

/-- Output of the Haar-selection/decoupling stage of the ADHW one-shot proof:
a concrete Alice isometry satisfying the source decoupling radius, together
with the finite-dimensional reference-size side conditions needed by the
Uhlmann assembly step. -/
structure ADHWFQSWSelectedDecouplingIsometry
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  aliceIsometry : ReferenceIsometry a (Prod q e)
  ebitPairing : e ≃ et
  target_ref_card_le : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b)
  bob_ref_card_le : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) et)
  decoupling_le :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ aliceIsometry).normalizedTraceDistance
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
        (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)

namespace ADHWFQSWSelectedDecouplingIsometry

variable {ψ : PureVector (Prod (Prod a b) r)}
variable (S : ADHWFQSWSelectedDecouplingIsometry ψ q e et)

/-- The selected ADHW decoupling isometry supplies a concrete one-shot FQSW
protocol. -/
noncomputable def toOneShotProtocol : FQSWOneShotProtocol ψ q e et :=
  Classical.choose
    (exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
      ψ S.aliceIsometry S.ebitPairing S.target_ref_card_le S.bob_ref_card_le S.decoupling_le)

/-- The protocol constructed from the selected decoupling isometry obeys the
ADHW one-shot trace-norm bound. -/
theorem toOneShotProtocol_traceNormError_le :
    S.toOneShotProtocol.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  (Classical.choose_spec
    (exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
      ψ S.aliceIsometry S.ebitPairing S.target_ref_card_le S.bob_ref_card_le S.decoupling_le))

end ADHWFQSWSelectedDecouplingIsometry

/-- A selected decoupling isometry closes the one-shot ADHW protocol theorem
shape.  The remaining upstream task is to prove such an isometry exists from
the Schur/HS/Haar route. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling
    (ψ : PureVector (Prod (Prod a b) r))
    (S : ADHWFQSWSelectedDecouplingIsometry ψ q e et) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  ⟨S.toOneShotProtocol, S.toOneShotProtocol_traceNormError_le⟩

/-- Haar-selection form that produces the selected-decoupling record used by
the source-route one-shot theorem.  The remaining upstream task is the ADHW
Schur/HS calculation proving the averaged trace-norm bound. -/
theorem exists_adhwFQSWSelectedDecouplingIsometry_of_split_unitary_haar_average
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (havg :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ S : ADHWFQSWSelectedDecouplingIsometry ψ q e e,
      S.aliceIsometry =
        adhwFQSWAliceIsometryOfSplitUnitary split
          (Classical.choose
            (unitaryHaar_exists_le_of_integral_le
              (a := Prod q e)
              (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
                adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
              (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split)
              havg)) := by
  let hsel :=
    unitaryHaar_exists_le_of_integral_le
      (a := Prod q e)
      (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split) havg
  let U : Matrix.unitaryGroup (Prod q e) ℂ := Classical.choose hsel
  have hU :
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) :=
    Classical.choose_spec hsel
  have hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) := by
    rw [adhwFQSWDecoupling_normalizedTraceDistance_eq_half_integrand]
    exact mul_le_mul_of_nonneg_left hU (by norm_num)
  refine ⟨{ aliceIsometry := adhwFQSWAliceIsometryOfSplitUnitary split U
            ebitPairing := Equiv.refl e
            target_ref_card_le := hcardTarget
            bob_ref_card_le := hcardRef
            decoupling_le := hdec }, ?_⟩
  rfl

/-- Source-component form of Haar selection: the Schur/HS decoupling record,
the max-mixed `A₂` record, and the source algebraic absorption inequality
select a concrete Alice isometry for the ADHW one-shot protocol route. -/
theorem exists_adhwFQSWSelectedDecouplingIsometry_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    Nonempty (ADHWFQSWSelectedDecouplingIsometry ψ q e e) := by
  have havg :=
    adhwFQSWFinalTraceNormAverage_le_oneShotFourthRoot_of_component_records
      ψ split D M hsource
  obtain ⟨S, _hS⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_split_unitary_haar_average
      ψ split hcardTarget hcardRef havg
  exact ⟨S⟩

/-- Source-component one-shot protocol theorem: once the Schur/HS
decoupling record, max-mixed `A₂` record, source algebraic absorption
inequality, and Uhlmann dimension side conditions are available, the ADHW
one-shot FQSW protocol exists with the source trace-norm error bound. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨S⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_component_records
      ψ split D M hsource hcardTarget hcardRef
  exact exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling ψ S

/-- Source-closed component-record one-shot theorem: the ADHW source algebra
absorbs the trace-norm decoupling and max-mixed `A₂` component bounds into the
single one-shot fourth-root argument, so callers no longer provide that
inequality as an external hypothesis. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_source_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  exact exists_fqswOneShotProtocol_traceNormError_le_of_component_records
    ψ split D M
    (adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument ψ q)
    hcardTarget hcardRef

/-- One-shot FQSW theorem-shape record for
`thm:trueoneShotMother` in ADHW fqsw.tex lines 553-568.  Its proof route is
the ADHW decoupling, max-mixed `A₂`, Haar-selected Alice isometry, and Uhlmann
assembly in fqsw.tex lines 580-841.  The protocol is computed from the selected
decoupling data rather than stored as an independent field. -/
structure ADHWFQSWOneShotBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    (split : a ≃ Prod q e)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  traceNormDecoupling : ADHWTraceNormDecouplingBound ψ q e split
  maxMixedA2 : ADHWMaxMixedA2Estimate ψ q e split
  selectedDecoupling : ADHWFQSWSelectedDecouplingIsometry ψ q e e

namespace ADHWFQSWOneShotBound

variable {ψ : PureVector (Prod (Prod a b) r)}
variable {split : a ≃ Prod q e}
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable (H : ADHWFQSWOneShotBound ψ q e split)

/-- The assembled ADHW one-shot bound record computes the concrete one-shot
protocol by delegating to its selected decoupling witness. -/
noncomputable def toOneShotProtocol : FQSWOneShotProtocol ψ q e e :=
  ADHWFQSWSelectedDecouplingIsometry.toOneShotProtocol H.selectedDecoupling

/-- The computed protocol of an assembled ADHW one-shot bound satisfies the
standard ADHW one-shot trace-norm error bound. -/
theorem toOneShotProtocol_traceNormError_le :
    H.toOneShotProtocol.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  ADHWFQSWSelectedDecouplingIsometry.toOneShotProtocol_traceNormError_le
    H.selectedDecoupling

end ADHWFQSWOneShotBound

/-- Assemble the ADHW one-shot bound record from source-route decoupling and
max-mixed records once the Haar average has selected the concrete split-unitary
decoupling isometry. -/
theorem exists_adhwFQSWOneShotBound_of_split_unitary_haar_average
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (havg :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ H : ADHWFQSWOneShotBound ψ q e split,
      H.traceNormDecoupling = D ∧ H.maxMixedA2 = M := by
  obtain ⟨S, _hS⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_split_unitary_haar_average
      ψ split hcardTarget hcardRef havg
  exact ⟨{ traceNormDecoupling := D
           maxMixedA2 := M
           selectedDecoupling := S }, rfl, rfl⟩

/-- Assemble the ADHW one-shot bound record directly from the source component
records and the algebraic absorption inequality, without taking an averaged
trace-norm bound as an external input. -/
theorem exists_adhwFQSWOneShotBound_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ H : ADHWFQSWOneShotBound ψ q e split,
      H.traceNormDecoupling = D ∧ H.maxMixedA2 = M := by
  obtain ⟨S⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_component_records
      ψ split D M hsource hcardTarget hcardRef
  exact ⟨{ traceNormDecoupling := D
           maxMixedA2 := M
           selectedDecoupling := S }, rfl, rfl⟩

/-- Source-closed assembly of the ADHW one-shot bound record from the two
component records and the Uhlmann dimension side conditions. -/
theorem exists_adhwFQSWOneShotBound_of_source_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ H : ADHWFQSWOneShotBound ψ q e split,
      H.traceNormDecoupling = D ∧ H.maxMixedA2 = M := by
  exact exists_adhwFQSWOneShotBound_of_component_records
    ψ split D M
    (adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument ψ q)
    hcardTarget hcardRef

/-- The `n`-fold i.i.d. source regrouped as `(A^n × B^n) × R^n`, matching
the source notation `ψ' = (φ^{ABR})^{⊗ n}` in ADHW fqsw.tex lines 1093-1101. -/
def adhwFQSWIidPureVector (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    PureVector (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (ψ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n)

/-- The density state of the regrouped i.i.d. source `ψ'` from ADHW fqsw.tex
lines 1093-1101. -/
def adhwFQSWIidSourceState (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (adhwFQSWIidPureVector ψ n).state

/-- Alice's one-copy marginal used for the `Π_A` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemAState (ψ : PureVector (Prod (Prod a b) r)) : State a :=
  ψ.state.marginalA.marginalA

/-- Bob's one-copy marginal used for the `Π_B` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemBState (ψ : PureVector (Prod (Prod a b) r)) : State b :=
  ψ.state.marginalA.marginalB

/-- Reference one-copy marginal used for the `Π_R` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemRState (ψ : PureVector (Prod (Prod a b) r)) : State r :=
  ψ.state.marginalB

/-- Entropy `H(A)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyA (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  (adhwFQSWSystemAState ψ).vonNeumann

/-- Entropy `H(B)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyB (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  (adhwFQSWSystemBState ψ).vonNeumann

/-- Entropy `H(R)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyR (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  (adhwFQSWSystemRState ψ).vonNeumann

/-- The `A` marginal of the source-route `AR` state is the original source
`A` marginal. -/
theorem adhwFQSWARState_marginalA_eq_systemA
    (ψ : PureVector (Prod (Prod a b) r)) :
    (adhwFQSWARState ψ).marginalA = adhwFQSWSystemAState ψ := by
  apply State.ext
  ext i j
  simp [adhwFQSWARState, adhwFQSWSystemAState, State.stateMergingReferenceState,
    State.marginalA, partialTraceB, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The `R` marginal of the source-route `AR` state is the original reference
marginal. -/
theorem adhwFQSWARState_marginalB_eq_systemR
    (ψ : PureVector (Prod (Prod a b) r)) :
    (adhwFQSWARState ψ).marginalB = adhwFQSWSystemRState ψ := by
  apply State.ext
  ext i j
  simp [adhwFQSWARState, adhwFQSWSystemRState, State.stateMergingReferenceState,
    State.marginalB, partialTraceA, Fintype.sum_prod_type]

/-- The `AR` marginal in the ADHW FQSW source route has the same entropy as
the complementary source `B` system. -/
theorem adhwFQSWARState_vonNeumann_eq_entropyB
    (ψ : PureVector (Prod (Prod a b) r)) :
    (adhwFQSWARState ψ).vonNeumann = adhwFQSWEntropyB ψ := by
  let Ω : PureVector (Prod (Prod a r) b) :=
    ψ.reindex (fqswSourceToARBEquiv a b r)
  have hΩA : Ω.state.marginalA = adhwFQSWARState ψ := by
    apply State.ext
    ext i j
    simp [Ω, adhwFQSWARState, State.stateMergingReferenceState,
      fqswSourceToARBEquiv, PureVector.reindex_state, State.reindex,
      State.marginalA, partialTraceB, PureVector.state_matrix, rankOneMatrix_apply]
  have hΩB : Ω.state.marginalB = adhwFQSWSystemBState ψ := by
    apply State.ext
    ext i j
    simp [Ω, adhwFQSWSystemBState, fqswSourceToARBEquiv,
      PureVector.reindex_state, State.reindex, State.marginalB,
      State.marginalA, partialTraceA, partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply, Fintype.sum_prod_type]
  have hdual := State.pureVector_marginalA_vonNeumann_eq_marginalB Ω
  rw [hΩA, hΩB] at hdual
  simpa [adhwFQSWEntropyB] using hdual

/-- The source `AB` marginal has the same entropy as the complementary
reference system `R`. -/
theorem adhwFQSWSourceAB_vonNeumann_eq_entropyR
    (ψ : PureVector (Prod (Prod a b) r)) :
    ψ.state.marginalA.vonNeumann = adhwFQSWEntropyR ψ := by
  simpa [adhwFQSWEntropyR, adhwFQSWSystemRState] using
    State.pureVector_marginalA_vonNeumann_eq_marginalB ψ

/-- Source-route mutual information identity
`I(A;R) = H(A) + H(R) - H(B)`. -/
theorem adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB
    (ψ : PureVector (Prod (Prod a b) r)) :
    mutualInformation ψ.state.stateMergingReferenceState =
      adhwFQSWEntropyA ψ + adhwFQSWEntropyR ψ - adhwFQSWEntropyB ψ := by
  rw [← adhwFQSWARState]
  rw [mutualInformation]
  rw [adhwFQSWARState_marginalA_eq_systemA,
    adhwFQSWARState_marginalB_eq_systemR,
    adhwFQSWARState_vonNeumann_eq_entropyB]
  rfl

/-- Source-route mutual information identity
`I(A;B) = H(A) + H(B) - H(R)`. -/
theorem adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR
    (ψ : PureVector (Prod (Prod a b) r)) :
    mutualInformation ψ.state.marginalA =
      adhwFQSWEntropyA ψ + adhwFQSWEntropyB ψ - adhwFQSWEntropyR ψ := by
  rw [mutualInformation]
  rw [adhwFQSWSourceAB_vonNeumann_eq_entropyR]
  rfl

/-- Local partial-trace pairing for a right identity factor:
`Tr_B[X (T ⊗ I)] = Tr_B[X] T`. -/
private theorem adhwFQSW_partialTraceB_mul_kronecker_one_left
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (X : CMatrix (Prod α β)) (T : CMatrix α) :
    partialTraceB (a := α) (b := β) (X * Matrix.kronecker T (1 : CMatrix β)) =
      partialTraceB (a := α) (b := β) X * T := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Trace pairing for an observable acting only on the left tensor factor. -/
private theorem adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (M : CMatrix (Prod α β)) (T : CMatrix α) :
    (Matrix.kronecker T (1 : CMatrix β) * M).trace =
      (T * partialTraceB (a := α) (b := β) M).trace := by
  calc
    (Matrix.kronecker T (1 : CMatrix β) * M).trace =
        (M * Matrix.kronecker T (1 : CMatrix β)).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((partialTraceB (a := α) (b := β) M) * T).trace := by
      rw [← adhwFQSW_partialTraceB_mul_kronecker_one_left
        (α := α) (β := β) M T]
      exact (partialTraceB_trace (a := α) (b := β)
        (M * Matrix.kronecker T (1 : CMatrix β))).symm
    _ = (T * partialTraceB (a := α) (b := β) M).trace := by
      rw [Matrix.trace_mul_comm]

/-- Local partial-trace pairing for a left identity factor:
`Tr_A[X (I ⊗ T)] = Tr_A[X] T`. -/
private theorem adhwFQSW_partialTraceA_mul_kronecker_one_right
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq α]
    (X : CMatrix (Prod α β)) (T : CMatrix β) :
    partialTraceA (a := α) (b := β) (X * Matrix.kronecker (1 : CMatrix α) T) =
      partialTraceA (a := α) (b := β) X * T := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Trace pairing for an observable acting only on the right tensor factor. -/
private theorem adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq α]
    (M : CMatrix (Prod α β)) (T : CMatrix β) :
    (Matrix.kronecker (1 : CMatrix α) T * M).trace =
      (T * partialTraceA (a := α) (b := β) M).trace := by
  calc
    (Matrix.kronecker (1 : CMatrix α) T * M).trace =
        (M * Matrix.kronecker (1 : CMatrix α) T).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((partialTraceA (a := α) (b := β) M) * T).trace := by
      rw [← adhwFQSW_partialTraceA_mul_kronecker_one_right
        (α := α) (β := β) M T]
      exact (partialTraceA_trace (a := α) (b := β)
        (M * Matrix.kronecker (1 : CMatrix α) T)).symm
    _ = (T * partialTraceA (a := α) (b := β) M).trace := by
      rw [Matrix.trace_mul_comm]

/-- Lift an `A^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorA
    (n : ℕ) (PA : CMatrix (TensorPower a n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker
    (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
    (1 : CMatrix (TensorPower r n))

/-- Lift a `B^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorB
    (n : ℕ) (PB : CMatrix (TensorPower b n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker
    (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
    (1 : CMatrix (TensorPower r n))

/-- Lift an `R^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorR
    (n : ℕ) (PR : CMatrix (TensorPower r n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n))) PR

/-- The simultaneous lifted `A^nB^nR^n` projector
`Π_A ⊗ Π_B ⊗ Π_R`. -/
def adhwFQSWIidLiftProjectorTriple
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker (Matrix.kronecker PA PB) PR

/-- The simultaneously projected i.i.d. source matrix
`Π_A Π_B Π_R ρ Π_A Π_B Π_R`. -/
def adhwFQSWIidProjectedSourceMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi

/-- The lifted triple projector factors as the product of the three
single-register lifted projectors. -/
private theorem adhwFQSWIidLiftProjectorTriple_eq_mul
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
        adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
  ext x y
  simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
    adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

-- Algebraic decomposition behind the simultaneous-projector union bound.
omit [Fintype a] [Fintype b] [Fintype r] in
private theorem adhwFQSWIidLiftProjector_union_decomp
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    ((1 - adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) +
        (1 - adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) +
          (1 - adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR)) -
        (1 - adhwFQSWIidLiftProjectorTriple
          (a := a) (b := b) (r := r) n PA PB PR) =
      Matrix.kronecker (Matrix.kronecker (1 - PA) (1 - PB))
          (1 : CMatrix (TensorPower r n)) +
        Matrix.kronecker (1 - Matrix.kronecker PA PB) (1 - PR) := by
  ext x y
  rcases x with ⟨⟨xa, xb⟩, xr⟩
  rcases y with ⟨⟨ya, yb⟩, yr⟩
  by_cases ha : xa = ya
  · subst ya
    by_cases hb : xb = yb
    · subst yb
      by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hr]
        try ring
    · by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hb]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hb, hr]
        try ring
  · by_cases hb : xb = yb
    · subst yb
      by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hr]
        try ring
    · by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hb]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hb, hr]
        try ring

/-- Simultaneous-projector union bound on the grouped i.i.d. source register. -/
private theorem adhwFQSWIidLiftProjector_union_bound
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef)
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR) :
    (1 - adhwFQSWIidLiftProjectorTriple
        (a := a) (b := b) (r := r) n PA PB PR) ≤
      (1 - adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) +
        (1 - adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) +
          (1 - adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) := by
  rw [Matrix.le_iff]
  rw [adhwFQSWIidLiftProjector_union_decomp]
  have hAcomp := projector_one_sub_posSemidef PA hPA hPAid
  have hBcomp := projector_one_sub_posSemidef PB hPB hPBid
  have hRcomp := projector_one_sub_posSemidef PR hPR hPRid
  have hAB : (Matrix.kronecker PA PB).PosSemidef := hPA.kronecker hPB
  have hABid : Matrix.kronecker PA PB * Matrix.kronecker PA PB =
      Matrix.kronecker PA PB := by
    simpa [hPAid, hPBid] using (Matrix.mul_kronecker_mul PA PA PB PB).symm
  have hABcomp := projector_one_sub_posSemidef (Matrix.kronecker PA PB) hAB hABid
  exact (hAcomp.kronecker hBcomp).kronecker Matrix.PosSemidef.one |>.add
    (hABcomp.kronecker hRcomp)

/-- The `A^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy `A` marginal. -/
private theorem adhwFQSWIidSourceState_marginalA_eq_tensorPower
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).marginalA.marginalA =
      (adhwFQSWSystemAState ψ).tensorPower n := by
  have hAB :
      (adhwFQSWIidSourceState ψ n).marginalA =
        ψ.state.marginalA.tensorPowerBipartite n := by
    simpa [adhwFQSWIidSourceState, adhwFQSWIidPureVector,
      fqswTensorPowerTripartiteEquiv, PureVector.tensorPowerTripartiteGrouped,
      PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
      PureVector.tensorPower_state] using
      PureVector.tensorPowerTripartiteGrouped_marginalAB (a := a) (b := b) (c := r) ψ n
  rw [hAB]
  simpa [adhwFQSWSystemAState] using
    State.tensorPowerBipartite_marginalA (rho := ψ.state.marginalA) n

/-- The `B^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy `B` marginal. -/
private theorem adhwFQSWIidSourceState_marginalB_eq_tensorPower
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).marginalA.marginalB =
      (adhwFQSWSystemBState ψ).tensorPower n := by
  have hAB :
      (adhwFQSWIidSourceState ψ n).marginalA =
        ψ.state.marginalA.tensorPowerBipartite n := by
    simpa [adhwFQSWIidSourceState, adhwFQSWIidPureVector,
      fqswTensorPowerTripartiteEquiv, PureVector.tensorPowerTripartiteGrouped,
      PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
      PureVector.tensorPower_state] using
      PureVector.tensorPowerTripartiteGrouped_marginalAB (a := a) (b := b) (c := r) ψ n
  rw [hAB]
  simpa [adhwFQSWSystemBState] using
    State.tensorPowerBipartite_marginalB (rho := ψ.state.marginalA) n

/-- Tracing the `AC` marginal down to `C` agrees with the direct `C`
marginal for a left-associated tripartite state. -/
private theorem adhwFQSW_marginalAC_marginalB_eq_marginalB
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (ρ : State (Prod (Prod α β) γ)) :
    ρ.marginalAC.marginalB = ρ.marginalB := by
  apply State.ext
  ext x y
  simp [State.marginalAC, State.marginalB, partialTraceA, Fintype.sum_prod_type]

/-- The `R^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy reference marginal. -/
private theorem adhwFQSWIidSourceState_marginalR_eq_tensorPower
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).marginalB =
      (adhwFQSWSystemRState ψ).tensorPower n := by
  let ρ := adhwFQSWIidSourceState ψ n
  have hAC :
      ρ.marginalAC = ψ.state.marginalAC.tensorPowerBipartite n := by
    simpa [ρ, adhwFQSWIidSourceState, adhwFQSWIidPureVector,
      fqswTensorPowerTripartiteEquiv, PureVector.tensorPowerTripartiteGrouped,
      PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
      PureVector.tensorPower_state] using
      PureVector.tensorPowerTripartiteGrouped_marginalAC (a := a) (b := b) (c := r) ψ n
  calc
    ρ.marginalB = ρ.marginalAC.marginalB := by
      exact (adhwFQSW_marginalAC_marginalB_eq_marginalB ρ).symm
    _ = (ψ.state.marginalAC.tensorPowerBipartite n).marginalB := by
      rw [hAC]
    _ = (ψ.state.marginalAC.marginalB).tensorPower n := by
      exact State.tensorPowerBipartite_marginalB (rho := ψ.state.marginalAC) n
    _ = (adhwFQSWSystemRState ψ).tensorPower n := by
      have hR := adhwFQSW_marginalAC_marginalB_eq_marginalB ψ.state
      simpa [adhwFQSWSystemRState] using congrArg (fun σ : State r => σ.tensorPower n) hR

/-- Acceptance identity for the lifted `A^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceA
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n
        ((adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
      (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ
  have htraceR :
      (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) *
          ρ.matrix).trace).re =
        (((Matrix.kronecker PA (1 : CMatrix (TensorPower b n))) *
            ρ.marginalA.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
      (α := Prod (TensorPower a n) (TensorPower b n)) (β := TensorPower r n)
      (M := ρ.matrix)
      (T := Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
    simpa [adhwFQSWIidLiftProjectorA, ρ, PA, State.marginalA_matrix] using
      congrArg Complex.re h
  have htraceB :
      (((Matrix.kronecker PA (1 : CMatrix (TensorPower b n))) *
            ρ.marginalA.matrix).trace).re =
        ((PA * ρ.marginalA.marginalA.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
      (α := TensorPower a n) (β := TensorPower b n)
      (M := ρ.marginalA.matrix) (T := PA)
    simpa [State.marginalA_matrix] using congrArg Complex.re h
  have hmarg := congrArg (fun σ : State (TensorPower a n) => σ.matrix)
    (adhwFQSWIidSourceState_marginalA_eq_tensorPower ψ n)
  have hmarg' :
      ρ.marginalA.marginalA.matrix =
        ((adhwFQSWSystemAState ψ).tensorPower n).matrix := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n
        ((adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
        ((PA * ρ.marginalA.marginalA.matrix).trace).re := by
          rw [htraceR, htraceB]
    _ = (((adhwFQSWSystemAState ψ).tensorPower n).matrix * PA).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PA] using
            (adhwFQSWSystemAState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Acceptance identity for the lifted `B^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceB
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n
        ((adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
      (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ
  have htraceR :
      (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) *
          ρ.matrix).trace).re =
        (((Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB) *
            ρ.marginalA.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
      (α := Prod (TensorPower a n) (TensorPower b n)) (β := TensorPower r n)
      (M := ρ.matrix)
      (T := Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
    simpa [adhwFQSWIidLiftProjectorB, ρ, PB, State.marginalA_matrix] using
      congrArg Complex.re h
  have htraceA :
      (((Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB) *
            ρ.marginalA.matrix).trace).re =
        ((PB * ρ.marginalA.marginalB.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
      (α := TensorPower a n) (β := TensorPower b n)
      (M := ρ.marginalA.matrix) (T := PB)
    simpa [State.marginalB_matrix] using congrArg Complex.re h
  have hmarg := congrArg (fun σ : State (TensorPower b n) => σ.matrix)
    (adhwFQSWIidSourceState_marginalB_eq_tensorPower ψ n)
  have hmarg' :
      ρ.marginalA.marginalB.matrix =
        ((adhwFQSWSystemBState ψ).tensorPower n).matrix := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n
        ((adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
        ((PB * ρ.marginalA.marginalB.matrix).trace).re := by
          rw [htraceR, htraceA]
    _ = (((adhwFQSWSystemBState ψ).tensorPower n).matrix * PB).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PB] using
            (adhwFQSWSystemBState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Acceptance identity for the lifted `R^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceR
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n
        ((adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
      (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ
  have htraceAB :
      (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) *
          ρ.matrix).trace).re =
        ((PR * ρ.marginalB.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
      (α := Prod (TensorPower a n) (TensorPower b n)) (β := TensorPower r n)
      (M := ρ.matrix) (T := PR)
    simpa [adhwFQSWIidLiftProjectorR, ρ, PR, State.marginalB_matrix] using
      congrArg Complex.re h
  have hmarg := congrArg (fun σ : State (TensorPower r n) => σ.matrix)
    (adhwFQSWIidSourceState_marginalR_eq_tensorPower ψ n)
  have hmarg' :
      ρ.marginalB.matrix =
        ((adhwFQSWSystemRState ψ).tensorPower n).matrix := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n
        ((adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
        ((PR * ρ.marginalB.matrix).trace).re := by
          rw [htraceAB]
    _ = (((adhwFQSWSystemRState ψ).tensorPower n).matrix * PR).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PR] using
            (adhwFQSWSystemRState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Selectively projecting the right register cannot increase the left
marginal in Loewner order. -/
private theorem adhwFQSW_partialTraceB_selective_projector_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (X : CMatrix (Prod α β)) (hX : X.PosSemidef)
    (Q : CMatrix β) (hQ : Q.PosSemidef) (hQid : Q * Q = Q) :
    partialTraceB (a := α) (b := β)
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q) ≤
      partialTraceB (a := α) (b := β) X := by
  rw [Matrix.le_iff]
  let D : CMatrix α :=
    partialTraceB (a := α) (b := β) X -
      partialTraceB (a := α) (b := β)
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q)
  change D.PosSemidef
  have hbranch_psd :
      (Matrix.kronecker (1 : CMatrix α) Q * X *
        Matrix.kronecker (1 : CMatrix α) Q).PosSemidef := by
    let K : CMatrix (Prod α β) := Matrix.kronecker (1 : CMatrix α) Q
    have hK : K.PosSemidef := Matrix.PosSemidef.one.kronecker hQ
    have h := hX.mul_mul_conjTranspose_same K
    rw [hK.isHermitian.eq] at h
    simpa [K, Matrix.mul_assoc] using h
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (partialTraceB_isHermitian hX.isHermitian).sub
      (partialTraceB_isHermitian hbranch_psd.isHermitian)
  rw [cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hDherm]
  intro W hW
  have hQcomp := projector_one_sub_posSemidef Q hQ hQid
  have hWQcomp : (Matrix.kronecker W (1 - Q)).PosSemidef :=
    hW.kronecker hQcomp
  have hnonneg :
      0 ≤ ((Matrix.kronecker W (1 - Q) * X).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hWQcomp hX
  have htrace_full :
      ((W * partialTraceB (a := α) (b := β) X).trace).re =
        ((Matrix.kronecker W (1 : CMatrix β) * X).trace).re := by
    exact congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
        (α := α) (β := β) X W).symm
  have htrace_branch :
      ((W * partialTraceB (a := α) (b := β)
          (Matrix.kronecker (1 : CMatrix α) Q * X *
            Matrix.kronecker (1 : CMatrix α) Q)).trace).re =
        ((Matrix.kronecker W Q * X).trace).re := by
    have hpair := congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
        (α := α) (β := β)
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q) W).symm
    rw [hpair]
    congr 1
    let K : CMatrix (Prod α β) := Matrix.kronecker (1 : CMatrix α) Q
    let L : CMatrix (Prod α β) := Matrix.kronecker W (1 : CMatrix β)
    have hKLK : K * L * K = Matrix.kronecker W Q := by
      have hKL : K * L = Matrix.kronecker W Q := by
        simpa [K, L, Matrix.one_mul, Matrix.mul_one] using
          (Matrix.mul_kronecker_mul (1 : CMatrix α) W Q (1 : CMatrix β)).symm
      calc
        K * L * K = (Matrix.kronecker W Q) * Matrix.kronecker (1 : CMatrix α) Q := by
          rw [hKL]
        _ = Matrix.kronecker W (Q * Q) := by
          simpa [Matrix.mul_one] using
            (Matrix.mul_kronecker_mul W (1 : CMatrix α) Q Q).symm
        _ = Matrix.kronecker W Q := by rw [hQid]
    calc
      (Matrix.kronecker W (1 : CMatrix β) *
          (Matrix.kronecker (1 : CMatrix α) Q * X *
            Matrix.kronecker (1 : CMatrix α) Q)).trace =
          ((K * L * K) * X).trace := by
            have hassoc :
                Matrix.kronecker W (1 : CMatrix β) *
                    (Matrix.kronecker (1 : CMatrix α) Q * X *
                      Matrix.kronecker (1 : CMatrix α) Q) =
                  L * K * X * K := by
              simp [K, L]
              noncomm_ring
            rw [hassoc]
            rw [Matrix.trace_mul_cycle]
            congr 1
            noncomm_ring
      _ = (Matrix.kronecker W Q * X).trace := by
            rw [hKLK]
  have htrace_decomp :
      ((W * D).trace).re =
        ((Matrix.kronecker W (1 - Q) * X).trace).re := by
    dsimp [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [htrace_full]
    have htrace_branch_expanded := htrace_branch
    simp only [Matrix.kronecker] at htrace_branch_expanded
    rw [htrace_branch_expanded]
    have hsplit :
        Matrix.kronecker W (1 : CMatrix β) - Matrix.kronecker W Q =
          Matrix.kronecker W (1 - Q) := by
      ext x y
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply]
      ring
    have hsplit_expanded := hsplit
    simp only [Matrix.kronecker] at hsplit_expanded
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
    simp only [Matrix.kronecker]
    rw [hsplit_expanded]
  rw [Matrix.trace_mul_comm]
  rw [htrace_decomp]
  exact hnonneg

/-- Selectively projecting the left register cannot increase the right
marginal in Loewner order. -/
private theorem adhwFQSW_partialTraceA_selective_projector_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (X : CMatrix (Prod α β)) (hX : X.PosSemidef)
    (Q : CMatrix α) (hQ : Q.PosSemidef) (hQid : Q * Q = Q) :
    partialTraceA (a := α) (b := β)
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β)) ≤
      partialTraceA (a := α) (b := β) X := by
  rw [Matrix.le_iff]
  let D : CMatrix β :=
    partialTraceA (a := α) (b := β) X -
      partialTraceA (a := α) (b := β)
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β))
  change D.PosSemidef
  have hbranch_psd :
      (Matrix.kronecker Q (1 : CMatrix β) * X *
        Matrix.kronecker Q (1 : CMatrix β)).PosSemidef := by
    let K : CMatrix (Prod α β) := Matrix.kronecker Q (1 : CMatrix β)
    have hK : K.PosSemidef := hQ.kronecker Matrix.PosSemidef.one
    have h := hX.mul_mul_conjTranspose_same K
    rw [hK.isHermitian.eq] at h
    simpa [K, Matrix.mul_assoc] using h
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (partialTraceA_isHermitian hX.isHermitian).sub
      (partialTraceA_isHermitian hbranch_psd.isHermitian)
  rw [cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hDherm]
  intro W hW
  have hQcomp := projector_one_sub_posSemidef Q hQ hQid
  have hQcompW : (Matrix.kronecker (1 - Q) W).PosSemidef :=
    hQcomp.kronecker hW
  have hnonneg :
      0 ≤ ((Matrix.kronecker (1 - Q) W * X).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hQcompW hX
  have htrace_full :
      ((W * partialTraceA (a := α) (b := β) X).trace).re =
        ((Matrix.kronecker (1 : CMatrix α) W * X).trace).re := by
    exact congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
        (α := α) (β := β) X W).symm
  have htrace_branch :
      ((W * partialTraceA (a := α) (b := β)
          (Matrix.kronecker Q (1 : CMatrix β) * X *
            Matrix.kronecker Q (1 : CMatrix β))).trace).re =
        ((Matrix.kronecker Q W * X).trace).re := by
    have hpair := congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
        (α := α) (β := β)
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β)) W).symm
    rw [hpair]
    congr 1
    let K : CMatrix (Prod α β) := Matrix.kronecker Q (1 : CMatrix β)
    let L : CMatrix (Prod α β) := Matrix.kronecker (1 : CMatrix α) W
    have hKLK : K * L * K = Matrix.kronecker Q W := by
      have hKL : K * L = Matrix.kronecker Q W := by
        simpa [K, L, Matrix.one_mul, Matrix.mul_one] using
          (Matrix.mul_kronecker_mul Q (1 : CMatrix α) (1 : CMatrix β) W).symm
      calc
        K * L * K = (Matrix.kronecker Q W) * Matrix.kronecker Q (1 : CMatrix β) := by
          rw [hKL]
        _ = Matrix.kronecker (Q * Q) W := by
          simpa [Matrix.mul_one] using
            (Matrix.mul_kronecker_mul Q Q W (1 : CMatrix β)).symm
        _ = Matrix.kronecker Q W := by rw [hQid]
    calc
      (Matrix.kronecker (1 : CMatrix α) W *
          (Matrix.kronecker Q (1 : CMatrix β) * X *
            Matrix.kronecker Q (1 : CMatrix β))).trace =
          ((K * L * K) * X).trace := by
            have hassoc :
                Matrix.kronecker (1 : CMatrix α) W *
                    (Matrix.kronecker Q (1 : CMatrix β) * X *
                      Matrix.kronecker Q (1 : CMatrix β)) =
                  L * K * X * K := by
              simp [K, L]
              noncomm_ring
            rw [hassoc]
            rw [Matrix.trace_mul_cycle]
            congr 1
            noncomm_ring
      _ = (Matrix.kronecker Q W * X).trace := by
            rw [hKLK]
  have htrace_decomp :
      ((W * D).trace).re =
        ((Matrix.kronecker (1 - Q) W * X).trace).re := by
    dsimp [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [htrace_full]
    have htrace_branch_expanded := htrace_branch
    simp only [Matrix.kronecker] at htrace_branch_expanded
    rw [htrace_branch_expanded]
    have hsplit :
        Matrix.kronecker (1 : CMatrix α) W - Matrix.kronecker Q W =
          Matrix.kronecker (1 - Q) W := by
      ext x y
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply]
      ring
    have hsplit_expanded := hsplit
    simp only [Matrix.kronecker] at hsplit_expanded
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
    simp only [Matrix.kronecker]
    rw [hsplit_expanded]
  rw [Matrix.trace_mul_comm]
  rw [htrace_decomp]
  exact hnonneg

private theorem adhwFQSW_partialTraceB_sub
    {α : Type u} {β : Type v} [Fintype β]
    (X Y : CMatrix (Prod α β)) :
    partialTraceB (a := α) (b := β) (X - Y) =
      partialTraceB (a := α) (b := β) X -
        partialTraceB (a := α) (b := β) Y := by
  ext i j
  simp [partialTraceB, Finset.sum_sub_distrib]

private theorem adhwFQSW_partialTraceA_sub
    {α : Type u} {β : Type v} [Fintype α]
    (X Y : CMatrix (Prod α β)) :
    partialTraceA (a := α) (b := β) (X - Y) =
      partialTraceA (a := α) (b := β) X -
        partialTraceA (a := α) (b := β) Y := by
  ext i j
  simp [partialTraceA, Finset.sum_sub_distrib]

private theorem adhwFQSW_partialTraceB_mono
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    {X Y : CMatrix (Prod α β)} (hXY : X ≤ Y) :
    partialTraceB (a := α) (b := β) X ≤
      partialTraceB (a := α) (b := β) Y := by
  rw [Matrix.le_iff]
  have hdiff : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
  have hpt := partialTraceB_posSemidef (a := α) (b := β) hdiff
  simpa [adhwFQSW_partialTraceB_sub] using hpt

private theorem adhwFQSW_partialTraceA_mono
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    {X Y : CMatrix (Prod α β)} (hXY : X ≤ Y) :
    partialTraceA (a := α) (b := β) X ≤
      partialTraceA (a := α) (b := β) Y := by
  rw [Matrix.le_iff]
  have hdiff : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
  have hpt := partialTraceA_posSemidef (a := α) (b := β) hdiff
  simpa [adhwFQSW_partialTraceA_sub] using hpt

private theorem adhwFQSW_smul_le_smul_of_nonneg
    {α : Type u} [Fintype α] [DecidableEq α]
    {A B : CMatrix α} {c : ℝ} (hc : 0 ≤ c) (hAB : A ≤ B) :
    (((c : ℝ) : ℂ) • A) ≤ (((c : ℝ) : ℂ) • B) := by
  rw [Matrix.le_iff] at hAB ⊢
  have hscaled : (((c : ℝ) : ℂ) • (B - A)).PosSemidef :=
    Matrix.PosSemidef.smul hAB (by exact_mod_cast hc)
  simpa [smul_sub] using hscaled

private theorem adhwFQSW_real_smul_smul
    {α : Type u} (c d : ℝ) (M : CMatrix α) :
    (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • M)) =
      ((((c * d : ℝ) : ℂ) • M)) := by
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]

private theorem adhwFQSW_complex_smul_smul
    {α : Type u} (c d : ℂ) (M : CMatrix α) :
    c • (d • M) = (c * d) • M := by
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, mul_assoc]

private theorem adhwFQSW_sum_four_comm
    {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
        = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]

private theorem adhwFQSW_sum_five_comm
    {α β γ δ ε M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [AddCommMonoid M]
    (f : α → β → γ → δ → ε → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ c, ∑ e, ∑ a, ∑ d, ∑ b, f a b c d e := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e)
        = ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, ∑ e, f a b c d e := by
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ e, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ e, ∑ b, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ e, ∑ a, ∑ b, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ e, ∑ a, ∑ d, ∑ b, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro e _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]

private theorem adhwFQSW_sum_five_comm_leftPair
    {α β γ δ ε M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [AddCommMonoid M]
    (f : α → β → γ → δ → ε → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ d, ∑ a, ∑ e, ∑ c, f a b c d e := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e)
        = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e := by
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, ∑ d, ∑ c, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ a, ∑ c, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ a, ∑ e, ∑ c, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro d _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]

private theorem adhwFQSWIidLiftProjectorA_marginalA_marginalA
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) :
    partialTraceB (a := TensorPower a n) (b := TensorPower b n)
      (partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.matrix *
          adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA)) =
      PA * ρ.marginalA.marginalA.matrix * PA := by
  ext x y
  simp [adhwFQSWIidLiftProjectorA, State.marginalA_matrix, partialTraceB,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun b0 r0 v0 u0 =>
        PA x u0 * (ρ.matrix ((u0, b0), r0) ((v0, b0), r0) * PA v0 y)))

private theorem adhwFQSWIidLiftProjectorB_marginalA_marginalB
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PB : CMatrix (TensorPower b n)) :
    partialTraceA (a := TensorPower a n) (b := TensorPower b n)
      (partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.matrix *
          adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB)) =
      PB * ρ.marginalA.marginalB.matrix * PB := by
  ext x y
  simp [adhwFQSWIidLiftProjectorB, State.marginalA_matrix, State.marginalB_matrix,
    partialTraceA, partialTraceB, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun a0 r0 v0 u0 =>
        PB x u0 * (ρ.matrix ((a0, u0), r0) ((a0, v0), r0) * PB v0 y)))

private theorem adhwFQSWIidLiftProjectorR_marginalB
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PR : CMatrix (TensorPower r n)) :
    partialTraceA (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.matrix *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) =
      PR * ρ.marginalB.matrix * PR := by
  ext x y
  simp [adhwFQSWIidLiftProjectorR, State.marginalB_matrix, partialTraceA,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun a0 b0 v0 u0 =>
        PR x u0 * (ρ.matrix ((a0, b0), u0) ((a0, b0), v0) * PR v0 y)))

private theorem adhwFQSWIidLiftProjectorA_posSemidef
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (hPA : PA.PosSemidef) :
    (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA).PosSemidef :=
  (hPA.kronecker Matrix.PosSemidef.one).kronecker Matrix.PosSemidef.one

private theorem adhwFQSWIidLiftProjectorB_posSemidef
    (n : ℕ) (PB : CMatrix (TensorPower b n)) (hPB : PB.PosSemidef) :
    (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB).PosSemidef :=
  (Matrix.PosSemidef.one.kronecker hPB).kronecker Matrix.PosSemidef.one

private theorem adhwFQSWIidLiftProjectorR_posSemidef
    (n : ℕ) (PR : CMatrix (TensorPower r n)) (hPR : PR.PosSemidef) :
    (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR).PosSemidef :=
  Matrix.PosSemidef.one.kronecker hPR

private theorem adhwFQSWIidLiftProjectorTriple_posSemidef
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef) :
    (adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR).PosSemidef :=
  (hPA.kronecker hPB).kronecker hPR

private theorem adhwFQSWIidLiftProjectorA_idempotent
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (hPAid : PA * PA = PA) :
    adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
      adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA =
        adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA := by
  have hAB :
      Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) =
        Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
    simpa [hPAid] using
      (Matrix.mul_kronecker_mul PA PA (1 : CMatrix (TensorPower b n))
        (1 : CMatrix (TensorPower b n))).symm
  calc
    adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
        adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA =
      Matrix.kronecker
        (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
        ((1 : CMatrix (TensorPower r n)) * (1 : CMatrix (TensorPower r n))) := by
          simpa [adhwFQSWIidLiftProjectorA] using
            (Matrix.mul_kronecker_mul
              (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
              (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
              (1 : CMatrix (TensorPower r n)) (1 : CMatrix (TensorPower r n))).symm
    _ = adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA := by
          rw [hAB]
          simp [adhwFQSWIidLiftProjectorA]

private theorem adhwFQSWIidLiftProjectorB_idempotent
    (n : ℕ) (PB : CMatrix (TensorPower b n)) (hPBid : PB * PB = PB) :
    adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB *
      adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB =
        adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB := by
  have hAB :
      Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB =
        Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
    simpa [hPBid] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (TensorPower a n))
        (1 : CMatrix (TensorPower a n)) PB PB).symm
  calc
    adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB *
        adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB =
      Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
        ((1 : CMatrix (TensorPower r n)) * (1 : CMatrix (TensorPower r n))) := by
          simpa [adhwFQSWIidLiftProjectorB] using
            (Matrix.mul_kronecker_mul
              (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
              (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
              (1 : CMatrix (TensorPower r n)) (1 : CMatrix (TensorPower r n))).symm
    _ = adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB := by
          rw [hAB]
          simp [adhwFQSWIidLiftProjectorB]

private theorem adhwFQSWIidLiftProjectorR_idempotent
    (n : ℕ) (PR : CMatrix (TensorPower r n)) (hPRid : PR * PR = PR) :
    adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR *
      adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR =
        adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
  simpa [adhwFQSWIidLiftProjectorR, hPRid] using
    (Matrix.mul_kronecker_mul
      (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
      (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n))) PR PR).symm

private theorem adhwFQSWIidLiftProjectorTriple_idempotent
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
      adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR := by
  have hAB :
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
        Matrix.kronecker PA PB := by
    simpa [hPAid, hPBid] using (Matrix.mul_kronecker_mul PA PA PB PB).symm
  calc
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      Matrix.kronecker
        (Matrix.kronecker PA PB * Matrix.kronecker PA PB) (PR * PR) := by
          simpa [adhwFQSWIidLiftProjectorTriple] using
            (Matrix.mul_kronecker_mul (Matrix.kronecker PA PB) (Matrix.kronecker PA PB)
              PR PR).symm
    _ = adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR := by
          rw [hAB, hPRid]
          simp [adhwFQSWIidLiftProjectorTriple]

private theorem adhwFQSW_rejection_trace_eq_one_sub_acceptance
    (ρ : State a) (P : CMatrix a) :
    ((ρ.matrix * (1 - P)).trace).re = 1 - ((P * ρ.matrix).trace).re := by
  have hmul : ρ.matrix * (1 - P) = ρ.matrix - ρ.matrix * P := by
    noncomm_ring
  rw [hmul, Matrix.trace_sub, Complex.sub_re, ρ.trace_eq_one, Complex.one_re]
  rw [Matrix.trace_mul_comm]

private theorem adhwFQSWIidLiftProjectorTriple_acceptance_of_single
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (η : ℝ)
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef)
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR)
    (haccA :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.matrix).trace).re)
    (haccB :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.matrix).trace).re)
    (haccR :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.matrix).trace).re) :
    1 - η ≤
      ((adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.matrix).trace).re := by
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hunion : (1 - Pi) ≤ (1 - PiA) + (1 - PiB) + (1 - PiR) := by
    simpa [Pi, PiA, PiB, PiR] using
      adhwFQSWIidLiftProjector_union_bound (a := a) (b := b) (r := r) n PA PB PR
        hPA hPB hPR hPAid hPBid hPRid
  have htrace_le :=
    cMatrix_trace_mul_le_of_le_posSemidef_left (W := ρ.matrix) ρ.pos hunion
  have hsum :
      ((ρ.matrix * ((1 - PiA) + (1 - PiB) + (1 - PiR))).trace).re =
        (1 - ((PiA * ρ.matrix).trace).re) +
          (1 - ((PiB * ρ.matrix).trace).re) +
            (1 - ((PiR * ρ.matrix).trace).re) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      Complex.add_re, Complex.add_re]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiA]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiB]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiR]
  have hrejection :
      ((ρ.matrix * (1 - Pi)).trace).re ≤ η := by
    calc
      ((ρ.matrix * (1 - Pi)).trace).re
          ≤ ((ρ.matrix * ((1 - PiA) + (1 - PiB) + (1 - PiR))).trace).re := htrace_le
      _ = (1 - ((PiA * ρ.matrix).trace).re) +
            (1 - ((PiB * ρ.matrix).trace).re) +
              (1 - ((PiR * ρ.matrix).trace).re) := hsum
      _ ≤ η := by linarith
  have hrej_eq := adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ Pi
  linarith

private theorem adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftB_sandwich_partialTraceR
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n)) :
    partialTraceB
        (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.matrix *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) =
      Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
          (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.matrix *
            adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) *
        Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  simp [adhwFQSWIidLiftProjectorA, partialTraceB, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (adhwFQSW_sum_five_comm
      (fun r0 aR bR aL bL =>
        PA xa aL *
          (PA aR ya *
            (PB xb bL *
              (PB bR yb * ρ.matrix ((aL, bL), r0) ((aR, bR), r0))))))

private theorem adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftA_sandwich_partialTraceR
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n)) :
    partialTraceB
        (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.matrix *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) =
      Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
          (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.matrix *
            adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) *
        Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  simp [adhwFQSWIidLiftProjectorB, partialTraceB, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (adhwFQSW_sum_five_comm_leftPair
      (fun r0 aR bR aL bL =>
        PA xa aL *
          (PA aR ya *
            (PB xb bL *
              (PB bR yb * ρ.matrix ((aL, bL), r0) ((aR, bR), r0))))))

private theorem adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.matrix *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR *
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.matrix *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) *
        adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
  let K : CMatrix (Prod (TensorPower a n) (TensorPower b n)) := Matrix.kronecker PA PB
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker K (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hleft : PiR * PiAB = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        K PR (1 : CMatrix (TensorPower r n))).symm
  have hright : PiAB * PiR = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul K (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        (1 : CMatrix (TensorPower r n)) PR).symm
  calc
    Pi * ρ.matrix * Pi = PiR * PiAB * ρ.matrix * (PiAB * PiR) := by
      rw [hleft, hright]
    _ = PiR * (PiAB * ρ.matrix * PiAB) * PiR := by
      noncomm_ring

private theorem adhwFQSW_triple_sandwich_eq_liftAB_select_liftR_sandwich
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.matrix *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
        (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.matrix *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) *
        Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) := by
  let K : CMatrix (Prod (TensorPower a n) (TensorPower b n)) := Matrix.kronecker PA PB
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker K (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hleft : PiAB * PiR = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul K (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        (1 : CMatrix (TensorPower r n)) PR).symm
  have hright : PiR * PiAB = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        K PR (1 : CMatrix (TensorPower r n))).symm
  calc
    Pi * ρ.matrix * Pi = PiAB * PiR * ρ.matrix * (PiR * PiAB) := by
      rw [hleft, hright]
    _ = PiAB * (PiR * ρ.matrix * PiR) * PiAB := by
      noncomm_ring

private theorem adhwFQSW_normalizedTripleSandwich_marginalA_le_envelope
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi
    0 < τM.trace.re →
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ'))) : ℝ) : ℂ)) • PA) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  let τAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiAB * ρ.matrix * PiAB
  let τA : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiA * ρ.matrix * PiA
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPiABpsd : PiAB.PosSemidef := by
    exact (hPApsd.kronecker hPBpsd).kronecker Matrix.PosSemidef.one
  have hτABpsd : τAB.PosSemidef := by
    simpa [τAB, PiAB] using projector_sandwich_posSemidef PiAB hPiABpsd ρ
  have hR :
      partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB := by
    have hsel :=
      adhwFQSW_partialTraceB_selective_projector_le
        (X := τAB) hτABpsd PR hPRpsd hPRid
    have hτeq :
        τM =
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * τAB *
            adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
      simpa [τM, τAB, Pi, PiAB, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τAB, hτeq, adhwFQSWIidLiftProjectorR] using hsel
  have hApsd : τA.PosSemidef := by
    have hPiApsd := adhwFQSWIidLiftProjectorA_posSemidef (b := b) (r := r) n PA hPApsd
    simpa [τA, PiA] using projector_sandwich_posSemidef PiA hPiApsd ρ
  have hB :
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) ≤
        partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA) := by
    have hτA_R_psd :
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA).PosSemidef :=
      partialTraceB_posSemidef (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n) hApsd
    have hsel :=
      adhwFQSW_partialTraceB_selective_projector_le
        (X := partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA)
        hτA_R_psd PB hPBpsd hPBid
    have heq :
        partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB =
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
            partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA *
            Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
      simpa [τAB, τA, PiAB, PiA] using
        adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftB_sandwich_partialTraceR
          (a := a) (b := b) (r := r) n ρ PA PB
    simpa [heq] using hsel
  have hcore₀ :
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
        PA * ρ.marginalA.marginalA.matrix * PA := by
    calc
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM)
          ≤ partialTraceB (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) :=
              adhwFQSW_partialTraceB_mono
                (α := TensorPower a n) (β := TensorPower b n) hR
      _ ≤ partialTraceB (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA) := hB
      _ = PA * ρ.marginalA.marginalA.matrix * PA := by
            simpa [τA, PiA] using
              adhwFQSWIidLiftProjectorA_marginalA_marginalA
                (a := a) (b := b) (r := r) n ρ PA
  have hmarg :
      ρ.marginalA.marginalA.matrix =
        ((adhwFQSWSystemAState ψ).tensorPower n).matrix := by
    simpa [ρ] using congrArg (fun σ : State (TensorPower a n) => σ.matrix)
      (adhwFQSWIidSourceState_marginalA_eq_tensorPower ψ n)
  have hcompress :
      PA * ρ.marginalA.marginalA.matrix * PA ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ')))) : ℝ) : ℂ) • PA) := by
    have htyp :=
      State.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemAState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyA ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemAState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyA]
      ring
    rw [hmarg]
    simpa [PA, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    adhwFQSW_smul_le_smul_of_nonneg
      (α := TensorPower a n)
      (A := partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n) τM))
      (B := (((d : ℝ) : ℂ) • PA))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          partialTraceB (a := TensorPower a n) (b := TensorPower b n)
            (partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n))
              (b := TensorPower r n) τM)) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PA)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            partialTraceB (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n))
                (b := TensorPower r n) τM)) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PA)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PA] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, partialTraceB_smul, Matrix.mul_assoc] using hscaled_prod

private theorem adhwFQSW_normalizedTripleSandwich_marginalB_le_envelope
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi
    0 < τM.trace.re →
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ'))) : ℝ) : ℂ)) • PB) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  let τAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiAB * ρ.matrix * PiAB
  let τB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiB * ρ.matrix * PiB
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPiABpsd : PiAB.PosSemidef := by
    exact (hPApsd.kronecker hPBpsd).kronecker Matrix.PosSemidef.one
  have hτABpsd : τAB.PosSemidef := by
    simpa [τAB, PiAB] using projector_sandwich_posSemidef PiAB hPiABpsd ρ
  have hR :
      partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB := by
    have hsel :=
      adhwFQSW_partialTraceB_selective_projector_le
        (X := τAB) hτABpsd PR hPRpsd hPRid
    have hτeq :
        τM =
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * τAB *
            adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
      simpa [τM, τAB, Pi, PiAB, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τAB, hτeq, adhwFQSWIidLiftProjectorR] using hsel
  have hBpsd : τB.PosSemidef := by
    have hPiBpsd := adhwFQSWIidLiftProjectorB_posSemidef (a := a) (r := r) n PB hPBpsd
    simpa [τB, PiB] using projector_sandwich_posSemidef PiB hPiBpsd ρ
  have hA :
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) ≤
        partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB) := by
    have hτB_R_psd :
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB).PosSemidef :=
      partialTraceB_posSemidef (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n) hBpsd
    have hsel :=
      adhwFQSW_partialTraceA_selective_projector_le
        (X := partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB)
        hτB_R_psd PA hPApsd hPAid
    have heq :
        partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB =
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
            partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB *
            Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
      simpa [τAB, τB, PiAB, PiB] using
        adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftA_sandwich_partialTraceR
          (a := a) (b := b) (r := r) n ρ PA PB
    simpa [heq] using hsel
  have hcore₀ :
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
        PB * ρ.marginalA.marginalB.matrix * PB := by
    calc
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM)
          ≤ partialTraceA (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) :=
              adhwFQSW_partialTraceA_mono
                (α := TensorPower a n) (β := TensorPower b n) hR
      _ ≤ partialTraceA (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB) := hA
      _ = PB * ρ.marginalA.marginalB.matrix * PB := by
            simpa [τB, PiB] using
              adhwFQSWIidLiftProjectorB_marginalA_marginalB
                (a := a) (b := b) (r := r) n ρ PB
  have hmarg :
      ρ.marginalA.marginalB.matrix =
        ((adhwFQSWSystemBState ψ).tensorPower n).matrix := by
    simpa [ρ] using congrArg (fun σ : State (TensorPower b n) => σ.matrix)
      (adhwFQSWIidSourceState_marginalB_eq_tensorPower ψ n)
  have hcompress :
      PB * ρ.marginalA.marginalB.matrix * PB ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ')))) : ℝ) : ℂ) • PB) := by
    have htyp :=
      State.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemBState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyB ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemBState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyB]
      ring
    rw [hmarg]
    simpa [PB, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    adhwFQSW_smul_le_smul_of_nonneg
      (α := TensorPower b n)
      (A := partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n) τM))
      (B := (((d : ℝ) : ℂ) • PB))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          partialTraceA (a := TensorPower a n) (b := TensorPower b n)
            (partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n))
              (b := TensorPower r n) τM)) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PB)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            partialTraceA (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n))
                (b := TensorPower r n) τM)) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PB)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PB] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, partialTraceA_smul, partialTraceB_smul,
    Matrix.mul_assoc] using hscaled_prod

private theorem adhwFQSW_normalizedTripleSandwich_marginalR_le_envelope
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi
    0 < τM.trace.re →
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ'))) : ℝ) : ℂ)) • PR) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  let τR : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiR * ρ.matrix * PiR
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, _hPRid, hPRle⟩
  have hQpsd : (Matrix.kronecker PA PB).PosSemidef := hPApsd.kronecker hPBpsd
  have hQid : Matrix.kronecker PA PB * Matrix.kronecker PA PB = Matrix.kronecker PA PB := by
    calc
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
          Matrix.kronecker (PA * PA) (PB * PB) := by
            exact (Matrix.mul_kronecker_mul PA PA PB PB).symm
      _ = Matrix.kronecker PA PB := by rw [hPAid, hPBid]
  have hRpsd : τR.PosSemidef := by
    have hPiRpsd := adhwFQSWIidLiftProjectorR_posSemidef (a := a) (b := b) n PR hPRpsd
    simpa [τR, PiR] using projector_sandwich_posSemidef PiR hPiRpsd ρ
  have hAB :
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τR := by
    have hsel :=
      adhwFQSW_partialTraceA_selective_projector_le
        (X := τR) hRpsd (Matrix.kronecker PA PB) hQpsd hQid
    have hτeq :
        τM = PiAB * τR * PiAB := by
      simpa [τM, τR, Pi, PiAB, PiR, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftAB_select_liftR_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τR, hτeq, PiAB] using hsel
  have hcore₀ :
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        PR * ρ.marginalB.matrix * PR := by
    calc
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM
          ≤ partialTraceA
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τR := hAB
      _ = PR * ρ.marginalB.matrix * PR := by
            simpa [τR, PiR] using
              adhwFQSWIidLiftProjectorR_marginalB
                (a := a) (b := b) (r := r) n ρ PR
  have hmarg :
      ρ.marginalB.matrix =
        ((adhwFQSWSystemRState ψ).tensorPower n).matrix := by
    simpa [ρ] using congrArg (fun σ : State (TensorPower r n) => σ.matrix)
      (adhwFQSWIidSourceState_marginalR_eq_tensorPower ψ n)
  have hcompress :
      PR * ρ.marginalB.matrix * PR ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ')))) : ℝ) : ℂ) • PR) := by
    have htyp :=
      State.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemRState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyR ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemRState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyR]
      ring
    rw [hmarg]
    simpa [PR, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    adhwFQSW_smul_le_smul_of_nonneg
      (α := TensorPower r n)
      (A := partialTraceA
        (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM)
      (B := (((d : ℝ) : ℂ) • PR))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          partialTraceA
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PR)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            partialTraceA
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PR)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PR] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, partialTraceA_smul, Matrix.mul_assoc] using
    hscaled_prod

/-- AEP high-weight form for one typical projector spectral weight. -/
private theorem adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
    (ρ : State a) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      1 - η ≤ ρ.typicalSubspaceSpectralWeight n δ := by
  have hlim := ρ.tendsto_typicalSubspaceSpectralWeight hδ
  have hball :
      ∀ᶠ n : ℕ in Filter.atTop,
        ρ.typicalSubspaceSpectralWeight n δ ∈ Metric.ball (1 : ℝ) η :=
    hlim.eventually (Metric.ball_mem_nhds _ hη)
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        1 - η ≤ ρ.typicalSubspaceSpectralWeight n δ := by
    filter_upwards [hball] with n hn
    rw [Metric.mem_ball, Real.dist_eq] at hn
    have hlt := abs_lt.mp hn
    linarith
  exact Filter.eventually_atTop.mp hev

/-- Small scalar split used to turn eventual high-weight estimates into an
ADHW-style final trace-error budget. -/
private def adhwFQSWTypicalEta (ε : ℝ) : ℝ :=
  min ((ε / 4) ^ 2) (min (ε / 4) (1 / 2))

private theorem adhwFQSWTypicalEta_pos {ε : ℝ} (hε : 0 < ε) :
    0 < adhwFQSWTypicalEta ε := by
  dsimp [adhwFQSWTypicalEta]
  positivity

private theorem adhwFQSWTypicalEta_error_split {ε : ℝ} (hε : 0 < ε) :
    2 * (Real.sqrt (adhwFQSWTypicalEta ε) + adhwFQSWTypicalEta ε) ≤ ε := by
  have hη_nonneg : 0 ≤ adhwFQSWTypicalEta ε := (adhwFQSWTypicalEta_pos hε).le
  have hη_sq : adhwFQSWTypicalEta ε ≤ (ε / 4) ^ 2 := by
    dsimp [adhwFQSWTypicalEta]
    exact min_le_left _ _
  have hη_quarter : adhwFQSWTypicalEta ε ≤ ε / 4 := by
    dsimp [adhwFQSWTypicalEta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hsqrt : Real.sqrt (adhwFQSWTypicalEta ε) ≤ ε / 4 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, hη_sq⟩
  linarith

private theorem adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
    {t η H δ δtyp : ℝ} (n : ℕ)
    (htrace : 1 - η ≤ t)
    (hη_le_half : η ≤ (1 / 2 : ℝ))
    (hδtyp : δtyp = δ / 2)
    (hn_absorb : 1 ≤ (n : ℝ) * δ / 2) :
    t⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (H - δ))) := by
  have ht_half : (1 / 2 : ℝ) ≤ t := by linarith
  have ht_pos : 0 < t := by linarith
  have hinv_le_two : t⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ ht_pos]
    nlinarith
  have hpow_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  calc
    t⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp)))
        ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) := by
          exact mul_le_mul_of_nonneg_right hinv_le_two hpow_nonneg
    _ = (2 : ℝ) ^ (1 + -((n : ℝ) * (H - δtyp))) := by
          nth_rw 1 [← Real.rpow_one (2 : ℝ)]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (H - δ))) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
          rw [hδtyp]
          nlinarith

private theorem adhwFQSW_real_smul_one_le_smul_one
    {α : Type u} [Fintype α] [DecidableEq α]
    {c d : ℝ} (hcd : c ≤ d) :
    (((c : ℝ) : ℂ) • (1 : CMatrix α)) ≤
      (((d : ℝ) : ℂ) • (1 : CMatrix α)) := by
  rw [Matrix.le_iff]
  have hdiff :
      (((d : ℝ) : ℂ) • (1 : CMatrix α) -
          ((c : ℝ) : ℂ) • (1 : CMatrix α)) =
        ((((d - c : ℝ) : ℂ)) • (1 : CMatrix α)) := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Complex.ofReal_sub, sub_mul]
  rw [hdiff]
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
    (by exact_mod_cast sub_nonneg.mpr hcd)

private theorem adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ : State α) {P : CMatrix α} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hP_le : P ≤ (1 : CMatrix α))
    (hcd : c ≤ d) (henv : ρ.matrix ≤ (((c : ℝ) : ℂ) • P)) :
    hilbertSchmidtSq ρ.matrix ≤ d := by
  have hPenv : (((c : ℝ) : ℂ) • P) ≤ (((c : ℝ) : ℂ) • (1 : CMatrix α)) :=
    adhwFQSW_smul_le_smul_of_nonneg hc hP_le
  have hdenv : (((c : ℝ) : ℂ) • (1 : CMatrix α)) ≤
      (((d : ℝ) : ℂ) • (1 : CMatrix α)) :=
    adhwFQSW_real_smul_one_le_smul_one hcd
  exact State.hilbertSchmidtSq_matrix_le_of_le_smul_one ρ hd
    (henv.trans (hPenv.trans hdenv))

private theorem adhwFQSW_traceDistance_le_of_normalizedTraceDistance_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ σ : State α) {η ε : ℝ}
    (hdist : ρ.normalizedTraceDistance σ ≤ Real.sqrt η + η)
    (hsplit : 2 * (Real.sqrt η + η) ≤ ε) :
    traceDistance ρ.matrix σ.matrix ≤ ε := by
  have hnorm : (1 / 2 : ℝ) * traceDistance ρ.matrix σ.matrix ≤
      Real.sqrt η + η := by
    simpa [State.normalizedTraceDistance, normalizedTraceDistance] using hdist
  have hnonneg : 0 ≤ traceDistance ρ.matrix σ.matrix :=
    traceDistance_nonneg ρ.matrix σ.matrix
  nlinarith

private theorem adhwFQSW_traceDistance_triangle_state
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ σ τ : State α) :
    traceDistance ρ.matrix τ.matrix ≤
      traceDistance ρ.matrix σ.matrix + traceDistance σ.matrix τ.matrix := by
  have htri := State.normalizedTraceDistance_triangle ρ σ τ
  have hscaled :
      (1 / 2 : ℝ) * traceDistance ρ.matrix τ.matrix ≤
        (1 / 2 : ℝ) * traceDistance ρ.matrix σ.matrix +
          (1 / 2 : ℝ) * traceDistance σ.matrix τ.matrix := by
    simpa [State.normalizedTraceDistance, normalizedTraceDistance,
      mul_add] using htri
  have hnonneg : 0 ≤ traceDistance ρ.matrix τ.matrix :=
    traceDistance_nonneg ρ.matrix τ.matrix
  nlinarith

namespace PureVector

variable (ψ : PureVector (Prod (Prod a b) r))

/-- FQSW communication rate `(1/2) I(A;R)_ψ`. -/
def fqswCommunicationRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.stateMergingReferenceState

/-- FQSW ebit-yield rate `(1/2) I(A;B)_ψ`. -/
def fqswEbitYieldRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.marginalA

/-- Public one-shot FQSW theorem-shape projection.  The source split
`A = A₁ × A₂`, together with the finite-dimensional side conditions needed by
the Uhlmann/Bob-isometry assembly, produces the protocol promised by
ADHW `thm:trueoneShotMother` (fqsw.tex lines 553-568).  Internally this is
assembled from the Schur twirl, Hilbert--Schmidt calculation, trace-norm
decoupling, max-mixed `A₂` estimate, Haar selection, and Uhlmann step in
fqsw.tex lines 580-841. -/
theorem exists_fqswOneShotProtocol_traceNormError_le
    [Nonempty q]
    (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨D⟩ :=
    exists_adhwFQSWTraceNormDecouplingBound_of_hilbertSchmidtAverage ψ split
      (adhwFQSWProductDecouplingHilbertSchmidtAverage_le ψ split)
  obtain ⟨M⟩ :=
    exists_adhwFQSWMaxMixedA2Estimate_of_hilbertSchmidtAverage ψ split
      (adhwFQSWMaxMixedA2HilbertSchmidtAverage_le ψ split)
  exact exists_fqswOneShotProtocol_traceNormError_le_of_source_component_records
    ψ split D M hcardTarget hcardRef

/-- Operational FQSW achievability with computed protocols: for every positive
rate slack and error tolerance, all sufficiently large block lengths have a
source-shaped protocol whose communication rate is at most
`1/2 I(A;R) + δ`, whose ebit yield is at least `1/2 I(A;B) - δ`, and whose
computed normalized trace-distance error is at most `ε`. -/
def IsAchievableFQSW : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ εerr : ℝ, 0 < εerr →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
          ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
            ∃ S : FQSWOperationalSurface ψ n q e,
              S.communicationRate ≤ ψ.fqswCommunicationRate + δ ∧
                ψ.fqswEbitYieldRate - δ ≤ S.ebitYieldRate ∧
                  S.normalizedError ≤ εerr

end PureVector

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
          (mutualInformation ψ.state.stateMergingReferenceState + 3 * δ)) /
          ((Fintype.card q : ℝ) ^ 2))
    (hcardA1 :
      (2 : ℝ) ^ ((n : ℝ) * (ψ.fqswCommunicationRate + 2 * δ)) ≤
        (Fintype.card q : ℝ)) :
    adhwFQSWOneShotErrorBound φ q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) := by
  let I : ℝ := mutualInformation ψ.state.stateMergingReferenceState
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
          (mutualInformation ψ.state.stateMergingReferenceState + 3 * δ)) /
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
          (mutualInformation ψ.state.stateMergingReferenceState + c * δ)) /
          ((Fintype.card q : ℝ) ^ 2))
    (hcardA1 :
      (2 : ℝ) ^ adhwFQSWIidCommunicationLogTarget ψ n δ ≤
        (Fintype.card q : ℝ)) :
    adhwFQSWOneShotErrorBound φ q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8)) := by
  let I : ℝ := mutualInformation ψ.state.stateMergingReferenceState
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

/-- Simultaneous ADHW i.i.d. typical projectors `Π_A`, `Π_B`, and `Π_R`,
with the no-witness spectral construction, source estimates, marginal purity
bounds, and item iii rank bounds from fqsw.tex lines 1110-1129.

The projectors use the internal typicality window `δ / 2`.  This is the
standard slack split needed by `State.eventually_two_pow_sub_le_typicalSubspaceDimension`:
the constructed projectors are typical at the smaller window while the public
ADHW rank and purity bounds are stated with the advertised `±δ` slack. -/
structure ADHWFQSWSimultaneousTypicalProjectors
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ) where
  typicalitySlack : ℝ
  typicalitySlack_eq : typicalitySlack = δ / 2
  typicalitySlack_pos : 0 < typicalitySlack
  typicalitySlack_lt_delta : typicalitySlack < δ
  projectorA : CMatrix (TensorPower a n)
  projectorB : CMatrix (TensorPower b n)
  projectorR : CMatrix (TensorPower r n)
  projectorA_eq :
    projectorA = (adhwFQSWSystemAState ψ).typicalSubspaceProjector n typicalitySlack
  projectorB_eq :
    projectorB = (adhwFQSWSystemBState ψ).typicalSubspaceProjector n typicalitySlack
  projectorR_eq :
    projectorR = (adhwFQSWSystemRState ψ).typicalSubspaceProjector n typicalitySlack
  projectorA_statement :
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement n typicalitySlack
  projectorB_statement :
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement n typicalitySlack
  projectorR_statement :
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement n typicalitySlack
  compressedSource :
    State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
  normalizedTypicalSource :
    State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
  normalizedTypicalSource_projected_trace_pos :
    0 < (adhwFQSWIidProjectedSourceMatrix
      (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR).trace.re
  normalizedTypicalSource_matrix_eq :
    normalizedTypicalSource.matrix =
      ((((adhwFQSWIidProjectedSourceMatrix
        (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR).trace.re)⁻¹ :
          ℝ) : ℂ) •
        adhwFQSWIidProjectedSourceMatrix
          (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR
  schumacher_traceNorm_le :
    traceDistance compressedSource.matrix (adhwFQSWIidSourceState ψ n).matrix ≤ ε
  schumacher_traceNorm_le_normalizedTypical :
    traceDistance compressedSource.matrix normalizedTypicalSource.matrix ≤ ε
  normalized_traceNorm_le :
    traceDistance normalizedTypicalSource.matrix (adhwFQSWIidSourceState ψ n).matrix ≤ ε
  purityA_le :
    hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalA.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
  purityB_le :
    hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
  purityR_le :
    hilbertSchmidtSq normalizedTypicalSource.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
  rankA_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ - δ)) ≤
      (adhwFQSWSystemAState ψ).typicalSubspaceDimension n typicalitySlack
  rankA_upper :
    (adhwFQSWSystemAState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δ))
  rankB_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δ)) ≤
      (adhwFQSWSystemBState ψ).typicalSubspaceDimension n typicalitySlack
  rankB_upper :
    (adhwFQSWSystemBState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ + δ))
  rankR_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ - δ)) ≤
      (adhwFQSWSystemRState ψ).typicalSubspaceDimension n typicalitySlack
  rankR_upper :
    (adhwFQSWSystemRState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δ))

/-- Upper rank bound after splitting the advertised ADHW slack `δ` into an
internal typicality window `δ / 2`. -/
private theorem adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
    (ρ : State a) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ρ.typicalSubspaceDimension n (δ / 2) ≤
      (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann + δ)) := by
  have hbase : (1 : ℝ) ≤ 2 := by norm_num
  have hdim := ρ.typicalSubspaceDimension_le_two_pow n (δ / 2)
  have hexp :
      (n : ℝ) * (ρ.vonNeumann + δ / 2) ≤
        (n : ℝ) * (ρ.vonNeumann + δ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  exact hdim.trans (Real.rpow_le_rpow_of_exponent_le hbase hexp)

/-- Construct the simultaneous typical-projector record from local spectral
typical projectors, with no external proof witnesses.

For every positive advertised slack `δ` and tolerance `ε`, all sufficiently
large `n` have the three internal-window projectors, the normalized source
estimates, the three marginal purity estimates, and the ADHW item iii rank
bounds. -/
theorem exists_adhwFQSWSimultaneousTypicalProjectors
    (ψ : PureVector (Prod (Prod a b) r)) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      Nonempty (ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε) := by
  have hhalf_pos : 0 < δ / 2 := by linarith
  have hhalf_lt : δ / 2 < δ := by linarith
  let η : ℝ := adhwFQSWTypicalEta (ε / 2)
  have hε_half_pos : 0 < ε / 2 := by positivity
  have hε_half_le : ε / 2 ≤ ε := by linarith
  have hη_pos : 0 < η := by
    simpa [η] using adhwFQSWTypicalEta_pos hε_half_pos
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hη_le_half : η ≤ (1 / 2 : ℝ) := by
    dsimp [η, adhwFQSWTypicalEta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hη_lt_one : η < 1 := by linarith
  have hη_third_pos : 0 < η / 3 := by linarith
  have hη_error := adhwFQSWTypicalEta_error_split hε_half_pos
  obtain ⟨NA, hNA⟩ :=
    (adhwFQSWSystemAState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NB, hNB⟩ :=
    (adhwFQSWSystemBState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NR, hNR⟩ :=
    (adhwFQSWSystemRState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NwA, hW_A⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemAState ψ) hhalf_pos hη_third_pos
  obtain ⟨NwB, hW_B⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemBState ψ) hhalf_pos hη_third_pos
  obtain ⟨NwR, hW_R⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemRState ψ) hhalf_pos hη_third_pos
  let Nabs : ℕ := Nat.ceil (2 / δ)
  let N : ℕ := max NA (max NB (max NR (max NwA (max NwB (max NwR Nabs)))))
  refine ⟨N, ?_⟩
  intro n hn
  have hnA : n ≥ NA := by dsimp [N] at hn; omega
  have hnB : n ≥ NB := by dsimp [N] at hn; omega
  have hnR : n ≥ NR := by dsimp [N] at hn; omega
  have hnWA : n ≥ NwA := by dsimp [N] at hn; omega
  have hnWB : n ≥ NwB := by dsimp [N] at hn; omega
  have hnWR : n ≥ NwR := by dsimp [N] at hn; omega
  have hnAbs : n ≥ Nabs := by dsimp [N] at hn; omega
  have hn_absorb : 1 ≤ (n : ℝ) * δ / 2 := by
    have hceil : 2 / δ ≤ (Nabs : ℝ) := by
      simpa [Nabs] using Nat.le_ceil (2 / δ)
    have hnAbs_real : (Nabs : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnAbs
    have htwo_div_le : 2 / δ ≤ (n : ℝ) := hceil.trans hnAbs_real
    have hmul := mul_le_mul_of_nonneg_right htwo_div_le hδ.le
    have hdiv_mul : (2 / δ) * δ = (2 : ℝ) := by field_simp [hδ.ne']
    nlinarith
  let δtyp : ℝ := δ / 2
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δtyp
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δtyp
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δtyp
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let τA : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiA * ρ.matrix * PiA
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  have hPAstmt :
      (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPBstmt :
      (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPRstmt :
      (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPAstmt_parts := hPAstmt
  have hPBstmt_parts := hPBstmt
  have hPRstmt_parts := hPRstmt
  rcases hPAstmt_parts with ⟨hPApsd, _hPAherm, hPAid, hPAle⟩
  rcases hPBstmt_parts with ⟨hPBpsd, _hPBherm, hPBid, hPBle⟩
  rcases hPRstmt_parts with ⟨hPRpsd, _hPRherm, hPRid, hPRle⟩
  have hPiApsd : PiA.PosSemidef := by
    simpa [PiA, PA] using
      adhwFQSWIidLiftProjectorA_posSemidef (b := b) (r := r) n PA hPApsd
  have hPiAid : PiA * PiA = PiA := by
    simpa [PiA, PA] using
      adhwFQSWIidLiftProjectorA_idempotent (b := b) (r := r) n PA hPAid
  have hPipsd : Pi.PosSemidef := by
    simpa [Pi, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_posSemidef (a := a) (b := b) (r := r)
        n PA PB PR hPApsd hPBpsd hPRpsd
  have hPiid : Pi * Pi = Pi := by
    simpa [Pi, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_idempotent (a := a) (b := b) (r := r)
        n PA PB PR hPAid hPBid hPRid
  have hτApsd : τA.PosSemidef := by
    simpa [τA] using projector_sandwich_posSemidef PiA hPiApsd ρ
  have hτMpsd : τM.PosSemidef := by
    simpa [τM] using projector_sandwich_posSemidef Pi hPipsd ρ
  have haccA3 :
      1 - η / 3 ≤ ((PiA * ρ.matrix).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_A n hnWA
      _ = ((PiA * ρ.matrix).trace).re := by
            simpa [PiA, PA, ρ, δtyp] using
              (adhwFQSWIid_acceptanceA (a := a) (b := b) (r := r) ψ n δtyp).symm
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  have haccB3 :
      1 - η / 3 ≤ ((PiB * ρ.matrix).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_B n hnWB
      _ = ((PiB * ρ.matrix).trace).re := by
            simpa [PiB, PB, ρ, δtyp] using
              (adhwFQSWIid_acceptanceB (a := a) (b := b) (r := r) ψ n δtyp).symm
  have haccR3 :
      1 - η / 3 ≤ ((PiR * ρ.matrix).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_R n hnWR
      _ = ((PiR * ρ.matrix).trace).re := by
            simpa [PiR, PR, ρ, δtyp] using
              (adhwFQSWIid_acceptanceR (a := a) (b := b) (r := r) ψ n δtyp).symm
  have haccA : 1 - η ≤ ((PiA * ρ.matrix).trace).re := by
    linarith
  have haccTriple : 1 - η ≤ ((Pi * ρ.matrix).trace).re := by
    simpa [Pi, PiA, PiB, PiR, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_acceptance_of_single
        (a := a) (b := b) (r := r) n ρ η PA PB PR
        hPApsd hPBpsd hPRpsd hPAid hPBid hPRid haccA3 haccB3 haccR3
  have htrA : τA.trace.re ≠ 0 := by
    simpa [τA] using
      projector_sandwich_trace_re_ne_zero_of_acceptance PiA hPiAid ρ hη_lt_one haccA
  have htrM : τM.trace.re ≠ 0 := by
    simpa [τM] using
      projector_sandwich_trace_re_ne_zero_of_acceptance Pi hPiid ρ hη_lt_one haccTriple
  have htraceM_lower : 1 - η ≤ τM.trace.re := by
    calc
      1 - η ≤ ((Pi * ρ.matrix).trace).re := haccTriple
      _ = τM.trace.re := by
            simpa [τM] using
              (projector_sandwich_trace_re_eq_acceptance Pi hPiid ρ).symm
  have htraceM_pos : 0 < τM.trace.re :=
    lt_of_lt_of_le (by linarith : 0 < 1 - η) htraceM_lower
  let compressedSource :
      State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    State.normalizePSD τA hτApsd htrA
  let normalizedTypicalSource :
      State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    State.normalizePSD τM hτMpsd htrM
  have hdistCompressed_norm :
      compressedSource.normalizedTraceDistance ρ ≤ Real.sqrt η + η := by
    simpa [compressedSource, τA, State.normalizedTraceDistance, normalizedTraceDistance,
      State.normalizePSD_matrix] using
      normalizedTraceDistance_normalize_projector_sandwich_le
        (P := PiA) hPiApsd hPiAid ρ hη_nonneg hη_lt_one haccA
  have hdistNormalized_norm :
      normalizedTypicalSource.normalizedTraceDistance ρ ≤ Real.sqrt η + η := by
    simpa [normalizedTypicalSource, τM, State.normalizedTraceDistance, normalizedTraceDistance,
      State.normalizePSD_matrix] using
      normalizedTraceDistance_normalize_projector_sandwich_le
        (P := Pi) hPipsd hPiid ρ hη_nonneg hη_lt_one haccTriple
  have hdistCompressed_half :
      traceDistance compressedSource.matrix ρ.matrix ≤ ε / 2 :=
    adhwFQSW_traceDistance_le_of_normalizedTraceDistance_le
      compressedSource ρ hdistCompressed_norm (by simpa [η] using hη_error)
  have hdistNormalized_half :
      traceDistance normalizedTypicalSource.matrix ρ.matrix ≤ ε / 2 :=
    adhwFQSW_traceDistance_le_of_normalizedTraceDistance_le
      normalizedTypicalSource ρ hdistNormalized_norm (by simpa [η] using hη_error)
  have hdistCompressed :
      traceDistance compressedSource.matrix ρ.matrix ≤ ε :=
    hdistCompressed_half.trans hε_half_le
  have hdistNormalized :
      traceDistance normalizedTypicalSource.matrix ρ.matrix ≤ ε :=
    hdistNormalized_half.trans hε_half_le
  have hdistCompressedNormalized :
      traceDistance compressedSource.matrix normalizedTypicalSource.matrix ≤ ε := by
    have hdistNormalized_half_comm :
        traceDistance ρ.matrix normalizedTypicalSource.matrix ≤ ε / 2 := by
      rw [traceDistance_comm]
      exact hdistNormalized_half
    calc
      traceDistance compressedSource.matrix normalizedTypicalSource.matrix
          ≤ traceDistance compressedSource.matrix ρ.matrix +
              traceDistance ρ.matrix normalizedTypicalSource.matrix :=
            adhwFQSW_traceDistance_triangle_state compressedSource ρ normalizedTypicalSource
      _ ≤ ε / 2 + ε / 2 := by
            exact add_le_add hdistCompressed_half hdistNormalized_half_comm
      _ = ε := by ring
  let cA : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δtyp)))
  let cB : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp)))
  let cR : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp)))
  have hcA_nonneg : 0 ≤ cA := by
    dsimp [cA]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hcB_nonneg : 0 ≤ cB := by
    dsimp [cB]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hcR_nonneg : 0 ≤ cR := by
    dsimp [cR]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have htargetA_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetB_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetR_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hcA_le :
      cA ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyA ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have hcB_le :
      cB ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyB ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have hcR_le :
      cR ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyR ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have henvA :
      normalizedTypicalSource.marginalA.marginalA.matrix ≤ (((cA : ℝ) : ℂ) • PA) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_marginalA_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    change
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤ (((cA : ℝ) : ℂ) • PA)
    rw [partialTraceB_smul, partialTraceB_smul]
    have henv' := henv
    rw [partialTraceB_smul, partialTraceB_smul] at henv'
    simpa only [τM, Pi, ρ, PA, PB, PR, cA, Matrix.mul_assoc, Complex.ofReal_mul] using henv'
  have henvB :
      normalizedTypicalSource.marginalA.marginalB.matrix ≤ (((cB : ℝ) : ℂ) • PB) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_marginalB_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    change
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤ (((cB : ℝ) : ℂ) • PB)
    rw [partialTraceB_smul, partialTraceA_smul]
    have henv' := henv
    rw [partialTraceB_smul, partialTraceA_smul] at henv'
    simpa only [τM, Pi, ρ, PA, PB, PR, cB, Matrix.mul_assoc, Complex.ofReal_mul] using henv'
  have henvR :
      normalizedTypicalSource.marginalB.matrix ≤ (((cR : ℝ) : ℂ) • PR) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_marginalR_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    change
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM) ≤
        (((((τM.trace.re)⁻¹ *
            (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp)))) : ℝ) : ℂ) • PR)
    rw [Complex.ofReal_mul]
    simpa only [τM, Pi, ρ, PA, PB, PR, Matrix.mul_assoc] using henv
  have hpurityA :
      hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalA.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cA)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))))
      normalizedTypicalSource.marginalA.marginalA
      hcA_nonneg htargetA_nonneg hPAle hcA_le henvA
  have hpurityB :
      hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalB.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cB)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))))
      normalizedTypicalSource.marginalA.marginalB
      hcB_nonneg htargetB_nonneg hPBle hcB_le henvB
  have hpurityR :
      hilbertSchmidtSq normalizedTypicalSource.marginalB.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cR)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))))
      normalizedTypicalSource.marginalB
      hcR_nonneg htargetR_nonneg hPRle hcR_le henvR
  exact
    ⟨{ typicalitySlack := δtyp
       typicalitySlack_eq := rfl
       typicalitySlack_pos := hhalf_pos
       typicalitySlack_lt_delta := hhalf_lt
       projectorA := PA
       projectorB := PB
       projectorR := PR
       projectorA_eq := rfl
       projectorB_eq := rfl
       projectorR_eq := rfl
       projectorA_statement := hPAstmt
       projectorB_statement := hPBstmt
       projectorR_statement := hPRstmt
       compressedSource := compressedSource
       normalizedTypicalSource := normalizedTypicalSource
       normalizedTypicalSource_projected_trace_pos := by
        change 0 < τM.trace.re
        exact htraceM_pos
       normalizedTypicalSource_matrix_eq := by
        change normalizedTypicalSource.matrix =
          (((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM
        exact State.normalizePSD_matrix τM hτMpsd htrM
       schumacher_traceNorm_le := by
        simpa [ρ] using hdistCompressed
       schumacher_traceNorm_le_normalizedTypical := by
        simpa using hdistCompressedNormalized
       normalized_traceNorm_le := by
        simpa [ρ] using hdistNormalized
       purityA_le := hpurityA
       purityB_le := hpurityB
       purityR_le := hpurityR
       rankA_lower := by
        simpa [δtyp, adhwFQSWEntropyA] using hNA n hnA
       rankA_upper := by
        simpa [δtyp, adhwFQSWEntropyA] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemAState ψ) n hδ
       rankB_lower := by
        simpa [δtyp, adhwFQSWEntropyB] using hNB n hnB
       rankB_upper := by
        simpa [δtyp, adhwFQSWEntropyB] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemBState ψ) n hδ
       rankR_lower := by
        simpa [δtyp, adhwFQSWEntropyR] using hNR n hnR
       rankR_upper := by
        simpa [δtyp, adhwFQSWEntropyR] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemRState ψ) n hδ }⟩

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
private theorem le_two_rpow_of_log2_le {x t : ℝ}
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
        0 ≤ mutualInformation ψ.state.stateMergingReferenceState :=
      State.mutualInformation_nonneg ψ.state.stateMergingReferenceState
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
        0 ≤ mutualInformation ψ.state.stateMergingReferenceState :=
      State.mutualInformation_nonneg ψ.state.stateMergingReferenceState
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

/-- Lift the compressed one-shot coordinates
`(A₁ × A₂) × B^typ × R^typ` into the full i.i.d. source coordinates
`A^n × B^n × R^n` using Alice's padded support lift and the Bob/reference
typical support inclusions. -/
def adhwFQSWIidCompressedSourceLiftMatrix
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    Matrix
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod (Prod (Prod q e) btyp) rtyp) ℂ :=
  Matrix.kronecker (Matrix.kronecker P.supportLiftMatrix B.supportIsometry.matrix)
    R.supportIsometry.matrix

/-- Lift the true simultaneous typical coordinates
`A^typ × B^typ × R^typ` into the full i.i.d. source coordinates
`A^n × B^n × R^n`. -/
def adhwFQSWIidTypicalSourceLiftMatrix
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    Matrix
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod (Prod atyp btyp) rtyp) ℂ :=
  Matrix.kronecker
    (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)
    R.supportIsometry.matrix

/-- The compressed source lift has range equal to the simultaneous
`A^nB^nR^n` typical projector. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_mul_conjTranspose
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    L * Matrix.conjTranspose L =
      adhwFQSWIidLiftProjectorTriple
        (a := a) (b := b) (r := r) n
        T.projectorA T.projectorB T.projectorR := by
  dsimp
  let LA : Matrix (TensorPower a n) (Prod q e) ℂ := P.supportLiftMatrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      LA * Matrix.conjTranspose LA =
        (adhwFQSWSystemAState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LA] using
      ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_mul_conjTranspose P
  have hB :
      LB * Matrix.conjTranspose LB =
        (adhwFQSWSystemBState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LB] using B.supportIsometry_range_projector_eq
  have hR :
      LR * Matrix.conjTranspose LR =
        (adhwFQSWSystemRState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LR] using R.supportIsometry_range_projector_eq
  have hct_outer :
      Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
        Matrix.kronecker
          (Matrix.conjTranspose (Matrix.kronecker LA LB))
          (Matrix.conjTranspose LR) := by
    simpa [Matrix.kronecker] using
      Matrix.conjTranspose_kronecker (Matrix.kronecker LA LB) LR
  have hct_inner :
      Matrix.conjTranspose (Matrix.kronecker LA LB) =
        Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker LA LB
  have hinner_mul :
      Matrix.kronecker LA LB *
          Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) =
        Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB) := by
    simpa using
      (Matrix.mul_kronecker_mul
        LA (Matrix.conjTranspose LA) LB (Matrix.conjTranspose LB)).symm
  calc
    Matrix.kronecker (Matrix.kronecker LA LB) LR *
        Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
      Matrix.kronecker
        (Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB))
        (LR * Matrix.conjTranspose LR) := by
        rw [hct_outer, hct_inner]
        calc
          Matrix.kronecker (Matrix.kronecker LA LB) LR *
              Matrix.kronecker
                (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                (Matrix.conjTranspose LR) =
            Matrix.kronecker
              (Matrix.kronecker LA LB *
                Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact
                (Matrix.mul_kronecker_mul
                  (Matrix.kronecker LA LB)
                  (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                  LR (Matrix.conjTranspose LR)).symm
          _ =
            Matrix.kronecker
              (Matrix.kronecker (LA * Matrix.conjTranspose LA)
                (LB * Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact congrArg
                (fun X => Matrix.kronecker X (LR * Matrix.conjTranspose LR))
                hinner_mul
    _ = Matrix.kronecker (Matrix.kronecker T.projectorA T.projectorB) T.projectorR := by
        rw [hA, hB, hR, ← T.projectorA_eq, ← T.projectorB_eq, ← T.projectorR_eq]

/-- The true typical-source lift has range equal to the simultaneous
`A^nB^nR^n` typical projector. -/
theorem adhwFQSWIidTypicalSourceLiftMatrix_mul_conjTranspose
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L0 := adhwFQSWIidTypicalSourceLiftMatrix P B R
    L0 * Matrix.conjTranspose L0 =
      adhwFQSWIidLiftProjectorTriple
        (a := a) (b := b) (r := r) n
        T.projectorA T.projectorB T.projectorR := by
  dsimp
  let LA : Matrix (TensorPower a n) atyp ℂ := P.supportIsometry.matrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      LA * Matrix.conjTranspose LA =
        (adhwFQSWSystemAState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LA] using P.supportIsometry_range_projector_eq
  have hB :
      LB * Matrix.conjTranspose LB =
        (adhwFQSWSystemBState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LB] using B.supportIsometry_range_projector_eq
  have hR :
      LR * Matrix.conjTranspose LR =
        (adhwFQSWSystemRState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LR] using R.supportIsometry_range_projector_eq
  have hct_outer :
      Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
        Matrix.kronecker
          (Matrix.conjTranspose (Matrix.kronecker LA LB))
          (Matrix.conjTranspose LR) := by
    simpa [Matrix.kronecker] using
      Matrix.conjTranspose_kronecker (Matrix.kronecker LA LB) LR
  have hct_inner :
      Matrix.conjTranspose (Matrix.kronecker LA LB) =
        Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker LA LB
  have hinner_mul :
      Matrix.kronecker LA LB *
          Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) =
        Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB) := by
    simpa using
      (Matrix.mul_kronecker_mul
        LA (Matrix.conjTranspose LA) LB (Matrix.conjTranspose LB)).symm
  calc
    Matrix.kronecker (Matrix.kronecker LA LB) LR *
        Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
      Matrix.kronecker
        (Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB))
        (LR * Matrix.conjTranspose LR) := by
        rw [hct_outer, hct_inner]
        calc
          Matrix.kronecker (Matrix.kronecker LA LB) LR *
              Matrix.kronecker
                (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                (Matrix.conjTranspose LR) =
            Matrix.kronecker
              (Matrix.kronecker LA LB *
                Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact
                (Matrix.mul_kronecker_mul
                  (Matrix.kronecker LA LB)
                  (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                  LR (Matrix.conjTranspose LR)).symm
          _ =
            Matrix.kronecker
              (Matrix.kronecker (LA * Matrix.conjTranspose LA)
                (LB * Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact congrArg
                (fun X => Matrix.kronecker X (LR * Matrix.conjTranspose LR))
                hinner_mul
    _ = Matrix.kronecker (Matrix.kronecker T.projectorA T.projectorB) T.projectorR := by
        rw [hA, hB, hR, ← T.projectorA_eq, ← T.projectorB_eq, ← T.projectorR_eq]

/-- The compressed source lift's initial projection is exactly the padded
Alice typical-support projection, tensor the full Bob and reference typical
registers. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_conjTranspose_mul
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    Matrix.conjTranspose L * L =
      Matrix.kronecker
        (Matrix.kronecker
          (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix)
          (1 : CMatrix btyp))
        (1 : CMatrix rtyp) := by
  dsimp
  let LA : Matrix (TensorPower a n) (Prod q e) ℂ := P.supportLiftMatrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      Matrix.conjTranspose LA * LA =
        P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix := by
    simpa [LA] using
      ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_conjTranspose_mul P
  have hB : Matrix.conjTranspose LB * LB = (1 : CMatrix btyp) := by
    simpa [LB] using B.supportIsometry.isometry
  have hR : Matrix.conjTranspose LR * LR = (1 : CMatrix rtyp) := by
    simpa [LR] using R.supportIsometry.isometry
  have hct_outer :
      Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
        Matrix.kronecker
          (Matrix.conjTranspose (Matrix.kronecker LA LB))
          (Matrix.conjTranspose LR) := by
    simpa [Matrix.kronecker] using
      Matrix.conjTranspose_kronecker (Matrix.kronecker LA LB) LR
  have hct_inner :
      Matrix.conjTranspose (Matrix.kronecker LA LB) =
        Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker LA LB
  have hinner_mul :
      Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) *
          Matrix.kronecker LA LB =
        Matrix.kronecker (Matrix.conjTranspose LA * LA)
          (Matrix.conjTranspose LB * LB) := by
    simpa using
      (Matrix.mul_kronecker_mul
        (Matrix.conjTranspose LA) LA (Matrix.conjTranspose LB) LB).symm
  calc
    Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) *
        Matrix.kronecker (Matrix.kronecker LA LB) LR =
      Matrix.kronecker
        (Matrix.kronecker (Matrix.conjTranspose LA * LA)
          (Matrix.conjTranspose LB * LB))
        (Matrix.conjTranspose LR * LR) := by
        rw [hct_outer, hct_inner]
        calc
          Matrix.kronecker
              (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
              (Matrix.conjTranspose LR) *
              Matrix.kronecker (Matrix.kronecker LA LB) LR =
            Matrix.kronecker
              (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) *
                Matrix.kronecker LA LB)
              (Matrix.conjTranspose LR * LR) := by
              exact
                (Matrix.mul_kronecker_mul
                  (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                  (Matrix.kronecker LA LB)
                  (Matrix.conjTranspose LR) LR).symm
          _ =
            Matrix.kronecker
              (Matrix.kronecker (Matrix.conjTranspose LA * LA)
                (Matrix.conjTranspose LB * LB))
              (Matrix.conjTranspose LR * LR) := by
              exact congrArg
                (fun X => Matrix.kronecker X (Matrix.conjTranspose LR * LR))
                hinner_mul
    _ =
      Matrix.kronecker
        (Matrix.kronecker
          (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix)
          (1 : CMatrix btyp))
        (1 : CMatrix rtyp) := by
        rw [hA, hB, hR]

/-- The compressed source lift is supported on its initial projection. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_mul_initialProjection
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    let Q := Matrix.kronecker
      (Matrix.kronecker
        (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix)
        (1 : CMatrix btyp))
      (1 : CMatrix rtyp)
    L * Q = L := by
  intro L Q
  let LA : Matrix (TensorPower a n) (Prod q e) ℂ := P.supportLiftMatrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      LA * (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix) = LA := by
    simpa [LA] using
      ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_mul_initialProjection P
  calc
    L * Q =
        Matrix.kronecker
          (Matrix.kronecker
            (LA * (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix))
            (LB * (1 : CMatrix btyp)))
          (LR * (1 : CMatrix rtyp)) := by
          dsimp [L, Q, adhwFQSWIidCompressedSourceLiftMatrix, LA, LB, LR]
          rw [← Matrix.mul_kronecker_mul]
          rw [← Matrix.mul_kronecker_mul]
    _ = L := by
          simp [hA, L, adhwFQSWIidCompressedSourceLiftMatrix, LA, LB, LR]

/-- The padded compressed lift factors through the true typical-source lift
followed by the adjoint of Alice's padded `A^typ ↪ A₁ × A₂` embedding. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_eq_typicalSourceLiftMatrix_mul_paddingAdjoint
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    let L0 := adhwFQSWIidTypicalSourceLiftMatrix P B R
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let K := Matrix.kronecker padAB.matrix (1 : CMatrix rtyp)
    L = L0 * Matrix.conjTranspose K := by
  intro L L0 padAB K
  have hpad :
      padAB.matrix =
        Matrix.kronecker P.isometry.matrix (1 : CMatrix btyp) := by
    ext i j
    simp [padAB, ReferenceIsometry.prod, ReferenceIsometry.ofEquiv,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  have hpad_ct :
      Matrix.conjTranspose padAB.matrix =
        Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
          (1 : CMatrix btyp) := by
    rw [hpad]
    simpa [Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker P.isometry.matrix (1 : CMatrix btyp)
  have hKct :
      Matrix.conjTranspose K =
        Matrix.kronecker
          (Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
            (1 : CMatrix btyp))
          (1 : CMatrix rtyp) := by
    dsimp [K]
    rw [Matrix.conjTranspose_kronecker, hpad_ct]
    simp [Matrix.conjTranspose_one]
  symm
  calc
    L0 * Matrix.conjTranspose K =
        Matrix.kronecker
          (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix *
            Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
              (1 : CMatrix btyp))
          (R.supportIsometry.matrix * (1 : CMatrix rtyp)) := by
          dsimp [L0, adhwFQSWIidTypicalSourceLiftMatrix]
          rw [hKct]
          exact
            (Matrix.mul_kronecker_mul
              (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)
              (Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
                (1 : CMatrix btyp))
              R.supportIsometry.matrix (1 : CMatrix rtyp)).symm
    _ =
        Matrix.kronecker
          (Matrix.kronecker
            (P.supportIsometry.matrix * Matrix.conjTranspose P.isometry.matrix)
            (B.supportIsometry.matrix * (1 : CMatrix btyp)))
          (R.supportIsometry.matrix * (1 : CMatrix rtyp)) := by
          exact congrArg
            (fun X => Matrix.kronecker X
              (R.supportIsometry.matrix * (1 : CMatrix rtyp)))
            (Matrix.mul_kronecker_mul
              P.supportIsometry.matrix (Matrix.conjTranspose P.isometry.matrix)
              B.supportIsometry.matrix (1 : CMatrix btyp)).symm
    _ = L := by
          simp [L, adhwFQSWIidCompressedSourceLiftMatrix,
            ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix]

/-- Padding the true simultaneous-typical source preserves Alice's source
purity, and the typical lift identifies that purity with the normalized
simultaneous-typical source's `A` purity. -/
theorem adhwFQSWIidPaddedTypicalSource_a_purity_le
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp)
    (source0 : PureVector (Prod (Prod atyp btyp) rtyp))
    (hsource0_lift :
      (adhwFQSWIidTypicalSourceLiftMatrix P B R) *
          source0.state.matrix *
          Matrix.conjTranspose (adhwFQSWIidTypicalSourceLiftMatrix P B R) =
        T.normalizedTypicalSource.matrix) :
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.applyPureVector source0
    adhwFQSWAPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) := by
  intro padAB source
  let idB : ReferenceIsometry btyp btyp :=
    ReferenceIsometry.ofEquiv (Equiv.refl btyp)
  let ABtyp : ReferenceIsometry (Prod atyp btyp)
      (Prod (TensorPower a n) (TensorPower b n)) :=
    P.supportIsometry.prod B.supportIsometry
  have hT_AB :
      T.normalizedTypicalSource.marginalA.matrix =
        ABtyp.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose ABtyp.matrix := by
    rw [State.marginalA_matrix, ← hsource0_lift]
    change partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix *
          source0.state.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix)) =
      ABtyp.matrix * source0.state.marginalA.matrix *
        Matrix.conjTranspose ABtyp.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hT_A :
      T.normalizedTypicalSource.marginalA.marginalA.matrix =
        P.supportIsometry.matrix * source0.state.marginalA.marginalA.matrix *
          Matrix.conjTranspose P.supportIsometry.matrix := by
    rw [State.marginalA_matrix, hT_AB]
    change partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)) =
      P.supportIsometry.matrix * source0.state.marginalA.marginalA.matrix *
        Matrix.conjTranspose P.supportIsometry.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hsource_AB :
      source.state.marginalA.matrix =
        padAB.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose padAB.matrix := by
    simpa [source] using referenceIsometry_marginalA_applyPureVector padAB source0
  have hsource_A :
      source.state.marginalA.marginalA.matrix =
        P.isometry.matrix * source0.state.marginalA.marginalA.matrix *
          Matrix.conjTranspose P.isometry.matrix := by
    rw [State.marginalA_matrix, hsource_AB]
    change partialTraceB (a := Prod q e) (b := btyp)
        (Matrix.kronecker P.isometry.matrix idB.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose (Matrix.kronecker P.isometry.matrix idB.matrix)) =
      P.isometry.matrix * source0.state.marginalA.marginalA.matrix *
        Matrix.conjTranspose P.isometry.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hsource_hs :
      hilbertSchmidtSq source.state.marginalA.marginalA.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalA.matrix := by
    rw [hsource_A]
    exact referenceIsometry_hilbertSchmidtSq_conj
      P.isometry source0.state.marginalA.marginalA
  have hT_hs :
      hilbertSchmidtSq T.normalizedTypicalSource.marginalA.marginalA.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalA.matrix := by
    rw [hT_A]
    exact referenceIsometry_hilbertSchmidtSq_conj
      P.supportIsometry source0.state.marginalA.marginalA
  rw [adhwFQSWAPurity, adhwFQSWARState_marginalA_eq_systemA,
    adhwFQSWSystemAState]
  rw [hsource_hs, ← hT_hs]
  exact T.purityA_le

/-- Padding the true simultaneous-typical source preserves Bob's source
purity, and the typical lift identifies that purity with the normalized
simultaneous-typical source's `B` purity. -/
theorem adhwFQSWIidPaddedTypicalSource_b_purity_le
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp)
    (source0 : PureVector (Prod (Prod atyp btyp) rtyp))
    (hsource0_lift :
      (adhwFQSWIidTypicalSourceLiftMatrix P B R) *
          source0.state.matrix *
          Matrix.conjTranspose (adhwFQSWIidTypicalSourceLiftMatrix P B R) =
        T.normalizedTypicalSource.matrix) :
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.applyPureVector source0
    hilbertSchmidtSq source.state.marginalA.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
  intro padAB source
  let idB : ReferenceIsometry btyp btyp :=
    ReferenceIsometry.ofEquiv (Equiv.refl btyp)
  let ABtyp : ReferenceIsometry (Prod atyp btyp)
      (Prod (TensorPower a n) (TensorPower b n)) :=
    P.supportIsometry.prod B.supportIsometry
  have hT_AB :
      T.normalizedTypicalSource.marginalA.matrix =
        ABtyp.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose ABtyp.matrix := by
    rw [State.marginalA_matrix, ← hsource0_lift]
    change partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix *
          source0.state.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix)) =
      ABtyp.matrix * source0.state.marginalA.matrix *
        Matrix.conjTranspose ABtyp.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hT_B :
      T.normalizedTypicalSource.marginalA.marginalB.matrix =
        B.supportIsometry.matrix * source0.state.marginalA.marginalB.matrix *
          Matrix.conjTranspose B.supportIsometry.matrix := by
    rw [State.marginalB_matrix, hT_AB]
    change partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)) =
      B.supportIsometry.matrix * source0.state.marginalA.marginalB.matrix *
        Matrix.conjTranspose B.supportIsometry.matrix
    rw [referenceIsometry_prod_partialTraceA_conj]
    rfl
  have hsource_AB :
      source.state.marginalA.matrix =
        padAB.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose padAB.matrix := by
    simpa [source] using referenceIsometry_marginalA_applyPureVector padAB source0
  have hsource_B :
      source.state.marginalA.marginalB.matrix =
        idB.matrix * source0.state.marginalA.marginalB.matrix *
          Matrix.conjTranspose idB.matrix := by
    rw [State.marginalB_matrix, hsource_AB]
    change partialTraceA (a := Prod q e) (b := btyp)
        (Matrix.kronecker P.isometry.matrix idB.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose (Matrix.kronecker P.isometry.matrix idB.matrix)) =
      idB.matrix * source0.state.marginalA.marginalB.matrix *
        Matrix.conjTranspose idB.matrix
    rw [referenceIsometry_prod_partialTraceA_conj]
    rfl
  have hsource_hs :
      hilbertSchmidtSq source.state.marginalA.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalB.matrix := by
    rw [hsource_B]
    exact referenceIsometry_hilbertSchmidtSq_conj
      idB source0.state.marginalA.marginalB
  have hT_hs :
      hilbertSchmidtSq T.normalizedTypicalSource.marginalA.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalB.matrix := by
    rw [hT_B]
    exact referenceIsometry_hilbertSchmidtSq_conj
      B.supportIsometry source0.state.marginalA.marginalB
  rw [hsource_hs, ← hT_hs]
  exact T.purityB_le

/-- Padding the true simultaneous-typical source preserves the reference
purity, and the typical lift identifies that purity with the normalized
simultaneous-typical source's `R` purity. -/
theorem adhwFQSWIidPaddedTypicalSource_r_purity_le
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp)
    (source0 : PureVector (Prod (Prod atyp btyp) rtyp))
    (hsource0_lift :
      (adhwFQSWIidTypicalSourceLiftMatrix P B R) *
          source0.state.matrix *
          Matrix.conjTranspose (adhwFQSWIidTypicalSourceLiftMatrix P B R) =
        T.normalizedTypicalSource.matrix) :
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.applyPureVector source0
    adhwFQSWRPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) := by
  intro padAB source
  let ABtyp : ReferenceIsometry (Prod atyp btyp)
      (Prod (TensorPower a n) (TensorPower b n)) :=
    P.supportIsometry.prod B.supportIsometry
  have hT_R :
      T.normalizedTypicalSource.marginalB.matrix =
        R.supportIsometry.matrix * source0.state.marginalB.matrix *
          Matrix.conjTranspose R.supportIsometry.matrix := by
    rw [State.marginalB_matrix, ← hsource0_lift]
    change partialTraceA (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix *
          source0.state.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix)) =
      R.supportIsometry.matrix * source0.state.marginalB.matrix *
        Matrix.conjTranspose R.supportIsometry.matrix
    rw [referenceIsometry_prod_partialTraceA_conj]
    rfl
  have hsource_R :
      source.state.marginalB.matrix = source0.state.marginalB.matrix := by
    have hpur : source.Purifies source0.state.marginalB := by
      simpa [source] using
        padAB.applyPureVector_purifies (PureVector.purifies_marginalB source0)
    simpa [PureVector.purifies_iff, State.marginalB_matrix] using hpur
  have hsource_hs :
      hilbertSchmidtSq source.state.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalB.matrix := by
    rw [hsource_R]
  have hT_hs :
      hilbertSchmidtSq T.normalizedTypicalSource.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalB.matrix := by
    rw [hT_R]
    exact referenceIsometry_hilbertSchmidtSq_conj
      R.supportIsometry source0.state.marginalB
  rw [adhwFQSWRPurity, adhwFQSWARState_marginalB_eq_systemR,
    adhwFQSWSystemRState]
  rw [hsource_hs, ← hT_hs]
  exact T.purityR_le

/-- Narrow bridge from the compressed one-shot coordinates back to the
simultaneous typical source.  This records the concrete `A`/`B`/`R` typical
support isometries used by the next source-route slice without claiming the
final no-witness i.i.d. FQSW theorem. -/
structure ADHWFQSWIidCompressedSourceWitness
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] where
  paddedAtypEmbedding :
    ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e
  typicalBobRegister :
    ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp
  typicalRefRegister :
    ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp
  source : PureVector (Prod (Prod (Prod q e) btyp) rtyp)
  source_a_purity_le :
    adhwFQSWAPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
  source_r_purity_le :
    adhwFQSWRPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
  source_b_purity_le :
    hilbertSchmidtSq source.state.marginalA.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
  source_ar_purity_le :
    adhwFQSWARPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
  lifted_state_eq_normalizedTypicalSource :
    (let L := adhwFQSWIidCompressedSourceLiftMatrix
       paddedAtypEmbedding typicalBobRegister typicalRefRegister
     L * source.state.matrix * Matrix.conjTranspose L =
       T.normalizedTypicalSource.matrix)
  source_traceNorm_le_original :
    traceDistance T.normalizedTypicalSource.matrix (adhwFQSWIidSourceState ψ n).matrix ≤ ε

/-- Construct the compressed pure source whose lift is the normalized
simultaneously typical i.i.d. source. -/
theorem exists_adhwFQSWIidCompressedSourceWitness
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    Nonempty
      (ADHWFQSWIidCompressedSourceWitness
        ψ n δ ε T atyp btyp rtyp q e) := by
  classical
  let φ := adhwFQSWIidPureVector ψ n
  let ρ := adhwFQSWIidSourceState ψ n
  let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
  let L0 := adhwFQSWIidTypicalSourceLiftMatrix P B R
  let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
    P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
  let K : Matrix (Prod (Prod (Prod q e) btyp) rtyp) (Prod (Prod atyp btyp) rtyp) ℂ :=
    Matrix.kronecker padAB.matrix (1 : CMatrix rtyp)
  let Pi := adhwFQSWIidLiftProjectorTriple
    (a := a) (b := b) (r := r) n T.projectorA T.projectorB T.projectorR
  let v0 := Matrix.mulVec (Matrix.conjTranspose L0) φ.amp
  have hL0range : L0 * Matrix.conjTranspose L0 = Pi := by
    simpa [L0, Pi] using
      adhwFQSWIidTypicalSourceLiftMatrix_mul_conjTranspose P B R
  rcases T.projectorA_statement with ⟨_hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases T.projectorB_statement with ⟨_hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases T.projectorR_statement with ⟨_hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPAidT : T.projectorA * T.projectorA = T.projectorA := by
    simpa [T.projectorA_eq] using hPAid
  have hPBidT : T.projectorB * T.projectorB = T.projectorB := by
    simpa [T.projectorB_eq] using hPBid
  have hPRidT : T.projectorR * T.projectorR = T.projectorR := by
    simpa [T.projectorR_eq] using hPRid
  have hPiid : Pi * Pi = Pi := by
    simpa [Pi] using
      adhwFQSWIidLiftProjectorTriple_idempotent
        (a := a) (b := b) (r := r) n
        T.projectorA T.projectorB T.projectorR hPAidT hPBidT hPRidT
  have hrank :
      rankOneMatrix v0 = Matrix.conjTranspose L0 * ρ.matrix * L0 := by
    calc
      rankOneMatrix v0 =
          Matrix.conjTranspose L0 * rankOneMatrix φ.amp *
            Matrix.conjTranspose (Matrix.conjTranspose L0) := by
            simpa [v0] using
              rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
                (Matrix.conjTranspose L0) φ.amp
      _ = Matrix.conjTranspose L0 * ρ.matrix * L0 := by
            simp [ρ, φ, adhwFQSWIidSourceState, PureVector.state_matrix,
              Matrix.mul_assoc]
  have hvtrace_to_range :
      (rankOneMatrix v0).trace = (ρ.matrix * Pi).trace := by
    calc
      (rankOneMatrix v0).trace =
          (Matrix.conjTranspose L0 * ρ.matrix * L0).trace := by rw [hrank]
      _ = (Matrix.conjTranspose L0 * (ρ.matrix * L0)).trace := by
            exact congrArg Matrix.trace
              (Matrix.mul_assoc (Matrix.conjTranspose L0) ρ.matrix L0)
      _ = ((ρ.matrix * L0) * Matrix.conjTranspose L0).trace := by
            exact Matrix.trace_mul_comm (Matrix.conjTranspose L0) (ρ.matrix * L0)
      _ = (ρ.matrix * (L0 * Matrix.conjTranspose L0)).trace := by
            exact congrArg Matrix.trace
              (Matrix.mul_assoc ρ.matrix L0 (Matrix.conjTranspose L0))
      _ = (ρ.matrix * Pi).trace := by rw [hL0range]
  have hprojected_trace :
      (Pi * ρ.matrix * Pi).trace = (ρ.matrix * Pi).trace := by
    calc
      (Pi * ρ.matrix * Pi).trace =
          (Pi * (ρ.matrix * Pi)).trace := by
            exact congrArg Matrix.trace (Matrix.mul_assoc Pi ρ.matrix Pi)
      _ = ((ρ.matrix * Pi) * Pi).trace := by
            exact Matrix.trace_mul_comm Pi (ρ.matrix * Pi)
      _ = (ρ.matrix * (Pi * Pi)).trace := by
            exact congrArg Matrix.trace (Matrix.mul_assoc ρ.matrix Pi Pi)
      _ = (ρ.matrix * Pi).trace := by rw [hPiid]
  have hvtrace_eq :
      (rankOneMatrix v0).trace = (Pi * ρ.matrix * Pi).trace := by
    rw [hvtrace_to_range, hprojected_trace]
  have hpos : 0 < (rankOneMatrix v0).trace.re := by
    have hproj : 0 < (Pi * ρ.matrix * Pi).trace.re := by
      simpa [Pi, ρ, adhwFQSWIidProjectedSourceMatrix] using
        T.normalizedTypicalSource_projected_trace_pos
    rw [hvtrace_eq]
    exact hproj
  let source0 : PureVector (Prod (Prod atyp btyp) rtyp) :=
    PureVector.normalize v0 hpos
  let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
    padAB.applyPureVector source0
  have hlift_rank :
      L0 * rankOneMatrix v0 * Matrix.conjTranspose L0 = Pi * ρ.matrix * Pi := by
    calc
      L0 * rankOneMatrix v0 * Matrix.conjTranspose L0 =
          L0 * (Matrix.conjTranspose L0 * ρ.matrix * L0) *
            Matrix.conjTranspose L0 := by
            rw [hrank]
      _ = (L0 * Matrix.conjTranspose L0) * ρ.matrix *
            (L0 * Matrix.conjTranspose L0) := by
            simp [Matrix.mul_assoc]
      _ = Pi * ρ.matrix * Pi := by rw [hL0range]
  have hsource0_lift :
      L0 * source0.state.matrix * Matrix.conjTranspose L0 =
        T.normalizedTypicalSource.matrix := by
    dsimp [source0]
    calc
      L0 * (PureVector.normalize v0 hpos).state.matrix * Matrix.conjTranspose L0 =
          L0 * (((((rankOneMatrix v0).trace.re)⁻¹ : ℝ) : ℂ) • rankOneMatrix v0) *
            Matrix.conjTranspose L0 := by
            rw [PureVector.normalize_state_matrix]
      _ = (((((rankOneMatrix v0).trace.re)⁻¹ : ℝ) : ℂ) •
            (L0 * rankOneMatrix v0 * Matrix.conjTranspose L0)) := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = (((((Pi * ρ.matrix * Pi).trace.re)⁻¹ : ℝ) : ℂ) •
            (Pi * ρ.matrix * Pi)) := by
            rw [hlift_rank]
            have htrace_re :
                (rankOneMatrix v0).trace.re = (Pi * ρ.matrix * Pi).trace.re :=
              congrArg Complex.re hvtrace_eq
            rw [htrace_re]
      _ = T.normalizedTypicalSource.matrix := by
            simpa [Pi, ρ, adhwFQSWIidProjectedSourceMatrix] using
              (T.normalizedTypicalSource_matrix_eq).symm
  have hsource_state :
      source.state.matrix =
        K * source0.state.matrix * Matrix.conjTranspose K := by
    simpa [source, K, PureVector.state_matrix,
      ReferenceIsometry.applyPureVector_amp] using
      (padAB.rankOne_applyAmp source0.amp).trans
        (referenceIsometry_applyMatrix_eq_kronecker_one_conj
          padAB (rankOneMatrix source0.amp))
  have hKiso :
      Matrix.conjTranspose K * K =
        (1 : CMatrix (Prod (Prod atyp btyp) rtyp)) := by
    let idR : ReferenceIsometry rtyp rtyp :=
      ReferenceIsometry.ofEquiv (Equiv.refl rtyp)
    let padR : ReferenceIsometry (Prod (Prod atyp btyp) rtyp)
        (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.prod idR
    have hpadR : padR.matrix = K := by
      ext i j
      simp [padR, idR, K, ReferenceIsometry.prod, ReferenceIsometry.ofEquiv,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    simpa [hpadR] using padR.isometry
  have hL_eq :
      L = L0 * Matrix.conjTranspose K := by
    simpa [L, L0, padAB, K] using
      adhwFQSWIidCompressedSourceLiftMatrix_eq_typicalSourceLiftMatrix_mul_paddingAdjoint
        P B R
  have hsource_a_purity_le :
      adhwFQSWAPurity source ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) := by
    simpa [padAB, source] using
      adhwFQSWIidPaddedTypicalSource_a_purity_le P B R source0 hsource0_lift
  have hsource_r_purity_le :
      adhwFQSWRPurity source ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) := by
    simpa [padAB, source] using
      adhwFQSWIidPaddedTypicalSource_r_purity_le P B R source0 hsource0_lift
  have hsource_b_purity_le :
      hilbertSchmidtSq source.state.marginalA.marginalB.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
    simpa [padAB, source] using
      adhwFQSWIidPaddedTypicalSource_b_purity_le P B R source0 hsource0_lift
  have hsource_ar_purity_le :
      adhwFQSWARPurity source ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
    rw [adhwFQSWARPurity_eq_systemBPurity source]
    exact hsource_b_purity_le
  refine
    ⟨{ paddedAtypEmbedding := P
       typicalBobRegister := B
       typicalRefRegister := R
       source := source
       source_a_purity_le := hsource_a_purity_le
       source_r_purity_le := hsource_r_purity_le
       source_b_purity_le := hsource_b_purity_le
       source_ar_purity_le := hsource_ar_purity_le
       lifted_state_eq_normalizedTypicalSource := ?_
       source_traceNorm_le_original := T.normalized_traceNorm_le }⟩
  calc
    L * source.state.matrix * Matrix.conjTranspose L =
        (L0 * Matrix.conjTranspose K) *
          (K * source0.state.matrix * Matrix.conjTranspose K) *
          Matrix.conjTranspose (L0 * Matrix.conjTranspose K) := by
          rw [hL_eq, hsource_state]
    _ = L0 * source0.state.matrix * Matrix.conjTranspose L0 := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          calc
            (L0 * Matrix.conjTranspose K) *
                (K * source0.state.matrix * Matrix.conjTranspose K) *
                (K * Matrix.conjTranspose L0) =
              L0 * ((Matrix.conjTranspose K * K) *
                  source0.state.matrix * (Matrix.conjTranspose K * K)) *
                  Matrix.conjTranspose L0 := by
                simp [Matrix.mul_assoc]
            _ = L0 * source0.state.matrix * Matrix.conjTranspose L0 := by
                  rw [hKiso]
                  simp [Matrix.mul_assoc]
    _ = T.normalizedTypicalSource.matrix := hsource0_lift

/-- Constant absorption used by the mixed source-route `skoro` estimate.  The
`4 ≤ nδ` tail condition supplies one factor of two, while nonnegative mutual
information supplies the remaining exponent slack. -/
private theorem fqsw_two_mul_three_delta_pow_le_target_pow
    (n : ℕ) (I δ : ℝ)
    (hI_nonneg : 0 ≤ I)
    (hn_large : 4 ≤ (n : ℝ) * δ) :
    2 * (2 : ℝ) ^ ((n : ℝ) * (3 * δ)) ≤
      (2 : ℝ) ^ ((n : ℝ) * (I + (7 / 2 : ℝ) * δ)) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hconst_absorb :
      (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (I + (1 / 2 : ℝ) * δ)) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (I + (1 / 2 : ℝ) * δ)) := by
        refine Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) ?_
        have hdelta_part : 1 ≤ (n : ℝ) * ((1 / 2 : ℝ) * δ) := by
          calc
            (1 : ℝ) ≤ 2 := by norm_num
            _ ≤ (n : ℝ) * δ / 2 := by nlinarith
            _ = (n : ℝ) * ((1 / 2 : ℝ) * δ) := by ring
        have hIpart : 0 ≤ (n : ℝ) * I := mul_nonneg hn_nonneg hI_nonneg
        calc
          (1 : ℝ) ≤ (n : ℝ) * ((1 / 2 : ℝ) * δ) := hdelta_part
          _ ≤ (n : ℝ) * I + (n : ℝ) * ((1 / 2 : ℝ) * δ) :=
                le_add_of_nonneg_left hIpart
          _ = (n : ℝ) * (I + (1 / 2 : ℝ) * δ) := by ring
  have hpow_three_nonneg :
      0 ≤ (2 : ℝ) ^ ((n : ℝ) * (3 * δ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hmul :=
    mul_le_mul_of_nonneg_right hconst_absorb hpow_three_nonneg
  calc
    2 * (2 : ℝ) ^ ((n : ℝ) * (3 * δ))
        ≤ (2 : ℝ) ^ ((n : ℝ) * (I + (1 / 2 : ℝ) * δ)) *
            (2 : ℝ) ^ ((n : ℝ) * (3 * δ)) := hmul
    _ = (2 : ℝ) ^ ((n : ℝ) * (I + (7 / 2 : ℝ) * δ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring

/-- Scalar `skoro` estimate for the mixed-slack padded source route.  The
`AR` term uses the source `AR` purity, while the product term uses the separate
`A` and `R` purity estimates.  The finite `q` upper rounding and `4 ≤ nδ`
absorb the constants without changing the source denominator `|q|²`. -/
private theorem fqsw_mixed_source_fourthRootArgument_scalar_le_skoro
    (n : ℕ) (I EB HA HB HR δtyp δrate Q E Rdim Apu Rpu ARpu : ℝ)
    (hbaseAR : (1 / 2 : ℝ) * I + EB + HR - HB = I)
    (hbaseProd : (1 / 2 : ℝ) * I + EB - HA = 0)
    (hI_nonneg : 0 ≤ I)
    (hδrate_nonneg : 0 ≤ δrate)
    (hδtyp_le_quarter : δtyp ≤ δrate / 4)
    (hn_large : 4 ≤ (n : ℝ) * δrate)
    (hQ_nonneg : 0 ≤ Q) (hE_nonneg : 0 ≤ E) (hRdim_nonneg : 0 ≤ Rdim)
    (hApu_nonneg : 0 ≤ Apu) (hRpu_nonneg : 0 ≤ Rpu) (hARpu_nonneg : 0 ≤ ARpu)
    (hQ_upper :
      Q ≤ (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate)))
    (hE_upper :
      E ≤ (2 : ℝ) ^ ((n : ℝ) * EB))
    (hRdim_upper :
      Rdim ≤ (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp)))
    (hApu_upper :
      Apu ≤ (2 : ℝ) ^ (-((n : ℝ) * (HA - δtyp))))
    (hRpu_upper :
      Rpu ≤ (2 : ℝ) ^ (-((n : ℝ) * (HR - δtyp))))
    (hARpu_upper :
      ARpu ≤ (2 : ℝ) ^ (-((n : ℝ) * (HB - δtyp)))) :
    (2 * Q * E * Rdim / (Q ^ 2)) * (ARpu + 2 * Apu * Rpu) ≤
      4 * (2 : ℝ) ^ ((n : ℝ) * (I + (7 / 2 : ℝ) * δrate)) / (Q ^ 2) := by
  let qPow : ℝ :=
    (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate))
  let ePow : ℝ := (2 : ℝ) ^ ((n : ℝ) * EB)
  let rPow : ℝ := (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp))
  let aPurPow : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (HA - δtyp)))
  let rPurPow : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (HR - δtyp)))
  let arPurPow : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (HB - δtyp)))
  let targetPow : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + (7 / 2 : ℝ) * δrate))
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hqPow_nonneg : 0 ≤ qPow := by
    dsimp [qPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hePow_nonneg : 0 ≤ ePow := by
    dsimp [ePow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hrPow_nonneg : 0 ≤ rPow := by
    dsimp [rPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have haPurPow_nonneg : 0 ≤ aPurPow := by
    dsimp [aPurPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hrPurPow_nonneg : 0 ≤ rPurPow := by
    dsimp [rPurPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have harPurPow_nonneg : 0 ≤ arPurPow := by
    dsimp [arPurPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetPow_nonneg : 0 ≤ targetPow := by
    dsimp [targetPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hQ_upper' : Q ≤ qPow := by simpa [qPow] using hQ_upper
  have hE_upper' : E ≤ ePow := by simpa [ePow] using hE_upper
  have hRdim_upper' : Rdim ≤ rPow := by simpa [rPow] using hRdim_upper
  have hApu_upper' : Apu ≤ aPurPow := by simpa [aPurPow] using hApu_upper
  have hRpu_upper' : Rpu ≤ rPurPow := by simpa [rPurPow] using hRpu_upper
  have hARpu_upper' : ARpu ≤ arPurPow := by simpa [arPurPow] using hARpu_upper
  have hQE : Q * E ≤ qPow * ePow :=
    mul_le_mul hQ_upper' hE_upper' hE_nonneg hqPow_nonneg
  have hQER : Q * E * Rdim ≤ qPow * ePow * rPow :=
    mul_le_mul hQE hRdim_upper' hRdim_nonneg
      (mul_nonneg hqPow_nonneg hePow_nonneg)
  have hQERAR : Q * E * Rdim * ARpu ≤ qPow * ePow * rPow * arPurPow :=
    mul_le_mul hQER hARpu_upper' hARpu_nonneg
      (mul_nonneg (mul_nonneg hqPow_nonneg hePow_nonneg) hrPow_nonneg)
  have hARpow :
      qPow * ePow * rPow * arPurPow =
        (2 : ℝ) ^ ((n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp)) := by
    dsimp [qPow, ePow, rPow, arPurPow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    calc
      (n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate) +
              (n : ℝ) * EB + (n : ℝ) * (HR + δtyp) +
              -((n : ℝ) * (HB - δtyp)) =
          (n : ℝ) * (((1 / 2 : ℝ) * I + EB + HR - HB) +
            (9 / 4 : ℝ) * δrate + 2 * δtyp) := by ring
      _ = (n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp) := by
            rw [hbaseAR]
  have hARexp_le :
      (n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp) ≤
        (n : ℝ) * (I + (7 / 2 : ℝ) * δrate) := by
    have htyp : 2 * δtyp ≤ (1 / 2 : ℝ) * δrate := by nlinarith
    have hinner :
        I + (9 / 4 : ℝ) * δrate + 2 * δtyp ≤
          I + (7 / 2 : ℝ) * δrate := by
      calc
        I + (9 / 4 : ℝ) * δrate + 2 * δtyp
            ≤ I + (9 / 4 : ℝ) * δrate + (1 / 2 : ℝ) * δrate := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left htyp (I + (9 / 4 : ℝ) * δrate)
        _ = I + (11 / 4 : ℝ) * δrate := by ring
        _ ≤ I + (7 / 2 : ℝ) * δrate := by
              have hslack :
                  (11 / 4 : ℝ) * δrate ≤ (7 / 2 : ℝ) * δrate :=
                mul_le_mul_of_nonneg_right (by norm_num : (11 / 4 : ℝ) ≤ 7 / 2)
                  hδrate_nonneg
              simpa [add_comm] using add_le_add_left hslack I
    exact mul_le_mul_of_nonneg_left hinner hn_nonneg
  have hARpow_le_target :
      (2 : ℝ) ^ ((n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp)) ≤
        targetPow := by
    dsimp [targetPow]
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hARexp_le
  have hARterm_le :
      2 * Q * E * Rdim * ARpu / (Q ^ 2) ≤
        2 * targetPow / (Q ^ 2) := by
    have hnum :
        2 * Q * E * Rdim * ARpu ≤ 2 * targetPow := by
      have hcore :
          Q * E * Rdim * ARpu ≤ targetPow := by
        exact hQERAR.trans (by simpa [hARpow] using hARpow_le_target)
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 2))
    exact div_le_div_of_nonneg_right hnum (sq_nonneg Q)
  have hQERA : Q * E * Rdim * Apu ≤ qPow * ePow * rPow * aPurPow :=
    mul_le_mul hQER hApu_upper' hApu_nonneg
      (mul_nonneg (mul_nonneg hqPow_nonneg hePow_nonneg) hrPow_nonneg)
  have hQERARprod :
      Q * E * Rdim * Apu * Rpu ≤ qPow * ePow * rPow * aPurPow * rPurPow :=
    mul_le_mul hQERA hRpu_upper' hRpu_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hqPow_nonneg hePow_nonneg) hrPow_nonneg)
        haPurPow_nonneg)
  have hProdPow :
      qPow * ePow * rPow * aPurPow * rPurPow =
        (2 : ℝ) ^ ((n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp)) := by
    dsimp [qPow, ePow, rPow, aPurPow, rPurPow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    calc
      (n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate) +
              (n : ℝ) * EB + (n : ℝ) * (HR + δtyp) +
              -((n : ℝ) * (HA - δtyp)) +
              -((n : ℝ) * (HR - δtyp)) =
          (n : ℝ) * (((1 / 2 : ℝ) * I + EB - HA) +
            (9 / 4 : ℝ) * δrate + 3 * δtyp) := by ring
      _ = (n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp) := by
            rw [hbaseProd]
            ring
  have hProdExp_le_three :
      (n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp) ≤
        (n : ℝ) * (3 * δrate) := by
    have htyp : 3 * δtyp ≤ (3 / 4 : ℝ) * δrate := by nlinarith
    have hinner :
        (9 / 4 : ℝ) * δrate + 3 * δtyp ≤ 3 * δrate := by
      calc
        (9 / 4 : ℝ) * δrate + 3 * δtyp
            ≤ (9 / 4 : ℝ) * δrate + (3 / 4 : ℝ) * δrate := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left htyp ((9 / 4 : ℝ) * δrate)
        _ = 3 * δrate := by ring
    exact mul_le_mul_of_nonneg_left hinner hn_nonneg
  have hProdPow_le_three :
      (2 : ℝ) ^ ((n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp)) ≤
        (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hProdExp_le_three
  have htwo_three_le_target :
      2 * (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) ≤ targetPow := by
    exact
      fqsw_two_mul_three_delta_pow_le_target_pow n I δrate hI_nonneg hn_large
  have hProdterm_le :
      4 * Q * E * Rdim * Apu * Rpu / (Q ^ 2) ≤
        2 * targetPow / (Q ^ 2) := by
    have hnum :
        4 * Q * E * Rdim * Apu * Rpu ≤ 2 * targetPow := by
      have hcore :
          Q * E * Rdim * Apu * Rpu ≤
            (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) := by
        calc
          Q * E * Rdim * Apu * Rpu ≤
              qPow * ePow * rPow * aPurPow * rPurPow := hQERARprod
          _ = (2 : ℝ) ^ ((n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp)) :=
                hProdPow
          _ ≤ (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) := hProdPow_le_three
      have hscaled :
          4 * (Q * E * Rdim * Apu * Rpu) ≤
            4 * (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) :=
        mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 4)
      have htarget_scaled :
          4 * (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) ≤ 2 * targetPow := by
        calc
          4 * (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) =
              2 * (2 * (2 : ℝ) ^ ((n : ℝ) * (3 * δrate))) := by ring
          _ ≤ 2 * targetPow :=
              mul_le_mul_of_nonneg_left htwo_three_le_target
                (by norm_num : (0 : ℝ) ≤ 2)
      have hscaled' :
          4 * Q * E * Rdim * Apu * Rpu ≤
            4 * (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) := by
        calc
          4 * Q * E * Rdim * Apu * Rpu =
              4 * (Q * E * Rdim * Apu * Rpu) := by ring
          _ ≤ 4 * (2 : ℝ) ^ ((n : ℝ) * (3 * δrate)) := hscaled
      exact hscaled'.trans htarget_scaled
    exact div_le_div_of_nonneg_right hnum (sq_nonneg Q)
  calc
    (2 * Q * E * Rdim / (Q ^ 2)) * (ARpu + 2 * Apu * Rpu)
        = 2 * Q * E * Rdim * ARpu / (Q ^ 2) +
            4 * Q * E * Rdim * Apu * Rpu / (Q ^ 2) := by ring
    _ ≤ 2 * targetPow / (Q ^ 2) + 2 * targetPow / (Q ^ 2) :=
          add_le_add hARterm_le hProdterm_le
    _ = 4 * targetPow / (Q ^ 2) := by ring
    _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (I + (7 / 2 : ℝ) * δrate)) / (Q ^ 2) := by
          rfl

/-- The padded compressed source satisfies the ADHW source-route `skoro`
fourth-root argument bound with mixed typicality/rate slack. -/
theorem ADHWFQSWIidCompressedSourceWitness.fourthRootArgument_le_iid_skoro_mixed
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e)
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (hδrate_nonneg : 0 ≤ δrate)
    (hδtyp_le_quarter : δtyp ≤ δrate / 4)
    (hn_large : 4 ≤ (n : ℝ) * δrate) :
    adhwFQSWOneShotFourthRootArgument W.source q ≤
      4 * (2 : ℝ) ^ ((n : ℝ) *
        (mutualInformation ψ.state.stateMergingReferenceState +
          (7 / 2 : ℝ) * δrate)) /
        ((Fintype.card q : ℝ) ^ 2) := by
  let I : ℝ := mutualInformation ψ.state.stateMergingReferenceState
  let EB : ℝ := ψ.fqswEbitYieldRate
  let HA : ℝ := adhwFQSWEntropyA ψ
  let HB : ℝ := adhwFQSWEntropyB ψ
  let HR : ℝ := adhwFQSWEntropyR ψ
  have hbaseAR : (1 / 2 : ℝ) * I + EB + HR - HB = I := by
    dsimp [I, EB, HA, HB, HR]
    unfold PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    ring
  have hbaseProd : (1 / 2 : ℝ) * I + EB - HA = 0 := by
    dsimp [I, EB, HA, HB, HR]
    unfold PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    ring
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact State.mutualInformation_nonneg ψ.state.stateMergingReferenceState
  have hq_pos_nat : 0 < Fintype.card q := Fintype.card_pos_iff.mpr inferInstance
  have hq_pos : 0 < (Fintype.card q : ℝ) := by exact_mod_cast hq_pos_nat
  have hq_nonneg : 0 ≤ (Fintype.card q : ℝ) := le_of_lt hq_pos
  have he_nonneg : 0 ≤ (Fintype.card e : ℝ) := Nat.cast_nonneg _
  have hrtyp_nonneg : 0 ≤ (Fintype.card rtyp : ℝ) := Nat.cast_nonneg _
  have hApu_nonneg : 0 ≤ adhwFQSWAPurity W.source := by
    simpa [adhwFQSWAPurity] using
      hilbertSchmidtSq_nonneg ((adhwFQSWARState W.source).marginalA.matrix)
  have hRpu_nonneg : 0 ≤ adhwFQSWRPurity W.source := by
    simpa [adhwFQSWRPurity] using
      hilbertSchmidtSq_nonneg ((adhwFQSWARState W.source).marginalB.matrix)
  have hARpu_nonneg : 0 ≤ adhwFQSWARPurity W.source := by
    simpa [adhwFQSWARPurity] using
      hilbertSchmidtSq_nonneg (adhwFQSWARState W.source).matrix
  have hQ_upper :
      (Fintype.card q : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate)) := by
    have hlog :=
      le_two_rpow_of_log2_le hq_pos
        balancedRateChoice.rateChoice.communication_log_le
    simpa [I, adhwFQSWIidRoundedCommunicationLogUpperTarget,
      PureVector.fqswCommunicationRate] using hlog
  have hE_upper :
      (Fintype.card e : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * EB) := by
    simpa [EB] using balancedRateChoice.ebit_card_upper_for_target
  have hRdim_upper :
      (Fintype.card rtyp : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp)) := by
    calc
      (Fintype.card rtyp : ℝ) =
          (adhwFQSWSystemRState ψ).typicalSubspaceDimension n T.typicalitySlack :=
            W.typicalRefRegister.card_eq_projector_rank
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp)) := T.rankR_upper
      _ = (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp)) := by rfl
  have hscalar :=
    fqsw_mixed_source_fourthRootArgument_scalar_le_skoro
      n I EB HA HB HR δtyp δrate
      (Fintype.card q : ℝ) (Fintype.card e : ℝ) (Fintype.card rtyp : ℝ)
      (adhwFQSWAPurity W.source) (adhwFQSWRPurity W.source)
      (adhwFQSWARPurity W.source)
      hbaseAR hbaseProd hI_nonneg hδrate_nonneg hδtyp_le_quarter hn_large
      hq_nonneg he_nonneg hrtyp_nonneg hApu_nonneg hRpu_nonneg hARpu_nonneg
      hQ_upper hE_upper hRdim_upper
      (by simpa [HA] using W.source_a_purity_le)
      (by simpa [HR] using W.source_r_purity_le)
      (by simpa [HB] using W.source_ar_purity_le)
  simpa [adhwFQSWOneShotFourthRootArgument, Fintype.card_prod, I,
    mul_assoc, mul_left_comm, mul_comm] using hscalar

/-- Mixed-slack source-route one-shot tail for the padded compressed source.
This closes the ADHW `skoro` step internally from the compressed source purity
fields and the balanced finite-register choice. -/
theorem ADHWFQSWIidCompressedSourceWitness.oneShotTail_le_mixed
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e)
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (hδrate_nonneg : 0 ≤ δrate)
    (hδtyp_le_quarter : δtyp ≤ δrate / 4)
    (hn_large : 4 ≤ (n : ℝ) * δrate) :
    adhwFQSWOneShotErrorBound W.source q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 8)) := by
  have hsource_a_purity_le := W.source_a_purity_le
  have hsource_r_purity_le := W.source_r_purity_le
  have hsource_b_purity_le := W.source_b_purity_le
  have hsource_ar_purity_le := W.source_ar_purity_le
  have hskoro :
      adhwFQSWOneShotFourthRootArgument W.source q ≤
        4 * (2 : ℝ) ^ ((n : ℝ) *
          (mutualInformation ψ.state.stateMergingReferenceState +
            (7 / 2 : ℝ) * δrate)) /
          ((Fintype.card q : ℝ) ^ 2) :=
    W.fourthRootArgument_le_iid_skoro_mixed
      balancedRateChoice hδrate_nonneg hδtyp_le_quarter hn_large
  exact
    adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_slack_skoro_bound
      ψ W.source q n δrate (7 / 2 : ℝ) hδrate_nonneg
      (by norm_num) hskoro balancedRateChoice.rateChoice.communication_card_lower

/-- Source-route scalar post-compression bridge for ADHW fqsw.tex lines
1168-1175.  The two trace-distance perturbation terms are the Schumacher
compressed source versus the normalized simultaneous-typical source, and the
normalized simultaneous-typical source versus the original i.i.d. source.  The
one-shot term is supplied by the ADHW one-shot protocol on `W.source`. -/
theorem ADHWFQSWIidCompressedSourceWitness.postCompressionTraceNormBridge_le
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (honeShot :
      H.toOneShotProtocol.traceNormError ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))) :
    traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
        H.toOneShotProtocol.traceNormError +
        traceDistance T.normalizedTypicalSource.matrix
          (adhwFQSWIidSourceState ψ n).matrix ≤
      adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ := by
  have hcompressed :
      traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix ≤ ε :=
    T.schumacher_traceNorm_le_normalizedTypical
  have htypical :
      traceDistance T.normalizedTypicalSource.matrix
          (adhwFQSWIidSourceState ψ n).matrix ≤ ε :=
    W.source_traceNorm_le_original
  calc
    traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
        H.toOneShotProtocol.traceNormError +
        traceDistance T.normalizedTypicalSource.matrix
          (adhwFQSWIidSourceState ψ n).matrix
        ≤ ε + (Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))) + ε := by
          linarith
    _ = 2 * ε + Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8)) := by
          ring
    _ = adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ := rfl

/-- Convert an ADHW one-shot error-bound tail estimate into the concrete
post-compression bridge used by the i.i.d. source route. -/
theorem ADHWFQSWIidCompressedSourceWitness.postCompressionTraceNormBridge_le_of_oneShotBound
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (honeShotBound :
      adhwFQSWOneShotErrorBound W.source q ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))) :
    traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
        H.toOneShotProtocol.traceNormError +
        traceDistance T.normalizedTypicalSource.matrix
          (adhwFQSWIidSourceState ψ n).matrix ≤
      adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  W.postCompressionTraceNormBridge_le H
    (H.toOneShotProtocol_traceNormError_le.trans honeShotBound)

/-- Source-route witness for ADHW fqsw.tex lines 1168-1175.  It fixes the
compressed source witness and one-shot bound used in the double triangle, and
records the semantic trace-norm error for that fixed route. -/
structure ADHWFQSWIidSourceRouteBlock
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    where
  compressedSourceWitness :
    ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e
  oneShotBound :
    ADHWFQSWOneShotBound compressedSourceWitness.source q e
      (Equiv.refl (Prod q e))
  oneShotTail_le :
    adhwFQSWOneShotErrorBound compressedSourceWitness.source q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))
  traceNormError : ℝ
  traceNormError_le_sourceRoute :
    traceNormError ≤
      traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
        oneShotBound.toOneShotProtocol.traceNormError +
        traceDistance T.normalizedTypicalSource.matrix
          (adhwFQSWIidSourceState ψ n).matrix

namespace ADHWFQSWIidSourceRouteBlock

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
variable {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable (B : ADHWFQSWIidSourceRouteBlock ψ n δ ε T atyp btyp rtyp q e)

/-- The source-route semantic trace-norm error is bounded by the rounded ADHW
post-compression bound. -/
theorem traceNormError_le_rounded :
    B.traceNormError ≤ adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  B.traceNormError_le_sourceRoute.trans
    (B.compressedSourceWitness.postCompressionTraceNormBridge_le_of_oneShotBound
      B.oneShotBound B.oneShotTail_le)

/-- Normalized trace-distance form of the source-route rounded error bound. -/
theorem normalizedError_le_rounded_half :
    (1 / 2 : ℝ) * B.traceNormError ≤
      (1 / 2 : ℝ) * adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  mul_le_mul_of_nonneg_left B.traceNormError_le_rounded (by norm_num)

end ADHWFQSWIidSourceRouteBlock

/-- Mixed-slack source-route block for the final no-witness route.  The
typical projectors and compressed source use `δtyp`, while the finite
communication/ebit registers and one-shot exponential tail use `δrate`. -/
structure ADHWFQSWIidMixedSourceRouteBlock
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δtyp δrate ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    where
  compressedSourceWitness :
    ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e
  oneShotBound :
    ADHWFQSWOneShotBound compressedSourceWitness.source q e
      (Equiv.refl (Prod q e))
  oneShotTail_le_mixed :
    adhwFQSWOneShotErrorBound compressedSourceWitness.source q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 8))
  traceNormError : ℝ
  traceNormError_le_sourceRoute :
    traceNormError ≤
      traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
        oneShotBound.toOneShotProtocol.traceNormError +
        traceDistance T.normalizedTypicalSource.matrix
          (adhwFQSWIidSourceState ψ n).matrix

namespace ADHWFQSWIidMixedSourceRouteBlock

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
variable {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable (B : ADHWFQSWIidMixedSourceRouteBlock ψ n δtyp δrate ε T atyp btyp rtyp q e)

/-- The mixed source-route semantic trace-norm error is bounded by the rounded
post-compression estimate at the rate slack `δrate`. -/
theorem traceNormError_le_rounded_rate :
    B.traceNormError ≤ adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δrate := by
  have honeShot :
      B.oneShotBound.toOneShotProtocol.traceNormError ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 8)) :=
    B.oneShotBound.toOneShotProtocol_traceNormError_le.trans
      B.oneShotTail_le_mixed
  calc
    B.traceNormError ≤
        traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
          B.oneShotBound.toOneShotProtocol.traceNormError +
          traceDistance T.normalizedTypicalSource.matrix
            (adhwFQSWIidSourceState ψ n).matrix :=
        B.traceNormError_le_sourceRoute
    _ ≤ ε + Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 8)) + ε := by
        linarith [T.schumacher_traceNorm_le_normalizedTypical, honeShot,
          B.compressedSourceWitness.source_traceNorm_le_original]
    _ = adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δrate := by
        rw [adhwFQSWIidRoundedPostCompressionTraceErrorBound]
        ring

/-- Normalized trace-distance form of the mixed rounded error bound. -/
theorem normalizedError_le_rounded_rate_half :
    (1 / 2 : ℝ) * B.traceNormError ≤
      (1 / 2 : ℝ) * adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δrate :=
  mul_le_mul_of_nonneg_left B.traceNormError_le_rounded_rate (by norm_num)

end ADHWFQSWIidMixedSourceRouteBlock

/-- Assemble a source-route block from its fixed compressed source witness,
one-shot bound, one-shot tail estimate, and semantic double-triangle field. -/
theorem exists_adhwFQSWIidSourceRouteBlock
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (honeShotBound :
      adhwFQSWOneShotErrorBound W.source q ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))) :
    ∀ traceNormError : ℝ,
      traceNormError ≤
          traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
            H.toOneShotProtocol.traceNormError +
            traceDistance T.normalizedTypicalSource.matrix
              (adhwFQSWIidSourceState ψ n).matrix →
        Nonempty (ADHWFQSWIidSourceRouteBlock ψ n δ ε T atyp btyp rtyp q e) :=
  fun traceNormError hsemantic =>
    ⟨{ compressedSourceWitness := W
       oneShotBound := H
       oneShotTail_le := honeShotBound
       traceNormError := traceNormError
       traceNormError_le_sourceRoute := hsemantic }⟩

/-- Assemble a mixed-slack source-route block from the fixed compressed source
witness, one-shot bound, rate-slack tail estimate, and semantic double-triangle
field. -/
theorem exists_adhwFQSWIidMixedSourceRouteBlock
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (honeShotBound :
      adhwFQSWOneShotErrorBound W.source q ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 8))) :
    ∀ traceNormError : ℝ,
      traceNormError ≤
          traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
            H.toOneShotProtocol.traceNormError +
            traceDistance T.normalizedTypicalSource.matrix
              (adhwFQSWIidSourceState ψ n).matrix →
        Nonempty
          (ADHWFQSWIidMixedSourceRouteBlock
            ψ n δtyp δrate ε T atyp btyp rtyp q e) :=
  fun traceNormError hsemantic =>
    ⟨{ compressedSourceWitness := W
       oneShotBound := H
       oneShotTail_le_mixed := honeShotBound
       traceNormError := traceNormError
       traceNormError_le_sourceRoute := hsemantic }⟩

/-- One finite i.i.d. ADHW FQSW block produced by the simultaneous typicality,
padded-embedding, one-shot, and rounded-rate route of fqsw.tex lines
1093-1180. -/
structure ADHWFQSWIidBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε
  paddedAtypEmbedding :
    ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e
  typicalBobRegister :
    ADHWFQSWIidTypicalBobRegister ψ n δ ε typicalProjectors btyp
  typicalRefRegister :
    ADHWFQSWIidTypicalRefRegister ψ n δ ε typicalProjectors rtyp
  rateChoice : ADHWFQSWIidRateChoice ψ n δ q e
  oneShotCardinalitySideConditions :
    ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e
  sourceRouteBlock :
    ADHWFQSWIidSourceRouteBlock ψ n δ ε typicalProjectors atyp btyp rtyp q e

/-- Assemble one finite ADHW i.i.d. block from the already constructed
typicality, padding, rounded-rate, one-shot, compression, and post-compression
error records. -/
theorem exists_adhwFQSWIidBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (paddedAtypEmbedding :
      ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e)
    (typicalBobRegister :
      ADHWFQSWIidTypicalBobRegister ψ n δ ε typicalProjectors btyp)
    (typicalRefRegister :
      ADHWFQSWIidTypicalRefRegister ψ n δ ε typicalProjectors rtyp)
    (rateChoice : ADHWFQSWIidRateChoice ψ n δ q e)
    (oneShotCardinalitySideConditions :
      ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e)
    (sourceRouteBlock :
      ADHWFQSWIidSourceRouteBlock ψ n δ ε typicalProjectors atyp btyp rtyp q e) :
    Nonempty (ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :=
  ⟨{ typicalProjectors := typicalProjectors
     paddedAtypEmbedding := paddedAtypEmbedding
     typicalBobRegister := typicalBobRegister
     typicalRefRegister := typicalRefRegister
     rateChoice := rateChoice
     oneShotCardinalitySideConditions := oneShotCardinalitySideConditions
     sourceRouteBlock := sourceRouteBlock }⟩

/-- Assemble one finite ADHW i.i.d. block through the source-route
post-compression bridge instead of supplying the final post-compression trace
bound as a free hypothesis. -/
theorem exists_adhwFQSWIidBlockConstruction_of_sourceRoutePostCompression
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (paddedAtypEmbedding :
      ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e)
    (typicalBobRegister :
      ADHWFQSWIidTypicalBobRegister ψ n δ ε typicalProjectors btyp)
    (typicalRefRegister :
      ADHWFQSWIidTypicalRefRegister ψ n δ ε typicalProjectors rtyp)
    (rateChoice : ADHWFQSWIidRateChoice ψ n δ q e)
    (oneShotCardinalitySideConditions :
      ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e)
    (sourceRouteBlock :
      ADHWFQSWIidSourceRouteBlock ψ n δ ε typicalProjectors atyp btyp rtyp q e) :
    Nonempty (ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :=
  exists_adhwFQSWIidBlockConstruction
    ψ n δ ε atyp btyp rtyp q e
    typicalProjectors paddedAtypEmbedding typicalBobRegister typicalRefRegister
    rateChoice oneShotCardinalitySideConditions sourceRouteBlock

theorem ADHWFQSWIidBlockConstruction.sourceRouteTraceNormError_le_rounded
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :
    B.sourceRouteBlock.traceNormError ≤
      adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  B.sourceRouteBlock.traceNormError_le_rounded

theorem ADHWFQSWIidBlockConstruction.sourceRouteNormalizedError_le_rounded_half
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :
    (1 / 2 : ℝ) * B.sourceRouteBlock.traceNormError ≤
      (1 / 2 : ℝ) *
        adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  B.sourceRouteBlock.normalizedError_le_rounded_half

/-- The source-route operational data exposed by the i.i.d. witness helper.
It records the post-compression trace-norm error proved by a source-route
block, without pretending to be a full-source `FQSWBlockProtocol`. -/
structure ADHWFQSWIidSourceRouteOperationalSurface
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (q : Type x) (e : Type y) where
  traceNormError : ℝ
  traceNormError_le_rounded :
    traceNormError ≤ adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ

namespace ADHWFQSWIidSourceRouteOperationalSurface

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
variable {q : Type x} {e : Type y}

/-- Forget ADHW source-route proof metadata, retaining only the public FQSW
operational surface consumed by `PureVector.IsAchievableFQSW`. -/
def toFQSWOperationalSurface
    (S : ADHWFQSWIidSourceRouteOperationalSurface ψ n δ ε q e) :
    FQSWOperationalSurface ψ n q e where
  traceNormError := S.traceNormError

end ADHWFQSWIidSourceRouteOperationalSurface

namespace ADHWFQSWIidBlockConstruction

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- Forget the private typical support types while retaining the source-route
post-compression error surface proved by this block. -/
def sourceRouteOperationalSurface
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :
    ADHWFQSWIidSourceRouteOperationalSurface ψ n δ ε q e where
  traceNormError := B.sourceRouteBlock.traceNormError
  traceNormError_le_rounded := B.sourceRouteTraceNormError_le_rounded

theorem sourceRouteOperationalSurface_normalizedError_le_rounded_half
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :
    (1 / 2 : ℝ) * B.sourceRouteOperationalSurface.traceNormError ≤
      (1 / 2 : ℝ) *
        adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  B.sourceRouteNormalizedError_le_rounded_half

end ADHWFQSWIidBlockConstruction

/-- One finite mixed-slack ADHW i.i.d. FQSW block.  The simultaneous typical
support and compressed source use `δtyp`; the rounded communication and ebit
registers use `δrate`, which is the slack exposed to the public rate and error
estimates. -/
structure ADHWFQSWIidMixedBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δtyp δrate ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε
  paddedAtypEmbedding :
    ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e
  typicalBobRegister :
    ADHWFQSWIidTypicalBobRegister ψ n δtyp ε typicalProjectors btyp
  typicalRefRegister :
    ADHWFQSWIidTypicalRefRegister ψ n δtyp ε typicalProjectors rtyp
  balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e
  oneShotCardinalitySideConditions :
    ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e
  sourceRouteBlock :
    ADHWFQSWIidMixedSourceRouteBlock
      ψ n δtyp δrate ε typicalProjectors atyp btyp rtyp q e

/-- Assemble one finite mixed-slack ADHW block from the already constructed
typicality, padding, rounded-rate, one-shot, compression, and source-route
records. -/
theorem exists_adhwFQSWIidMixedBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δtyp δrate ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε)
    (paddedAtypEmbedding :
      ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e)
    (typicalBobRegister :
      ADHWFQSWIidTypicalBobRegister ψ n δtyp ε typicalProjectors btyp)
    (typicalRefRegister :
      ADHWFQSWIidTypicalRefRegister ψ n δtyp ε typicalProjectors rtyp)
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (oneShotCardinalitySideConditions :
      ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e)
    (sourceRouteBlock :
      ADHWFQSWIidMixedSourceRouteBlock
        ψ n δtyp δrate ε typicalProjectors atyp btyp rtyp q e) :
    Nonempty
      (ADHWFQSWIidMixedBlockConstruction
        ψ n δtyp δrate ε atyp btyp rtyp q e) :=
  ⟨{ typicalProjectors := typicalProjectors
     paddedAtypEmbedding := paddedAtypEmbedding
     typicalBobRegister := typicalBobRegister
     typicalRefRegister := typicalRefRegister
     balancedRateChoice := balancedRateChoice
     oneShotCardinalitySideConditions := oneShotCardinalitySideConditions
     sourceRouteBlock := sourceRouteBlock }⟩

theorem ADHWFQSWIidMixedBlockConstruction.rateChoice
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (B : ADHWFQSWIidMixedBlockConstruction ψ n δtyp δrate ε atyp btyp rtyp q e) :
    ADHWFQSWIidRateChoice ψ n δrate q e :=
  B.balancedRateChoice.rateChoice

theorem ADHWFQSWIidMixedBlockConstruction.sourceRouteTraceNormError_le_rounded_rate
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (B : ADHWFQSWIidMixedBlockConstruction ψ n δtyp δrate ε atyp btyp rtyp q e) :
    B.sourceRouteBlock.traceNormError ≤
      adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δrate :=
  B.sourceRouteBlock.traceNormError_le_rounded_rate

theorem ADHWFQSWIidMixedBlockConstruction.sourceRouteNormalizedError_le_rounded_rate_half
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (B : ADHWFQSWIidMixedBlockConstruction ψ n δtyp δrate ε atyp btyp rtyp q e) :
    (1 / 2 : ℝ) * B.sourceRouteBlock.traceNormError ≤
      (1 / 2 : ℝ) *
        adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δrate :=
  B.sourceRouteBlock.normalizedError_le_rounded_rate_half

namespace ADHWFQSWIidMixedBlockConstruction

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- Forget the private typical support types while retaining the mixed
source-route post-compression error surface proved by this block. -/
def sourceRouteOperationalSurface
    (B : ADHWFQSWIidMixedBlockConstruction ψ n δtyp δrate ε atyp btyp rtyp q e) :
    ADHWFQSWIidSourceRouteOperationalSurface ψ n δrate ε q e where
  traceNormError := B.sourceRouteBlock.traceNormError
  traceNormError_le_rounded := B.sourceRouteTraceNormError_le_rounded_rate

theorem sourceRouteOperationalSurface_normalizedError_le_rounded_rate_half
    (B : ADHWFQSWIidMixedBlockConstruction ψ n δtyp δrate ε atyp btyp rtyp q e) :
    (1 / 2 : ℝ) * B.sourceRouteOperationalSurface.traceNormError ≤
      (1 / 2 : ℝ) *
        adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δrate :=
  B.sourceRouteNormalizedError_le_rounded_rate_half

end ADHWFQSWIidMixedBlockConstruction

/-- Mixed-slack no-witness assembly of one finite ADHW i.i.d. block.  It reuses
the existing simultaneous-typicality, balanced-cardinality, compressed-source,
and one-shot APIs, then closes the tail with the source-route mixed `skoro`
estimate. -/
theorem exists_adhwFQSWIidMixedBlockConstruction_eventually
    (ψ : PureVector (Prod (Prod a b) r)) {δtyp δrate ε : ℝ}
    (hδtyp : 0 < δtyp) (hδrate : 0 < δrate) (hε : 0 < ε)
    (hδtyp_le_quarter : δtyp ≤ δrate / 4) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (atyp : Type u), ∃ (_ : Fintype atyp), ∃ (_ : DecidableEq atyp),
        ∃ (btyp : Type v), ∃ (_ : Fintype btyp), ∃ (_ : DecidableEq btyp),
          ∃ (rtyp : Type w), ∃ (_ : Fintype rtyp), ∃ (_ : DecidableEq rtyp),
            ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
              ∃ (_ : Nonempty q), ∃ (e : Type y), ∃ (_ : Fintype e),
                ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
                  Nonempty
                    (ADHWFQSWIidMixedBlockConstruction
                      ψ n δtyp δrate ε atyp btyp rtyp q e) := by
  obtain ⟨Ndata, hdata⟩ :=
    exists_adhwFQSWIidBalancedCardinalityChoice_mixed_eventually
      (ψ := ψ) hδtyp hδrate hε hδtyp_le_quarter
  let Nlarge : ℕ := Nat.ceil (4 / δrate)
  refine ⟨max Ndata Nlarge, ?_⟩
  intro n hn
  have hn_data : n ≥ Ndata := le_trans (Nat.le_max_left _ _) hn
  have hn_large_nat : n ≥ Nlarge := le_trans (Nat.le_max_right _ _) hn
  have hn_large : 4 ≤ (n : ℝ) * δrate := by
    have hceil : 4 / δrate ≤ (Nlarge : ℝ) := by
      simpa [Nlarge] using Nat.le_ceil (4 / δrate)
    have hnLargeR : (Nlarge : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_large_nat
    have hbound : 4 / δrate ≤ (n : ℝ) := hceil.trans hnLargeR
    have hmul := mul_le_mul_of_nonneg_right hbound hδrate.le
    have hcancel : (4 / δrate) * δrate = (4 : ℝ) := by
      field_simp [ne_of_gt hδrate]
    nlinarith
  obtain ⟨T, atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
      rtyp, hrtypF, hrtypD, q, hqF, hqD, hqN, e, heF, heD, heN,
      hatypDim, hbtypReg, hrtypReg, hbalancedRate, hbalancedCardinality⟩ :=
    hdata n hn_data
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨Btyp⟩ := hbtypReg
  obtain ⟨Rtyp⟩ := hrtypReg
  obtain ⟨Rbalanced⟩ := hbalancedRate
  obtain ⟨Bcard⟩ := hbalancedCardinality
  obtain ⟨P, hside⟩ :=
    Bcard.to_padded_and_sideConditions (δtyp := T.typicalitySlack) hatypDim
  obtain ⟨Sside⟩ := hside
  obtain ⟨W⟩ := exists_adhwFQSWIidCompressedSourceWitness T P Btyp Rtyp
  obtain ⟨H⟩ := exists_adhwFQSWIidCompressedOneShotBound W.source Sside
  have honeShotTail :
      adhwFQSWOneShotErrorBound W.source q ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 8)) :=
    W.oneShotTail_le_mixed Rbalanced hδrate.le hδtyp_le_quarter hn_large
  let traceNormError : ℝ :=
    traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
      H.toOneShotProtocol.traceNormError +
      traceDistance T.normalizedTypicalSource.matrix
        (adhwFQSWIidSourceState ψ n).matrix
  have hsemantic :
      traceNormError ≤
        traceDistance T.compressedSource.matrix T.normalizedTypicalSource.matrix +
          H.toOneShotProtocol.traceNormError +
          traceDistance T.normalizedTypicalSource.matrix
            (adhwFQSWIidSourceState ψ n).matrix := by
    dsimp [traceNormError]
    exact le_rfl
  obtain ⟨Route⟩ :=
    exists_adhwFQSWIidMixedSourceRouteBlock
      W H honeShotTail traceNormError hsemantic
  obtain ⟨Bmixed⟩ :=
    exists_adhwFQSWIidMixedBlockConstruction
      ψ n δtyp δrate ε atyp btyp rtyp q e
      T P Btyp Rtyp Rbalanced Sside Route
  refine ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
    rtyp, hrtypF, hrtypD, q, hqF, hqD, hqN, e, heF, heD, heN, ?_⟩
  exact ⟨Bmixed⟩

/-- ADHW i.i.d. FQSW construction record: the typical-subspace and Schumacher
compression route of fqsw.tex lines 1093-1180 supplies the block protocols
used by the asymptotic direct theorem. -/
structure ADHWFQSWIidConstruction (ψ : PureVector (Prod (Prod a b) r)) where
  typical_rate_blocks :
    ∀ δ : ℝ, 0 < δ → ∀ εerr : ℝ, 0 < εerr →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ (atyp : Type u), ∃ (_ : Fintype atyp), ∃ (_ : DecidableEq atyp),
          ∃ (btyp : Type v), ∃ (_ : Fintype btyp), ∃ (_ : DecidableEq btyp),
            ∃ (rtyp : Type w), ∃ (_ : Fintype rtyp), ∃ (_ : DecidableEq rtyp),
              ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
                ∃ (_ : Nonempty q), ∃ (e : Type y), ∃ (_ : Fintype e),
                  ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
                    Nonempty
                      (ADHWFQSWIidMixedBlockConstruction
                        ψ n (δ / 4) δ εerr atyp btyp rtyp q e)

/-- No-witness ADHW i.i.d. FQSW construction record.  The source route uses
`δtyp = δrate / 4`, matching the mixed `skoro` proof path. -/
theorem exists_adhwFQSWIidConstruction
    (ψ : PureVector (Prod (Prod a b) r)) :
    Nonempty (ADHWFQSWIidConstruction.{u, v, w, x, y} ψ) := by
  refine ⟨{ typical_rate_blocks := ?_ }⟩
  intro δ hδ εerr hεerr
  exact
    exists_adhwFQSWIidMixedBlockConstruction_eventually
      (ψ := ψ) (δtyp := δ / 4) (δrate := δ) (ε := εerr)
      (by positivity) hδ hεerr le_rfl

namespace PureVector

variable (ψ : PureVector (Prod (Prod a b) r))

/-- Witness-based ADHW direct FQSW helper: the i.i.d. typical-subspace and
Schumacher construction record yields eventual compressed-block protocols with
the ADHW rate window and explicit-source normalized error bound from fqsw.tex
lines 1093-1180. -/
theorem fqsw_direct_achievable_of_iidConstruction
    (h : ADHWFQSWIidConstruction.{u, v, w, x, y} ψ) :
    PureVector.IsAchievableFQSW.{u, v, w, x, y} ψ := by
  intro δ hδ εerr hεerr
  have hδ3_pos : 0 < δ / 3 := by positivity
  have hε4_pos : 0 < εerr / 4 := by positivity
  obtain ⟨Nblocks, hblocks⟩ := h.typical_rate_blocks (δ / 3) hδ3_pos (εerr / 4) hε4_pos
  obtain ⟨Nerr, hNerr⟩ :=
    eventually_half_adhwFQSWIidRoundedPostCompressionTraceErrorBound_le
      (δ := δ / 3) (ε := εerr) hδ3_pos hεerr
  refine ⟨max (max Nblocks Nerr) 1, fun n hn => ?_⟩
  have hn_blocks : n ≥ Nblocks := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_err : n ≥ Nerr := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_pos : 0 < n := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  obtain ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD, rtyp, hrtypF, hrtypD,
      q, hqF, hqD, hqN, e, heF, heD, heN, hBnonempty⟩ :=
    hblocks n hn_blocks
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨B⟩ := hBnonempty
  let S : ADHWFQSWIidSourceRouteOperationalSurface ψ n (δ / 3) (εerr / 4) q e :=
    B.sourceRouteOperationalSurface
  let Spublic : FQSWOperationalSurface ψ n q e := S.toFQSWOperationalSurface
  refine ⟨q, hqF, hqD, e, heF, heD, heN, Spublic, ?_, ?_, ?_⟩
  · have hrate := B.rateChoice.communicationLogRate_le hn_pos
    simp [FQSWOperationalSurface.communicationRate, if_neg (Nat.ne_of_gt hn_pos)]
    nlinarith [hδ]
  · have hyield := B.rateChoice.ebitYieldLogRate_ge hn_pos
    simp [FQSWOperationalSurface.ebitYieldRate, if_neg (Nat.ne_of_gt hn_pos)]
    nlinarith
  · change (1 / 2 : ℝ) * S.traceNormError ≤ εerr
    exact
      (B.sourceRouteOperationalSurface_normalizedError_le_rounded_rate_half).trans
        (hNerr n hn_err)

/-- No-witness ADHW direct FQSW theorem: for every pure source, the ADHW
typical-subspace, source compression, one-shot decoupling, and mixed-slack
source route of fqsw.tex lines 1093-1180 give direct FQSW achievability. -/
theorem fqsw_direct_achievable :
    PureVector.IsAchievableFQSW.{u, v, w, x, y} ψ := by
  intro δ hδ εerr hεerr
  have hδ3_pos : 0 < δ / 3 := by positivity
  have hδtyp_pos : 0 < (δ / 3) / 4 := by positivity
  have hε4_pos : 0 < εerr / 4 := by positivity
  obtain ⟨Nblocks, hblocks⟩ :=
    exists_adhwFQSWIidMixedBlockConstruction_eventually
      (ψ := ψ) (δtyp := (δ / 3) / 4) (δrate := δ / 3) (ε := εerr / 4)
      hδtyp_pos hδ3_pos hε4_pos le_rfl
  obtain ⟨Nerr, hNerr⟩ :=
    eventually_half_adhwFQSWIidRoundedPostCompressionTraceErrorBound_le
      (δ := δ / 3) (ε := εerr) hδ3_pos hεerr
  refine ⟨max (max Nblocks Nerr) 1, fun n hn => ?_⟩
  have hn_blocks : n ≥ Nblocks := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_err : n ≥ Nerr := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_pos : 0 < n := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  obtain ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD, rtyp, hrtypF, hrtypD,
      q, hqF, hqD, hqN, e, heF, heD, heN, hBnonempty⟩ :=
    hblocks n hn_blocks
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨B⟩ := hBnonempty
  let S : ADHWFQSWIidSourceRouteOperationalSurface ψ n (δ / 3) (εerr / 4) q e :=
    B.sourceRouteOperationalSurface
  let Spublic : FQSWOperationalSurface ψ n q e := S.toFQSWOperationalSurface
  refine ⟨q, hqF, hqD, e, heF, heD, heN, Spublic, ?_, ?_, ?_⟩
  · have hrate := B.rateChoice.communicationLogRate_le hn_pos
    simp [FQSWOperationalSurface.communicationRate, if_neg (Nat.ne_of_gt hn_pos)]
    nlinarith [hδ]
  · have hyield := B.rateChoice.ebitYieldLogRate_ge hn_pos
    simp [FQSWOperationalSurface.ebitYieldRate, if_neg (Nat.ne_of_gt hn_pos)]
    nlinarith
  · change (1 / 2 : ℝ) * S.traceNormError ≤ εerr
    exact
      (B.sourceRouteOperationalSurface_normalizedError_le_rounded_rate_half).trans
        (hNerr n hn_err)

end PureVector

end

end QIT
