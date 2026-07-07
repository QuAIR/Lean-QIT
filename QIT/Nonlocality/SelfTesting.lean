/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.Bell
public import QIT.Nonlocality.TwoQubit

/-!
# Self-testing manifest scaffold

This module introduces the minimal statement surface for self-testing.
It separates a reusable witness layer from the future uniqueness theorem:
`RealizesTargetState` records that one quantum realization extracts a target
state, while `SelfTestsState` is the full "all realizations extract the target"
predicate [ColadangeloGohScarani2016SelfTesting, all_pure_v2.tex:70-128] and
[MayersYao2003SelfTesting, mayers-yao-2003-self-testing.tex:344-373] and
[MayersYao2003SelfTesting, mayers-yao-2003-self-testing.tex:375-390].

The auxiliary extraction predicate records the source-correct Yang-Navascues
shape `extra ⊗ target` from [ColadangeloGohScarani2016SelfTesting,
all_pure_v2.tex:161-188].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v w z uX uY uA uB uGA uGB uTA uTB

noncomputable section

namespace ReferenceIsometry

variable (a : Type u) [Fintype a] [DecidableEq a]

/-- Identity reference isometry. -/
def refl : ReferenceIsometry a a where
  matrix := 1
  isometry := by
    simp

end ReferenceIsometry

namespace TwoQubit
namespace LocalIsometry

variable (a : Type u) (b : Type v)
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Identity local isometry on a bipartite system. -/
def refl : LocalIsometry a a b b where
  alice := ReferenceIsometry.refl a
  bob := ReferenceIsometry.refl b

@[simp]
theorem refl_matrix :
    (refl a b).matrix = (1 : CMatrix (a × b)) := by
  change (1 : CMatrix a) ⊗ₖ (1 : CMatrix b) = (1 : CMatrix (a × b))
  rw [Matrix.one_kronecker_one]

@[simp]
theorem refl_applyState (rho : State (a × b)) :
    (refl a b).applyState rho = rho := by
  apply State.ext
  simp [applyState_matrix, applyMatrix]

end LocalIsometry
end TwoQubit

namespace Bell

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

variable {HA : Type u} {HB : Type v} {TA : Type w} {TB : Type z}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]

/--
Relabel a density state along a finite basis equivalence.

This is kept local to the Bell/self-testing layer for now; it is the only
matrix bookkeeping needed to state the source's `extra tensor target`
conclusion in the local-isometry output order.
-/
def reindexState {α : Type uGA} {β : Type uGB}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (rho : State α) : State β where
  matrix := rho.matrix.submatrix e.symm e.symm
  pos := rho.pos.submatrix e.symm
  trace_eq_one := by
    rw [← rho.trace_eq_one, Matrix.trace]
    apply Fintype.sum_equiv e.symm
    intro x
    rfl

@[simp]
theorem reindexState_matrix {α : Type uGA} {β : Type uGB}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (rho : State α) :
    (reindexState e rho).matrix = rho.matrix.submatrix e.symm e.symm :=
  rfl

/--
Reorder `(garbage_A × garbage_B) × (target_A × target_B)` into the output order
of a local isometry, `(garbage_A × target_A) × (garbage_B × target_B)`.
-/
def garbageTensorTargetEquiv (GA : Type uGA) (GB : Type uGB)
    (TA : Type uTA) (TB : Type uTB) :
    ((GA × GB) × (TA × TB)) ≃ ((GA × TA) × (GB × TB)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by
    rintro ⟨⟨ga, gb⟩, ⟨ta, tb⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨ga, ta⟩, ⟨gb, tb⟩⟩
    rfl

/--
Auxiliary-garbage tensor target state in local-isometry output order.

The source writes the conclusion as `|extra⟩ ⊗ |target⟩`; the local isometry in
this library outputs Alice-side factors together and Bob-side factors together,
so the product state is explicitly reindexed.
-/
def garbageTensorTargetState {GA : Type uGA} {GB : Type uGB}
    {TA : Type uTA} {TB : Type uTB}
    [Fintype GA] [DecidableEq GA] [Fintype GB] [DecidableEq GB]
    [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]
    (garbage : State (GA × GB)) (target : State (TA × TB)) :
    State ((GA × TA) × (GB × TB)) :=
  reindexState (garbageTensorTargetEquiv GA GB TA TB) (garbage.prod target)

@[simp]
theorem garbageTensorTargetState_matrix {GA : Type uGA} {GB : Type uGB}
    {TA : Type uTA} {TB : Type uTB}
    [Fintype GA] [DecidableEq GA] [Fintype GB] [DecidableEq GB]
    [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]
    (garbage : State (GA × GB)) (target : State (TA × TB)) :
    (garbageTensorTargetState garbage target).matrix =
      (garbage.prod target).matrix.submatrix
        (garbageTensorTargetEquiv GA GB TA TB).symm
        (garbageTensorTargetEquiv GA GB TA TB).symm :=
  rfl

/--
A physical bipartite state extracts a target bipartite state when a local
isometry maps the physical state to the target state.
-/
def ExtractsBipartiteState (rho : State (HA × HB)) (target : State (TA × TB)) : Prop :=
  ∃ V : TwoQubit.LocalIsometry HA TA HB TB, V.applyState rho = target

/--
Source-correct auxiliary extraction predicate for the Yang-Navascues route:
a local isometry maps the physical state to auxiliary garbage tensored with the
target state, in the local output ordering.
-/
def ExtractsBipartiteStateWithAux {GA : Type uGA} {GB : Type uGB}
    {TA : Type uTA} {TB : Type uTB}
    [Fintype GA] [DecidableEq GA] [Fintype GB] [DecidableEq GB]
    [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]
    (rho : State (HA × HB)) (garbage : State (GA × GB))
    (target : State (TA × TB)) : Prop :=
  ∃ V : TwoQubit.LocalIsometry HA (GA × TA) HB (GB × TB),
    V.applyState rho = garbageTensorTargetState garbage target

namespace QuantumRealization

/-- A quantum realization reproduces a Bell behavior's probability table. -/
def RealizesBehavior (R : QuantumRealization X Y A B) (p : Behavior X Y A B) : Prop :=
  ∀ a b x y, p.prob a b x y = R.prob a b x y

end QuantumRealization

/--
Witness layer for self-testing: one quantum realization reproduces the behavior
and its state extracts the target state by a local isometry.
-/
def RealizesTargetState (p : Behavior X Y A B) (target : State (TA × TB)) : Prop :=
  ∃ R : QuantumRealization X Y A B,
    R.RealizesBehavior p ∧
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      ExtractsBipartiteState R.rho target

namespace RealizesTargetState

/-- A realization plus an extraction witness gives the manifest target-state witness. -/
theorem of_realization (R : QuantumRealization X Y A B)
    {p : Behavior X Y A B} {target : State (TA × TB)}
    (hR : R.RealizesBehavior p)
    (hExtract :
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      ExtractsBipartiteState R.rho target) :
    RealizesTargetState p target :=
  ⟨R, hR, hExtract⟩

end RealizesTargetState

/--
Source-strength witness layer for self-testing with auxiliary garbage: one
quantum realization reproduces the behavior and its state extracts
`garbage ⊗ target` by a local isometry.

This matches the Mayers-Yao/Yang-Navascues output shape with explicit finite
auxiliary systems; it is still existential in the chosen realization.
-/
def RealizesTargetStateWithAux (p : Behavior X Y A B) (target : State (TA × TB)) : Prop :=
  ∃ R : QuantumRealization X Y A B,
    R.RealizesBehavior p ∧
      ∃ (GA : Type uGA) (GB : Type uGB),
        ∃ (instGA : Fintype GA) (decGA : DecidableEq GA)
          (instGB : Fintype GB) (decGB : DecidableEq GB),
          letI : Fintype GA := instGA
          letI : DecidableEq GA := decGA
          letI : Fintype GB := instGB
          letI : DecidableEq GB := decGB
          ∃ garbage : State (GA × GB),
            letI : Fintype R.HA := R.fintypeHA
            letI : DecidableEq R.HA := R.decidableEqHA
            letI : Fintype R.HB := R.fintypeHB
            letI : DecidableEq R.HB := R.decidableEqHB
            ExtractsBipartiteStateWithAux R.rho garbage target

namespace RealizesTargetStateWithAux

/--
A realization plus an auxiliary-garbage extraction witness gives the
source-strength manifest target-state witness.
-/
theorem of_realization (R : QuantumRealization X Y A B)
    {p : Behavior X Y A B} {target : State (TA × TB)}
    {GA : Type uGA} {GB : Type uGB}
    [Fintype GA] [DecidableEq GA] [Fintype GB] [DecidableEq GB]
    (garbage : State (GA × GB))
    (hR : R.RealizesBehavior p)
    (hExtract :
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      ExtractsBipartiteStateWithAux R.rho garbage target) :
    RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  ⟨R, hR, GA, GB, inferInstance, inferInstance, inferInstance, inferInstance, garbage, hExtract⟩

end RealizesTargetStateWithAux

/--
Full state self-testing predicate: the behavior has a target realization, and
every quantum realization of the behavior extracts the same target state.
-/
def SelfTestsState (p : Behavior X Y A B) (target : State (TA × TB)) : Prop :=
  RealizesTargetState p target ∧
    ∀ R : QuantumRealization X Y A B,
      R.RealizesBehavior p →
        letI : Fintype R.HA := R.fintypeHA
        letI : DecidableEq R.HA := R.decidableEqHA
        letI : Fintype R.HB := R.fintypeHB
        letI : DecidableEq R.HB := R.decidableEqHB
        ExtractsBipartiteState R.rho target

namespace SelfTestsState

/-- Package the manifest realization and all-realizations extraction clauses into a self-test. -/
theorem of_realizesTargetState {p : Behavior X Y A B} {target : State (TA × TB)}
    (hRealizes : RealizesTargetState p target)
    (hAll :
      ∀ R : QuantumRealization X Y A B,
        R.RealizesBehavior p →
          letI : Fintype R.HA := R.fintypeHA
          letI : DecidableEq R.HA := R.decidableEqHA
          letI : Fintype R.HB := R.fintypeHB
          letI : DecidableEq R.HB := R.decidableEqHB
          ExtractsBipartiteState R.rho target) :
    SelfTestsState p target :=
  ⟨hRealizes, hAll⟩

/-- A full self-test includes its manifest target-state realization witness. -/
theorem realizesTargetState {p : Behavior X Y A B} {target : State (TA × TB)}
    (h : SelfTestsState p target) :
    RealizesTargetState p target :=
  h.1

/-- A full self-test extracts the target from every realization of the behavior. -/
theorem extracts_every_realization {p : Behavior X Y A B} {target : State (TA × TB)}
    (h : SelfTestsState p target) (R : QuantumRealization X Y A B)
    (hR : R.RealizesBehavior p) :
    letI : Fintype R.HA := R.fintypeHA
    letI : DecidableEq R.HA := R.decidableEqHA
    letI : Fintype R.HB := R.fintypeHB
    letI : DecidableEq R.HB := R.decidableEqHB
    ExtractsBipartiteState R.rho target :=
  h.2 R hR

end SelfTestsState

/--
Source-strength full state self-testing predicate: the behavior has an
auxiliary-garbage target realization, and every realization extracts
`garbage ⊗ target` for some finite auxiliary systems and garbage state.
-/
def SelfTestsStateWithAux (p : Behavior X Y A B) (target : State (TA × TB)) : Prop :=
  RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target ∧
    ∀ R : QuantumRealization X Y A B,
      R.RealizesBehavior p →
        ∃ (GA : Type uGA) (GB : Type uGB),
          ∃ (instGA : Fintype GA) (decGA : DecidableEq GA)
            (instGB : Fintype GB) (decGB : DecidableEq GB),
            letI : Fintype GA := instGA
            letI : DecidableEq GA := decGA
            letI : Fintype GB := instGB
            letI : DecidableEq GB := decGB
            ∃ garbage : State (GA × GB),
              letI : Fintype R.HA := R.fintypeHA
              letI : DecidableEq R.HA := R.decidableEqHA
              letI : Fintype R.HB := R.fintypeHB
              letI : DecidableEq R.HB := R.decidableEqHB
              ExtractsBipartiteStateWithAux R.rho garbage target

namespace SelfTestsStateWithAux

/--
Package the auxiliary-garbage manifest realization and all-realizations
extraction clauses into a source-strength self-test.
-/
theorem of_realizesTargetStateWithAux {p : Behavior X Y A B} {target : State (TA × TB)}
    (hRealizes : RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target)
    (hAll :
      ∀ R : QuantumRealization X Y A B,
        R.RealizesBehavior p →
          ∃ (GA : Type uGA) (GB : Type uGB),
            ∃ (instGA : Fintype GA) (decGA : DecidableEq GA)
              (instGB : Fintype GB) (decGB : DecidableEq GB),
              letI : Fintype GA := instGA
              letI : DecidableEq GA := decGA
              letI : Fintype GB := instGB
              letI : DecidableEq GB := decGB
              ∃ garbage : State (GA × GB),
                letI : Fintype R.HA := R.fintypeHA
                letI : DecidableEq R.HA := R.decidableEqHA
                letI : Fintype R.HB := R.fintypeHB
                letI : DecidableEq R.HB := R.decidableEqHB
                ExtractsBipartiteStateWithAux R.rho garbage target) :
    SelfTestsStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  ⟨hRealizes, hAll⟩

/--
A source-strength full self-test includes its auxiliary-garbage manifest
target-state realization witness.
-/
theorem realizesTargetStateWithAux {p : Behavior X Y A B} {target : State (TA × TB)}
    (h : SelfTestsStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target) :
    RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  h.1

/--
A source-strength full self-test extracts `garbage ⊗ target` from every
realization of the behavior.
-/
theorem extracts_every_realization {p : Behavior X Y A B} {target : State (TA × TB)}
    (h : SelfTestsStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target)
    (R : QuantumRealization X Y A B)
    (hR : R.RealizesBehavior p) :
    ∃ (GA : Type uGA) (GB : Type uGB),
      ∃ (instGA : Fintype GA) (decGA : DecidableEq GA)
        (instGB : Fintype GB) (decGB : DecidableEq GB),
        letI : Fintype GA := instGA
        letI : DecidableEq GA := decGA
        letI : Fintype GB := instGB
        letI : DecidableEq GB := decGB
        ∃ garbage : State (GA × GB),
          letI : Fintype R.HA := R.fintypeHA
          letI : DecidableEq R.HA := R.decidableEqHA
          letI : Fintype R.HB := R.fintypeHB
          letI : DecidableEq R.HB := R.decidableEqHB
          ExtractsBipartiteStateWithAux R.rho garbage target :=
  h.2 R hR

end SelfTestsStateWithAux

end Bell

namespace SelfTesting

namespace Definition

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]
variable {TA : Type w} {TB : Type z}
variable [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]

/--
Public catalog-support entrypoint for a full state self-testing theorem.

This packages the two source-strength clauses: a manifest target realization,
and extraction of the same target from every realization of the behavior.
-/
public theorem main {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    (hRealizes : Bell.RealizesTargetState p target)
    (hAll :
      ∀ R : Bell.QuantumRealization X Y A B,
        R.RealizesBehavior p →
          letI : Fintype R.HA := R.fintypeHA
          letI : DecidableEq R.HA := R.decidableEqHA
          letI : Fintype R.HB := R.fintypeHB
          letI : DecidableEq R.HB := R.decidableEqHB
          Bell.ExtractsBipartiteState R.rho target) :
    Bell.SelfTestsState p target :=
  Bell.SelfTestsState.of_realizesTargetState hRealizes hAll

/--
Public catalog-support entrypoint for a full state self-testing theorem with
explicit auxiliary garbage in each local-isometry output.

This packages the manifest auxiliary target realization and the
all-realizations auxiliary extraction clause; it does not discard the auxiliary
systems.
-/
public theorem main_with_aux {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    (hRealizes :
      Bell.RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target)
    (hAll :
      ∀ R : Bell.QuantumRealization X Y A B,
        R.RealizesBehavior p →
          ∃ (GA : Type uGA) (GB : Type uGB),
            ∃ (instGA : Fintype GA) (decGA : DecidableEq GA)
              (instGB : Fintype GB) (decGB : DecidableEq GB),
              letI : Fintype GA := instGA
              letI : DecidableEq GA := decGA
              letI : Fintype GB := instGB
              letI : DecidableEq GB := decGB
              ∃ garbage : State (GA × GB),
                letI : Fintype R.HA := R.fintypeHA
                letI : DecidableEq R.HA := R.decidableEqHA
                letI : Fintype R.HB := R.fintypeHB
                letI : DecidableEq R.HB := R.decidableEqHB
                Bell.ExtractsBipartiteStateWithAux R.rho garbage target) :
    Bell.SelfTestsStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  Bell.SelfTestsStateWithAux.of_realizesTargetStateWithAux hRealizes hAll

end Definition

namespace Manifest

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]
variable {HA : Type u} {HB : Type v} {TA : Type w} {TB : Type z}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]

/-- Public catalog entrypoint for the manifest self-testing witness. -/
public theorem main (R : Bell.QuantumRealization X Y A B)
    {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    (hR : R.RealizesBehavior p)
    (hExtract :
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      Bell.ExtractsBipartiteState R.rho target) :
    Bell.RealizesTargetState p target :=
  Bell.RealizesTargetState.of_realization R hR hExtract

/-- Project the manifest realization witness from a full self-testing theorem. -/
public theorem of_selfTestsState {p : Bell.Behavior X Y A B}
    {target : State (TA × TB)}
    (h : Bell.SelfTestsState p target) :
    Bell.RealizesTargetState p target :=
  Bell.SelfTestsState.realizesTargetState h

/--
Public catalog-support entrypoint for a manifest self-testing witness with
explicit auxiliary garbage in the local-isometry output.
-/
public theorem main_with_aux (R : Bell.QuantumRealization X Y A B)
    {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    {GA : Type uGA} {GB : Type uGB}
    [Fintype GA] [DecidableEq GA] [Fintype GB] [DecidableEq GB]
    (garbage : State (GA × GB))
    (hR : R.RealizesBehavior p)
    (hExtract :
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      Bell.ExtractsBipartiteStateWithAux R.rho garbage target) :
    Bell.RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  Bell.RealizesTargetStateWithAux.of_realization.{w, z, uX, uY, uA, uB, uGA, uGB}
    R garbage hR hExtract

/--
Project the auxiliary-garbage manifest realization witness from a full
source-strength self-testing theorem.
-/
public theorem of_selfTestsStateWithAux {p : Bell.Behavior X Y A B}
    {target : State (TA × TB)}
    (h : Bell.SelfTestsStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target) :
    Bell.RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  Bell.SelfTestsStateWithAux.realizesTargetStateWithAux h

end Manifest
end SelfTesting

namespace TwoQubit

/-- The two-qubit singlet extracts itself by the identity local isometry. -/
theorem singletState_extracts_itself :
    Bell.ExtractsBipartiteState singletState singletState :=
  ⟨LocalIsometry.refl Bool Bool, by simp⟩

end TwoQubit

end

end QIT
