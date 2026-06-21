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

end Bell

namespace SelfTesting
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
