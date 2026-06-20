/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Init
public import Mathlib.Data.Fintype.Prod

/-!
# Finite systems

Finite label types used by the local matrix model. `TensorPower a n` is the
right-associated type-level tensor power used for IID constructions
[Tomamichel2015FiniteResources, prelim.tex:38-43;
Wilde2011Qst, qit-notes.tex:1888-1920].
-/

@[expose] public section

namespace QIT

universe u

/-- Recursive finite tensor-power label type. -/
def TensorPower (a : Type u) : Nat -> Type u
  | 0 => PUnit
  | n + 1 => Prod a (TensorPower a n)

instance tensorPowerFintype {a : Type u} [Fintype a] (n : Nat) :
    Fintype (TensorPower a n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (Prod a (TensorPower a n)))

instance tensorPowerDecidableEq {a : Type u} [DecidableEq a] (n : Nat) :
    DecidableEq (TensorPower a n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Prod a (TensorPower a n)))

end QIT
