/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel

/-!
# Measurement maps with quantum side information

Applying a measurement on subsystem `A` of a bipartite state while leaving the
side-information system `B` untouched, as required by the tripartite entropic
uncertainty statement. The identity-on-`B` factor is a single-Kraus (identity)
channel, so the side-information map is `Channel.measure M ⊗ Channel.idChannel`.

Source: Tomamichel2015FiniteResources, `apps.tex` (measurement maps
`M_X ∈ CPTP(A,X)`, applied to a tripartite `rho_ABC`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

namespace Channel

/-- The identity channel on a system, realized as a single-Kraus map with the
identity operator as its sole Kraus operator. -/
def idChannel (a : Type u) [Fintype a] [DecidableEq a] : Channel a a where
  map := MatrixMap.ofKraus (fun (_ : Unit) => (1 : CMatrix a))
  completelyPositive := by
    rw [MatrixMap.IsCompletelyPositive, MatrixMap.choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ (fun _ _ =>
      Matrix.posSemidef_vecMulVec_self_star (fun x : a × a => (1 : CMatrix a) x.2 x.1))
  tracePreserving := by
    intro X
    show (MatrixMap.ofKraus (fun (_ : Unit) => (1 : CMatrix a)) X).trace = X.trace
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    simp
  mapsPositive := MatrixMap.ofKraus_mapsPositive (fun (_ : Unit) => (1 : CMatrix a))

end Channel

variable {a : Type u} {b : Type v} {x : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype x] [DecidableEq x]

/-- Measure subsystem `A` of a bipartite state with a POVM `M`, keeping the
quantum side information `B` untouched. The output lives on `Prod x b`, where
`x` indexes the measurement outcomes. -/
def measureSubsystemState (M : POVM x a) (ρ : State (Prod a b)) :
    State (Prod x b) :=
  (Channel.prod (Channel.measure M) (Channel.idChannel b)).applyState ρ

end

end QIT
