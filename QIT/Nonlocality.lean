/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.Bell
public import QIT.Nonlocality.Tsirelson
public import QIT.Nonlocality.TwoQubit
public import QIT.Nonlocality.SelfTesting
public import QIT.Nonlocality.ProjectiveRealization
public import QIT.Nonlocality.YangNavascues
public import QIT.Nonlocality.YangNavascues.BobLocal
public import QIT.Nonlocality.YangNavascues.RankOneSupport
public import QIT.Nonlocality.YangNavascues.BobSupport
public import QIT.Nonlocality.YangNavascues.Fourier
public import QIT.Nonlocality.YangNavascues.LocalIsometry
public import QIT.Nonlocality.YangNavascues.Coherence
public import QIT.Nonlocality.YangNavascues.Action

/-!
# Nonlocality interfaces

Thin nonlocality-facing import surface for Bell/CHSH, Tsirelson, and
self-testing work.
-/

@[expose] public section

universe uX uY uA uB u v w z

namespace QIT
namespace Nonlocality

namespace SelfTestingManifest

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]
variable {HA : Type u} {HB : Type v} {TA : Type w} {TB : Type z}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]

/-- Public nonlocality entrypoint for the manifest self-testing witness. -/
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
  SelfTesting.Manifest.main R hR hExtract

end SelfTestingManifest

namespace ProjectiveRealization

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B] [Inhabited A] [Inhabited B]

/-- Public nonlocality entrypoint for replacing finite POVM realizations by projective ones. -/
public theorem main (R : Bell.QuantumRealization X Y A B) :
    ∃ PR : Bell.ProjectiveQuantumRealization X Y A B,
      ∀ a b x y, PR.prob a b x y = R.prob a b x y :=
  SelfTesting.ProjectiveRealization.main R

end ProjectiveRealization

end Nonlocality
end QIT
