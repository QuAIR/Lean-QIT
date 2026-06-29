/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Holevo
public import QIT.Information.HSW
public import QIT.Information.HSWConverse
public import QIT.Information.RandomnessDistribution
public import QIT.Information.ConditionalTypicality
public import QIT.Information.GentleMeasurement
public import QIT.Information.HayashiNagaoka
public import QIT.Information.PackingLemma

/-!
# Classical capacity facade

Grouped import surface for Holevo information, HSW coding infrastructure, and
packing-lemma support.  It does not move `RandomnessDistribution.lean`; that
file remains at its current path for ongoing work.
-/

@[expose] public section

namespace QIT
namespace Information
namespace ClassicalCapacity

end ClassicalCapacity
end Information
end QIT
