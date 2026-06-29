/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.CQGuessing
public import QIT.Information.Smooth
public import QIT.Information.SmoothEndpoint
public import QIT.Information.HypothesisTestingMutualInformation
public import QIT.Information.ComparatorTest
public import QIT.Information.HypothesisTestingDPI
public import QIT.Information.HypothesisTestingPetzComparison

/-!
# One-shot information facade

Grouped import surface for smooth entropy, hypothesis-testing information, and
one-shot comparison lemmas.  This facade is additive: existing module paths stay
valid for active proof branches.
-/

@[expose] public section

namespace QIT
namespace Information
namespace OneShot

end OneShot
end Information
end QIT
