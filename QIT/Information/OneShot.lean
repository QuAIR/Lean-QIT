/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.CQGuessing
public import QIT.OneShot.Smooth
public import QIT.OneShot.SmoothEndpoint
public import QIT.HypothesisTesting.MutualInformation
public import QIT.HypothesisTesting.ComparatorTest
public import QIT.HypothesisTesting.DPI
public import QIT.HypothesisTesting.PetzComparison

/-!
# Compatibility one-shot information facade

Compatibility grouped import surface for downstream code that still imports the
information-layer one-shot facade. New one-shot modules live under
`QIT.OneShot.*`; use the top-level `QIT.OneShot` facade for new work.
-/

@[expose] public section

namespace QIT
namespace Information
namespace OneShot

end OneShot
end Information
end QIT
