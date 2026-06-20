/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Information.Entropy
public import QIT.Core.TraceNorm.Distance
public import QIT.Core.TraceNorm.Spectral
public import QIT.Core.TraceNorm.PositivePart
public import QIT.Core.TraceNorm.PositivePartBlock
public import QIT.Core.TraceNorm.Variational
public import QIT.Core.Information.Fidelity
public import QIT.Core.Information.FuchsVdG
public import QIT.Core.Information.Renyi
public import QIT.Core.Information.ConditionalRenyi
public import QIT.Core.Information.RenyiDPI
public import QIT.Core.Information.Smooth
public import QIT.Core.Information.CQGuessing

/-!
# Basic information quantities

Compatibility import surface for entropy, divergences, trace distance,
fidelity, smooth quantities, and cq guessing APIs.
-/

@[expose] public section

namespace QIT
namespace Information
namespace Basic

end Basic
end Information
end QIT
