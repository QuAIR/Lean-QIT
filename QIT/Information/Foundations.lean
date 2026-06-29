/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy
public import QIT.Information.EntropyTensorPower
public import QIT.Information.Fidelity
public import QIT.Information.FuchsVdG
public import QIT.Information.Renyi
public import QIT.Information.RenyiDPI
public import QIT.Information.ConditionalRenyi
public import QIT.Information.ConditionalRenyiTraceBridge
public import QIT.Information.CQGuessing
public import QIT.Information.Smooth
public import QIT.Information.SmoothEndpoint
public import QIT.Information.Typicality
public import QIT.Information.ConditionalTypicality
public import QIT.Information.AEP

/-!
# Information foundations

Low-conflict facade for entropy, fidelity, Rényi, smooth entropy, typicality,
and AEP infrastructure.  This file intentionally preserves the existing flat
module paths while giving downstream work a stable grouped import.
-/

@[expose] public section

namespace QIT
namespace Information
namespace Foundations

end Foundations
end Information
end QIT
