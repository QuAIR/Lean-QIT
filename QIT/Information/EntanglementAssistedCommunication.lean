/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.EntanglementAssisted
public import QIT.Information.EntanglementAssistedConverse
public import QIT.Information.EntanglementAssistedWeakConverse
public import QIT.Information.PositionBasedCoding
public import QIT.Information.SequentialDecoding
public import QIT.Information.EntanglementAssistedLowerBound
public import QIT.Information.PositionNaimarkTrace
public import QIT.Information.EntanglementAssistedHTLowerBound
public import QIT.Information.EntanglementAssistedPetzLowerBound
public import QIT.Information.HypothesisTestingMutualInformation
public import QIT.Information.ComparatorTest
public import QIT.Information.HypothesisTestingDPI
public import QIT.Information.HypothesisTestingPetzComparison

/-!
# Entanglement-assisted classical communication facade

Grouped import surface for one-shot and asymptotic entanglement-assisted
classical communication infrastructure.  It is an additive facade for active
branches; no underlying file paths are changed.
-/

@[expose] public section

namespace QIT
namespace Information
namespace EntanglementAssistedCommunication

end EntanglementAssistedCommunication
end Information
end QIT
