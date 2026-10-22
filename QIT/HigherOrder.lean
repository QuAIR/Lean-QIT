/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HigherOrder.Comb.Basic
public import QIT.HigherOrder.Comb.Admissible
public import QIT.HigherOrder.Comb.Closure
public import QIT.HigherOrder.Comb.Characterization
public import QIT.HigherOrder.Comb.Realization
public import QIT.HigherOrder.Comb.MemoryEffect
public import QIT.HigherOrder.Superchannel
public import QIT.HigherOrder.Superchannel.Realization
public import QIT.HigherOrder.Comb.Associativity
public import QIT.HigherOrder.Comb.Composition
public import QIT.HigherOrder.Comb.Compression
public import QIT.HigherOrder.Comb.PortReplacement
public import QIT.HigherOrder.Comb.ForwardContraction
public import QIT.HigherOrder.Comb.EventSchedule
public import QIT.HigherOrder.Comb.ScheduledTensor
public import QIT.HigherOrder.Comb.WireJoin
public import QIT.HigherOrder.Comb.CausalJoin
public import QIT.HigherOrder.Comb.IteratedContraction
public import QIT.HigherOrder.Comb.CausalComposition
public import QIT.HigherOrder.Comb.CausalAssociativity
public import QIT.HigherOrder.Comb.Instrument
public import QIT.HigherOrder.Comb.Completion
public import QIT.HigherOrder.Comb.InstrumentRealization
public import QIT.HigherOrder.Tester
public import QIT.HigherOrder.Tester.Boundary
public import QIT.HigherOrder.Tester.Characterization
public import QIT.HigherOrder.Tester.Instrument
public import QIT.HigherOrder.Tester.Realization

/-!
# Higher-order quantum maps

Public import surface for recursive comb normalization, ancillary map action,
finite superinstruments, and quantum testers.
-/

@[expose] public section
