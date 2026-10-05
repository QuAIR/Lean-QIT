/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.Basic
public import QIT.Coding.Quantum.PiNorm
public import QIT.Coding.Quantum.Stinespring
public import QIT.Coding.Quantum.BlowingUp
public import QIT.Coding.Quantum.PolyApprox
public import QIT.Coding.Quantum.StrongConverse.Final

/-!
# Quantum coding

Entanglement-generation and transmission codes, operational quantum capacity,
exponential strong-converse predicates, Stinespring lifts, decoder tests, and
the projective tensor norm of bipartite matrices, and quantum blowing-up
conditional on an explicit one-shot achievability witness.
Polynomial tensor-power projector approximation uses a scalar NOR witness.
The exponential strong converse assembles these results under an explicit
weak-converse witness, including specialization to operational quantum capacity.
-/

@[expose] public section

namespace QIT.Coding.Quantum

end QIT.Coding.Quantum
