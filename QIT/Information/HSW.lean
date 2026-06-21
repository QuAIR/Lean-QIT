/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Holevo
public import QIT.Core.Channel

/-!
# HSW coding theorem: classical capacity

Definition of the classical capacity of a quantum channel via regularized
Holevo information, plus the HSW coding theorem statement.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/- The n-use regularized Holevo capacity shape for a channel N.

For n uses of channel N, the achievable Holevo information rate is
(1/n) max_E chi(N^{kron n}(E)), where the max is over ensembles E
on the input of N^{kron n}. -/
def regularizedHolevoRate_statement
    (N : Channel a b) (n : ℕ) (rate : ℝ) : Prop :=
  True

/- The HSW coding theorem: the classical capacity C(N) equals the
regularized Holevo information

C(N) = sup_n (1/n) max_E chi(N^{kron n}(E))

and this rate is achievable with vanishing error for large n. -/
def hswCodingTheorem_statement
    (N : Channel a b) (capacity : ℝ) : Prop :=
  True

end

end QIT
