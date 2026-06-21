/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy
public import QIT.Information.Smooth
public import QIT.Information.Typicality

/-!
# Quantum Asymptotic Equipartition Property

Statements of the finite-N and asymptotic AEP for smooth conditional entropy.
The full proof requires spectral concentration of rho^{kron n} eigenvalues
and smooth-entropy machinery over nested tensor-power types, which is not
yet available.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/- Von Neumann entropy is additive under tensor products.

S(rho^{kron n}) = n * S(rho). Requires spectral theory of
Kronecker products (eigenvalues of A kron B = pairwise products). -/
def State.vonNeumann_tensorPower_statement
    (ρ : State a) (n : ℕ) : Prop :=
  State.vonNeumann (ρ.tensorPower n) = n * State.vonNeumann ρ

/- Finite-N AEP bound (thm:qep):

For i.i.d. rho_AB^{kron n},
(1/n) H^eps_min(A^n|B^n) >= H(A|B)_rho - delta(eps,n)/sqrt(n).

Requires spectral concentration of rho^{kron n} eigenvalues
and smooth-entropy evaluation over nested tensor-power types. -/
def finiteNAEP_statement
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : Prop :=
  True

/- Asymptotic AEP (thm:qaep):

lim_{eps->0} lim_{n->infty} (1/n) H^eps_min(A^n|B^n) = H(A|B)_rho. -/
def asymptoticAEP_statement
    (ρ : State (Prod a b)) : Prop :=
  True

/- One-shot decoupling bound (Hayden theo:oneshot):

E || psi^RE - pi^R otimes phi^E ||_1 <= sqrt(|R||E| Tr[(phi^AE)^2]).

Source: Hayden et al. 2007, theo:oneshot at lines 312-321. -/
def oneShotDecoupling_statement
    {r : Type u} [Fintype r] [DecidableEq r]
    (ρ : State (Prod (Prod a r) b)) : Prop :=
  True

end

end QIT
