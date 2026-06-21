/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.System
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Complex.Basic

/-!
# Symmetric (Bose) subspace

The symmetric subspace of `(TensorPower a n) → ℂ`, defined as the
fixed-point/invariant subspace of the natural `Equiv.Perm (Fin n)` action on
`TensorPower a n` (recursive factor-swap). Permutation invariance follows the
symmetric-subspace convention registered from [Harrow2013Symmetric,
arxiv-symmetric.tex:272-294] and [Renner2007Symmetry, sub.tex:800-825].
Schur's lemma is cited from mathlib. No asymptotics, no smooth entropy.
-/

@[expose] public section

namespace QIT

universe u

noncomputable section

variable {a : Type u} [DecidableEq a]

/-- `TensorPower a n` is canonically equivalent to `Fin n → a` (right-associated
Prod unfolds to a function on `Fin n` via `Fin.cons` head/tail decomposition). -/
def tensorPowerEquiv : (n : ℕ) → TensorPower a n ≃ (Fin n → a)
  | 0 =>
    { toFun := fun _ i => i.elim0,
      invFun := fun _ => ⟨⟩,
      left_inv := fun _ => rfl,
      right_inv := fun _ => by ext i; exact i.elim0 }
  | Nat.succ n =>
    let ih := tensorPowerEquiv n
    ((Equiv.refl a).prodCongr ih).trans
      { toFun := fun (head, tail) => Fin.cons head tail,
        invFun := fun f => (f 0, Fin.tail f),
        left_inv := by
          rintro ⟨head, tail⟩
          ext i <;> simp [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
        right_inv := by
          intro f
          ext i <;> simp [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons] }

/-- Precompose a `Fin n → a` function by permutation inverse (left action via `⁻¹`). -/
def precompPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv (Fin n → a) (Fin n → a) where
  toFun f i := f ((σ⁻¹) i)
  invFun f i := f (σ i)
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp

/-- Permutation action on `TensorPower a n` via the `Fin n → a` correspondence. -/
def permEquiv (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv (TensorPower a n) (TensorPower a n) :=
  (tensorPowerEquiv n).trans ((precompPerm n σ).trans (tensorPowerEquiv n).symm)

instance tensorPowerMulAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (TensorPower a n) where
  smul σ x := permEquiv n σ x
  one_smul x := by
    show permEquiv n 1 x = x
    unfold permEquiv precompPerm
    simp [Equiv.trans_apply, Equiv.symm_apply_apply]
  mul_smul σ τ x := by
    show permEquiv n (σ * τ) x = permEquiv n σ (permEquiv n τ x)
    unfold permEquiv precompPerm
    simp [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply, mul_inv_rev]

/-- The symmetric (Bose) subspace = vectors invariant under all permutations. -/
def symmetricSubspace (n : ℕ) : Set ((TensorPower a n) → ℂ) :=
  { f | ∀ σ : Equiv.Perm (Fin n), f ∘ permEquiv n σ = f }

/-- Membership characterization. -/
theorem mem_symmetric (n : ℕ) (f : (TensorPower a n) → ℂ) :
    f ∈ symmetricSubspace n ↔ ∀ σ : Equiv.Perm (Fin n), f ∘ permEquiv n σ = f := by
  rfl

end

end QIT
