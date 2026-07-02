/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.ConditionalTypicality
public import QIT.Coding.Classical.PackingLemma

/-!
# HSW direct-achievability bridge

This module sits after the HSW packing and conditional-typicality layers.  It
does not prove new typicality estimates; it packages a completed
`HSWPackingHypothesesSpectral` bundle into the average-error coding witness
used by the operational direct-achievability assembly.

The full HSW direct theorem still requires a source-shaped family of these
witnesses for every block-channel ensemble, including the message-size and
packing-error asymptotics.  This module proves the downstream operational
assembly and the block-channel rate-normalization transport.
[Wilde2011Qst, qit-notes.tex:33634-33808]
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

namespace TensorPower

/-- Split functions on `Fin (m+r)` into the first `m` and last `r`
coordinates.  This HSW-local name avoids depending on the higher-level
DeFinetti module for elementary tensor-word bookkeeping. -/
def finTakeDropEquiv (a : Type u) (m r : ℕ) :
    (Fin (m + r) → a) ≃ Prod (Fin m → a) (Fin r → a) where
  toFun f := (fun i => f (Fin.castAdd r i), fun j => f (Fin.natAdd m j))
  invFun g := fun i => Fin.addCases (fun j : Fin m => g.1 j) (fun j : Fin r => g.2 j) i
  left_inv := by
    intro f
    ext i
    exact Fin.addCases
      (motive := fun i =>
        Fin.addCases (fun j : Fin m => f (Fin.castAdd r j))
          (fun j : Fin r => f (Fin.natAdd m j)) i = f i)
      (fun j => by simp)
      (fun j => by simp)
      i
  right_inv := by
    intro g
    ext i <;> simp

/-- Split a recursive tensor power into a left prefix and right suffix. -/
def takeDropEquiv (a : Type u) [Fintype a] [DecidableEq a] (m r : ℕ) :
    TensorPower a (m + r) ≃ Prod (TensorPower a m) (TensorPower a r) :=
  (tensorPowerEquiv (a := a) (m + r)).trans
    ((finTakeDropEquiv a m r).trans
      (Equiv.prodCongr (tensorPowerEquiv (a := a) m).symm
        (tensorPowerEquiv (a := a) r).symm))

/-- Append a left tensor word and right tensor word into one recursive tensor
power. -/
def appendEquiv (a : Type u) [Fintype a] [DecidableEq a] (m r : ℕ) :
    Prod (TensorPower a m) (TensorPower a r) ≃ TensorPower a (m + r) :=
  (takeDropEquiv a m r).symm

/-- Flatten `t` blocks of length `k` into one tensor word of length `t * k`.

This is the type-level bookkeeping needed to turn a code for the block channel
`N^{⊗ k}` used `t` times into a code for `N` used `t * k` times.  The
coordinate order follows `finProdFinEquiv`: block index first, within-block
coordinate second. -/
def blockFlattenEquiv (a : Type u) [Fintype a] [DecidableEq a] (t k : ℕ) :
    TensorPower (TensorPower a k) t ≃ TensorPower a (t * k) :=
  (tensorPowerEquiv (a := TensorPower a k) t).trans
    ((Equiv.piCongrRight fun _ => tensorPowerEquiv (a := a) k).trans
      ((Equiv.curry (Fin t) (Fin k) a).symm.trans
        ((Equiv.arrowCongr finProdFinEquiv (Equiv.refl a)).trans
          (tensorPowerEquiv (a := a) (t * k)).symm)))

@[simp]
theorem blockFlattenEquiv_apply (a : Type u) [Fintype a] [DecidableEq a]
    (t k : ℕ) (x : TensorPower (TensorPower a k) t) (i : Fin t) (j : Fin k) :
    tensorPowerEquiv (a := a) (t * k)
        ((blockFlattenEquiv a t k) x) (finProdFinEquiv (i, j)) =
      tensorPowerEquiv (a := a) k
        (tensorPowerEquiv (a := TensorPower a k) t x i) j := by
  simp [blockFlattenEquiv]

end TensorPower

private theorem fin_prod_univ_add {M : Type _} [CommMonoid M] (n k : ℕ)
    (f : Fin (n + k) → M) :
    (∏ i : Fin (n + k), f i) =
      (∏ i : Fin n, f (Fin.castAdd k i)) *
        (∏ j : Fin k, f (Fin.natAdd n j)) := by
  calc
    (∏ i : Fin (n + k), f i) =
        ∏ s : Sum (Fin n) (Fin k), f (finSumFinEquiv s) := by
          refine (Finset.prod_equiv finSumFinEquiv ?_ ?_).symm
          · intro s
            simp
          · intro s hs
            rfl
    _ = (∏ i : Fin n, f (Fin.castAdd k i)) *
          (∏ j : Fin k, f (Fin.natAdd n j)) := by
          simp [Fintype.prod_sum_type, finSumFinEquiv_apply_left,
            finSumFinEquiv_apply_right]

private theorem fin_prod_univ_mul {M : Type _} [CommMonoid M] (t k : ℕ)
    (f : Fin (t * k) → M) :
    (∏ h : Fin (t * k), f h) = ∏ i : Fin t, ∏ j : Fin k, f (finProdFinEquiv (i, j)) := by
  calc
    (∏ h : Fin (t * k), f h) = ∏ p : Fin t × Fin k, f (finProdFinEquiv p) := by
      exact (Fintype.prod_equiv finProdFinEquiv
        (fun p : Fin t × Fin k => f (finProdFinEquiv p))
        (fun h : Fin (t * k) => f h) (by intro p; rfl)).symm
    _ = ∏ i : Fin t, ∏ j : Fin k, f (finProdFinEquiv (i, j)) := by
      rw [Fintype.prod_prod_type]

private theorem sum_prod_prod_pair {α β R : Type*} [Fintype α] [Fintype β]
    [CommSemiring R] (F : α → α → R) (G : β → β → R) :
    (∑ p : Prod α β, ∑ q : Prod α β, F p.1 q.1 * G p.2 q.2) =
      (∑ i : α, ∑ i' : α, F i i') * (∑ j : β, ∑ j' : β, G j j') := by
  simp [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

private theorem sum_prod_prod_pair_smul_complex {α β : Type*} [Fintype α] [Fintype β]
    (F A : α → α → ℂ) (G B : β → β → ℂ) :
    (∑ p : Prod α β, ∑ q : Prod α β, (F p.1 q.1 * G p.2 q.2) •
        (A p.1 q.1 * B p.2 q.2)) =
      (∑ i : α, ∑ i' : α, F i i' • A i i') *
        (∑ j : β, ∑ j' : β, G j j' • B j j') := by
  calc
    (∑ p : Prod α β, ∑ q : Prod α β, (F p.1 q.1 * G p.2 q.2) •
        (A p.1 q.1 * B p.2 q.2)) =
        ∑ p : Prod α β, ∑ q : Prod α β,
          (F p.1 q.1 * A p.1 q.1) * (G p.2 q.2 * B p.2 q.2) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp [smul_eq_mul]
      ring
    _ = (∑ i : α, ∑ i' : α, F i i' • A i i') *
        (∑ j : β, ∑ j' : β, G j j' • B j j') :=
      sum_prod_prod_pair (fun i i' : α => F i i' * A i i')
        (fun j j' : β => G j j' * B j j')

private def hswBasisState (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] :
    State α where
  matrix := Matrix.single (Classical.choice (inferInstance : Nonempty α))
    (Classical.choice (inferInstance : Nonempty α)) (1 : ℂ)
  pos := posSemidef_single (Classical.choice (inferInstance : Nonempty α))
  trace_eq_one := by
    rw [trace_single_one]
    simp

private def tensorPowerBasisState (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] :
    (n : ℕ) → State (TensorPower α n)
  | 0 => State.unit
  | n + 1 => (hswBasisState α).prod (tensorPowerBasisState α n)

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Tensor powers of a channel act coordinatewise on matrix units. -/
theorem tensorPower_map_single_apply (N : Channel a b) :
    ∀ (n : ℕ) (x y : QIT.TensorPower a n) (u v : QIT.TensorPower b n),
      (N.tensorPower n).map (Matrix.single x y (1 : Complex)) u v =
        ∏ i : Fin n,
          N.map (Matrix.single (tensorPowerEquiv (a := a) n x i)
            (tensorPowerEquiv (a := a) n y i) (1 : Complex))
              (tensorPowerEquiv (a := b) n u i) (tensorPowerEquiv (a := b) n v i) := by
  intro n
  induction n with
  | zero =>
      intro x y u v
      cases x
      cases y
      cases u
      cases v
      change (Matrix.single PUnit.unit PUnit.unit (1 : Complex)) PUnit.unit PUnit.unit = 1
      simp [Matrix.single]
  | succ n ih =>
      intro x y u v
      cases x with
      | mk x0 xs =>
      cases y with
      | mk y0 ys =>
      cases u with
      | mk u0 us =>
      cases v with
      | mk v0 vs =>
      change (N.prod (N.tensorPower n)).map
          (Matrix.single ((x0, xs) : Prod a (QIT.TensorPower a n)) (y0, ys)
            (1 : Complex)) (u0, us) (v0, vs) = _
      rw [single_prod_eq_kronecker_single x0 y0 xs ys]
      rw [Channel.prod_map_kronecker]
      change N.map (Matrix.single x0 y0 (1 : Complex)) u0 v0 *
          (N.tensorPower n).map (Matrix.single xs ys (1 : Complex)) us vs = _
      rw [ih xs ys us vs]
      rw [Fin.prod_univ_succ]
      simp [tensorPowerEquiv_succ_zero, tensorPowerEquiv_succ_succ]

/-- Matrix-unit form of the channel tensor-power append transport. -/
theorem tensorPower_append_single_apply (N : Channel a b) (m r : ℕ)
    (i i' : QIT.TensorPower a m) (j j' : QIT.TensorPower a r)
    (x y : QIT.TensorPower b (m + r)) :
    (N.tensorPower (m + r)).map
        (Matrix.single (TensorPower.appendEquiv a m r (i, j))
          (TensorPower.appendEquiv a m r (i', j')) (1 : Complex)) x y =
      (N.tensorPower m).map (Matrix.single i i' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).1) ((TensorPower.takeDropEquiv b m r y).1) *
        (N.tensorPower r).map (Matrix.single j j' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).2) ((TensorPower.takeDropEquiv b m r y).2) := by
  rw [tensorPower_map_single_apply]
  rw [fin_prod_univ_add m r]
  have hleft :
      (∏ k : Fin m,
          N.map
            (Matrix.single
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i, j)) (Fin.castAdd r k))
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i', j')) (Fin.castAdd r k))
              (1 : Complex))
            ((tensorPowerEquiv (a := b) (m + r)) x (Fin.castAdd r k))
            ((tensorPowerEquiv (a := b) (m + r)) y (Fin.castAdd r k))) =
        (N.tensorPower m).map (Matrix.single i i' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).1) ((TensorPower.takeDropEquiv b m r y).1) := by
    rw [tensorPower_map_single_apply]
    apply Finset.prod_congr rfl
    intro k hk
    simp [TensorPower.appendEquiv, TensorPower.takeDropEquiv, TensorPower.finTakeDropEquiv]
  have hright :
      (∏ k : Fin r,
          N.map
            (Matrix.single
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i, j)) (Fin.natAdd m k))
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i', j')) (Fin.natAdd m k))
              (1 : Complex))
            ((tensorPowerEquiv (a := b) (m + r)) x (Fin.natAdd m k))
            ((tensorPowerEquiv (a := b) (m + r)) y (Fin.natAdd m k))) =
        (N.tensorPower r).map (Matrix.single j j' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).2) ((TensorPower.takeDropEquiv b m r y).2) := by
    rw [tensorPower_map_single_apply]
    apply Finset.prod_congr rfl
    intro k hk
    simp [TensorPower.appendEquiv, TensorPower.takeDropEquiv, TensorPower.finTakeDropEquiv]
  rw [hleft, hright]

/-- General matrix form of the channel tensor-power append transport. -/
theorem tensorPower_append_map_kronecker_apply (N : Channel a b) (m r : ℕ)
    (X : CMatrix (QIT.TensorPower a m)) (Y : CMatrix (QIT.TensorPower a r))
    (x y : QIT.TensorPower b (m + r)) :
    (N.tensorPower (m + r)).map
        ((Matrix.kronecker X Y).submatrix (TensorPower.appendEquiv a m r).symm
          (TensorPower.appendEquiv a m r).symm) x y =
      (Matrix.kronecker ((N.tensorPower m).map X) ((N.tensorPower r).map Y)).submatrix
        (TensorPower.appendEquiv b m r).symm (TensorPower.appendEquiv b m r).symm x y := by
  rw [MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp only [Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [MatrixMap.map_eq_sum_single (N.tensorPower m).map X]
  rw [MatrixMap.map_eq_sum_single (N.tensorPower r).map Y]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  change _ =
    (∑ x₁ : QIT.TensorPower a m, ∑ x₂ : QIT.TensorPower a m,
        X x₁ x₂ •
          (N.tensorPower m).map (Matrix.single x₁ x₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).1)
            ((TensorPower.takeDropEquiv b m r y).1) : Complex) *
      ∑ y₁ : QIT.TensorPower a r, ∑ y₂ : QIT.TensorPower a r,
        Y y₁ y₂ •
          (N.tensorPower r).map (Matrix.single y₁ y₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).2)
            ((TensorPower.takeDropEquiv b m r y).2)
  calc
    (∑ x₁ : QIT.TensorPower a (m + r),
      ∑ x₂ : QIT.TensorPower a (m + r),
        (X ((TensorPower.appendEquiv a m r).symm x₁).1
            ((TensorPower.appendEquiv a m r).symm x₂).1 *
          Y ((TensorPower.appendEquiv a m r).symm x₁).2
            ((TensorPower.appendEquiv a m r).symm x₂).2) •
          (N.tensorPower (m + r)).map (Matrix.single x₁ x₂ (1 : Complex)) x y) =
        ∑ p : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
          ∑ q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
            (X p.1 q.1 * Y p.2 q.2) •
              (N.tensorPower (m + r)).map
                (Matrix.single (TensorPower.appendEquiv a m r p)
                  (TensorPower.appendEquiv a m r q) (1 : Complex)) x y := by
      exact (Fintype.sum_equiv (TensorPower.appendEquiv a m r)
        (fun p : Prod (QIT.TensorPower a m) (QIT.TensorPower a r) =>
          ∑ q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
            (X p.1 q.1 * Y p.2 q.2) •
              (N.tensorPower (m + r)).map
                (Matrix.single (TensorPower.appendEquiv a m r p)
                  (TensorPower.appendEquiv a m r q) (1 : Complex)) x y)
        (fun z : QIT.TensorPower a (m + r) =>
          ∑ w : QIT.TensorPower a (m + r),
            (X ((TensorPower.appendEquiv a m r).symm z).1
                ((TensorPower.appendEquiv a m r).symm w).1 *
              Y ((TensorPower.appendEquiv a m r).symm z).2
                ((TensorPower.appendEquiv a m r).symm w).2) •
              (N.tensorPower (m + r)).map (Matrix.single z w (1 : Complex)) x y)
        (by
          intro p
          exact Fintype.sum_equiv (TensorPower.appendEquiv a m r)
            (fun q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r) =>
              (X p.1 q.1 * Y p.2 q.2) •
                (N.tensorPower (m + r)).map
                  (Matrix.single (TensorPower.appendEquiv a m r p)
                    (TensorPower.appendEquiv a m r q) (1 : Complex)) x y)
            (fun w : QIT.TensorPower a (m + r) =>
              (X ((TensorPower.appendEquiv a m r).symm
                    (TensorPower.appendEquiv a m r p)).1
                  ((TensorPower.appendEquiv a m r).symm w).1 *
                Y ((TensorPower.appendEquiv a m r).symm
                    (TensorPower.appendEquiv a m r p)).2
                  ((TensorPower.appendEquiv a m r).symm w).2) •
                (N.tensorPower (m + r)).map
                  (Matrix.single (TensorPower.appendEquiv a m r p) w (1 : Complex)) x y)
            (by intro q; simp))).symm
    _ = ∑ p : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
          ∑ q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
            (X p.1 q.1 * Y p.2 q.2) •
              ((N.tensorPower m).map (Matrix.single p.1 q.1 (1 : Complex))
                  ((TensorPower.takeDropEquiv b m r x).1)
                  ((TensorPower.takeDropEquiv b m r y).1) *
                (N.tensorPower r).map (Matrix.single p.2 q.2 (1 : Complex))
                  ((TensorPower.takeDropEquiv b m r x).2)
                  ((TensorPower.takeDropEquiv b m r y).2)) := by
      simp_rw [tensorPower_append_single_apply N]
    _ = (∑ x₁ : QIT.TensorPower a m, ∑ x₂ : QIT.TensorPower a m,
        X x₁ x₂ •
          (N.tensorPower m).map (Matrix.single x₁ x₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).1)
            ((TensorPower.takeDropEquiv b m r y).1) : Complex) *
      ∑ y₁ : QIT.TensorPower a r, ∑ y₂ : QIT.TensorPower a r,
        Y y₁ y₂ •
          (N.tensorPower r).map (Matrix.single y₁ y₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).2)
            ((TensorPower.takeDropEquiv b m r y).2) := by
      let A : QIT.TensorPower a m → QIT.TensorPower a m → Complex := fun i i' =>
        (N.tensorPower m).map (Matrix.single i i' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).1) ((TensorPower.takeDropEquiv b m r y).1)
      let B : QIT.TensorPower a r → QIT.TensorPower a r → Complex := fun j j' =>
        (N.tensorPower r).map (Matrix.single j j' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).2) ((TensorPower.takeDropEquiv b m r y).2)
      exact sum_prod_prod_pair_smul_complex
        (fun i i' : QIT.TensorPower a m => X i i')
        (fun i i' : QIT.TensorPower a m => A i i')
        (fun j j' : QIT.TensorPower a r => Y j j')
        (fun j j' : QIT.TensorPower a r => B j j')

/-- State form of the channel tensor-power append transport. -/
theorem tensorPower_append_applyState_prod (N : Channel a b) (m r : ℕ)
    (ρ : State (QIT.TensorPower a m)) (σ : State (QIT.TensorPower a r)) :
    (N.tensorPower (m + r)).applyState
        ((ρ.prod σ).reindex (TensorPower.appendEquiv a m r)) =
      (((N.tensorPower m).applyState ρ).prod
        ((N.tensorPower r).applyState σ)).reindex (TensorPower.appendEquiv b m r) := by
  apply State.ext
  ext x y
  change (N.tensorPower (m + r)).map
      ((Matrix.kronecker ρ.matrix σ.matrix).submatrix
        (TensorPower.appendEquiv a m r).symm (TensorPower.appendEquiv a m r).symm) x y =
    (Matrix.kronecker ((N.tensorPower m).map ρ.matrix)
      ((N.tensorPower r).map σ.matrix)).submatrix
        (TensorPower.appendEquiv b m r).symm (TensorPower.appendEquiv b m r).symm x y
  exact tensorPower_append_map_kronecker_apply N m r ρ.matrix σ.matrix x y

/-- Tensor powers of a memoryless channel act coordinatewise on product states. -/
theorem tensorPower_applyState_productState (N : Channel a b) :
    ∀ (n : ℕ) (states : Fin n → State a),
      (N.tensorPower n).applyState (productState states) =
        productState (fun i => N.applyState (states i))
  | 0, states => by
      apply State.ext
      ext x y
      cases x
      cases y
      rfl
  | n + 1, states => by
      rw [Channel.tensorPower_succ]
      conv_lhs => rw [productState_succ]
      conv_rhs => rw [productState_succ]
      have hprod :
          (N.prod (N.tensorPower n)).applyState
              ((states 0).prod (productState fun i : Fin n => states i.succ)) =
          (N.applyState (states 0)).prod
              ((N.tensorPower n).applyState
                (productState fun i : Fin n => states i.succ)) :=
        Channel.applyState_prod N (N.tensorPower n)
          (states 0) (productState fun i : Fin n => states i.succ)
      change
        (N.prod (N.tensorPower n)).applyState
            ((states 0).prod (productState fun i : Fin n => states i.succ)) =
          (N.applyState (states 0)).prod
            (productState fun i : Fin n => N.applyState (states i.succ))
      rw [hprod]
      rw [tensorPower_applyState_productState N n (states ·.succ)]

/-- Matrix-unit form of block-flatten transport for recursive tensor powers. -/
theorem tensorPower_blockFlatten_single_apply (N : Channel a b) (t k : ℕ)
    (i i' : QIT.TensorPower (QIT.TensorPower a k) t)
    (x y : QIT.TensorPower b (t * k)) :
    (N.tensorPower (t * k)).map
        (Matrix.single (TensorPower.blockFlattenEquiv a t k i)
          (TensorPower.blockFlattenEquiv a t k i') (1 : Complex)) x y =
      (((N.tensorPower k).tensorPower t).map (Matrix.single i i' (1 : Complex))
        ((TensorPower.blockFlattenEquiv b t k).symm x)
        ((TensorPower.blockFlattenEquiv b t k).symm y)) := by
  rw [tensorPower_map_single_apply]
  rw [tensorPower_map_single_apply]
  rw [fin_prod_univ_mul t k]
  apply Finset.prod_congr rfl
  intro ib hib
  rw [tensorPower_map_single_apply]
  apply Finset.prod_congr rfl
  intro jb hjb
  have hxin := TensorPower.blockFlattenEquiv_apply (a := a) t k i ib jb
  have hyin := TensorPower.blockFlattenEquiv_apply (a := a) t k i' ib jb
  have hxout := TensorPower.blockFlattenEquiv_apply (a := b) t k
    ((TensorPower.blockFlattenEquiv b t k).symm x) ib jb
  have hyout := TensorPower.blockFlattenEquiv_apply (a := b) t k
    ((TensorPower.blockFlattenEquiv b t k).symm y) ib jb
  simp at hxout hyout
  rw [← hxin, ← hyin, hxout, hyout]

/-- General matrix form of block-flatten transport for recursive tensor powers. -/
theorem tensorPower_blockFlatten_map_apply (N : Channel a b) (t k : ℕ)
    (X : CMatrix (QIT.TensorPower (QIT.TensorPower a k) t))
    (x y : QIT.TensorPower b (t * k)) :
    (N.tensorPower (t * k)).map
        (X.submatrix (TensorPower.blockFlattenEquiv a t k).symm
          (TensorPower.blockFlattenEquiv a t k).symm) x y =
      (((N.tensorPower k).tensorPower t).map X).submatrix
        (TensorPower.blockFlattenEquiv b t k).symm
        (TensorPower.blockFlattenEquiv b t k).symm x y := by
  rw [MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [MatrixMap.map_eq_sum_single ((N.tensorPower k).tensorPower t).map X]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]
  calc
    (∑ x₁ : QIT.TensorPower a (t * k), ∑ x₂ : QIT.TensorPower a (t * k),
        X ((TensorPower.blockFlattenEquiv a t k).symm x₁)
            ((TensorPower.blockFlattenEquiv a t k).symm x₂) •
          (N.tensorPower (t * k)).map (Matrix.single x₁ x₂ (1 : Complex)) x y) =
        ∑ p : QIT.TensorPower (QIT.TensorPower a k) t,
          ∑ q : QIT.TensorPower (QIT.TensorPower a k) t,
            X p q •
              (N.tensorPower (t * k)).map
                (Matrix.single (TensorPower.blockFlattenEquiv a t k p)
                  (TensorPower.blockFlattenEquiv a t k q) (1 : Complex)) x y := by
      exact (Fintype.sum_equiv (TensorPower.blockFlattenEquiv a t k)
        (fun p : QIT.TensorPower (QIT.TensorPower a k) t =>
          ∑ q : QIT.TensorPower (QIT.TensorPower a k) t,
            X p q •
              (N.tensorPower (t * k)).map
                (Matrix.single (TensorPower.blockFlattenEquiv a t k p)
                  (TensorPower.blockFlattenEquiv a t k q) (1 : Complex)) x y)
        (fun z : QIT.TensorPower a (t * k) =>
          ∑ w : QIT.TensorPower a (t * k),
            X ((TensorPower.blockFlattenEquiv a t k).symm z)
              ((TensorPower.blockFlattenEquiv a t k).symm w) •
              (N.tensorPower (t * k)).map (Matrix.single z w (1 : Complex)) x y)
        (by
          intro p
          exact Fintype.sum_equiv (TensorPower.blockFlattenEquiv a t k)
            (fun q : QIT.TensorPower (QIT.TensorPower a k) t =>
              X p q •
                (N.tensorPower (t * k)).map
                  (Matrix.single (TensorPower.blockFlattenEquiv a t k p)
                    (TensorPower.blockFlattenEquiv a t k q) (1 : Complex)) x y)
            (fun w : QIT.TensorPower a (t * k) =>
              X ((TensorPower.blockFlattenEquiv a t k).symm
                    (TensorPower.blockFlattenEquiv a t k p))
                ((TensorPower.blockFlattenEquiv a t k).symm w) •
                (N.tensorPower (t * k)).map
                  (Matrix.single (TensorPower.blockFlattenEquiv a t k p) w
                    (1 : Complex)) x y)
            (by intro q; simp))).symm
    _ = ∑ p : QIT.TensorPower (QIT.TensorPower a k) t,
          ∑ q : QIT.TensorPower (QIT.TensorPower a k) t,
            X p q •
              (((N.tensorPower k).tensorPower t).map (Matrix.single p q (1 : Complex))
                ((TensorPower.blockFlattenEquiv b t k).symm x)
                ((TensorPower.blockFlattenEquiv b t k).symm y)) := by
      simp_rw [tensorPower_blockFlatten_single_apply N]

/-- State form of block-flatten transport for recursive tensor powers. -/
theorem tensorPower_blockFlatten_applyState (N : Channel a b) (t k : ℕ)
    (ρ : State (QIT.TensorPower (QIT.TensorPower a k) t)) :
    (N.tensorPower (t * k)).applyState
        (ρ.reindex (TensorPower.blockFlattenEquiv a t k)) =
      (((N.tensorPower k).tensorPower t).applyState ρ).reindex
        (TensorPower.blockFlattenEquiv b t k) := by
  apply State.ext
  ext x y
  change (N.tensorPower (t * k)).map
      (ρ.matrix.submatrix (TensorPower.blockFlattenEquiv a t k).symm
        (TensorPower.blockFlattenEquiv a t k).symm) x y =
    (((N.tensorPower k).tensorPower t).map ρ.matrix).submatrix
      (TensorPower.blockFlattenEquiv b t k).symm
      (TensorPower.blockFlattenEquiv b t k).symm x y
  exact tensorPower_blockFlatten_map_apply N t k ρ.matrix x y

end Channel

namespace hswMessageRate

theorem nonneg {M : Type u} [Fintype M] [Nonempty M] (n : ℕ) :
    0 ≤ hswMessageRate M n := by
  by_cases hn : n = 0
  · simp [hswMessageRate, hn]
  · have hcard_pos_nat : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
    have hcard_one : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by exact_mod_cast hcard_pos_nat
    have hlog_nonneg : 0 ≤ log2 (Fintype.card M : ℝ) := by
      unfold log2
      exact div_nonneg (Real.log_nonneg hcard_one)
        (le_of_lt (Real.log_pos one_lt_two))
    unfold hswMessageRate
    rw [if_neg hn]
    exact div_nonneg hlog_nonneg (Nat.cast_nonneg n)

theorem block_pad_eq
    {M : Type u} [Fintype M] {t k r : ℕ} (ht : 0 < t) (hk : 0 < k) :
    hswMessageRate M (t * k + r) =
      (hswMessageRate M t / (k : ℝ)) *
        (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := by
  have ht_ne : t ≠ 0 := Nat.ne_of_gt ht
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have htk_pos : 0 < t * k := Nat.mul_pos ht hk
  have hsum_pos : 0 < t * k + r := Nat.add_pos_left htk_pos r
  have hsum_ne : t * k + r ≠ 0 := Nat.ne_of_gt hsum_pos
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum_pos_real : (0 : ℝ) < t * k + r := by exact_mod_cast hsum_pos
  unfold hswMessageRate
  rw [if_neg hsum_ne, if_neg ht_ne]
  rw [Nat.cast_add, Nat.cast_mul]
  field_simp [ne_of_gt ht_pos, ne_of_gt hk_pos, ne_of_gt hsum_pos_real]

theorem block_pad_ge_of_ratio
    {M : Type u} [Fintype M] {t k r : ℕ} {A B : ℝ}
    (ht : 0 < t) (hk : 0 < k)
    (hbase : A ≤ hswMessageRate M t / (k : ℝ))
    (hratio : B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ))) :
    B ≤ hswMessageRate M (t * k + r) := by
  have hratio_nonneg :
      0 ≤ (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := hratio
    _ ≤ (hswMessageRate M t / (k : ℝ)) *
          (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hbase hratio_nonneg
    _ = hswMessageRate M (t * k + r) := by
        rw [block_pad_eq (M := M) ht hk]

private theorem rpow_two_log2_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hx
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  unfold log2
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

/-- The operational message rate exactly exponentiates back to the message
cardinality for positive block lengths. -/
theorem rpow_two_mul_rate_eq_card
    {M : Type u} [Fintype M] [Nonempty M] {n : ℕ} (hn : 0 < n) :
    Real.rpow 2 ((n : ℝ) * hswMessageRate M n) = (Fintype.card M : ℝ) := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard_pos : (0 : ℝ) < Fintype.card M := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold hswMessageRate
  rw [if_neg hn_ne]
  have hmul :
      (n : ℝ) * (log2 (Fintype.card M : ℝ) / (n : ℝ)) =
        log2 (Fintype.card M : ℝ) := by
    field_simp [ne_of_gt hn_pos]
  rw [hmul]
  exact rpow_two_log2_pos hcard_pos

/-- The cross-codeword cardinality factor is bounded by the exponential of the
HSW message rate. -/
theorem card_sub_one_le_rpow_two_mul_rate
    {M : Type u} [Fintype M] [Nonempty M] {n : ℕ} (hn : 0 < n) :
    (Fintype.card M : ℝ) - 1 ≤ Real.rpow 2 ((n : ℝ) * hswMessageRate M n) := by
  rw [rpow_two_mul_rate_eq_card (M := M) hn]
  linarith

/-- Choose a finite nonempty message type whose `n`-use HSW message rate is at
least any prescribed real value.

The construction uses `Fin (max 1 ⌈2^(nR)⌉)`.  This lemma is deliberately
rate-only: the HSW packing-error side condition still has to be discharged from
the separate typical-estimate exponents. -/
theorem exists_finite_message_type_rate_ge {n : ℕ} (hn : 0 < n) (R : ℝ) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      R ≤ hswMessageRate M n := by
  let m : ℕ := max 1 (Nat.ceil (Real.rpow 2 ((n : ℝ) * R)))
  have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hceil_le_m : Nat.ceil (Real.rpow 2 ((n : ℝ) * R)) ≤ m := Nat.le_max_right 1 _
  have hpow_le_m : Real.rpow 2 ((n : ℝ) * R) ≤ (m : ℝ) := by
    exact (Nat.le_ceil (Real.rpow 2 ((n : ℝ) * R))).trans
      (by exact_mod_cast hceil_le_m)
  refine ⟨ULift.{u} (Fin m), inferInstance, inferInstance, ?_, ?_⟩
  · exact ⟨ULift.up ⟨0, hm_pos⟩⟩
  · have hcard : Real.rpow 2 ((n : ℝ) * R) ≤
        (Fintype.card (ULift.{u} (Fin m)) : ℝ) := by
      simpa using hpow_le_m
    exact lowerBound_le_of_rpow_two_mul_le_card (M := ULift.{u} (Fin m)) hn hcard

/-- Choose a finite nonempty message type whose rate is at least `R` while the
cross-codeword cardinality factor is at most `2^(nR)`.

This is the rate/cardinality accounting used in the HSW direct proof after the
packing-error exponent is separated from the code construction. -/
theorem exists_finite_message_type_rate_ge_card_sub_one_le
    {n : ℕ} (hn : 0 < n) (R : ℝ) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      R ≤ hswMessageRate M n ∧
        (Fintype.card M : ℝ) - 1 ≤ Real.rpow 2 ((n : ℝ) * R) := by
  let x : ℝ := Real.rpow 2 ((n : ℝ) * R)
  let m : ℕ := max 1 (Nat.ceil x)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hceil_le_m : Nat.ceil x ≤ m := Nat.le_max_right 1 _
  have hx_le_m : x ≤ (m : ℝ) := by
    exact (Nat.le_ceil x).trans (by exact_mod_cast hceil_le_m)
  have hm_sub_le : (m : ℝ) - 1 ≤ x := by
    by_cases hceil_le_one : Nat.ceil x ≤ 1
    · have hm_eq : m = 1 := by
        dsimp [m]
        exact max_eq_left hceil_le_one
      rw [hm_eq]
      norm_num
      exact hx_pos.le
    · have hceil_one_le : 1 ≤ Nat.ceil x := (Nat.lt_of_not_ge hceil_le_one).le
      have hm_eq : m = Nat.ceil x := by
        dsimp [m]
        exact max_eq_right hceil_one_le
      have hceil_lt : (Nat.ceil x : ℝ) < x + 1 :=
        Nat.ceil_lt_add_one (le_of_lt hx_pos)
      rw [hm_eq]
      linarith
  refine ⟨ULift.{u} (Fin m), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact ⟨ULift.up ⟨0, hm_pos⟩⟩
  · have hcard : Real.rpow 2 ((n : ℝ) * R) ≤
        (Fintype.card (ULift.{u} (Fin m)) : ℝ) := by
      simpa [x] using hx_le_m
    exact lowerBound_le_of_rpow_two_mul_le_card (M := ULift.{u} (Fin m)) hn hcard
  · simpa [x] using hm_sub_le

end hswMessageRate

/-- Combine the two HSW packing-error terms after the message-cardinality
factor has been bounded by an exponential rate estimate. -/
theorem hswPackingError_le_of_rate_cross_bound
    {M : Type u} [Fintype M] {n : ℕ} {R ratio packingε ε : ℝ}
    (hcard : (Fintype.card M : ℝ) - 1 ≤ Real.rpow 2 ((n : ℝ) * R))
    (hratio : 0 ≤ ratio)
    (hself : 2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4)
    (hcross : 4 * Real.rpow 2 ((n : ℝ) * R) * ratio ≤ ε / 4) :
    2 * (packingε + 2 * Real.sqrt packingε) +
        4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 2 := by
  have hcard_mul :
      ((Fintype.card M : ℝ) - 1) * ratio ≤
        Real.rpow 2 ((n : ℝ) * R) * ratio :=
    mul_le_mul_of_nonneg_right hcard hratio
  have hcross' :
      4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 4 := by
    calc
      4 * ((Fintype.card M : ℝ) - 1) * ratio
          = 4 * (((Fintype.card M : ℝ) - 1) * ratio) := by ring
      _ ≤ 4 * (Real.rpow 2 ((n : ℝ) * R) * ratio) :=
          mul_le_mul_of_nonneg_left hcard_mul (by norm_num)
      _ = 4 * Real.rpow 2 ((n : ℝ) * R) * ratio := by ring
      _ ≤ ε / 4 := hcross
  linarith

/-- Combine the two HSW packing-error terms after they have been bounded
separately.  This is the local numerical bridge used before the cross term is
eventually discharged from an exponential rate estimate. -/
theorem hswPackingError_le_of_self_cross_bound
    {M : Type u} [Fintype M] {ratio packingε ε : ℝ}
    (hself : 2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4)
    (hcross : 4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 4) :
    2 * (packingε + 2 * Real.sqrt packingε) +
        4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 2 := by
  linarith

/-- A concrete small packing-error parameter for the HSW self-error term.

The minimum keeps both `η ≤ ε/32` and `sqrt η ≤ ε/32`, uniformly for all
positive error tolerances. -/
noncomputable def hswSelfPackingEpsilon (ε : ℝ) : ℝ :=
  min (ε / 32) ((ε / 32) ^ 2)

theorem hswSelfPackingEpsilon_pos {ε : ℝ} (hε : 0 < ε) :
    0 < hswSelfPackingEpsilon ε := by
  dsimp [hswSelfPackingEpsilon]
  exact lt_min (by positivity) (sq_pos_of_pos (by positivity))

theorem hswSelfPackingEpsilon_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ hswSelfPackingEpsilon ε :=
  (hswSelfPackingEpsilon_pos hε).le

theorem hswSelfPackingEpsilon_self_bound {ε : ℝ} (hε : 0 < ε) :
    2 * (hswSelfPackingEpsilon ε + 2 * Real.sqrt (hswSelfPackingEpsilon ε))
        ≤ ε / 4 := by
  have hlinear : hswSelfPackingEpsilon ε ≤ ε / 32 := by
    dsimp [hswSelfPackingEpsilon]
    exact min_le_left _ _
  have hsquare : hswSelfPackingEpsilon ε ≤ (ε / 32) ^ 2 := by
    dsimp [hswSelfPackingEpsilon]
    exact min_le_right _ _
  have hε32_nonneg : 0 ≤ ε / 32 := by positivity
  have hsqrt :
      Real.sqrt (hswSelfPackingEpsilon ε) ≤ ε / 32 := by
    have hs := Real.sqrt_le_sqrt hsquare
    have hsimp : Real.sqrt ((ε / 32) ^ 2) = ε / 32 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hε32_nonneg]
    simpa [hsimp] using hs
  nlinarith

/-- Eventually, an inverse-linear Chebyshev-style ratio is below any positive
threshold.  The denominator is written as `n * δ²` to match the HSW packing
estimates. -/
theorem exists_nat_real_div_mul_sq_le {C η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 → C / ((n : ℝ) * δ ^ 2) ≤ η := by
  let X : ℝ := C / (η * δ ^ 2)
  refine ⟨max 1 (Nat.ceil X), ?_⟩
  intro n hn
  have hceil_le_n : Nat.ceil X ≤ n := (Nat.le_max_right 1 (Nat.ceil X)).trans hn
  have hX_le_n : X ≤ (n : ℝ) :=
    (Nat.le_ceil X).trans (by exact_mod_cast hceil_le_n)
  have hn_one : 1 ≤ n := (Nat.le_max_left 1 (Nat.ceil X)).trans hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_one
  have hδ2_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hcoef_pos : 0 < η * δ ^ 2 := mul_pos hη hδ2_pos
  have hC_le : C ≤ (n : ℝ) * (η * δ ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hX_le_n hcoef_pos.le
    have hX_mul : X * (η * δ ^ 2) = C := by
      dsimp [X]
      field_simp [ne_of_gt hcoef_pos]
    calc
      C = X * (η * δ ^ 2) := hX_mul.symm
      _ ≤ (n : ℝ) * (η * δ ^ 2) := hmul
  have hden_pos : 0 < (n : ℝ) * δ ^ 2 := mul_pos hn_pos hδ2_pos
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- A constant multiple of a nonnegative geometric sequence with ratio below
one is eventually below every positive threshold. -/
theorem exists_nat_const_mul_pow_le {A q η : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 → A * q ^ n ≤ η := by
  by_cases hA : A ≤ 0
  · refine ⟨0, ?_⟩
    intro n _hn
    have hpow_nonneg : 0 ≤ q ^ n := pow_nonneg hq_nonneg n
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hA hpow_nonneg) hη.le
  · have htend :
        Filter.Tendsto (fun n : ℕ => A * q ^ n) Filter.atTop (nhds (A * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one)
    rw [mul_zero] at htend
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (htend.eventually (Iio_mem_nhds hη))
    exact ⟨N0, fun n hn => le_of_lt (hN0 n hn)⟩

/-- Exponential base-two decay in blocklength is eventually below every
positive threshold. -/
theorem exists_nat_const_mul_rpow_two_neg_mul_le {A c η : ℝ}
    (hc : 0 < c) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      A * Real.rpow 2 (-(n : ℝ) * c) ≤ η := by
  let q : ℝ := Real.rpow 2 (-c)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-c)
  have hq_lt_one : q < 1 := by
    have hlt : -c < (0 : ℝ) := by linarith
    have hpow_lt :
        Real.rpow 2 (-c) < Real.rpow 2 (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlt
    simpa using hpow_lt
  obtain ⟨N0, hN0⟩ := exists_nat_const_mul_pow_le (A := A) (q := q) (η := η)
    hq_pos.le hq_lt_one hη
  refine ⟨N0, ?_⟩
  intro n hn
  have hpow :
      q ^ n = Real.rpow 2 (-(n : ℝ) * c) := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  simpa [hpow] using hN0 n hn

/-- Positive slacks can make a finite nonnegative linear error budget
arbitrarily small.  This is the elementary "choose the typicality windows
small enough" step used in the HSW cross-exponent bookkeeping. -/
theorem exists_pos_pair_linear_slack {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ y + x * A + B * (x + y) ≤ δ / 4 := by
  let C : ℝ := 1 + A + B
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith
  let x : ℝ := δ / (16 * C)
  let y : ℝ := δ / (16 * C)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact div_pos hδ (mul_pos (by norm_num) hC_pos)
  have hy_pos : 0 < y := by
    dsimp [y]
    exact div_pos hδ (mul_pos (by norm_num) hC_pos)
  have hC_ge_one : 1 ≤ C := by
    dsimp [C]
    nlinarith
  have hA_le_C : A ≤ C := by
    dsimp [C]
    nlinarith
  have hB_le_C : B ≤ C := by
    dsimp [C]
    nlinarith
  have hxC : x * C = δ / 16 := by
    dsimp [x]
    field_simp [ne_of_gt hC_pos]
  have hyC : y * C = δ / 16 := by
    dsimp [y]
    field_simp [ne_of_gt hC_pos]
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hy_le : y ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_left hC_ge_one hy_nonneg
    simpa [mul_one, hyC] using h
  have hxA_le : x * A ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_left hA_le_C hx_nonneg
    simpa [hxC] using h
  have hBx_le : B * x ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_right hB_le_C hx_nonneg
    have hCx : C * x = δ / 16 := by simpa [mul_comm] using hxC
    simpa [hCx] using h
  have hBy_le : B * y ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_right hB_le_C hy_nonneg
    have hCy : C * y = δ / 16 := by simpa [mul_comm] using hyC
    simpa [hCy] using h
  refine ⟨x, y, hx_pos, hy_pos, ?_⟩
  have hsplit : B * (x + y) = B * x + B * y := by ring
  rw [hsplit]
  nlinarith

/-- The HSW cross term has a strictly negative exponent once the conditional
dimension slack and source-projector mass slack are chosen below a quarter of
the Holevo-rate gap. -/
theorem hsw_crossExponent_rpow_bound {n : ℕ} {χ avg cond ex ey δ : ℝ}
    (hχ : χ = avg - cond) (hslack : ex + ey ≤ δ / 4) :
    4 * Real.rpow 2 ((n : ℝ) * (χ - δ / 2)) *
          (Real.rpow 2 ((n : ℝ) * (cond + ex)) /
            ((1 - (1 / 2 : ℝ)) *
              Real.rpow 2 ((n : ℝ) * avg - (n : ℝ) * ey))) ≤
        8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) := by
  let e₁ : ℝ := (n : ℝ) * (χ - δ / 2)
  let e₂ : ℝ := (n : ℝ) * (cond + ex)
  let e₃ : ℝ := (n : ℝ) * avg - (n : ℝ) * ey
  have htwo_pos : 0 < (2 : ℝ) := by norm_num
  have hpow_pos : 0 < Real.rpow 2 e₃ := Real.rpow_pos_of_pos htwo_pos e₃
  have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
  have hdiv_half :
      Real.rpow 2 e₂ / ((1 - (1 / 2 : ℝ)) * Real.rpow 2 e₃) =
        2 * (Real.rpow 2 e₂ / Real.rpow 2 e₃) := by
    rw [hhalf]
    field_simp [ne_of_gt hpow_pos]
  have hpow_combine :
      Real.rpow 2 e₁ * (Real.rpow 2 e₂ / Real.rpow 2 e₃) =
        Real.rpow 2 (e₁ + e₂ - e₃) := by
    rw [div_eq_mul_inv]
    have hinv : (Real.rpow 2 e₃)⁻¹ = Real.rpow 2 (-e₃) :=
      (Real.rpow_neg htwo_pos.le e₃).symm
    rw [hinv]
    rw [← mul_assoc]
    have h12 :
        Real.rpow 2 e₁ * Real.rpow 2 e₂ = Real.rpow 2 (e₁ + e₂) :=
      (Real.rpow_add htwo_pos e₁ e₂).symm
    rw [h12]
    have h123 :
        Real.rpow 2 (e₁ + e₂) * Real.rpow 2 (-e₃) =
          Real.rpow 2 ((e₁ + e₂) + (-e₃)) :=
      (Real.rpow_add htwo_pos (e₁ + e₂) (-e₃)).symm
    rw [h123]
    ring_nf
  have hexp_eq : e₁ + e₂ - e₃ = (n : ℝ) * (ex + ey - δ / 2) := by
    dsimp [e₁, e₂, e₃]
    rw [hχ]
    ring
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hexp_le : e₁ + e₂ - e₃ ≤ -(n : ℝ) * (δ / 4) := by
    rw [hexp_eq]
    nlinarith [mul_le_mul_of_nonneg_left hslack hn_nonneg]
  have hpow_le :
      Real.rpow 2 (e₁ + e₂ - e₃) ≤ Real.rpow 2 (-(n : ℝ) * (δ / 4)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_le
  calc
    4 * Real.rpow 2 ((n : ℝ) * (χ - δ / 2)) *
          (Real.rpow 2 ((n : ℝ) * (cond + ex)) /
            ((1 - (1 / 2 : ℝ)) *
              Real.rpow 2 ((n : ℝ) * avg - (n : ℝ) * ey)))
        = 8 * Real.rpow 2 (e₁ + e₂ - e₃) := by
          change
            4 * Real.rpow 2 e₁ *
                (Real.rpow 2 e₂ / ((1 - (1 / 2 : ℝ)) * Real.rpow 2 e₃)) =
              8 * Real.rpow 2 (e₁ + e₂ - e₃)
          rw [hdiv_half]
          rw [show (4 : ℝ) * Real.rpow 2 e₁ *
                (2 * (Real.rpow 2 e₂ / Real.rpow 2 e₃)) =
              8 * (Real.rpow 2 e₁ * (Real.rpow 2 e₂ / Real.rpow 2 e₃)) by ring]
          rw [hpow_combine]
    _ ≤ 8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) :=
        mul_le_mul_of_nonneg_left hpow_le (by norm_num)

/-- Concrete HSW cross-exponent bound for an output ensemble.  The slack
budget is exactly the sum of the conditionally-typical dimension slack and the
source-projector product-mass slack. -/
theorem hsw_crossExponentBound_of_typicalitySlack
    {ι : Type u} {out : Type v} [Fintype ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (n : ℕ) (δ δx δc : ℝ)
    (hslack :
      δc + δx * ∑ x, |(E.states x).vonNeumann| +
          ((Fintype.card ι : ℝ) * (δx + δc)) *
            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
              E.averageState).logTypicalitySlack ≤
        δ / 4) :
    4 * Real.rpow 2 ((n : ℝ) * (E.holevoInformation - δ / 2)) *
          (E.strongTypicalDimensionEnvelope n δx δc /
            ((1 - (1 / 2 : ℝ)) *
              QIT.FiniteDistribution.strongTypicalMassScale
                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution E.averageState)
                n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
        8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) := by
  let avg : ℝ := E.averageState.vonNeumann
  let cond : ℝ := ∑ x, (E.probs x : ℝ) * (E.states x).vonNeumann
  let ex : ℝ := δc + δx * ∑ x, |(E.states x).vonNeumann|
  let ey : ℝ :=
    ((Fintype.card ι : ℝ) * (δx + δc)) *
      (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
        E.averageState).logTypicalitySlack
  have hχ : E.holevoInformation = avg - cond := by
    dsimp [avg, cond]
    rw [Ensemble.holevoInformation_def]
  have hslack' : ex + ey ≤ δ / 4 := by
    dsimp [ex, ey]
    simpa [add_assoc] using hslack
  have h :=
    hsw_crossExponent_rpow_bound (n := n) (χ := E.holevoInformation) (avg := avg)
      (cond := cond) (ex := ex) (ey := ey) (δ := δ) hχ hslack'
  simpa [Ensemble.strongTypicalDimensionEnvelope, QIT.FiniteDistribution.strongTypicalMassScale,
    HSWPackingHypothesesSpectral.stateEigenvalueDistribution_shannonEntropy, avg, cond, ex, ey,
    add_assoc, mul_assoc] using h

/-- For every finite output ensemble and positive Holevo-rate gap, there are
positive typicality slacks making the HSW cross term uniformly exponentially
small in the blocklength. -/
theorem exists_hsw_crossExponentBound_slacks
    {ι : Type u} {out : Type v} [Fintype ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δx δc : ℝ, 0 < δx ∧ 0 < δc ∧
      ∀ n : ℕ,
        4 * Real.rpow 2 ((n : ℝ) * (E.holevoInformation - δ / 2)) *
            (E.strongTypicalDimensionEnvelope n δx δc /
              ((1 - (1 / 2 : ℝ)) *
                QIT.FiniteDistribution.strongTypicalMassScale
                  (HSWPackingHypothesesSpectral.stateEigenvalueDistribution E.averageState)
                  n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
          8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) := by
  let A : ℝ := ∑ x, |(E.states x).vonNeumann|
  let L : ℝ :=
    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
      E.averageState).logTypicalitySlack
  let B : ℝ := (Fintype.card ι : ℝ) * L
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun x _ => abs_nonneg _
  have hL : 0 ≤ L := by
    dsimp [L]
    exact QIT.FiniteDistribution.logTypicalitySlack_nonneg
      (HSWPackingHypothesesSpectral.stateEigenvalueDistribution E.averageState)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card ι)) hL
  obtain ⟨δx, δc, hδx, hδc, hbudget⟩ :=
    exists_pos_pair_linear_slack (A := A) (B := B) (δ := δ) hA hB hδ
  refine ⟨δx, δc, hδx, hδc, ?_⟩
  intro n
  refine hsw_crossExponentBound_of_typicalitySlack (E := E) (n := n) (δ := δ)
    (δx := δx) (δc := δc) ?_
  dsimp [A, B, L] at hbudget ⊢
  calc
    δc + δx * ∑ x, |(E.states x).vonNeumann| +
          ((Fintype.card ι : ℝ) * (δx + δc)) *
            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
              E.averageState).logTypicalitySlack =
        δc + δx * ∑ x, |(E.states x).vonNeumann| +
          ((Fintype.card ι : ℝ) *
            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
              E.averageState).logTypicalitySlack) *
            (δx + δc) := by ring
    _ ≤ δ / 4 := hbudget

namespace HSWClassicalCode

variable {a : Type u} {b : Type v} {M : Type u}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype M] [DecidableEq M] [Nonempty M]
variable {N : Channel a b} {t k : ℕ}

/-- Transport an HSW code across an equality of block lengths. -/
def castLength {n n' : ℕ} (h : n = n') (C : HSWClassicalCode N n M) :
    HSWClassicalCode N n' M :=
  h ▸ C

@[simp]
theorem castLength_rate {n n' : ℕ} (h : n = n') (C : HSWClassicalCode N n M) :
    (C.castLength h).rate = C.rate := by
  cases h
  rfl

theorem castLength_maxErrorAtMost {n n' : ℕ} (h : n = n')
    (C : HSWClassicalCode N n M) {ε : ℝ} (hC : C.maxErrorAtMost ε) :
    (C.castLength h).maxErrorAtMost ε := by
  cases h
  exact hC

/-- Flatten an exact-multiple block-channel HSW code.

A code for `(N^{⊗ k})` used `t` times has input type
`(A^k)^t` and output type `(B^k)^t`.  This constructor relabels those systems
to `A^{t*k}` and `B^{t*k}`.  The separate theorem
`flattenBlock_maxErrorAtMost_of_outputState` records the still-substantive
channel-action compatibility needed to preserve decoding probabilities. -/
def flattenBlock (C : HSWClassicalCode (N.tensorPower k) t M) :
    HSWClassicalCode N (t * k) M where
  encoder m := (C.encoder m).reindex (TensorPower.blockFlattenEquiv a t k)
  decoder := C.decoder.hswReindex (TensorPower.blockFlattenEquiv b t k)

/-- Exact-multiple block flattening divides the block-channel code rate by the
inner block size `k`. -/
theorem flattenBlock_rate_eq_div (C : HSWClassicalCode (N.tensorPower k) t M)
    (ht : 0 < t) (hk : 0 < k) :
    C.flattenBlock.rate = C.rate / (k : ℝ) := by
  have ht_ne : t ≠ 0 := Nat.ne_of_gt ht
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have htk_ne : t * k ≠ 0 := Nat.mul_ne_zero ht_ne hk_ne
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  unfold flattenBlock HSWClassicalCode.rate hswMessageRate
  rw [if_neg htk_ne, if_neg ht_ne]
  field_simp [ne_of_gt ht_pos, ne_of_gt hk_pos]
  rw [Nat.cast_mul]
  ring

/-- Rate lower bound form of `flattenBlock_rate_eq_div`. -/
theorem flattenBlock_rate_ge_of_mul_le_rate
    (C : HSWClassicalCode (N.tensorPower k) t M)
    {R : ℝ} (ht : 0 < t) (hk : 0 < k) (hR : (k : ℝ) * R ≤ C.rate) :
    R ≤ C.flattenBlock.rate := by
  rw [C.flattenBlock_rate_eq_div ht hk]
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  exact (le_div_iff₀ hk_pos).mpr (by simpa [mul_comm] using hR)

/-- If the flattened channel output is the reindexed block-channel output, then
flattening preserves each message success probability.

The hypothesis is intentionally explicit: proving it requires the recursive
matrix identity relating `(N^{⊗ k})^{⊗ t}` and `N^{⊗ (t*k)}` under
`TensorPower.blockFlattenEquiv`, which is a separate block-transport proof
dependency. -/
theorem flattenBlock_successProbability_of_outputState
    (C : HSWClassicalCode (N.tensorPower k) t M)
    (houtput : ∀ m : M,
      C.flattenBlock.outputState m =
        (C.outputState m).reindex (TensorPower.blockFlattenEquiv b t k))
    (m : M) :
    C.flattenBlock.successProbability m = C.successProbability m := by
  unfold HSWClassicalCode.successProbability
  rw [houtput m]
  exact POVM.hswReindex_prob_reindex_state C.decoder (C.outputState m)
    (TensorPower.blockFlattenEquiv b t k) m

/-- Under the explicit output-state compatibility, exact-multiple block
flattening preserves maximal-error reliability. -/
theorem flattenBlock_maxErrorAtMost_of_outputState
    (C : HSWClassicalCode (N.tensorPower k) t M)
    {ε : ℝ}
    (houtput : ∀ m : M,
      C.flattenBlock.outputState m =
        (C.outputState m).reindex (TensorPower.blockFlattenEquiv b t k))
    (hC : C.maxErrorAtMost ε) :
    C.flattenBlock.maxErrorAtMost ε := by
  intro m
  unfold HSWClassicalCode.error
  rw [C.flattenBlock_successProbability_of_outputState houtput m]
  exact hC m

/-- Exact-multiple block flattening has the expected reindexed output state. -/
theorem flattenBlock_outputState
    (C : HSWClassicalCode (N.tensorPower k) t M) (m : M) :
    C.flattenBlock.outputState m =
      (C.outputState m).reindex (TensorPower.blockFlattenEquiv b t k) := by
  unfold HSWClassicalCode.outputState HSWClassicalCode.flattenBlock
  exact Channel.tensorPower_blockFlatten_applyState N t k (C.encoder m)

/-- Exact-multiple block flattening preserves each message success probability. -/
theorem flattenBlock_successProbability
    (C : HSWClassicalCode (N.tensorPower k) t M) (m : M) :
    C.flattenBlock.successProbability m = C.successProbability m :=
  C.flattenBlock_successProbability_of_outputState C.flattenBlock_outputState m

/-- Exact-multiple block flattening preserves maximal-error reliability. -/
theorem flattenBlock_maxErrorAtMost
    (C : HSWClassicalCode (N.tensorPower k) t M) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    C.flattenBlock.maxErrorAtMost ε :=
  C.flattenBlock_maxErrorAtMost_of_outputState C.flattenBlock_outputState hC

/-- Pad an HSW code on the right by a fixed tail input state, with the decoder
ignoring the tail output register.

This is the code-level primitive needed to convert exact-multiple block codes
into codes at arbitrary sufficiently large lengths.  The channel-output product
identity for `N^{⊗ (m+r)}` is kept as an explicit proof obligation in the
preservation theorems below. -/
def padRight {m r : ℕ} (C : HSWClassicalCode N m M)
    (tail : State (TensorPower a r)) : HSWClassicalCode N (m + r) M where
  encoder msg :=
    ((C.encoder msg).prod tail).reindex (TensorPower.appendEquiv a m r)
  decoder :=
    (C.decoder.hswTensorRightIdentity (TensorPower b r)).hswReindex
      (TensorPower.appendEquiv b m r)

/-- Under the explicit product-output compatibility, right padding preserves
each message success probability. -/
theorem padRight_successProbability_of_outputState {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : State (TensorPower a r))
    (houtput : ∀ msg : M,
      (C.padRight tail).outputState msg =
        ((C.outputState msg).prod ((N.tensorPower r).applyState tail)).reindex
          (TensorPower.appendEquiv b m r))
    (msg : M) :
    (C.padRight tail).successProbability msg = C.successProbability msg := by
  unfold HSWClassicalCode.successProbability
  rw [houtput msg]
  change
    (((C.decoder.hswTensorRightIdentity (TensorPower b r)).hswReindex
        (TensorPower.appendEquiv b m r)).prob
      (((C.outputState msg).prod ((N.tensorPower r).applyState tail)).reindex
        (TensorPower.appendEquiv b m r)) msg : ℝ) =
      (C.decoder.prob (C.outputState msg) msg : ℝ)
  rw [POVM.hswReindex_prob_reindex_state]
  exact POVM.hswTensorRightIdentity_prob_prod C.decoder (C.outputState msg)
    ((N.tensorPower r).applyState tail) msg

/-- Under the explicit product-output compatibility, right padding preserves
maximal-error reliability. -/
theorem padRight_maxErrorAtMost_of_outputState {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : State (TensorPower a r)) {ε : ℝ}
    (houtput : ∀ msg : M,
      (C.padRight tail).outputState msg =
        ((C.outputState msg).prod ((N.tensorPower r).applyState tail)).reindex
          (TensorPower.appendEquiv b m r))
    (hC : C.maxErrorAtMost ε) :
    (C.padRight tail).maxErrorAtMost ε := by
  intro msg
  unfold HSWClassicalCode.error
  rw [C.padRight_successProbability_of_outputState tail houtput msg]
  exact hC msg

/-- Right padding has the expected product output under the tensor-power
append transport. -/
theorem padRight_outputState {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : State (TensorPower a r)) (msg : M) :
    (C.padRight tail).outputState msg =
      ((C.outputState msg).prod ((N.tensorPower r).applyState tail)).reindex
        (TensorPower.appendEquiv b m r) := by
  unfold HSWClassicalCode.outputState HSWClassicalCode.padRight
  exact Channel.tensorPower_append_applyState_prod N m r (C.encoder msg) tail

/-- Right padding preserves each message success probability. -/
theorem padRight_successProbability {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : State (TensorPower a r)) (msg : M) :
    (C.padRight tail).successProbability msg = C.successProbability msg :=
  C.padRight_successProbability_of_outputState tail (C.padRight_outputState tail) msg

/-- Right padding preserves maximal-error reliability. -/
theorem padRight_maxErrorAtMost {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : State (TensorPower a r)) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    (C.padRight tail).maxErrorAtMost ε :=
  C.padRight_maxErrorAtMost_of_outputState tail (C.padRight_outputState tail) hC

/-- Rate lower bound for the exact-multiple flattening followed by right
padding.  The hypothesis `hratio` is the explicit large-block arithmetic that
absorbs the padding loss. -/
theorem flattenBlock_padRight_rate_ge_of_ratio
    {r : ℕ} (C : HSWClassicalCode (N.tensorPower k) t M)
    (tail : State (TensorPower a r)) {A B : ℝ} (ht : 0 < t) (hk : 0 < k)
    (hbase : A ≤ C.rate / (k : ℝ))
    (hratio : B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ))) :
    B ≤ (C.flattenBlock.padRight tail).rate := by
  change B ≤ hswMessageRate M (t * k + r)
  exact hswMessageRate.block_pad_ge_of_ratio (M := M) ht hk hbase hratio

end HSWClassicalCode

namespace HSWPackingHypothesesSpectral

/-- A completed HSW spectral packing-hypotheses bundle yields the deterministic
average-error packing witness consumed by the HSW direct-achievability
assembly layer.

This theorem is only a bridge: the caller must already supply the source-shaped
packing hypotheses, the input-codeword lift `φ`, the channel-output agreement,
and the message-cardinality/rate estimate.  No random-coding existence,
typicality estimate, or block-channel lift is hidden in this statement. -/
theorem toAverageErrorPackingWitness
    {a : Type u} {b : Type v} {ι : Type u} {𝒳 : Type*} {M : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype ι] [DecidableEq ι] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M] [Nonempty M]
    (N : Channel a b) (E₀ : Ensemble ι a) {n : ℕ} {typicalitySlack rateSlack : ℝ}
    {Eout : Ensemble 𝒳 (TensorPower b n)}
    (H : HSWPackingHypothesesSpectral Eout typicalitySlack)
    (φ : 𝒳 → State (TensorPower a n))
    (houtput : ∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x)
    (hrate : hswMessageRate M n ≥ N.hswHolevoRate E₀ - rateSlack) :
    Nonempty
      (HSWAverageErrorPackingWitness N E₀ n rateSlack
        (2 * (H.ε + 2 * Real.sqrt H.ε) +
          4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)) M) :=
  PackingLemma.hswAverageErrorPackingWitness_of_packing
    N E₀ n rateSlack Eout H.P H.P_posSemidef H.P_idempotent H.P_le_one
    H.Px H.Px_projector φ houtput H.d H.D H.ε H.hD_pos H.hε_nonneg
    H.h1 H.h2 H.h3 H.h4 hrate

/-- A completed HSW spectral packing-hypotheses bundle, together with a positive
packing-error bound, expurgates to the maximal-error direct-coding witness used
by operational achievability.

The additional `1/n` rate slack and the factor-two error loss are exactly the
average-to-maximal expurgation losses formalized in `HSW.lean`.  The positivity
assumption on the displayed packing-error expression is not hidden: it is the
side condition required by that expurgation step. -/
theorem exists_directCodingWitness_expurgated
    {a : Type u} {b : Type v} {ι : Type u} {𝒳 : Type*} {M : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype ι] [DecidableEq ι] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M] [Nonempty M]
    (N : Channel a b) (E₀ : Ensemble ι a) {n : ℕ} {typicalitySlack rateSlack : ℝ}
    {Eout : Ensemble 𝒳 (TensorPower b n)}
    (H : HSWPackingHypothesesSpectral Eout typicalitySlack)
    (φ : 𝒳 → State (TensorPower a n))
    (houtput : ∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x)
    (hrate : hswMessageRate M n ≥ N.hswHolevoRate E₀ - rateSlack)
    (hn : 0 < n)
    (hpackingError_pos :
      0 < 2 * (H.ε + 2 * Real.sqrt H.ε) +
        4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)) :
    ∃ (M' : Type u), ∃ (_ : Fintype M'), ∃ (_ : DecidableEq M'), ∃ (_ : Nonempty M'),
      Nonempty
        (HSWDirectCodingWitness N E₀ n (rateSlack + (1 : ℝ) / (n : ℝ))
          (2 * (2 * (H.ε + 2 * Real.sqrt H.ε) +
            4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D))) M') := by
  let packingError : ℝ :=
    2 * (H.ε + 2 * Real.sqrt H.ε) +
      4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)
  have havg :
      Nonempty (HSWAverageErrorPackingWitness N E₀ n rateSlack packingError M) := by
    simpa [packingError] using
      H.toAverageErrorPackingWitness N E₀ φ houtput hrate
  rcases havg with ⟨W⟩
  have hpos : 0 < packingError := by
    simpa [packingError] using hpackingError_pos
  simpa [packingError] using W.exists_directCodingWitness_expurgated hn hpos

end HSWPackingHypothesesSpectral

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- HSW direct-achievability assembly from completed spectral packing bundles.

This is the post-typicality interface for the direct proof.  For every target
rate slack `δ` and target maximal-error tolerance `ε`, the caller must provide,
eventually in the block length `n`,

* positivity of `n` and the expurgation rate-loss bound `1/n ≤ δ/2`;
* a finite message set `M`;
* a finite random-codeword alphabet `𝒳`;
* an output ensemble over `B^n`;
* a completed `HSWPackingHypothesesSpectral` bundle for that output ensemble;
* an input codeword lift whose channel outputs agree with the output ensemble;
* a message-cardinality/rate estimate at slack `δ/2`;
* and the displayed packing-error expression bounded by `ε/2`.

Under exactly those hypotheses, the existing packing lemma, expurgation, and
operational-achievability layer prove that the one-letter Holevo rate
`χ(N,E₀)` is achievable.  The random-code existence and typical-estimate
families remain explicit upstream obligations. -/
theorem hsw_directWitnessAssembly_from_spectralPackingHypotheses
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
              ∃ (_ : Nonempty M),
                ∃ (𝒳 : Type u), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                  ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                    ∃ (typicalitySlack : ℝ),
                      ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                        ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                          (∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 ∧
                              2 * (H.ε + 2 * Real.sqrt H.ε) +
                                  4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D) ≤
                                ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_averageErrorPacking E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, M, hMfin, hMdec, hMnonempty,
    𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ,
    houtput, hrate, hpacking_le⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype 𝒳 := h𝒳fin
  letI : DecidableEq 𝒳 := h𝒳dec
  let packingError : ℝ :=
    2 * (H.ε + 2 * Real.sqrt H.ε) +
      4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)
  have havg :
      Nonempty (HSWAverageErrorPackingWitness N E₀ n (δ / 2) packingError M) := by
    simpa [packingError] using
      H.toAverageErrorPackingWitness N E₀ φ houtput hrate
  refine ⟨hn_pos, hinv_le, M, inferInstance, inferInstance, inferInstance, ?_⟩
  rcases havg with ⟨W⟩
  exact ⟨W.weaken le_rfl (by simpa [packingError] using hpacking_le)⟩

/-- HSW direct-achievability assembly from spectral packing estimates, with the
finite message set chosen internally.

Compared with `hsw_directWitnessAssembly_from_spectralPackingHypotheses`, the
caller no longer supplies the message alphabet or the rate estimate.  For each
large block length, this theorem chooses a finite nonempty message type whose
HSW rate is at least `χ(N,E₀) - δ/2`; the remaining hypothesis is exactly the
source-shaped spectral/typical estimate package for that chosen message set,
including the packing-error bound. -/
theorem hsw_directWitnessAssembly_from_spectralPackingEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (𝒳 : Type u), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                  ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                    ∃ (typicalitySlack : ℝ),
                      ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                        ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                          (∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            2 * (H.ε + 2 * Real.sqrt H.ε) +
                                4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D) ≤
                              ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingHypotheses E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, hrate⟩ :=
    hswMessageRate.exists_finite_message_type_rate_ge hn_pos
      (N.hswHolevoRate E₀ - δ / 2)
  obtain ⟨𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hpacking_le⟩ :=
    hpack M hMfin hMdec hMnonempty hrate
  exact ⟨hn_pos, hinv_le, M, hMfin, hMdec, hMnonempty,
    𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hrate, hpacking_le⟩

/-- HSW direct-achievability assembly from spectral packing estimates, with the
finite message set chosen internally and its cross-term cardinality bound
exposed to the estimate layer.

This variant is the rate-accounting form used by the asymptotic HSW direct
proof.  The chosen message alphabet satisfies both
`χ(N,E₀)-δ/2 ≤ log₂ |M|/n` and
`|M|-1 ≤ 2^{n(χ(N,E₀)-δ/2)}`.  The second inequality is what lets the final
packing-error bound be proved from a source exponent estimate instead of being
assumed as an opaque all-message-set hypothesis. -/
theorem hsw_directWitnessAssembly_from_spectralPackingEstimatesWithCardBound
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                (Fintype.card M : ℝ) - 1 ≤
                  Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) →
                ∃ (𝒳 : Type u), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                  ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                    ∃ (typicalitySlack : ℝ),
                      ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                        ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                          (∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            2 * (H.ε + 2 * Real.sqrt H.ε) +
                                4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D) ≤
                              ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingHypotheses E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, hrate, hcard⟩ :=
    hswMessageRate.exists_finite_message_type_rate_ge_card_sub_one_le hn_pos
      (N.hswHolevoRate E₀ - δ / 2)
  obtain ⟨𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hpacking_le⟩ :=
    hpack M hMfin hMdec hMnonempty hrate hcard
  exact ⟨hn_pos, hinv_le, M, hMfin, hMdec, hMnonempty,
    𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hrate, hpacking_le⟩

/-- HSW direct-achievability assembly from the diagonal strong-typical packing
route.

This is the source-shaped version of
`hsw_directWitnessAssembly_from_spectralPackingEstimates` for the currently
formalized pack-1 route.  The caller supplies the diagonal classical channel
`K`, strongly typical codeword map, codeword projectors, and the remaining
pack-2/3/4 estimates in the shape consumed by
`hswPackingHypothesesDiagonal_of_pinchedStrongTypical`.  This theorem then
constructs the generic packing bundle, chooses the finite message set, applies
the packing lemma and expurgation, and proves operational achievability of
`χ(N,E₀)`.

The asymptotic typical/packing estimates remain explicit hypotheses: no
random-coding existence or spectral/strong projector identification is hidden
in this bridge. -/
theorem hsw_directWitnessAssembly_from_diagonalPackingEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (𝒳 : Type u), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                      ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                        ∃ (codewordOf : 𝒳 → Fin n → α),
                          ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (d : ℝ), ∃ (D : ℝ),
                                ∃ (Px : 𝒳 → CMatrix (QIT.TensorPower b n)),
                                  0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                    (∀ x,
                                      (Eout.states x).matrix =
                                        (HSWPackingHypothesesSpectral.conditionalProductDiagonalState K
                                          (codewordOf x)).matrix) ∧
                                    (∀ x,
                                      ClassicalTypicality.StrongTypical p
                                        (codewordOf x) δx) ∧
                                    (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                        ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                    (∀ x,
                                      (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                        Px x ≤ 1) ∧
                                    (∀ x,
                                      1 - packingε ≤
                                        ((Px x * (Eout.states x).matrix).trace).re) ∧
                                    (∀ x, ((Px x).trace).re ≤ d) ∧
                                    (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K) n
                                          ((Fintype.card α : ℝ) * (δx + δc)) *
                                        Eout.averageState.matrix *
                                        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K) n
                                          ((Fintype.card α : ℝ) * (δx + δc))
                                        ≤ ((D : ℝ)⁻¹) •
                                          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                            (ClassicalTypicality.inducedMarginal p K)
                                            n
                                            ((Fintype.card α : ℝ) * (δx + δc))) ∧
                                    (∀ x, (N.tensorPower n).applyState (φ x) =
                                      Eout.states x) ∧
                                    2 * (packingε + 2 * Real.sqrt packingε) +
                                        4 * ((Fintype.card M : ℝ) - 1) * (d / D) ≤
                                      ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, 𝒳, h𝒳fin, h𝒳dec, Eout, codewordOf, φ,
    δx, δc, packingε, d, D, Px, hδx, hδc, hpackingε, hD, hstates, hx, hlarge,
    hPx, h2, h3, h4, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  letI : Fintype 𝒳 := h𝒳fin
  letI : DecidableEq 𝒳 := h𝒳dec
  let H : HSWPackingHypothesesSpectral Eout
      ((Fintype.card α : ℝ) * (δx + δc)) :=
    HSWPackingHypothesesSpectral.hswPackingHypothesesDiagonal_of_pinchedStrongTypical
      p K Eout codewordOf hn_pos hδx hδc hpackingε hD hstates hx hlarge
      Px hPx h2 h3 h4
  refine ⟨𝒳, inferInstance, inferInstance, Eout,
    (Fintype.card α : ℝ) * (δx + δc), H, φ, houtput, ?_⟩
  simpa [H] using hpacking_le

/-- HSW direct-achievability assembly from pruned diagonal packing estimates.

This theorem removes the projected-average pack-4 bound from the caller's
obligations in the diagonal route.  The caller supplies the source-shaped
pruned distribution domination
`p'(xⁿ) ≤ (1 - η)⁻¹ pⁿ(xⁿ)` and the marginal-product mass envelope on the
strong-typical output set.  The proved pruned pack-4 bridge in
`ConditionalTypicality.lean` then constructs the `h4` Loewner bound consumed by
`hsw_directWitnessAssembly_from_diagonalPackingEstimates`.

The remaining inputs are still genuine HSW direct-proof content: a pruned
codeword ensemble, codeword projectors with pack-2/pack-3 estimates, physical
channel-output realizations, and the final packing-error rate inequality. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
                        ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                          ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                            ∃ (Px : (Fin n → α) → CMatrix (QIT.TensorPower b n)),
                              0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                pruneε < 1 ∧
                                (∀ x : Fin n → α,
                                  Eout.states x =
                                    HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                      K x) ∧
                                (∀ x : Fin n → α,
                                  ClassicalTypicality.StrongTypical p x δx) ∧
                                (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                    ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                (∀ x : Fin n → α,
                                  (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                    Px x ≤ 1) ∧
                                (∀ x : Fin n → α,
                                  1 - packingε ≤
                                    ((Px x * (Eout.states x).matrix).trace).re) ∧
                                (∀ x : Fin n → α, ((Px x).trace).re ≤ d) ∧
                                (∀ zseq : Fin n → b,
                                  ClassicalTypicality.StrongTypical
                                      (ClassicalTypicality.inducedMarginal p K)
                                      zseq
                                      ((Fintype.card α : ℝ) * (δx + δc)) →
                                    (HSWPackingHypothesesSpectral.marginalProductMass
                                      (ClassicalTypicality.inducedMarginal p K) zseq : ℝ)
                                      ≤ D⁻¹) ∧
                                (∀ x : Fin n → α,
                                  (Eout.probs x : ℝ) ≤
                                    (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                                (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                  Eout.states x) ∧
                                2 * (packingε + 2 * Real.sqrt packingε) +
                                    4 * ((Fintype.card M : ℝ) - 1) *
                                      (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, d, D, pruneε,
    Px, hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hPx, h2, h3,
    hmass_bound, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  have hD_eff : 0 < (1 - pruneε) * D := by
    have hpos : 0 < 1 - pruneε := by linarith
    exact mul_pos hpos hD
  refine ⟨α, inferInstance, inferInstance, p, K, (Fin n → α), inferInstance,
    inferInstance, Eout, (fun x => x), φ, δx, δc, packingε, d,
    (1 - pruneε) * D, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, hD_eff, ?_, hx, hlarge, hPx, h2, h3, ?_,
    houtput, hpacking_le⟩
  · intro x
    rw [hstates x]
  · exact
      strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_effectiveD
        p K hprune hD Eout hstates hdom hmass_bound

/-- HSW direct-achievability assembly from source-shaped conditionally-typical
projector estimates.

This is the next specialization after
`hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates`: instead of
asking the caller to provide arbitrary codeword projectors `Π_x` satisfying
pack-2 and pack-3, it instantiates them as the conditionally typical projectors
of the product output states.  The remaining obligations are the genuine
Wilde HSW estimates: the second-moment capture bound, the
conditionally-typical-subspace dimension bound, the pruned-distribution
domination, the marginal-product mass envelope, physical channel output, and
the final packing-error inequality.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
                        ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                          ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                            0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                              pruneε < 1 ∧
                              (∀ x : Fin n → α,
                                Eout.states x =
                                  HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                    K x) ∧
                              (∀ x : Fin n → α,
                                ClassicalTypicality.StrongTypical p x δx) ∧
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                  ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                              (∀ x : Fin n → α,
                                conditionalLogDeviationSecondMoment
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob (x i)) (K.sum_eq_one (x i))) /
                                  ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                              (∀ x : Fin n → α,
                                conditionallyTypicalSubspaceDimension
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob (x i)) (K.sum_eq_one (x i))) δc ≤ d) ∧
                              (∀ zseq : Fin n → b,
                                ClassicalTypicality.StrongTypical
                                    (ClassicalTypicality.inducedMarginal p K)
                                    zseq
                                    ((Fintype.card α : ℝ) * (δx + δc)) →
                                  (HSWPackingHypothesesSpectral.marginalProductMass
                                    (ClassicalTypicality.inducedMarginal p K) zseq : ℝ)
                                    ≤ D⁻¹) ∧
                              (∀ x : Fin n → α,
                                (Eout.probs x : ℝ) ≤
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, d, D, pruneε,
    hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment, hdim,
    hmass_bound, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let Px : (Fin n → α) → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
      δc
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    d, D, pruneε, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, ?_, ?_, ?_,
    hmass_bound, hdom, houtput, hpacking_le⟩
  · intro x
    dsimp [Px]
    exact ⟨
      conditionallyTypicalSubspaceProjector_posSemidef
        (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
        δc,
      conditionallyTypicalSubspaceProjector_idempotent
        (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
        δc,
      conditionallyTypicalSubspaceProjector_le_one
        (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
        δc⟩
  · intro x
    dsimp [Px]
    rw [hstates x]
    rw [HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K x]
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (states := fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
      (δ := δc) hn_pos hδc
    have hkey :
        1 - packingε ≤
          1 - conditionalLogDeviationSecondMoment
              (fun i : Fin n => Classical.diagonalState
                (K.prob (x i)) (K.sum_eq_one (x i))) /
            ((n : ℝ) * δc) ^ 2 := by
      linarith [hmoment x]
    exact le_trans hkey hown
  · intro x
    dsimp [Px]
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
    exact hdim x

/-- HSW direct-achievability assembly from source-shaped conditionally-typical
projector estimates and the finite classical entropy envelope for pack-4.

Compared with `hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates`,
this theorem no longer asks for a word-by-word `hmass_bound`.  It instead
consumes the explicit strong-typical product-mass exponent
`2^{-n H(Z) + n δ L(Z)} ≤ D⁻¹` for the induced output distribution. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
                        ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                          ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                            0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                              pruneε < 1 ∧
                              (∀ x : Fin n → α,
                                Eout.states x =
                                  HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                    K x) ∧
                              (∀ x : Fin n → α,
                                ClassicalTypicality.StrongTypical p x δx) ∧
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                  ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                              (∀ x : Fin n → α,
                                conditionalLogDeviationSecondMoment
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob (x i)) (K.sum_eq_one (x i))) /
                                  ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                              (∀ x : Fin n → α,
                                conditionallyTypicalSubspaceDimension
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob (x i)) (K.sum_eq_one (x i))) δc ≤ d) ∧
                              Real.rpow 2
                                (- (n : ℝ) *
                                    (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
                                  (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
                                    (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
                                  ≤ D⁻¹ ∧
                              (∀ x : Fin n → α,
                                (Eout.probs x : ℝ) ≤
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, d, D, pruneε,
    hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment, hdim,
    hD_entropy, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  have hδtyp : 0 ≤ (Fintype.card α : ℝ) * (δx + δc) := by
    have hcard : 0 ≤ (Fintype.card α : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsum : 0 ≤ δx + δc := by linarith
    exact mul_nonneg hcard hsum
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    d, D, pruneε, hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment,
    hdim, ?_, hdom, houtput, hpacking_le⟩
  intro zseq hz
  exact HSWPackingHypothesesSpectral.marginalProductMass_le_D_inv_of_entropy_slack
    (ClassicalTypicality.inducedMarginal p K) zseq hn_pos hδtyp hD_entropy hz

/-- HSW direct-achievability assembly with both pack-3 and pack-4 discharged by
finite classical typicality envelopes.

Compared with `hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates`,
this theorem no longer asks the caller for a separate conditionally-typical
subspace dimension bound.  Strong typicality of every selected codeword supplies
the named diagonal-output dimension envelope
`hswConditionalDiagonalDimensionEnvelope p K n δx δc`. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
                        ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                          ∃ (D : ℝ), ∃ (pruneε : ℝ),
                            0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                              pruneε < 1 ∧
                              (∀ x : Fin n → α,
                                Eout.states x =
                                  HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                    K x) ∧
                              (∀ x : Fin n → α,
                                ClassicalTypicality.StrongTypical p x δx) ∧
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                  ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                              (∀ x : Fin n → α,
                                conditionalLogDeviationSecondMoment
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob (x i)) (K.sum_eq_one (x i))) /
                                  ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                              Real.rpow 2
                                (- (n : ℝ) *
                                    (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
                                  (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
                                    (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
                                  ≤ D⁻¹ ∧
                              (∀ x : Fin n → α,
                                (Eout.probs x : ℝ) ≤
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                      ((1 - pruneε) * D)) ≤ ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, D, pruneε,
    hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment,
    hD_entropy, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let d := hswConditionalDiagonalDimensionEnvelope p K n δx δc
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    d, D, pruneε, hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment,
    ?_, hD_entropy, hdom, houtput, ?_⟩
  · intro x
    dsimp [d]
    exact conditionallyTypicalSubspaceProjector_dim_le_hswConditionalDiagonalDimensionEnvelope
      p K x hn_pos hδx hδc (hx x)
  · simpa [d] using hpacking_le

/-- HSW direct-achievability assembly with the canonical marginal-product mass
scale `D = 2^{nH(Z)-nδL(Z)}` chosen internally.

Compared with
`hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates`,
this theorem no longer asks the caller to provide `D` or prove the
`2^{-nH+nδL} ≤ D⁻¹` side condition. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorTypicalityScaleEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
                        ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                          ∃ (pruneε : ℝ),
                            0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                              (∀ x : Fin n → α,
                                Eout.states x =
                                  HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                    K x) ∧
                              (∀ x : Fin n → α,
                                ClassicalTypicality.StrongTypical p x δx) ∧
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                  ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                              (∀ x : Fin n → α,
                                conditionalLogDeviationSecondMoment
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob (x i)) (K.sum_eq_one (x i))) /
                                  ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                              (∀ x : Fin n → α,
                                (Eout.probs x : ℝ) ≤
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                      ((1 - pruneε) *
                                        (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                          n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                    ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates
    E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, pruneε,
    hδx, hδc, hpackingε, hprune, hstates, hx, hlarge, hmoment, hdom, houtput,
    hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let δz : ℝ := (Fintype.card α : ℝ) * (δx + δc)
  let D : ℝ := (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale n δz
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    D, pruneε, hδx, hδc, hpackingε, ?_, hprune, hstates, hx, hlarge, hmoment,
    ?_, hdom, houtput, ?_⟩
  · exact (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos n δz
  · dsimp [D, δz]
    exact le_of_eq
      ((ClassicalTypicality.inducedMarginal p K).rpow_entropy_slack_eq_strongTypicalMassScale_inv
        n ((Fintype.card α : ℝ) * (δx + δc)))
  · simpa [D, δz] using hpacking_le

/-- HSW direct-achievability assembly indexed by the strongly-typical pruned
codebook subtype.

Compared with
`hsw_directWitnessAssembly_from_prunedDiagonalProjectorTypicalityScaleEstimates`,
this theorem no longer asks the caller to prove
`∀ x : Fin n → α, StrongTypical p x δx`, which is not the right pruned-codebook
shape.  Instead, the random-coding index type is the subtype
`ClassicalTypicality.StrongTypicalWord p n δx`, and the codeword map is the
subtype inclusion.  The strong-typicality hypothesis and the pack-3 dimension
envelope are then discharged internally.

The theorem still keeps the genuinely independent HSW obligations explicit:
the diagonal/pinched output realization, the projected-average pack-4 bound for
the pruned ensemble, the uniform conditional log-deviation estimate, the
physical channel-output realization, and the final packing-error inequality. -/
theorem hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                      ∃ (Eout :
                          Ensemble (ClassicalTypicality.StrongTypicalWord p n δx)
                            (QIT.TensorPower b n)),
                        ∃ (φ :
                            ClassicalTypicality.StrongTypicalWord p n δx →
                              State (QIT.TensorPower a n)),
                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            (∀ x,
                              (Eout.states x).matrix =
                                (HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                  K
                                  (ClassicalTypicality.StrongTypicalWord.codeword p δx x)).matrix) ∧
                            (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    Classical.diagonalState
                                      (K.prob
                                        (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
                                      (K.sum_eq_one
                                        (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                  (ClassicalTypicality.inducedMarginal p K)
                                  n
                                  ((Fintype.card α : ℝ) * (δx + δc)) *
                                Eout.averageState.matrix *
                                HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                  (ClassicalTypicality.inducedMarginal p K)
                                  n
                                  ((Fintype.card α : ℝ) * (δx + δc))
                                ≤
                                  (((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                      n ((Fintype.card α : ℝ) * (δx + δc))) : ℝ)⁻¹ •
                                    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                      (ClassicalTypicality.inducedMarginal p K)
                                      n
                                      ((Fintype.card α : ℝ) * (δx + δc))) ∧
                            (∀ x,
                              (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) +
                                4 * ((Fintype.card M : ℝ) - 1) *
                                  (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                    ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                      n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                  ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, δx, δc, packingε, Eout, φ,
    hδx, hδc, hpackingε, hstates, hlarge, hmoment, h4, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  let codewordOf : 𝒳 → Fin n → α := fun x =>
    ClassicalTypicality.StrongTypicalWord.codeword p δx x
  let D : ℝ :=
    (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
      n ((Fintype.card α : ℝ) * (δx + δc))
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      δc
  refine ⟨α, inferInstance, inferInstance, p, K, 𝒳, inferInstance, inferInstance,
    Eout, codewordOf, φ, δx, δc, packingε,
    hswConditionalDiagonalDimensionEnvelope p K n δx δc, D, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, ?_, hstates, ?_, hlarge, ?_, ?_, ?_, ?_,
    houtput, ?_⟩
  · dsimp [D]
    exact (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos
      n ((Fintype.card α : ℝ) * (δx + δc))
  · intro x
    exact ClassicalTypicality.StrongTypicalWord.strongTypical p δx x
  · intro x
    dsimp [Px]
    exact ⟨
      conditionallyTypicalSubspaceProjector_posSemidef
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_idempotent
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_le_one
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc⟩
  · intro x
    dsimp [Px]
    rw [hstates x]
    rw [HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K (codewordOf x)]
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (states := fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      (δ := δc) hn_pos hδc
    have hkey :
        1 - packingε ≤
          1 - conditionalLogDeviationSecondMoment
              (fun i : Fin n =>
                Classical.diagonalState (K.prob (codewordOf x i))
                  (K.sum_eq_one (codewordOf x i))) /
            ((n : ℝ) * δc) ^ 2 := by
      linarith [hmoment x]
    exact le_trans hkey hown
  · intro x
    dsimp [Px]
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
    exact conditionallyTypicalSubspaceProjector_dim_le_hswConditionalDiagonalDimensionEnvelope
      p K (codewordOf x) hn_pos hδx hδc
      (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
  · dsimp [D]
    exact h4
  · dsimp [D]
    exact hpacking_le

/-- HSW direct-achievability assembly for the canonical pruned strongly-typical
codebook law.

This strengthens
`hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates`
by deriving the projected-average `pack-4` bound internally from the normalized
i.i.d. law on the strongly-typical subtype.  Consequently the effective
packing denominator is `(1 - pruneε) * strongTypicalMassScale`, matching the
HSW pruning prefactor rather than assuming it away. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                      ∃ (hmass_pos :
                          0 < ClassicalTypicality.strongTypicalMass (n := n) p δx),
                        ∃ (Eout :
                            Ensemble (ClassicalTypicality.StrongTypicalWord p n δx)
                              (QIT.TensorPower b n)),
                          ∃ (φ :
                              ClassicalTypicality.StrongTypicalWord p n δx →
                                State (QIT.TensorPower a n)),
                            0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                              (1 - pruneε : ℝ) ≤
                                (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) ∧
                              (∀ x,
                                Eout.probs x =
                                  (ClassicalTypicality.prunedStrongTypicalDistribution
                                    p δx hmass_pos).prob x) ∧
                              (∀ x,
                                Eout.states x =
                                  HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                    K
                                    (ClassicalTypicality.StrongTypicalWord.codeword
                                      p δx x)) ∧
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                  ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                              (∀ x,
                                conditionalLogDeviationSecondMoment
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob
                                          (ClassicalTypicality.StrongTypicalWord.codeword
                                            p δx x i))
                                        (K.sum_eq_one
                                          (ClassicalTypicality.StrongTypicalWord.codeword
                                            p δx x i))) /
                                  ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                              (∀ x,
                                (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                      ((1 - pruneε) *
                                        (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                          n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                    ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, δx, δc, packingε, pruneε, hmass_pos,
    Eout, φ, hδx, hδc, hpackingε, hprune, hmass_lower, hprobs, hstates,
    hlarge, hmoment, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  let codewordOf : 𝒳 → Fin n → α := fun x =>
    ClassicalTypicality.StrongTypicalWord.codeword p δx x
  let δz : ℝ := (Fintype.card α : ℝ) * (δx + δc)
  let scale : ℝ :=
    (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale n δz
  let D : ℝ := (1 - pruneε) * scale
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      δc
  refine ⟨α, inferInstance, inferInstance, p, K, 𝒳, inferInstance, inferInstance,
    Eout, codewordOf, φ, δx, δc, packingε,
    hswConditionalDiagonalDimensionEnvelope p K n δx δc, D, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, ?_, ?_, ?_, hlarge, ?_, ?_, ?_, ?_,
    houtput, ?_⟩
  · dsimp [D, scale]
    have hprune_pos : 0 < 1 - pruneε := by linarith
    exact mul_pos hprune_pos
      ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos n δz)
  · intro x
    rw [hstates x]
  · intro x
    exact ClassicalTypicality.StrongTypicalWord.strongTypical p δx x
  · intro x
    dsimp [Px]
    exact ⟨
      conditionallyTypicalSubspaceProjector_posSemidef
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_idempotent
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_le_one
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc⟩
  · intro x
    dsimp [Px]
    rw [hstates x]
    rw [HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K (codewordOf x)]
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (states := fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      (δ := δc) hn_pos hδc
    have hkey :
        1 - packingε ≤
          1 - conditionalLogDeviationSecondMoment
              (fun i : Fin n =>
                Classical.diagonalState (K.prob (codewordOf x i))
                  (K.sum_eq_one (codewordOf x i))) /
            ((n : ℝ) * δc) ^ 2 := by
      linarith [hmoment x]
    exact le_trans hkey hown
  · intro x
    dsimp [Px]
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
    exact conditionallyTypicalSubspaceProjector_dim_le_hswConditionalDiagonalDimensionEnvelope
      p K (codewordOf x) hn_pos hδx hδc
      (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
  · dsimp [D, scale, δz]
    have hδz : 0 ≤ (Fintype.card α : ℝ) * (δx + δc) := by
      have hcard : 0 ≤ (Fintype.card α : ℝ) := by exact_mod_cast Nat.zero_le _
      have hsum : 0 ≤ δx + δc := by linarith
      exact mul_nonneg hcard hsum
    have hD_entropy :
        Real.rpow 2
          (- (n : ℝ) * (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
            (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
              (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
          ≤
            ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
              n ((Fintype.card α : ℝ) * (δx + δc)))⁻¹ := by
      exact le_of_eq
        ((ClassicalTypicality.inducedMarginal p K).rpow_entropy_slack_eq_strongTypicalMassScale_inv
          n ((Fintype.card α : ℝ) * (δx + δc)))
    exact
      strongTypicalDiagonalProjector_projectedPrunedStrongTypicalConditionalProductAverage_le_entropyD
        p K hn_pos hprune hmass_pos hmass_lower
        ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos
          n ((Fintype.card α : ℝ) * (δx + δc)))
        hδz hD_entropy Eout hprobs hstates
  · dsimp [D, scale, δz]
    exact hpacking_le

/-- HSW direct-achievability assembly with the canonical pruned output ensemble
constructed internally.

This removes the remaining bookkeeping burden of constructing the pruned
strongly-typical output ensemble from the caller.  The caller supplies only the
typical-set mass lower bound, the conditional spectral log-deviation estimate,
the physical realization of the canonical diagonal product outputs, and the
final packing-error numerical bound. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleBounds
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                      ∃ (φ :
                          ClassicalTypicality.StrongTypicalWord p n δx →
                            State (QIT.TensorPower a n)),
                        0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                          (1 - pruneε : ℝ) ≤
                            (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) ∧
                          (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                              ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                          (∀ x,
                            conditionalLogDeviationSecondMoment
                                (fun i : Fin n =>
                                  Classical.diagonalState
                                    (K.prob
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        p δx x i))
                                    (K.sum_eq_one
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        p δx x i))) /
                              ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                          (∀ x,
                            (N.tensorPower n).applyState (φ x) =
                              HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                K
                                (ClassicalTypicality.StrongTypicalWord.codeword p δx x)) ∧
                          2 * (packingε + 2 * Real.sqrt packingε) +
                              4 * ((Fintype.card M : ℝ) - 1) *
                                (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                  ((1 - pruneε) *
                                    (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                      n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, δx, δc, packingε, pruneε, φ,
    hδx, hδc, hpackingε, hprune, hmass_lower, hlarge, hmoment, houtput,
    hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    have hprune_pos : 0 < 1 - pruneε := by linarith
    have hmass_real_pos :
        0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
      lt_of_lt_of_le hprune_pos hmass_lower
    exact_mod_cast hmass_real_pos
  let Eout : Ensemble (ClassicalTypicality.StrongTypicalWord p n δx)
      (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        HSWPackingHypothesesSpectral.conditionalProductDiagonalState
          K (ClassicalTypicality.StrongTypicalWord.codeword p δx x) }
  refine ⟨α, inferInstance, inferInstance, p, K, δx, δc, packingε, pruneε,
    hmass_pos, Eout, φ, hδx, hδc, hpackingε, hprune, hmass_lower, ?_, ?_,
    hlarge, hmoment, ?_, hpacking_le⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    exact houtput x

/-- HSW direct-achievability assembly with the canonical pruned strongly-typical
codebook and **actual quantum channel outputs**.

The random-code alphabet is the strongly-typical subtype for the output
ensemble's inherited input law.  The input encoder is constructed internally as
the product input state `⊗ᵢ ρ_{xᵢ}`, and the output ensemble is the actual
product output `⊗ᵢ N(ρ_{xᵢ})`.  Therefore this theorem does not assume that a
general quantum output state is diagonal.

The remaining hypotheses are the genuine HSW spectral estimates: pack-1
cross-capture by the average-output typical projector, a uniform conditional
log-deviation bound for pack-2, and the final packing-error exponent.  Pack-3
and pruned pack-4 are discharged internally. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δavg : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 ≤ δx ∧ 0 < δavg ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (1 - pruneε : ℝ) ≤
                        (ClassicalTypicality.strongTypicalMass
                          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        1 - packingε ≤
                          ((((N.outputEnsemble E₀).averageState.typicalSubspaceProjector
                              n δavg) *
                            (productState fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)).matrix).trace).re) ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) +
                          4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                Real.rpow 2
                                  ((n : ℝ) * (N.outputEnsemble E₀).averageState.vonNeumann -
                                    (n : ℝ) * δavg))) ≤
                            ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δavg, δc, packingε, pruneε, hδx, hδavg, hδc, hpackingε,
    hprune, hmass_lower, hpack1, hmoment, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  let p := (N.outputEnsemble E₀).indexDistribution
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hmass_pos_real :
      0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
    lt_of_lt_of_le hprune_pos hmass_lower
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    exact_mod_cast hmass_pos_real
  let Eout : Ensemble 𝒳 (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        productState fun i : Fin n =>
          (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i) }
  let φ : 𝒳 → State (QIT.TensorPower a n) := fun x =>
    productState fun i : Fin n =>
      E₀.states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)
  let σbar := (N.outputEnsemble E₀).averageState
  let baseD : ℝ := Real.rpow 2 ((n : ℝ) * σbar.vonNeumann - (n : ℝ) * δavg)
  let D : ℝ := (1 - pruneε) * baseD
  let P : CMatrix (QIT.TensorPower b n) := σbar.typicalSubspaceProjector n δavg
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
      δc
  have hbaseD_pos : 0 < baseD := by
    dsimp [baseD]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hprune_pos hbaseD_pos
  let H : HSWPackingHypothesesSpectral Eout δavg := {
    P := P
    Px := Px
    d := (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc
    D := D
    ε := packingε
    hε_nonneg := hpackingε
    hD_pos := hD_pos
    P_posSemidef := by
      dsimp [P, σbar]
      exact (N.outputEnsemble E₀).averageState.typicalSubspaceProjector_posSemidef n δavg
    P_idempotent := by
      dsimp [P, σbar]
      exact (N.outputEnsemble E₀).averageState.typicalSubspaceProjector_idempotent n δavg
    P_le_one := by
      dsimp [P, σbar]
      exact (N.outputEnsemble E₀).averageState.typicalSubspaceProjector_le_one n δavg
    Px_projector := by
      intro x
      dsimp [Px]
      exact ⟨
        conditionallyTypicalSubspaceProjector_posSemidef
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_idempotent
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_le_one
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc⟩
    h1 := by
      intro x
      dsimp [P, Eout, σbar]
      exact hpack1 x
    h2 := by
      intro x
      dsimp [Px, Eout]
      have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
        (states := fun i : Fin n =>
          (N.outputEnsemble E₀).states
            (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
        (δ := δc) hn_pos hδc
      have hkey :
          1 - packingε ≤
            1 - conditionalLogDeviationSecondMoment
                (fun i : Fin n =>
                  (N.outputEnsemble E₀).states
                    (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) /
              ((n : ℝ) * δc) ^ 2 := by
        linarith [hmoment x]
      exact le_trans hkey hown
    h3 := by
      intro x
      dsimp [Px]
      rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
      exact conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
        (E := N.outputEnsemble E₀)
        (codeword := ClassicalTypicality.StrongTypicalWord.codeword p δx x)
        hn_pos hδx hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
    h4 := by
      have hσbar :
          σbar.matrix =
            ∑ j, (p.prob j) • ((N.outputEnsemble E₀).states j).matrix := by
        dsimp [σbar, p, Ensemble.indexDistribution]
        rfl
      have hpruned :
          Eout.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
        exact pack4_prunedStrongTypicalReduction
          (fun j => (N.outputEnsemble E₀).states j) p σbar hσbar hmass_pos
          hmass_lower hprune Eout (by intro x; rfl) (by intro x; rfl)
      have hprojected :
          P * (σbar.tensorPower n).matrix * P ≤ ((baseD : ℝ)⁻¹) • P := by
        have hpack4 :=
          averageState_typicalProjector_projectedAvgState_le
            (n := n) (N.outputEnsemble E₀) δavg
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hpack4
        dsimp [P, σbar, baseD]
        exact_mod_cast hpack4
      have hP_herm : P.IsHermitian := by
        dsimp [P, σbar]
        exact ((N.outputEnsemble E₀).averageState.typicalSubspaceProjector_posSemidef
          n δavg).isHermitian
      have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := inv_nonneg.mpr hprune_pos.le
      have hbase :
          P * Eout.averageState.matrix * P ≤
            (((1 - pruneε)⁻¹ : ℝ) * ((baseD : ℝ)⁻¹)) • P :=
        cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
          hP_herm hinv_nonneg hpruned hprojected
      have hscalar :
          (((1 - pruneε)⁻¹ : ℝ) * ((baseD : ℝ)⁻¹)) = ((D : ℝ)⁻¹) := by
        dsimp [D]
        field_simp [ne_of_gt hprune_pos, ne_of_gt hbaseD_pos]
      simpa [hscalar] using hbase }
  refine ⟨𝒳, inferInstance, inferInstance, Eout, δavg, H, φ, ?_, ?_⟩
  · intro x
    dsimp [φ, Eout, p]
    exact tensorPower_applyState_productState N n
      (fun i : Fin n => E₀.states
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x i))
  · dsimp [H, D, baseD, σbar]
    exact hpacking_le

/-- HSW direct-achievability assembly with the canonical pruned strongly-typical
codebook, actual quantum channel outputs, and the source-shaped average-output
projector.

Compared with
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates`,
this theorem no longer asks the caller for a legacy spectral average-projector
cross-capture estimate or a separate `δavg`.  The total projector is the
source-shaped eigenbasis strong-typical projector of the average output state,
with slack `(card ι) * (δx + δc)`.  Pack-1 follows from the proved
source-projector capture theorem, and pack-4 follows from the source projector
mass-scale estimate plus the pruned-distribution domination prefactor.

The remaining hypotheses are exactly the still-external asymptotic ingredients
for the HSW direct route: the strongly-typical mass lower bound, the conditional
log-deviation estimate for the conditionally-typical projectors, and the final
packing-error numerical inequality. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (1 - pruneε : ℝ) ≤
                        (ClassicalTypicality.strongTypicalMass
                          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) +
                          4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 2) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε,
    hprune, hmass_lower, hlarge, hmoment, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  let p := (N.outputEnsemble E₀).indexDistribution
  let δz : ℝ := (Fintype.card ι : ℝ) * (δx + δc)
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hmass_pos_real :
      0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
    lt_of_lt_of_le hprune_pos hmass_lower
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    exact_mod_cast hmass_pos_real
  let Eout : Ensemble 𝒳 (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        productState fun i : Fin n =>
          (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i) }
  let φ : 𝒳 → State (QIT.TensorPower a n) := fun x =>
    productState fun i : Fin n =>
      E₀.states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)
  let σbar := (N.outputEnsemble E₀).averageState
  let scale : ℝ :=
    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution σbar).strongTypicalMassScale
      n δz
  let D : ℝ := (1 - pruneε) * scale
  let P : CMatrix (QIT.TensorPower b n) :=
    HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector σbar n δz
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
      δc
  have hδz : 0 ≤ δz := by
    dsimp [δz]
    have hcard : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsum : 0 ≤ δx + δc := by linarith
    exact mul_nonneg hcard hsum
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
      σbar).strongTypicalMassScale_pos n δz
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hprune_pos hscale_pos
  let H : HSWPackingHypothesesSpectral Eout δz := {
    P := P
    Px := Px
    d := (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc
    D := D
    ε := packingε
    hε_nonneg := hpackingε
    hD_pos := hD_pos
    P_posSemidef := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
        (N.outputEnsemble E₀).averageState n δz
    P_idempotent := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_idempotent
        (N.outputEnsemble E₀).averageState n δz
    P_le_one := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_le_one
        (N.outputEnsemble E₀).averageState n δz
    Px_projector := by
      intro x
      dsimp [Px]
      exact ⟨
        conditionallyTypicalSubspaceProjector_posSemidef
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_idempotent
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_le_one
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc⟩
    h1 := by
      intro x
      dsimp [P, Eout, σbar, p, δz]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_product_capture_of_strongTypical
        (N.outputEnsemble E₀)
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x)
        hn_pos hδx hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical
          (N.outputEnsemble E₀).indexDistribution δx x)
        hlarge
    h2 := by
      intro x
      dsimp [Px, Eout]
      have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
        (states := fun i : Fin n =>
          (N.outputEnsemble E₀).states
            (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
        (δ := δc) hn_pos hδc
      have hkey :
          1 - packingε ≤
            1 - conditionalLogDeviationSecondMoment
                (fun i : Fin n =>
                  (N.outputEnsemble E₀).states
                    (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) /
              ((n : ℝ) * δc) ^ 2 := by
        linarith [hmoment x]
      exact le_trans hkey hown
    h3 := by
      intro x
      dsimp [Px]
      rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
      exact conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
        (E := N.outputEnsemble E₀)
        (codeword := ClassicalTypicality.StrongTypicalWord.codeword p δx x)
        hn_pos hδx hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
    h4 := by
      have hσbar :
          σbar.matrix =
            ∑ j, (p.prob j) • ((N.outputEnsemble E₀).states j).matrix := by
        dsimp [σbar, p, Ensemble.indexDistribution]
        rfl
      have hpruned :
          Eout.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
        exact pack4_prunedStrongTypicalReduction
          (fun j => (N.outputEnsemble E₀).states j) p σbar hσbar hmass_pos
          hmass_lower hprune Eout (by intro x; rfl) (by intro x; rfl)
      have hprojected :
          P * (σbar.tensorPower n).matrix * P ≤ ((scale : ℝ)⁻¹) • P := by
        dsimp [P, σbar, scale]
        exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_projectedTensorPower_le_strongTypicalMassScale
          (N.outputEnsemble E₀).averageState hn_pos hδz
      have hP_herm : P.IsHermitian := by
        dsimp [P, σbar]
        exact (HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
          (N.outputEnsemble E₀).averageState n δz).isHermitian
      have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := inv_nonneg.mpr hprune_pos.le
      have hbase :
          P * Eout.averageState.matrix * P ≤
            (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) • P :=
        cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
          hP_herm hinv_nonneg hpruned hprojected
      have hscalar :
          (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) = ((D : ℝ)⁻¹) := by
        dsimp [D]
        field_simp [ne_of_gt hprune_pos, ne_of_gt hscale_pos]
      simpa [hscalar] using hbase }
  refine ⟨𝒳, inferInstance, inferInstance, Eout, δz, H, φ, ?_, ?_⟩
  · intro x
    dsimp [φ, Eout, p]
    exact tensorPower_applyState_productState N n
      (fun i : Fin n => E₀.states
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x i))
  · dsimp [H, D, scale, σbar, δz]
    exact hpacking_le

/-- HSW direct-achievability assembly from the canonical source-projector
route with the final packing-error estimate split into its self-error and
cross-error components.

This theorem is logically equivalent to
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds`
at the assembly layer, but exposes the two asymptotic tasks separately: the
Hayashi-Nagaoka/self term and the cross-codeword packing exponent.  Later HSW
proof leaves discharge these two estimates by different large-block arguments,
so keeping them separated avoids a monolithic opaque numerical hypothesis. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (1 - pruneε : ℝ) ≤
                        (ClassicalTypicality.strongTypicalMass
                          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                      4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 4) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine
    N.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds
      E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_lower, hlarge, hmoment, hself, hcross⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  refine ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_lower, hlarge, hmoment, ?_⟩
  exact hswPackingError_le_of_self_cross_bound hself hcross

/-- HSW direct-achievability assembly from the canonical source-projector
route, with the strongly-typical codebook mass lower bound discharged by the
finite Chebyshev/union-bound estimate for input strong typicality.

The caller now supplies the explicit large-block condition
`|X|/(n δ_x²) ≤ pruneε`; the theorem proves
`1 - pruneε ≤ P[Xⁿ strongly typical]` internally. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤ pruneε ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                      4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 4) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine
    N.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds
      E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_large, hlarge, hmoment, hself, hcross⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  have hmass0 :
      1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) :=
    ClassicalTypicality.strongTypicalMass_ge_one_sub_card_bound
      (p := (N.outputEnsemble E₀).indexDistribution) hn_pos hδx
  have hmass_lower :
      (1 - pruneε : ℝ) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) := by
    have hleft :
        (1 - pruneε : ℝ) ≤
          1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) := by
      linarith
    exact le_trans hleft hmass0
  refine ⟨δx, δc, packingε, pruneε, hδx.le, hδc, hpackingε, hprune,
    hmass_lower, hlarge, hmoment, hself, hcross⟩

/-- HSW direct-achievability assembly from the canonical source-projector
route, with both the strongly-typical codebook mass and the message-cardinality
rate accounting discharged internally.

Compared with
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds`,
the final cross-error estimate is stated with the source proof's exponential
rate factor `2^{n(χ-δ/2)}`.  The theorem chooses the message set using
`hswMessageRate.exists_finite_message_type_rate_ge_card_sub_one_le`, then uses
the proved `|M|-1` bound to recover the packing lemma's actual cross term. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
    (N : Channel a b) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                (Fintype.card M : ℝ) - 1 ≤
                  Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤ pruneε ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                      4 * Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 4) :
    N.IsAchievableClassicalRate (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimatesWithCardBound E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate hcard
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_large, hlarge, hmoment, hself, hcrossCap⟩ :=
      hpack M hMfin hMdec hMnonempty hrate hcard
  let p := (N.outputEnsemble E₀).indexDistribution
  let δz : ℝ := (Fintype.card ι : ℝ) * (δx + δc)
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  have hmass0 :
      1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) :=
    ClassicalTypicality.strongTypicalMass_ge_one_sub_card_bound
      (p := (N.outputEnsemble E₀).indexDistribution) hn_pos hδx
  have hmass_lower :
      (1 - pruneε : ℝ) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) := by
    have hleft :
        (1 - pruneε : ℝ) ≤
          1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) := by
      linarith
    exact le_trans hleft hmass0
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hmass_pos_real :
      0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
    lt_of_lt_of_le hprune_pos hmass_lower
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    exact_mod_cast hmass_pos_real
  let Eout : Ensemble 𝒳 (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        productState fun i : Fin n =>
          (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i) }
  let φ : 𝒳 → State (QIT.TensorPower a n) := fun x =>
    productState fun i : Fin n =>
      E₀.states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)
  let σbar := (N.outputEnsemble E₀).averageState
  let scale : ℝ :=
    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution σbar).strongTypicalMassScale
      n δz
  let D : ℝ := (1 - pruneε) * scale
  let P : CMatrix (QIT.TensorPower b n) :=
    HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector σbar n δz
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
      δc
  have hδz : 0 ≤ δz := by
    dsimp [δz]
    have hcardι : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsum : 0 ≤ δx + δc := by linarith
    exact mul_nonneg hcardι hsum
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
      σbar).strongTypicalMassScale_pos n δz
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hprune_pos hscale_pos
  let H : HSWPackingHypothesesSpectral Eout δz := {
    P := P
    Px := Px
    d := (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc
    D := D
    ε := packingε
    hε_nonneg := hpackingε
    hD_pos := hD_pos
    P_posSemidef := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
        (N.outputEnsemble E₀).averageState n δz
    P_idempotent := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_idempotent
        (N.outputEnsemble E₀).averageState n δz
    P_le_one := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_le_one
        (N.outputEnsemble E₀).averageState n δz
    Px_projector := by
      intro x
      dsimp [Px]
      exact ⟨
        conditionallyTypicalSubspaceProjector_posSemidef
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_idempotent
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_le_one
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc⟩
    h1 := by
      intro x
      dsimp [P, Eout, σbar, p, δz]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_product_capture_of_strongTypical
        (N.outputEnsemble E₀)
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x)
        hn_pos hδx.le hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical
          (N.outputEnsemble E₀).indexDistribution δx x)
        hlarge
    h2 := by
      intro x
      dsimp [Px, Eout]
      have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
        (states := fun i : Fin n =>
          (N.outputEnsemble E₀).states
            (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
        (δ := δc) hn_pos hδc
      have hkey :
          1 - packingε ≤
            1 - conditionalLogDeviationSecondMoment
                (fun i : Fin n =>
                  (N.outputEnsemble E₀).states
                    (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) /
              ((n : ℝ) * δc) ^ 2 := by
        linarith [hmoment x]
      exact le_trans hkey hown
    h3 := by
      intro x
      dsimp [Px]
      rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
      exact conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
        (E := N.outputEnsemble E₀)
        (codeword := ClassicalTypicality.StrongTypicalWord.codeword p δx x)
        hn_pos hδx.le hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
    h4 := by
      have hσbar :
          σbar.matrix =
            ∑ j, (p.prob j) • ((N.outputEnsemble E₀).states j).matrix := by
        dsimp [σbar, p, Ensemble.indexDistribution]
        rfl
      have hpruned :
          Eout.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
        exact pack4_prunedStrongTypicalReduction
          (fun j => (N.outputEnsemble E₀).states j) p σbar hσbar hmass_pos
          hmass_lower hprune Eout (by intro x; rfl) (by intro x; rfl)
      have hprojected :
          P * (σbar.tensorPower n).matrix * P ≤ ((scale : ℝ)⁻¹) • P := by
        dsimp [P, σbar, scale]
        exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_projectedTensorPower_le_strongTypicalMassScale
          (N.outputEnsemble E₀).averageState hn_pos hδz
      have hP_herm : P.IsHermitian := by
        dsimp [P, σbar]
        exact (HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
          (N.outputEnsemble E₀).averageState n δz).isHermitian
      have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := inv_nonneg.mpr hprune_pos.le
      have hbase :
          P * Eout.averageState.matrix * P ≤
            (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) • P :=
        cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
          hP_herm hinv_nonneg hpruned hprojected
      have hscalar :
          (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) = ((D : ℝ)⁻¹) := by
        dsimp [D]
        field_simp [ne_of_gt hprune_pos, ne_of_gt hscale_pos]
      simpa [hscalar] using hbase }
  refine ⟨𝒳, inferInstance, inferInstance, Eout, δz, H, φ, ?_, ?_⟩
  · intro x
    dsimp [φ, Eout, p]
    exact tensorPower_applyState_productState N n
      (fun i : Fin n => E₀.states
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x i))
  · have hratio_nonneg :
        0 ≤
          (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
            ((1 - pruneε) * scale) := by
      have hd_nonneg :
          0 ≤ (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc := by
        dsimp [Ensemble.strongTypicalDimensionEnvelope]
        exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      exact div_nonneg hd_nonneg hD_pos.le
    have hcross_actual :
        4 * ((Fintype.card M : ℝ) - 1) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) ≤
          4 * Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) := by
      have hmul := mul_le_mul_of_nonneg_right hcard hratio_nonneg
      nlinarith
    have hcross :
        4 * ((Fintype.card M : ℝ) - 1) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) ≤ ε / 4 := by
      exact le_trans hcross_actual hcrossCap
    have htotal := hswPackingError_le_of_self_cross_bound hself hcross
    dsimp [H, D, scale, σbar, δz]
    exact htotal

/-- Block-channel achievability transports to the original channel with the
standard rate normalization.

For an `S`-rate code family for the block channel `N^{⊗ k}`, this theorem
constructs `S/k`-rate codes for `N`: for a large requested length `ℓ`, write
`ℓ = t*k + r`, use a `t`-use block-channel code, flatten it to `t*k` uses of
`N`, and right-pad the remaining `r` uses with a fixed input state.  The proof
keeps the padding rate loss explicit and absorbs it into the operational
achievability slack. -/
theorem hsw_blockChannelAchievable_transport [Nonempty a]
    (N : Channel a b) (k : ℕ) (hk : 0 < k) (S : ℝ)
    (hS : (N.tensorPower k).IsAchievableClassicalRate S) :
    N.IsAchievableClassicalRate (S / (k : ℝ)) := by
  intro δ hδ ε hε
  have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk
  let blockSlack : ℝ := (k : ℝ) * (δ / 4)
  have hblockSlack_pos : 0 < blockSlack := by
    dsimp [blockSlack]
    positivity
  obtain ⟨T0, hT0⟩ := hS blockSlack hblockSlack_pos ε hε
  by_cases htarget_nonpos : S / (k : ℝ) - δ ≤ 0
  · let L : ℕ := max T0 1
    refine ⟨(L + 1) * k, ?_⟩
    intro ℓ hℓ
    let t : ℕ := ℓ / k
    let r : ℕ := ℓ % k
    have hL1_le_t : L + 1 ≤ t := by
      dsimp [t]
      exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hℓ)
    have ht_pos : 0 < t := lt_of_lt_of_le (Nat.succ_pos L) hL1_le_t
    have hL_le_t : L ≤ t := (Nat.le_succ L).trans hL1_le_t
    have ht_ge_T0 : t ≥ T0 := (Nat.le_max_left T0 1).trans hL_le_t
    obtain ⟨M, hMfin, hMdec, hMnonempty, C, hrateC, herrC⟩ := hT0 t ht_ge_T0
    letI : Fintype M := hMfin
    letI : DecidableEq M := hMdec
    letI : Nonempty M := hMnonempty
    let tail : State (QIT.TensorPower a r) := tensorPowerBasisState a r
    let Cpad : HSWClassicalCode N (t * k + r) M := C.flattenBlock.padRight tail
    have hlen : t * k + r = ℓ := by
      dsimp [t, r]
      simpa [Nat.mul_comm] using Nat.div_add_mod ℓ k
    let Cfinal : HSWClassicalCode N ℓ M := Cpad.castLength hlen
    have hrate_final : Cfinal.rate ≥ S / (k : ℝ) - δ := by
      have hnonneg : 0 ≤ Cpad.rate := by
        dsimp [Cpad, HSWClassicalCode.rate]
        exact hswMessageRate.nonneg (M := M) (t * k + r)
      simpa [Cfinal] using (show Cpad.rate ≥ S / (k : ℝ) - δ by linarith)
    have herr_pad : Cpad.maxErrorAtMost ε := by
      dsimp [Cpad]
      exact (C.flattenBlock).padRight_maxErrorAtMost tail (C.flattenBlock_maxErrorAtMost herrC)
    have herr_final : Cfinal.maxErrorAtMost ε := by
      dsimp [Cfinal]
      exact Cpad.castLength_maxErrorAtMost hlen herr_pad
    exact ⟨M, inferInstance, inferInstance, inferInstance, Cfinal, hrate_final, herr_final⟩
  · let B : ℝ := S / (k : ℝ) - δ
    have hB_pos : 0 < B := lt_of_not_ge htarget_nonpos
    let X : ℝ := (4 * B) / (3 * δ)
    let L : ℕ := max T0 (Nat.ceil X)
    refine ⟨(L + 1) * k, ?_⟩
    intro ℓ hℓ
    let t : ℕ := ℓ / k
    let r : ℕ := ℓ % k
    have hL1_le_t : L + 1 ≤ t := by
      dsimp [t]
      exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hℓ)
    have ht_pos : 0 < t := lt_of_lt_of_le (Nat.succ_pos L) hL1_le_t
    have hL_le_t : L ≤ t := (Nat.le_succ L).trans hL1_le_t
    have ht_ge_T0 : t ≥ T0 := (Nat.le_max_left T0 (Nat.ceil X)).trans hL_le_t
    obtain ⟨M, hMfin, hMdec, hMnonempty, C, hrateC, herrC⟩ := hT0 t ht_ge_T0
    letI : Fintype M := hMfin
    letI : DecidableEq M := hMdec
    letI : Nonempty M := hMnonempty
    let tail : State (QIT.TensorPower a r) := tensorPowerBasisState a r
    let Cpad : HSWClassicalCode N (t * k + r) M := C.flattenBlock.padRight tail
    let A : ℝ := S / (k : ℝ) - δ / 4
    have hbase : A ≤ C.rate / (k : ℝ) := by
      have hdiv :
          (S - blockSlack) / (k : ℝ) ≤ C.rate / (k : ℝ) :=
        div_le_div_of_nonneg_right hrateC hkR_pos.le
      have hslack :
          (S - blockSlack) / (k : ℝ) = S / (k : ℝ) - δ / 4 := by
        dsimp [blockSlack]
        field_simp [ne_of_gt hkR_pos]
      simpa [A, hslack] using hdiv
    have hceil_le_t : Nat.ceil X ≤ t :=
      (Nat.le_max_right T0 (Nat.ceil X)).trans hL_le_t
    have hX_le_t : X ≤ (t : ℝ) := by
      exact (Nat.le_ceil X).trans (by exact_mod_cast hceil_le_t)
    have hcoeff_pos : 0 < (3 * δ / 4 : ℝ) := by positivity
    have hBt : B ≤ (3 * δ / 4) * (t : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hX_le_t (le_of_lt hcoeff_pos)
      have hcalc : (3 * δ / 4 : ℝ) * ((4 * B) / (3 * δ)) = B := by
        field_simp [ne_of_gt hδ]
      simpa [X, hcalc] using hmul
    have hr_le_k : (r : ℝ) ≤ (k : ℝ) := by
      have hr_lt : r < k := by
        dsimp [r]
        exact Nat.mod_lt ℓ hk
      exact_mod_cast le_of_lt hr_lt
    have hpadding_loss :
        B * (r : ℝ) ≤ (3 * δ / 4) * (t : ℝ) * (k : ℝ) := by
      have h1 : B * (r : ℝ) ≤ B * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hr_le_k hB_pos.le
      have h2 : B * (k : ℝ) ≤ ((3 * δ / 4) * (t : ℝ)) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hBt hkR_pos.le
      exact h1.trans h2
    have hden_pos : (0 : ℝ) < ((t * k + r : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_pos_left (Nat.mul_pos ht_pos hk) r
    have hratio :
        B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      refine (le_div_iff₀ hden_pos).mpr ?_
      norm_num [Nat.cast_add, Nat.cast_mul]
      have hAeq : A = B + 3 * δ / 4 := by
        dsimp [A, B]
        ring
      calc
        B * ((t : ℝ) * (k : ℝ) + (r : ℝ)) =
            B * (r : ℝ) + B * ((t : ℝ) * (k : ℝ)) := by ring
        _ ≤ (3 * δ / 4) * (t : ℝ) * (k : ℝ) +
              B * ((t : ℝ) * (k : ℝ)) :=
            by
              have h := add_le_add_right hpadding_loss (B * ((t : ℝ) * (k : ℝ)))
              simpa [add_comm, add_left_comm, add_assoc] using h
        _ = (B + 3 * δ / 4) * ((t : ℝ) * (k : ℝ)) := by ring
        _ = A * ((t : ℝ) * (k : ℝ)) := by rw [hAeq]
    have hrate_final : Cpad.rate ≥ S / (k : ℝ) - δ := by
      dsimp [B] at hB_pos
      have hB_rate :
          B ≤ Cpad.rate := by
        dsimp [Cpad]
        exact C.flattenBlock_padRight_rate_ge_of_ratio tail ht_pos hk hbase hratio
      simpa [B] using hB_rate
    have herr_final : Cpad.maxErrorAtMost ε := by
      dsimp [Cpad]
      exact (C.flattenBlock).padRight_maxErrorAtMost tail (C.flattenBlock_maxErrorAtMost herrC)
    have hlen : t * k + r = ℓ := by
      dsimp [t, r]
      simpa [Nat.mul_comm] using Nat.div_add_mod ℓ k
    let Cfinal : HSWClassicalCode N ℓ M := Cpad.castLength hlen
    have hrate_final' : Cfinal.rate ≥ S / (k : ℝ) - δ := by
      simpa [Cfinal] using hrate_final
    have herr_final' : Cfinal.maxErrorAtMost ε := by
      dsimp [Cfinal]
      exact Cpad.castLength_maxErrorAtMost hlen herr_final
    exact ⟨M, inferInstance, inferInstance, inferInstance, Cfinal, hrate_final', herr_final'⟩

/-- Regularized HSW direct achievability with the block-channel transport
obligation discharged by `hsw_blockChannelAchievable_transport`.

This is the block-to-regularized bridge: once every positive block channel has
ensemble-specific HSW direct coding at its one-letter Holevo rate, the
regularized direct half for the original channel follows. -/
theorem hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblockEnsemble :
      ∀ n : ℕ, 0 < n →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E : Ensemble ι (QIT.TensorPower a n),
            (N.tensorPower n).IsAchievableClassicalRate
              ((N.tensorPower n).hswHolevoRate E)) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R :=
  N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses
    (fun n hn S hS => N.hsw_blockChannelAchievable_transport n hn S hS)
    hblockEnsemble

/-- HSW regularized direct achievability from source-shaped spectral packing
families for every block channel.

For every block size `k`, finite input ensemble for `N^{⊗ k}`, slack `δ`, and
target error `ε`, the hypothesis supplies the eventual spectral packing bundle
needed by `hsw_directWitnessAssembly_from_spectralPackingHypotheses` for the
block channel.  The theorem then performs both remaining assembly steps:
ensemble-specific direct coding for each block channel and the
block-to-base rate-normalization transport. -/
theorem hsw_regularized_direct_of_blockSpectralPackingHypotheses
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
                    ∃ (_ : Nonempty M),
                      ∃ (𝒳 : Type u), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                        ∃ (Eout :
                            Ensemble 𝒳 (QIT.TensorPower (QIT.TensorPower b k) n)),
                          ∃ (typicalitySlack : ℝ),
                            ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                              ∃ (φ :
                                  𝒳 → State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                (∀ x,
                                    ((N.tensorPower k).tensorPower n).applyState (φ x) =
                                      Eout.states x) ∧
                                  hswMessageRate M n ≥
                                    (N.tensorPower k).hswHolevoRate E₀ - δ / 2 ∧
                                    2 * (H.ε + 2 * Real.sqrt H.ε) +
                                        4 * ((Fintype.card M : ℝ) - 1) *
                                          (H.d / H.D) ≤
                                      ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_spectralPackingHypotheses E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel spectral packing
estimates, with the finite message set chosen internally at every coding block
length.

This theorem is the strict direct-achievability assembly point closest to the
remaining source proof obligations: the caller supplies the asymptotic HSW
typical/packing estimates for the message type selected by the rate lemma, and
this theorem performs message-size choice, packing/expurgation assembly,
block-channel ensemble coding, and block-to-base rate normalization. -/
theorem hsw_regularized_direct_of_blockSpectralPackingEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (𝒳 : Type u), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                        ∃ (Eout :
                            Ensemble 𝒳 (QIT.TensorPower (QIT.TensorPower b k) n)),
                          ∃ (typicalitySlack : ℝ),
                            ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                              ∃ (φ :
                                  𝒳 → State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                (∀ x,
                                    ((N.tensorPower k).tensorPower n).applyState (φ x) =
                                      Eout.states x) ∧
                                  2 * (H.ε + 2 * Real.sqrt H.ε) +
                                      4 * ((Fintype.card M : ℝ) - 1) *
                                        (H.d / H.D) ≤
                                    ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_spectralPackingEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel diagonal
strong-typical packing estimates.

This is the highest direct-achievability assembly point available for the
source-shaped diagonal route formalized in `ConditionalTypicality.lean`.  For
each positive block size `k`, the caller supplies the diagonal/pinched strong
typical estimates for the block channel `N^{⊗ k}`; this theorem then applies
the one-block diagonal assembly theorem and the already-proved
block-to-base-channel rate normalization.

The statement deliberately keeps the diagonal/pinching and asymptotic
typical-estimate family explicit.  It does not identify the diagonal
strong-typical projector with the legacy spectral projector, and it does not
pretend that arbitrary quantum output ensembles have already been reduced to
the pinched classical kernel. -/
theorem hsw_regularized_direct_of_blockDiagonalPackingEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (𝒳 : Type u), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                              ∃ (Eout :
                                  Ensemble 𝒳 (QIT.TensorPower (QIT.TensorPower b k) n)),
                                ∃ (codewordOf : 𝒳 → Fin n → α),
                                  ∃ (φ :
                                      𝒳 →
                                        State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                      ∃ (d : ℝ), ∃ (D : ℝ),
                                        ∃ (Px :
                                            𝒳 →
                                              CMatrix
                                                (QIT.TensorPower
                                                  (QIT.TensorPower b k) n)),
                                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                            (∀ x,
                                              (Eout.states x).matrix =
                                                (HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                                  K
                                                  (codewordOf x)).matrix) ∧
                                            (∀ x,
                                              ClassicalTypicality.StrongTypical p
                                                (codewordOf x) δx) ∧
                                            (Fintype.card α : ℝ) *
                                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                            (∀ x,
                                              (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                                Px x ≤ 1) ∧
                                            (∀ x,
                                              1 - packingε ≤
                                                ((Px x * (Eout.states x).matrix).trace).re) ∧
                                            (∀ x, ((Px x).trace).re ≤ d) ∧
                                            (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                                  (ClassicalTypicality.inducedMarginal p K)
                                                  n
                                                  ((Fintype.card α : ℝ) * (δx + δc)) *
                                                Eout.averageState.matrix *
                                                HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                                  (ClassicalTypicality.inducedMarginal p K)
                                                  n
                                                  ((Fintype.card α : ℝ) * (δx + δc))
                                                ≤ ((D : ℝ)⁻¹) •
                                                  HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                                    (ClassicalTypicality.inducedMarginal p K)
                                                    n
                                                    ((Fintype.card α : ℝ) * (δx + δc))) ∧
                                            (∀ x,
                                              ((N.tensorPower k).tensorPower n).applyState
                                                  (φ x) =
                                                Eout.states x) ∧
                                            2 * (packingε + 2 * Real.sqrt packingε) +
                                                4 * ((Fintype.card M : ℝ) - 1) * (d / D) ≤
                                              ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
strong-typical packing estimates.

This is the regularized direct-achievability entry point for the source-shaped
post-pinching/pruned-distribution route: for every positive block channel
`N^{⊗ k}`, finite input ensemble, and sufficiently large random-coding block
length, the caller supplies the pruned conditional-product estimates.  The
proved pruned pack-4 bridge supplies the projected-average Loewner bound, the
one-block HSW assembly supplies an achievable block-channel Holevo rate, and
the block-transport theorem normalizes the rate back to the original channel.

The theorem still keeps the genuinely asymptotic HSW estimates explicit:
typical-codeword selection, conditionally-typical projectors, marginal-product
mass envelopes, physical output realizations, and final packing-error
inequality are not hidden or replaced by placeholders. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalPackingEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    ∃ (Px :
                                        (Fin n → α) →
                                          CMatrix
                                            (QIT.TensorPower
                                              (QIT.TensorPower b k) n)),
                                      0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                        pruneε < 1 ∧
                                        (∀ x : Fin n → α,
                                          Eout.states x =
                                            HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                              K x) ∧
                                        (∀ x : Fin n → α,
                                          ClassicalTypicality.StrongTypical p x δx) ∧
                                        (Fintype.card α : ℝ) *
                                            (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                            ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                        (∀ x : Fin n → α,
                                          (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                            Px x ≤ 1) ∧
                                        (∀ x : Fin n → α,
                                          1 - packingε ≤
                                            ((Px x * (Eout.states x).matrix).trace).re) ∧
                                        (∀ x : Fin n → α, ((Px x).trace).re ≤ d) ∧
                                        (∀ zseq : Fin n → QIT.TensorPower b k,
                                          ClassicalTypicality.StrongTypical
                                              (ClassicalTypicality.inducedMarginal p K)
                                              zseq
                                              ((Fintype.card α : ℝ) * (δx + δc)) →
                                            (HSWPackingHypothesesSpectral.marginalProductMass
                                              (ClassicalTypicality.inducedMarginal p K)
                                              zseq : ℝ) ≤ D⁻¹) ∧
                                        (∀ x : Fin n → α,
                                          (Eout.probs x : ℝ) ≤
                                            (1 - pruneε)⁻¹ *
                                              ∏ i, (p.prob (x i) : ℝ)) ∧
                                        (∀ x : Fin n → α,
                                          ((N.tensorPower k).tensorPower n).applyState
                                              (φ x) =
                                            Eout.states x) ∧
                                        2 * (packingε + 2 * Real.sqrt packingε) +
                                            4 * ((Fintype.card M : ℝ) - 1) *
                                              (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
conditionally-typical projector estimates.

Compared with `hsw_regularized_direct_of_blockPrunedDiagonalPackingEstimates`,
this entry point no longer asks the caller to construct arbitrary per-codeword
projectors.  It instantiates the projectors as the conditionally typical
subspace projectors and consumes the source-shaped second-moment and dimension
estimates instead.  The remaining explicit assumptions are precisely the
unproved asymptotic HSW ingredients that are not part of this bridge:
strong-typical codewords, marginal-product mass envelope, pruned distribution
domination, physical output realization, and the final packing-error
inequality. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      (∀ x : Fin n → α,
                                        conditionallyTypicalSubspaceDimension
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i)))
                                            δc ≤ d) ∧
                                      (∀ zseq : Fin n → QIT.TensorPower b k,
                                        ClassicalTypicality.StrongTypical
                                            (ClassicalTypicality.inducedMarginal p K)
                                            zseq
                                            ((Fintype.card α : ℝ) * (δx + δc)) →
                                          (HSWPackingHypothesesSpectral.marginalProductMass
                                            (ClassicalTypicality.inducedMarginal p K)
                                            zseq : ℝ) ≤ D⁻¹) ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
conditionally-typical projector estimates with the pack-4 mass bound discharged
by the finite classical entropy envelope.

This is the current source-shaped direct-achievability assembly point for the
diagonal/pruned route: the caller supplies the HSW asymptotic estimates and the
explicit entropy-exponent choice of `D`; the theorem derives the word-level
product-mass envelope, constructs the packing hypotheses, and transports the
block-channel codes back to the original channel. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorEntropyEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      (∀ x : Fin n → α,
                                        conditionallyTypicalSubspaceDimension
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i)))
                                            δc ≤ d) ∧
                                      Real.rpow 2
                                        (- (n : ℝ) *
                                            (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
                                          (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
                                            (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
                                          ≤ D⁻¹ ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates
    E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
projector estimates, with both pack-3 and pack-4 supplied by finite classical
typicality envelopes.

This is stronger than
`hsw_regularized_direct_of_blockPrunedDiagonalProjectorEntropyEstimates`: it no
longer requires a separate conditionally-typical-subspace dimension estimate in
the block-channel hypothesis.  The dimension term in the final packing-error
bound is the named value
`hswConditionalDiagonalDimensionEnvelope p K n δx δc`, derived from codeword
strong typicality. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorEntropyDimensionEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      Real.rpow 2
                                        (- (n : ℝ) *
                                            (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
                                          (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
                                            (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
                                          ≤ D⁻¹ ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (hswConditionalDiagonalDimensionEnvelope
                                                p K n δx δc /
                                              ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates
    E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
projector estimates with the canonical marginal-product mass scale chosen
internally.

This is the current strongest regularized direct-assembly interface in this
file: the caller supplies the HSW asymptotic random-coding/pruning estimates,
while pack-3's dimension envelope, pack-4's product-mass scale `D`, the
packing/expurgation assembly, and block-to-base rate normalization are all
proved here. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorTypicalityScaleEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (hswConditionalDiagonalDimensionEnvelope
                                                p K n δx δc /
                                              ((1 - pruneε) *
                                                (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                                  n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                            ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorTypicalityScaleEstimates
    E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel strongly-typical
pruned codebook estimates.

This is the regularized counterpart of
`hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates`.
It removes the impossible full-word assumption
`∀ x : Fin n → α, StrongTypical p x δx` from the block-level interface:
the random-coding index type is the strongly-typical subtype, while the
remaining independent source obligations are kept explicit. -/
theorem hsw_regularized_direct_of_blockStrongTypicalCodebookProjectorTypicalityScaleEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (Eout :
                                  Ensemble
                                    (ClassicalTypicality.StrongTypicalWord p n δx)
                                    (QIT.TensorPower (QIT.TensorPower b k) n)),
                                ∃ (φ :
                                    ClassicalTypicality.StrongTypicalWord p n δx →
                                      State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                  0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                    (∀ x,
                                      (Eout.states x).matrix =
                                        (HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                          K
                                          (ClassicalTypicality.StrongTypicalWord.codeword
                                            p δx x)).matrix) ∧
                                    (Fintype.card α : ℝ) *
                                        (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                        ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                    (∀ x,
                                      conditionalLogDeviationSecondMoment
                                          (fun i : Fin n =>
                                            Classical.diagonalState
                                              (K.prob
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))
                                              (K.sum_eq_one
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))) /
                                        ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                    (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K)
                                          n
                                          ((Fintype.card α : ℝ) * (δx + δc)) *
                                        Eout.averageState.matrix *
                                        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K)
                                          n
                                          ((Fintype.card α : ℝ) * (δx + δc))
                                        ≤
                                          (((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                              n ((Fintype.card α : ℝ) * (δx + δc))) : ℝ)⁻¹ •
                                            HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                              (ClassicalTypicality.inducedMarginal p K)
                                              n
                                              ((Fintype.card α : ℝ) * (δx + δc))) ∧
                                    (∀ x,
                                      ((N.tensorPower k).tensorPower n).applyState
                                          (φ x) =
                                        Eout.states x) ∧
                                    2 * (packingε + 2 * Real.sqrt packingε) +
                                        4 * ((Fintype.card M : ℝ) - 1) *
                                          (hswConditionalDiagonalDimensionEnvelope
                                              p K n δx δc /
                                            ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                              n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                          ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from canonical pruned strongly-typical
codebook estimates.

This is the strongest currently proved direct-achievability assembly theorem in
this module.  Compared with
`hsw_regularized_direct_of_blockStrongTypicalCodebookProjectorTypicalityScaleEstimates`,
the projected-average pack-4 hypothesis has been eliminated: it is derived from
the canonical pruned i.i.d. distribution on the strongly-typical subtype, and
the resulting effective denominator contains the source's `(1 - pruneε)`
factor. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (pruneε : ℝ),
                                ∃ (hmass_pos :
                                    0 < ClassicalTypicality.strongTypicalMass
                                      (n := n) p δx),
                                  ∃ (Eout :
                                      Ensemble
                                        (ClassicalTypicality.StrongTypicalWord p n δx)
                                        (QIT.TensorPower (QIT.TensorPower b k) n)),
                                    ∃ (φ :
                                        ClassicalTypicality.StrongTypicalWord p n δx →
                                          State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                      0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                        pruneε < 1 ∧
                                        (1 - pruneε : ℝ) ≤
                                          (ClassicalTypicality.strongTypicalMass
                                            (n := n) p δx : ℝ) ∧
                                        (∀ x,
                                          Eout.probs x =
                                            (ClassicalTypicality.prunedStrongTypicalDistribution
                                              p δx hmass_pos).prob x) ∧
                                        (∀ x,
                                          Eout.states x =
                                            HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                              K
                                              (ClassicalTypicality.StrongTypicalWord.codeword
                                                p δx x)) ∧
                                        (Fintype.card α : ℝ) *
                                            (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                            ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                        (∀ x,
                                          conditionalLogDeviationSecondMoment
                                              (fun i : Fin n =>
                                                Classical.diagonalState
                                                  (K.prob
                                                    (ClassicalTypicality.StrongTypicalWord.codeword
                                                      p δx x i))
                                                  (K.sum_eq_one
                                                    (ClassicalTypicality.StrongTypicalWord.codeword
                                                      p δx x i))) /
                                            ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                        (∀ x,
                                          ((N.tensorPower k).tensorPower n).applyState
                                              (φ x) =
                                            Eout.states x) ∧
                                        2 * (packingε + 2 * Real.sqrt packingε) +
                                            4 * ((Fintype.card M : ℝ) - 1) *
                                              (hswConditionalDiagonalDimensionEnvelope
                                                  p K n δx δc /
                                                ((1 - pruneε) *
                                                  (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                                    n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                              ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from canonical pruned strongly-typical
codebook bounds, with the pruned output ensemble constructed internally.

This is the regularized form of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleBounds`.
The block-level hypothesis now contains only the mathematical estimates that
are still genuinely external to this assembly layer: typical-set mass,
conditional log-deviation, physical output realization, and final numerical
packing exponent. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalCodebookProjectorTypicalityScaleBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type u), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (pruneε : ℝ),
                                ∃ (φ :
                                    ClassicalTypicality.StrongTypicalWord p n δx →
                                      State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                  0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                    pruneε < 1 ∧
                                    (1 - pruneε : ℝ) ≤
                                      (ClassicalTypicality.strongTypicalMass
                                        (n := n) p δx : ℝ) ∧
                                    (Fintype.card α : ℝ) *
                                        (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                        ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                    (∀ x,
                                      conditionalLogDeviationSecondMoment
                                          (fun i : Fin n =>
                                            Classical.diagonalState
                                              (K.prob
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))
                                              (K.sum_eq_one
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))) /
                                        ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                    (∀ x,
                                      ((N.tensorPower k).tensorPower n).applyState
                                          (φ x) =
                                        HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                          K
                                          (ClassicalTypicality.StrongTypicalWord.codeword
                                            p δx x)) ∧
                                    2 * (packingε + 2 * Real.sqrt packingε) +
                                        4 * ((Fintype.card M : ℝ) - 1) *
                                          (hswConditionalDiagonalDimensionEnvelope
                                              p K n δx δc /
                                            ((1 - pruneε) *
                                              (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                                n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                          ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleBounds
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct-achievability from source-shaped spectral estimates
for the canonical pruned strongly-typical codebook with actual quantum outputs.

This is the regularized/block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates`.
It removes the older diagonal-output realization hypothesis from the HSW direct
route: for each block ensemble of `N^{⊗ k}`, the random codebook is the
strongly-typical subtype of the induced input law and the encoder is the actual
product input state.  The remaining assumptions are exactly the still-external
asymptotic estimates for pack-1 cross-capture, conditional log-deviation, and
the final packing-error exponent. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSpectralEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δavg : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 ≤ δx ∧ 0 < δavg ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (1 - pruneε : ℝ) ≤
                              (ClassicalTypicality.strongTypicalMass
                                (n := n)
                                ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                δx : ℝ) ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              1 - packingε ≤
                                ((((N.tensorPower k).outputEnsemble E₀).averageState.typicalSubspaceProjector
                                    n δavg) *
                                  (productState fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)).matrix).trace.re) ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) +
                                4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      Real.rpow 2
                                        ((n : ℝ) *
                                            ((N.tensorPower k).outputEnsemble E₀).averageState.vonNeumann -
                                          (n : ℝ) * δavg))) ≤
                                  ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
for the canonical pruned strongly-typical codebook with actual quantum outputs.

This is the block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds`.
It keeps the remaining asymptotic estimates explicit but no longer asks the
caller for the legacy arbitrary spectral projector slack `δavg`: the average
projector is the source-shaped eigenbasis typical projector of the block
average output state, with denominator given by the canonical eigenvalue
strong-typical mass scale. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (1 - pruneε : ℝ) ≤
                              (ClassicalTypicality.strongTypicalMass
                                (n := n)
                                ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                δx : ℝ) ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) +
                                4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 2) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
with the final packing-error estimate split into self-error and cross-error
components.

This is the block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds`.
It is the preferred staging point for the remaining asymptotic HSW direct
proof: the codebook/source-projector construction has been internalized, and
the caller must now prove only the genuine large-block estimates for typical
mass, conditional log-deviation, self-error, and cross-error. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorComponentBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (1 - pruneε : ℝ) ≤
                              (ClassicalTypicality.strongTypicalMass
                                (n := n)
                                ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                δx : ℝ) ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact
    Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds
      (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
with the input strongly-typical mass discharged by its finite Chebyshev bound.

Compared with
`hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorComponentBounds`,
the block hypothesis no longer contains the strongly-typical codebook mass
lower bound.  It is replaced by the explicit large-block condition
`|X|/(nδ_x²) ≤ pruneε`. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                              pruneε ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact
    Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds
      (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
with both finite strong-typical mass and source-shaped message-cardinality
rate accounting discharged.

This is the block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound`.
It is the strongest assembly point in this file: after the caller proves the
remaining source estimates for conditional log-deviation, self-error, and the
cross exponent with the factor `2^{n(χ-δ/2)}`, this theorem performs the
message-set choice, packing/expurgation, block-channel coding, and
block-to-base-channel rate normalization. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                              pruneε ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * Real.rpow 2
                                  ((n : ℝ) *
                                    ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact
    Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
      (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability with the conditional log-deviation
estimate discharged by the finite ensemble second-moment envelope.

Compared with
`hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound`,
the block hypothesis no longer asks for a pointwise second-moment bound for
every strongly-typical codeword.  The proved non-iid product variance identity
in `ConditionalTypicality.lean` shows that every codeword product has centered
log-deviation second moment bounded by
`n * E.logDeviationSecondMomentEnvelope`; the caller only supplies the resulting
large-block ratio bound.  The older cardinal-dimensional moment condition is
still explicit at this stage and is removed by a later source-estimate layer. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelope
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                              pruneε ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope /
                                ((n : ℝ) * δc ^ 2) ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * Real.rpow 2
                                  ((n : ℝ) *
                                    ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨N0, hN0⟩ := hblock k hk ι inferInstance inferInstance E₀ δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hnN0
  obtain ⟨hn_pos, hn_small, hM⟩ := hN0 n hnN0
  refine ⟨hn_pos, hn_small, ?_⟩
  intro M hMF hMD hMne hrate hcard
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpack_nonneg, hprune_lt,
      hprune_mass, hcardMoment, hmoment, hself, hcross⟩ :=
    hM M inferInstance inferInstance hMne hrate hcard
  refine ⟨δx, δc, packingε, pruneε, hδx, hδc, hpack_nonneg, hprune_lt,
    hprune_mass, hcardMoment, ?_, hself, hcross⟩
  intro x
  exact
    (((N.tensorPower k).outputEnsemble E₀).conditionalLogDeviationSecondMoment_codeword_ratio_le_of_envelope
      (fun i : Fin n =>
        ClassicalTypicality.StrongTypicalWord.codeword
          (((N.tensorPower k).outputEnsemble E₀).indexDistribution) δx x i)
      hn_pos hδc hmoment)

/-- Regularized HSW direct achievability with the self-error parameter fixed
explicitly from the requested error tolerance.

This removes the ad hoc `packingε` and `pruneε` choices from the block
hypothesis.  The caller now proves only the large-block source estimates using
the concrete choices `packingε = hswSelfPackingEpsilon ε` and `pruneε = 1/2`. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelopeFixedSelfError
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        0 < δx ∧ 0 < δc ∧
                          (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                            (1 / 2 : ℝ) ∧
                          (Fintype.card ι : ℝ) *
                              (Fintype.card (QIT.TensorPower b k) : ℝ) /
                              ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε ∧
                          (((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope /
                              ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε) ∧
                          4 * Real.rpow 2
                                ((n : ℝ) *
                                  ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                                (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                    n δx δc /
                                  ((1 - (1 / 2 : ℝ)) *
                                    QIT.FiniteDistribution.strongTypicalMassScale
                                      (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                        ((N.tensorPower k).outputEnsemble E₀).averageState)
                                      n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                ε / 4) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelope
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨N0, hN0⟩ := hblock k hk ι inferInstance inferInstance E₀ δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hnN0
  obtain ⟨hn_pos, hn_small, hM⟩ := hN0 n hnN0
  refine ⟨hn_pos, hn_small, ?_⟩
  intro M hMF hMD hMne hrate hcard
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  obtain ⟨δx, δc, hδx, hδc, hprune_mass, hcardMoment, hmoment, hcross⟩ :=
    hM M inferInstance inferInstance hMne hrate hcard
  refine ⟨δx, δc, hswSelfPackingEpsilon ε, (1 / 2 : ℝ), hδx, hδc,
    hswSelfPackingEpsilon_nonneg hε, ?_, hprune_mass, hcardMoment, hmoment,
    hswSelfPackingEpsilon_self_bound hε, ?_⟩
  · norm_num
  · simpa using hcross

/-- Regularized HSW direct achievability after the inverse-square large-block
estimates have been discharged.

For fixed positive typicality slacks `δx, δc`, the prune-mass, finite
cardinality moment, and log-deviation moment conditions are all of the form
`C/(n δ²) ≤ η`; this theorem proves those eventually from
`exists_nat_real_div_mul_sq_le`.  The only remaining source estimate supplied by
the caller is the final cross exponent, which carries the actual Holevo-rate
gap. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFixedSlackCrossEstimate
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ (δx : ℝ), ∃ (δc : ℝ), 0 < δx ∧ 0 < δc ∧
                ∃ Ncross : ℕ, ∀ n : ℕ, n ≥ Ncross →
                  ∀ (M : Type u) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                        4 * Real.rpow 2
                              ((n : ℝ) *
                                ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                              (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                  n δx δc /
                                ((1 - (1 / 2 : ℝ)) *
                                  QIT.FiniteDistribution.strongTypicalMassScale
                                    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                      ((N.tensorPower k).outputEnsemble E₀).averageState)
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                              ε / 4) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelopeFixedSelfError
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨δx, δc, hδx, hδc, Ncross, hcross⟩ :=
    hblock k hk ι inferInstance inferInstance E₀ δ hδ ε hε
  obtain ⟨Nsmall, hNsmall⟩ :=
    exists_nat_real_div_mul_sq_le (C := (1 : ℝ)) (η := δ / 2) (δ := (1 : ℝ))
      (by positivity) (by norm_num)
  obtain ⟨Nprune, hNprune⟩ :=
    exists_nat_real_div_mul_sq_le (C := (Fintype.card ι : ℝ)) (η := (1 / 2 : ℝ))
      (δ := δx) (by norm_num) hδx
  obtain ⟨Ncard, hNcard⟩ :=
    exists_nat_real_div_mul_sq_le
      (C := (Fintype.card ι : ℝ) * (Fintype.card (QIT.TensorPower b k) : ℝ))
      (η := hswSelfPackingEpsilon ε) (δ := δc)
      (hswSelfPackingEpsilon_pos hε) hδc
  obtain ⟨Nmoment, hNmoment⟩ :=
    exists_nat_real_div_mul_sq_le
      (C := ((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope)
      (η := hswSelfPackingEpsilon ε) (δ := δc)
      (hswSelfPackingEpsilon_pos hε) hδc
  let N0 : ℕ := max 1 (max Nsmall (max Nprune (max Ncard (max Nmoment Ncross))))
  refine ⟨N0, ?_⟩
  intro n hnN0
  have hn_one : 1 ≤ n := by
    dsimp [N0] at hnN0
    omega
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn_one
  have hn_small_ge : n ≥ Nsmall := by
    dsimp [N0] at hnN0
    omega
  have hn_prune_ge : n ≥ Nprune := by
    dsimp [N0] at hnN0
    omega
  have hn_card_ge : n ≥ Ncard := by
    dsimp [N0] at hnN0
    omega
  have hn_moment_ge : n ≥ Nmoment := by
    dsimp [N0] at hnN0
    omega
  have hn_cross_ge : n ≥ Ncross := by
    dsimp [N0] at hnN0
    omega
  have hsmall : (1 : ℝ) / (n : ℝ) ≤ δ / 2 := by
    have h := hNsmall n hn_small_ge
    simpa using h
  refine ⟨hn_pos, hsmall, ?_⟩
  intro M hMF hMD hMne hrate hcard
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  have hprune : (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤ (1 / 2 : ℝ) :=
    hNprune n hn_prune_ge
  have hcardMoment :
      (Fintype.card ι : ℝ) * (Fintype.card (QIT.TensorPower b k) : ℝ) /
          ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε :=
    hNcard n hn_card_ge
  have hmoment :
      ((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope /
          ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε :=
    hNmoment n hn_moment_ge
  refine ⟨δx, δc, hδx, hδc, hprune, hcardMoment, hmoment, ?_⟩
  exact hcross n hn_cross_ge M inferInstance inferInstance hMne hrate hcard

/-- Regularized HSW direct achievability after the cross term has been bounded
by a uniform exponentially decaying source exponent.

This removes the final `Ncross`/`ε` bookkeeping from
`hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFixedSlackCrossEstimate`.
The caller now supplies only fixed positive typicality slacks and the
pointwise source exponent bound
`cross(n) ≤ 8 * 2^{-nδ/4}`.  The proved geometric-decay lemma chooses the
large enough blocklength making this bound at most `ε/4`. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorCrossExponentBound
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ →
              ∃ (δx : ℝ), ∃ (δc : ℝ), 0 < δx ∧ 0 < δc ∧
                ∀ n : ℕ,
                  4 * Real.rpow 2
                        ((n : ℝ) *
                          ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                      (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                          n δx δc /
                        ((1 - (1 / 2 : ℝ)) *
                          QIT.FiniteDistribution.strongTypicalMassScale
                            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                              ((N.tensorPower k).outputEnsemble E₀).averageState)
                            n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                    8 * Real.rpow 2 (-(n : ℝ) * (δ / 4))) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFixedSlackCrossEstimate
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨δx, δc, hδx, hδc, hcrossExp⟩ :=
    hblock k hk ι inferInstance inferInstance E₀ δ hδ
  obtain ⟨Ncross, hNcross⟩ :=
    exists_nat_const_mul_rpow_two_neg_mul_le (A := (8 : ℝ)) (c := δ / 4)
      (η := ε / 4) (by positivity) (by positivity)
  refine ⟨δx, δc, hδx, hδc, Ncross, ?_⟩
  intro n hn M hMF hMD hMne hrate hcard
  exact le_trans (hcrossExp n) (hNcross n hn)

/-- HSW direct achievability for the regularized Holevo information.

This is the direct half of Wilde's HSW theorem: every rate strictly below the
regularized Holevo information is operationally achievable.  The proof composes
the source-shaped strongly-typical random-coding construction, packing
lemma/expurgation assembly, block-channel normalization, and the explicit HSW
cross-exponent slack choice.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
theorem hsw_regularizedHolevoInformation_direct
    [Nonempty a] [Nonempty b] (N : Channel a b) :
    ∀ R : ℝ, R < N.regularizedHolevoInformation → N.IsAchievableClassicalRate R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorCrossExponentBound
      ?_
  intro k hk ι hιF hιD E₀ δ hδ
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  simpa [Channel.hswHolevoRate] using
    exists_hsw_crossExponentBound_slacks
      (E := ((N.tensorPower k).outputEnsemble E₀)) hδ

end Channel

end

end QIT
