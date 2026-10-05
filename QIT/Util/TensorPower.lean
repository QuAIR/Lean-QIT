/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.System
public import QIT.Util.Wires
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Tensor-power labels and operator tensor powers

The canonical type equivalence between the right-associated recursive tensor
power `TensorPower a n` and the function type `Fin n → a`, together with the
operator algebra built on top of it.

* **Label equivalence.** `tensorPowerEquiv` identifies `TensorPower a n` with
  `Fin n → a` by iterating the head/tail (`Fin.cons`) decomposition, with
  `tensorPowerEquiv_succ` as the successor unfolding; `tensorPower_card` and
  `tensorPower_nonempty_of_nonempty` give the basic cardinality and
  inhabitation facts.

* **Operator tensor powers.** `tensorPowMatrixPi M n` is the entrywise
  `n`-fold tensor power of an operator on `Fin n → a` (the `(x, y)` entry is
  the product of the per-wire entries), and `tensorPowMatrix M n` is the
  right-nested Kronecker form on `TensorPower a n`;
  `matReindex_tensorPowerEquiv_tensorPowMatrix` transports between the two
  views along the label equivalence. The master identity
  `tensorPowMatrixPi_eq_prod_liftAt` writes the entrywise power as the
  noncommutative product of the per-wire lifts (`oneKroneckerMonoidHom`
  packages the identity factors), giving `tensorPowMatrix_eq_prod_liftAt_reindex`
  on the nested form.

* **Bipartition register discipline.** Reading a tensor power of product
  labels `a × b` through `tensorPowerProdEquiv` splits it into the two factor
  powers (`tensorPowerProdEquiv_fst`, `tensorPowerProdEquiv_snd`);
  `tensorPowMatrixPair` is the entrywise power on the two-sided view, with
  `tensorPowMatrixPair_kronecker` and the full transport theorem
  `matReindex_tensorPowerProdEquiv_tensorPowMatrix`.
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
          ext i <;> simp [Fin.cons_zero, Fin.tail_cons]
        right_inv := by
          intro f
          (ext i; simp) }

omit [DecidableEq a] in
/-- The recursive tensor-power type has the expected cardinality `|a|^n`. -/
theorem tensorPower_card [Fintype a] (n : ℕ) :
    Fintype.card (TensorPower a n) = Fintype.card a ^ n := by
  induction n with
  | zero =>
      simp [TensorPower]
      rfl
  | succ n ih =>
      calc
        Fintype.card (TensorPower a (n + 1)) =
            Fintype.card (a × TensorPower a n) := rfl
        _ = Fintype.card a * Fintype.card (TensorPower a n) := Fintype.card_prod a (TensorPower a n)
        _ = Fintype.card a * Fintype.card a ^ n := by rw [ih]
        _ = Fintype.card a ^ (n + 1) := by rw [pow_succ']

omit [DecidableEq a] in
/-- The tensor power of a nonempty type is nonempty. -/
theorem tensorPower_nonempty_of_nonempty {α : Type u} [Nonempty α] :
    (n : ℕ) → Nonempty (TensorPower α n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 =>
      haveI : Nonempty (TensorPower α n) := tensorPower_nonempty_of_nonempty n
      inferInstanceAs (Nonempty (Prod α (TensorPower α n)))

end

/-! ## Operator tensor powers and the bipartition register discipline -/

open scoped BigOperators Kronecker ComplexOrder

noncomputable section

universe v

variable {a : Type u} [Fintype a] [DecidableEq a] {b : Type v} [Fintype b]
  [DecidableEq b]

namespace TensorPower

/-- Entrywise operator tensor power: the matrix on `Fin n → a` whose
`(x, y)` entry is the product of the per-wire entries. This is the
entry-first view of the `n`-fold tensor power of an operator that avoids
Kronecker associativity questions
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:216-216]. -/
def tensorPowMatrixPi (M : CMatrix a) (n : ℕ) : CMatrix (Fin n → a) :=
  fun x y => ∏ i : Fin n, M (x i) (y i)

omit [Fintype a] [DecidableEq a] in
/-- Entrywise computation of the operator tensor power. -/
@[simp]
theorem tensorPowMatrixPi_apply (M : CMatrix a) (n : ℕ) (x y : Fin n → a) :
    tensorPowMatrixPi M n x y = ∏ i : Fin n, M (x i) (y i) :=
  rfl

omit [Fintype a] in
/-- The zeroth operator tensor power is the identity. -/
theorem tensorPowMatrixPi_zero (M : CMatrix a) :
    tensorPowMatrixPi M 0 = 1 := by
  ext x y
  rw [tensorPowMatrixPi_apply, Fin.prod_univ_zero, Matrix.one_apply,
    ite_eq_left (Subsingleton.elim _ _)]

omit [Fintype a] in
/-- The entrywise operator tensor power of the identity is the identity. -/
theorem tensorPowMatrixPi_one (n : ℕ) :
    tensorPowMatrixPi (1 : CMatrix a) n = 1 := by
  ext x y
  simp only [tensorPowMatrixPi_apply, Matrix.one_apply, Finset.prod_boole,
    funext_iff, Finset.mem_univ, true_implies]

omit [DecidableEq a] in
/-- Operator tensor powers preserve multiplication. -/
theorem tensorPowMatrixPi_mul (M N : CMatrix a) (n : ℕ) :
    tensorPowMatrixPi (M * N) n =
      tensorPowMatrixPi M n * tensorPowMatrixPi N n := by
  ext x y
  simp only [tensorPowMatrixPi_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.prod_mul_distrib]

omit [Fintype a] [DecidableEq a] in
/-- The `(n + 1)`-fold operator tensor power, seen through the cons
equivalence, is the head factor tensored with the `n`-fold power. -/
theorem tensorPowMatrixPi_succ (M : CMatrix a) (n : ℕ) :
    WireFam.matReindex (Fin.consEquiv (fun _ : Fin (n + 1) => a)).symm
        (tensorPowMatrixPi M (n + 1)) =
      M ⊗ₖ tensorPowMatrixPi M n := by
  ext ⟨x₀, g⟩ ⟨y₀, g'⟩
  simp [WireFam.matReindex_apply, tensorPowMatrixPi_apply, Fin.prod_univ_succ]

/-- The right-nested operator tensor power: the `n`-fold tensor power of `M`
on `TensorPower a n`, by recursion with the head factor on the left. -/
def tensorPowMatrix (M : CMatrix a) : (n : ℕ) → CMatrix (TensorPower a n)
  | 0 => 1
  | n + 1 => M ⊗ₖ tensorPowMatrix M n

omit [Fintype a] in
/-- The zeroth right-nested operator tensor power is the identity. -/
theorem tensorPowMatrix_zero (M : CMatrix a) : tensorPowMatrix M 0 = 1 :=
  rfl

omit [Fintype a] in
/-- The successor unfolding of the right-nested operator tensor power. -/
theorem tensorPowMatrix_succ (M : CMatrix a) (n : ℕ) :
    tensorPowMatrix M (n + 1) = M ⊗ₖ tensorPowMatrix M n :=
  rfl

omit [Fintype a] in
/-- Right-nested operator tensor powers preserve the identity. -/
theorem tensorPowMatrix_one : (n : ℕ) → tensorPowMatrix (1 : CMatrix a) n = 1
  | 0 => rfl
  | n + 1 => by
      rw [tensorPowMatrix_succ, tensorPowMatrix_one n,
        Matrix.one_kronecker_one]
      rfl

/-- Right-nested operator tensor powers preserve multiplication. -/
theorem tensorPowMatrix_mul (M N : CMatrix a) :
    (n : ℕ) → tensorPowMatrix (M * N) n =
      tensorPowMatrix M n * tensorPowMatrix N n
  | 0 => by
      rw [tensorPowMatrix_zero, tensorPowMatrix_zero, tensorPowMatrix_zero,
        Matrix.mul_one]
  | n + 1 => by
      rw [tensorPowMatrix_succ, tensorPowMatrix_succ, tensorPowMatrix_succ,
        tensorPowMatrix_mul M N n]
      exact Matrix.mul_kronecker_mul M N (tensorPowMatrix M n) (tensorPowMatrix N n)

/-- Right-nested operator tensor powers preserve idempotence. -/
theorem tensorPowMatrix_idempotent {M : CMatrix a} (h : M * M = M) :
    (n : ℕ) → tensorPowMatrix M n * tensorPowMatrix M n = tensorPowMatrix M n
  | 0 => by rw [tensorPowMatrix_zero, Matrix.one_mul]
  | n + 1 => by
      rw [tensorPowMatrix_succ]
      refine (Matrix.mul_kronecker_mul M M (tensorPowMatrix M n)
        (tensorPowMatrix M n)).symm.trans ?_
      rw [h, tensorPowMatrix_idempotent h n]

omit [Fintype a] in
/-- Right-nested operator tensor powers preserve Hermiticity. -/
theorem tensorPowMatrix_isHermitian {M : CMatrix a} (h : M.IsHermitian) :
    (n : ℕ) → (tensorPowMatrix M n).IsHermitian
  | 0 => by
      rw [tensorPowMatrix_zero]
      exact Matrix.isHermitian_one
  | n + 1 => by
      show Matrix.conjTranspose (tensorPowMatrix M (n + 1)) =
        tensorPowMatrix M (n + 1)
      rw [tensorPowMatrix_succ]
      refine (Matrix.conjTranspose_kronecker M (tensorPowMatrix M n)).trans ?_
      rw [h, tensorPowMatrix_isHermitian h n]

/-- Right-nested operator tensor powers preserve positive
semidefiniteness. -/
theorem tensorPowMatrix_posSemidef {M : CMatrix a} (h : M.PosSemidef) :
    (n : ℕ) → (tensorPowMatrix M n).PosSemidef
  | 0 => by
      rw [tensorPowMatrix_zero]
      exact Matrix.PosSemidef.one
  | n + 1 => by
      rw [tensorPowMatrix_succ]
      exact h.kronecker (tensorPowMatrix_posSemidef h n)

omit [Fintype a] [DecidableEq a] in
/-- The successor unfolding of the tensor-power label equivalence: it is the
product of the head identity with the tail equivalence, followed by the
cons equivalence. -/
theorem tensorPowerEquiv_succ (n : ℕ) :
    tensorPowerEquiv (a := a) (n + 1) =
      ((Equiv.refl a).prodCongr (tensorPowerEquiv (a := a) n)).trans
        (Fin.consEquiv (fun _ : Fin (n + 1) => a)) := by
  ext z i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

omit [Fintype a] in
/-- The right-nested operator tensor power, transported along the label
equivalence, is the entrywise operator tensor power. -/
theorem matReindex_tensorPowerEquiv_tensorPowMatrix (M : CMatrix a) :
    (n : ℕ) →
      WireFam.matReindex (tensorPowerEquiv (a := a) n) (tensorPowMatrix M n) =
        tensorPowMatrixPi M n
  | 0 => by
      rw [tensorPowMatrix_zero, WireFam.matReindex_one, tensorPowMatrixPi_zero]
  | n + 1 => by
      apply (WireFam.matReindex
        (Fin.consEquiv (fun _ : Fin (n + 1) => a)).symm).injective
      rw [tensorPowMatrixPi_succ]
      show (WireFam.matReindex (Fin.consEquiv (fun _ : Fin (n + 1) => a)).symm)
          ((WireFam.matReindex (((Equiv.refl a).prodCongr
            (tensorPowerEquiv (a := a) n)).trans
            (Fin.consEquiv (fun _ : Fin (n + 1) => a))))
            (Matrix.kronecker M (tensorPowMatrix M n))) =
        Matrix.kronecker M (tensorPowMatrixPi M n)
      rw [WireFam.matReindex_trans_apply,
        WireFam.matReindex_kronecker_prodCongr, WireFam.matReindex_refl,
        matReindex_tensorPowerEquiv_tensorPowMatrix M n,
        ← WireFam.matReindex_symm, Equiv.symm_apply_apply]

/-- Left Kronecker multiplication by the identity matrix, as a monoid
homomorphism. -/
def oneKroneckerMonoidHom : CMatrix a →* CMatrix (b × a) where
  toFun N := (1 : CMatrix b) ⊗ₖ N
  map_one' := Matrix.one_kronecker_one
  map_mul' := fun x y => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- The monoid-homomorphism form of left identity Kronecker multiplication
computes entrywise. -/
@[simp]
theorem oneKroneckerMonoidHom_apply (N : CMatrix a) :
    oneKroneckerMonoidHom (b := b) N = (1 : CMatrix b) ⊗ₖ N :=
  rfl

/-- A noncommutative product of left-identity Kronecker factors is the
left-identity Kronecker of the product. -/
theorem one_kronecker_noncommProd {γ : Type*} (s : Finset γ)
    (f : γ → CMatrix a)
    (comm : (s : Set γ).Pairwise (Function.onFun Commute f)) :
    s.noncommProd (fun i => (1 : CMatrix b) ⊗ₖ f i)
        (fun _ hx _ hy h =>
          (comm hx hy h).map (oneKroneckerMonoidHom (a := a) (b := b))) =
      (1 : CMatrix b) ⊗ₖ s.noncommProd f comm :=
  (Finset.map_noncommProd s f comm
    (oneKroneckerMonoidHom (a := a) (b := b))).symm

/-- The master identity of the register discipline: the entrywise operator
tensor power on `n + 1` wires is the product of the per-wire lifts
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:216-216]. -/
theorem tensorPowMatrixPi_eq_prod_liftAt (M : CMatrix a) :
    (n : ℕ) → tensorPowMatrixPi M (n + 1) =
      Finset.univ.noncommProd
        (fun i => WireFam.liftAt (fun _ : Fin (n + 1) => a) i M)
        (WireFam.liftAt_pairwise_commute M)
  | 0 => by
      show tensorPowMatrixPi M 1 =
        Finset.univ.noncommProd
          (fun i => WireFam.liftAt (fun _ : Fin 1 => a) i M)
          (WireFam.liftAt_pairwise_commute M)
      have h0 : (Finset.univ : Finset (Fin 1)) = {0} := Finset.univ_unique
      have hprod : Finset.univ.noncommProd
          (fun i => WireFam.liftAt (fun _ : Fin 1 => a) i M)
          (WireFam.liftAt_pairwise_commute M) =
            WireFam.liftAt (fun _ : Fin 1 => a) 0 M := by
        rw [Finset.noncommProd_congr h0 (fun _ _ => rfl)
          (WireFam.liftAt_pairwise_commute M), Finset.noncommProd_singleton]
      ext x y
      rw [tensorPowMatrixPi_apply, Fin.prod_univ_one, hprod,
        WireFam.liftAt_apply, Matrix.one_apply,
        ite_eq_left (Subsingleton.elim _ _), mul_one]
  | n + 1 => by
      show tensorPowMatrixPi M (n + 2) =
        Finset.univ.noncommProd
          (fun i => WireFam.liftAt (fun _ : Fin (n + 2) => a) i M)
          (WireFam.liftAt_pairwise_commute M)
      have head : WireFam.matReindex
          (Fin.consEquiv (fun _ : Fin (n + 2) => a)).symm
          (WireFam.liftAt (fun _ : Fin (n + 2) => a) 0 M) =
            M ⊗ₖ (1 : CMatrix (Fin (n + 1) → a)) := by
        have h := WireFam.liftAt_eq_kronecker
          (W := fun _ : Fin (n + 2) => a) 0 M
        rwa [WireFam.extractAt_zero] at h
      have tail (j : Fin (n + 1)) : WireFam.matReindex
          (Fin.consEquiv (fun _ : Fin (n + 2) => a)).symm
          (WireFam.liftAt (fun _ : Fin (n + 2) => a) j.succ M) =
            (1 : CMatrix a) ⊗ₖ
              WireFam.liftAt (fun _ : Fin (n + 1) => a) j M := by
        have h := WireFam.liftAt_succAbove
          (W := fun _ : Fin (n + 2) => a) 0 j M
        rwa [WireFam.extractAt_zero] at h
      apply (WireFam.matReindex
        (Fin.consEquiv (fun _ : Fin (n + 2) => a)).symm).injective
      have htail := WireFam.matReindex_noncommProd
        (Fin.consEquiv (fun _ : Fin (n + 2) => a)).symm Finset.univ
        (fun i : Fin (n + 1) => WireFam.liftAt (fun _ : Fin (n + 2) => a) i.succ M)
        (fun i _ j _ hij => WireFam.liftAt_pairwise_commute M
          (Finset.mem_univ i.succ) (Finset.mem_univ j.succ)
          ((Fin.succ_injective _).ne hij))
      have htail' := htail.trans (Finset.noncommProd_congr rfl (fun j _ => tail j) _)
      have htail'' := htail'.trans (one_kronecker_noncommProd Finset.univ
        (fun i : Fin (n + 1) => WireFam.liftAt (fun _ : Fin (n + 1) => a) i M)
        (WireFam.liftAt_pairwise_commute M))
      rw [tensorPowMatrixPi_succ, WireFam.fin_noncommProd_univ_succ,
        tensorPowMatrixPi_eq_prod_liftAt M n, WireFam.matReindex_mul]
      exact ((congrArg₂ (· * ·) head htail'').trans
        (by simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul])).symm

/-- The right-nested operator tensor power on `n + 1` wires is the reindexed
product of per-wire lifts. -/
theorem tensorPowMatrix_eq_prod_liftAt_reindex (M : CMatrix a) (n : ℕ) :
    tensorPowMatrix M (n + 1) =
      (WireFam.matReindex (tensorPowerEquiv (a := a) (n + 1))).symm
        (Finset.univ.noncommProd
          (fun i => WireFam.liftAt (fun _ : Fin (n + 1) => a) i M)
          (WireFam.liftAt_pairwise_commute M)) := by
  rw [← tensorPowMatrixPi_eq_prod_liftAt M n,
    ← matReindex_tensorPowerEquiv_tensorPowMatrix, Equiv.symm_apply_apply]

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Entrywise characterization of the bipartition label equivalence, read at a
tensor position. -/
theorem tensorPowerProdEquiv_apply (n : ℕ) (z : TensorPower (Prod a b) n)
    (i : Fin n) :
    tensorPowerEquiv (a := Prod a b) n z i =
      (tensorPowerEquiv (a := a) n ((tensorPowerProdEquiv a b n z).1) i,
        tensorPowerEquiv (a := b) n ((tensorPowerProdEquiv a b n z).2) i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- First-coordinate projection of `tensorPowerProdEquiv`, read at a tensor
position. -/
theorem tensorPowerProdEquiv_fst (n : ℕ) (z : TensorPower (Prod a b) n)
    (i : Fin n) :
    tensorPowerEquiv (a := a) n ((tensorPowerProdEquiv a b n z).1) i =
      (tensorPowerEquiv (a := Prod a b) n z i).1 :=
  (congrArg Prod.fst (tensorPowerProdEquiv_apply n z i)).symm

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Second-coordinate projection of `tensorPowerProdEquiv`, read at a tensor
position. -/
theorem tensorPowerProdEquiv_snd (n : ℕ) (z : TensorPower (Prod a b) n)
    (i : Fin n) :
    tensorPowerEquiv (a := b) n ((tensorPowerProdEquiv a b n z).2) i =
      (tensorPowerEquiv (a := Prod a b) n z i).2 :=
  (congrArg Prod.snd (tensorPowerProdEquiv_apply n z i)).symm

/-- Entrywise operator tensor power on the bipartition view: the matrix on
`(Fin n → a) × (Fin n → b)` whose `((x, y), (x', y'))` entry is the product
of the per-wire entries. -/
def tensorPowMatrixPair (M : CMatrix (a × b)) (n : ℕ) :
    CMatrix ((Fin n → a) × (Fin n → b)) :=
  fun p q => ∏ i : Fin n, M (p.1 i, p.2 i) (q.1 i, q.2 i)

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Entrywise computation of the bipartition operator tensor power. -/
@[simp]
theorem tensorPowMatrixPair_apply (M : CMatrix (a × b)) (n : ℕ)
    (p q : (Fin n → a) × (Fin n → b)) :
    tensorPowMatrixPair M n p q =
      ∏ i : Fin n, M (p.1 i, p.2 i) (q.1 i, q.2 i) :=
  rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- When the operator factors as a Kronecker product, the bipartition
operator tensor power factors as the Kronecker product of the two entrywise
powers. -/
theorem tensorPowMatrixPair_kronecker (MB : CMatrix a) (ME : CMatrix b)
    (n : ℕ) :
    tensorPowMatrixPair (MB ⊗ₖ ME) n =
      tensorPowMatrixPi MB n ⊗ₖ tensorPowMatrixPi ME n := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  rw [tensorPowMatrixPair_apply, Matrix.kronecker_apply,
    tensorPowMatrixPi_apply, tensorPowMatrixPi_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.kronecker_apply]

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- The bipartition label equivalence followed by the two factor label
equivalences is the joint label equivalence followed by the arrow/product
swap. -/
theorem tensorPowerProdEquiv_trans_prodCongr (n : ℕ) :
    (tensorPowerProdEquiv a b n).trans
        ((tensorPowerEquiv (a := a) n).prodCongr (tensorPowerEquiv (a := b) n)) =
      (tensorPowerEquiv (a := Prod a b) n).trans
        (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => a) (fun _ => b)) := by
  ext z i
  · exact tensorPowerProdEquiv_fst n z i
  · exact tensorPowerProdEquiv_snd n z i

omit [Fintype a] [Fintype b] in
/-- The full bipartition transport theorem: the right-nested operator tensor
power of a bipartite operator, transported to the two-sided register view,
is the entrywise bipartition operator tensor power
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:216-216]. -/
theorem matReindex_tensorPowerProdEquiv_tensorPowMatrix
    (M : CMatrix (a × b)) (n : ℕ) :
    WireFam.matReindex
        ((tensorPowerEquiv (a := a) n).prodCongr
          (tensorPowerEquiv (a := b) n))
        (WireFam.matReindex (tensorPowerProdEquiv a b n)
          (tensorPowMatrix M n)) =
      tensorPowMatrixPair M n := by
  rw [← WireFam.matReindex_trans_apply, tensorPowerProdEquiv_trans_prodCongr,
    WireFam.matReindex_trans_apply, matReindex_tensorPowerEquiv_tensorPowMatrix]
  rfl

end TensorPower

end
