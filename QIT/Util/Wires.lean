/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Heterogeneous finite wire families

A *wire family* is a dependent family `W : Fin n → Type u` of finite, typically
nonempty, types: wire `i` carries its own classical configuration type `W i`,
with no common dimension across wires. The joint configuration space of the
family is the ordered dependent product `∀ i, W i`, which indexes the
computational basis of the associated joint system.

This module develops the combinatorics of such joint configuration spaces.

* **Mixed-radix enumeration.** `indexEquivOfEnum` turns an explicit enumeration
  `ε : ∀ i, W i ≃ Fin (d i)` of the wires into the odometer (mixed-radix)
  enumeration `(∀ i, W i) ≃ Fin (∏ i, d i)` of joint configurations, built on
  `finPiFinEquiv`; `indexEquiv` is the canonical instance obtained from the
  `Fintype` structure of the wires. The forward map is the mixed-radix value
  `∑ i, (ε i (f i) : ℕ) * ∏ j : Fin i, d j`, the backward map recovers the
  digit of wire `i` by division and remainder
  (`finPiFinEquiv_symm_apply_val`), and the enumeration respects the
  co-lexicographic order: if the *last* wire on which two configurations
  differ carries a strictly smaller value in `f` than in `g`, then the index
  of `f` is strictly smaller than the index of `g`
  (`finPiFinEquiv_lt_of_last_lt`).

* **Splitting and appending.** `append W₁ W₂` concatenates two wire families
  along `Fin.castAdd` and `Fin.natAdd`, and `splitEquiv` decomposes a joint
  configuration over `Fin (m + k)` into the pair of its left and right
  restrictions, with `Fin.addCases` as its inverse (`splitEquiv_symm_apply`).
  `splitAppendEquiv` identifies the configurations of an appended family with
  the product of the factor configurations.

* **Permutation.** `permuteEquiv W e` reorders the wires of a joint
  configuration along an equivalence `e : Fin n ≃ Fin n`, coherently under
  reflexivity and composition (`permuteEquiv_refl`, `permuteEquiv_trans`).

* **Reindexing vectors and matrices.** `vecReindex` and `matReindex`
  transport complex vectors and square matrices along equivalences of the
  index types, preserving multiplication, the identity matrix, the trace,
  the conjugate transpose, and Kronecker products
  (`matReindex_kronecker_prodCongr`), with `matReindex_symm` and
  `matReindex_trans_apply` for inverse and composite reindexings and
  `matReindexMonoidHom`/`matReindex_noncommProd` for distribution over
  noncommutative products. `vecSplit`, `matSplit`, `vecPermute`,
  and `matPermute` specialize these transports to the split and permutation
  structure of wire families.

* **Head-tail splits for products.** `fin_noncommProd_univ_succAbove` and
  `fin_noncommProd_univ_succ` split a noncommutative product over
  `Fin (n + 1)` into the pivot factor and the product over the remaining
  wires, built on `finset_noncommProd_map`.

* **Factor extraction.** `extractAt W i` identifies the joint configuration
  space of a wire family over `Fin (n + 1)` with the factor at wire `i`
  times the joint configuration space of the remaining wires
  (`Fin.insertNthEquiv` in reverse), with `extractAt_zero` recovering the
  cons equivalence at wire zero.

* **Single-wire operators.** `liftAt W i M` lifts an operator on wire `i`
  to the joint system, acting as `M` on factor `i` and as the identity on
  the remaining wires (`liftAt_eq_kronecker`). The lift preserves
  multiplication, the identity, the conjugate transpose, Hermiticity,
  positive semidefiniteness, and idempotence, and `liftAt_succAbove` is the
  recursion principle relating lifts at successive wire levels.

* **Commutation and defect operators.** Lifts at distinct wires commute
  (`liftAt_commute`), packaged as `liftAt_pairwise_commute` for the side
  conditions of noncommutative products; `deltaAt W i M = 1 - liftAt W i M`
  is the complementary (defect) local operator, commuting across wires
  (`deltaAt_comm`) and preserving idempotence and Hermiticity.
-/

@[expose] public section

open scoped BigOperators Kronecker ComplexOrder

namespace QIT

universe u

namespace WireFam

/-! ## Ordered dependent-product basis -/

section Basis

variable {n : ℕ} {W : Fin n → Type u}

/-- The cardinality of a joint configuration space is the product of the wire
cardinalities. -/
theorem card_config [∀ i, Fintype (W i)] :
    Fintype.card (∀ i, W i) = ∏ i, Fintype.card (W i) :=
  Fintype.card_pi

/-- The joint configuration space of a family of nonempty wires is nontrivial:
its cardinality is a positive product. -/
theorem card_pos [∀ i, Fintype (W i)] [∀ i, Nonempty (W i)] :
    0 < ∏ i, Fintype.card (W i) :=
  Finset.prod_pos fun _i _ => Fintype.card_pos

/-- Backward computation rule for the mixed-radix enumeration `finPiFinEquiv`:
the digit of wire `i` in the configuration encoded by `a` is the quotient of
`a` by the weight `∏ j : Fin i, d j` of that wire, taken modulo the radix
`d i`. -/
theorem finPiFinEquiv_symm_apply_val {d : Fin n → ℕ} (a : Fin (∏ i, d i)) (i : Fin n) :
    (finPiFinEquiv.symm a i : ℕ) =
      (a / ∏ j : Fin i, d (Fin.castLE i.is_lt.le j)) % d i :=
  rfl

/-- The mixed-radix index equivalence induced by an explicit enumeration
`ε : ∀ i, W i ≃ Fin (d i)` of the wires: joint configurations of the family
are encoded as numerals below the product of the wire radixes. -/
def indexEquivOfEnum (d : Fin n → ℕ) (ε : ∀ i, W i ≃ Fin (d i)) :
    (∀ i, W i) ≃ Fin (∏ i, d i) :=
  (Equiv.piCongrRight ε).trans finPiFinEquiv

/-- Forward computation rule for `indexEquivOfEnum`: the code of a
configuration is its mixed-radix value with wire digits read off by `ε`. -/
theorem indexEquivOfEnum_apply (d : Fin n → ℕ) (ε : ∀ i, W i ≃ Fin (d i)) (f : ∀ i, W i) :
    (indexEquivOfEnum d ε f : ℕ) =
      ∑ i, (ε i (f i) : ℕ) * ∏ j : Fin i, d (Fin.castLE i.is_lt.le j) :=
  finPiFinEquiv_apply _

/-- Backward computation rule for `indexEquivOfEnum`: reading the digit of
wire `i` back through `ε` recovers the quotient-remainder extraction. -/
theorem indexEquivOfEnum_symm_apply_val (d : Fin n → ℕ) (ε : ∀ i, W i ≃ Fin (d i))
    (a : Fin (∏ i, d i)) (i : Fin n) :
    (ε i ((indexEquivOfEnum d ε).symm a i) : ℕ) =
      (a / ∏ j : Fin i, d (Fin.castLE i.is_lt.le j)) % d i := by
  have h : (indexEquivOfEnum d ε).symm a i = (ε i).symm (finPiFinEquiv.symm a i) := rfl
  rw [h, Equiv.apply_symm_apply]
  exact finPiFinEquiv_symm_apply_val a i

/-- The canonical mixed-radix index equivalence of a finite wire family, using
the `Fintype` enumeration of each wire. -/
noncomputable def indexEquiv [∀ i, Fintype (W i)] :
    (∀ i, W i) ≃ Fin (∏ i, Fintype.card (W i)) :=
  indexEquivOfEnum _ fun i => Fintype.equivFin (W i)

/-- `indexEquiv` is `indexEquivOfEnum` at the `Fintype` enumerations. -/
theorem indexEquiv_eq_indexEquivOfEnum [∀ i, Fintype (W i)] :
    indexEquiv (W := W) = indexEquivOfEnum _ (fun i => Fintype.equivFin (W i)) :=
  rfl

/-- Forward computation rule for `indexEquiv`: the code of a configuration is
its mixed-radix value with digits read off by the `Fintype` enumerations. -/
theorem indexEquiv_apply [∀ i, Fintype (W i)] (f : ∀ i, W i) :
    (indexEquiv f : ℕ) =
      ∑ i, (Fintype.equivFin (W i) (f i) : ℕ) *
        ∏ j : Fin i, Fintype.card (W (Fin.castLE i.is_lt.le j)) :=
  indexEquivOfEnum_apply _ _ f

/-- Backward computation rule for `indexEquiv`: reading the digit of wire `i`
back through the `Fintype` enumeration recovers the quotient-remainder
extraction. -/
theorem indexEquiv_symm_apply_val [∀ i, Fintype (W i)]
    (a : Fin (∏ i, Fintype.card (W i))) (i : Fin n) :
    (Fintype.equivFin (W i) ((indexEquiv (W := W)).symm a i) : ℕ) =
      (a / ∏ j : Fin i, Fintype.card (W (Fin.castLE i.is_lt.le j))) %
        Fintype.card (W i) :=
  indexEquivOfEnum_symm_apply_val _ (fun i => Fintype.equivFin (W i)) a i

end Basis

/-! ## Order-respecting property of the mixed-radix enumeration -/

section Order

/-- The weight `∏ j : Fin i, n j` of wire `i` in the mixed-radix enumeration,
rewritten as a product over `Finset.range i` along any extension `N` of the
radix family `n` to all of `ℕ`. -/
theorem prod_univ_castLE_eq_prod_range {m : ℕ} {n : Fin m → ℕ} (N : ℕ → ℕ)
    (hN : ∀ j (h : j < m), N j = n ⟨j, h⟩) (i : Fin m) :
    ∏ j : Fin i, n (Fin.castLE i.is_lt.le j) = ∏ j ∈ Finset.range i, N j := by
  have h : (∏ j : Fin i, n (Fin.castLE i.is_lt.le j)) = ∏ j : Fin i, N j :=
    Finset.prod_congr rfl fun j _ => (hN j (j.is_lt.trans i.is_lt)).symm
  rw [h, Fin.prod_univ_eq_prod_range]

/-- Telescoping identity behind the odometer enumeration: a product of radices
is one more than the sum of the maximal contributions of the lower digits. -/
theorem prod_range_eq_one_add_sum_sub_one_mul (N : ℕ → ℕ) (m : ℕ)
    (hN : ∀ j < m, 1 ≤ N j) :
    ∏ j ∈ Finset.range m, N j =
      1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      ih fun j hj => hN j (hj.trans (Nat.lt_succ_self m))]
    have hNm := hN m (Nat.lt_succ_self m)
    calc (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) * N m
        = (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) *
            (N m - 1 + 1) := by
          rw [Nat.sub_add_cancel hNm]
      _ = (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) * (N m - 1) +
            (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) := by
          rw [mul_add, mul_one]
      _ = 1 + (∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k +
            (N m - 1) * (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k)) := by
          rw [mul_comm (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k)
            (N m - 1)]
          omega

/-- The mixed-radix enumeration respects the co-lexicographic order: if `i` is
the last wire on which the configurations `f` and `g` differ, and the digit of
`f` at wire `i` is strictly smaller than that of `g`, then the mixed-radix
code of `f` is strictly smaller than the code of `g`. -/
theorem finPiFinEquiv_lt_of_last_lt {m : ℕ} {n : Fin m → ℕ} {f g : ∀ i, Fin (n i)}
    (i : Fin m) (hEq : ∀ j, i < j → f j = g j) (hLt : f i < g i) :
    finPiFinEquiv f < finPiFinEquiv g := by
  rw [Fin.lt_def, finPiFinEquiv_apply, finPiFinEquiv_apply]
  set N : ℕ → ℕ := fun j => if h : j < m then n ⟨j, h⟩ else 1 with hN_def
  set w : ℕ → ℕ := fun j => ∏ k ∈ Finset.range j, N k with hw_def
  have hN_eq : ∀ j (h : j < m), N j = n ⟨j, h⟩ := fun j h => dite_eq_left h
  have hN_pos : ∀ j < m, 1 ≤ N j := by
    intro j hj
    rw [hN_eq j hj]
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun h0 => by
      have hf := f ⟨j, hj⟩
      rw [h0] at hf
      exact hf.elim0)
  have hw : ∀ i' : Fin m, ∏ j : Fin i', n (Fin.castLE i'.is_lt.le j) = w i' := fun i' =>
    prod_univ_castLE_eq_prod_range N hN_eq i'
  -- Convert both mixed-radix values to range sums over the weight function.
  set F : ℕ → ℕ := fun j => if h : j < m then (f ⟨j, h⟩ : ℕ) * w j else 0 with hF_def
  set G : ℕ → ℕ := fun j => if h : j < m then (g ⟨j, h⟩ : ℕ) * w j else 0 with hG_def
  have hL : (∑ i' : Fin m, (f i' : ℕ) * ∏ j : Fin i', n (Fin.castLE i'.is_lt.le j)) =
      ∑ j ∈ Finset.range m, F j := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [dite_eq_left hj, hF_def]
    show (f ⟨j, hj⟩ : ℕ) * ∏ j' : Fin j, n (Fin.castLE _ j') =
      if h : j < m then (f ⟨j, h⟩ : ℕ) * w j else 0
    rw [dite_eq_left hj]
    exact congrArg _ (hw ⟨j, hj⟩)
  have hR : (∑ i' : Fin m, (g i' : ℕ) * ∏ j : Fin i', n (Fin.castLE i'.is_lt.le j)) =
      ∑ j ∈ Finset.range m, G j := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [dite_eq_left hj, hG_def]
    show (g ⟨j, hj⟩ : ℕ) * ∏ j' : Fin j, n (Fin.castLE _ j') =
      if h : j < m then (g ⟨j, h⟩ : ℕ) * w j else 0
    rw [dite_eq_left hj]
    exact congrArg _ (hw ⟨j, hj⟩)
  rw [hL, hR]
  -- The prefix of `f` below wire `i` is strictly bounded by the weight of `i`.
  have hpreF : (∑ j ∈ Finset.range i, F j) + 1 ≤ w i := by
    have h1 : (∑ j ∈ Finset.range i, F j) ≤
        ∑ j ∈ Finset.range i, (N j - 1) * w j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm : j < m := (Finset.mem_range.mp hj).trans i.is_lt
      rw [hF_def]
      show (if h : j < m then (f ⟨j, h⟩ : ℕ) * w j else 0) ≤ (N j - 1) * w j
      rw [dite_eq_left hjm]
      refine Nat.mul_le_mul_right _ ?_
      rw [hN_eq j hjm]
      exact Nat.le_pred_of_lt (f ⟨j, hjm⟩).is_lt
    have h2 : w i = 1 + ∑ j ∈ Finset.range i, (N j - 1) * w j :=
      prod_range_eq_one_add_sum_sub_one_mul N i fun j hj => hN_pos j (hj.trans i.is_lt)
    omega
  -- The middle digit of `f` at wire `i` leaves room for one full weight.
  have hmidF : F i + w i ≤ G i := by
    have hfw : F i = (f i : ℕ) * w i := by
      rw [hF_def]
      show (if h : i.val < m then (f ⟨i.val, h⟩ : ℕ) * w i.val else 0) = _
      rw [dite_eq_left i.is_lt]
    have hgw : G i = (g i : ℕ) * w i := by
      rw [hG_def]
      show (if h : i.val < m then (g ⟨i.val, h⟩ : ℕ) * w i.val else 0) = _
      rw [dite_eq_left i.is_lt]
    rw [hfw, hgw]
    calc (f i : ℕ) * w i + w i = ((f i : ℕ) + 1) * w i := (Nat.succ_mul _ _).symm
      _ ≤ (g i : ℕ) * w i := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Fin.lt_def.mp hLt))
  -- The tails above wire `i` agree.
  have htailF : ∀ j ∈ Finset.range (m - (i.val + 1)),
      F (i.val + 1 + j) = G (i.val + 1 + j) := by
    intro j hj
    have h1 : i.val + 1 + j < m := by
      have := Finset.mem_range.mp hj
      omega
    rw [hF_def, hG_def]
    show (if h : i.val + 1 + j < m then (f ⟨i.val + 1 + j, h⟩ : ℕ) * w (i.val + 1 + j) else 0) =
      if h : i.val + 1 + j < m then (g ⟨i.val + 1 + j, h⟩ : ℕ) * w (i.val + 1 + j) else 0
    rw [dite_eq_left h1, dite_eq_left h1]
    have hlt : i < ⟨i.val + 1 + j, h1⟩ := by
      rw [Fin.lt_def]
      show i.val < i.val + 1 + j
      omega
    rw [hEq ⟨i.val + 1 + j, h1⟩ hlt]
  -- Split both sums at wire `i` and compare.
  have hm : m = i.val + 1 + (m - (i.val + 1)) := (Nat.add_sub_cancel' i.is_lt).symm
  rw [hm, Finset.sum_range_add (f := F), Finset.sum_range_succ (f := F),
    Finset.sum_range_add (f := G), Finset.sum_range_succ (f := G),
    Finset.sum_congr rfl htailF]
  have key : (∑ j ∈ Finset.range i, F j) + F i + 1 ≤
      (∑ j ∈ Finset.range i, G j) + G i := by
    have hG_nonneg : 0 ≤ ∑ j ∈ Finset.range i, G j := Nat.zero_le _
    omega
  omega

end Order

/-! ## Splitting and appending wire families -/

section Append

variable {m k : ℕ} {W₁ : Fin m → Type u} {W₂ : Fin k → Type u}

/-- The concatenation of two wire families: wires `0, …, m - 1` come from
`W₁` and wires `m, …, m + k - 1` come from `W₂`. -/
def append (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) : Fin (m + k) → Type u :=
  Fin.addCases W₁ W₂

@[simp]
theorem append_castAdd (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) (i : Fin m) :
    append W₁ W₂ (Fin.castAdd k i) = W₁ i :=
  Fin.addCases_left i

@[simp]
theorem append_natAdd (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) (j : Fin k) :
    append W₁ W₂ (Fin.natAdd m j) = W₂ j :=
  Fin.addCases_right j

instance instFintypeAppend [∀ i, Fintype (W₁ i)] [∀ j, Fintype (W₂ j)] (i : Fin (m + k)) :
    Fintype (append W₁ W₂ i) := by
  induction i using Fin.addCases with
  | left i => rw [append_castAdd]; infer_instance
  | right j => rw [append_natAdd]; infer_instance

instance instNonemptyAppend [∀ i, Nonempty (W₁ i)] [∀ j, Nonempty (W₂ j)] (i : Fin (m + k)) :
    Nonempty (append W₁ W₂ i) := by
  induction i using Fin.addCases with
  | left i => rw [append_castAdd]; infer_instance
  | right j => rw [append_natAdd]; infer_instance

/-- The cardinality product of an appended family splits into the products of
the factors. -/
theorem card_append [∀ i, Fintype (W₁ i)] [∀ j, Fintype (W₂ j)] :
    ∏ i, Fintype.card (append W₁ W₂ i) =
      (∏ i, Fintype.card (W₁ i)) * ∏ j, Fintype.card (W₂ j) := by
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun i _ =>
      Fintype.card_congr (Equiv.cast (append_castAdd W₁ W₂ i))
  · exact Finset.prod_congr rfl fun j _ =>
      Fintype.card_congr (Equiv.cast (append_natAdd W₁ W₂ j))

end Append

/-- Splitting a joint configuration over `Fin (m + k)` into the pair of its
restrictions to the first `m` wires and the last `k` wires. -/
def splitEquiv {m k : ℕ} (W : Fin (m + k) → Type u) :
    (∀ i, W i) ≃ (∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j)) :=
  (Equiv.piCongrLeft W finSumFinEquiv).symm.trans (Equiv.sumPiEquivProdPi _)

/-- Computing `splitEquiv` on a configuration: the two restrictions of `f`. -/
theorem splitEquiv_apply {m k : ℕ} (W : Fin (m + k) → Type u) (f : ∀ i, W i) :
    splitEquiv W f = (fun i => f (Fin.castAdd k i), fun j => f (Fin.natAdd m j)) := by
  ext i <;> rfl

/-- The left factor of a split configuration is its restriction to the first
`m` wires. -/
@[simp]
theorem splitEquiv_apply_fst {m k : ℕ} (W : Fin (m + k) → Type u) (f : ∀ i, W i)
    (i : Fin m) :
    (splitEquiv W f).1 i = f (Fin.castAdd k i) :=
  rfl

/-- The right factor of a split configuration is its restriction to the last
`k` wires. -/
@[simp]
theorem splitEquiv_apply_snd {m k : ℕ} (W : Fin (m + k) → Type u) (f : ∀ i, W i)
    (j : Fin k) :
    (splitEquiv W f).2 j = f (Fin.natAdd m j) :=
  rfl

/-- Splitting a configuration assembled by `Fin.addCases` recovers the two
parts: splitting and case assembly are inverse operations. -/
theorem splitEquiv_addCases {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) :
    splitEquiv W (Fin.addCases g h) = (g, h) := by
  ext i <;> simp

/-- The inverse of `splitEquiv` assembles a pair of partial configurations by
`Fin.addCases`. -/
theorem splitEquiv_symm_apply {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) :
    (splitEquiv W).symm (g, h) = Fin.addCases g h :=
  (splitEquiv W).injective ((Equiv.apply_symm_apply _ _).trans (splitEquiv_addCases W g h).symm)

/-- Assembling and reading back at a left wire recovers the left part. -/
@[simp]
theorem splitEquiv_symm_apply_castAdd {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) (i : Fin m) :
    (splitEquiv W).symm (g, h) (Fin.castAdd k i) = g i := by
  simp only [splitEquiv_symm_apply, Fin.addCases_left]

/-- Assembling and reading back at a right wire recovers the right part. -/
@[simp]
theorem splitEquiv_symm_apply_natAdd {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) (j : Fin k) :
    (splitEquiv W).symm (g, h) (Fin.natAdd m j) = h j := by
  simp only [splitEquiv_symm_apply, Fin.addCases_right]

section AppendSplit

variable {m k : ℕ} {W₁ : Fin m → Type u} {W₂ : Fin k → Type u}

/-- The configurations of an appended wire family identify with the product of
the configurations of the factors: splitting an appended family recovers the
two factor families. -/
def splitAppendEquiv (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) :
    (∀ i, append W₁ W₂ i) ≃ (∀ i, W₁ i) × (∀ j, W₂ j) :=
  (splitEquiv (append W₁ W₂)).trans
    (Equiv.prodCongr
      (Equiv.piCongrRight fun i => Equiv.cast (append_castAdd W₁ W₂ i))
      (Equiv.piCongrRight fun j => Equiv.cast (append_natAdd W₁ W₂ j)))

/-- Computing `splitAppendEquiv` on a configuration of an appended family. -/
theorem splitAppendEquiv_apply (W₁ : Fin m → Type u) (W₂ : Fin k → Type u)
    (f : ∀ i, append W₁ W₂ i) :
    splitAppendEquiv W₁ W₂ f =
      (fun i => Equiv.cast (append_castAdd W₁ W₂ i) (f (Fin.castAdd k i)),
        fun j => Equiv.cast (append_natAdd W₁ W₂ j) (f (Fin.natAdd m j))) := by
  ext i <;> rfl

/-- Assembling a pair of factor configurations and splitting the result
recovers the factors. -/
theorem splitAppendEquiv_symm_apply (W₁ : Fin m → Type u) (W₂ : Fin k → Type u)
    (g₁ : ∀ i, W₁ i) (g₂ : ∀ j, W₂ j) :
    (splitAppendEquiv W₁ W₂).symm (g₁, g₂) =
      Fin.addCases (fun i => Equiv.cast (append_castAdd W₁ W₂ i).symm (g₁ i))
        (fun j => Equiv.cast (append_natAdd W₁ W₂ j).symm (g₂ j)) := by
  have hc : ∀ {α β : Type u} (h : α = β) (x : β), Equiv.cast h (Equiv.cast h.symm x) = x := by
    intro α β h x
    subst h
    rfl
  apply (splitAppendEquiv W₁ W₂).injective
  rw [Equiv.apply_symm_apply, splitAppendEquiv_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · show g₁ i = Equiv.cast (append_castAdd W₁ W₂ i) (Fin.addCases _ _ (Fin.castAdd k i))
    rw [Fin.addCases_left]
    exact (hc _ _).symm
  · show g₂ j = Equiv.cast (append_natAdd W₁ W₂ j) (Fin.addCases _ _ (Fin.natAdd m j))
    rw [Fin.addCases_right]
    exact (hc _ _).symm

end AppendSplit

/-! ## Permuting wire families -/

section Permute

variable {n : ℕ} {W : Fin n → Type u}

/-- The wire family `W` with its wires reordered along `e`. -/
abbrev permute (W : Fin n → Type u) (e : Fin n ≃ Fin n) : Fin n → Type u :=
  fun i => W (e i)

/-- Reordering the wires of a joint configuration along `e`: the permuted
configuration carries at wire `i` the value of the original configuration at
wire `e i`. -/
def permuteEquiv (W : Fin n → Type u) (e : Fin n ≃ Fin n) :
    (∀ i, W i) ≃ (∀ i, W (e i)) :=
  (Equiv.piCongrLeft W e).symm

/-- Computing `permuteEquiv`: entrywise reindexing along `e`. -/
@[simp]
theorem permuteEquiv_apply (W : Fin n → Type u) (e : Fin n ≃ Fin n) (f : ∀ i, W i)
    (i : Fin n) :
    permuteEquiv W e f i = f (e i) :=
  rfl

/-- The inverse wire permutation transports along `e.symm`, up to the
canonical identification of `W (e (e.symm i))` with `W i`. -/
theorem permuteEquiv_symm_apply (W : Fin n → Type u) (e : Fin n ≃ Fin n)
    (g : ∀ i, W (e i)) (i : Fin n) :
    (permuteEquiv W e).symm g i = e.apply_symm_apply i ▸ g (e.symm i) :=
  Equiv.piCongrLeft_apply W e g i

/-- Permuting by the identity equivalence is the identity on configurations. -/
theorem permuteEquiv_refl (W : Fin n → Type u) :
    permuteEquiv W (Equiv.refl (Fin n)) = Equiv.refl (∀ i, W i) := by
  ext f i
  rfl

/-- Permutation of wires is contravariantly functorial in the reordering
equivalence. -/
theorem permuteEquiv_trans (W : Fin n → Type u) (e₁ e₂ : Fin n ≃ Fin n) :
    permuteEquiv W (e₁.trans e₂) =
      (permuteEquiv W e₂).trans (permuteEquiv (fun i => W (e₂ i)) e₁) := by
  ext f i
  rfl

/-- Permuting the wires preserves the cardinality product. -/
theorem card_permute [∀ i, Fintype (W i)] (e : Fin n ≃ Fin n) :
    ∏ i, Fintype.card (W (e i)) = ∏ i, Fintype.card (W i) :=
  Equiv.prod_comp e fun i => Fintype.card (W i)

end Permute

/-! ## Reindexing vectors and matrices -/

section Reindex

variable {ι κ τ : Type*}

/-- Transport of complex vectors along an equivalence of index types:
`vecReindex e v` is the vector on `κ` whose entry at `k` is the entry of `v`
at `e.symm k`. -/
def vecReindex (e : ι ≃ κ) : (ι → ℂ) ≃ (κ → ℂ) where
  toFun v k := v (e.symm k)
  invFun w i := w (e i)
  left_inv v := funext fun i => by simp
  right_inv w := funext fun k => by simp

/-- Computing `vecReindex`: entrywise reindexing along `e.symm`. -/
@[simp]
theorem vecReindex_apply (e : ι ≃ κ) (v : ι → ℂ) (k : κ) :
    vecReindex e v k = v (e.symm k) :=
  rfl

/-- Computing the inverse of `vecReindex`: entrywise reindexing along `e`. -/
@[simp]
theorem vecReindex_symm_apply (e : ι ≃ κ) (w : κ → ℂ) (i : ι) :
    (vecReindex e).symm w i = w (e i) :=
  rfl

/-- Reindexing by the identity equivalence is the identity on vectors. -/
theorem vecReindex_refl : vecReindex (Equiv.refl ι) = Equiv.refl (ι → ℂ) := by
  ext v k
  rfl

/-- Reindexing vectors is contravariantly functorial in the index
equivalence. -/
theorem vecReindex_trans (e₁ : ι ≃ κ) (e₂ : κ ≃ τ) :
    vecReindex (e₁.trans e₂) = (vecReindex e₁).trans (vecReindex e₂) := by
  ext v t
  rfl

/-- Reindexing a vector preserves its total sum. -/
theorem vecReindex_sum [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : ι → ℂ) :
    ∑ k, vecReindex e v k = ∑ i, v i :=
  Equiv.sum_comp e.symm v

/-- Transport of complex square matrices along an equivalence of index types:
`matReindex e M` is the matrix on `κ` whose `(k, k')` entry is the
`(e.symm k, e.symm k')` entry of `M`. -/
def matReindex (e : ι ≃ κ) : CMatrix ι ≃ CMatrix κ :=
  Matrix.reindex e e

/-- Computing `matReindex`: entrywise reindexing along `e.symm`. -/
@[simp]
theorem matReindex_apply (e : ι ≃ κ) (M : CMatrix ι) (k k' : κ) :
    matReindex e M k k' = M (e.symm k) (e.symm k') :=
  rfl

/-- Computing the inverse of `matReindex`: entrywise reindexing along `e`. -/
@[simp]
theorem matReindex_symm_apply (e : ι ≃ κ) (N : CMatrix κ) (i i' : ι) :
    (matReindex e).symm N i i' = N (e i) (e i') :=
  rfl

/-- Reindexing by the identity equivalence is the identity on matrices. -/
theorem matReindex_refl (M : CMatrix ι) : matReindex (Equiv.refl ι) M = M :=
  Matrix.reindex_refl_refl M

/-- Reindexing matrices is contravariantly functorial in the index
equivalence. -/
theorem matReindex_trans (e₁ : ι ≃ κ) (e₂ : κ ≃ τ) :
    matReindex (e₁.trans e₂) = (matReindex e₁).trans (matReindex e₂) :=
  (Matrix.reindex_trans e₁ e₁ e₂ e₂).symm

/-- Reindexing preserves matrix multiplication. -/
theorem matReindex_mul [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M N : CMatrix ι) :
    matReindex e (M * N) = matReindex e M * matReindex e N :=
  (Matrix.submatrix_mul_equiv M N e.symm e.symm e.symm).symm

/-- Reindexing preserves the identity matrix. -/
theorem matReindex_one [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    matReindex e (1 : CMatrix ι) = 1 :=
  Matrix.submatrix_one_equiv e.symm

/-- Reindexing preserves the trace. -/
theorem matReindex_trace [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M : CMatrix ι) :
    (matReindex e M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag, matReindex_apply]
  exact Equiv.sum_comp e.symm fun i => M i i

/-- Reindexing commutes with the conjugate transpose. -/
theorem matReindex_conjTranspose (e : ι ≃ κ) (M : CMatrix ι) :
    matReindex e (Matrix.conjTranspose M) = Matrix.conjTranspose (matReindex e M) :=
  rfl

/-- Reindexing a Kronecker product along a product of equivalences is the
Kronecker product of the reindexed factors. -/
theorem matReindex_kronecker_prodCongr {ι₁ κ₁ ι₂ κ₂ : Type*}
    (e₁ : ι₁ ≃ κ₁) (e₂ : ι₂ ≃ κ₂) (M : CMatrix ι₁) (N : CMatrix ι₂) :
    matReindex (Equiv.prodCongr e₁ e₂) (Matrix.kronecker M N) =
      Matrix.kronecker (matReindex e₁ M) (matReindex e₂ N) := by
  ext ⟨k₁, k₂⟩ ⟨k₁', k₂'⟩
  rfl

/-- The inverse of matrix reindexing is reindexing along the inverse
equivalence. -/
theorem matReindex_symm (e : ι ≃ κ) :
    (matReindex e).symm = matReindex e.symm :=
  rfl

/-- Reindexing preserves matrix addition. -/
theorem matReindex_add (e : ι ≃ κ) (M N : CMatrix ι) :
    matReindex e (M + N) = matReindex e M + matReindex e N :=
  rfl

/-- Reindexing preserves matrix subtraction. -/
theorem matReindex_sub (e : ι ≃ κ) (M N : CMatrix ι) :
    matReindex e (M - N) = matReindex e M - matReindex e N :=
  rfl

/-- Reindexing along a composite equivalence is the composite of the
reindexings, applied outermost-last. -/
theorem matReindex_trans_apply (e₁ : ι ≃ κ) (e₂ : κ ≃ τ) (M : CMatrix ι) :
    matReindex (e₁.trans e₂) M = matReindex e₂ (matReindex e₁ M) :=
  rfl

/-- Matrix reindexing as a multiplicative monoid homomorphism. This is the
`matReindex` spelling of `(Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom`
(`Matrix.reindexAlgEquiv_apply`). -/
def matReindexMonoidHom [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : CMatrix ι →* CMatrix κ where
  toFun := matReindex e
  map_one' := matReindex_one e
  map_mul' := matReindex_mul e

/-- The monoid-homomorphism form of reindexing agrees with reindexing. -/
@[simp]
theorem matReindexMonoidHom_apply [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (M : CMatrix ι) :
    matReindexMonoidHom e M = matReindex e M :=
  rfl

/-- Reindexing distributes over a finset noncommutative product of matrices. -/
theorem matReindex_noncommProd [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {γ : Type*} (e : ι ≃ κ) (s : Finset γ) (f : γ → CMatrix ι)
    (comm : (s : Set γ).Pairwise (Function.onFun Commute f)) :
    matReindex e (s.noncommProd f comm) =
      s.noncommProd (fun i => matReindex e (f i))
        (fun _ hx _ hy h => (comm hx hy h).map (matReindexMonoidHom e)) :=
  Finset.map_noncommProd s f comm (matReindexMonoidHom e)

end Reindex

/-! ## Head-tail splits for noncommutative products over `Fin` -/

section NoncommProdFin

variable {α β : Type*} [Monoid β]

/-- A noncommutative product over a mapped finset is a noncommutative product
over the source finset. -/
theorem finset_noncommProd_map {γ : Type*} (s : Finset α) (e : α ↪ γ)
    (f : γ → β)
    (comm : (s.map e : Set γ).Pairwise (Function.onFun Commute f)) :
    (s.map e).noncommProd f comm =
      s.noncommProd (fun a => f (e a))
        (fun x hx y hy h =>
          comm (Finset.mem_map.2 ⟨x, hx, rfl⟩) (Finset.mem_map.2 ⟨y, hy, rfl⟩)
            (e.injective.ne h)) := by
  simp [Finset.noncommProd, Multiset.map_map]

/-- Head-tail split of a noncommutative product over `Fin (n + 1)` at a pivot:
the product is the pivot factor times the product over the remaining wires. -/
theorem fin_noncommProd_univ_succAbove {n : ℕ} (f : Fin (n + 1) → β)
    (comm : ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).Pairwise
      (Function.onFun Commute f)) (x : Fin (n + 1)) :
    Finset.univ.noncommProd f comm =
      f x * Finset.univ.noncommProd (fun i : Fin n => f (x.succAbove i))
        (fun a _ b _ h =>
          comm (Finset.mem_univ (x.succAbove a))
            (Finset.mem_univ (x.succAbove b))
            (Fin.succAbove_right_injective.ne h)) := by
  exact (Finset.noncommProd_congr (Fin.univ_succAbove n x)
    (fun _ _ => rfl) comm).trans
    ((Finset.noncommProd_cons _ _ _ _ _).trans
      (congrArg (fun y => f x * y)
        (finset_noncommProd_map Finset.univ x.succAboveEmb f _)))

/-- Head-tail split of a noncommutative product over `Fin (n + 1)` at wire
zero: the product is the zero factor times the product over the successors. -/
theorem fin_noncommProd_univ_succ {n : ℕ} (f : Fin (n + 1) → β)
    (comm : ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).Pairwise
      (Function.onFun Commute f)) :
    Finset.univ.noncommProd f comm =
      f 0 * Finset.univ.noncommProd (fun i : Fin n => f i.succ)
        (fun a _ b _ h =>
          comm (Finset.mem_univ a.succ) (Finset.mem_univ b.succ)
            ((Fin.succ_injective n).ne h)) :=
  fin_noncommProd_univ_succAbove f comm 0

end NoncommProdFin

/-! ## Factor extraction at a single wire -/

section FactorExtraction

variable {n : ℕ}

/-- Extraction of wire `i` from a joint configuration: the joint configuration
space of a wire family over `Fin (n + 1)` is canonically the factor at `i`
times the joint configuration space of the remaining wires. This is the
register-discipline equivalence that makes the placement of a single tensor
factor explicit
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:216-216]. -/
def extractAt (W : Fin (n + 1) → Type u) (i : Fin (n + 1)) :
    (∀ j, W j) ≃ W i × (∀ j : Fin n, W (i.succAbove j)) :=
  (Fin.insertNthEquiv W i).symm

/-- Extraction returns the value at the extracted wire together with the
restriction to the remaining wires. -/
@[simp]
theorem extractAt_apply (W : Fin (n + 1) → Type u) (i : Fin (n + 1))
    (f : ∀ j, W j) :
    extractAt W i f = (f i, Fin.removeNth i f) :=
  rfl

/-- The inverse of extraction inserts a value at the extracted wire. -/
@[simp]
theorem extractAt_symm_apply (W : Fin (n + 1) → Type u) (i : Fin (n + 1))
    (x : W i) (g : ∀ j : Fin n, W (i.succAbove j)) :
    (extractAt W i).symm (x, g) = Fin.insertNth i x g :=
  rfl

/-- Inserting at wire `i` and reading wire `i` returns the inserted value. -/
theorem extractAt_symm_apply_same (W : Fin (n + 1) → Type u)
    (i : Fin (n + 1)) (x : W i) (g : ∀ j : Fin n, W (i.succAbove j)) :
    (extractAt W i).symm (x, g) i = x := by
  rw [extractAt_symm_apply, Fin.insertNth_apply_same]

/-- Inserting at wire `i` and reading any other wire returns the complementary
value. -/
theorem extractAt_symm_apply_succAbove (W : Fin (n + 1) → Type u)
    (i : Fin (n + 1)) (x : W i) (g : ∀ j : Fin n, W (i.succAbove j))
    (j : Fin n) :
    (extractAt W i).symm (x, g) (i.succAbove j) = g j := by
  rw [extractAt_symm_apply, Fin.insertNth_apply_succAbove]

/-- Extraction at wire zero of a constant family is the inverse of the
cons-equivalence. -/
theorem extractAt_zero {a : Type u} :
    extractAt (fun _ : Fin (n + 1) => a) 0 =
      (Fin.consEquiv (fun _ : Fin (n + 1) => a)).symm := by
  simp only [extractAt, Fin.insertNthEquiv_zero]

end FactorExtraction

/-! ## Operators acting on a single wire -/

section LocalLift

variable {n : ℕ} {W : Fin (n + 1) → Type u} [∀ j, Fintype (W j)]
  [∀ j, DecidableEq (W j)]

/-- Lift of an operator on wire `i` to the joint system: under the extraction
equivalence it acts as `M` on factor `i` and as the identity on the remaining
wires. This makes the tensor-factor placement of local operators explicit
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:216-216]. -/
def liftAt (W : Fin (n + 1) → Type u) [∀ j, Fintype (W j)]
    [∀ j, DecidableEq (W j)] (i : Fin (n + 1)) (M : CMatrix (W i)) :
    CMatrix (∀ j, W j) :=
  (matReindex (extractAt W i)).symm
    (M ⊗ₖ (1 : CMatrix (∀ j : Fin n, W (i.succAbove j))))

/-- Entrywise characterization of a lifted operator. -/
@[simp]
theorem liftAt_apply (i : Fin (n + 1)) (M : CMatrix (W i))
    (x y : ∀ j, W j) :
    liftAt W i M x y =
      M (x i) (y i) *
        (1 : CMatrix (∀ j : Fin n, W (i.succAbove j)))
          (fun j => x (i.succAbove j)) (fun j => y (i.succAbove j)) :=
  rfl

/-- Entrywise characterization of a lifted operator, with the identity factor
as a product of diagonal tests. -/
theorem liftAt_apply_prod (i : Fin (n + 1)) (M : CMatrix (W i))
    (x y : ∀ j, W j) :
    liftAt W i M x y =
      M (x i) (y i) *
        ∏ j : Fin n,
          (if x (i.succAbove j) = y (i.succAbove j) then (1 : ℂ) else 0) := by
  rw [liftAt_apply, Matrix.one_apply, Finset.prod_boole]
  simp only [funext_iff, Finset.mem_univ, true_implies]

/-- The extracted image of a lifted operator is the Kronecker product with the
identity on the remaining wires. -/
theorem liftAt_eq_kronecker (i : Fin (n + 1)) (M : CMatrix (W i)) :
    matReindex (extractAt W i) (liftAt W i M) =
      M ⊗ₖ (1 : CMatrix (∀ j : Fin n, W (i.succAbove j))) :=
  Equiv.apply_symm_apply _ _

/-- Lifting the identity yields the identity. -/
theorem liftAt_one (i : Fin (n + 1)) : liftAt W i (1 : CMatrix (W i)) = 1 := by
  apply (matReindex (extractAt W i)).injective
  rw [liftAt_eq_kronecker, Matrix.one_kronecker_one, matReindex_one]

/-- Lifting preserves multiplication. -/
theorem liftAt_mul (i : Fin (n + 1)) (A B : CMatrix (W i)) :
    liftAt W i (A * B) = liftAt W i A * liftAt W i B := by
  apply (matReindex (extractAt W i)).injective
  rw [liftAt_eq_kronecker, matReindex_mul, liftAt_eq_kronecker,
    liftAt_eq_kronecker, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Lifting preserves addition. -/
theorem liftAt_add (i : Fin (n + 1)) (A B : CMatrix (W i)) :
    liftAt W i (A + B) = liftAt W i A + liftAt W i B := by
  apply (matReindex (extractAt W i)).injective
  rw [liftAt_eq_kronecker, matReindex_add, liftAt_eq_kronecker,
    liftAt_eq_kronecker, Matrix.add_kronecker]

/-- Lifting preserves subtraction. -/
theorem liftAt_sub (i : Fin (n + 1)) (A B : CMatrix (W i)) :
    liftAt W i (A - B) = liftAt W i A - liftAt W i B := by
  apply (matReindex (extractAt W i)).injective
  rw [liftAt_eq_kronecker, matReindex_sub, liftAt_eq_kronecker,
    liftAt_eq_kronecker]
  ext ⟨x₀, g⟩ ⟨y₀, g'⟩
  simp [Matrix.sub_apply, sub_mul]

/-- Lifting preserves the conjugate transpose. -/
@[simp]
theorem liftAt_conjTranspose (i : Fin (n + 1)) (M : CMatrix (W i)) :
    liftAt W i (Matrix.conjTranspose M) =
      Matrix.conjTranspose (liftAt W i M) := by
  apply (matReindex (extractAt W i)).injective
  rw [liftAt_eq_kronecker, matReindex_conjTranspose, liftAt_eq_kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Lifting preserves Hermiticity. -/
theorem liftAt_isHermitian (i : Fin (n + 1)) {M : CMatrix (W i)}
    (h : M.IsHermitian) : (liftAt W i M).IsHermitian := by
  show Matrix.conjTranspose (liftAt W i M) = liftAt W i M
  rw [← liftAt_conjTranspose, h]

/-- Lifting preserves positive semidefiniteness. -/
theorem liftAt_posSemidef (i : Fin (n + 1)) {M : CMatrix (W i)}
    (h : M.PosSemidef) : (liftAt W i M).PosSemidef := by
  have hk : (M ⊗ₖ (1 : CMatrix (∀ j : Fin n, W (i.succAbove j)))).PosSemidef :=
    h.kronecker Matrix.PosSemidef.one
  have heq : liftAt W i M =
      (M ⊗ₖ (1 : CMatrix (∀ j : Fin n, W (i.succAbove j)))).submatrix
        (extractAt W i) (extractAt W i) :=
    rfl
  rw [heq]
  exact (Matrix.posSemidef_submatrix_equiv (extractAt W i)).2 hk

/-- Lifting preserves idempotence. -/
theorem liftAt_idempotent (i : Fin (n + 1)) {M : CMatrix (W i)}
    (h : M * M = M) : liftAt W i M * liftAt W i M = liftAt W i M := by
  rw [← liftAt_mul, h]

end LocalLift

/-! ## The recursion principle for local operators -/

section LocalLiftRec

variable {n : ℕ} {W : Fin (n + 2) → Type u} [∀ j, Fintype (W j)]
  [∀ j, DecidableEq (W j)]

/-- Lifting at the `i.succAbove j` position, seen through the extraction at
wire `i`, is the identity on wire `i` tensored with the lift at `j` on the
remaining wires: the recursion principle for local operators. -/
theorem liftAt_succAbove (i : Fin (n + 2)) (j : Fin (n + 1))
    (M : CMatrix (W (i.succAbove j))) :
    matReindex (extractAt W i) (liftAt W (i.succAbove j) M) =
      (1 : CMatrix (W i)) ⊗ₖ liftAt (fun j : Fin (n + 1) => W (i.succAbove j)) j M := by
  ext ⟨x₀, g⟩ ⟨y₀, g'⟩
  rw [matReindex_apply, liftAt_apply_prod, Matrix.kronecker_apply,
    Matrix.one_apply, liftAt_apply_prod]
  simp only [extractAt_symm_apply_succAbove]
  rw [Fin.prod_univ_succAbove _ (j.predAbove i),
    Fin.succAbove_succAbove_predAbove]
  simp only [extractAt_symm_apply_same]
  have hfactor : ∀ l : Fin n,
      (if (extractAt W i).symm (x₀, g)
            ((i.succAbove j).succAbove ((j.predAbove i).succAbove l)) =
          (extractAt W i).symm (y₀, g')
            ((i.succAbove j).succAbove ((j.predAbove i).succAbove l))
        then (1 : ℂ) else 0) =
      if g (j.succAbove l) = g' (j.succAbove l) then (1 : ℂ) else 0 := by
    intro l
    rw [Fin.succAbove_succAbove_succAbove_predAbove]
    simp only [extractAt_symm_apply_succAbove]
  simp only [hfactor]
  ring

end LocalLiftRec

/-! ## Commutation of local lifts and defect operators -/

section LocalLiftComm

variable {n : ℕ} {W : Fin (n + 1) → Type u} [∀ j, Fintype (W j)]
  [∀ j, DecidableEq (W j)]

/-- Lifts of operators at distinct wires commute. -/
theorem liftAt_commute (i j : Fin (n + 1)) (hij : i ≠ j)
    (A : CMatrix (W i)) (B : CMatrix (W j)) :
    Commute (liftAt W i A) (liftAt W j B) := by
  cases n with
  | zero =>
      have h : i = j := by
        ext
        have hi := i.isLt
        have hj := j.isLt
        omega
      exact absurd h hij
  | succ n' =>
      have hj : ∃ j₀ : Fin (n' + 1), i.succAbove j₀ = j := by
        rcases hfc : finSuccEquiv' i j with _ | k
        · exact absurd (finSuccEquiv'_eq_none.mp hfc) hij
        · exact ⟨k, (finSuccEquiv'_eq_some.mp hfc).symm⟩
      obtain ⟨j₀, rfl⟩ := hj
      show liftAt W i A * liftAt W (i.succAbove j₀) B =
        liftAt W (i.succAbove j₀) B * liftAt W i A
      apply (matReindex (extractAt W i)).injective
      rw [matReindex_mul, matReindex_mul, liftAt_eq_kronecker, liftAt_succAbove,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp only [Matrix.mul_one, Matrix.one_mul]

/-- The lifted copies of a single operator across the wires of a constant
family pairwise commute: the side condition for noncommutative products of
local operators. -/
theorem liftAt_pairwise_commute {a : Type u} [Fintype a] [DecidableEq a]
    (M : CMatrix a) :
    ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).Pairwise
      (Function.onFun Commute fun i => liftAt (fun _ : Fin (n + 1) => a) i M) := by
  intro x _ y _ h
  exact liftAt_commute (W := fun _ : Fin (n + 1) => a) x y h M M

/-- The complementary local operator `1 - liftAt W i M`: for a projector `M`
this is the defect operator of the register discipline
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:533-533]. -/
def deltaAt (W : Fin (n + 1) → Type u) [∀ j, Fintype (W j)]
    [∀ j, DecidableEq (W j)] (i : Fin (n + 1)) (M : CMatrix (W i)) :
    CMatrix (∀ j, W j) :=
  1 - liftAt W i M

/-- Defect operators at distinct wires commute. -/
theorem deltaAt_comm_of_ne {i j : Fin (n + 1)} (hij : i ≠ j)
    (M : CMatrix (W i)) (N : CMatrix (W j)) :
    Commute (deltaAt W i M) (deltaAt W j N) := by
  have h : Commute (liftAt W i M) (liftAt W j N) :=
    liftAt_commute i j hij M N
  exact ((Commute.one_left (1 - liftAt W j N)).sub_left
    ((Commute.one_right _).sub_right h))

/-- Defect operators at any two wires of a constant family commute. -/
theorem deltaAt_comm {a : Type u} [Fintype a] [DecidableEq a]
    (i j : Fin (n + 1)) (M : CMatrix a) :
    Commute (deltaAt (fun _ : Fin (n + 1) => a) i M)
      (deltaAt (fun _ : Fin (n + 1) => a) j M) := by
  by_cases h : i = j
  · subst h; exact Commute.refl _
  · exact deltaAt_comm_of_ne (W := fun _ : Fin (n + 1) => a) h M M

/-- The defect operator is the lift of the complementary operator. -/
theorem deltaAt_eq_liftAt_one_sub (i : Fin (n + 1)) (M : CMatrix (W i)) :
    deltaAt W i M = liftAt W i (1 - M) := by
  show 1 - liftAt W i M = liftAt W i (1 - M)
  rw [liftAt_sub, liftAt_one]

/-- Defect operators of a single operator across the wires of a constant
family pairwise commute on any finset: the side condition for noncommutative
products of defect operators. -/
theorem deltaAt_pairwise_commute {a : Type u} [Fintype a] [DecidableEq a]
    (M : CMatrix a) (s : Finset (Fin (n + 1))) :
    (s : Set (Fin (n + 1))).Pairwise
      (Function.onFun Commute fun i => deltaAt (fun _ : Fin (n + 1) => a) i M) :=
  fun x _ y _ _ => deltaAt_comm x y M

/-- Defect operators of idempotents are idempotent. -/
theorem deltaAt_idempotent (i : Fin (n + 1)) {M : CMatrix (W i)}
    (h : M * M = M) : deltaAt W i M * deltaAt W i M = deltaAt W i M := by
  have h' := liftAt_idempotent i h
  calc (1 - liftAt W i M) * (1 - liftAt W i M)
      = 1 - liftAt W i M - liftAt W i M + liftAt W i M * liftAt W i M := by
        noncomm_ring
    _ = 1 - liftAt W i M := by rw [h']; abel

/-- Defect operators of Hermitian operators are Hermitian. -/
theorem deltaAt_isHermitian (i : Fin (n + 1)) {M : CMatrix (W i)}
    (h : M.IsHermitian) : (deltaAt W i M).IsHermitian :=
  Matrix.isHermitian_one.sub (liftAt_isHermitian i h)

end LocalLiftComm

/-! ## Wire-indexed reindexing -/

section WireReindex

/-- Transport of complex vectors along a permutation of the wires. -/
def vecPermute {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n) :
    ((∀ i, W i) → ℂ) ≃ ((∀ i, W (e i)) → ℂ) :=
  vecReindex (permuteEquiv W e)

/-- Computing `vecPermute` on a permuted configuration. -/
theorem vecPermute_apply {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n)
    (v : (∀ i, W i) → ℂ) (g : ∀ i, W (e i)) :
    vecPermute W e v g = v ((permuteEquiv W e).symm g) :=
  rfl

/-- Transport of complex matrices along a permutation of the wires. -/
def matPermute {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n) :
    CMatrix (∀ i, W i) ≃ CMatrix (∀ i, W (e i)) :=
  matReindex (permuteEquiv W e)

/-- Computing `matPermute` on a pair of permuted configurations. -/
theorem matPermute_apply {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n)
    (M : CMatrix (∀ i, W i)) (g g' : ∀ i, W (e i)) :
    matPermute W e M g g' = M ((permuteEquiv W e).symm g) ((permuteEquiv W e).symm g') :=
  rfl

/-- Transport of complex vectors along the split of a wire family at `m`. -/
def vecSplit {m k : ℕ} (W : Fin (m + k) → Type u) :
    ((∀ i, W i) → ℂ) ≃
      ((∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j)) → ℂ) :=
  vecReindex (splitEquiv W)

/-- Computing `vecSplit` on a pair of partial configurations. -/
theorem vecSplit_apply {m k : ℕ} (W : Fin (m + k) → Type u) (v : (∀ i, W i) → ℂ)
    (p : (∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j))) :
    vecSplit W v p = v ((splitEquiv W).symm p) :=
  rfl

/-- Transport of complex matrices along the split of a wire family at `m`. -/
def matSplit {m k : ℕ} (W : Fin (m + k) → Type u) :
    CMatrix (∀ i, W i) ≃
      CMatrix ((∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j))) :=
  matReindex (splitEquiv W)

/-- Computing `matSplit` on a pair of partial configurations. -/
theorem matSplit_apply {m k : ℕ} (W : Fin (m + k) → Type u) (M : CMatrix (∀ i, W i))
    (p p' : (∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j))) :
    matSplit W M p p' = M ((splitEquiv W).symm p) ((splitEquiv W).symm p') :=
  rfl

end WireReindex

end WireFam

end QIT
