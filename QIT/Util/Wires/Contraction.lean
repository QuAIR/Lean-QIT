/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Wires
public import QIT.Util.Matrix

/-!
# Wire contractions: coordinate partial trace and partial transpose

This module realizes the contraction layer over heterogeneous finite wire
families (`QIT.Util.Wires`): the two coordinate operations that contract a
joint matrix on `W : Fin n → Type u` along one wire, or along a final block
of wires, with no common dimension across wires.

* **Coordinate partial trace.** `traceAt W i M` contracts wire `i` of a joint
  matrix `M`, leaving the remaining wires `W (i.succAbove j)` untouched: it is
  defined by extracting wire `i` to the front (via `extractAt` and
  `matReindex`) and applying the two-system `QIT.partialTraceA`.
  `traceOutLast W M` contracts the last `k` wires of a family of length `m + k`
  via `matSplit` and `QIT.partialTraceB`. Both come with entrywise forms
  (`traceAt_apply`, `traceOutLast_apply`, `traceOutLast_apply'`).

* **Coordinate partial transpose.** `transposeAt W i M` exchanges the wire-`i`
  values of the row and column configurations. It is basis-explicit and
  instance-free: the transpose basis is the computational basis of the joint
  configuration space, and the connected-wire orientation stays visible in the
  statement.

* **Algebraic contracts.** The trace/adjoint/Hermitian/PSD/monotonicity lemmas
  required by Choi contractions (`traceAt_trace`, `traceAt_conjTranspose`,
  `traceAt_isHermitian`, `traceAt_posSemidef`, `traceAt_mono`,
  `traceOutLast_posSemidef`), the linearity contracts (`traceAt_add`,
  `traceAt_smul`, `traceAt_sub`, `traceOutLast_add`, `traceOutLast_smul`,
  `traceOutLast_sub`), the behavior on lifted single-wire operators
  (`traceAt_liftAt`, `transposeAt_liftAt`), and the interaction with the
  extract-at-`i` coordinates: extraction conjugates `transposeAt W i` into the
  two-system `QIT.partialTransposeA` (`matReindex_extractAt_transposeAt`), and
  transposing a nested wire `i.succAbove j` becomes the slot-`j` transpose of
  the remaining family
  (`matReindex_extractAt_transposeAt_succAbove_apply`,
  `matReindex_extractAt_transposeAt_succAbove`). The coordinate transposes are
  involutive (`transposeAt_involutive`) and commute at distinct wires
  (`transposeAt_commute`).

* **Generic compatibility with split, permute, and composition.** For
  arbitrary heterogeneous families, the coordinate trace at the last wire is
  the `k = 1` instance of `traceOutLast`, up to the canonical kept-wire
  identification `lastKeepEquiv` (`traceAt_last_eq_traceOutLast`,
  `traceOutLast_one_eq_traceAt`, entrywise `traceAt_last_entrywise`); tracing
  an arbitrary wire `i` equals the canonical move-to-last permutation
  `permMoveLastEquiv` followed by `traceOutLast`, up to `permKeepEquiv`
  (`traceAt_eq_permute`); double coordinate traces compose order-independently,
  up to the canonical double-removal identification `doubleRemoveEquiv`
  (`traceAt_traceAt`), realizing traces over arbitrary wire subsets; and the
  coordinate partial transpose commutes with the coordinate partial trace
  (`transposeAt_traceAt` at a distinct wire, and the trivial action
  `traceAt_transposeAt_self` at the traced wire itself). Tracing out a final
  block of `k + 1` wires splits off the last wire as a single `traceAt` and
  recurses on the last `k` wires of the shifted family, up to `succKeepEquiv`
  (`traceOutLast_succ_split`, the `traceAt`-form `traceOutLast_succ` and its
  reverse `traceOutLast_succ'`); permutation preserves positive
  semidefiniteness (`matPermute_posSemidef`). When chaining the composition
  lemmas at concrete wire positions, state the remainder family as a named
  `abbrev` so `rw` can match the higher-order pattern; residual `Fin.succAbove`
  slot arithmetic then closes by `rfl`.

## Main definitions

* `QIT.WireFam.traceAt`
* `QIT.WireFam.traceOutLast`
* `QIT.WireFam.transposeAt`

## Tags

partial trace, partial transpose, contraction, wire family
-/

open scoped BigOperators ComplexOrder MatrixOrder

universe u

@[expose] public section

namespace QIT

namespace WireFam

/-! ## Coordinate partial trace -/

/-- Coordinate partial trace over wire `i` of a joint matrix on the wire
family `W`: the wire-`i` index is contracted entrywise, and the remaining
wires keep their heterogeneous types `W (i.succAbove j)`. Defined by
extracting wire `i` to the front (via `extractAt` and `matReindex`) and
applying the two-system `QIT.partialTraceA`; no common dimension across
wires is assumed. -/
def traceAt {n : ℕ} (W : Fin (n + 1) → Type u) [∀ j, Fintype (W j)] (i : Fin (n + 1))
    (M : CMatrix (∀ j, W j)) : CMatrix (∀ j : Fin n, W (i.succAbove j)) :=
  QIT.partialTraceA (matReindex (extractAt W i) M)

/-- Entrywise form of `traceAt`: the wire-`i` value is inserted into both the
row and the column configuration and summed over. -/
theorem traceAt_apply {n : ℕ} (W : Fin (n + 1) → Type u) [∀ j, Fintype (W j)]
    (i : Fin (n + 1)) (M : CMatrix (∀ j, W j))
    (g g' : ∀ j : Fin n, W (i.succAbove j)) :
    traceAt W i M g g' = ∑ x : W i, M (Fin.insertNth i x g) (Fin.insertNth i x g') :=
  rfl

/-- Trace out the last `k` wires of a joint matrix, keeping the first `m`:
the split form of the coordinate partial trace, defined via `matSplit` and
the two-system `QIT.partialTraceB`. For the homogeneous tensor-power spelling
on states, see `QIT.State.traceOutLastK`. -/
def traceOutLast {m k : ℕ} (W : Fin (m + k) → Type u) [∀ i, Fintype (W i)]
    (M : CMatrix (∀ i, W i)) : CMatrix (∀ i, W (Fin.castAdd k i)) :=
  QIT.partialTraceB (matSplit W M)

/-- Entrywise form of `traceOutLast`. -/
theorem traceOutLast_apply {m k : ℕ} (W : Fin (m + k) → Type u) [∀ i, Fintype (W i)]
    (M : CMatrix (∀ i, W i)) (g g' : ∀ i, W (Fin.castAdd k i)) :
    traceOutLast W M g g' =
      ∑ y : ∀ j, W (Fin.natAdd m j), M (Fin.addCases g y) (Fin.addCases g' y) := by
  simp only [traceOutLast, QIT.partialTraceB, matSplit_apply, splitEquiv_symm_apply]

/-- Entrywise form of `traceOutLast` with the `Fin.addCases` arguments written
out explicitly (no eta-expansion), so that entrywise rewrites match
syntactically. -/
theorem traceOutLast_apply' {m k : ℕ} (W : Fin (m + k) → Type u) [∀ i, Fintype (W i)]
    (M : CMatrix (∀ i, W i)) (g g' : ∀ i, W (Fin.castAdd k i)) :
    traceOutLast W M g g' =
      ∑ y : ∀ j, W (Fin.natAdd m j),
        M (Fin.addCases (m := m) (n := k) (motive := W) g y)
          (Fin.addCases (m := m) (n := k) (motive := W) g' y) := by
  rw [traceOutLast_apply]

/-- Tracing out a final block of wires preserves positive semidefiniteness. -/
theorem traceOutLast_posSemidef {m k : ℕ} (W : Fin (m + k) → Type u) [∀ i, Fintype (W i)]
    {M : CMatrix (∀ i, W i)} (hM : M.PosSemidef) :
    (traceOutLast W M).PosSemidef :=
  QIT.partialTraceB_posSemidef
    ((Matrix.posSemidef_submatrix_equiv (splitEquiv W).symm).2 hM)

/-- `traceOutLast` is additive in the matrix. -/
theorem traceOutLast_add {m k : ℕ} (W : Fin (m + k) → Type u) [∀ i, Fintype (W i)]
    (X Y : CMatrix (∀ i, W i)) :
    traceOutLast W (X + Y) = traceOutLast W X + traceOutLast W Y := by
  simp only [traceOutLast, matSplit, ← QIT.partialTraceB_add, ← matReindex_add]

/-- `traceOutLast` is homogeneous. -/
theorem traceOutLast_smul {m k : ℕ} (W : Fin (m + k) → Type u) [∀ i, Fintype (W i)]
    (c : ℂ) (X : CMatrix (∀ i, W i)) :
    traceOutLast W (c • X) = c • traceOutLast W X := by
  simp only [traceOutLast, matSplit, ← QIT.partialTraceB_smul]
  rfl

/-- `traceOutLast` is subtractive. -/
theorem traceOutLast_sub {m k : ℕ} (W : Fin (m + k) → Type u) [∀ i, Fintype (W i)]
    (X Y : CMatrix (∀ i, W i)) :
    traceOutLast W (X - Y) = traceOutLast W X - traceOutLast W Y := by
  simp only [traceOutLast, matSplit, ← QIT.partialTraceB_sub, ← matReindex_sub]

/-! ## Coordinate partial transpose -/

/-- Coordinate partial transpose on wire `i`: the wire-`i` values of the row
and column configurations are exchanged. The transpose basis is the
computational basis of the joint configuration space and stays explicit; no
typeclass assumption on the family is needed. -/
def transposeAt {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1))
    (M : CMatrix (∀ j, W j)) : CMatrix (∀ j, W j) :=
  fun x y =>
    M (Fin.insertNth i (y i) (Fin.removeNth i x)) (Fin.insertNth i (x i) (Fin.removeNth i y))

/-- Entrywise form of `transposeAt`. -/
@[simp]
theorem transposeAt_apply {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1))
    (M : CMatrix (∀ j, W j)) (x y : ∀ j, W j) :
    transposeAt W i M x y =
      M (Fin.insertNth i (y i) (Fin.removeNth i x)) (Fin.insertNth i (x i) (Fin.removeNth i y)) :=
  rfl

/-! ## Algebraic contracts -/

section Contracts

variable {n : ℕ} {W : Fin (n + 1) → Type u} [∀ j, Fintype (W j)]

/-- Bridge between the `Matrix.kroneckerMap` multiplication and the
`Matrix.kronecker` alias. -/
private theorem kroneckerMap_mul {ι₁ ι₂ : Type*} (M : CMatrix ι₁) (N : CMatrix ι₂) :
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M N = Matrix.kronecker M N :=
  rfl

/-- Tracing out wire `i` of a lifted single-wire operator scales the identity
by the trace of the lifted factor. -/
theorem traceAt_liftAt [∀ j, DecidableEq (W j)] (i : Fin (n + 1)) (M : CMatrix (W i)) :
    traceAt W i (liftAt W i M) =
      matrixScale M.trace (1 : CMatrix (∀ j : Fin n, W (i.succAbove j))) := by
  show QIT.partialTraceA (matReindex (extractAt W i) (liftAt W i M)) = _
  rw [liftAt_eq_kronecker, kroneckerMap_mul, QIT.partialTraceA_kronecker]

/-- The coordinate partial trace preserves the total trace. -/
theorem traceAt_trace (i : Fin (n + 1)) (M : CMatrix (∀ j, W j)) :
    (traceAt W i M).trace = M.trace := by
  show (QIT.partialTraceA (matReindex (extractAt W i) M)).trace = M.trace
  rw [QIT.partialTraceA_trace, matReindex_trace]

/-- `traceAt` is additive in the matrix. -/
theorem traceAt_add (i : Fin (n + 1)) (X Y : CMatrix (∀ j, W j)) :
    traceAt W i (X + Y) = traceAt W i X + traceAt W i Y := by
  simp only [traceAt, ← QIT.partialTraceA_add, ← matReindex_add]

/-- `traceAt` is homogeneous. -/
theorem traceAt_smul (c : ℂ) (i : Fin (n + 1)) (X : CMatrix (∀ j, W j)) :
    traceAt W i (c • X) = c • traceAt W i X := by
  simp only [traceAt, ← QIT.partialTraceA_smul]
  rfl

/-- `traceAt` is subtractive. -/
theorem traceAt_sub (i : Fin (n + 1)) (X Y : CMatrix (∀ j, W j)) :
    traceAt W i (X - Y) = traceAt W i X - traceAt W i Y := by
  simp only [traceAt, ← QIT.partialTraceA_sub, ← matReindex_sub]

/-- The coordinate partial trace commutes with the conjugate transpose. -/
theorem traceAt_conjTranspose (i : Fin (n + 1)) (M : CMatrix (∀ j, W j)) :
    Matrix.conjTranspose (traceAt W i M) = traceAt W i (Matrix.conjTranspose M) := by
  show Matrix.conjTranspose (QIT.partialTraceA (matReindex (extractAt W i) M)) = _
  rw [QIT.partialTraceA_conjTranspose, ← matReindex_conjTranspose]
  rfl

/-- The coordinate partial trace preserves Hermiticity. -/
theorem traceAt_isHermitian (i : Fin (n + 1)) {M : CMatrix (∀ j, W j)}
    (hM : M.IsHermitian) : (traceAt W i M).IsHermitian := by
  rw [Matrix.IsHermitian, traceAt_conjTranspose, hM]

/-- The coordinate partial trace preserves positive semidefiniteness. -/
theorem traceAt_posSemidef (i : Fin (n + 1))
    {M : CMatrix (∀ j, W j)} (hM : M.PosSemidef) : (traceAt W i M).PosSemidef :=
  QIT.partialTraceA_posSemidef
    ((Matrix.posSemidef_submatrix_equiv (extractAt W i).symm).2 hM)

/-- The coordinate partial trace is monotone for the Löwner order. -/
theorem traceAt_mono (i : Fin (n + 1))
    {X Y : CMatrix (∀ j, W j)} (h : X ≤ Y) : traceAt W i X ≤ traceAt W i Y := by
  rw [Matrix.le_iff, ← traceAt_sub]
  exact traceAt_posSemidef (i := i) (Matrix.le_iff.mp h)

/-- THE bridge: extraction at `i` conjugates `transposeAt` into the
two-system `QIT.partialTransposeA`. -/
theorem matReindex_extractAt_transposeAt {n : ℕ} (W : Fin (n + 1) → Type u)
    (i : Fin (n + 1)) (M : CMatrix (∀ j, W j)) :
    matReindex (extractAt W i) (transposeAt W i M) =
      QIT.partialTransposeA (matReindex (extractAt W i) M) := by
  ext p q
  cases p with
  | mk x g =>
  cases q with
  | mk y g' =>
  simp only [matReindex_apply, QIT.partialTransposeA_apply, extractAt_symm_apply,
    transposeAt_apply, Fin.insertNth_apply_same, Fin.removeNth_insertNth]

/-- Involutivity of the coordinate partial transpose. -/
@[simp]
theorem transposeAt_involutive {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1))
    (M : CMatrix (∀ j, W j)) : transposeAt W i (transposeAt W i M) = M := by
  ext x y
  simp only [transposeAt_apply, Fin.insertNth_apply_same, Fin.removeNth_insertNth,
    Fin.insertNth_self_removeNth]

/-- Transposing a lifted operator transposes the lifted factor. -/
theorem transposeAt_liftAt {n : ℕ} {W : Fin (n + 1) → Type u} [∀ j, Fintype (W j)]
    [∀ j, DecidableEq (W j)] (i : Fin (n + 1)) (M : CMatrix (W i)) :
    transposeAt W i (liftAt W i M) = liftAt W i (Matrix.transpose M) := by
  apply (matReindex (extractAt W i)).injective
  rw [matReindex_extractAt_transposeAt, liftAt_eq_kronecker, kroneckerMap_mul,
    QIT.partialTransposeA_kronecker, ← kroneckerMap_mul, ← liftAt_eq_kronecker]

/-- Exchange law for `Fin.insertNth`/`Fin.removeNth` across two positions:
updating wire `i.succAbove j` after inserting at wire `i` is the same as
updating slot `j` inside the remaining family before inserting at wire `i`. -/
theorem insertNth_succAbove_exchange {n : ℕ} {α : Fin (n + 2) → Type u}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (x : α i)
    (g : ∀ m : Fin (n + 1), α (i.succAbove m)) (c : α (i.succAbove j)) :
    Fin.insertNth (i.succAbove j) c (Fin.removeNth (i.succAbove j) (Fin.insertNth i x g)) =
      Fin.insertNth i x (Fin.insertNth j c (Fin.removeNth j g)) := by
  funext l
  rcases Fin.eq_self_or_eq_succAbove (i.succAbove j) l with rfl | ⟨m, hm⟩
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  · rw [hm]
    simp only [Fin.insertNth_apply_succAbove, Fin.removeNth_apply]
    rcases Fin.eq_self_or_eq_succAbove i ((i.succAbove j).succAbove m) with hm' | ⟨m', hm'⟩
    · rw [hm']
      simp only [Fin.insertNth_apply_same]
    · rw [hm']
      simp only [Fin.insertNth_apply_succAbove]
      rcases Fin.eq_self_or_eq_succAbove j m' with rfl | ⟨m'', hm''⟩
      · exact absurd hm' (Fin.succAbove_ne _ m)
      · rw [hm'']
        simp only [Fin.insertNth_apply_succAbove, Fin.removeNth_apply]

/-- Corrected entrywise statement: in the extract-at-`i` coordinates,
transposing wire `i.succAbove j` swaps slot `j` of the remaining family
between row and column, leaving all other slots in place. -/
theorem matReindex_extractAt_transposeAt_succAbove_apply {n : ℕ}
    (W : Fin (n + 2) → Type u)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (X : CMatrix (∀ l, W l))
    (x y : W i) (g g' : ∀ m : Fin (n + 1), W (i.succAbove m)) :
    matReindex (extractAt W i) (transposeAt W (i.succAbove j) X) (x, g) (y, g') =
      matReindex (extractAt W i) X
        (x, Fin.insertNth j (g' j) (Fin.removeNth j g))
        (y, Fin.insertNth j (g j) (Fin.removeNth j g')) := by
  simp only [matReindex_apply, extractAt_symm_apply, transposeAt_apply,
    Fin.insertNth_apply_succAbove]
  rw [insertNth_succAbove_exchange i j x g (g' j),
    insertNth_succAbove_exchange i j y g' (g j)]

/-- Packaged form: `transposeAt` at wire `i.succAbove j` is the slot-`j`
transpose of the remaining family, in the extract-at-`i` coordinates. -/
theorem matReindex_extractAt_transposeAt_succAbove {n : ℕ} (W : Fin (n + 2) → Type u)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (X : CMatrix (∀ l, W l)) :
    matReindex (extractAt W i) (transposeAt W (i.succAbove j) X) =
      (fun p q => matReindex (extractAt W i) X
          (p.1, Fin.insertNth j (q.2 j) (Fin.removeNth j p.2))
          (q.1, Fin.insertNth j (p.2 j) (Fin.removeNth j q.2)) :
        CMatrix (W i × ∀ m : Fin (n + 1), W (i.succAbove m))) := by
  ext ⟨x, g⟩ ⟨y, g'⟩
  exact matReindex_extractAt_transposeAt_succAbove_apply W i j X x y g g'

/-- Coordinate transposes at distinct wires commute. -/
theorem transposeAt_commute {n : ℕ} (W : Fin (n + 1) → Type u) (i j : Fin (n + 1))
    (hij : i ≠ j) (X : CMatrix (∀ l, W l)) :
    transposeAt W i (transposeAt W j X) = transposeAt W j (transposeAt W i X) := by
  ext x y
  simp only [transposeAt_apply, Fin.insertNth_removeNth]
  rw [Function.update_of_ne (Ne.symm hij), Function.update_of_ne (Ne.symm hij),
      Function.update_of_ne hij, Function.update_of_ne hij,
      Function.update_comm hij (y i) (y j) x, Function.update_comm hij (x i) (x j) y]

end Contracts

/-! ## Generic compatibility with split, permute, and composition

Compatibility between the coordinate contractions and the wire-family
equivalences of `QIT.Util.Wires`, for arbitrary heterogeneous families: the
last-wire trace is the `k = 1` split, an arbitrary-wire trace is the canonical
move-to-last permutation followed by the last-wire trace, double traces
compose order-independently, and the coordinate partial transpose commutes
with the coordinate partial trace. -/

/-! ### Cast transport helpers

Private workhorses shared by the compatibility proofs below: reading a
dependent tuple at two propositionally equal indices differs by the canonical
cast, and a cast composed with its inverse is the identity. -/

/-- Transporting an application along a wire-index equality: evaluating a
dependent configuration at `x` is casting its value at `y` back along the
congruent fiber equality. -/
private theorem apply_cast_eq {n : ℕ} (W : Fin (n + 1) → Type u) (f : ∀ w, W w)
    {x y : Fin (n + 1)} (h : x = y) : f x = cast (congrArg W h).symm (f y) := by
  subst h
  rfl

/-- A cast preceded by its inverse cast is the identity (input on the source
fiber). -/
private theorem cast_cast_cancel {α β : Type u} (h : α = β) (x : α) :
    cast h.symm (cast h x) = x := by
  cases h
  rfl

/-- A cast followed by its inverse cast is the identity (input on the target
fiber). -/
private theorem cast_cast_cancel' {α β : Type u} (h : α = β) (y : β) :
    cast h (cast h.symm y) = y := by
  cases h
  rfl

/-! ### Split compatibility at the last wire -/

/-- At the last wire, `succAbove` is exactly the kept-wire embedding
`castAdd 1`: this is `Fin.succAbove_last_apply` in the `castAdd 1` spelling
(`castSucc` is by definition `castAdd 1`). -/
theorem last_succAbove {m : ℕ} (j : Fin m) :
    (Fin.last (n := m)).succAbove j = Fin.castAdd 1 j :=
  Fin.succAbove_last_apply j

/-- Every index below the last wire is a `castAdd 1` of a kept index. -/
private theorem eq_castAdd_one_or_last {m : ℕ} (i : Fin (m + 1)) :
    (∃ j : Fin m, i = Fin.castAdd 1 j) ∨ i = Fin.last (n := m) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | rfl
  · exact Or.inl ⟨j, hj⟩
  · exact Or.inr rfl

/-- Transport between the two kept-wire encodings at the last wire:
`traceOutLast (k = 1)` keeps `W ∘ castAdd 1` while `traceAt W Fin.last`
keeps `W ∘ ((Fin.last).succAbove ·)`. -/
def lastKeepEquiv {m : ℕ} (W : Fin (m + 1) → Type u) :
    (∀ i : Fin m, W (Fin.castAdd 1 i)) ≃
    (∀ j : Fin m, W ((Fin.last (n := m)).succAbove j)) where
  toFun f j := cast (congrArg W (last_succAbove j)).symm (f j)
  invFun g j := cast (congrArg W (last_succAbove j)) (g j)
  left_inv f := by
    funext j
    exact cast_cast_cancel' (congrArg W (last_succAbove j)) (f j)
  right_inv g := by
    funext j
    exact cast_cast_cancel (congrArg W (last_succAbove j)) (g j)

/-- Per-slot computation of `lastKeepEquiv`: each kept slot is transported
along the last-wire `succAbove`-versus-`castAdd` index identity. -/
theorem lastKeepEquiv_apply {m : ℕ} (W : Fin (m + 1) → Type u)
    (f : ∀ i : Fin m, W (Fin.castAdd 1 i)) (j : Fin m) :
    lastKeepEquiv W f j = cast (congrArg W (last_succAbove j)).symm (f j) :=
  rfl

/-- Per-slot computation of the inverse of `lastKeepEquiv`. -/
theorem lastKeepEquiv_symm_apply {m : ℕ} (W : Fin (m + 1) → Type u)
    (g : ∀ j : Fin m, W ((Fin.last (n := m)).succAbove j)) (j : Fin m) :
    (lastKeepEquiv W).symm g j = cast (congrArg W (last_succAbove j)) (g j) :=
  rfl

/-- Transport between the single kept slot of the traced block
(`Fin 1`-indexed, shifted) and the last wire itself. -/
def lastWireEquiv {m : ℕ} (W : Fin (m + 1) → Type u) :
    (∀ j : Fin 1, W (Fin.natAdd m j)) ≃ W (Fin.last (n := m)) where
  toFun y := y 0
  invFun x j := Fin.fin_one_eq_zero j ▸ x
  left_inv y := by
    funext j
    rw [Fin.fin_one_eq_zero j]
  right_inv x := rfl

/-- Inserting at the last wire is `Fin.snoc` of the transported kept family:
the per-point transport is exactly the inverse of `lastKeepEquiv`. -/
private theorem insertNth_last_eq_snoc {m : ℕ} {W : Fin (m + 1) → Type u}
    (g : ∀ j : Fin m, W ((Fin.last (n := m)).succAbove j))
    (x : W (Fin.last (n := m))) :
    Fin.insertNth (Fin.last (n := m)) x g = Fin.snoc ((lastKeepEquiv W).symm g) x :=
  Fin.insertNth_last x g

/-- THE assembly helper: assembling the kept block (transported by
`lastKeepEquiv`) with a single traced value (transported by `lastWireEquiv`)
is exactly `Fin.insertNth` at the last wire. -/
theorem addCases_last {m : ℕ} {W : Fin (m + 1) → Type u}
    (g : ∀ j : Fin m, W ((Fin.last (n := m)).succAbove j))
    (x : W (Fin.last (n := m))) :
    Fin.addCases (m := m) (n := 1) (motive := W)
        ((lastKeepEquiv W).symm g) ((lastWireEquiv W).symm x) =
      Fin.insertNth (Fin.last (n := m)) x g := by
  rw [insertNth_last_eq_snoc]
  funext i
  rcases eq_castAdd_one_or_last i with ⟨j, hj⟩ | rfl
  · subst hj
    rw [Fin.addCases_left]
    exact (Fin.snoc_castAdd ((lastKeepEquiv W).symm g) x j).symm
  · have hA : (Fin.addCases (m := m) (n := 1) (motive := W)
          ((lastKeepEquiv W).symm g) ((lastWireEquiv W).symm x)) (Fin.last (n := m)) =
        (lastWireEquiv W).symm x 0 := by
      show (Fin.addCases (m := m) (n := 1) (motive := W) _ _) (Fin.natAdd m 0) = _
      rw [Fin.addCases_right]
    rw [hA, Fin.snoc_last]
    rfl

/-- Entrywise form of the last-wire split compatibility: `traceAt` at the
last wire agrees with `traceOutLast (k = 1)` on transported arguments. -/
theorem traceAt_last_entrywise {m : ℕ} (W : Fin (m + 1) → Type u) [∀ i, Fintype (W i)]
    (M : CMatrix (∀ i, W i))
    (g g' : ∀ j : Fin m, W ((Fin.last (n := m)).succAbove j)) :
    traceAt W (Fin.last (n := m)) M g g' =
      traceOutLast (k := 1) W M ((lastKeepEquiv W).symm g) ((lastKeepEquiv W).symm g') := by
  rw [traceAt_apply, traceOutLast_apply']
  have hsum : ∀ F : (∀ j : Fin 1, W (Fin.natAdd m j)) → ℂ,
      ∑ t : W (Fin.last (n := m)), F ((lastWireEquiv W).symm t) =
        ∑ y : ∀ j : Fin 1, W (Fin.natAdd m j), F y :=
    fun F => Equiv.sum_comp (lastWireEquiv W).symm F
  rw [← hsum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [addCases_last g t, addCases_last g' t]

/-- Generic split compatibility: the coordinate trace at the last wire is the
`k = 1` instance of `traceOutLast`, up to the canonical identification
`lastKeepEquiv` of the kept-wire encodings. -/
theorem traceAt_last_eq_traceOutLast {m : ℕ} (W : Fin (m + 1) → Type u)
    [∀ i, Fintype (W i)] (M : CMatrix (∀ i, W i)) :
    traceAt W (Fin.last (n := m)) M = matReindex (lastKeepEquiv W) (traceOutLast (k := 1) W M) := by
  ext g g'
  rw [matReindex_apply]
  exact traceAt_last_entrywise W M g g'

/-- Reverse direction: the `k = 1` trace-out-last splits off a single
`traceAt` at the last wire, up to the inverse identification. -/
theorem traceOutLast_one_eq_traceAt {m : ℕ} (W : Fin (m + 1) → Type u)
    [∀ i, Fintype (W i)] (M : CMatrix (∀ i, W i)) :
    traceOutLast (k := 1) W M =
      matReindex (lastKeepEquiv W).symm (traceAt W (Fin.last (n := m)) M) := by
  have H := traceAt_last_eq_traceOutLast W M
  exact ((Equiv.symm_apply_eq (e := matReindex (lastKeepEquiv W))).2 H).symm

/-! ### The move-to-last permutation -/

/-- The canonical permutation of `Fin (n + 1)` that moves wire `i` to the last
position: position `Fin.castAdd 1 l` carries wire `i.succAbove l` (the
remaining wires, in order) and the last position `Fin.natAdd n j` carries wire
`i`. The inverse inserts the last position at wire `i`. Note this is a
rotation of the complement, not a transposition: it is self-inverse only in
degenerate positions. -/
def permMoveLastEquiv {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.addCases (motive := fun _ => Fin (n + 1)) (fun l => i.succAbove l) (fun _ => i)
  invFun := Fin.insertNth (α := fun _ => Fin (n + 1)) i (Fin.natAdd n 0) (fun l => Fin.castAdd 1 l)
  left_inv q := by
    induction q using Fin.addCases with
    | left l =>
      show Fin.insertNth (α := fun _ => Fin (n + 1)) i (Fin.natAdd n 0) (fun l => Fin.castAdd 1 l)
          (Fin.addCases (motive := fun _ => Fin (n + 1)) (fun l => i.succAbove l) (fun _ => i)
            (Fin.castAdd 1 l)) = Fin.castAdd 1 l
      rw [Fin.addCases_left, Fin.insertNth_apply_succAbove]
    | right j =>
      show Fin.insertNth (α := fun _ => Fin (n + 1)) i (Fin.natAdd n 0) (fun l => Fin.castAdd 1 l)
          (Fin.addCases (motive := fun _ => Fin (n + 1)) (fun l => i.succAbove l) (fun _ => i)
            (Fin.natAdd n j)) = Fin.natAdd n j
      rw [Fin.addCases_right, Fin.insertNth_apply_same]
      exact congrArg _ (Fin.fin_one_eq_zero j).symm
  right_inv p := by
    rcases Fin.eq_self_or_eq_succAbove i p with hp0 | ⟨l, hp⟩
    · rw [hp0]
      show Fin.addCases (motive := fun _ => Fin (n + 1)) (fun l => i.succAbove l) (fun _ => i)
          (Fin.insertNth (α := fun _ => Fin (n + 1)) i (Fin.natAdd n 0)
            (fun l => Fin.castAdd 1 l) i) = i
      rw [Fin.insertNth_apply_same, Fin.addCases_right]
    · subst hp
      show Fin.addCases (motive := fun _ => Fin (n + 1)) (fun l => i.succAbove l) (fun _ => i)
          (Fin.insertNth (α := fun _ => Fin (n + 1)) i (Fin.natAdd n 0)
            (fun l => Fin.castAdd 1 l) (i.succAbove l)) = i.succAbove l
      rw [Fin.insertNth_apply_succAbove, Fin.addCases_left]

/-- First computation rule for `permMoveLastEquiv`: a kept position carries the
corresponding complement wire. -/
theorem permMoveLastEquiv_castAdd {n : ℕ} (i : Fin (n + 1)) (l : Fin n) :
    permMoveLastEquiv i (Fin.castAdd 1 l) = i.succAbove l := by
  show Fin.addCases (motive := fun _ => Fin (n + 1)) (fun l => i.succAbove l) (fun _ => i)
      (Fin.castAdd 1 l) = i.succAbove l
  rw [Fin.addCases_left]

/-- Second computation rule for `permMoveLastEquiv`: the last position carries
wire `i` itself. -/
theorem permMoveLastEquiv_natAdd {n : ℕ} (i : Fin (n + 1)) (j : Fin 1) :
    permMoveLastEquiv i (Fin.natAdd n j) = i := by
  show Fin.addCases (motive := fun _ => Fin (n + 1)) (fun l => i.succAbove l) (fun _ => i)
      (Fin.natAdd n j) = i
  rw [Fin.addCases_right]

/-! ### Transport equivalences for the kept and traced wires -/

/-- Canonical identification of the kept-wire family of the move-to-last
permutation with the complement family `j ↦ W (i.succAbove j)`: position `l`
of the permuted family carries wire `permMoveLastEquiv i (Fin.castAdd 1 l)`,
which is `i.succAbove l`. -/
def permKeepEquiv {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1)) :
    (∀ l : Fin n, W (permMoveLastEquiv i (Fin.castAdd 1 l))) ≃ (∀ j : Fin n, W (i.succAbove j))
  where
  toFun f j := cast (congrArg W (permMoveLastEquiv_castAdd i j)) (f j)
  invFun g l := cast (congrArg W (permMoveLastEquiv_castAdd i l)).symm (g l)
  left_inv f := by funext l; exact cast_cast_cancel _ (f l)
  right_inv g := by funext j; exact cast_cast_cancel' _ (g j)

/-- Entrywise form of the inverse of `permKeepEquiv`. -/
theorem permKeepEquiv_symm_apply {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1))
    (g : ∀ j : Fin n, W (i.succAbove j)) (l : Fin n) :
    (permKeepEquiv W i).symm g l =
      cast (congrArg W (permMoveLastEquiv_castAdd i l)).symm (g l) :=
  rfl

/-- Canonical identification of the single traced wire of the move-to-last
permutation with wire `i` itself. -/
def permTracedEquiv {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1)) :
    (∀ j : Fin 1, W (permMoveLastEquiv i (Fin.natAdd n j))) ≃ W i
  where
  toFun g := cast (congrArg W (permMoveLastEquiv_natAdd i 0)) (g 0)
  invFun t j :=
    cast ((congrArg W (permMoveLastEquiv_natAdd i 0)).symm.trans
      (congrArg (fun m => W (permMoveLastEquiv i (Fin.natAdd n m)))
        (Fin.fin_one_eq_zero j)).symm) t
  left_inv g := by
    funext j
    have hj0 : j = 0 := Fin.fin_one_eq_zero j
    subst hj0
    exact cast_cast_cancel _ (g 0)
  right_inv t := by
    exact cast_cast_cancel' _ t

/-- Entrywise form of the inverse of `permTracedEquiv`. -/
theorem permTracedEquiv_symm_apply {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1))
    (t : W i) (j : Fin 1) :
    (permTracedEquiv W i).symm t j =
      cast ((congrArg W (permMoveLastEquiv_natAdd i 0)).symm.trans
        (congrArg (fun m => W (permMoveLastEquiv i (Fin.natAdd n m)))
          (Fin.fin_one_eq_zero j)).symm) t :=
  rfl

/-! ### The assembly bridge -/

/-- Forward form of the assembly bridge: inserting `t` at wire `i` into the
complement configuration `g` is, after permuting wire `i` to the last position,
exactly the `Fin.addCases` assembly of the kept part and the traced part of the
permuted family. -/
theorem permuteEquiv_insertNth {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1)) (t : W i)
    (g : ∀ j : Fin n, W (i.succAbove j)) :
    permuteEquiv W (permMoveLastEquiv i) (Fin.insertNth i t g) =
      Fin.addCases (m := n) (n := 1) (motive := fun l => W (permMoveLastEquiv i l))
        ((permKeepEquiv W i).symm g) ((permTracedEquiv W i).symm t) := by
  funext l
  induction l using Fin.addCases with
  | left m =>
    rw [permuteEquiv_apply, Fin.addCases_left, permKeepEquiv_symm_apply]
    exact (apply_cast_eq W (Fin.insertNth i t g) (permMoveLastEquiv_castAdd i m)).trans
      (congrArg _ (Fin.insertNth_apply_succAbove i t g m))
  | right j =>
    rw [permuteEquiv_apply, Fin.addCases_right, permTracedEquiv_symm_apply]
    exact (apply_cast_eq W (Fin.insertNth i t g) (permMoveLastEquiv_natAdd i j)).trans
      (congrArg _ (Fin.insertNth_apply_same i t g))

/-- Inverse form of the assembly bridge, as consumed entrywise by the partial
trace: reading a `Fin.addCases` assembly of the permuted family back through
`permuteEquiv` is exactly inserting the traced value at wire `i`. -/
theorem permuteEquiv_symm_addCases {n : ℕ} (W : Fin (n + 1) → Type u) (i : Fin (n + 1)) (t : W i)
    (g : ∀ j : Fin n, W (i.succAbove j)) :
    (permuteEquiv W (permMoveLastEquiv i)).symm
        (Fin.addCases (m := n) (n := 1) (motive := fun l => W (permMoveLastEquiv i l))
          ((permKeepEquiv W i).symm g) ((permTracedEquiv W i).symm t)) =
      Fin.insertNth i t g := by
  rw [← permuteEquiv_insertNth W i t g]
  exact Equiv.symm_apply_apply _ _

/-! ### Permute compatibility: tracing an arbitrary wire is permute-to-last
plus tracing out the last wire -/

/-- Permuting the wires of a joint matrix preserves positive semidefiniteness:
the PSD transport needed on the permute side of `traceAt_eq_permute`. -/
theorem matPermute_posSemidef {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n)
    {M : CMatrix (∀ i, W i)} (hM : M.PosSemidef) : (matPermute W e M).PosSemidef :=
  (Matrix.posSemidef_submatrix_equiv _).2 hM

/-- Tracing out an arbitrary wire `i` of a heterogeneous wire family equals
permuting wire `i` to the last position (via the canonical
`permMoveLastEquiv`) and tracing out the last wire with `traceOutLast`; the
kept wires are canonically identified by `permKeepEquiv`. -/
theorem traceAt_eq_permute {n : ℕ} (W : Fin (n + 1) → Type u) [∀ j, Fintype (W j)]
    (i : Fin (n + 1)) (M : CMatrix (∀ j, W j)) :
    traceAt W i M =
      matReindex (permKeepEquiv W i)
        (traceOutLast (W := fun l => W (permMoveLastEquiv i l)) (m := n) (k := 1)
          (matPermute W (permMoveLastEquiv i) M)) := by
  ext g g'
  rw [matReindex_apply, traceAt_apply, traceOutLast_apply']
  have hsum : ∀ F : (∀ j : Fin 1, W (permMoveLastEquiv i (Fin.natAdd n j))) → ℂ,
      ∑ t : W i, F ((permTracedEquiv W i).symm t) = ∑ y, F y :=
    fun F => Equiv.sum_comp (permTracedEquiv W i).symm F
  rw [← hsum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [matPermute_apply, permuteEquiv_symm_addCases W i t g, permuteEquiv_symm_addCases W i t g']

/-! ### Composition of coordinate partial traces across distinct wires -/

/-- Canonical identification of the two double-removed wire families: removing
wire `i` and then slot `j` of the remainder leaves the family
`fun l => W (i.succAbove (j.succAbove l))`, while removing wire `i.succAbove j`
and then slot `j.predAbove i` leaves
`fun l => W ((i.succAbove j).succAbove ((j.predAbove i).succAbove l))`; the two
are pointwise equal along `Fin.succAbove_succAbove_succAbove_predAbove`. -/
def doubleRemoveEquiv {n : ℕ} (W : Fin (n + 2) → Type u) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (∀ l : Fin n, W ((i.succAbove j).succAbove ((j.predAbove i).succAbove l))) ≃
      (∀ l : Fin n, W (i.succAbove (j.succAbove l))) :=
  Equiv.piCongrRight fun l =>
    Equiv.cast (congrArg W (Fin.succAbove_succAbove_succAbove_predAbove i j l))

/-- Computing the inverse of `doubleRemoveEquiv`: per-slot cast along the
double-hole index identity. -/
theorem doubleRemoveEquiv_symm_apply {n : ℕ} (W : Fin (n + 2) → Type u) (i : Fin (n + 2))
    (j : Fin (n + 1)) (g : ∀ l : Fin n, W (i.succAbove (j.succAbove l))) :
    (doubleRemoveEquiv W i j).symm g =
      fun l => cast (congrArg W (Fin.succAbove_succAbove_succAbove_predAbove i j l)).symm (g l) :=
  rfl

/-- Exchange law for double `Fin.insertNth`: assembling the two removed wire
values in the order "`i` first, then slot `j`" equals assembling them in the
swapped order "`i.succAbove j` first, then slot `j.predAbove i`", the two
double-removed remainder tuples being identified by the canonical casts. -/
theorem insertNth_insertNth_exchange {n : ℕ} (W : Fin (n + 2) → Type u) (i : Fin (n + 2))
    (j : Fin (n + 1)) (x : W i) (c : W (i.succAbove j))
    (g : ∀ l : Fin n, W (i.succAbove (j.succAbove l))) :
    Fin.insertNth (i.succAbove j) c
        (Fin.insertNth (j.predAbove i)
          (cast (congrArg W (Fin.succAbove_succAbove_predAbove i j)).symm x)
          (fun l => cast (congrArg W (Fin.succAbove_succAbove_succAbove_predAbove i j l)).symm
            (g l))) =
      Fin.insertNth i x (Fin.insertNth j c g) := by
  rw [Fin.insertNth_eq_iff]
  refine ⟨?_, ?_⟩
  · simp only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
  · rw [Fin.insertNth_eq_iff]
    refine ⟨?_, ?_⟩
    · exact Eq.symm
        ((apply_cast_eq W (Fin.insertNth i x (Fin.insertNth j c g))
            (Fin.succAbove_succAbove_predAbove i j)).trans
          (congrArg _ (Fin.insertNth_apply_same i x (Fin.insertNth j c g))))
    · funext l
      have h2 : Fin.insertNth i x (Fin.insertNth j c g) (i.succAbove (j.succAbove l)) = g l := by
        rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      exact Eq.symm
        ((apply_cast_eq W (Fin.insertNth i x (Fin.insertNth j c g))
            (Fin.succAbove_succAbove_succAbove_predAbove i j l)).trans
          (congrArg _ h2))

/-- Composition of coordinate partial traces across distinct wires: tracing out
wire `i` and then slot `j` of the remaining family equals tracing out wire
`i.succAbove j` and then slot `j.predAbove i` (the slot where wire `i` ends up
after wire `i.succAbove j` is removed). The two resulting matrices live on the
two double-removed families, identified by `doubleRemoveEquiv`. -/
theorem traceAt_traceAt {n : ℕ} (W : Fin (n + 2) → Type u) [∀ l, Fintype (W l)]
    (i : Fin (n + 2)) (j : Fin (n + 1)) (M : CMatrix (∀ l, W l)) :
    traceAt (fun m => W (i.succAbove m)) j (traceAt W i M) =
      matReindex (doubleRemoveEquiv W i j)
        (traceAt (fun m => W ((i.succAbove j).succAbove m)) (j.predAbove i)
          (traceAt W (i.succAbove j) M)) := by
  ext g g'
  rw [matReindex_apply, doubleRemoveEquiv_symm_apply W i j g,
    doubleRemoveEquiv_symm_apply W i j g']
  simp only [traceAt_apply]
  have hz : ∀ F : W ((i.succAbove j).succAbove (j.predAbove i)) → ℂ,
      ∑ z, F z = ∑ a : W i,
        F (cast (congrArg W (Fin.succAbove_succAbove_predAbove i j)).symm a) :=
    fun F =>
      (Equiv.sum_comp (Equiv.cast (congrArg W (Fin.succAbove_succAbove_predAbove i j)).symm)
        F).symm
  rw [hz]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
  rw [insertNth_insertNth_exchange W i j x c g,
    insertNth_insertNth_exchange W i j x c g']

/-! ### Partial transpose commutes with partial trace -/

/-- Coordinate partial transpose at a wire distinct from the traced wire
commutes with the coordinate partial trace: transposing slot `j` of the traced
matrix equals tracing the matrix transposed at wire `i.succAbove j`. -/
theorem transposeAt_traceAt {n : ℕ} (W : Fin (n + 2) → Type u) [∀ l, Fintype (W l)]
    (i : Fin (n + 2)) (j : Fin (n + 1)) (M : CMatrix (∀ l, W l)) :
    transposeAt (fun m => W (i.succAbove m)) j (traceAt W i M) =
      traceAt W i (transposeAt W (i.succAbove j) M) := by
  ext g g'
  simp only [transposeAt_apply, traceAt_apply, Fin.insertNth_apply_succAbove]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← insertNth_succAbove_exchange i j x g (g' j),
    ← insertNth_succAbove_exchange i j x g' (g j)]

/-- Transposing the traced wire itself acts trivially after the trace: the
trace inserts the same wire-`i` value `x` into both the row and the column
configuration, so exchanging the row and column values at wire `i` changes
nothing. -/
@[simp]
theorem traceAt_transposeAt_self {n : ℕ} (W : Fin (n + 1) → Type u) [∀ l, Fintype (W l)]
    (i : Fin (n + 1)) (M : CMatrix (∀ l, W l)) :
    traceAt W i (transposeAt W i M) = traceAt W i M := by
  ext g g'
  simp only [traceAt_apply, transposeAt_apply, Fin.insertNth_apply_same,
    Fin.removeNth_insertNth]

/-! ### Split compatibility at a final block of k + 1 wires -/

/-- Composition identity for the kept-wire embedding: appending one wire
after `k` wires is appending `k + 1` wires. This is the orientation-flattened
form of `Fin.castAdd_castAdd` (whose associativity cast is discharged here
definitionally, since `m + k + 1` and `m + (k + 1)` agree), and it holds by
`rfl`. -/
theorem castAdd_one_castAdd {m k : ℕ} (i : Fin m) :
    Fin.castAdd 1 (Fin.castAdd k i) = Fin.castAdd (k + 1) i := rfl

/-- Index identity inside the traced block: appending the final wire first and
then shifting by `m` is shifting by `m` first and then appending the final
wire. It holds by `rfl` and is the flattened form of `Fin.natAdd_castAdd`. -/
theorem natAdd_castAdd_one {m k : ℕ} (j : Fin k) :
    Fin.castAdd 1 (Fin.natAdd m j) = Fin.natAdd m (Fin.castAdd 1 j) := rfl

/-- Canonical identification of the two kept-wire encodings of the successor
split: tracing out the last `k + 1` wires directly keeps
`W (Fin.castAdd (k + 1) i)`, while tracing the last wire first and then the
remaining `k` wires keeps `W (Fin.castAdd 1 (Fin.castAdd k i))`; the two are
pointwise identified along `castAdd_one_castAdd`. -/
def succKeepEquiv {m k : ℕ} (W : Fin (m + k + 1) → Type u) :
    (∀ i : Fin m, W (Fin.castAdd 1 (Fin.castAdd k i))) ≃
      (∀ i : Fin m, W (Fin.castAdd (k + 1) i)) :=
  Equiv.piCongrRight fun i => Equiv.cast (congrArg W (castAdd_one_castAdd i))

/-- Computing the inverse of `succKeepEquiv` per kept slot. -/
theorem succKeepEquiv_symm_apply {m k : ℕ} (W : Fin (m + k + 1) → Type u)
    (g : ∀ i : Fin m, W (Fin.castAdd (k + 1) i)) (i : Fin m) :
    (succKeepEquiv W).symm g i = g i := rfl

/-- Canonical identification of the traced-block configurations of the
successor split: a configuration of the last `k + 1` wires of the shifted
family is a configuration of the last `k` wires together with a value on the
final wire. -/
def tracedSuccEquiv {m k : ℕ} (W : Fin (m + k + 1) → Type u) :
    (∀ j : Fin (k + 1), W (Fin.natAdd m j)) ≃
      (∀ j : Fin k, W (Fin.castAdd 1 (Fin.natAdd m j))) × W (Fin.last (n := m + k)) where
  toFun y := (fun a => y (Fin.castAdd 1 a), y (Fin.natAdd k 0))
  invFun p :=
    Fin.addCases (m := k) (n := 1) (motive := fun l => W (Fin.natAdd m l)) p.1
      ((lastWireEquiv (fun l => W (Fin.natAdd m l))).symm p.2)
  left_inv y := by
    show Fin.addCases (m := k) (n := 1) (motive := fun l => W (Fin.natAdd m l))
        (fun a => y (Fin.castAdd 1 a))
        ((lastWireEquiv (fun l => W (Fin.natAdd m l))).symm (y (Fin.natAdd k 0))) = y
    funext j
    induction j using Fin.addCases with
    | left a => rw [Fin.addCases_left]
    | right t =>
      rw [Fin.addCases_right, Fin.fin_one_eq_zero t]
      rfl
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext a
      show Fin.addCases (m := k) (n := 1) (motive := fun l => W (Fin.natAdd m l)) p.1
          ((lastWireEquiv (fun l => W (Fin.natAdd m l))).symm p.2) (Fin.castAdd 1 a) = p.1 a
      rw [Fin.addCases_left]
    · show Fin.addCases (m := k) (n := 1) (motive := fun l => W (Fin.natAdd m l)) p.1
        ((lastWireEquiv (fun l => W (Fin.natAdd m l))).symm p.2) (Fin.natAdd k 0) = p.2
      rw [Fin.addCases_right]
      rfl

/-- THE assembly bridge for the successor split: assembling the `m + k`
configuration (kept part first, then the `k` traced wires) with the final-wire
value is the same flat `Fin.addCases` assembly over the `k + 1` traced wires of
the shifted family, where the final wire is itself assembled last. -/
theorem addCases_last_succ {m k : ℕ} (W : Fin (m + k + 1) → Type u)
    (g : ∀ i : Fin m, W (Fin.castAdd (k + 1) i))
    (z : ∀ j : Fin k, W (Fin.castAdd 1 (Fin.natAdd m j)))
    (x : W (Fin.last (n := m + k))) :
    Fin.addCases (m := m + k) (n := 1) (motive := W)
        (Fin.addCases (m := m) (n := k) (motive := fun l => W (Fin.castAdd 1 l))
          ((succKeepEquiv W).symm g) z)
        ((lastWireEquiv (m := m + k) W).symm x) =
      Fin.addCases (m := m) (n := k + 1) (motive := W) g
        (Fin.addCases (m := k) (n := 1) (motive := fun l => W (Fin.natAdd m l)) z
          ((lastWireEquiv (fun l => W (Fin.natAdd m l))).symm x)) := by
  funext l
  induction l using Fin.addCases with
  | left a =>
    rw [Fin.addCases_left]
    induction a using Fin.addCases with
    | left i =>
      rw [Fin.addCases_left]
      show ((succKeepEquiv W).symm g) i =
        Fin.addCases (m := m) (n := k + 1) (motive := W) g _ (Fin.castAdd (k + 1) i)
      rw [Fin.addCases_left]
      exact succKeepEquiv_symm_apply W g i
    | right j =>
      rw [Fin.addCases_right]
      show z j = Fin.addCases (m := m) (n := k + 1) (motive := W) g _
          (Fin.natAdd m (Fin.castAdd 1 j))
      rw [Fin.addCases_right, Fin.addCases_left]
  | right t =>
    rw [Fin.addCases_right, Fin.fin_one_eq_zero t]
    show ((lastWireEquiv (m := m + k) W).symm x) 0 =
      Fin.addCases (m := m) (n := k + 1) (motive := W) g _ (Fin.natAdd m (Fin.natAdd k 0))
    rw [Fin.addCases_right, Fin.addCases_right]
    rfl

/-! ### Generic append compatibility for the trace-out-last recursion -/

/-- Workhorse: tracing out the last `k + 1` wires of a heterogeneous family is
tracing out the final wire first and then the last `k` wires of the shifted
family, the kept-wire encodings being identified by `succKeepEquiv`. Entrywise
proof: both sides expand to the same iterated sum over the `k`-block
configurations and the final-wire value, via the configuration assembly
`addCases_last_succ`. -/
theorem traceOutLast_succ_split {m k : ℕ} (W : Fin (m + k + 1) → Type u)
    [∀ l, Fintype (W l)] (M : CMatrix (∀ l, W l)) :
    traceOutLast (k := k + 1) W M =
      matReindex (succKeepEquiv W)
        (traceOutLast (W := fun j => W (Fin.castAdd 1 j)) (m := m) (k := k)
          (traceOutLast (k := 1) (m := m + k) W M)) := by
  ext g g'
  simp only [matReindex_apply, traceOutLast_apply']
  have hsum : ∀ F : (∀ j : Fin (k + 1), W (Fin.natAdd m j)) → ℂ,
      ∑ s : ∀ j : Fin (k + 1), W (Fin.natAdd m j), F s =
        ∑ z : ∀ j : Fin k, W (Fin.castAdd 1 (Fin.natAdd m j)),
          ∑ x : W (Fin.last (n := m + k)),
            F (Fin.addCases (m := k) (n := 1) (motive := fun l => W (Fin.natAdd m l)) z
              ((lastWireEquiv (fun l => W (Fin.natAdd m l))).symm x)) := by
    intro F
    have h1 : ∑ s : ∀ j : Fin (k + 1), W (Fin.natAdd m j), F s =
        ∑ p : (∀ j : Fin k, W (Fin.castAdd 1 (Fin.natAdd m j))) × W (Fin.last (n := m + k)),
          F ((tracedSuccEquiv W).symm p) :=
      (Equiv.sum_comp (tracedSuccEquiv W).symm F).symm
    rw [h1, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => rfl
  have ht : ∀ F : (∀ j : Fin 1, W (Fin.natAdd (m + k) j)) → ℂ,
      ∑ t : ∀ j : Fin 1, W (Fin.natAdd (m + k) j), F t =
        ∑ x : W (Fin.last (n := m + k)),
          F ((lastWireEquiv (m := m + k) W).symm x) :=
    fun F => (Equiv.sum_comp (lastWireEquiv (m := m + k) W).symm F).symm
  rw [hsum]
  simp only [ht]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => ?_
  rw [addCases_last_succ W g z x, addCases_last_succ W g' z x]

/-- Generic split/append compatibility: tracing out the last `k + 1` wires of
a heterogeneous family is a single `traceAt` at the final wire (transported by
`lastKeepEquiv`, as in `traceOutLast_one_eq_traceAt`) followed by tracing out
the last `k` wires of the shifted family, the kept-wire encodings being
identified by `succKeepEquiv`. -/
theorem traceOutLast_succ {m k : ℕ} (W : Fin (m + k + 1) → Type u) [∀ l, Fintype (W l)]
    (M : CMatrix (∀ l, W l)) :
    traceOutLast (k := k + 1) W M =
      matReindex (succKeepEquiv W)
        (traceOutLast (W := fun j => W (Fin.castAdd 1 j)) (m := m) (k := k)
          (matReindex (lastKeepEquiv W).symm (traceAt W (Fin.last (n := m + k)) M))) := by
  rw [traceOutLast_succ_split W M, traceOutLast_one_eq_traceAt]

/-- Reverse direction: the iterated trace, transported back along
`succKeepEquiv`, is the flat `k + 1`-fold trace-out-last. -/
theorem traceOutLast_succ' {m k : ℕ} (W : Fin (m + k + 1) → Type u) [∀ l, Fintype (W l)]
    (M : CMatrix (∀ l, W l)) :
    matReindex (succKeepEquiv W).symm (traceOutLast (k := k + 1) W M) =
      traceOutLast (W := fun j => W (Fin.castAdd 1 j)) (m := m) (k := k)
        (matReindex (lastKeepEquiv W).symm (traceAt W (Fin.last (n := m + k)) M)) := by
  have H := traceOutLast_succ W M
  exact (Equiv.symm_apply_eq (e := matReindex (succKeepEquiv W))).2 H

end WireFam

end QIT
