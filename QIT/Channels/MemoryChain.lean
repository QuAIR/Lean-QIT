/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.Core.Map
public import QIT.States.Purification.ReferenceIsometry
public import QIT.Util.Wires.Contraction

/-!
# Memory-channel chains and recursive ancilla bookkeeping

This module builds the reusable infrastructure for finite chains of isometric
interactions with heterogeneous memories: the chain side of the source's
memory-channel realization, built on the normalization recursion
[Chiribella2009Networks, comblong-pub.tex:860-869], the realization theorem
[Chiribella2009Networks, comblong-pub.tex:986-997], and the memory-channel
phrasing [Chiribella2009Networks, comblong-pub.tex:1891-1892]. A chain
with `N = n + 1` links (indexed by `Nat.succ`, matching the public comb
convention of `N` teeth on a `2N`-wire comb space, the one-link chain being
the base case) is a sequence of isometries
`link j : linkDom I E j → O j × E j`: link `0` prepares from the free input
wire `I 0`, and each later link consumes the memory produced by its
predecessor together with its own free input; the final memory `E n` is the
discarded ancilla.

* **The chain and its Choi operator.** `MemoryChain` bundles the link
  isometries; `MemoryChain.kraus` is the explicit memory-sliced Kraus family
  (internal memory configurations are summed coherently within each final-environment slice);
  `MemoryChain.chainMap` is the induced matrix map and
  `MemoryChain.chainChoi` its Choi operator, reindexed onto the comb wire
  family `combWire` (the input block `I` followed by the output block `O`,
  matching the Choi convention). Entrywise forms: `MemoryChain.krausEntry_zero`,
  `MemoryChain.krausEntry_succ`, `MemoryChain.kraus_apply`, `MemoryChain.chainChoi_apply`,
  and the extraction bridge `MemoryChain.chainChoi_eq_choi`.

* **Positivity.** `MemoryChain.chainMap_isCompletelyPositive`,
  `MemoryChain.chainChoi_posSemidef`, `MemoryChain.chainChoi_isHermitian`.

* **Recursive partial-trace behavior.** The chain-side normalization
  recursion of the source's Lemma (lemrecnet): tracing the last comb wire of
  the chain Choi collapses the last link telescopically (by
  `ReferenceIsometry.sum_mul_star`) and leaves the identity on the adjacent
  input wire tensored with the Choi of the truncated chain
  (`MemoryChain.traceAt_last_chainChoi`), with the single-link base case
  `MemoryChain.chainChoi_one_traceAt`. Contracting the final-link isometry
  in the coherent Kraus sums gives the Kraus isometry equation
  `MemoryChain.krausIsometry`, hence `MemoryChain.chainMap_isTracePreserving`
  and the memory channel `MemoryChain.channel`.

* **Memory reindexing.** Relabelling the internal memories does not change
  the chain Choi (`MemoryChain.chainChoi_reindexMemory`); reindexing the free
  wires transports the chain Choi along the canonical comb-family
  equivalence (`MemoryChain.chainChoi_reindexWires`).

* **Composition.** `MemoryChain.snoc` extends a chain by one final isometric
  link, with the coherent amplitude-summing computation rules
  `MemoryChain.kraus_snoc` and `MemoryChain.chainChoi_snoc`; appending links
  one at a time via `snoc` builds longer chains, which is the induction the
  comb-realization direction performs. No link product (and no chain-to-chain
  concatenation operation) is defined here; the general heterogeneous link
  product is out of scope for this module.

## Main definitions

* `QIT.HigherOrder.MemoryChain`
* `QIT.HigherOrder.MemoryChain.snoc`
* `QIT.HigherOrder.MemoryChain.chainChoi`
* `QIT.HigherOrder.MemoryChain.channel`

## Tags

memory channel, quantum comb, chain, ancilla, wire family
-/

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

universe u

@[expose] public section

namespace QIT.HigherOrder

noncomputable section

/-! ## Link domains over heterogeneous wires -/

section LinkDom

variable {n : ℕ} {I E : Fin (n + 1) → Type u}

/-- The input system of link `j`: the free input wire `I j`, preceded by the
incoming memory `E j.castSucc` when `j > 0` (there is no incoming memory
before the first link; the first isometry is a preparation). The memory
factor comes first so that no factor swap is needed in the composition
assemblies. -/
def linkDom (I E : Fin (n + 1) → Type u) : (j : Fin (n + 1)) → Type u :=
  Fin.cons (I 0) fun k => E k.castSucc × I k.succ

/-- The first link reads only the free input wire `I 0`. -/
theorem linkDom_zero : linkDom I E 0 = I 0 :=
  rfl

/-- A later link reads the incoming memory together with its free input. -/
theorem linkDom_succ (k : Fin n) : linkDom I E k.succ = (E k.castSucc × I k.succ) :=
  rfl

instance instFintypeLinkDom [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    (j : Fin (n + 1)) : Fintype (linkDom I E j) :=
  Fin.cases (motive := fun j => Fintype (linkDom I E j))
    (inferInstanceAs (Fintype (I 0)))
    (fun k => inferInstanceAs (Fintype (E k.castSucc × I k.succ))) j

instance instDecidableEqLinkDom [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (E j)]
    (j : Fin (n + 1)) : DecidableEq (linkDom I E j) :=
  Fin.cases (motive := fun j => DecidableEq (linkDom I E j))
    (inferInstanceAs (DecidableEq (I 0)))
    (fun k => inferInstanceAs (DecidableEq (E k.castSucc × I k.succ))) j

end LinkDom

/-! ## The comb wire family -/

section CombWire

variable {m : ℕ} {I O : Fin m → Type u}

/-- The comb wire family of a chain with `m` links: the `m` free input wires
followed by the `m` free output wires, the wire content of the source's comb
[Chiribella2009Networks, comblong-pub.tex:860-869] in the block order of the
Choi convention. The memories are internal and do not appear. Reducible, so
that the `WireFam.append` computation lemmas apply to it directly. -/
abbrev combWire (I O : Fin m → Type u) : Fin (m + m) → Type u :=
  WireFam.append I O

/-- Input-block comb positions carry the free input wires. -/
theorem combWire_castAdd (j : Fin m) :
    combWire I O (Fin.castAdd m j) = I j :=
  WireFam.append_castAdd I O j

/-- Output-block comb positions carry the free output wires. -/
theorem combWire_natAdd (j : Fin m) :
    combWire I O (Fin.natAdd m j) = O j :=
  WireFam.append_natAdd I O j

/-- The last comb position carries the last free output wire. -/
theorem combWire_last {n : ℕ} (I O : Fin (n + 1) → Type u) :
    combWire I O (Fin.last (n := (n + 1) + n)) = O (Fin.last n) := by
  have hlast : (Fin.last (n := (n + 1) + n)) = Fin.natAdd (n + 1) (Fin.last n) :=
    rfl
  rw [hlast, combWire_natAdd]

instance instFintypeCombWire [∀ j, Fintype (I j)] [∀ j, Fintype (O j)]
    (i : Fin (m + m)) : Fintype (combWire I O i) :=
  WireFam.instFintypeAppend (W₁ := I) (W₂ := O) i

instance instDecidableEqCombWire [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)]
    (i : Fin (m + m)) : DecidableEq (combWire I O i) := by
  induction i using Fin.addCases with
  | left i => rw [combWire_castAdd]; infer_instance
  | right j => rw [combWire_natAdd]; infer_instance

/-- The input-block read of a comb configuration: the value carried at the
input position of link `j`, transported to `I j`. -/
def readI (f : ∀ i, combWire I O i) (j : Fin m) : I j :=
  cast (combWire_castAdd (I := I) (O := O) j) (f (Fin.castAdd m j))

/-- The output-block read of a comb configuration: the value carried at the
output position of link `j`, transported to `O j`. -/
def readO (f : ∀ i, combWire I O i) (j : Fin m) : O j :=
  cast (combWire_natAdd (I := I) (O := O) j) (f (Fin.natAdd m j))

/-- Splitting the comb configurations into the input block and the output
block. Reducible, so that the computation lemmas of `WireFam.splitAppendEquiv`
apply to it directly. -/
abbrev combSplitEquiv (I O : Fin m → Type u) :
    (∀ i, combWire I O i) ≃ (∀ j, I j) × (∀ j, O j) :=
  WireFam.splitAppendEquiv I O

/-- Computing the comb split: the two blocks are the input-block and
output-block reads. -/
theorem combSplitEquiv_apply (f : ∀ i, combWire I O i) :
    combSplitEquiv I O f = (readI f, readO f) := by
  rw [WireFam.splitAppendEquiv_apply]
  rfl

/-- Reading back an assembled comb configuration at an input position gives
the input-block value. -/
theorem combSplitEquiv_symm_apply_castAdd (g : ∀ j, I j) (h : ∀ j, O j)
    (j : Fin m) :
    (combSplitEquiv I O).symm (g, h) (Fin.castAdd m j) =
      cast (combWire_castAdd (I := I) (O := O) j).symm (g j) := by
  simp only [WireFam.splitAppendEquiv_symm_apply, Fin.addCases_left]
  rfl

/-- Reading back an assembled comb configuration at an output position gives
the output-block value. -/
theorem combSplitEquiv_symm_apply_natAdd (g : ∀ j, I j) (h : ∀ j, O j)
    (j : Fin m) :
    (combSplitEquiv I O).symm (g, h) (Fin.natAdd m j) =
      cast (combWire_natAdd (I := I) (O := O) j).symm (h j) := by
  simp only [WireFam.splitAppendEquiv_symm_apply, Fin.addCases_right]
  rfl

end CombWire

/-! ## Reading assembled comb configurations -/

section ReadAssembled

variable {m : ℕ} {I O : Fin (m + 1) → Type u}

/-- Reading the input block of a comb configuration assembled from a kept
configuration and a value on the traced last output wire. -/
theorem readI_addCases (g : ∀ i : Fin (m + 1 + m), combWire I O (Fin.castAdd 1 i))
    (y : ∀ j : Fin 1, combWire I O (Fin.natAdd (m + 1 + m) j)) (j : Fin (m + 1)) :
    readI (m := m + 1) (I := I) (O := O) (Fin.addCases (m := m + 1 + m) (n := 1) g y) j =
      cast (combWire_castAdd (I := I) (O := O) j) (g (Fin.castAdd m j)) := by
  have h := Fin.addCases_left (n := 1) (left := g) (right := y) (Fin.castAdd m j)
  show cast (combWire_castAdd (I := I) (O := O) j)
      (Fin.addCases g y (Fin.castAdd 1 (Fin.castAdd m j))) = _
  exact congrArg _ h

/-- Reading the output block of a comb configuration assembled from a kept
configuration and a value on the traced last output wire, at one of the output
positions kept by the truncated chain. -/
theorem readO_addCases_castSucc (g : ∀ i : Fin (m + 1 + m), combWire I O (Fin.castAdd 1 i))
    (y : ∀ j : Fin 1, combWire I O (Fin.natAdd (m + 1 + m) j)) (j : Fin m) :
    readO (m := m + 1) (I := I) (O := O) (Fin.addCases (m := m + 1 + m) (n := 1) g y)
        j.castSucc =
      cast (combWire_natAdd (I := I) (O := O) j.castSucc) (g (Fin.natAdd (m + 1) j)) := by
  have h := Fin.addCases_left (n := 1) (left := g) (right := y) (Fin.natAdd (m + 1) j)
  exact congrArg _ h

/-- Reading the output block of a comb configuration assembled from a kept
configuration and a value on the traced last output wire, at the traced
position itself, gives the traced value. -/
theorem readO_addCases_last (g : ∀ i : Fin (m + 1 + m), combWire I O (Fin.castAdd 1 i))
    (y : ∀ j : Fin 1, combWire I O (Fin.natAdd (m + 1 + m) j)) :
    readO (m := m + 1) (I := I) (O := O) (Fin.addCases (m := m + 1 + m) (n := 1) g y)
        (Fin.last (n := m)) =
      cast (combWire_natAdd (I := I) (O := O) (Fin.last (n := m)))
        (y (0 : Fin 1)) := by
  have h := Fin.addCases_right (n := 1) (left := g) (right := y) (0 : Fin 1)
  show cast (combWire_natAdd (I := I) (O := O) (Fin.last (n := m)))
      (Fin.addCases g y (Fin.natAdd (m + 1 + m) (0 : Fin 1))) = _
  exact congrArg _ h

end ReadAssembled

/-! ## Memory-channel chains -/

section Chain

variable {n : ℕ}
variable {I O E : Fin (n + 1) → Type u}
variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- A memory-channel chain with `n + 1` isometric links over heterogeneous
wires: link `j` maps its free input wire `I j` (preceded by the incoming
memory when `j > 0`) to the free output wire `O j` together with the memory
`E j`; the final memory `E n` is the ancilla discarded by `chainChoi`.
This is the `N = n + 1` chain of the source's memory-channel realization
[Chiribella2009Networks, comblong-pub.tex:986-997] in its memory-channel form
[Chiribella2009Networks, comblong-pub.tex:1924-1934]. -/
structure MemoryChain (I O E : Fin (n + 1) → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)] where
  link : (j : Fin (n + 1)) → ReferenceIsometry (linkDom I E j) (O j × E j)

/-- The per-link entries at a full memory configuration `α`: the entry at
link `j` is that link's matrix entry, consuming the memory produced by link
`j - 1` (there is none before the first link) and producing the memory read
by link `j + 1`. No internal sums appear. -/
def MemoryChain.krausEntry (c : MemoryChain I O E) (α : ∀ j, E j)
    (o : ∀ j, O j) (i : ∀ j, I j) : Fin (n + 1) → ℂ :=
  Fin.cons ((c.link 0).matrix (o 0, α 0) (i 0))
    fun k => (c.link k.succ).matrix (o k.succ, α k.succ) (α k.castSucc, i k.succ)

/-- Computation rule for the first link's Kraus entry. -/
@[simp]
theorem MemoryChain.krausEntry_zero (c : MemoryChain I O E) (α : ∀ j, E j)
    (o : ∀ j, O j) (i : ∀ j, I j) :
    c.krausEntry α o i 0 = (c.link 0).matrix (o 0, α 0) (i 0) :=
  rfl

/-- Computation rule for a later link's Kraus entry. -/
@[simp]
theorem MemoryChain.krausEntry_succ (c : MemoryChain I O E) (α : ∀ j, E j)
    (o : ∀ j, O j) (i : ∀ j, I j) (k : Fin n) :
    c.krausEntry α o i k.succ =
      (c.link k.succ).matrix (o k.succ, α k.succ) (α k.castSucc, i k.succ) :=
  rfl

/-- Kraus slices labelled only by the final environment. Internal memories are summed
coherently at the amplitude level [Chiribella2009Networks, comblong-pub.tex:1037-1057]. -/
def MemoryChain.kraus (c : MemoryChain I O E) (e : E (Fin.last n)) :
    Matrix (∀ j, O j) (∀ j, I j) ℂ :=
  fun o i => ∑ α : ∀ j : Fin n, E j.castSucc,
    ∏ j, c.krausEntry (Fin.snoc α e) o i j

/-- The internal-memory path expansion of a final-environment Kraus slice. -/
theorem MemoryChain.kraus_apply (c : MemoryChain I O E) (e : E (Fin.last n))
    (o : ∀ j, O j) (i : ∀ j, I j) :
    c.kraus e o i = ∑ α : ∀ j : Fin n, E j.castSucc,
      ∏ j, c.krausEntry (Fin.snoc α e) o i j := rfl

/-- A single link has no internal memories to sum over. -/
theorem MemoryChain.kraus_one
    {I O E : Fin 1 → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
    (c : MemoryChain I O E) (e : E 0) (o : ∀ j, O j) (i : ∀ j, I j) :
    c.kraus e o i = (c.link 0).matrix (o 0, e) (i 0) := by
  simp [kraus, Fin.snoc]

/-- The memory channel as a matrix map. -/
def MemoryChain.chainMap (c : MemoryChain I O E) : MatrixMap (∀ j, I j) (∀ j, O j) :=
  MatrixMap.ofKraus c.kraus

/-- The Choi operator of the chain on the block-ordered comb wire family. -/
def MemoryChain.chainChoi (c : MemoryChain I O E) : CMatrix (∀ i, combWire I O i) :=
  WireFam.matReindex (combSplitEquiv I O).symm (MatrixMap.choi c.chainMap)

/-- Extraction bridge: reading the chain Choi through the comb split is the
Choi matrix of the chain map. -/
theorem MemoryChain.chainChoi_eq_choi (c : MemoryChain I O E) :
    WireFam.matReindex (combSplitEquiv I O) c.chainChoi = MatrixMap.choi c.chainMap :=
  Equiv.apply_symm_apply _ _

/-- The Choi expansion over the discarded final environment only. -/
theorem MemoryChain.chainChoi_apply (c : MemoryChain I O E)
    (f g : ∀ i, combWire I O i) :
    c.chainChoi f g = ∑ e, c.kraus e (readO f) (readI f) *
      star (c.kraus e (readO g) (readI g)) := by
  simp only [chainChoi, chainMap, WireFam.matReindex_apply, Equiv.symm_symm,
    MatrixMap.choi_ofKraus, combSplitEquiv_apply, Matrix.sum_apply, Matrix.vecMulVec]
  rfl

/-- Independent internal memory configurations on the ket and bra retain interference. -/
theorem MemoryChain.chainChoi_path_expansion (c : MemoryChain I O E)
    (f g : ∀ i, combWire I O i) :
    c.chainChoi f g = ∑ e : E (Fin.last n),
      (∑ α : ∀ j : Fin n, E j.castSucc,
        ∏ j, c.krausEntry (Fin.snoc α e) (readO f) (readI f) j) *
      star (∑ β : ∀ j : Fin n, E j.castSucc,
        ∏ j, c.krausEntry (Fin.snoc β e) (readO g) (readI g) j) :=
  c.chainChoi_apply f g

/-- Orthogonality of the final isometry collapses the two independent incoming memories.
This is the contraction behind the coherent recursion
[Chiribella2009Networks, comblong-pub.tex:1037-1057]. -/
theorem coherent_step_inner {M A B F : Type u}
    [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype F] [DecidableEq F]
    (V : ReferenceIsometry (M × A) (B × F)) (a b : M → ℂ) (i j : A) :
    (∑ o, ∑ e, (∑ m, a m * V.matrix (o, e) (m, i)) *
      star (∑ m, b m * V.matrix (o, e) (m, j))) =
      (if i = j then 1 else 0) * ∑ m, a m * star (b m) := by
  let v : B × F → M × A → ℂ := V.matrix
  have hv (p q) : (∑ z, v z p * star (v z q)) = if p = q then 1 else 0 :=
    V.sum_mul_star p q
  change (∑ o, ∑ e, (∑ m, a m * v (o, e) (m, i)) *
    star (∑ m, b m * v (o, e) (m, j))) = _
  rw [← Fintype.sum_prod_type']
  calc
    _ = ∑ k, ∑ m, (a m * star (b k)) *
        ∑ p, v p (m, i) * star (v p (k, j)) := by
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      simp only [hv, Prod.mk.injEq]
      by_cases h : i = j
      · simp [h]
      · simp [h]

/-! ### Positivity of the chain -/

/-- The memory channel is completely positive in the Choi-positive
formulation. -/
theorem MemoryChain.chainMap_isCompletelyPositive (c : MemoryChain I O E) :
    c.chainMap.IsCompletelyPositive :=
  MatrixMap.ofKraus_completelyPositive c.kraus

/-- The chain Choi operator is positive semidefinite. -/
theorem MemoryChain.chainChoi_posSemidef (c : MemoryChain I O E) :
    c.chainChoi.PosSemidef :=
  (Matrix.posSemidef_submatrix_equiv (combSplitEquiv I O)).2
    c.chainMap_isCompletelyPositive

/-- The chain Choi operator is Hermitian. -/
theorem MemoryChain.chainChoi_isHermitian (c : MemoryChain I O E) :
    c.chainChoi.IsHermitian :=
  c.chainChoi_posSemidef.isHermitian

/-! ### The truncated chain -/

section Truncate

variable {n : ℕ}
variable {I O E : Fin (n + 2) → Type u}
variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- Position bridge: appending after a successor is the successor of the
append. -/
private theorem castAdd_one_succ {m : ℕ} (k : Fin m) :
    Fin.castAdd 1 k.succ = (Fin.castAdd 1 k).succ :=
  rfl

/-- Position bridge: coercing is appending one, in either spelling. -/
private theorem castSucc_eq_castAdd_one {m : ℕ} (k : Fin m) :
    k.castSucc = Fin.castAdd 1 k :=
  rfl

/-- The chain with the final link removed: its wires are the coercions of
the first `n + 1` wires of `c`, and its links are the corresponding initial
links of `c`. The link field is assembled branch-wise through `Fin.cases`,
since the link domains of the truncated family only reduce per branch. -/
def MemoryChain.dropLast (c : MemoryChain I O E) :
    MemoryChain (fun j => I j.castSucc) (fun j => O j.castSucc)
      (fun j => E j.castSucc) where
  link := Fin.cases (c.link 0) fun k => c.link k.succ.castSucc

/-- The truncated chain's first link is the original first link. -/
@[simp]
theorem MemoryChain.dropLast_link_zero (c : MemoryChain I O E) :
    c.dropLast.link 0 = c.link 0 :=
  rfl

/-- The truncated chain's link after `k` is the original link at the coerced
successor position. -/
@[simp]
theorem MemoryChain.dropLast_link_succ (c : MemoryChain I O E) (k : Fin n) :
    c.dropLast.link k.succ = c.link k.succ.castSucc :=
  rfl

/-- Restricting the link entries to the prefix commutes with dropping the last link. -/
theorem MemoryChain.krausEntry_init (c : MemoryChain I O E)
    (α : ∀ j, E j) (o : ∀ j, O j) (i : ∀ j, I j) (j : Fin (n + 1)) :
    c.krausEntry α o i j.castSucc =
      c.dropLast.krausEntry (Fin.init α) (Fin.init o) (Fin.init i) j := by
  cases j using Fin.cases <;> rfl

/-- The amplitude recursion: sum over the incoming memory before discarding the final memory
[Chiribella2009Networks, comblong-pub.tex:1037-1057]. -/
theorem MemoryChain.kraus_step (c : MemoryChain I O E)
    (e : E (Fin.last (n + 1))) (o : ∀ j, O j) (i : ∀ j, I j) :
    c.kraus e o i =
      ∑ m : E (Fin.last n).castSucc,
        c.dropLast.kraus m (Fin.init o) (Fin.init i) *
          (c.link (Fin.last (n + 1))).matrix (o (Fin.last (n + 1)), e)
            (m, i (Fin.last (n + 1))) := by
  rw [kraus, ← Equiv.sum_comp (Fin.snocEquiv (fun j => E j.castSucc))]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro m _
  rw [kraus, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  rw [Fin.prod_univ_castSucc]
  simp only [krausEntry_init, Fin.init_snoc]
  congr 1
  change (c.link (Fin.last (n + 1))).matrix
    (o (Fin.last (n + 1)), Fin.snoc (Fin.snoc α m) e (Fin.last (n + 1)))
    (Fin.snoc (Fin.snoc α m) e (Fin.last n).castSucc, i (Fin.last (n + 1))) = _
  simp
/-- Entry-level bridge between the original chain's Kraus entries at kept
positions and the truncated chain's entries: assembling the full memory
configuration from a prefix configuration and a final value, the entries
below the final link are exactly the truncated chain's entries. The memory
reads are bridged as standalone equations first, since rewriting positions
under the dependent link types is not motive-safe. -/
theorem MemoryChain.krausEntry_castSucc (c : MemoryChain I O E)
    (α' : ∀ i : Fin (n + 1), E (Fin.castAdd 1 i))
    (e : E (Fin.last (n := n + 1)))
    (o : ∀ j, O j) (i : ∀ j, I j) :
    ∀ j : Fin (n + 1), c.krausEntry
        ((WireFam.splitEquiv (m := n + 1) (k := 1) E).symm
          (α', (WireFam.lastWireEquiv E).symm e)) o i j.castSucc =
      c.dropLast.krausEntry α' (fun k => o k.castSucc) (fun k => i k.castSucc) j := by
  intro j
  induction j using Fin.cases with
  | zero =>
    have h0 : ((0 : Fin (n + 1)).castSucc) = (0 : Fin (n + 2)) := rfl
    rw [h0, MemoryChain.krausEntry_zero, MemoryChain.krausEntry_zero, dropLast_link_zero]
    have h0' : ((WireFam.splitEquiv (m := n + 1) (k := 1) E).symm
        (α', (WireFam.lastWireEquiv E).symm e)) (0 : Fin (n + 2)) =
        α' (0 : Fin (n + 1)) :=
      WireFam.splitEquiv_symm_apply_castAdd (m := n + 1) (k := 1) E α'
        ((WireFam.lastWireEquiv E).symm e) 0
    rw [h0']
    rfl
  | succ k =>
    rw [castSucc_eq_castAdd_one, castAdd_one_succ, MemoryChain.krausEntry_succ, MemoryChain.krausEntry_succ,
      dropLast_link_succ]
    have h1 : ((WireFam.splitEquiv (m := n + 1) (k := 1) E).symm
        (α', (WireFam.lastWireEquiv E).symm e)) ((Fin.castAdd 1 k).succ) =
        α' k.succ :=
      WireFam.splitEquiv_symm_apply_castAdd (m := n + 1) (k := 1) E α'
        ((WireFam.lastWireEquiv E).symm e) k.succ
    have h2 : ((WireFam.splitEquiv (m := n + 1) (k := 1) E).symm
        (α', (WireFam.lastWireEquiv E).symm e)) ((Fin.castAdd 1 k).castSucc) =
        α' (Fin.castAdd 1 k) :=
      WireFam.splitEquiv_symm_apply_castAdd (m := n + 1) (k := 1) E α'
        ((WireFam.lastWireEquiv E).symm e) (Fin.castAdd 1 k)
    rw [h1, h2]
    rfl

/-! ### The kept-wire decomposition of the normalization recursion -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Position bridge for the kept comb wires: below the traced output wire, the
kept input-slot of link `i + 1` carries the input wire `I i` of the truncated
chain. -/
theorem keptI (i : Fin (n + 1)) :
    combWire I O (Fin.castAdd 1 (Fin.castAdd (n + 1) (Fin.castAdd 1 i))) = I i.castSucc := by
  have hp : Fin.castAdd 1 (Fin.castAdd (n + 1) (Fin.castAdd 1 i)) =
      Fin.castAdd (n + 2) (Fin.castAdd 1 i) := by
    apply Fin.ext
    simp only [Fin.val_castAdd]
  exact (congrArg (combWire I O) hp).trans
    (combWire_castAdd (I := I) (O := O) (Fin.castAdd 1 i))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Position bridge for the kept comb wires: after the last input slot, the
kept output-slot `j` carries the output wire `O j` of the truncated chain. -/
theorem keptO (j : Fin (n + 1)) :
    combWire I O (Fin.castAdd 1 (Fin.natAdd (n + 2) j)) = O j.castSucc := by
  rw [WireFam.natAdd_castAdd_one]
  exact combWire_natAdd (I := I) (O := O) (Fin.castAdd 1 j)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Position bridge for the kept comb wires: the last kept input slot carries
the input wire consumed by the discarded final link. -/
theorem keptIL :
    combWire I O (Fin.castAdd 1 (Fin.castAdd (n + 1) (Fin.last (n := n + 1)))) =
      I (Fin.last (n := n + 1)) := by
  have hp : Fin.castAdd 1 (Fin.castAdd (n + 1) (Fin.last (n := n + 1))) =
      Fin.castAdd (n + 2) (Fin.last (n := n + 1)) := by
    apply Fin.ext
    simp only [Fin.val_castAdd, Fin.val_last]
  exact (congrArg (combWire I O) hp).trans
    (combWire_castAdd (I := I) (O := O) (Fin.last (n := n + 1)))

/-- The kept comb wires of a chain with the last output wire traced out,
identified with the input wire of the discarded final link together with the
comb wires of the truncated chain. This is the codomain decomposition of the
normalization recursion `lemrecnet`
[Chiribella2009Networks, comblong-pub.tex:860-869]. -/
def combKeptEquiv (I O : Fin (n + 2) → Type u) :
    (∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j)) ≃
      I (Fin.last (n := n + 1)) ×
        (∀ i : Fin ((n + 1) + (n + 1)),
          combWire (fun k => I k.castSucc) (fun k => O k.castSucc) i) :=
  (WireFam.splitEquiv (fun j => combWire I O (Fin.castAdd 1 j))).trans
    (Equiv.prodCongr
      ((WireFam.splitEquiv (m := n + 1) (k := 1)
          (fun i => combWire I O (Fin.castAdd 1 (Fin.castAdd (n + 1) i)))).trans
        (Equiv.prodComm _ _))
      (Equiv.refl _))
    |>.trans (Equiv.prodAssoc _ _ _)
    |>.trans
      (Equiv.prodCongr
        ((WireFam.lastWireEquiv
            (fun i => combWire I O (Fin.castAdd 1 (Fin.castAdd (n + 1) i)))).trans
          (Equiv.cast (keptIL (I := I) (O := O))))
        ((Equiv.prodCongr
            (Equiv.piCongrRight fun i =>
              Equiv.cast (keptI (I := I) (O := O) i))
            (Equiv.piCongrRight fun j =>
              Equiv.cast (keptO (I := I) (O := O) j))).trans
          (WireFam.splitAppendEquiv (fun k => I k.castSucc) (fun k => O k.castSucc)).symm))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Computing the kept decomposition: the discarded-final-link input component
is the value at the last kept input slot. -/
theorem combKeptEquiv_fst (g : ∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j)) :
    (combKeptEquiv I O g).1 =
      cast (keptIL (I := I) (O := O))
        (g (Fin.castAdd (n + 1) (Fin.natAdd (n + 1) (0 : Fin 1)))) :=
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Computing the kept decomposition: the truncated-chain comb component
assembles from the kept values below the traced wire. -/
theorem combKeptEquiv_snd (g : ∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j)) :
    (combKeptEquiv I O g).2 =
      (combSplitEquiv (fun k => I k.castSucc) (fun k => O k.castSucc)).symm
        (fun i => cast (keptI (I := I) (O := O) i) (g (Fin.castAdd (n + 1) (Fin.castAdd 1 i))),
         fun j => cast (keptO (I := I) (O := O) j) (g (Fin.natAdd (n + 2) j))) :=
  rfl

private theorem cast_cast_cancel {α β : Type u} (h : α = β) (y : β) :
    cast h (cast h.symm y) = y := by
  cases h
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Reading the truncated-chain comb component at an input slot of the
truncated chain gives the kept input value of the original chain. -/
theorem readI_combKeptEquiv (g : ∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j))
    (j : Fin (n + 1)) :
    readI ((combKeptEquiv I O g).2) j =
      cast (keptI (I := I) (O := O) j) (g (Fin.castAdd (n + 1) (Fin.castAdd 1 j))) := by
  rw [readI, combKeptEquiv_snd, combSplitEquiv_symm_apply_castAdd]
  exact cast_cast_cancel _ _

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Reading the truncated-chain comb component at an output slot of the
truncated chain gives the kept output value of the original chain. -/
theorem readO_combKeptEquiv (g : ∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j))
    (j : Fin (n + 1)) :
    readO ((combKeptEquiv I O g).2) j =
      cast (keptO (I := I) (O := O) j) (g (Fin.natAdd (n + 2) j)) := by
  rw [readO, combKeptEquiv_snd, combSplitEquiv_symm_apply_natAdd]
  exact cast_cast_cancel _ _


/-! ### The normalization recursion -/

/-- The last free output wire of the comb family, as a wire over `O` of the
final link. -/
private def lastCombWireEquiv :
    (∀ j : Fin 1, combWire (m := n + 2) I O (Fin.natAdd ((n + 2) + (n + 1)) j)) ≃
      O (Fin.last (n := n + 1)) :=
  (WireFam.lastWireEquiv (m := (n + 2) + (n + 1)) (combWire (m := n + 2) I O)).trans
    (Equiv.cast (combWire_last (n := n + 1) I O))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Reading the assembled configuration at the final output position returns
the discarded final output value. -/
private theorem lastCombWireEquiv_symm_apply_zero (x : O (Fin.last (n := n + 1))) :
    lastCombWireEquiv.symm x (0 : Fin 1) =
      cast (combWire_natAdd (I := I) (O := O) (Fin.last (n := n + 1))).symm x := by
  simp only [lastCombWireEquiv, Equiv.symm_trans_apply]
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- The kept-output reads of the assembled configuration are the kept-output
reads of the truncated-chain comb component. -/
private theorem readO_addCases_lastCombWireEquiv
    (g : ∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j))
    (x : O (Fin.last (n := n + 1))) :
    (fun k : Fin (n + 1) => readO (m := n + 2) (I := I) (O := O)
        (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g (lastCombWireEquiv.symm x)) k.castSucc) =
      readO ((combKeptEquiv I O g).2) := by
  funext k
  rw [readO_addCases_castSucc, readO_combKeptEquiv]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- The kept-input reads of the assembled configuration are the kept-input
reads of the truncated-chain comb component. -/
private theorem readI_addCases_lastCombWireEquiv
    (g : ∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j))
    (x : O (Fin.last (n := n + 1))) :
    (fun k : Fin (n + 1) => readI (m := n + 2) (I := I) (O := O)
        (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g (lastCombWireEquiv.symm x)) k.castSucc) =
      readI ((combKeptEquiv I O g).2) := by
  funext k
  rw [readI_addCases (m := n + 1) (I := I) (O := O) (g := g)
      (y := lastCombWireEquiv.symm x) (j := k.castSucc), readI_combKeptEquiv]
  rfl

/-- The normalization recursion of the source's Lemma (lemrecnet): tracing the
last free output wire of the chain Choi collapses the final link telescopically
(over its free output and discarded ancilla memory, by
`ReferenceIsometry.sum_mul_star`) and leaves the identity on the final link's
input wire tensored with the Choi of the truncated chain, on the kept comb
wires [Chiribella2009Networks, comblong-pub.tex:860-869]. -/
theorem MemoryChain.traceOutLast_one_chainChoi (c : MemoryChain I O E) :
    WireFam.traceOutLast (k := 1) (combWire (m := n + 2) I O) c.chainChoi =
      (WireFam.matReindex (combKeptEquiv I O).symm)
        ((1 : CMatrix (I (Fin.last (n := n + 1)))) ⊗ₖ c.dropLast.chainChoi) := by
  ext g g'
  rw [WireFam.matReindex_apply, Equiv.symm_symm, Matrix.kronecker_apply,
    Matrix.one_apply, WireFam.traceOutLast_apply']
  simp only [chainChoi_apply]
  refine (Equiv.sum_comp (lastCombWireEquiv (I := I) (O := O)).symm
    (fun x => ∑ e, c.kraus e
      (readO (m := n + 2) (I := I) (O := O)
        (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g x))
      (readI (m := n + 2) (I := I) (O := O)
        (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g x)) *
      star (c.kraus e
        (readO (m := n + 2) (I := I) (O := O)
          (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g' x))
        (readI (m := n + 2) (I := I) (O := O)
          (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g' x))))).symm.trans ?_
  have hread (g : ∀ j : Fin ((n + 2) + (n + 1)), combWire I O (Fin.castAdd 1 j))
      (x : O (Fin.last (n + 1))) (e : E (Fin.last (n + 1))) :
      c.kraus e
        (readO (m := n + 2) (I := I) (O := O)
          (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g
            ((lastCombWireEquiv (I := I) (O := O)).symm x)))
        (readI (m := n + 2) (I := I) (O := O)
          (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g
            ((lastCombWireEquiv (I := I) (O := O)).symm x))) =
      ∑ m, c.dropLast.kraus m (readO ((combKeptEquiv I O g).2))
        (readI ((combKeptEquiv I O g).2)) *
        (c.link (Fin.last (n + 1))).matrix (x, e) (m, (combKeptEquiv I O g).1) := by
    rw [kraus_step]
    have ho : readO (m := n + 2) (I := I) (O := O)
        (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g (lastCombWireEquiv.symm x))
        (Fin.last (n + 1)) = x := by
      rw [readO_addCases_last, lastCombWireEquiv_symm_apply_zero, cast_cast_cancel]
    have hi : readI (m := n + 2) (I := I) (O := O)
        (Fin.addCases (m := (n + 2) + (n + 1)) (n := 1) g (lastCombWireEquiv.symm x))
        (Fin.last (n + 1)) = (combKeptEquiv I O g).1 := by
      rw [readI_addCases, combKeptEquiv_fst]
      rfl
    apply Finset.sum_congr rfl
    intro m _
    exact congrArg₂ (· * ·)
      (congrArg₂ (c.dropLast.kraus m)
        (readO_addCases_lastCombWireEquiv g x) (readI_addCases_lastCombWireEquiv g x))
      (congrArg₂ (c.link (Fin.last (n + 1))).matrix
        (congrArg (fun o => (o, e)) ho) (congrArg (fun i => (m, i)) hi))
  refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun e _ =>
    congrArg₂ (· * ·) (hread g x e) (congrArg star (hread g' x e))).trans ?_
  exact coherent_step_inner (c.link (Fin.last (n + 1))) _ _ _ _

/-- The trace form of the normalization recursion: tracing the last free
output wire of the chain Choi leaves the identity on the final link's input
wire tensored with the truncated chain's Choi, reindexed onto the kept comb
wires. -/
theorem MemoryChain.traceAt_last_chainChoi (c : MemoryChain I O E) :
    WireFam.traceAt (combWire (m := n + 2) I O) (Fin.last (n := (n + 2) + (n + 1))) c.chainChoi =
      (WireFam.matReindex ((combKeptEquiv I O).symm.trans
          (WireFam.lastKeepEquiv (combWire (m := n + 2) I O)))
        ((1 : CMatrix (I (Fin.last (n := n + 1)))) ⊗ₖ c.dropLast.chainChoi)) := by
  rw [show WireFam.traceAt (combWire (m := n + 2) I O)
      (Fin.last (n := (n + 2) + (n + 1))) c.chainChoi =
      WireFam.matReindex (WireFam.lastKeepEquiv (combWire (m := n + 2) I O))
        (WireFam.traceOutLast (k := 1) (combWire (m := n + 2) I O) c.chainChoi) from
    WireFam.traceAt_last_eq_traceOutLast _ _,
    MemoryChain.traceOutLast_one_chainChoi,
    ← WireFam.matReindex_trans_apply]

end Truncate

/-- Cast is injective: equal transported values come from equal values. -/
private theorem castInj {α β : Type u} (h : α = β) (u v : α)
    (huv : cast h u = cast h v) : u = v := by
  cases h
  exact huv

/-! ### The single-link base case -/

section OneLink

variable {I O E : Fin 1 → Type u}
variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- The single-entry equivalence for `Fin 1`-indexed dependent families. -/
private def piOneEquiv (F : Fin 1 → Type u) : F 0 ≃ (∀ j, F j) where
  toFun e := fun j => (Fin.fin_one_eq_zero j ▸ e : F j)
  invFun α := α 0
  left_inv e := rfl
  right_inv α := by
    funext j
    rw [Fin.fin_one_eq_zero j]

/-- The single free output wire of the one-link comb family. -/
private def oneLastEquiv :
    (∀ j : Fin 1, combWire (m := 1) I O (Fin.natAdd 1 j)) ≃ O (Fin.last (n := 0)) :=
  (WireFam.lastWireEquiv (m := 1) (combWire (m := 1) I O)).trans
    (Equiv.cast (combWire_last (n := 0) I O))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)] in
/-- Evaluating the assembled configuration at the traced position returns the
traced value. -/
private theorem oneLastEquiv_symm_apply_zero (x : O (Fin.last (n := 0))) :
    oneLastEquiv.symm x (0 : Fin 1) =
      cast (combWire_natAdd (I := I) (O := O) (Fin.last (n := 0))).symm x := by
  simp only [oneLastEquiv, Equiv.symm_trans_apply]
  rfl

/-- Tracing the single output wire of a one-link chain's Choi gives one: the
single link is an isometry, so the memory-sliced rank-one expansion collapses
over the output and memory values to the isometry equation. This is the
`traceOutLast` form of the base case. -/
private theorem one_workhorse (c : MemoryChain I O E) :
    WireFam.traceOutLast (k := 1) (combWire (m := 1) I O) c.chainChoi = 1 := by
  ext g g'
  rw [WireFam.traceOutLast_apply']
  simp only [Matrix.one_apply, MemoryChain.chainChoi_apply]
  rw [← Equiv.sum_comp (oneLastEquiv (I := I) (O := O)).symm]
  have hO : ∀ (y : ∀ j : Fin 1, combWire (m := 1) I O (Fin.natAdd 1 j)),
      readO (m := 1) (I := I) (O := O) (Fin.addCases (m := 1) (n := 1) g y) (0 : Fin 1) =
        cast (combWire_natAdd (I := I) (O := O) (Fin.last (n := 0))) (y (0 : Fin 1)) :=
    fun y => readO_addCases_last (m := 0) (I := I) (O := O) g y
  have hO' : ∀ (y : ∀ j : Fin 1, combWire (m := 1) I O (Fin.natAdd 1 j)),
      readO (m := 1) (I := I) (O := O) (Fin.addCases (m := 1) (n := 1) g' y) (0 : Fin 1) =
        cast (combWire_natAdd (I := I) (O := O) (Fin.last (n := 0))) (y (0 : Fin 1)) :=
    fun y => readO_addCases_last (m := 0) (I := I) (O := O) g' y
  have hI : ∀ (y : ∀ j : Fin 1, combWire (m := 1) I O (Fin.natAdd 1 j)),
      readI (m := 1) (I := I) (O := O) (Fin.addCases (m := 1) (n := 1) g y) (0 : Fin 1) =
        cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1)) (g (Fin.castAdd 0 (0 : Fin 1))) :=
    fun y => readI_addCases (m := 0) (I := I) (O := O) g y (0 : Fin 1)
  have hI' : ∀ (y : ∀ j : Fin 1, combWire (m := 1) I O (Fin.natAdd 1 j)),
      readI (m := 1) (I := I) (O := O) (Fin.addCases (m := 1) (n := 1) g' y) (0 : Fin 1) =
        cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1)) (g' (Fin.castAdd 0 (0 : Fin 1))) :=
    fun y => readI_addCases (m := 0) (I := I) (O := O) g' y (0 : Fin 1)
  simp only [MemoryChain.kraus_one, hO, hO', hI, hI',
    oneLastEquiv_symm_apply_zero, cast_cast_cancel]
  rw [← Fintype.sum_prod_type']
  have hstar : (∑ x : O (Fin.last (n := 0)) × E (0 : Fin 1),
      (c.link (0 : Fin (0 + 1))).matrix (x.1, x.2)
        (cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1)) (g (Fin.castAdd 0 (0 : Fin 1)))) *
      star ((c.link (0 : Fin (0 + 1))).matrix (x.1, x.2)
        (cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1)) (g' (Fin.castAdd 0 (0 : Fin 1)))))) =
      (if cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1)) (g (Fin.castAdd 0 (0 : Fin 1))) =
            cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1)) (g' (Fin.castAdd 0 (0 : Fin 1)))
        then 1 else 0) :=
    ReferenceIsometry.sum_mul_star (c.link (0 : Fin (0 + 1))) _ _
  refine hstar.trans ?_
  by_cases hgg : g = g'
  · subst hgg
    have hc : (cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1))
          (g (Fin.castAdd 0 (0 : Fin 1))) =
        cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1))
          (g (Fin.castAdd 0 (0 : Fin 1)))) := rfl
    rw [ite_eq_left hc, ite_eq_left (rfl : g = g)]
  · have hne : ¬ (cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1))
          (g (Fin.castAdd 0 (0 : Fin 1))) =
        cast (combWire_castAdd (I := I) (O := O) (0 : Fin 1))
          (g' (Fin.castAdd 0 (0 : Fin 1)))) := by
      intro heq
      apply hgg
      funext j
      rw [Fin.fin_one_eq_zero j]
      have hz : (Fin.castAdd 0 (0 : Fin 1)) = (0 : Fin 1) := rfl
      rw [← hz]
      exact castInj _ _ _ heq
    rw [ite_eq_right hne, ite_eq_right hgg]

/-- The one-link base case of the normalization recursion: tracing the one
free output wire of a one-link chain's Choi operator gives the identity on the
one input wire (the tensor factor of the discarded empty truncation). -/
theorem MemoryChain.chainChoi_one_traceAt (c : MemoryChain I O E) :
    WireFam.traceAt (combWire (m := 1) I O) (Fin.last (n := 1)) c.chainChoi = 1 := by
  rw [WireFam.traceAt_last_eq_traceOutLast, one_workhorse, WireFam.matReindex_one]

end OneLink

/-! ### Coherent isometry and trace preservation -/

/-- Column orthogonality of the coherent chain, proved by the last-link recursion. -/
theorem MemoryChain.kraus_orthogonal (c : MemoryChain I O E)
    (i j : ∀ k, I k) :
    (∑ o, ∑ e, c.kraus e o i * star (c.kraus e o j)) =
      if i = j then 1 else 0 := by
  induction n with
  | zero =>
    rw [← Equiv.sum_comp (piOneEquiv O)]
    simp only [kraus_one]
    change (∑ o, ∑ e, (c.link 0).matrix (o, e) (i 0) *
      star ((c.link 0).matrix (o, e) (j 0))) = _
    have h := (c.link 0).sum_mul_star (i 0) (j 0)
    rw [Fintype.sum_prod_type] at h
    rw [h]
    congr 1
    exact propext ((piOneEquiv I).symm.injective.eq_iff)
  | succ n ih =>
    rw [← Equiv.sum_comp (Fin.snocEquiv O)]
    simp only [Fintype.sum_prod_type, kraus_step, Fin.snocEquiv,
      Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last]
    rw [Finset.sum_comm]
    have hstep (o : ∀ j : Fin (n + 1), O j.castSucc) :=
      coherent_step_inner (c.link (Fin.last (n + 1)))
        (fun m => c.dropLast.kraus m o (Fin.init i))
        (fun m => c.dropLast.kraus m o (Fin.init j))
        (i (Fin.last (n + 1))) (j (Fin.last (n + 1)))
    refine (Finset.sum_congr rfl (fun o _ => hstep o)).trans ?_
    rw [← Finset.mul_sum]
    refine (congrArg
      ((if i (Fin.last (n + 1)) = j (Fin.last (n + 1)) then (1 : ℂ) else 0) * ·)
      (ih c.dropLast (Fin.init i) (Fin.init j))).trans ?_
    by_cases hlast : i (Fin.last (n + 1)) = j (Fin.last (n + 1))
    · have heq : i = j ↔ Fin.init i = Fin.init j := by
        constructor
        · exact congrArg Fin.init
        · intro h
          exact (Fin.snocEquiv I).symm.injective (Prod.ext hlast h)
      simp [hlast, heq]
    · have hne : i ≠ j := fun h => hlast (congrFun h _)
      simp [hlast, hne]

/-- Star-first form of the reference-isometry equation: collapsing an
isometry's entries with the star on the first factor also gives the Kronecker
delta. -/
private theorem sum_star_mul_eq_one {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (V : ReferenceIsometry A B) (a a' : A) :
    ∑ b : B, star (V.matrix b a) * V.matrix b a' = if a = a' then 1 else 0 := by
  have key : ∀ x y : ℂ, star x * y = star (x * star y) := by
    intro x y
    rw [star_mul, star_star]
    ring
  rw [Finset.sum_congr rfl fun b _ => key (V.matrix b a) (V.matrix b a'), ← star_sum,
    ReferenceIsometry.sum_mul_star V a a']
  by_cases h : a = a'
  · simp [h]
  · simp [h]

/-- Conjugating a reference isometry along equivalences of its reference
systems: the matrix entries are read through the inverse transports. -/
def MemoryChain.linkCongr {A B A' B' : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    (V : ReferenceIsometry A B) (ea : A ≃ A') (eb : B ≃ B') : ReferenceIsometry A' B' where
  matrix := fun b' a' => V.matrix (eb.symm b') (ea.symm a')
  isometry := by
    ext a₁ a₂
    show (∑ b' : B', star (V.matrix (eb.symm b') (ea.symm a₁)) *
        V.matrix (eb.symm b') (ea.symm a₂)) = (if a₁ = a₂ then 1 else 0)
    have hfinal : (∑ b : B, star (V.matrix b (ea.symm a₁)) * V.matrix b (ea.symm a₂)) =
        (if a₁ = a₂ then 1 else 0) := by
      rw [sum_star_mul_eq_one V (ea.symm a₁) (ea.symm a₂)]
      by_cases ha : a₁ = a₂
      · subst ha
        simp
      · rw [ite_eq_right (fun hne => ha (Equiv.injective ea.symm hne)), ite_eq_right ha]
    exact (Equiv.sum_comp eb.symm
        (fun b => star (V.matrix b (ea.symm a₁)) * V.matrix b (ea.symm a₂))).trans hfinal

/-- The coherent global isometry, obtained by stacking the final-environment Kraus slices. -/
def MemoryChain.coherentIsometry (c : MemoryChain I O E) :
    ReferenceIsometry (∀ j, I j) ((∀ j, O j) × E (Fin.last n)) where
  matrix p i := c.kraus p.2 p.1 i
  isometry := by
    ext i j
    change (∑ p : (∀ j, O j) × E (Fin.last n),
      star (c.kraus p.2 p.1 i) * c.kraus p.2 p.1 j) = _
    simpa only [Fintype.sum_prod_type, mul_comm, Matrix.one_apply, eq_comm] using
      c.kraus_orthogonal j i

/-- Compose a prefix isometry with its next memory interaction, with explicit tensor reassociation. -/
def coherentStepIsometry {A B M C D F : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
    (W : ReferenceIsometry A (B × M)) (V : ReferenceIsometry (M × C) (D × F)) :
    ReferenceIsometry (A × C) ((B × D) × F) :=
  MemoryChain.linkCongr
    (((ReferenceIsometry.ofInjective (id : B → B) Function.injective_id).prod V).comp
      (MemoryChain.linkCongr
        (W.prod (ReferenceIsometry.ofInjective (id : C → C) Function.injective_id))
        (Equiv.refl _) (Equiv.prodAssoc B M C)))
    (Equiv.refl _) (Equiv.prodAssoc B D F).symm

/-- Matrix entries of the tensor-composed step are coherent incoming-memory sums. -/
theorem coherentStepIsometry_matrix {A B M C D F : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
    (W : ReferenceIsometry A (B × M)) (V : ReferenceIsometry (M × C) (D × F))
    (a : A) (b : B) (c : C) (d : D) (f : F) :
    (coherentStepIsometry W V).matrix ((b, d), f) (a, c) =
      ∑ m, W.matrix (b, m) a * V.matrix (d, f) (m, c) := by
  change (∑ p : B × (M × C),
    ((if b = p.1 then (1 : ℂ) else 0) * V.matrix (d, f) p.2) *
      (W.matrix (p.1, p.2.1) a * (if p.2.2 = c then 1 else 0))) = _
  simp [Fintype.sum_prod_type, mul_comm]

/-- Reference isometries with the same matrix are equal. -/
private theorem refIso_ext {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (V W : ReferenceIsometry A B)
    (h : V.matrix = W.matrix) : V = W := by
  cases V
  cases W
  cases h
  rfl

/-- The coherent chain extends by tensor product and composition, up to explicit wire equivalences.
This realizes the source's isometry recursion
[Chiribella2009Networks, comblong-pub.tex:1037-1057]. -/
theorem MemoryChain.coherentIsometry_step
    {I O E : Fin (n + 2) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
    (c : MemoryChain I O E) :
    c.coherentIsometry =
      MemoryChain.linkCongr
        (coherentStepIsometry c.dropLast.coherentIsometry (c.link (Fin.last (n + 1))))
        ((Equiv.prodComm _ _).trans (Fin.snocEquiv I))
        (Equiv.prodCongr ((Equiv.prodComm _ _).trans (Fin.snocEquiv O)) (Equiv.refl _)) := by
  have hm : c.coherentIsometry.matrix =
      (MemoryChain.linkCongr
        (coherentStepIsometry c.dropLast.coherentIsometry (c.link (Fin.last (n + 1))))
        ((Equiv.prodComm _ _).trans (Fin.snocEquiv I))
        (Equiv.prodCongr ((Equiv.prodComm _ _).trans (Fin.snocEquiv O))
          (Equiv.refl _))).matrix := by
    ext p i
    change c.kraus p.2 p.1 i =
      (coherentStepIsometry c.dropLast.coherentIsometry (c.link (Fin.last (n + 1)))).matrix
        ((Fin.init p.1, p.1 (Fin.last (n + 1))), p.2)
        (Fin.init i, i (Fin.last (n + 1)))
    exact (c.kraus_step p.2 p.1 i).trans
      (coherentStepIsometry_matrix c.dropLast.coherentIsometry
        (c.link (Fin.last (n + 1))) (Fin.init i) (Fin.init p.1)
        (i (Fin.last (n + 1))) (p.1 (Fin.last (n + 1))) p.2).symm
  exact refIso_ext _ _ hm

/-- The chain channel discards only the final environment of its coherent global isometry
[Chiribella2009Networks, comblong-pub.tex:1037-1057]. -/
theorem MemoryChain.chainMap_eq_partialTrace (c : MemoryChain I O E)
    (X : CMatrix (∀ j, I j)) :
    c.chainMap X =
      partialTraceB (c.coherentIsometry.matrix * X * c.coherentIsometry.matrix.conjTranspose) := by
  ext o p
  change (∑ e, c.kraus e * X * (c.kraus e).conjTranspose) o p = _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    partialTraceB, coherentIsometry]
  rfl

/-- Completeness of the final-environment Kraus family. -/
theorem MemoryChain.krausIsometry (c : MemoryChain I O E) :
    MatrixMap.krausAdjoint c.kraus (1 : CMatrix (∀ j, O j)) = 1 := by
  ext i j
  simp only [MatrixMap.krausAdjoint, Matrix.mul_one, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [Finset.sum_comm]
  simpa only [mul_comm, eq_comm] using c.kraus_orthogonal j i

/-- The memory channel of the chain is trace-preserving. -/
theorem MemoryChain.chainMap_isTracePreserving (c : MemoryChain I O E) :
    c.chainMap.IsTracePreserving :=
  MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one c.kraus c.krausIsometry

/-- The memory channel realized by the chain [Chiribella2009Networks,
comblong-pub.tex:1891-1892]. -/
def MemoryChain.channel (c : MemoryChain I O E) : Channel (∀ j, I j) (∀ j, O j) where
  map := c.chainMap
  completelyPositive := c.chainMap_isCompletelyPositive
  tracePreserving := c.chainMap_isTracePreserving
  mapsPositive := MatrixMap.ofKraus_mapsPositive c.kraus

section ReindexMemory

variable {E' : Fin (n + 1) → Type u}
variable [∀ j, Fintype (E' j)] [∀ j, DecidableEq (E' j)]

/-- Relabelling the internal memories of a chain along pointwise wire
equivalences: each link isometry transports the memory it consumes and the
memory it produces. -/
def MemoryChain.reindexMemory (c : MemoryChain I O E)
    (e : (j : Fin (n + 1)) → E j ≃ E' j) : MemoryChain I O E' where
  link := Fin.cases
    (MemoryChain.linkCongr (c.link 0) (Equiv.refl (I 0)) (Equiv.prodCongr (Equiv.refl (O 0)) (e 0)))
    fun k => MemoryChain.linkCongr (c.link k.succ)
      (Equiv.prodCongr (e k.castSucc) (Equiv.refl (I k.succ)))
      (Equiv.prodCongr (Equiv.refl (O k.succ)) (e k.succ))

/-- Entrywise, the relabelled chain's Kraus entries are the original entries,
read through the pointwise inverse memory transports. -/
theorem MemoryChain.krausEntry_reindexMemory (c : MemoryChain I O E)
    (e : (j : Fin (n + 1)) → E j ≃ E' j) (α' : ∀ j, E' j) (o : ∀ j, O j) (i : ∀ j, I j) :
    ∀ j : Fin (n + 1), (c.reindexMemory e).krausEntry α' o i j =
      c.krausEntry (fun j => (e j).symm (α' j)) o i j := by
  intro j
  induction j using Fin.cases with
  | zero =>
    rw [MemoryChain.krausEntry_zero, MemoryChain.krausEntry_zero]
    rfl
  | succ k =>
    rw [MemoryChain.krausEntry_succ, MemoryChain.krausEntry_succ]
    rfl

/-- The Kraus family of the memory-relabelled chain is the original family,
read through the pointwise inverse memory transports. -/
theorem MemoryChain.kraus_reindexMemory (c : MemoryChain I O E)
    (e : (j : Fin (n + 1)) → E j ≃ E' j) (z : E' (Fin.last n)) :
    (c.reindexMemory e).kraus z = c.kraus ((e (Fin.last n)).symm z) := by
  ext o i
  rw [kraus_apply, kraus_apply,
    ← Equiv.sum_comp (Equiv.piCongrRight fun j : Fin n => e j.castSucc)]
  apply Finset.sum_congr rfl
  intro α _
  have hmem : (fun j => (e j).symm
      (Fin.snoc ((Equiv.piCongrRight fun k : Fin n => e k.castSucc) α) z j)) =
      Fin.snoc α ((e (Fin.last n)).symm z) := by
    funext j
    cases j using Fin.lastCases <;> simp
  simp only [krausEntry_reindexMemory, hmem]

/-- Relabelling the internal memories does not change the chain Choi: the
memories are internal to the chain and only their configurations are summed
over [Chiribella2009Networks, comblong-pub.tex:1891-1892]. -/
theorem MemoryChain.chainChoi_reindexMemory (c : MemoryChain I O E)
    (e : (j : Fin (n + 1)) → E j ≃ E' j) :
    (c.reindexMemory e).chainChoi = c.chainChoi := by
  ext f g
  rw [chainChoi_apply, chainChoi_apply, ← Equiv.sum_comp (e (Fin.last n))]
  simp only [kraus_reindexMemory, Equiv.symm_apply_apply]

end ReindexMemory

/-! ### Reindexing the free wires -/

section ReindexWires

variable {I' O' : Fin (n + 1) → Type u}
variable [∀ j, Fintype (I' j)] [∀ j, DecidableEq (I' j)]
variable [∀ j, Fintype (O' j)] [∀ j, DecidableEq (O' j)]

/-- Relabelling the free wires of a chain along pointwise wire equivalences:
each link isometry transports its free input and output wires; the internal
memories are untouched. -/
def MemoryChain.reindexWires (c : MemoryChain I O E)
    (dI : (j : Fin (n + 1)) → I j ≃ I' j) (dO : (j : Fin (n + 1)) → O j ≃ O' j) :
    MemoryChain I' O' E where
  link := Fin.cases
    (MemoryChain.linkCongr (c.link 0) (dI 0) (Equiv.prodCongr (dO 0) (Equiv.refl (E 0))))
    fun k => MemoryChain.linkCongr (c.link k.succ)
      (Equiv.prodCongr (Equiv.refl (E k.castSucc)) (dI k.succ))
      (Equiv.prodCongr (dO k.succ) (Equiv.refl (E k.succ)))

/-- Entrywise, the relabelled chain's Kraus entries are the original entries,
read through the pointwise inverse free-wire transports. -/
theorem MemoryChain.krausEntry_reindexWires (c : MemoryChain I O E)
    (dI : (j : Fin (n + 1)) → I j ≃ I' j) (dO : (j : Fin (n + 1)) → O j ≃ O' j)
    (α : ∀ j, E j) (o' : ∀ j, O' j) (i' : ∀ j, I' j) :
    ∀ j : Fin (n + 1), (c.reindexWires dI dO).krausEntry α o' i' j =
      c.krausEntry α (fun j => (dO j).symm (o' j)) (fun j => (dI j).symm (i' j)) j := by
  intro j
  induction j using Fin.cases with
  | zero =>
    rw [MemoryChain.krausEntry_zero, MemoryChain.krausEntry_zero]
    rfl
  | succ k =>
    rw [MemoryChain.krausEntry_succ, MemoryChain.krausEntry_succ]
    rfl

/-- The Kraus family of the wire-relabelled chain is the original family, read
through the pointwise inverse free-wire transports. -/
theorem MemoryChain.kraus_reindexWires (c : MemoryChain I O E)
    (dI : (j : Fin (n + 1)) → I j ≃ I' j) (dO : (j : Fin (n + 1)) → O j ≃ O' j)
    (e : E (Fin.last n)) (o' : ∀ j, O' j) (i' : ∀ j, I' j) :
    (c.reindexWires dI dO).kraus e o' i' =
      c.kraus e (fun j => (dO j).symm (o' j)) (fun j => (dI j).symm (i' j)) := by
  rw [kraus_apply, kraus_apply]
  exact Finset.sum_congr rfl fun α _ =>
    Finset.prod_congr rfl fun j _ =>
      krausEntry_reindexWires c dI dO (Fin.snoc α e) o' i' j

/-- The Choi operator of the wire-relabelled chain map is the original Choi
operator with both configuration blocks transported through the pointwise
inverse wire equivalences. -/
theorem MemoryChain.choi_chainMap_reindexWires (c : MemoryChain I O E)
    (dI : (j : Fin (n + 1)) → I j ≃ I' j) (dO : (j : Fin (n + 1)) → O j ≃ O' j) :
    MatrixMap.choi (c.reindexWires dI dO).chainMap =
      WireFam.matReindex
        (Equiv.prodCongr (Equiv.piCongrRight dI) (Equiv.piCongrRight dO))
        (MatrixMap.choi c.chainMap) := by
  ext q₁ q₂
  simp only [chainMap, MatrixMap.choi_ofKraus, Matrix.sum_apply, Matrix.vecMulVec,
    WireFam.matReindex_apply, MemoryChain.kraus_apply, MemoryChain.krausEntry_reindexWires]
  rfl

/-- The canonical equivalence of comb wire families induced by pointwise
free-wire equivalences: through the block split, both blocks transport
componentwise. -/
def combWireEquiv {I O I' O' : Fin (n + 1) → Type u}
    (dI : (j : Fin (n + 1)) → I j ≃ I' j) (dO : (j : Fin (n + 1)) → O j ≃ O' j) :
    (∀ i, combWire I O i) ≃ (∀ i, combWire I' O' i) :=
  (combSplitEquiv I O).trans
    ((Equiv.prodCongr (Equiv.piCongrRight dI) (Equiv.piCongrRight dO)).trans
      (combSplitEquiv I' O').symm)

/-- Reindexing the free wires transports the chain Choi along the canonical
comb-family equivalence [Chiribella2009Networks, comblong-pub.tex:1891-1892]. -/
theorem MemoryChain.chainChoi_reindexWires (c : MemoryChain I O E)
    (dI : (j : Fin (n + 1)) → I j ≃ I' j) (dO : (j : Fin (n + 1)) → O j ≃ O' j) :
    (c.reindexWires dI dO).chainChoi = WireFam.matReindex (combWireEquiv dI dO) c.chainChoi := by
  show WireFam.matReindex (combSplitEquiv I' O').symm
      (MatrixMap.choi (c.reindexWires dI dO).chainMap) =
    WireFam.matReindex (combWireEquiv dI dO)
      (WireFam.matReindex (combSplitEquiv I O).symm (MatrixMap.choi c.chainMap))
  rw [choi_chainMap_reindexWires, ← WireFam.matReindex_trans_apply,
    ← WireFam.matReindex_trans_apply]
  have hsquare : (combSplitEquiv I O).symm.trans (combWireEquiv dI dO) =
      (Equiv.prodCongr (Equiv.piCongrRight dI) (Equiv.piCongrRight dO)).trans
        (combSplitEquiv I' O').symm := by
    simp only [combWireEquiv, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
  rw [hsquare]

end ReindexWires

/-! ## Composition: extending a chain by one final link -/

section Snoc

variable {n : ℕ}
variable {I O E : Fin (n + 1) → Type u}
variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
variable {I' O' E' : Type u}
variable [Fintype I'] [DecidableEq I']
variable [Fintype O'] [DecidableEq O']
variable [Fintype E'] [DecidableEq E']

/-- Extending a wire family by one final wire: the appended family, whose
computation rules are those of `WireFam.append` at the coerced and final
positions. -/
abbrev snocFam (W : Fin (n + 1) → Type u) (W' : Type u) : Fin (n + 2) → Type u :=
  WireFam.append (m := n + 1) (k := 1) W fun _ : Fin 1 => W'

/-- The appended family carries the original family at the coerced positions. -/
theorem snocFam_castSucc (W : Fin (n + 1) → Type u) (W' : Type u) (j : Fin (n + 1)) :
    snocFam W W' (Fin.castAdd 1 j) = W j :=
  WireFam.append_castAdd (m := n + 1) (k := 1) W (fun _ : Fin 1 => W') j

/-- The appended family carries the new wire at the final position. -/
theorem snocFam_last (W : Fin (n + 1) → Type u) (W' : Type u) :
    snocFam W W' (Fin.last (n := n + 1)) = W' := by
  have h : (Fin.last (n := n + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) := rfl
  rw [h]
  exact WireFam.append_natAdd (m := n + 1) (k := 1) W (fun _ : Fin 1 => W') 0

instance instFintypeSnocFam {W : Fin (n + 1) → Type u} [∀ j, Fintype (W j)]
    {W' : Type u} [Fintype W'] {i : Fin (n + 1 + 1)} :
    Fintype (snocFam W W' i) :=
  WireFam.instFintypeAppend (W₁ := W) (W₂ := fun _ : Fin 1 => W') i

instance instDecidableEqSnocFam {W : Fin (n + 1) → Type u} [∀ j, DecidableEq (W j)]
    {W' : Type u} [DecidableEq W'] {i : Fin (n + 1 + 1)} :
    DecidableEq (snocFam W W' i) := by
  induction i using Fin.addCases with
  | left j => rw [snocFam_castSucc]; infer_instance
  | right j =>
    have h : snocFam W W' (Fin.natAdd (n + 1) j) = W' :=
      WireFam.append_natAdd (m := n + 1) (k := 1) W (fun _ : Fin 1 => W') j
    rw [h]
    infer_instance

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (E j)]
  [∀ j, DecidableEq (E j)] [Fintype I'] [DecidableEq I'] [Fintype E'] [DecidableEq E'] in
/-- Splitting a cast of a pair into the pair of the component casts. -/
private theorem cast_pair_inv {A A' B B' : Type u} (ha : A = A') (hb : B = B')
    (x : A') (y : B') :
    cast (congrArg₂ Prod ha hb).symm (x, y) = (cast ha.symm x, cast hb.symm y) := by
  cases ha
  cases hb
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (E j)]
  [∀ j, DecidableEq (E j)] [Fintype I'] [DecidableEq I'] [Fintype E'] [DecidableEq E'] in
/-- Splitting a doubly-inverted cast of a pair into the pair of the component
casts. -/
private theorem cast_pair_symm_symm {A A' B B' : Type u} (ha : A' = A) (hb : B' = B)
    (x : A') (y : B') :
    cast (congrArg₂ Prod ha hb).symm.symm (x, y) = (cast ha x, cast hb y) := by
  cases ha
  cases hb
  rfl

/-- Extending a chain by one final isometric link `V`: the appended chain
whose first `n + 1` links are `c`'s links, transported to the appended
families, and whose final link is `V`. Appending links one at a time via
`snoc` builds longer chains,
which is the induction the comb-realization direction performs. -/
def MemoryChain.snoc (c : MemoryChain I O E)
    (V : ReferenceIsometry (E (Fin.last n) × I') (O' × E')) :
    MemoryChain (snocFam I I') (snocFam O O') (snocFam E E') where
  link := Fin.cases
    (MemoryChain.linkCongr (c.link 0) (Equiv.cast (snocFam_castSucc I I' 0).symm)
      (Equiv.cast (congrArg₂ Prod (snocFam_castSucc O O' 0).symm
        (snocFam_castSucc E E' 0).symm)))
    fun k => Fin.snoc
      (α := fun i : Fin (n + 1) => ReferenceIsometry
        (linkDom (snocFam I I') (snocFam E E') i.succ)
        ((snocFam O O') i.succ × (snocFam E E') i.succ))
      (fun i : Fin n => MemoryChain.linkCongr (c.link i.succ)
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' i.castSucc)
          (snocFam_castSucc I I' i.succ)).symm)
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc O O' i.succ).symm
          (snocFam_castSucc E E' i.succ).symm)))
      (MemoryChain.linkCongr V
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' (Fin.last n))
          (snocFam_last I I')).symm)
        (Equiv.cast (congrArg₂ Prod (snocFam_last O O').symm (snocFam_last E E').symm)))
      k

/-- Entrywise below the final link, the appended chain's Kraus entries are the
original chain's entries, read through the coerced configurations. -/
private theorem MemoryChain.krausEntry_snoc (c : MemoryChain I O E)
    (V : ReferenceIsometry (E (Fin.last n) × I') (O' × E'))
    (α : ∀ j, snocFam E E' j) (o : ∀ j, snocFam O O' j) (i : ∀ j, snocFam I I' j) :
    ∀ j : Fin (n + 1), (c.snoc V).krausEntry α o i j.castSucc =
      c.krausEntry (fun l => cast (snocFam_castSucc E E' l) (α l.castSucc))
        (fun l => cast (snocFam_castSucc O O' l) (o l.castSucc))
        (fun l => cast (snocFam_castSucc I I' l) (i l.castSucc)) j := by
  intro j
  induction j using Fin.cases with
  | zero =>
    have h0 : ((0 : Fin (n + 1)).castSucc) = (0 : Fin (n + 2)) := rfl
    rw [h0, MemoryChain.krausEntry_zero, MemoryChain.krausEntry_zero]
    show (c.link 0).matrix
        (cast (congrArg₂ Prod (snocFam_castSucc O O' 0).symm
            (snocFam_castSucc E E' 0).symm).symm (o 0, α 0))
        (cast ((snocFam_castSucc I I' 0).symm).symm (i 0)) = _
    have hp := cast_pair_inv (snocFam_castSucc O O' 0).symm
      (snocFam_castSucc E E' 0).symm (o 0) (α 0)
    rw [hp]
    rfl
  | succ k =>
    rw [castSucc_eq_castAdd_one, castAdd_one_succ, MemoryChain.krausEntry_succ, MemoryChain.krausEntry_succ]
    have hlink : ((c.snoc V).link ((Fin.castAdd 1 k).succ)) = MemoryChain.linkCongr (c.link k.succ)
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' k.castSucc)
          (snocFam_castSucc I I' k.succ)).symm)
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc O O' k.succ).symm
          (snocFam_castSucc E E' k.succ).symm)) := by
      show Fin.snoc
        (α := fun i : Fin (n + 1) => ReferenceIsometry
          (linkDom (snocFam I I') (snocFam E E') i.succ)
          ((snocFam O O') i.succ × (snocFam E E') i.succ))
        (fun i : Fin n => MemoryChain.linkCongr (c.link i.succ)
          (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' i.castSucc)
            (snocFam_castSucc I I' i.succ)).symm)
          (Equiv.cast (congrArg₂ Prod (snocFam_castSucc O O' i.succ).symm
            (snocFam_castSucc E E' i.succ).symm)))
        (MemoryChain.linkCongr V
          (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' (Fin.last n))
            (snocFam_last I I')).symm)
          (Equiv.cast (congrArg₂ Prod (snocFam_last O O').symm (snocFam_last E E').symm)))
        (Fin.castAdd 1 k) = _
      exact Fin.snoc_castSucc
        (α := fun i : Fin (n + 1) => ReferenceIsometry
          (linkDom (snocFam I I') (snocFam E E') i.succ)
          ((snocFam O O') i.succ × (snocFam E E') i.succ))
        (MemoryChain.linkCongr V
          (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' (Fin.last n))
            (snocFam_last I I')).symm)
          (Equiv.cast (congrArg₂ Prod (snocFam_last O O').symm (snocFam_last E E').symm)))
        (fun i : Fin n => MemoryChain.linkCongr (c.link i.succ)
          (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' i.castSucc)
            (snocFam_castSucc I I' i.succ)).symm)
          (Equiv.cast (congrArg₂ Prod (snocFam_castSucc O O' i.succ).symm
            (snocFam_castSucc E E' i.succ).symm)))
        k
    rw [hlink]
    show (c.link k.succ).matrix
        (cast (congrArg₂ Prod (snocFam_castSucc O O' k.succ).symm
            (snocFam_castSucc E E' k.succ).symm).symm
          (o ((Fin.castAdd 1 k).succ), α ((Fin.castAdd 1 k).succ)))
        (cast (congrArg₂ Prod (snocFam_castSucc E E' k.castSucc)
            (snocFam_castSucc I I' k.succ)).symm.symm
          (α ((Fin.castAdd 1 k).castSucc), i ((Fin.castAdd 1 k).succ))) = _
    have hp := cast_pair_inv (snocFam_castSucc O O' k.succ).symm
      (snocFam_castSucc E E' k.succ).symm (o ((Fin.castAdd 1 k).succ))
      (α ((Fin.castAdd 1 k).succ))
    have hq := cast_pair_symm_symm (snocFam_castSucc E E' k.castSucc)
      (snocFam_castSucc I I' k.succ) (α ((Fin.castAdd 1 k).castSucc))
      (i ((Fin.castAdd 1 k).succ))
    exact congrArg₂
      (fun (u : O k.succ × E k.succ) (w : E k.castSucc × I k.succ) =>
        (c.link k.succ).matrix u w) hp hq

/-- At the final position, the appended chain's Kraus entry is the final
link's entry, read through the final configurations. -/
private theorem MemoryChain.krausEntry_snoc_last (c : MemoryChain I O E)
    (V : ReferenceIsometry (E (Fin.last n) × I') (O' × E'))
    (α : ∀ j, snocFam E E' j) (o : ∀ j, snocFam O O' j) (i : ∀ j, snocFam I I' j) :
    (c.snoc V).krausEntry α o i (Fin.last (n := n + 1)) =
      V.matrix (cast (snocFam_last O O') (o (Fin.last (n := n + 1))),
          cast (snocFam_last E E') (α (Fin.last (n := n + 1))))
        (cast (snocFam_castSucc E E' (Fin.last n)) (α ((Fin.last (n := n)).castSucc)),
          cast (snocFam_last I I') (i (Fin.last (n := n + 1)))) := by
  have h0 : (c.snoc V).krausEntry α o i (Fin.last (n := n + 1)) =
      (c.snoc V).krausEntry α o i ((Fin.last (n := n)).succ) := rfl
  rw [h0, MemoryChain.krausEntry_succ]
  have hlink : ((c.snoc V).link ((Fin.last n).succ)) = MemoryChain.linkCongr V
      (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' (Fin.last n))
        (snocFam_last I I')).symm)
      (Equiv.cast (congrArg₂ Prod (snocFam_last O O').symm (snocFam_last E E').symm)) := by
    show Fin.snoc
      (α := fun i : Fin (n + 1) => ReferenceIsometry
        (linkDom (snocFam I I') (snocFam E E') i.succ)
        ((snocFam O O') i.succ × (snocFam E E') i.succ))
      (fun i : Fin n => MemoryChain.linkCongr (c.link i.succ)
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' i.castSucc)
          (snocFam_castSucc I I' i.succ)).symm)
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc O O' i.succ).symm
          (snocFam_castSucc E E' i.succ).symm)))
      (MemoryChain.linkCongr V
        (Equiv.cast (congrArg₂ Prod (snocFam_castSucc E E' (Fin.last n))
          (snocFam_last I I')).symm)
        (Equiv.cast (congrArg₂ Prod (snocFam_last O O').symm (snocFam_last E E').symm)))
      (Fin.last n) = _
    rw [Fin.snoc_last]
    rfl
  rw [hlink]
  show V.matrix
      (cast (congrArg₂ Prod (snocFam_last O O').symm (snocFam_last E E').symm).symm
        (o ((Fin.last n).succ), α ((Fin.last n).succ)))
      (cast (congrArg₂ Prod (snocFam_castSucc E E' (Fin.last n))
          (snocFam_last I I')).symm.symm
        (α ((Fin.last n).castSucc), i ((Fin.last n).succ))) = _
  have hp := cast_pair_inv (snocFam_last O O').symm (snocFam_last E E').symm
    (o ((Fin.last n).succ)) (α ((Fin.last n).succ))
  have hq := cast_pair_symm_symm (snocFam_castSucc E E' (Fin.last n))
    (snocFam_last I I') (α ((Fin.last n).castSucc)) (i ((Fin.last n).succ))
  rw [hp, hq]
  rfl

/-- Appending an isometry coherently sums the incoming memory in each final Kraus slice. -/
theorem MemoryChain.kraus_snoc (c : MemoryChain I O E)
    (V : ReferenceIsometry (E (Fin.last n) × I') (O' × E'))
    (e : snocFam E E' (Fin.last (n + 1)))
    (o : ∀ j, snocFam O O' j) (i : ∀ j, snocFam I I' j) :
    (c.snoc V).kraus e o i =
      ∑ m : E (Fin.last n),
        c.kraus m
          (fun j => cast (snocFam_castSucc O O' j) (o j.castSucc))
          (fun j => cast (snocFam_castSucc I I' j) (i j.castSucc)) *
        V.matrix (cast (snocFam_last O O') (o (Fin.last (n + 1))),
            cast (snocFam_last E E') e)
          (m, cast (snocFam_last I I') (i (Fin.last (n + 1)))) := by
  let t := Equiv.piCongrRight fun j : Fin (n + 1) =>
    Equiv.cast (snocFam_castSucc E E' j).symm
  rw [kraus_apply]
  refine (Equiv.sum_comp t
    (fun α => ∏ j, (c.snoc V).krausEntry (Fin.snoc α e) o i j)).symm.trans ?_
  have hmem (α : ∀ j, E j) :
      (fun j => cast (snocFam_castSucc E E' j) ((Fin.snoc (t α) e) j.castSucc)) = α := by
    funext j
    simp [t]
  have hpath (α : ∀ j, E j) :
      (∏ j, (c.snoc V).krausEntry (Fin.snoc (t α) e) o i j) =
      (∏ j, c.krausEntry α
        (fun j => cast (snocFam_castSucc O O' j) (o j.castSucc))
        (fun j => cast (snocFam_castSucc I I' j) (i j.castSucc)) j) *
      V.matrix (cast (snocFam_last O O') (o (Fin.last (n + 1))),
          cast (snocFam_last E E') e)
        (α (Fin.last n), cast (snocFam_last I I') (i (Fin.last (n + 1)))) := by
    rw [Fin.prod_univ_castSucc]
    simp only [krausEntry_snoc, hmem, krausEntry_snoc_last, Fin.snoc_last]
    rw [← congrFun (hmem α) (Fin.last n)]
  simp only [hpath]
  rw [← Equiv.sum_comp (Fin.snocEquiv E)]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last,
    kraus_apply, Finset.sum_mul]

/-- The appended Choi has independent incoming-memory sums on the two amplitudes. -/
theorem MemoryChain.chainChoi_snoc (c : MemoryChain I O E)
    (V : ReferenceIsometry (E (Fin.last n) × I') (O' × E'))
    (f g : ∀ i, combWire (snocFam I I') (snocFam O O') i) :
    (c.snoc V).chainChoi f g =
      ∑ e : snocFam E E' (Fin.last (n + 1)),
        (∑ m : E (Fin.last n),
          c.kraus m
            (fun j => cast (snocFam_castSucc O O' j) (readO f j.castSucc))
            (fun j => cast (snocFam_castSucc I I' j) (readI f j.castSucc)) *
          V.matrix (cast (snocFam_last O O') (readO f (Fin.last (n + 1))),
              cast (snocFam_last E E') e)
            (m, cast (snocFam_last I I') (readI f (Fin.last (n + 1))))) *
        star (∑ m' : E (Fin.last n),
          c.kraus m'
            (fun j => cast (snocFam_castSucc O O' j) (readO g j.castSucc))
            (fun j => cast (snocFam_castSucc I I' j) (readI g j.castSucc)) *
          V.matrix (cast (snocFam_last O O') (readO g (Fin.last (n + 1))),
              cast (snocFam_last E E') e)
            (m', cast (snocFam_last I I') (readI g (Fin.last (n + 1))))) := by
  simp only [chainChoi_apply, kraus_snoc]

end Snoc

end Chain

end

end QIT.HigherOrder
