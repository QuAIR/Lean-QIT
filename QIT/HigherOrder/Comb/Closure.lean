/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HigherOrder.Comb.Admissible
public import QIT.Core.Map.LinkProductPositivity

/-!
# Closure of comb normalization under admissible-map insertion

This module proves that recursive comb normalization is closed under the
admissible-map insertion action, per the normalization recursion
[Chiribella2009Networks, comblong-pub.tex:860-877] (which includes its
partial-trace restatement), with composition read as the link product
[Chiribella2009Networks, comblong-pub.tex:1279-1286].

## Main results

* `Comb.Normalized.isDeterministicMap`: every recursively normalized comb
  acts as a completely deterministic N-map on every jointly normalized inner
  comb with independent boundary ancillas.
* `Comb.Normalized.reindex_iff`: normalization transports along pointwise
  wire equivalences of the input and output families.
* `Comb.spaceEquiv`: pointwise wire equivalences induce an equivalence of
  comb spaces, with `@[simp]` action lemmas.
* `Comb.normalized_suffix_comp_final`: normalization is closed under the
  monotone-suffix composition of a normalized comb with a normalized
  window, with `Comb.IsProbabilistic.suffix_comp` as the probabilistic
  corollary.
* `Comb.suffixComp_eq_linkAction`: at the endpoint `k = 0`, `m = n` the
  suffix composition is exactly the outer comb's link action on the window
  operator, transported to the composite's packaged channel space.
* `Comb.normalized_linkAction`: the link action of a normalized comb on a
  normalized window is a channel (positive semidefinite with unit input
  partial trace) — the endpoint reading of the composition closure.

## Design notes

The insertion closure is proved by entrywise induction mirroring the source
split: the operator identities are carried by the existing
`actionMap`/`linkAction` definitions, while normalization is transported by
the recursion itself. Reindexing transport bridges the packaged
`Comb.Space` carrier and per-wire matrix manipulations. Closure under
link-product composition of combs is proved here in the monotone-suffix
form: `Comb.normalized_suffix_comp` carries the recursion as a budgeted
inductive, and `Comb.normalized_suffix_comp_final` is the consumer-facing
closure theorem.

The composition is built on `Comb.suffixMatch`: every wire of the inner
comb connects to one contiguous, order-preserving window of an outer comb
with at least two teeth. The index maps `Comb.compIn`/`Comb.compOut` and
`k + m + 1 ≤ n + 1` place this window within the outer comb. This is a
sufficient acyclic insertion topology, not a characterization of the source's
arbitrary acyclic joins of selected free wires in the network-composition
result [Chiribella2009Networks, comblong-pub.tex:1279-1286]; the preceding
acyclic-join condition is stated at comblong-pub.tex lines 1233-1243. It does
not supply serial composition of two one-tooth combs through one shared
wire or general matched-wire associativity. Finite link contractions are
algebraically defined even for cyclic connections; causal normalization is
what cannot be inferred for arbitrary cycles.

The suffix normalization and endpoint-channel theorems allow empty wires.
At an empty final output, the outer peel sum vanishes. If the last input is
inhabited, its tail witness vanishes; if that input is empty, the window
peel instead makes its witness vanish in each contraction term. The
probabilistic closure applies to both subnormalized factors via their
deterministic completions. General acyclic composition and its
associativity coherence remain outside this API.

The endpoint section closes the loop between the two readings of
composition: at `k = 0`, `m = n` the suffix-composition shared wires are
exactly the window's whole Choi space, so the entrywise link-product sum
collapses to the aggregate-wire `linkAction` sum
(`Comb.suffixComp_eq_linkAction`), and the general normalization closure
specializes to the statement that the link action is a channel
(`Comb.normalized_linkAction`). The transport chain is built from explicit
packaging equivalences (`Comb.endWinEquiv`, `Comb.endPackEquiv`,
`Comb.endChanEquiv`) so that every rewriting step stays at default
transparency on the heterogeneous wire families.
-/

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder

universe u v

noncomputable section

namespace QIT.HigherOrder

namespace Comb

/-! ## Family reindexing invariance -/

/-- Pointwise wire equivalences induce an equivalence of comb spaces. -/
def spaceEquiv {n : Nat} {I O I' O' : Fin n → Type u}
    (eI : ∀ j, I j ≃ I' j) (eO : ∀ j, O j ≃ O' j) :
    Space I O ≃ Space I' O' :=
  Equiv.prodCongr (Equiv.piCongrRight fun j => eI j) (Equiv.piCongrRight fun j => eO j)

@[simp] theorem spaceEquiv_apply {n : Nat} {I O I' O' : Fin n → Type u}
    (eI : ∀ j, I j ≃ I' j) (eO : ∀ j, O j ≃ O' j) (p : Space I O) :
    spaceEquiv eI eO p =
      ((Equiv.piCongrRight fun j => eI j) p.1, (Equiv.piCongrRight fun j => eO j) p.2) := rfl

@[simp] theorem spaceEquiv_symm_apply {n : Nat} {I O I' O' : Fin n → Type u}
    (eI : ∀ j, I j ≃ I' j) (eO : ∀ j, O j ≃ O' j) (p : Space I' O') :
    (spaceEquiv eI eO).symm p =
      ((Equiv.piCongrRight fun j => eI j).symm p.1,
        (Equiv.piCongrRight fun j => eO j).symm p.2) := rfl

/-- The inverse of a pointwise space equivalence is the pointwise inverse. -/
theorem spaceEquiv_symm {n : Nat} {I O I' O' : Fin n → Type u}
    (eI : ∀ j, I j ≃ I' j) (eO : ∀ j, O j ≃ O' j) :
    (spaceEquiv eI eO).symm =
      spaceEquiv (fun j => (eI j).symm) (fun j => (eO j).symm) := by
  apply Equiv.ext
  rintro ⟨i, o⟩
  simp [spaceEquiv, Equiv.prodCongr_symm, WireFam.piCongrRight_symm]

private theorem matReindex_spaceEquiv_cancel {n : Nat} {I O I' O' : Fin n → Type u}
    (eI : ∀ j, I j ≃ I' j) (eO : ∀ j, O j ≃ O' j) (J : CMatrix (Space I O)) :
    WireFam.matReindex (spaceEquiv (fun j => (eI j).symm) (fun j => (eO j).symm))
      (WireFam.matReindex (spaceEquiv eI eO) J) = J := by
  rw [← spaceEquiv_symm, WireFam.matReindex_symm_matReindex]

/-- A reindexed matrix, read back through the same reindexing, is the
original matrix. -/
private theorem submatrix_matReindex_self {ι κ : Type u} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : CMatrix ι) :
    (WireFam.matReindex e M).submatrix e e = M := by
  ext i j
  simp

/-- Pointwise wire equivalences act on truncated `Fin.snoc` shapes by
truncation, keeping the final wire separate. -/
private theorem piCongrRight_symm_snoc {n : Nat} {O O' : Fin (n + 1) → Type u}
    (eO : ∀ j, O j ≃ O' j) (y : ∀ j : Fin n, O' j.castSucc) (w : O' (Fin.last n)) :
    (Equiv.piCongrRight eO).symm (Fin.snoc y w) =
      Fin.snoc ((Equiv.piCongrRight fun j : Fin n => eO j.castSucc).symm y)
        ((eO (Fin.last n)).symm w) := by
  funext j
  cases j using Fin.lastCases with
  | last =>
    show (eO (Fin.last n)).symm (Fin.snoc y w (Fin.last n)) = _
    simp only [Fin.snoc_last]
  | cast j =>
    show (eO (Fin.castSucc j)).symm (Fin.snoc y w (Fin.castSucc j)) = _
    simp only [Fin.snoc_castSucc]
    rfl

/-- Transport of recursive normalization along pointwise wire equivalences,
forward direction. -/
private theorem Normalized.reindex_fwd {n : Nat} {I O I' O' : Fin n → Type u}
    [instI : ∀ j, Fintype (I j)] [instDI : ∀ j, DecidableEq (I j)]
    [instO : ∀ j, Fintype (O j)] [instDO : ∀ j, DecidableEq (O j)]
    [instI' : ∀ j, Fintype (I' j)] [instDI' : ∀ j, DecidableEq (I' j)]
    [instO' : ∀ j, Fintype (O' j)] [instDO' : ∀ j, DecidableEq (O' j)]
    (eI : ∀ j, I j ≃ I' j) (eO : ∀ j, O j ≃ O' j)
    (J : CMatrix (Space I O)) :
    Normalized I O J →
      Normalized I' O' (WireFam.matReindex (spaceEquiv eI eO) J) := by
  induction n with
  | zero =>
    intro h
    simp only [normalized_zero] at h
    rw [h]
    exact (normalized_zero I' O' _).mpr (WireFam.matReindex_one _)
  | succ n ih =>
    rintro ⟨hpsd, K, hK, heq⟩
    constructor
    · exact (WireFam.matReindex_posSemidef_iff (spaceEquiv eI eO) J).mpr hpsd
    · refine ⟨WireFam.matReindex (spaceEquiv (fun j => eI j.castSucc)
          (fun j => eO j.castSucc)) K, ?_, ?_⟩
      · exact @ih (fun j => I j.castSucc) (fun j => O j.castSucc)
          (fun j => I' j.castSucc) (fun j => O' j.castSucc)
          (fun j => instI j.castSucc) (fun j => instDI j.castSucc)
          (fun j => instO j.castSucc) (fun j => instDO j.castSucc)
          (fun j => instI' j.castSucc) (fun j => instDI' j.castSucc)
          (fun j => instO' j.castSucc) (fun j => instDO' j.castSucc)
          (fun j => eI j.castSucc) (fun j => eO j.castSucc) K hK
      · intro x x' y y'
        have hlast : ∀ v : ∀ j, I' j, (Equiv.piCongrRight fun j => eI j).symm v (Fin.last n)
            = (eI (Fin.last n)).symm (v (Fin.last n)) := fun _ => rfl
        have hup : ∀ v : ∀ j, I' j,
            (fun k : Fin n => (Equiv.piCongrRight fun j => eI j).symm v k.castSucc) =
              (Equiv.piCongrRight fun j : Fin n => eI j.castSucc).symm
                (fun k => v k.castSucc) := fun _ => funext fun _ => rfl
        have hsnoc : ∀ (x : ∀ j, I' j) (y : ∀ j : Fin n, O' j.castSucc) (w : O' (Fin.last n)),
            (spaceEquiv eI eO).symm (x, Fin.snoc y w) =
              ((Equiv.piCongrRight fun j => eI j).symm x,
                Fin.snoc ((Equiv.piCongrRight fun j : Fin n => eO j.castSucc).symm y)
                  ((eO (Fin.last n)).symm w)) := by
          intro x y w
          simp only [spaceEquiv_symm_apply, piCongrRight_symm_snoc]
        have hsum : ∑ w : O' (Fin.last n),
            WireFam.matReindex (spaceEquiv eI eO) J (x, Fin.snoc y w) (x', Fin.snoc y' w)
              = ∑ z : O (Fin.last n), J ((Equiv.piCongrRight fun j => eI j).symm x,
                  Fin.snoc ((Equiv.piCongrRight fun j : Fin n => eO j.castSucc).symm y) z)
                ((Equiv.piCongrRight fun j => eI j).symm x',
                  Fin.snoc ((Equiv.piCongrRight fun j : Fin n => eO j.castSucc).symm y') z) := by
          rw [Fintype.sum_equiv ((eO (Fin.last n)).symm)
            (fun w => WireFam.matReindex (spaceEquiv eI eO) J (x, Fin.snoc y w)
              (x', Fin.snoc y' w))
            (fun z => J ((Equiv.piCongrRight fun j => eI j).symm x,
                Fin.snoc ((Equiv.piCongrRight fun j : Fin n => eO j.castSucc).symm y) z)
              ((Equiv.piCongrRight fun j => eI j).symm x',
                Fin.snoc ((Equiv.piCongrRight fun j : Fin n => eO j.castSucc).symm y') z))
            (fun w => by
              simp only [WireFam.matReindex_apply]
              rw [hsnoc x y w, hsnoc x' y' w])]
        rw [hsum, heq]
        by_cases hx : x (Fin.last n) = x' (Fin.last n)
        · have hh : (Equiv.piCongrRight fun j => eI j).symm x (Fin.last n) =
                (Equiv.piCongrRight fun j => eI j).symm x' (Fin.last n) := by
            rw [hlast x, hlast x']
            exact congrArg _ hx
          rw [ite_eq_left hh, ite_eq_left hx, hup x, hup x']
          simp only [WireFam.matReindex_apply, spaceEquiv_symm_apply]
        · have hh : ¬((Equiv.piCongrRight fun j => eI j).symm x (Fin.last n) =
                (Equiv.piCongrRight fun j => eI j).symm x' (Fin.last n)) := by
            rw [hlast x, hlast x']
            intro h
            exact hx ((eI (Fin.last n)).symm.injective h)
          rw [ite_eq_right hh, ite_eq_right hx]

/-- Recursive normalization transports along pointwise wire equivalences:
the condition depends only on the wire content, not on the carrier types. -/
theorem Normalized.reindex_iff {n : Nat} {I O I' O' : Fin n → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, Fintype (I' j)] [∀ j, DecidableEq (I' j)]
    [∀ j, Fintype (O' j)] [∀ j, DecidableEq (O' j)]
    (eI : ∀ j, I j ≃ I' j) (eO : ∀ j, O j ≃ O' j)
    (J : CMatrix (Space I O)) :
    Normalized I O J ↔
      Normalized I' O' (WireFam.matReindex (spaceEquiv eI eO) J) :=
  ⟨Normalized.reindex_fwd eI eO J, fun h =>
    matReindex_spaceEquiv_cancel eI eO J ▸
      Normalized.reindex_fwd (fun j => (eI j).symm) (fun j => (eO j).symm)
        (WireFam.matReindex (spaceEquiv eI eO) J) h⟩

/-! ## Boundary spectator absorption -/

/-- The `PUnit` spectator wedge at the last output boundary is invisible:
pointwise, the wedged wire is equivalent to the bare wire. -/
private def punitWedgeEquiv {m : Nat} (A : Fin (m + 1) → Type u) (j : Fin (m + 1)) :
    boundaryOutput A PUnit j ≃ A j := by
  cases j using Fin.lastCases with
  | last =>
    show boundaryOutput A PUnit (Fin.last m) ≃ A (Fin.last m)
    have h : boundaryOutput A PUnit (Fin.last m) = (A (Fin.last m) × PUnit.{u + 1}) := by
      simp [boundaryOutput]
    exact (Equiv.cast h).trans (Equiv.prodPUnit (A (Fin.last m)))
  | cast k =>
    show boundaryOutput A PUnit (Fin.castSucc k) ≃ A (Fin.castSucc k)
    have h : boundaryOutput A PUnit (Fin.castSucc k) = A (Fin.castSucc k) := by
      simp [boundaryOutput]
    exact Equiv.cast h

/-- A `PUnit` output spectator does not affect recursive normalization. -/
private theorem Normalized.punit_wedge_iff {m : Nat} {I A : Fin (m + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    [∀ j, Fintype (boundaryOutput A PUnit j)] [∀ j, DecidableEq (boundaryOutput A PUnit j)]
    (X : CMatrix (Space I (boundaryOutput A PUnit))) :
    Normalized I (boundaryOutput A PUnit) X ↔
      Normalized I A (WireFam.matReindex
        (spaceEquiv (fun j => Equiv.refl (I j)) (punitWedgeEquiv A)) X) :=
  Normalized.reindex_iff _ _ X

/-! ## Boundary equivalence computation rules -/

/-- The first-boundary equivalence splits off the spectator from the first
input wire, keeping the remaining wires in order. -/
private theorem boundaryInputEquiv_apply {m : Nat} (I : Fin (m + 1) → Type u) (r : Type u)
    (i : ∀ j, boundaryInput I r j) :
    boundaryInputEquiv I r i = (Fin.cons (i 0).1 (fun j => i j.succ), (i 0).2) := rfl

/- The last-boundary equivalence `boundaryOutputEquiv` is not pointwise
computable (the wedge type at the last output index does not reduce to a
product definitionally), so output-side facts below are transported through
`Fintype.sum_equiv` along `boundaryOutputEquiv` itself instead of through a
computation rule. -/

section ActionEntrywise
variable {n : Nat} (I O : Fin (n + 2) → Type u)
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- Entrywise form of the ancillary extension of the insertion action: each
entry is the contraction of the inner operator with the outer comb along all
inner wires, exactly the Choi form of the source's inserted network. -/
private theorem actionMap_ext_apply (J : CMatrix (Space I O))
    (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s)))
    (p q : (I 0 × r) × (O (Fin.last (n + 1)) × s)) :
    ancillaryExtension (actionMap I O J) Y p q =
      ∑ z : Space (innerInput O) (innerOutput I),
        ∑ z' : Space (innerInput O) (innerOutput I),
          Y ((z.1, p.1.2), (z.2, p.2.2)) ((z'.1, q.1.2), (z'.2, q.2.2)) *
            J (Fin.cons p.1.1 z.2, Fin.snoc z.1 p.2.1)
              (Fin.cons q.1.1 z'.2, Fin.snoc z'.1 q.2.1) := by
  show (∑ z : Space (innerInput O) (innerOutput I),
        ∑ z' : Space (innerInput O) (innerOutput I),
          Y ((z.1, p.1.2), (z.2, p.2.2)) ((z'.1, q.1.2), (z'.2, q.2.2)) *
            WireFam.matReindex (actionEquiv I O) J
              (z, (p.1.1, p.2.1)) (z', (q.1.1, q.2.1))) = _
  rfl

end ActionEntrywise

/-! ## Trace preservation under insertion -/

section InsertionTrace
variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- Entrywise channel property of a jointly normalized inner comb at the
bottom tooth: the submatrix definition of `ExtendedNormalized` is read
through round trips along the boundary equivalences, so no pointwise
computation rule for `boundaryOutputEquiv` is needed. -/
private theorem extended_channel_one {I O : Fin 2 → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s)))
    (hY : ExtendedNormalized (innerInput O) (innerOutput I) r s Y) :
    ∀ a a' : (∀ j, innerInput O j) × r,
      ∑ b : (∀ j, innerOutput I j) × s, Y (a, b) (a', b) =
        if a = a' then 1 else 0 := by
  obtain ⟨_, htr⟩ := (normalized_one_iff _).mp hY
  intro a a'
  have hentry : ∀ u u' : ∀ j, boundaryInput (innerInput O) r j,
      ∑ w : ∀ j, boundaryOutput (innerOutput I) s j,
        Y (boundaryEquiv (innerInput O) (innerOutput I) r s (u, w))
          (boundaryEquiv (innerInput O) (innerOutput I) r s (u', w)) =
        if u = u' then 1 else 0 := by
    intro u u'
    have h := congrFun (congrFun htr u) u'
    simpa only [partialTraceB, Matrix.one_apply, Matrix.submatrix,
      Matrix.of_apply] using h
  have h2 := hentry ((boundaryInputEquiv (innerInput O) r).symm a)
    ((boundaryInputEquiv (innerInput O) r).symm a')
  simp only [boundaryEquiv, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.apply_symm_apply] at h2
  rw [Fintype.sum_equiv (boundaryOutputEquiv (innerOutput I) s)
    (fun w => Y (a, boundaryOutputEquiv (innerOutput I) s w)
      (a', boundaryOutputEquiv (innerOutput I) s w))
    (fun b => Y (a, b) (a', b))
    (fun _ => rfl)] at h2
  by_cases hab : a = a'
  · rw [ite_eq_left hab]
    rw [ite_eq_left (congrArg ((boundaryInputEquiv (innerInput O) r).symm) hab)] at h2
    exact h2
  · rw [ite_eq_right hab]
    rw [ite_eq_right (fun h => hab ((boundaryInputEquiv (innerInput O) r).symm.injective h))]
      at h2
    exact h2

/-- Entrywise channel form of one-tooth normalization. -/
private theorem normalized_one_channel {A B : Fin 1 → Type u}
    [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    {K : CMatrix (Space A B)} (hK : Normalized A B K) :
    ∀ a a' : ∀ j, A j,
      ∑ ov : ∀ j, B j, K (a, ov) (a', ov) = if a = a' then 1 else 0 := by
  obtain ⟨_, htr⟩ := (normalized_one_iff _).mp hK
  intro a a'
  have h := congrFun (congrFun htr a) a'
  simpa only [partialTraceB, Matrix.one_apply, Matrix.of_apply] using h

/-- Single-wire tuples are determined by their value at the last index. -/
private theorem fin1_tuple_ext {β : Fin 1 → Type u} (t t' : ∀ j, β j) :
    t = t' ↔ t (Fin.last 0) = t' (Fin.last 0) := by
  constructor
  · rintro rfl; rfl
  · intro h
    funext j
    have hj : j = Fin.last 0 := Subsingleton.elim _ _
    rw [hj]
    exact h

/-- An input prefix tuple extended by `Fin.cons` is read at the second wire
through the tail alone, and truncated by `castSucc` through the head alone. -/
private theorem cons_last_one {α : Fin 2 → Type u} (i₀ : α 0) (t : ∀ j : Fin 1, α j.succ) :
    (Fin.cons i₀ t) (Fin.last 1) = t (Fin.last 0) := rfl

/-- The constant first-wire tuple: every index of the truncated family
`fun j : Fin 1 => α j.castSucc` is the zeroth wire, so the head value alone
inhabits it. -/
private def fin1Head {α : Fin 2 → Type u} (i₀ : α 0) : ∀ j : Fin 1, α j.castSucc :=
  fun j => Fin.cases i₀ (fun k => absurd k.isLt (by omega)) j

private theorem cons_castSucc_eq_head {α : Fin 2 → Type u} (i₀ : α 0)
    (t : ∀ j : Fin 1, α j.succ) :
    (fun j : Fin 1 => (Fin.cons i₀ t) j.castSucc) = fin1Head i₀ := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rfl

/-- The truncated-tuple constructor is injective in its head value. -/
private theorem fin1Head_eq_iff {α : Fin 2 → Type u} (i₀ i₀' : α 0) :
    fin1Head i₀ = fin1Head i₀' ↔ i₀ = i₀' := by
  constructor
  · intro h
    exact congrFun h (0 : Fin 1)
  · rintro rfl
    rfl

/-- Base case of the insertion trace induction: at two wires, the entrywise
chain is the three-channel contraction of the source recursion, with the
outer comb's peeled tooth consumed first, then the inner comb's channel
property, then the peeled tooth's channel property. -/
private theorem action_extension_trace_zero {I O : Fin 2 → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (J : CMatrix (Space I O)) (hJ : Normalized I O J)
    (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s)))
    (hY : ExtendedNormalized (innerInput O) (innerOutput I) r s Y) :
    partialTraceB (ancillaryExtension (actionMap I O J) Y) = 1 := by
  obtain ⟨_, K, hK, heq⟩ := hJ
  have hKch := normalized_one_channel hK
  have hYch := extended_channel_one Y hY
  classical
  ext x x'
  rcases x with ⟨i₀, ρ⟩
  rcases x' with ⟨i₀', ρ'⟩
  simp only [partialTraceB, actionMap_ext_apply, Matrix.one_apply, Prod.mk.injEq]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_comm]
  -- Stage 1: bring the traced last output wire innermost, then consume the
  -- outer comb's peeled tooth via the recursion witness `heq`.
  have hstage1 : (∑ σ : s, ∑ ω : O (Fin.last 1),
      ∑ z : Space (innerInput O) (innerOutput I),
        ∑ z' : Space (innerInput O) (innerOutput I),
          Y ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ)) *
            J (Fin.cons i₀ z.2, Fin.snoc z.1 ω) (Fin.cons i₀' z'.2, Fin.snoc z'.1 ω)) =
    (∑ σ : s, ∑ z : Space (innerInput O) (innerOutput I),
      ∑ z' : Space (innerInput O) (innerOutput I),
        if z.2 (Fin.last 0) = z'.2 (Fin.last 0) then
          Y ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ)) *
            K (fin1Head i₀, z.1) (fin1Head i₀', z'.1) else 0) := by
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [← Finset.mul_sum, heq (Fin.cons i₀ z.2) (Fin.cons i₀' z'.2) z.1 z'.1,
      cons_last_one, cons_last_one, cons_castSucc_eq_head, cons_castSucc_eq_head,
      mul_ite, mul_zero]
  rw [hstage1]
  -- Stage 2: collapse the fiber of the traced inner-output wire: the tooth
  -- condition pins the whole single-wire tuple, not just its last entry.
  have hstage2 : (∑ σ : s, ∑ z : Space (innerInput O) (innerOutput I),
      ∑ z' : Space (innerInput O) (innerOutput I),
        if z.2 (Fin.last 0) = z'.2 (Fin.last 0) then
          Y ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ)) *
            K (fin1Head i₀, z.1) (fin1Head i₀', z'.1) else 0) =
    (∑ σ : s, ∑ z : Space (innerInput O) (innerOutput I),
      ∑ β' : ∀ j, innerInput O j,
        Y ((z.1, ρ), (z.2, σ)) ((β', ρ'), (z.2, σ)) *
          K (fin1Head i₀, z.1) (fin1Head i₀', β')) := by
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.sum_prod_type]
    dsimp only
    refine Finset.sum_congr rfl fun β' _ => ?_
    have hconv : ∀ γ' : ∀ j, innerOutput I j,
        (if z.2 (Fin.last 0) = γ' (Fin.last 0) then
          Y ((z.1, ρ), (z.2, σ)) ((β', ρ'), (γ', σ)) *
            K (fin1Head i₀, z.1) (fin1Head i₀', β') else 0) =
        (if γ' = z.2 then
          Y ((z.1, ρ), (z.2, σ)) ((β', ρ'), (γ', σ)) *
            K (fin1Head i₀, z.1) (fin1Head i₀', β') else 0) := by
      intro γ'
      by_cases h : z.2 (Fin.last 0) = γ' (Fin.last 0)
      · rw [ite_eq_left h, ite_eq_left ((fin1_tuple_ext _ _).mpr h).symm]
      · rw [ite_eq_right h,
          ite_eq_right fun hh => h ((fin1_tuple_ext _ _).mp hh.symm)]
    rw [Finset.sum_congr rfl (fun γ' _ => hconv γ'), Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _)]
  rw [hstage2]
  -- Stage 3: unpack the paired inner wire and reorder so that the two wires
  -- contracted by the inner comb's channel property are innermost.
  have hstage3 : (∑ σ : s, ∑ z : Space (innerInput O) (innerOutput I),
      ∑ β' : ∀ j, innerInput O j,
        Y ((z.1, ρ), (z.2, σ)) ((β', ρ'), (z.2, σ)) *
          K (fin1Head i₀, z.1) (fin1Head i₀', β')) =
    (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
      ∑ z2 : ∀ j, innerOutput I j, ∑ σ : s,
        Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
          K (fin1Head i₀, z1) (fin1Head i₀', β')) := by
    have hA : (∑ σ : s, ∑ z : Space (innerInput O) (innerOutput I),
        ∑ β' : ∀ j, innerInput O j,
          Y ((z.1, ρ), (z.2, σ)) ((β', ρ'), (z.2, σ)) *
            K (fin1Head i₀, z.1) (fin1Head i₀', β')) =
      (∑ σ : s, ∑ z1 : ∀ j, innerInput O j, ∑ z2 : ∀ j, innerOutput I j,
        ∑ β' : ∀ j, innerInput O j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) :=
      Finset.sum_congr rfl fun σ _ => by
        rw [Fintype.sum_prod_type]
    have hB : (∑ σ : s, ∑ z1 : ∀ j, innerInput O j, ∑ z2 : ∀ j, innerOutput I j,
        ∑ β' : ∀ j, innerInput O j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) =
      (∑ σ : s, ∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
        ∑ z2 : ∀ j, innerOutput I j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) :=
      Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    have hC : (∑ σ : s, ∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
        ∑ z2 : ∀ j, innerOutput I j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) =
      (∑ z1 : ∀ j, innerInput O j, ∑ σ : s, ∑ β' : ∀ j, innerInput O j,
        ∑ z2 : ∀ j, innerOutput I j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) := Finset.sum_comm
    have hD : (∑ z1 : ∀ j, innerInput O j, ∑ σ : s, ∑ β' : ∀ j, innerInput O j,
        ∑ z2 : ∀ j, innerOutput I j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) =
      (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j, ∑ σ : s,
        ∑ z2 : ∀ j, innerOutput I j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    have hE : (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j, ∑ σ : s,
        ∑ z2 : ∀ j, innerOutput I j,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) =
      (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
        ∑ z2 : ∀ j, innerOutput I j, ∑ σ : s,
          Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
            K (fin1Head i₀, z1) (fin1Head i₀', β')) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hA, hB, hC, hD, hE]
  rw [hstage3]
  -- Stage 4: the peeled tooth factor no longer depends on the two innermost
  -- wires, so those are contracted by the inner comb's channel property.
  have hstage4 : (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
      ∑ z2 : ∀ j, innerOutput I j, ∑ σ : s,
        Y ((z1, ρ), (z2, σ)) ((β', ρ'), (z2, σ)) *
          K (fin1Head i₀, z1) (fin1Head i₀', β')) =
    (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
      (if (z1, ρ) = (β', ρ') then 1 else 0) *
        K (fin1Head i₀, z1) (fin1Head i₀', β')) := by
    refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun β' _ => ?_
    simp only [← Finset.sum_mul]
    rw [← Fintype.sum_prod_type
        (fun p : (∀ j, innerOutput I j) × s => Y ((z1, ρ), p) ((β', ρ'), p)),
      hYch (z1, ρ) (β', ρ')]
  rw [hstage4]
  -- Stage 5: final assembly.  The spectator condition splits first; on it,
  -- the β'-fiber collapses to the diagonal, and the remaining contraction is
  -- exactly the peeled tooth's own channel property.
  by_cases hρ : ρ = ρ'
  · rw [hρ]
    have h5a : (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
        (if (z1, ρ') = (β', ρ') then 1 else 0) *
          K (fin1Head i₀, z1) (fin1Head i₀', β')) =
      (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
        if z1 = β' then K (fin1Head i₀, z1) (fin1Head i₀', β') else 0) := by
      refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun β' _ => ?_
      by_cases hz : z1 = β'
      · rw [ite_eq_left (by rw [hz]), ite_eq_left hz, one_mul]
      · rw [ite_eq_right (fun hh => hz (congrArg Prod.fst hh)), ite_eq_right hz,
          zero_mul]
    rw [h5a]
    have h5b : (∑ z1 : ∀ j, innerInput O j, ∑ β' : ∀ j, innerInput O j,
        if z1 = β' then K (fin1Head i₀, z1) (fin1Head i₀', β') else 0) =
      (∑ z1 : ∀ j, innerInput O j,
        K (fin1Head i₀, z1) (fin1Head i₀', z1)) :=
      Finset.sum_congr rfl fun z1 _ => by
        rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    rw [h5b, hKch (fin1Head i₀) (fin1Head i₀')]
    simp only [fin1Head_eq_iff, and_true]
  · have h5z : ∀ z1 : ∀ j, innerInput O j, ∀ β' : ∀ j, innerInput O j,
        ((if (z1, ρ) = (β', ρ') then 1 else 0) *
          K (fin1Head i₀, z1) (fin1Head i₀', β')) = 0 := by
      intro z1 β'
      rw [ite_eq_right (fun hh => hρ (congrArg Prod.snd hh)), zero_mul]
    simp only [h5z, Finset.sum_const_zero]
    rw [ite_eq_right (fun h => hρ h.2)]

/-- The positivity of a jointly normalized inner comb is already carried by
the boundary submatrix. -/
private theorem extendedNormalized_posSemidef {n : Nat}
    {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    {Y : CMatrix (((∀ j, I j) × r) × ((∀ j, O j) × s))}
    (hY : ExtendedNormalized I O r s Y) : Y.PosSemidef :=
  (Matrix.posSemidef_submatrix_equiv
    (boundaryEquiv I O r s)).mp hY.1

/-- Splitting a tuple sum at the last wire. -/
private theorem sum_pi_snoc {m : Nat} {α : Fin (m + 1) → Type u}
    [∀ j, Fintype (α j)] [∀ j, DecidableEq (α j)]
    {β : Type v} [AddCommMonoid β] (F : (∀ j, α j) → β) :
    (∑ x : ∀ j, α j, F x) =
      (∑ y : ∀ j : Fin m, α j.castSucc, ∑ w : α (Fin.last m), F (Fin.snoc y w)) := by
  have hround : ∀ x : ∀ j, α j,
      Fin.snoc (fun j : Fin m => x j.castSucc) (x (Fin.last m)) = x := by
    intro x
    funext j
    cases j using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast k => simp [Fin.snoc_castSucc]
  rw [Fintype.sum_equiv (Fin.snocEquiv α).symm
    (fun x => F x)
    (fun p => F (Fin.snoc p.2 p.1))
    (fun x => by
      rw [show ((Fin.snocEquiv α).symm x) =
        (x (Fin.last m), fun j : Fin m => x j.castSucc) from rfl, hround x])]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- A `PUnit`-indexed sum collapses to the value at the unit. -/
private theorem sum_punit_eq {M : Type _} [AddCommMonoid M] (h : PUnit → M) :
    (∑ u : PUnit, h u) = h PUnit.unit := by
  refine Finset.sum_eq_single PUnit.unit ?_ ?_
  · intro u _ hu
    exact absurd (Subsingleton.elim u PUnit.unit) hu
  · intro hu
    exact absurd (Finset.mem_univ _) hu

/-- The nonfinal output boundary wires are the inner-output wires. -/
private theorem boundaryOutput_castSucc_eq {m : Nat} {B : Fin (m + 1) → Type u}
    {s : Type u} (j : Fin m) :
    boundaryOutput B s j.castSucc = B j.castSucc := by
  simp [boundaryOutput]

section SuccTooth
variable {n : Nat} {I O : Fin (n + 3) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- Generating rule for the last output boundary equivalence on `Fin.snoc`
shapes: the snoc tail is read through the nonfinal wire casts and the head
pair through the wedge cast. -/
private theorem bOE_snoc {m : Nat} {B : Fin (m + 1) → Type u}
    [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    {s : Type u} [Fintype s] [DecidableEq s]
    (t : ∀ j : Fin m, B j.castSucc) (γ : B (Fin.last m)) (σ : s) :
    boundaryOutputEquiv B s (Fin.snoc
      (fun j : Fin m =>
        Equiv.cast ((show boundaryOutput B s j.castSucc = B j.castSucc by
          simp [boundaryOutput]).symm) (t j))
      (Equiv.cast (show boundaryOutput B s (Fin.last m) = (B (Fin.last m) × s) by
        simp [boundaryOutput]).symm (γ, σ))) = (Fin.snoc t γ, σ) := by
  have hcore : (Equiv.piCongrRight fun j : Fin m =>
      Equiv.cast (show boundaryOutput B s j.castSucc = B j.castSucc by
        simp [boundaryOutput]))
      (fun j => cast ((show boundaryOutput B s j.castSucc = B j.castSucc by
        simp [boundaryOutput]).symm) (t j)) = t := by
    funext j
    simp
  simp [boundaryOutputEquiv]
  rw [hcore]
  rfl

/-- The `PUnit` spectator wedge absorbs the last-boundary equivalence: reading
the inverse image of a bare output tuple with a unit spectator through the
wedge projection returns the tuple itself. -/
private theorem punitWedgeEquiv_boundaryOutputEquiv_symm {m : Nat} {B : Fin (m + 1) → Type u}
    [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)] (y : ∀ j, B j) :
    (Equiv.piCongrRight (punitWedgeEquiv B)
      ((boundaryOutputEquiv B PUnit).symm (y, ⟨⟩))) = y := by
  have hw : boundaryOutput B PUnit (Fin.last m) = (B (Fin.last m) × PUnit) := by
    simp [boundaryOutput]
  have hround : Fin.snoc (fun j : Fin m => y j.castSucc) (y (Fin.last m)) = y := by
    funext j
    cases j using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast j => simp [Fin.snoc_castSucc]
  have hsymm : (boundaryOutputEquiv B PUnit).symm (y, ⟨⟩) =
      Fin.snoc (fun j : Fin m =>
        Equiv.cast ((boundaryOutput_castSucc_eq (B := B) (s := PUnit) j).symm) (y j.castSucc))
        (Equiv.cast hw.symm (y (Fin.last m), ⟨⟩)) := by
    rw [Equiv.symm_apply_eq, bOE_snoc, hround]
  rw [hsymm]
  funext j
  cases j using Fin.lastCases with
  | last =>
    simp only [Equiv.piCongrRight_apply]
    simp [punitWedgeEquiv]
  | cast j =>
    simp only [Equiv.piCongrRight_apply]
    simp [punitWedgeEquiv]

/-- Pointwise identification of the castSucc-truncated first boundary family
with the first boundary family of the castSucc-restricted comb: built by
`Fin.cases` as the identity at every index, so it reduces at both
constructors. -/
private def famEquiv (r : Type u) (j : Fin (n + 1)) :
    boundaryInput (innerInput O) r j.castSucc
      ≃ boundaryInput (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r j :=
  Fin.cases (Equiv.refl _) (fun _ => Equiv.refl _) j

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Input-side bridge: reading the inverse image of an input pair through the
outer boundary equivalence, truncated at `castSucc`, agrees with reading it
through the restricted comb's boundary equivalence and transporting by
`famEquiv`. -/
private theorem bIE_castSucc_brid {r : Type u} [Fintype r] [DecidableEq r]
    (a : ∀ j, innerInput O j) (ρ : r) :
    (fun j : Fin (n + 1) => (boundaryInputEquiv (innerInput O) r).symm (a, ρ) j.castSucc)
      = (Equiv.piCongrRight (famEquiv (O := O) r)).symm
          ((boundaryInputEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r).symm
            ((fun j : Fin (n + 1) => a j.castSucc, ρ))) := by
  have hSfull : (boundaryInputEquiv (innerInput O) r).symm (a, ρ)
      = (Fin.cons (a 0, ρ) (fun j : Fin (n + 1) => a j.succ) :
          ∀ j : Fin (n + 2), boundaryInput (innerInput O) r j) := by
    rw [Equiv.symm_apply_eq, boundaryInputEquiv_apply]
    simp only [Prod.mk.injEq]
    exact ⟨(Fin.cons_self_tail a).symm, rfl⟩
  have hTfull : (boundaryInputEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r).symm
        ((fun j : Fin (n + 1) => a j.castSucc, ρ))
      = (Fin.cons (((fun j : Fin (n + 1) => a j.castSucc) 0), ρ)
          (fun j : Fin n => (fun j : Fin (n + 1) => a j.castSucc) j.succ) :
          ∀ j : Fin (n + 1), boundaryInput
            (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r j) := by
    rw [Equiv.symm_apply_eq, boundaryInputEquiv_apply]
    simp only [Prod.mk.injEq]
    exact ⟨(Fin.cons_self_tail (fun j : Fin (n + 1) => a j.castSucc)).symm, rfl⟩
  funext j
  cases j using Fin.cases with
  | zero =>
    show (boundaryInputEquiv (innerInput O) r).symm (a, ρ) 0
        = (boundaryInputEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r).symm
            ((fun j : Fin (n + 1) => a j.castSucc, ρ)) 0
    rw [hSfull, hTfull]
    rfl
  | succ k =>
    show (boundaryInputEquiv (innerInput O) r).symm (a, ρ) ((k : Fin n).succ).castSucc
        = (boundaryInputEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r).symm
            ((fun j : Fin (n + 1) => a j.castSucc, ρ)) k.succ
    simp only [Fin.castSucc_succ]
    rw [hSfull, hTfull]
    rfl

/-- The output-side family transport is the identity: the truncated
inner-output family and the restricted comb's inner-output family are
pointwise definitionally equal. -/
private theorem piCongrRight_refl_symm_id {I : Fin (n + 3) → Type u}
    (b : ∀ j : Fin (n + 1), innerOutput I j.castSucc) :
    (Equiv.piCongrRight (fun j : Fin (n + 1) =>
        (Equiv.refl (innerOutput I j.castSucc) :
          innerOutput I j.castSucc ≃
            innerOutput (fun k : Fin (n + 2) => I k.castSucc) j))).symm b = b := by
  funext j
  rfl

/-- Entrywise tooth of the extended recursion, read through the boundary
equivalences: the inner comb's own recursion witness is returned with the
output-side wedge wires uncurried, so the peeled last extended output wire
(the inner-output wedge with the spectator) is evaluated joint-first. -/
private theorem extended_succ_tooth
    {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    {Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))}
    (hY : ExtendedNormalized (innerInput O) (innerOutput I) r s Y) :
    ∃ (Y' : CMatrix (Space (fun j : Fin (n + 1) => boundaryInput (innerInput O) r j.castSucc)
        (fun j : Fin (n + 1) => innerOutput I j.castSucc))),
      Normalized (fun j : Fin (n + 1) => boundaryInput (innerInput O) r j.castSucc)
        (fun j : Fin (n + 1) => innerOutput I j.castSucc) Y' ∧
      ∀ (a : ∀ j, innerInput O j) (ρ : r) (a' : ∀ j, innerInput O j) (ρ' : r)
        (b b' : ∀ j : Fin (n + 1), innerOutput I j.castSucc),
        (∑ p : I (Fin.last (n + 2)) × s,
          Y ((a, ρ), (Fin.snoc b p.1, p.2)) ((a', ρ'), (Fin.snoc b' p.1, p.2))) =
        (if a (Fin.last (n + 1)) = a' (Fin.last (n + 1)) then
          Y' ((fun j : Fin (n + 1) =>
                (boundaryInputEquiv (innerInput O) r).symm (a, ρ) j.castSucc), b)
            ((fun j : Fin (n + 1) =>
                (boundaryInputEquiv (innerInput O) r).symm (a', ρ') j.castSucc), b')
        else 0) := by
  obtain ⟨_, Y_K, hY_K, hY_eq⟩ := hY
  have hOutw : ∀ j : Fin (n + 1),
      boundaryOutput (innerOutput I) s j.castSucc = innerOutput I j.castSucc :=
    fun j => boundaryOutput_castSucc_eq j
  refine ⟨WireFam.matReindex (spaceEquiv (fun j : Fin (n + 1) => Equiv.refl _)
      (fun j : Fin (n + 1) => Equiv.cast (hOutw j))) Y_K,
    Normalized.reindex_fwd _ _ Y_K hY_K, ?_⟩
  intro a ρ a' ρ' b b'
  set u : ∀ j, boundaryInput (innerInput O) r j :=
    (boundaryInputEquiv (innerInput O) r).symm (a, ρ) with hu_def
  set u' : ∀ j, boundaryInput (innerInput O) r j :=
    (boundaryInputEquiv (innerInput O) r).symm (a', ρ') with hu'_def
  have huimg : boundaryInputEquiv (innerInput O) r u = (a, ρ) :=
    Equiv.apply_symm_apply _ _
  have hu'img : boundaryInputEquiv (innerInput O) r u' = (a', ρ') :=
    Equiv.apply_symm_apply _ _
  have hlast : u (Fin.last (n + 1)) = a (Fin.last (n + 1)) := by
    rw [show u (Fin.last (n + 1)) =
        ((boundaryInputEquiv (innerInput O) r) u).1 (Fin.last (n + 1)) from rfl, huimg]
  have hlast' : u' (Fin.last (n + 1)) = a' (Fin.last (n + 1)) := by
    rw [show u' (Fin.last (n + 1)) =
        ((boundaryInputEquiv (innerInput O) r) u').1 (Fin.last (n + 1)) from rfl, hu'img]
  have hw : boundaryOutput (innerOutput I) s (Fin.last (n + 1))
      = (I (Fin.last (n + 2)) × s) :=
    (show boundaryOutput (innerOutput I) s (Fin.last (n + 1))
        = (innerOutput I (Fin.last (n + 1)) × s) by simp [boundaryOutput]).trans
      (by rfl)
  have hwedge : ∀ (bb : ∀ j : Fin (n + 1), innerOutput I j.castSucc)
      (p : I (Fin.last (n + 2)) × s),
      boundaryOutputEquiv (innerOutput I) s
        (Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (bb j))
          (Equiv.cast hw.symm p)) = (Fin.snoc bb p.1, p.2) := by
    intro bb p
    have h1 : (Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (bb j))
        (Equiv.cast hw.symm p)) =
      (Fin.snoc (fun j : Fin (n + 1) =>
          Equiv.cast ((show boundaryOutput (innerOutput I) s j.castSucc
              = innerOutput I j.castSucc by simp [boundaryOutput]).symm) (bb j))
        (Equiv.cast (show boundaryOutput (innerOutput I) s (Fin.last (n + 1))
            = (innerOutput I (Fin.last (n + 1)) × s) by simp [boundaryOutput]).symm
          (p.1, p.2))) := rfl
    rw [h1]
    exact bOE_snoc bb p.1 p.2
  have hpt : ∀ p : I (Fin.last (n + 2)) × s,
      Y ((a, ρ), (Fin.snoc b p.1, p.2)) ((a', ρ'), (Fin.snoc b' p.1, p.2)) =
      (Y.submatrix (boundaryEquiv (innerInput O) (innerOutput I) r s)
        (boundaryEquiv (innerInput O) (innerOutput I) r s))
        (u, Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b j))
          (Equiv.cast hw.symm p))
        (u', Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b' j))
          (Equiv.cast hw.symm p)) := by
    intro p
    show Y ((a, ρ), (Fin.snoc b p.1, p.2)) ((a', ρ'), (Fin.snoc b' p.1, p.2)) =
      Y (boundaryEquiv (innerInput O) (innerOutput I) r s
          (u, Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b j))
            (Equiv.cast hw.symm p)))
        (boundaryEquiv (innerInput O) (innerOutput I) r s
          (u', Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b' j))
            (Equiv.cast hw.symm p)))
    simp only [boundaryEquiv, Equiv.prodCongr_apply, Prod.map_apply, huimg, hu'img]
    rw [hwedge b p, hwedge b' p]
  have key := hY_eq u u'
    (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b j))
    (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b' j))
  rw [Fintype.sum_equiv (Equiv.cast hw.symm)
    (fun p => Y ((a, ρ), (Fin.snoc b p.1, p.2)) ((a', ρ'), (Fin.snoc b' p.1, p.2)))
    (fun z => (Y.submatrix (boundaryEquiv (innerInput O) (innerOutput I) r s)
        (boundaryEquiv (innerInput O) (innerOutput I) r s))
      (u, Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b j)) z)
      (u', Fin.snoc (fun j : Fin (n + 1) => Equiv.cast (hOutw j).symm (b' j)) z))
    hpt]
  rw [hlast, hlast'] at key
  rw [key]
  split
  · next h =>
    have h' : a (Fin.last (n + 1)) = a' (Fin.last (n + 1)) := h
    rw [ite_eq_left h']
    simp only [WireFam.matReindex_apply, spaceEquiv_symm_apply]
    congr 1
  · next h =>
    have h' : ¬(a (Fin.last (n + 1)) = a' (Fin.last (n + 1))) := h
    rw [ite_eq_right h']

/-- The tooth witness transported to the restricted comb's extended shape:
peeling the last tooth of a jointly normalized extended comb yields a
genuinely extended normalized matrix for the castSucc-restricted comb, with
a `PUnit` output spectator, whose unit-spectator entries are the witness's
entries read through the boundary equivalences. -/
private theorem extended_succ_tooth_restricted
    {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    {Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))}
    (hY : ExtendedNormalized (innerInput O) (innerOutput I) r s Y) :
    ∃ Yr : CMatrix (((∀ j : Fin (n + 1), innerInput (fun k : Fin (n + 2) => O k.castSucc) j) × r) ×
        ((∀ j : Fin (n + 1), innerOutput (fun k : Fin (n + 2) => I k.castSucc) j) × PUnit)),
      ExtendedNormalized (innerInput (fun k : Fin (n + 2) => O k.castSucc))
        (innerOutput (fun k : Fin (n + 2) => I k.castSucc)) r PUnit Yr ∧
      ∀ (a a' : ∀ j, innerInput O j) (ρ ρ' : r)
        (b b' : ∀ j : Fin (n + 1), innerOutput I j.castSucc),
        (∑ p : I (Fin.last (n + 2)) × s,
          Y ((a, ρ), (Fin.snoc b p.1, p.2)) ((a', ρ'), (Fin.snoc b' p.1, p.2))) =
        (if a (Fin.last (n + 1)) = a' (Fin.last (n + 1)) then
          Yr ((fun j : Fin (n + 1) => a j.castSucc, ρ), (b, ⟨⟩))
            ((fun j : Fin (n + 1) => a' j.castSucc, ρ'), (b', ⟨⟩))
        else 0) := by
  obtain ⟨Y', hY', hEq⟩ := extended_succ_tooth hY
  refine ⟨WireFam.matReindex
      (boundaryEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc))
        (innerOutput (fun k : Fin (n + 2) => I k.castSucc)) r PUnit)
      ((WireFam.matReindex (spaceEquiv (fun j : Fin (n + 1) =>
          Equiv.refl (boundaryInput (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r j))
          (punitWedgeEquiv (innerOutput (fun k : Fin (n + 2) => I k.castSucc))))).symm
        (WireFam.matReindex (spaceEquiv (famEquiv (O := O) r)
            (fun j : Fin (n + 1) => (Equiv.refl (innerOutput I j.castSucc) :
              innerOutput I j.castSucc ≃
                innerOutput (fun k : Fin (n + 2) => I k.castSucc) j))) Y')), ?_, ?_⟩
  · simp only [ExtendedNormalized]
    rw [submatrix_matReindex_self]
    refine (Normalized.punit_wedge_iff _).mpr ?_
    rw [WireFam.matReindex_symm, WireFam.matReindex_matReindex_symm]
    exact Normalized.reindex_fwd (famEquiv (O := O) r)
      (fun j : Fin (n + 1) => (Equiv.refl (innerOutput I j.castSucc) :
        innerOutput I j.castSucc ≃
          innerOutput (fun k : Fin (n + 2) => I k.castSucc) j)) Y' hY'
  · intro a a' ρ ρ' b b'
    rw [hEq a ρ a' ρ' b b']
    by_cases hlast : a (Fin.last (n + 1)) = a' (Fin.last (n + 1))
    · rw [ite_eq_left hlast, ite_eq_left hlast]
      have hsplit : ∀ (x : ∀ j : Fin (n + 1), innerInput (fun k : Fin (n + 2) => O k.castSucc) j)
          (ρx : r) (bb : ∀ j : Fin (n + 1), innerOutput (fun k : Fin (n + 2) => I k.castSucc) j),
          (boundaryEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc))
              (innerOutput (fun k : Fin (n + 2) => I k.castSucc)) r PUnit).symm
              ((x, ρx), (bb, ⟨⟩))
            = ((boundaryInputEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r).symm
                (x, ρx),
              (boundaryOutputEquiv (innerOutput (fun k : Fin (n + 2) => I k.castSucc)) PUnit).symm
                (bb, ⟨⟩)) := fun _ _ _ => rfl
      have hwedge : ∀ (x : ∀ j : Fin (n + 1), innerInput (fun k : Fin (n + 2) => O k.castSucc) j)
          (ρx : r) (bb : ∀ j : Fin (n + 1), innerOutput (fun k : Fin (n + 2) => I k.castSucc) j),
          (spaceEquiv (fun j : Fin (n + 1) =>
              Equiv.refl (boundaryInput (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r j))
              (punitWedgeEquiv (innerOutput (fun k : Fin (n + 2) => I k.castSucc))))
            ((boundaryInputEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r).symm
                (x, ρx),
              (boundaryOutputEquiv (innerOutput (fun k : Fin (n + 2) => I k.castSucc)) PUnit).symm
                (bb, ⟨⟩))
            = ((boundaryInputEquiv (innerInput (fun k : Fin (n + 2) => O k.castSucc)) r).symm
                (x, ρx), bb) := by
        intro x ρx bb
        simp only [spaceEquiv_apply, punitWedgeEquiv_boundaryOutputEquiv_symm]
        rfl
      rw [WireFam.matReindex_apply,
        hsplit (fun j : Fin (n + 1) => a j.castSucc) ρ b,
        hsplit (fun j : Fin (n + 1) => a' j.castSucc) ρ' b',
        WireFam.matReindex_symm_apply,
        hwedge (fun j : Fin (n + 1) => a j.castSucc) ρ b,
        hwedge (fun j : Fin (n + 1) => a' j.castSucc) ρ' b',
        WireFam.matReindex_apply]
      simp only [spaceEquiv_symm_apply]
      rw [piCongrRight_refl_symm_id, piCongrRight_refl_symm_id,
        ← bIE_castSucc_brid, ← bIE_castSucc_brid]
    · rw [ite_eq_right hlast, ite_eq_right hlast]

end SuccTooth

/-- The castSucc-truncation of a cons-extended tuple is the cons of the
castSucc-truncated tail. -/
private theorem cons_castSucc_trunc {m : Nat} {α : Fin (m + 2) → Type u}
    (x : α 0) (t : ∀ j : Fin (m + 1), α j.succ) :
    (fun j : Fin (m + 1) => (Fin.cons x t) j.castSucc) =
      (Fin.cons x (fun k : Fin m => t k.castSucc) :
        ∀ j : Fin (m + 1), α j.castSucc) := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ k => rfl

/-- Reading a cons-extended tuple at the last wire is reading the tail at its
own last wire. -/
private theorem cons_last_gen {m : Nat} {α : Fin (m + 2) → Type u} (x : α 0)
    (t : ∀ j : Fin (m + 1), α j.succ) :
    (Fin.cons x t) (Fin.last (m + 1)) = t (Fin.last m) := rfl

/-- Reading a snoc-extended tuple at the last wire is the appended value. -/
private theorem snoc_last_val {m : Nat} {γ : Fin (m + 1) → Type u}
    (y : ∀ j : Fin m, γ j.castSucc) (w : γ (Fin.last m)) :
    (Fin.snoc y w) (Fin.last m) = w := by
  simp [Fin.snoc_last]

/-- The castSucc-truncation of a snoc-extended tuple is the original
truncated tuple. -/
private theorem snoc_castSucc_self {m : Nat} {γ : Fin (m + 1) → Type u}
    (y : ∀ j : Fin m, γ j.castSucc) (w : γ (Fin.last m)) :
    (fun k : Fin m => (Fin.snoc y w) k.castSucc) = y := by
  funext k
  simp [Fin.snoc_castSucc]

/-- A conditional fiber guarded by equality of two snoc-extended tuples'
last-wire values collapses onto the diagonal: the guard pins the summed
last value to the fixed one, so the inner sum evaluates to the guarded
summand at that value. -/
private theorem sum_snoc_last_diag {m : Nat} {γ : Fin (m + 1) → Type u}
    [∀ j, Fintype (γ j)] [∀ j, DecidableEq (γ j)]
    {M : Type v} [AddCommMonoid M]
    (y y' : ∀ j : Fin m, γ j.castSucc) (w : γ (Fin.last m))
    (F : γ (Fin.last m) → M) :
    (∑ w' : γ (Fin.last m),
        if (Fin.snoc y w) (Fin.last m) = (Fin.snoc y' w') (Fin.last m) then
          F w' else 0) = F w := by
  have hcell : ∀ w' : γ (Fin.last m),
      (if (Fin.snoc y w) (Fin.last m) = (Fin.snoc y' w') (Fin.last m) then
        F w' else 0) = (if w' = w then F w' else 0) := by
    intro w'
    rw [snoc_last_val, snoc_last_val]
    by_cases h : w = w'
    · subst h
      rfl
    · rw [ite_eq_right h, ite_eq_right fun hh => h hh.symm]
  rw [Finset.sum_congr rfl (fun w' _ => hcell w'), Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ _)]

/-! ### Summation rotations for the insertion induction

The insertion induction repeatedly moves one summation binder past its
neighbors (bringing a spectator or traced wire to the position the next
stage consumes).  These rotations package the `Finset.sum_comm` congruence
chains for six-fold sums, so each stage states only the target binder
order. -/

private theorem sum6_swap23 {A₁ A₂ A₃ A₄ A₅ A₆ : Type u}
    [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype A₄] [Fintype A₅] [Fintype A₆]
    {M : Type v} [AddCommMonoid M] (f : A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → M) :
    (∑ a₁ : A₁, ∑ a₂ : A₂, ∑ a₃ : A₃, ∑ a₄ : A₄, ∑ a₅ : A₅, ∑ a₆ : A₆,
        f a₁ a₂ a₃ a₄ a₅ a₆) =
    (∑ a₁ : A₁, ∑ a₃ : A₃, ∑ a₂ : A₂, ∑ a₄ : A₄, ∑ a₅ : A₅, ∑ a₆ : A₆,
        f a₁ a₂ a₃ a₄ a₅ a₆) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem sum6_swap34 {A₁ A₂ A₃ A₄ A₅ A₆ : Type u}
    [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype A₄] [Fintype A₅] [Fintype A₆]
    {M : Type v} [AddCommMonoid M] (f : A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → M) :
    (∑ a₁ : A₁, ∑ a₂ : A₂, ∑ a₃ : A₃, ∑ a₄ : A₄, ∑ a₅ : A₅, ∑ a₆ : A₆,
        f a₁ a₂ a₃ a₄ a₅ a₆) =
    (∑ a₁ : A₁, ∑ a₂ : A₂, ∑ a₄ : A₄, ∑ a₃ : A₃, ∑ a₅ : A₅, ∑ a₆ : A₆,
        f a₁ a₂ a₃ a₄ a₅ a₆) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem sum6_swap45 {A₁ A₂ A₃ A₄ A₅ A₆ : Type u}
    [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype A₄] [Fintype A₅] [Fintype A₆]
    {M : Type v} [AddCommMonoid M] (f : A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → M) :
    (∑ a₁ : A₁, ∑ a₂ : A₂, ∑ a₃ : A₃, ∑ a₄ : A₄, ∑ a₅ : A₅, ∑ a₆ : A₆,
        f a₁ a₂ a₃ a₄ a₅ a₆) =
    (∑ a₁ : A₁, ∑ a₂ : A₂, ∑ a₃ : A₃, ∑ a₅ : A₅, ∑ a₄ : A₄, ∑ a₆ : A₆,
        f a₁ a₂ a₃ a₄ a₅ a₆) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem sum6_swap56 {A₁ A₂ A₃ A₄ A₅ A₆ : Type u}
    [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype A₄] [Fintype A₅] [Fintype A₆]
    {M : Type v} [AddCommMonoid M] (f : A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → M) :
    (∑ a₁ : A₁, ∑ a₂ : A₂, ∑ a₃ : A₃, ∑ a₄ : A₄, ∑ a₅ : A₅, ∑ a₆ : A₆,
        f a₁ a₂ a₃ a₄ a₅ a₆) =
    (∑ a₁ : A₁, ∑ a₂ : A₂, ∑ a₃ : A₃, ∑ a₄ : A₄, ∑ a₆ : A₆, ∑ a₅ : A₅,
        f a₁ a₂ a₃ a₄ a₅ a₆) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Both comb-index factors of a spectator-guarded sum split at the last
output wire: each pair index becomes input, truncated output, and last
output value. -/
private theorem sum_prod_snoc_split {m : Nat}
    {X Y : Fin (m + 1) → Type u}
    [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]
    {S : Type u} [Fintype S] {M : Type v} [AddCommMonoid M]
    (F : (∀ j, X j) × (∀ j, Y j) → (∀ j, X j) × (∀ j, Y j) → S → M) :
    (∑ σ : S, ∑ z : (∀ j, X j) × (∀ j, Y j),
        ∑ z' : (∀ j, X j) × (∀ j, Y j), F z z' σ) =
    (∑ σ : S, ∑ z₁ : ∀ j, X j,
        ∑ z₂ : ∀ j : Fin m, Y j.castSucc, ∑ η : Y (Fin.last m),
        ∑ z₁' : ∀ j, X j,
        ∑ z₂' : ∀ j : Fin m, Y j.castSucc, ∑ η' : Y (Fin.last m),
        F (z₁, Fin.snoc z₂ η) (z₁', Fin.snoc z₂' η') σ) := by
  simp only [Fintype.sum_prod_type, sum_pi_snoc]

/-- Entrywise trace preservation under insertion, by induction on the comb
length: the base case is the two-wire contraction; the step peels the outer
comb's last tooth, contracts the inner comb's tooth through the restricted
comb's extended normalization, and re-applies the induction hypothesis to
the restricted comb. -/
private theorem action_extension_trace_aux : ∀ (n : Nat) (I O : Fin (n + 2) → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (J : CMatrix (Space I O)) (_hJ : Normalized I O J)
    (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s)))
    (_hY : ExtendedNormalized (innerInput O) (innerOutput I) r s Y),
    partialTraceB (ancillaryExtension (actionMap I O J) Y) = 1 := by
  intro n
  induction n with
  | zero =>
    intro I O _ _ _ _ r s _ _ _ _ J hJ Y hY
    exact action_extension_trace_zero J hJ Y hY
  | succ n ih =>
    intro I O instI instDI instO instDO r s instR instDR instS instDS J hJ Y hY
    obtain ⟨_, K, hK, heq⟩ := hJ
    obtain ⟨Yr, hYr, hEqY⟩ := extended_succ_tooth_restricted hY
    have hIHK := @ih (fun k : Fin (n + 2) => I k.castSucc) (fun k : Fin (n + 2) => O k.castSucc)
      (fun k => instI k.castSucc) (fun k => instDI k.castSucc)
      (fun k => instO k.castSucc) (fun k => instDO k.castSucc)
      r PUnit instR instDR inferInstance inferInstance K hK Yr hYr
    classical
    ext x x'
    rcases x with ⟨i₀, ρ⟩
    rcases x' with ⟨i₀', ρ'⟩
    simp only [partialTraceB, actionMap_ext_apply, Matrix.one_apply, Prod.mk.injEq]
    rw [Fintype.sum_prod_type]
    dsimp only
    -- Stage 1: bring the traced last output wire innermost and consume the
    -- outer comb's peeled tooth via the recursion witness `heq`.
    have hstage1 : (∑ ω : O (Fin.last (n + 1 + 1)), ∑ σ : s,
        ∑ z : Space (innerInput O) (innerOutput I),
        ∑ z' : Space (innerInput O) (innerOutput I),
          Y ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ)) *
            J (Fin.cons i₀ z.2, Fin.snoc z.1 ω) (Fin.cons i₀' z'.2, Fin.snoc z'.1 ω)) =
      (∑ σ : s, ∑ z : Space (innerInput O) (innerOutput I),
        ∑ z' : Space (innerInput O) (innerOutput I),
          if z.2 (Fin.last (n + 1)) = z'.2 (Fin.last (n + 1)) then
            Y ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ)) *
              K ((fun j : Fin (n + 2) => (Fin.cons i₀ z.2) j.castSucc), z.1)
                ((fun j : Fin (n + 2) => (Fin.cons i₀' z'.2) j.castSucc), z'.1)
          else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [← Finset.mul_sum, heq (Fin.cons i₀ z.2) (Fin.cons i₀' z'.2) z.1 z'.1,
        cons_last_gen, cons_last_gen, mul_ite, mul_zero]
    rw [hstage1]
    -- Stage 2: split both inner tuples into input, truncated output, and
    -- last output value; the peeled tooth's input truncation reads only the
    -- truncated output, so its factor is independent of the last value.
    rw [sum_prod_snoc_split]
    simp only [cons_castSucc_trunc, snoc_castSucc_self]
    -- Stage 3a: the tooth condition pins the two last output values
    -- together, collapsing the second one's fiber to the diagonal.
    simp only [sum_snoc_last_diag]
    -- Stage 3b: reorder so that, per quadruple, the last output value and
    -- the spectator sit innermost.
    rw [Finset.sum_comm, sum6_swap23, sum6_swap34, sum6_swap45, sum6_swap56,
      sum6_swap34, sum6_swap45]
    -- Stage 3c: per quadruple, pair the last output value with the spectator
    -- and consume the resulting joint fiber through the restricted comb's
    -- peeled tooth.
    have hstage3c : (∑ z₁ : ∀ j, innerInput O j,
        ∑ z₂ : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ z₁' : ∀ j, innerInput O j,
        ∑ z₂' : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ η : innerOutput I (Fin.last (n + 1)), ∑ σ : s,
          Y ((z₁, ρ), (Fin.snoc z₂ η, σ)) ((z₁', ρ'), (Fin.snoc z₂' η, σ)) *
            K (Fin.cons i₀ z₂, z₁) (Fin.cons i₀' z₂', z₁')) =
      (∑ z₁ : ∀ j, innerInput O j,
        ∑ z₂ : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ z₁' : ∀ j, innerInput O j,
        ∑ z₂' : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
          if z₁ (Fin.last (n + 1)) = z₁' (Fin.last (n + 1)) then
            Yr ((fun j : Fin (n + 1) => z₁ j.castSucc, ρ), (z₂, PUnit.unit))
              ((fun j : Fin (n + 1) => z₁' j.castSucc, ρ'), (z₂', PUnit.unit)) *
              K (Fin.cons i₀ z₂, z₁) (Fin.cons i₀' z₂', z₁') else 0) := by
      refine Finset.sum_congr rfl fun z₁ _ => Finset.sum_congr rfl fun z₂ _ =>
        Finset.sum_congr rfl fun z₁' _ => Finset.sum_congr rfl fun z₂' _ => ?_
      have hpair : (∑ η : innerOutput I (Fin.last (n + 1)), ∑ σ : s,
          Y ((z₁, ρ), (Fin.snoc z₂ η, σ)) ((z₁', ρ'), (Fin.snoc z₂' η, σ))) =
          (∑ p : I (Fin.last (n + 2)) × s,
            Y ((z₁, ρ), (Fin.snoc z₂ p.1, p.2)) ((z₁', ρ'), (Fin.snoc z₂' p.1, p.2))) := by
        rw [Fintype.sum_prod_type]
        rfl
      simp only [← Finset.sum_mul]
      rw [hpair, hEqY z₁ z₁' ρ ρ' z₂ z₂', ite_mul, zero_mul]
    rw [hstage3c]
    -- Stage 4: snoc-split the two input tuples so that the traced last input
    -- wire (the restricted comb's own traced output wire) is explicit, collapse
    -- the second one's fiber to the diagonal, and reorder it outermost.
    have h4a : (∑ z₁ : ∀ j, innerInput O j,
        ∑ z₂ : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ z₁' : ∀ j, innerInput O j,
        ∑ z₂' : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
          if z₁ (Fin.last (n + 1)) = z₁' (Fin.last (n + 1)) then
            Yr ((fun j : Fin (n + 1) => z₁ j.castSucc, ρ), (z₂, PUnit.unit))
              ((fun j : Fin (n + 1) => z₁' j.castSucc, ρ'), (z₂', PUnit.unit)) *
              K (Fin.cons i₀ z₂, z₁) (Fin.cons i₀' z₂', z₁') else 0) =
      (∑ γ₁ : ∀ j : Fin (n + 1), innerInput O j.castSucc,
        ∑ γ : innerInput O (Fin.last (n + 1)),
        ∑ z₂ : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ γ₁' : ∀ j : Fin (n + 1), innerInput O j.castSucc,
        ∑ z₂' : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ γ' : innerInput O (Fin.last (n + 1)),
          if (Fin.snoc γ₁ γ) (Fin.last (n + 1)) = (Fin.snoc γ₁' γ') (Fin.last (n + 1)) then
            Yr ((fun j : Fin (n + 1) => (Fin.snoc γ₁ γ) j.castSucc, ρ), (z₂, PUnit.unit))
              ((fun j : Fin (n + 1) => (Fin.snoc γ₁' γ') j.castSucc, ρ'), (z₂', PUnit.unit)) *
            K (Fin.cons i₀ z₂, Fin.snoc γ₁ γ) (Fin.cons i₀' z₂', Fin.snoc γ₁' γ') else 0) := by
      rw [sum_pi_snoc]
      refine Finset.sum_congr rfl fun γ₁ _ => Finset.sum_congr rfl fun γ _ =>
        Finset.sum_congr rfl fun z₂ _ => ?_
      rw [sum_pi_snoc]
      exact Finset.sum_congr rfl fun γ₁' _ => Finset.sum_comm
    rw [h4a]
    simp only [sum_snoc_last_diag]
    rw [Finset.sum_comm]
    simp only [snoc_castSucc_self]
    -- Stage 5: consume the induction hypothesis on the restricted comb: the
    -- remaining contraction is exactly the restricted comb's own insertion
    -- trace, reassembled through the boundary wire identification.
    have hIHe := congrFun (congrFun hIHK (i₀, ρ)) (i₀', ρ')
    simp only [partialTraceB, Matrix.one_apply] at hIHe
    rw [Finset.sum_congr rfl (fun j _ =>
        actionMap_ext_apply (fun k : Fin (n + 2) => I k.castSucc)
          (fun k : Fin (n + 2) => O k.castSucc) K r PUnit
          Yr ((i₀, ρ), j) ((i₀', ρ'), j))] at hIHe
    rw [Fintype.sum_prod_type] at hIHe
    dsimp only at hIHe
    rw [Finset.sum_congr rfl (fun x _ => sum_punit_eq
        (fun u => (∑ z : Space (innerInput (fun k => O k.castSucc))
                (innerOutput (fun k => I k.castSucc)),
            ∑ z' : Space (innerInput (fun k => O k.castSucc))
                (innerOutput (fun k => I k.castSucc)),
            Yr ((z.1, ρ), (z.2, u)) ((z'.1, ρ'), (z'.2, u)) *
              K (Fin.cons i₀ z.2, Fin.snoc z.1 x) (Fin.cons i₀' z'.2, Fin.snoc z'.1 x))))] at hIHe
    have hsplit : (∑ x : O ((Fin.last (n + 1)).castSucc),
        ∑ z : Space (innerInput (fun k => O k.castSucc))
            (innerOutput (fun k => I k.castSucc)),
        ∑ z' : Space (innerInput (fun k => O k.castSucc))
            (innerOutput (fun k => I k.castSucc)),
          Yr ((z.1, ρ), (z.2, PUnit.unit)) ((z'.1, ρ'), (z'.2, PUnit.unit)) *
            K (Fin.cons i₀ z.2, Fin.snoc z.1 x) (Fin.cons i₀' z'.2, Fin.snoc z'.1 x)) =
      (∑ γ : innerInput O (Fin.last (n + 1)),
        ∑ γ₁ : ∀ j : Fin (n + 1), innerInput O j.castSucc,
        ∑ z₂ : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ γ₁' : ∀ j : Fin (n + 1), innerInput O j.castSucc,
        ∑ z₂' : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
          Yr ((γ₁, ρ), (z₂, PUnit.unit)) ((γ₁', ρ'), (z₂', PUnit.unit)) *
            K (Fin.cons i₀ z₂, Fin.snoc γ₁ γ) (Fin.cons i₀' z₂', Fin.snoc γ₁' γ)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
      rw [Fintype.sum_prod_type]
      rfl
    have hfinal : (∑ γ : innerInput O (Fin.last (n + 1)),
        ∑ γ₁ : ∀ j : Fin (n + 1), innerInput O j.castSucc,
        ∑ z₂ : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
        ∑ γ₁' : ∀ j : Fin (n + 1), innerInput O j.castSucc,
        ∑ z₂' : ∀ j : Fin (n + 1), innerOutput I j.castSucc,
          Yr ((γ₁, ρ), (z₂, PUnit.unit)) ((γ₁', ρ'), (z₂', PUnit.unit)) *
            K (Fin.cons i₀ z₂, Fin.snoc γ₁ γ) (Fin.cons i₀' z₂', Fin.snoc γ₁' γ)) =
        (if (i₀, ρ) = (i₀', ρ') then 1 else 0) := by
      rw [← hsplit]
      exact hIHe
    rw [hfinal]
    by_cases hp : i₀ = i₀' ∧ ρ = ρ'
    · have hmk : (i₀, ρ) = (i₀', ρ') := by
        obtain ⟨h1, h2⟩ := hp
        rw [h1, h2]
      rw [ite_eq_left hmk, ite_eq_left hp]
    · have hmk : ¬((i₀, ρ) = (i₀', ρ')) := by
        intro hh
        exact hp ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
      rw [ite_eq_right hmk, ite_eq_right hp]

/-- Every recursively normalized comb acts as a completely deterministic
N-map: its Choi-space action is completely positive, and it sends every
jointly normalized inner comb with independent finite boundary ancillas to
a channel Choi operator.  Complete positivity is the comb's own positivity
through `Comb.actionMap_cp_iff`; the trace side is the entrywise induction
over the normalization recursion itself
[Chiribella2009Networks, comblong-pub.tex:860-877].  This closes the
admissibility gap left open at `Comb.IsDeterministicMap`. -/
theorem Normalized.isDeterministicMap {J : CMatrix (Space I O)}
    (hJ : Normalized I O J) :
    IsDeterministicMap I O (actionMap I O J) := by
  refine ⟨(actionMap_cp_iff I O J).2 hJ.posSemidef, ?_⟩
  intro r s _ _ _ _ Y hY
  exact ⟨ancillaryExtension_posSemidef _ ((actionMap_cp_iff I O J).2 hJ.posSemidef) Y
    (extendedNormalized_posSemidef hY),
    action_extension_trace_aux n I O J hJ Y hY⟩

end InsertionTrace

open QIT.WireFam

/-! ## Suffix composition: the composite comb and its closure properties -/

section Transport
variable {a b s : ℕ} {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}

/-- Cast cancellation: casting along an equation and back returns the original
value. -/
private theorem cast_cast_cancel {A B : Type u} (h : A = B) (x : B) :
    cast h (cast h.symm x) = x := by
  cases h
  rfl

/-- Cast cancellation in the composed direction: casting forward along an
equation and back returns the original value. -/
private theorem cast_cast_cancel' {A B : Type u} (h : A = B) (x : A) :
    cast h.symm (cast h x) = x := by
  cases h
  rfl

/-- Cast along an equation with a shifted source: composing the shift with a
second cast equals casting along the directly-shifted equation. -/
private theorem cast_comp {A A' B : Type u} (hAA : A = A') (h1 : A' = B) (h2 : A = B) (x : A) :
    cast h1.symm (cast h2 x) = cast hAA x := by
  cases hAA
  exact cast_cast_cancel' h2 x

/-- Mirror shift: composing a cast with a shifted-target cast equals casting
the target shift directly. -/
private theorem cast_comp' {A B B' : Type u} (hBB : B = B') (h1 : A = B) (h2 : A = B') (x : B') :
    cast h1 (cast h2.symm x) = cast hBB.symm x := by
  cases hBB
  exact cast_cast_cancel h1 x

/-- Two-step cast collapse along composed type equations. -/
private theorem cast2 {A B C : Type u} (h1 : A = B) (h2 : B = C) (x : A) :
    cast h2 (cast h1 x) = cast (h1.trans h2) x := by
  cases h1; cases h2; rfl

/-- Four-step cast collapse along composed type equations. -/
private theorem cast4 {A B C D E : Type u} (h1 : A = B) (h2 : B = C) (h3 : C = D) (h4 : D = E)
    (x : A) :
    cast h4 (cast h3 (cast h2 (cast h1 x))) = cast (h1.trans (h2.trans (h3.trans h4))) x := by
  cases h1; cases h2; cases h3; cases h4; rfl

/-- Casting a family value along a congruence of its index gives the value at
the new index. -/
private theorem cast_congrArg_apply {ι : Type v} {X : ι → Type u} {a b : ι} (h : a = b) (g : ∀ i, X i) :
    cast (congrArg X h) (g a) = g b := by
  cases h
  rfl

end Transport

/-! ## The suffix match of the inner comb -/

section SuffixMatchD2

variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The composite input index map. -/
def compIn (k m : Nat) (j : Fin (n + 1 - m)) : Fin (n + 2) :=
  if (j : Nat) ≤ k then ⟨(j : Nat), by omega⟩ else ⟨(j : Nat) + (m + 1), by omega⟩

/-- The composite output index map. -/
def compOut (k m : Nat) (j : Fin (n + 1 - m)) : Fin (n + 2) :=
  if (j : Nat) < k then ⟨(j : Nat), by omega⟩ else ⟨(j : Nat) + (m + 1), by omega⟩

@[simp] private theorem compIn_val (k m : Nat) (j : Fin (n + 1 - m)) :
    (compIn (n := n) k m j : Nat) = if (j : Nat) ≤ k then (j : Nat) else (j : Nat) + (m + 1) := by
  unfold compIn
  split
  all_goals rfl

@[simp] private theorem compOut_val (k m : Nat) (j : Fin (n + 1 - m)) :
    (compOut (n := n) k m j : Nat) = if (j : Nat) < k then (j : Nat) else (j : Nat) + (m + 1) := by
  unfold compOut
  split
  all_goals rfl

/-- Outer input-wire pick, supplying the inner window's output wires. -/
def suffixInIdx (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (j : Fin (m + 1)) : Fin (n + 2) :=
  ⟨k + 1 + j, by omega⟩

/-- Outer output-wire pick, supplying the inner window's input wires. -/
def suffixOutIdx (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (j : Fin (m + 1)) : Fin (n + 2) :=
  ⟨k + j, by omega⟩

/-- The outer input wires inside the suffix window. These are the inner
comb's output family, since the inner outputs feed the outer inputs. -/
abbrev suffixIn (I : Fin (n + 2) → Type u) (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Fin (m + 1) → Type u := fun j => I (suffixInIdx k m hkm j)

/-- The outer output wires inside the suffix window. These are the inner
comb's input family, since the outer outputs feed the inner inputs. -/
abbrev suffixOut (O : Fin (n + 2) → Type u) (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Fin (m + 1) → Type u := fun j => O (suffixOutIdx k m hkm j)

/-- The connected-wire pick into the outer comb's flat index space. -/
def suffixConnIdx (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (i : Fin (m + 1 + (m + 1))) :
    Fin (n + 2 + (n + 2)) :=
  Fin.addCases
    (fun t => Fin.natAdd (n + 2) ⟨k + t, by omega⟩)
    (fun t => Fin.castAdd (n + 2) ⟨k + 1 + t, by omega⟩) i

/-- The output-side connected wires of the suffix window land in the outer
comb's output block. -/
@[simp] theorem suffixConnIdx_castAdd (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (t : Fin (m + 1)) :
    suffixConnIdx k m hkm (Fin.castAdd (m + 1) t) = Fin.natAdd (n + 2) ⟨k + t, by omega⟩ := by
  simp only [suffixConnIdx, Fin.addCases_left]

/-- The input-side connected wires of the suffix window land in the outer
comb's input block. -/
@[simp] theorem suffixConnIdx_natAdd (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (t : Fin (m + 1)) :
    suffixConnIdx k m hkm (Fin.natAdd (m + 1) t) = Fin.castAdd (n + 2) ⟨k + 1 + t, by omega⟩ := by
  simp only [suffixConnIdx, Fin.addCases_right]

/-- The matched connection of the inner comb into the outer comb's suffix. -/
def suffixMatch (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    WireMatch (append (suffixOut O k m hkm) (suffixIn I k m hkm)) (append I O) where
  s := m + 1 + (m + 1)
  ι₁ := fun i => i
  ι₂ := suffixConnIdx k m hkm
  hι₁ := fun _ _ h => h
  hι₂ := by
    intro i i' h
    induction i using Fin.addCases with
    | left t =>
      induction i' using Fin.addCases with
      | left t' =>
        simp only [suffixConnIdx_castAdd] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd] at hv
        simp only [Fin.ext_iff, Fin.val_castAdd]
        omega
      | right t' =>
        simp only [suffixConnIdx_castAdd, suffixConnIdx_natAdd] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        omega
    | right t =>
      induction i' using Fin.addCases with
      | left t' =>
        simp only [suffixConnIdx_natAdd, suffixConnIdx_castAdd] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        omega
      | right t' =>
        simp only [suffixConnIdx_natAdd] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd] at hv
        simp only [Fin.ext_iff, Fin.val_natAdd]
        omega
  e := fun i => Equiv.cast (by
    induction i using Fin.addCases with
    | left t =>
      simp only [suffixConnIdx_castAdd, append_castAdd, append_natAdd]
      rfl
    | right t =>
      simp only [suffixConnIdx_natAdd, append_castAdd, append_natAdd]
      rfl)

private instance {k m : Nat} (hkm : k + m + 1 ≤ n + 1) (i : Fin (m + 1 + (m + 1))) :
    Fintype ((suffixMatch (I := I) (O := O) k m hkm).connFam₁ i) :=
  inferInstanceAs (Fintype (append (suffixOut O k m hkm) (suffixIn I k m hkm) i))

end SuffixMatchD2

/-! ## The suffix composition: specialized readback rules and flat transport -/

section SuffixComp

variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Reading the outer configuration at a private wire of the suffix match
returns the private entry. -/
private theorem suffixRead₂_compl (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (z : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (w : ∀ j, (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j)
    (j : Fin ((n + 2 + (n + 2)) - (m + 1 + (m + 1)))) :
    (suffixMatch (I := I) (O := O) k m hkm).read₂ z w
      (complEmb (suffixConnIdx k m hkm)
        (suffixMatch (I := I) (O := O) k m hkm).hι₂ j) = w j :=
  WireMatch.read₂_compl (suffixMatch (I := I) (O := O) k m hkm) z w j

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Reading the outer configuration at an input-side window wire returns the
connected entry, whose type equality is transparent. -/
private theorem suffixRead₂_conn_natAdd (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (z : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (w : ∀ j, (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j)
    (t : Fin (m + 1)) :
    (suffixMatch (I := I) (O := O) k m hkm).read₂ z w
        (suffixConnIdx k m hkm (Fin.natAdd (m + 1) t))
      = (suffixMatch (I := I) (O := O) k m hkm).eRelabel z (Fin.natAdd (m + 1) t) :=
  WireMatch.read₂_conn (suffixMatch (I := I) (O := O) k m hkm) z w (Fin.natAdd (m + 1) t)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Reading the outer configuration at an output-side window wire returns the
connected entry. -/
private theorem suffixRead₂_conn_castAdd (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (z : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (w : ∀ j, (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j)
    (t : Fin (m + 1)) :
    (suffixMatch (I := I) (O := O) k m hkm).read₂ z w
        (suffixConnIdx k m hkm (Fin.castAdd (m + 1) t))
      = (suffixMatch (I := I) (O := O) k m hkm).eRelabel z (Fin.castAdd (m + 1) t) :=
  WireMatch.read₂_conn (suffixMatch (I := I) (O := O) k m hkm) z w (Fin.castAdd (m + 1) t)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Reading the inner configuration through the suffix match is the identity:
the first family is entirely connected, and its connection is the identity. -/
private theorem suffixRead₁ (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (g : ∀ j, (suffixMatch (I := I) (O := O) k m hkm).complFam₁ j)
    (z : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i) :
    (suffixMatch (I := I) (O := O) k m hkm).read₁ (g, z) = z := by
  funext i
  exact WireMatch.read₁_conn (suffixMatch (I := I) (O := O) k m hkm) g z i

/-- Flattening of the outer comb's Choi matrix into its wire-indexed form. -/
def JFlat (J : CMatrix (Space I O)) : CMatrix (∀ i, append I O i) :=
  matReindex (splitAppendEquiv I O).symm J

/-- The flattening equivalence of the inner comb's Choi space: inputs first
(the consumed outer outputs), then outputs (the produced outer inputs),
matching the suffix match's first wire family. -/
def XFlatEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Space (suffixOut O k m hkm) (suffixIn I k m hkm) ≃
      (∀ i, append (suffixOut O k m hkm) (suffixIn I k m hkm) i) :=
  (splitAppendEquiv (suffixOut O k m hkm) (suffixIn I k m hkm)).symm

/-- Flattening of the inner comb's Choi matrix along `XFlatEquiv`. -/
def XFlat (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))) :
    CMatrix (∀ i, append (suffixOut O k m hkm) (suffixIn I k m hkm) i) :=
  matReindex (XFlatEquiv (I := I) (O := O) k m hkm) X

end SuffixComp
/-! ## The four-region complement enumeration -/

section SuffixRegions

variable {n : Nat}

/-- The explicit enumeration of the outer comb's private wires: first the
untouched input wires below and above the suffix window, then the untouched
output wires below and above it. -/
def suffixComplIdx (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) : Fin (n + 2 + (n + 2)) :=
  if h : (j : Nat) < n + 1 - m then
    Fin.castAdd (n + 2) (compIn k m ⟨(j : Nat), by omega⟩)
  else
    Fin.natAdd (n + 2) (compOut k m ⟨(j : Nat) - (n + 1 - m), by omega⟩)

/-- Numeric form of the four-region enumeration. -/
private theorem suffixComplIdx_val (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) :
    (suffixComplIdx k m hkm j : Nat) =
      (if (j : Nat) < n + 1 - m then
        (if (j : Nat) ≤ k then (j : Nat) else (j : Nat) + (m + 1))
      else
        (n + 2) + (if (j : Nat) - (n + 1 - m) < k then (j : Nat) - (n + 1 - m)
          else (j : Nat) - (n + 1 - m) + (m + 1))) := by
  have hj : (j : Nat) < (n + 2 + (n + 2)) - ((m + 1) + (m + 1)) := j.isLt
  rw [suffixComplIdx]
  split
  simp only [Fin.val_castAdd, compIn_val]
  simp only [Fin.val_natAdd, compOut_val]

/-- Region computation: an input-below index enumerates the untouched input
wires at or below `k`. -/
private theorem suffixComplIdx_of_lt_le (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))))
    (hj : (j : Nat) < n + 1 - m) (hjk : (j : Nat) ≤ k) :
    suffixComplIdx k m hkm j = Fin.castAdd (n + 2) (⟨(j : Nat), by omega⟩ : Fin (n + 2)) := by
  have hc : compIn k m (⟨(j : Nat), by omega⟩ : Fin (n + 1 - m))
      = (⟨(j : Nat), by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    show (compIn k m (⟨(j : Nat), by omega⟩ : Fin (n + 1 - m)) : Nat) = (j : Nat)
    rw [compIn_val]
    exact ite_eq_left (by simpa using hjk)
  rw [suffixComplIdx, dite_eq_left hj, hc]

/-- Region computation: an input-above index enumerates the untouched input
wires above the suffix window. -/
private theorem suffixComplIdx_of_lt_gt (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))))
    (hj : (j : Nat) < n + 1 - m) (hjk : k < (j : Nat)) :
    suffixComplIdx k m hkm j
      = Fin.castAdd (n + 2) (⟨(j : Nat) + (m + 1), by omega⟩ : Fin (n + 2)) := by
  have hc : compIn k m (⟨(j : Nat), by omega⟩ : Fin (n + 1 - m))
      = (⟨(j : Nat) + (m + 1), by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    show (compIn k m (⟨(j : Nat), by omega⟩ : Fin (n + 1 - m)) : Nat)
        = (j : Nat) + (m + 1)
    rw [compIn_val]
    exact ite_eq_right (by simpa using hjk)
  rw [suffixComplIdx, dite_eq_left hj, hc]

/-- Region computation: an output-below index enumerates the untouched output
wires below `k`. -/
private theorem suffixComplIdx_of_ge_lt (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))))
    (hjn : ¬((j : Nat) < n + 1 - m)) (hjk : (j : Nat) - (n + 1 - m) < k) :
    suffixComplIdx k m hkm j
      = Fin.natAdd (n + 2) (⟨(j : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 2)) := by
  have hc : compOut k m (⟨(j : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m))
      = (⟨(j : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    show (compOut k m (⟨(j : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m)) : Nat)
        = (j : Nat) - (n + 1 - m)
    rw [compOut_val]
    exact ite_eq_left (by simpa using hjk)
  rw [suffixComplIdx, dite_eq_right hjn, hc]

/-- Region computation: an output-above index enumerates the untouched output
wires above the suffix window. -/
private theorem suffixComplIdx_of_ge_ge (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))))
    (hjn : ¬((j : Nat) < n + 1 - m)) (hjk : k ≤ (j : Nat) - (n + 1 - m)) :
    suffixComplIdx k m hkm j
      = Fin.natAdd (n + 2) (⟨(j : Nat) - (n + 1 - m) + (m + 1), by omega⟩ : Fin (n + 2)) := by
  have hc : compOut k m (⟨(j : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m))
      = (⟨(j : Nat) - (n + 1 - m) + (m + 1), by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    show (compOut k m (⟨(j : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m)) : Nat)
        = (j : Nat) - (n + 1 - m) + (m + 1)
    rw [compOut_val]
    exact ite_eq_right (by simpa using Nat.not_lt.2 hjk)
  rw [suffixComplIdx, dite_eq_right hjn, hc]

/-- The four-region enumeration is strictly increasing. -/
private theorem suffixComplIdx_lt (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    {j₁ j₂ : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))}
    (h : (j₁ : Nat) < (j₂ : Nat)) :
    (suffixComplIdx k m hkm j₁ : Nat) < (suffixComplIdx k m hkm j₂ : Nat) := by
  have hj₁ : (j₁ : Nat) < (n + 2 + (n + 2)) - ((m + 1) + (m + 1)) := j₁.isLt
  have hj₂ : (j₂ : Nat) < (n + 2 + (n + 2)) - ((m + 1) + (m + 1)) := j₂.isLt
  simp only [suffixComplIdx_val]
  split_ifs <;> omega

/-- The four-region enumeration is injective. -/
private theorem suffixComplIdx_injective (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Function.Injective (suffixComplIdx (n := n) k m hkm) := by
  intro j₁ j₂ heq
  have hv : (suffixComplIdx k m hkm j₁ : Nat) = (suffixComplIdx k m hkm j₂ : Nat) :=
    congrArg Fin.val heq
  rcases Nat.lt_trichotomy (j₁ : Nat) (j₂ : Nat) with h | h | h
  · exact absurd hv (Nat.ne_of_lt (suffixComplIdx_lt k m hkm h))
  · exact Fin.ext h
  · exact absurd hv.symm (Nat.ne_of_lt (suffixComplIdx_lt k m hkm h))

/-- Every output-side connected position is a `suffixConnIdx` value. -/
private theorem suffixConnIdx_surj_O (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (p : Fin (n + 2 + (n + 2))) (h1 : n + 2 + k ≤ (p : Nat)) (h2 : (p : Nat) ≤ n + 2 + k + m) :
    ∃ t : Fin (m + 1), suffixConnIdx k m hkm (Fin.castAdd (m + 1) t) = p := by
  refine ⟨⟨(p : Nat) - (n + 2) - k, by omega⟩, ?_⟩
  apply Fin.ext
  show (suffixConnIdx k m hkm
      (Fin.castAdd (m + 1) ⟨(p : Nat) - (n + 2) - k, by omega⟩) : Nat) = (p : Nat)
  rw [suffixConnIdx_castAdd]
  simp only [Fin.val_natAdd]
  omega

/-- Every input-side connected position is a `suffixConnIdx` value. -/
private theorem suffixConnIdx_surj_I (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (p : Fin (n + 2 + (n + 2))) (h1 : k + 1 ≤ (p : Nat)) (h2 : (p : Nat) ≤ k + m + 1) :
    ∃ t : Fin (m + 1), suffixConnIdx k m hkm (Fin.natAdd (m + 1) t) = p := by
  refine ⟨⟨(p : Nat) - (k + 1), by omega⟩, ?_⟩
  apply Fin.ext
  show (suffixConnIdx k m hkm
      (Fin.natAdd (m + 1) ⟨(p : Nat) - (k + 1), by omega⟩) : Nat) = (p : Nat)
  rw [suffixConnIdx_natAdd]
  simp only [Fin.val_castAdd]
  omega

/-- The four-region enumeration avoids the connected positions. -/
private theorem suffixConnIdx_ne_suffixComplIdx (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (i : Fin (m + 1 + (m + 1)))
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) :
    suffixConnIdx k m hkm i ≠ suffixComplIdx k m hkm j := by
  have hj : (j : Nat) < (n + 2 + (n + 2)) - ((m + 1) + (m + 1)) := j.isLt
  intro heq
  have hv := congrArg Fin.val heq
  simp only [suffixComplIdx_val] at hv
  induction i using Fin.addCases with
  | left t =>
    have ht : (t : Nat) < m + 1 := t.isLt
    simp only [suffixConnIdx_castAdd, Fin.val_natAdd] at hv
    split_ifs at hv <;> omega
  | right t =>
    have ht : (t : Nat) < m + 1 := t.isLt
    simp only [suffixConnIdx_natAdd, Fin.val_castAdd] at hv
    split_ifs at hv <;> omega

/-- The four-region enumeration covers every private position. -/
private theorem exists_suffixComplIdx (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (p : Fin (n + 2 + (n + 2)))
    (hp : ∀ i, suffixConnIdx k m hkm i ≠ p) :
    ∃ j, suffixComplIdx k m hkm j = p := by
  have hpv : (p : Nat) < n + 2 + (n + 2) := p.isLt
  rcases Nat.lt_or_ge (p : Nat) (n + 2) with hIO | hIO
  · rcases Nat.lt_or_ge (p : Nat) (k + 1) with h1 | h1
    · refine ⟨⟨(p : Nat), by omega⟩, ?_⟩
      rw [suffixComplIdx_of_lt_le k m hkm _
        (by show (p : Nat) < n + 1 - m; omega) (by show (p : Nat) ≤ k; omega)]
      exact Fin.ext (by simp only [Fin.val_castAdd])
    rcases Nat.lt_or_ge (p : Nat) (k + m + 2) with h2 | h2
    · obtain ⟨t, ht⟩ := suffixConnIdx_surj_I k m hkm p (by omega) (by omega)
      exact absurd ht (hp (Fin.natAdd (m + 1) t))
    · refine ⟨⟨(p : Nat) - (m + 1), by omega⟩, ?_⟩
      rw [suffixComplIdx_of_lt_gt k m hkm _
        (by show (p : Nat) - (m + 1) < n + 1 - m; omega)
        (by show k < (p : Nat) - (m + 1); omega)]
      exact Fin.ext (by simp only [Fin.val_castAdd]; omega)
  · rcases Nat.lt_or_ge ((p : Nat) - (n + 2)) k with h1 | h1
    · refine ⟨⟨(n + 1 - m) + ((p : Nat) - (n + 2)), by omega⟩, ?_⟩
      rw [suffixComplIdx_of_ge_lt k m hkm _
        (by show ¬((n + 1 - m) + ((p : Nat) - (n + 2)) < n + 1 - m); omega)
        (by show (n + 1 - m) + ((p : Nat) - (n + 2)) - (n + 1 - m) < k; omega)]
      exact Fin.ext (by simp only [Fin.val_natAdd]; omega)
    rcases Nat.lt_or_ge ((p : Nat) - (n + 2)) (k + m + 1) with h2 | h2
    · obtain ⟨t, ht⟩ := suffixConnIdx_surj_O k m hkm p (by omega) (by omega)
      exact absurd ht (hp (Fin.castAdd (m + 1) t))
    · refine ⟨⟨(n + 1 - m) + ((p : Nat) - (n + 2) - (m + 1)), by omega⟩, ?_⟩
      rw [suffixComplIdx_of_ge_ge k m hkm _
        (by show ¬((n + 1 - m) + ((p : Nat) - (n + 2) - (m + 1)) < n + 1 - m); omega)
        (by show k ≤ (n + 1 - m) + ((p : Nat) - (n + 2) - (m + 1)) - (n + 1 - m); omega)]
      exact Fin.ext (by simp only [Fin.val_natAdd]; omega)

/-- `finRange` is strictly increasing: all pairs are ordered by `<`. -/
private theorem finRange_lt_pairwise : ∀ N : Nat,
    List.Pairwise (fun a b : Fin N => a < b) (List.finRange N)
  | 0 => List.Pairwise.nil
  | N + 1 => by
    rw [List.finRange_succ]
    refine List.Pairwise.cons (fun x hx => ?_) ?_
    · simp only [List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact Fin.succ_pos y
    · exact List.Pairwise.map Fin.succ
        (fun a b h => by show a.val.succ < b.val.succ; exact Nat.succ_lt_succ h)
        (finRange_lt_pairwise N)

/-- The sort-based complement embedding of the suffix connection agrees with
the explicit four-region enumeration. -/
theorem suffixComplEmb (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (hι : Function.Injective (suffixConnIdx k m hkm))
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) :
    complEmb (suffixConnIdx k m hkm) hι j = suffixComplIdx k m hkm j := by
  have hnd : (List.map (suffixComplIdx k m hkm) (List.finRange _)).Nodup :=
    (List.nodup_finRange _).map (suffixComplIdx_injective k m hkm)
  have hlist : (List.map (suffixComplIdx k m hkm) (List.finRange _)).toFinset
      = complFinset (suffixConnIdx k m hkm) hι := by
    ext p
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, mem_complFinset]
    constructor
    · rintro ⟨q, -, hq⟩ hall
      intro heq
      exact suffixConnIdx_ne_suffixComplIdx k m hkm hall q (heq.trans hq.symm)
    · intro hp
      obtain ⟨q, hq⟩ := exists_suffixComplIdx k m hkm p hp
      exact ⟨q, trivial, hq⟩
  have hpair : List.Pairwise (fun a b : Fin (n + 2 + (n + 2)) => a ≤ b)
      (List.map (suffixComplIdx k m hkm) (List.finRange _)) :=
    List.Pairwise.map (suffixComplIdx k m hkm)
      (fun a b h => Fin.le_of_lt (suffixComplIdx_lt k m hkm h)) (finRange_lt_pairwise _)
  have hsort : (complFinset (suffixConnIdx k m hkm) hι).sort (fun a b => a ≤ b)
      = List.map (suffixComplIdx k m hkm) (List.finRange _) := by
    rw [← hlist]
    exact (List.toFinset_sort _ hnd).mpr hpair
  simp only [complEmb, Finset.orderEmbOfFin_apply, hsort]
  simp

end SuffixRegions

/-! ## The composite comb -/

section SuffixCompDef

variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Region computation of the private wire family: an input-region index
carries the composite input wire's type. -/
theorem complFam₂_eq_lt (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) (h : (j : Nat) < n + 1 - m) :
    (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j
      = I (compIn k m ⟨(j : Nat), by omega⟩) := by
  show (append I O) (complEmb (suffixConnIdx k m hkm)
      (suffixMatch (I := I) (O := O) k m hkm).hι₂ j) = _
  rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ j]
  simp only [suffixComplIdx, dite_eq_left h, append_castAdd]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Region computation of the private wire family: an output-region index
carries the composite output wire's type. -/
theorem complFam₂_eq_ge (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) (h : ¬((j : Nat) < n + 1 - m)) :
    (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j
      = O (compOut k m ⟨(j : Nat) - (n + 1 - m), by omega⟩) := by
  show (append I O) (complEmb (suffixConnIdx k m hkm)
      (suffixMatch (I := I) (O := O) k m hkm).hι₂ j) = _
  rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ j]
  simp only [suffixComplIdx, dite_eq_right h, append_natAdd]

/-- The private configuration of the outer comb induced by a point of the
composite comb's Choi space: the four untouched regions are read off the
composite input and output tuples. -/
def complPack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j))
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) :
    (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j :=
  if h : (j : Nat) < n + 1 - m then
    cast (complFam₂_eq_lt (I := I) (O := O) k m hkm j h).symm (u ⟨(j : Nat), by omega⟩)
  else
    cast (complFam₂_eq_ge (I := I) (O := O) k m hkm j h).symm
      (v ⟨(j : Nat) - (n + 1 - m), by omega⟩)

/-- The composite comb of the suffix composition: the link product of the
inner comb's and the outer comb's Choi matrices over the shared suffix
wires, packaged on the composite comb's Choi space. -/
noncomputable def suffixComp (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))) :
    CMatrix (Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j))) :=
  Matrix.of fun p q => (suffixMatch (I := I) (O := O) k m hkm).linkProduct
    (XFlat (I := I) (O := O) k m hkm X) (JFlat (I := I) (O := O) J)
    ((splitAppendEquiv (suffixMatch (I := I) (O := O) k m hkm).complFam₁
        (suffixMatch (I := I) (O := O) k m hkm).complFam₂).symm
      ((fun j => absurd j.isLt (by simp only [suffixMatch]; omega)), complPack (I := I) (O := O) k m hkm p.1 p.2))
    ((splitAppendEquiv (suffixMatch (I := I) (O := O) k m hkm).complFam₁
        (suffixMatch (I := I) (O := O) k m hkm).complFam₂).symm
      ((fun j => absurd j.isLt (by simp only [suffixMatch]; omega)), complPack (I := I) (O := O) k m hkm q.1 q.2))

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- Entrywise form of the composite comb: each entry is the contraction of
the inner and outer Choi matrices over the shared suffix wires, with the
private configuration induced by the composite Choi-space point. -/
theorem suffixComp_apply (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (u u' : Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j))) :
    suffixComp (I := I) (O := O) k m hkm J X u u' =
      ∑ z : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i,
        ∑ z' : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i,
          X ((XFlatEquiv (I := I) (O := O) k m hkm).symm
              ((suffixMatch (I := I) (O := O) k m hkm).read₁
                ((fun j => absurd j.isLt (by simp only [suffixMatch]; omega)), z')))
            ((XFlatEquiv (I := I) (O := O) k m hkm).symm
              ((suffixMatch (I := I) (O := O) k m hkm).read₁
                ((fun j => absurd j.isLt (by simp only [suffixMatch]; omega)), z))) *
          J (splitAppendEquiv I O
              ((suffixMatch (I := I) (O := O) k m hkm).read₂ z'
                (complPack (I := I) (O := O) k m hkm u.1 u.2)))
            (splitAppendEquiv I O
              ((suffixMatch (I := I) (O := O) k m hkm).read₂ z
                (complPack (I := I) (O := O) k m hkm u'.1 u'.2))) := by
  have h := WireMatch.linkProduct_apply (suffixMatch (I := I) (O := O) k m hkm)
    (XFlat (I := I) (O := O) k m hkm X) (JFlat (I := I) (O := O) J)
    (fun j => absurd j.isLt (by simp only [suffixMatch]; omega)) (fun j => absurd j.isLt (by simp only [suffixMatch]; omega))
    (complPack (I := I) (O := O) k m hkm u.1 u.2)
    (complPack (I := I) (O := O) k m hkm u'.1 u'.2)
  exact h

/-! ### Region computation of the packing -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Computing the packing at an input-region index: the entry is the composite
input value read at the region's index, cast along the region equation. -/
private theorem complPack_lt (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j))
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) (h : (j : Nat) < n + 1 - m) :
    complPack (I := I) (O := O) k m hkm u v j
      = cast (complFam₂_eq_lt (I := I) (O := O) k m hkm j h).symm (u ⟨(j : Nat), by omega⟩) := by
  rw [complPack, dite_eq_left h]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Computing the packing at an output-region index: the entry is the composite
output value read at the region's index, cast along the region equation. -/
private theorem complPack_ge (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j))
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) (h : ¬((j : Nat) < n + 1 - m)) :
    complPack (I := I) (O := O) k m hkm u v j
      = cast (complFam₂_eq_ge (I := I) (O := O) k m hkm j h).symm
          (v ⟨(j : Nat) - (n + 1 - m), by omega⟩) := by
  rw [complPack, dite_eq_right h]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- j'-parametrized region equation for the output region: the private wire
at the shifted index `n + 1 - m + j'` carries the composite output wire
`j'`'s type.  Unlike `complFam₂_eq_ge`, the right-hand side mentions no
unnormalized arithmetic on the index. -/
theorem complFam₂_eq_ge' (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (j' : Fin (n + 1 - m)) :
    (suffixMatch (I := I) (O := O) k m hkm).complFam₂ ⟨(n + 1 - m) + (j' : Nat),
      by simp only [suffixMatch]; omega⟩
      = O (compOut k m j') := by
  have hj' : (j' : Nat) < n + 1 - m := j'.isLt
  show (append I O) (complEmb (suffixConnIdx k m hkm)
      (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨(n + 1 - m) + (j' : Nat), by omega⟩) = _
  rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂
      ⟨(n + 1 - m) + (j' : Nat), by omega⟩]
  simp only [suffixComplIdx,
    dite_eq_right (by show ¬((n + 1 - m) + (j' : Nat) < n + 1 - m); omega), append_natAdd]
  have hid : (⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m)) = j' := by
    apply Fin.ext
    show (n + 1 - m) + (j' : Nat) - (n + 1 - m) = (j' : Nat)
    omega
  exact congrArg (fun t : Fin (n + 1 - m) => O (compOut k m t)) hid

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Computing the packing at a shifted output-region index, parametrized by the
composite output index itself: the entry is the composite output value at
`j'`, cast along the primed region equation. -/
private theorem complPack_ge' (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j))
    (j' : Fin (n + 1 - m)) :
    complPack (I := I) (O := O) k m hkm u v ⟨(n + 1 - m) + (j' : Nat), by omega⟩
      = cast (complFam₂_eq_ge' (I := I) (O := O) k m hkm j').symm (v j') := by
  have hge : ¬((n + 1 - m) + (j' : Nat) < n + 1 - m) := by omega
  have hid : (⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m)) = j' := by
    apply Fin.ext
    show (n + 1 - m) + (j' : Nat) - (n + 1 - m) = (j' : Nat)
    omega
  rw [complPack_ge (I := I) (O := O) k m hkm u v ⟨(n + 1 - m) + (j' : Nat), by omega⟩ hge]
  have hX := congrArg (fun t : Fin (n + 1 - m) => O (compOut k m t)) hid
  have hmid := (complFam₂_eq_ge' (I := I) (O := O) k m hkm j').symm
  have hcc := cast_congrArg_apply (ι := Fin (n + 1 - m))
    (X := fun t => O (compOut k m t)) hid v
  have s1 : cast (complFam₂_eq_ge (I := I) (O := O) k m hkm
          ⟨(n + 1 - m) + (j' : Nat), by omega⟩ hge).symm
          (v ⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩)
      = cast (hX.trans hmid) (v ⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩) := rfl
  have s2 : cast (hX.trans hmid) (v ⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩)
      = cast hmid (v j') :=
    (cast2 hX hmid (v ⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩)).symm.trans
      (congrArg (cast hmid) hcc)
  exact s1.trans s2

/-- The inverse of the packing: a private configuration is read back into a
composite input and output tuple through the region equations. -/
def complUnpack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (w : ∀ j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))),
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j) :
    Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j)) :=
  ((fun j' => cast (complFam₂_eq_lt (I := I) (O := O) k m hkm ⟨(j' : Nat), by omega⟩
        (by show (j' : Nat) < n + 1 - m; omega)) (w ⟨(j' : Nat), by omega⟩)),
    (fun j' => cast (complFam₂_eq_ge' (I := I) (O := O) k m hkm j')
      (w ⟨(n + 1 - m) + (j' : Nat), by omega⟩)))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Computing the unpacking's input component. -/
private theorem complUnpack_one (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (w : ∀ j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))),
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j)
    (j' : Fin (n + 1 - m)) :
    (complUnpack (I := I) (O := O) k m hkm w).1 j'
      = cast (complFam₂_eq_lt (I := I) (O := O) k m hkm ⟨(j' : Nat), by omega⟩
          (by show (j' : Nat) < n + 1 - m; omega)) (w ⟨(j' : Nat), by omega⟩) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Computing the unpacking's output component. -/
private theorem complUnpack_two (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (w : ∀ j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))),
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j)
    (j' : Fin (n + 1 - m)) :
    (complUnpack (I := I) (O := O) k m hkm w).2 j'
      = cast (complFam₂_eq_ge' (I := I) (O := O) k m hkm j')
          (w ⟨(n + 1 - m) + (j' : Nat), by omega⟩) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Unpacking the packing returns the original composite point, componentwise. -/
private theorem complUnpack_complPack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j)) :
    complUnpack (I := I) (O := O) k m hkm (complPack (I := I) (O := O) k m hkm u v) = (u, v) := by
  apply Prod.ext
  · funext j'
    have hj' : (j' : Nat) < n + 1 - m := j'.isLt
    rw [complUnpack_one]
    simp only [complPack]
    split
    · exact cast_cast_cancel _ (u j')
    · next hge => exact absurd (show (j' : Nat) < n + 1 - m from j'.isLt) hge
  · funext j'
    have hj' : (j' : Nat) < n + 1 - m := j'.isLt
    rw [complUnpack_two]
    have hu2 := complPack_ge (I := I) (O := O) k m hkm u v ⟨(n + 1 - m) + (j' : Nat), by omega⟩
      (by show ¬((n + 1 - m) + (j' : Nat) < n + 1 - m); omega)
    rw [hu2]
    have hj2 : (⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m)) = j' := by
      apply Fin.ext
      show (n + 1 - m) + (j' : Nat) - (n + 1 - m) = (j' : Nat)
      omega
    refine (cast_comp' (congrArg (fun t : Fin (n + 1 - m) => O (compOut k m t)) hj2.symm)
      (complFam₂_eq_ge' (I := I) (O := O) k m hkm j')
      (complFam₂_eq_ge (I := I) (O := O) k m hkm ⟨(n + 1 - m) + (j' : Nat), by omega⟩
        (by show ¬((n + 1 - m) + (j' : Nat) < n + 1 - m); omega))
      (v ⟨(n + 1 - m) + (j' : Nat) - (n + 1 - m), by omega⟩)).trans ?_
    exact cast_congrArg_apply (ι := Fin (n + 1 - m))
      (X := fun j => O (compOut k m j)) hj2 v

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Packing the unpacking returns the original private configuration, by
regions. -/
private theorem complPack_complUnpack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (w : ∀ j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))),
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j) :
    complPack (I := I) (O := O) k m hkm (complUnpack (I := I) (O := O) k m hkm w).1
        (complUnpack (I := I) (O := O) k m hkm w).2 = w := by
  funext j
  by_cases hj : (j : Nat) < n + 1 - m
  · rw [complPack_lt _ _ _ _ _ j hj, complUnpack_one]
    exact cast_cast_cancel' _ (w j)
  · rw [complPack_ge _ _ _ _ _ j hj]
    have hu := complUnpack_two (I := I) (O := O) k m hkm w
      ⟨(j : Nat) - (n + 1 - m), by omega⟩
    rw [hu]
    have hjw : (⟨(n + 1 - m) + ((j : Nat) - (n + 1 - m)), by omega⟩ :
        Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))) = j := by
      apply Fin.ext
      show (n + 1 - m) + ((j : Nat) - (n + 1 - m)) = (j : Nat)
      omega
    have hshift : (suffixMatch (I := I) (O := O) k m hkm).complFam₂
        ((⟨(n + 1 - m) + ((j : Nat) - (n + 1 - m)), by omega⟩ :
          Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1)))))
        = (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j :=
      congrArg ((suffixMatch (I := I) (O := O) k m hkm).complFam₂) hjw
    refine (cast_comp hshift (complFam₂_eq_ge (I := I) (O := O) k m hkm j hj)
      (complFam₂_eq_ge' (I := I) (O := O) k m hkm ⟨(j : Nat) - (n + 1 - m), by omega⟩)
      (w ⟨(n + 1 - m) + ((j : Nat) - (n + 1 - m)), by omega⟩)).trans ?_
    exact cast_congrArg_apply
      (ι := Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))))
      (X := fun i => (suffixMatch (I := I) (O := O) k m hkm).complFam₂ i) hjw w

/-- The region packing as an equivalence between the composite comb's Choi
space and the outer comb's private configurations. -/
private def complPackEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    (∀ j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))),
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j) ≃
      Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j)) where
  toFun := complUnpack (I := I) (O := O) k m hkm
  invFun := fun p => complPack (I := I) (O := O) k m hkm p.1 p.2
  left_inv := complPack_complUnpack (I := I) (O := O) k m hkm
  right_inv := fun p => complUnpack_complPack (I := I) (O := O) k m hkm p.1 p.2

/-! ### The space packing equivalence and positive semidefiniteness -/

private instance {m k : ℕ} {W₁ : Fin m → Type u} {W₂ : Fin k → Type u}
    [∀ i, DecidableEq (W₁ i)] [∀ j, DecidableEq (W₂ j)] (i : Fin (m + k)) :
    DecidableEq (append W₁ W₂ i) := by
  induction i using Fin.addCases with
  | left i => rw [append_castAdd]; infer_instance
  | right j => rw [append_natAdd]; infer_instance

/-- The packing of a composite Choi-space point into the outer comb's full
private configuration space. -/
def spacePack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (p : Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j))) :
    ∀ i, append (suffixMatch (I := I) (O := O) k m hkm).complFam₁
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ i :=
  (splitAppendEquiv
      (suffixMatch (I := I) (O := O) k m hkm).complFam₁
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂).symm
    ((fun j => absurd j.isLt (by simp only [suffixMatch]; omega)),
      complPack (I := I) (O := O) k m hkm p.1 p.2)

/-- The inverse packing: reading a private configuration back into a composite
Choi-space point. -/
def spaceUnpack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (P : ∀ i, append (suffixMatch (I := I) (O := O) k m hkm).complFam₁
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ i) :
    Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j)) :=
  complUnpack (I := I) (O := O) k m hkm
    ((splitAppendEquiv
        (suffixMatch (I := I) (O := O) k m hkm).complFam₁
        (suffixMatch (I := I) (O := O) k m hkm).complFam₂ P).2)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Unpacking the packing returns the original composite point. -/
theorem spaceUnpack_spacePack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (p : Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j))) :
    spaceUnpack (I := I) (O := O) k m hkm (spacePack (I := I) (O := O) k m hkm p) = p := by
  have h := Equiv.apply_symm_apply (splitAppendEquiv
      (suffixMatch (I := I) (O := O) k m hkm).complFam₁
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂)
    ((fun j => absurd j.isLt (by simp only [suffixMatch]; omega)),
      complPack (I := I) (O := O) k m hkm p.1 p.2)
  unfold spacePack spaceUnpack
  rw [h]
  exact complUnpack_complPack (I := I) (O := O) k m hkm p.1 p.2

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Packing the unpacking returns the original private configuration. -/
theorem spacePack_spaceUnpack (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (P : ∀ i, append (suffixMatch (I := I) (O := O) k m hkm).complFam₁
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂ i) :
    spacePack (I := I) (O := O) k m hkm (spaceUnpack (I := I) (O := O) k m hkm P) = P := by
  rw [spacePack, spaceUnpack]
  have hsa := splitAppendEquiv_symm_apply
      (suffixMatch (I := I) (O := O) k m hkm).complFam₁
      (suffixMatch (I := I) (O := O) k m hkm).complFam₂
      (fun j => absurd j.isLt (by simp only [suffixMatch]; omega))
      (complPack (I := I) (O := O) k m hkm
        (complUnpack (I := I) (O := O) k m hkm
          ((splitAppendEquiv
              (suffixMatch (I := I) (O := O) k m hkm).complFam₁
              (suffixMatch (I := I) (O := O) k m hkm).complFam₂ P).2)).1
        (complUnpack (I := I) (O := O) k m hkm
          ((splitAppendEquiv
              (suffixMatch (I := I) (O := O) k m hkm).complFam₁
              (suffixMatch (I := I) (O := O) k m hkm).complFam₂ P).2)).2)
  rw [hsa]
  funext i
  induction i using Fin.addCases with
  | left j => exact absurd j.isLt (by simp only [suffixMatch]; omega)
  | right j =>
      simp only [Fin.addCases_right]
      have hcu := complPack_complUnpack (I := I) (O := O) k m hkm
        ((splitAppendEquiv
            (suffixMatch (I := I) (O := O) k m hkm).complFam₁
            (suffixMatch (I := I) (O := O) k m hkm).complFam₂ P).2)
      rw [hcu, splitAppendEquiv_apply]
      exact cast_cast_cancel' _ _

/-- The space packing as an equivalence between the composite comb's Choi
space and the outer comb's private configuration space. -/
def spacePackEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j)) ≃
      (∀ i, append (suffixMatch (I := I) (O := O) k m hkm).complFam₁
        (suffixMatch (I := I) (O := O) k m hkm).complFam₂ i) where
  toFun := spacePack (I := I) (O := O) k m hkm
  invFun := spaceUnpack (I := I) (O := O) k m hkm
  left_inv := spaceUnpack_spacePack (I := I) (O := O) k m hkm
  right_inv := spacePack_spaceUnpack (I := I) (O := O) k m hkm

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- The suffix composition is the raw suffix link product read through the
space packing equivalence. -/
theorem suffixComp_eq_reindex (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))) :
    suffixComp (I := I) (O := O) k m hkm J X =
      matReindex (spacePackEquiv (I := I) (O := O) k m hkm).symm
        ((suffixMatch (I := I) (O := O) k m hkm).linkProduct
          (XFlat (I := I) (O := O) k m hkm X) (JFlat (I := I) (O := O) J)) := rfl

/-- The suffix composition of positive semidefinite factors is positive
semidefinite: the link product preserves semidefiniteness and the space
packing is a matrix reindexing. -/
theorem suffixComp_posSemidef (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (hJ : J.PosSemidef) (hX : X.PosSemidef) :
    (suffixComp (I := I) (O := O) k m hkm J X).PosSemidef := by
  rw [suffixComp_eq_reindex]
  exact matReindex_posSemidef _
    (linkProduct_posSemidef (matReindex_posSemidef _ (matReindex_posSemidef _ hX))
      (matReindex_posSemidef _ (matReindex_posSemidef _ hJ)))

end SuffixCompDef

/-! ## Normalization induction — index arithmetic -/

section CompositionClosure

/-- An empty final output makes a peel witness vanish whenever the final
input has a value. No other wire needs to be inhabited. -/
private theorem peel_zero_of_empty_output {r : Nat} {A B : Fin (r + 1) → Type u}
    [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)]
    (J : CMatrix (Space A B))
    (K : CMatrix (Space (fun j : Fin r => A j.castSucc) (fun j => B j.castSucc)))
    (hpeel : ∀ (i i' : ∀ j, A j) (o o' : ∀ j : Fin r, B j.castSucc),
      (∑ z : B (Fin.last r), J (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
        if i (Fin.last r) = i' (Fin.last r) then
          K ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o') else 0)
    (hE : IsEmpty (B (Fin.last r))) (a : A (Fin.last r))
    (p q : Space (fun j : Fin r => A j.castSucc) (fun j => B j.castSucc)) :
    K p q = 0 := by
  have h := hpeel (Fin.snoc p.1 a) (Fin.snoc q.1 a) p.2 q.2
  have hz : (∑ z : B (Fin.last r),
      J (Fin.snoc p.1 a, Fin.snoc p.2 z) (Fin.snoc q.1 a, Fin.snoc q.2 z)) = 0 :=
    Finset.sum_eq_zero fun z _ => hE.elim z
  simpa only [hz, Fin.snoc_last, Fin.snoc_castSucc, ite_true, Prod.mk.eta] using h.symm

/-- A normalized one-tooth window cannot send an inhabited input wire to an
empty output wire. This derives the needed value locally from normalization. -/
private theorem normalized_one_output_nonempty {A B : Fin 1 → Type u}
    [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    {X : CMatrix (Space A B)} (hX : Normalized A B X)
    (a : A (Fin.last 0)) : Nonempty (B (Fin.last 0)) := by
  rcases isEmpty_or_nonempty (B (Fin.last 0)) with hE | hNE
  · obtain ⟨-, K, hK, hpeel⟩ := hX
    have hzero := peel_zero_of_empty_output X K hpeel hE a
      ((fun j => Fin.elim0 j), (fun j => Fin.elim0 j))
      ((fun j => Fin.elim0 j), (fun j => Fin.elim0 j))
    rw [(normalized_zero _ _ K).mp hK, Matrix.one_apply, ite_eq_left rfl] at hzero
    exact (one_ne_zero hzero).elim
  · exact hNE

variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The composite tooth index in successor form, so that the composite wire
count is directly a recursion pattern for `Normalized`. -/
def compIdxEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Fin (n - m + 1) ≃ Fin (n + 1 - m) :=
  finCongr (by omega : n - m + 1 = n + 1 - m)

@[simp] private theorem compIdxEquiv_val (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin (n - m + 1)) :
    (compIdxEquiv (n := n) k m hkm j : Nat) = (j : Nat) := by
  simp only [compIdxEquiv, finCongr_apply, Fin.val_cast]

/-- The composite input index map in successor form. -/
def compInS (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (j : Fin (n - m + 1)) : Fin (n + 2) :=
  compIn k m (compIdxEquiv (n := n) k m hkm j)

/-- The composite output index map in successor form. -/
def compOutS (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (j : Fin (n - m + 1)) : Fin (n + 2) :=
  compOut k m (compIdxEquiv (n := n) k m hkm j)

@[simp] private theorem compInS_val (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin (n - m + 1)) :
    (compInS (n := n) k m hkm j : Nat) =
      if (j : Nat) ≤ k then (j : Nat) else (j : Nat) + (m + 1) := by
  simp only [compInS, compIn_val, compIdxEquiv_val]

@[simp] private theorem compOutS_val (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin (n - m + 1)) :
    (compOutS (n := n) k m hkm j : Nat) =
      if (j : Nat) < k then (j : Nat) else (j : Nat) + (m + 1) := by
  simp only [compOutS, compOut_val, compIdxEquiv_val]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The composite's last tooth output is the outer comb's last output wire,
independently of the window position. -/
private theorem compOutS_last (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    compOutS (n := n) k m hkm (Fin.last (n - m)) = Fin.last (n + 1) := by
  apply Fin.ext
  simp only [compOutS_val, Fin.val_last]
  split <;> omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- In the non-boundary case the composite's last tooth input is the outer
comb's last input wire. -/
private theorem compInS_last (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (hk : k < n - m) :
    compInS (n := n) k m hkm (Fin.last (n - m)) = Fin.last (n + 1) := by
  apply Fin.ext
  simp only [compInS_val, Fin.val_last]
  split <;> omega

/-! ### The successor-form composite matrix -/

/-- The family equivalence carrying the successor-form composite point to the
plain-form suffix composition point. -/
def spaceIdxEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    Space (fun j => I (compInS k m hkm j)) (fun j => O (compOutS k m hkm j)) ≃
      Space (fun j => I (compIn k m j)) (fun j => O (compOut k m j)) :=
  (Equiv.piCongrLeft (fun j => I (compIn k m j)) (compIdxEquiv k m hkm)).prodCongr
    (Equiv.piCongrLeft (fun j => O (compOut k m j)) (compIdxEquiv k m hkm))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The components of the forward family equivalence. -/
private theorem spaceIdxEquiv_apply (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : Space (fun j => I (compInS k m hkm j)) (fun j => O (compOutS k m hkm j))) :
    spaceIdxEquiv (I := I) (O := O) k m hkm u =
      ((fun j => u.1 ((compIdxEquiv (n := n) k m hkm).symm j)),
        (fun j => u.2 ((compIdxEquiv (n := n) k m hkm).symm j))) := rfl

/-- The suffix composition in successor form: the composite comb indexed so
that its wire count is a direct recursion pattern for `Normalized`. -/
noncomputable def suffixCompS (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))) :
    CMatrix (Space (fun j => I (compInS k m hkm j)) (fun j => O (compOutS k m hkm j))) :=
  WireFam.matReindex (spaceIdxEquiv (I := I) (O := O) k m hkm).symm
    (suffixComp (I := I) (O := O) k m hkm J X)

/-! ### Case A configuration arithmetic: the last-output position -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The inverse successor-form index equivalence preserves values. -/
private theorem compIdxEquiv_symm_val (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (j : Fin (n + 1 - m)) :
    ((compIdxEquiv (n := n) k m hkm).symm j : Nat) = (j : Nat) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The last private index of the packing carries the composite's last output
value. -/
private theorem complPack_last (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j)) :
    complPack (I := I) (O := O) k m hkm u v ⟨(n + 1 - m) + (n - m), by omega⟩ =
      cast (complFam₂_eq_ge' (I := I) (O := O) k m hkm ⟨n - m, by omega⟩).symm
        (v ⟨n - m, by omega⟩) := by
  have hge : complPack (I := I) (O := O) k m hkm u v ⟨(n + 1 - m) + (n - m), by omega⟩ =
      cast (complFam₂_eq_ge (I := I) (O := O) k m hkm ⟨(n + 1 - m) + (n - m), by omega⟩
          (by show ¬((n + 1 - m) + (n - m) < n + 1 - m); omega)).symm
        (v ⟨(n + 1 - m) + (n - m) - (n + 1 - m), by omega⟩) :=
    complPack_ge (I := I) (O := O) k m hkm u v ⟨(n + 1 - m) + (n - m), by omega⟩
      (by show ¬((n + 1 - m) + (n - m) < n + 1 - m); omega)
  rw [hge]
  have hj2 : (⟨(n + 1 - m) + (n - m) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m))
      = ⟨n - m, by omega⟩ := by
    apply Fin.ext; show (n + 1 - m) + (n - m) - (n + 1 - m) = n - m; omega
  have hc := cast_congrArg_apply (ι := Fin (n + 1 - m))
    (X := fun t => O (compOut k m t)) hj2 v
  rw [← hc]
  exact Eq.symm (cast_comp
    ((complFam₂_eq_ge (I := I) (O := O) k m hkm ⟨(n + 1 - m) + (n - m), by omega⟩
        (by show ¬((n + 1 - m) + (n - m) < n + 1 - m); omega)).symm)
    (complFam₂_eq_ge' (I := I) (O := O) k m hkm ⟨n - m, by omega⟩)
    (congrArg (fun t : Fin (n + 1 - m) => O (compOut k m t)) hj2)
    (v ⟨(n + 1 - m) + (n - m) - (n + 1 - m), by omega⟩))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The packing is insensitive to changes of the output component away from
the last tooth. -/
private theorem complPack_congr (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (u : ∀ j, I (compIn k m j)) (v v' : ∀ j, O (compOut k m j))
    (hv : ∀ t : Fin (n + 1 - m), (t : Nat) ≠ n - m → v t = v' t)
    (j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))))
    (hj : (j : Nat) ≠ (n + 1 - m) + (n - m)) :
    complPack (I := I) (O := O) k m hkm u v j = complPack (I := I) (O := O) k m hkm u v' j := by
  by_cases h : (j : Nat) < n + 1 - m
  · rw [complPack_lt _ _ _ _ _ j h, complPack_lt _ _ _ _ _ j h]
  · rw [complPack_ge _ _ _ _ _ j h, complPack_ge _ _ _ _ _ j h]
    rw [(hv ⟨(j : Nat) - (n + 1 - m), by omega⟩
      (by show (j : Nat) - (n + 1 - m) ≠ n - m; omega))]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Triple cast collapse along a composed type equation. -/
private theorem cast3 {A B C D : Type u} (h1 : A = B) (h2 : B = C) (h3 : C = D) (x : A) :
    cast h3 (cast h2 (cast h1 x)) = cast (h1.trans (h2.trans h3)) x := by
  cases h1; cases h2; cases h3; rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The composite's last output wire is the outer comb's last output wire. -/
private theorem compOut_last (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    compOut (n := n) k m ⟨n - m, by omega⟩ = Fin.last (n + 1) :=
  compOutS_last (n := n) k m hkm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- In the non-boundary case the composite's last input wire is the outer
comb's last input wire. -/
private theorem compIn_last (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (hk : k < n - m) :
    compIn (n := n) k m ⟨n - m, by omega⟩ = Fin.last (n + 1) :=
  compInS_last (n := n) k m hkm hk

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Position bridge: the last private output index enumerates the outer comb's
last output wire. -/
private theorem complEmb_lastOut (k m : Nat) (hkm : k + m + 1 ≤ n + 1) :
    complEmb (suffixConnIdx k m hkm) (suffixMatch (I := I) (O := O) k m hkm).hι₂
        ⟨(n + 1 - m) + (n - m), by omega⟩ = Fin.natAdd (n + 2) (Fin.last (n + 1)) := by
  rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂
      ⟨(n + 1 - m) + (n - m), by omega⟩,
    suffixComplIdx, dite_eq_right (by show ¬((n + 1 - m) + (n - m) < n + 1 - m); omega)]
  have hid : (⟨(n + 1 - m) + (n - m) - (n + 1 - m), by omega⟩ : Fin (n + 1 - m))
      = ⟨n - m, by omega⟩ := by
    apply Fin.ext
    show (n + 1 - m) + (n - m) - (n + 1 - m) = n - m
    omega
  exact congrArg (Fin.natAdd (n + 2))
    ((congrArg (compOut (n := n) k m) hid).trans (compOut_last k m hkm))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Position bridge: in the non-boundary case the last private input index
enumerates the outer comb's last input wire. -/
private theorem complEmb_lastIn (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (hk : k < n - m) :
    complEmb (suffixConnIdx k m hkm) (suffixMatch (I := I) (O := O) k m hkm).hι₂
        ⟨n - m, by omega⟩ = Fin.castAdd (n + 2) (Fin.last (n + 1)) := by
  rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨n - m, by omega⟩,
    suffixComplIdx, dite_eq_left (by show (n - m : Nat) < n + 1 - m; omega)]
  exact congrArg (Fin.castAdd (n + 2)) (compIn_last k m hkm hk)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Reading the outer configuration is stable under renaming the position,
up to the induced family cast. -/
private theorem read₂_congr_pos (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (w : ∀ j, (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j)
    {p q : Fin (n + 2 + (n + 2))} (hpq : p = q) :
    cast (congrArg (append I O) hpq)
        ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc w p) =
      (suffixMatch (I := I) (O := O) k m hkm).read₂ zc w q := by
  subst hpq
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Pointwise computation at the outer comb's last output wire: the flattened
configuration's output entry there is the composite's last output value. -/
private theorem splitRead₂_lastOut (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j)) :
    (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v))).2 (Fin.last (n + 1))
      = cast (congrArg O (compOut_last k m hkm)) (v ⟨n - m, by omega⟩) := by
  show cast (append_natAdd I O (Fin.last (n + 1)))
      ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v)
        (Fin.natAdd (n + 2) (Fin.last (n + 1)))) = _
  have hpos : complEmb (suffixConnIdx k m hkm) (suffixMatch (I := I) (O := O) k m hkm).hι₂
      ⟨(n + 1 - m) + (n - m), by omega⟩ = Fin.natAdd (n + 2) (Fin.last (n + 1)) :=
    complEmb_lastOut (I := I) (O := O) k m hkm
  have hc1 := read₂_congr_pos (I := I) (O := O) k m hkm zc
    (complPack (I := I) (O := O) k m hkm u v) hpos
  refine Eq.trans (congrArg (cast (append_natAdd I O (Fin.last (n + 1)))) hc1.symm) ?_
  rw [suffixRead₂_compl (I := I) (O := O) k m hkm zc
      (complPack (I := I) (O := O) k m hkm u v) ⟨(n + 1 - m) + (n - m), by omega⟩,
    complPack_last (I := I) (O := O) k m hkm u v]
  exact (cast3 ((complFam₂_eq_ge' (I := I) (O := O) k m hkm ⟨n - m, by omega⟩).symm)
    (congrArg (append I O) hpos) (append_natAdd I O (Fin.last (n + 1)))
    (v ⟨n - m, by omega⟩)).trans rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Pointwise computation at the outer comb's last input wire: in the
non-boundary case, the flattened configuration's input entry there is the
composite's last input value. -/
private theorem splitRead₂_lastIn (k m : Nat) (hkm : k + m + 1 ≤ n + 1) (hk : k < n - m)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j)) :
    (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v))).1 (Fin.last (n + 1))
      = cast (congrArg I (compIn_last k m hkm hk)) (u ⟨n - m, by omega⟩) := by
  show cast (append_castAdd I O (Fin.last (n + 1)))
      ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v)
        (Fin.castAdd (n + 2) (Fin.last (n + 1)))) = _
  have hpos : complEmb (suffixConnIdx k m hkm) (suffixMatch (I := I) (O := O) k m hkm).hι₂
      ⟨n - m, by omega⟩ = Fin.castAdd (n + 2) (Fin.last (n + 1)) :=
    complEmb_lastIn (I := I) (O := O) k m hkm hk
  have hc1 := read₂_congr_pos (I := I) (O := O) k m hkm zc
    (complPack (I := I) (O := O) k m hkm u v) hpos
  refine Eq.trans (congrArg (cast (append_castAdd I O (Fin.last (n + 1)))) hc1.symm) ?_
  rw [suffixRead₂_compl (I := I) (O := O) k m hkm zc
      (complPack (I := I) (O := O) k m hkm u v) ⟨n - m, by omega⟩,
    complPack_lt (I := I) (O := O) k m hkm u v ⟨n - m, by omega⟩
      (by show (n - m : Nat) < n + 1 - m; omega)]
  exact (cast3 ((complFam₂_eq_lt (I := I) (O := O) k m hkm ⟨n - m, by omega⟩
      (by show (n - m : Nat) < n + 1 - m; omega)).symm)
    (congrArg (append I O) hpos) (append_castAdd I O (Fin.last (n + 1)))
    (u ⟨((⟨n - m, by omega⟩ : Fin (n + 1 - m)) : Nat), by omega⟩)).trans rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the boundary the window's last input-side connected wire is the outer
comb's last input wire. -/
private theorem connFam₁_natAdd_last_bnd (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (hkb : k + m + 1 = n + 1) :
    (suffixMatch (I := I) (O := O) k m hkm).connFam₁ (Fin.natAdd (m + 1) (Fin.last m))
      = I (Fin.last (n + 1)) := by
  show append (suffixOut O k m hkm) (suffixIn I k m hkm) (Fin.natAdd (m + 1) (Fin.last m)) = _
  rw [append_natAdd]
  exact congrArg I (Fin.ext (by simp only [suffixInIdx, Fin.val_last]; omega))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Pointwise computation at the outer comb's last input wire: at the boundary,
that wire is the inner comb's last output, so the flattened configuration's
input entry there is the connected configuration's last input-side entry. -/
private theorem splitRead₂_lastIn_bnd (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (hkb : k + m + 1 = n + 1)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (u : ∀ j, I (compIn k m j)) (v : ∀ j, O (compOut k m j)) :
    (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v))).1 (Fin.last (n + 1))
      = cast (connFam₁_natAdd_last_bnd (I := I) (O := O) k m hkm hkb)
        (zc (Fin.natAdd (m + 1) (Fin.last m))) := by
  show cast (append_castAdd I O (Fin.last (n + 1)))
      ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v)
        (Fin.castAdd (n + 2) (Fin.last (n + 1)))) = _
  have hpos : suffixConnIdx k m hkm (Fin.natAdd (m + 1) (Fin.last m))
      = Fin.castAdd (n + 2) (Fin.last (n + 1)) := by
    rw [suffixConnIdx_natAdd]
    exact Fin.ext (by simp only [Fin.val_castAdd, Fin.val_last]; omega)
  have hc1 := read₂_congr_pos (I := I) (O := O) k m hkm zc
    (complPack (I := I) (O := O) k m hkm u v) hpos
  refine Eq.trans (congrArg (cast (append_castAdd I O (Fin.last (n + 1)))) hc1.symm) ?_
  rw [suffixRead₂_conn_natAdd (I := I) (O := O) k m hkm zc
    (complPack (I := I) (O := O) k m hkm u v) (Fin.last m)]
  have hEq : (suffixMatch (I := I) (O := O) k m hkm).connFam₁ (Fin.natAdd (m + 1) (Fin.last m))
      = append I O (suffixConnIdx k m hkm (Fin.natAdd (m + 1) (Fin.last m))) := by
    show append (suffixOut O k m hkm) (suffixIn I k m hkm) (Fin.natAdd (m + 1) (Fin.last m)) = _
    rw [append_natAdd, suffixConnIdx_natAdd, append_castAdd]
    rfl
  rw [show (suffixMatch (I := I) (O := O) k m hkm).eRelabel zc (Fin.natAdd (m + 1) (Fin.last m))
      = cast hEq (zc (Fin.natAdd (m + 1) (Fin.last m))) from rfl]
  exact (cast3 hEq (congrArg (append I O) hpos) (append_castAdd I O (Fin.last (n + 1)))
    (zc (Fin.natAdd (m + 1) (Fin.last m)))).trans rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Snoc eta: a wire-indexed tuple is the snoc of its tail and its last entry. -/
private theorem snoc_tail_eq {N : Nat} {X : Fin (N + 1) → Type u} (s : ∀ j, X j) :
    Fin.snoc (α := X) (fun t : Fin N => s t.castSucc) (s (Fin.last N)) = s := by
  funext j
  rcases j.eq_castSucc_or_eq_last with ⟨t, hj⟩ | hj
  · rw [hj, Fin.snoc_castSucc]
  · rw [hj, Fin.snoc_last]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Position-wise independence of the outer configuration readback: away from
the last output wire, the read value does not depend on how the two private
configurations differ at the last-output index. -/
private theorem read₂_pos_eq_of_w_eq (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (w w' : ∀ j, (suffixMatch (I := I) (O := O) k m hkm).complFam₂ j)
    (hw : ∀ j : Fin ((n + 2 + (n + 2)) - ((m + 1) + (m + 1))),
      (j : Nat) ≠ (n + 1 - m) + (n - m) → w j = w' j)
    (p : Fin (n + 2 + (n + 2)))
    (hlast : p ≠ Fin.natAdd (n + 2) (Fin.last (n + 1))) :
    (suffixMatch (I := I) (O := O) k m hkm).read₂ zc w p =
      (suffixMatch (I := I) (O := O) k m hkm).read₂ zc w' p := by
  by_cases hconn : ∃ i : Fin (m + 1 + (m + 1)), suffixConnIdx k m hkm i = p
  · obtain ⟨i, hi⟩ := hconn
    rw [← hi]
    exact (WireMatch.read₂_conn (suffixMatch (I := I) (O := O) k m hkm) zc w i).trans
      (WireMatch.read₂_conn (suffixMatch (I := I) (O := O) k m hkm) zc w' i).symm
  · obtain ⟨j, hj⟩ := exists_suffixComplIdx k m hkm p (fun i hie => hconn ⟨i, hie⟩)
    have heq : complEmb (suffixConnIdx k m hkm) (suffixMatch (I := I) (O := O) k m hkm).hι₂ j = p :=
      (suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ j).trans hj
    have hnjB : (j : Nat) ≠ (n + 1 - m) + (n - m) := by
      intro hjB
      apply hlast
      refine Eq.trans heq.symm ?_
      refine Eq.trans (congrArg (complEmb (suffixConnIdx k m hkm)
        (suffixMatch (I := I) (O := O) k m hkm).hι₂) ?_) (complEmb_lastOut (I := I) (O := O) k m hkm)
      apply Fin.ext
      show (j : Nat) = (n + 1 - m) + (n - m)
      exact hjB
    rw [← heq, suffixRead₂_compl (I := I) (O := O) k m hkm zc w j,
      suffixRead₂_compl (I := I) (O := O) k m hkm zc w' j]
    exact hw j hnjB

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The input part of the flattened configuration is independent of the
composite's last output value. -/
private theorem splitRead₂_fst_congr (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (u : ∀ j, I (compIn k m j)) (v v' : ∀ j, O (compOut k m j))
    (hv : ∀ t : Fin (n + 1 - m), (t : Nat) ≠ n - m → v t = v' t) :
    (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v))).1 =
      (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v'))).1 := by
  funext s
  have hs := s.isLt
  show cast (append_castAdd I O s)
      ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v) (Fin.castAdd (n + 2) s)) = _
  refine congrArg (cast (append_castAdd I O s)) (read₂_pos_eq_of_w_eq (I := I) (O := O) k m hkm zc
    (complPack (I := I) (O := O) k m hkm u v) (complPack (I := I) (O := O) k m hkm u v')
    (fun j hj => complPack_congr (I := I) (O := O) k m hkm u v v' hv j hj)
    (Fin.castAdd (n + 2) s) ?_)
  intro h
  have hv2 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_last] at hv2
  omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Away from the last output wire, the output part of the flattened
configuration is independent of the composite's last output value. -/
private theorem splitRead₂_out_congr (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (u : ∀ j, I (compIn k m j)) (v v' : ∀ j, O (compOut k m j))
    (hv : ∀ t : Fin (n + 1 - m), (t : Nat) ≠ n - m → v t = v' t)
    (t : Fin (n + 1)) :
    (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v))).2 t.castSucc =
      (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v'))).2 t.castSucc := by
  have ht := t.isLt
  show cast (append_natAdd I O t.castSucc)
      ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u v) (Fin.natAdd (n + 2) t.castSucc)) = _
  refine congrArg (cast (append_natAdd I O t.castSucc)) (read₂_pos_eq_of_w_eq (I := I) (O := O) k m hkm zc
    (complPack (I := I) (O := O) k m hkm u v) (complPack (I := I) (O := O) k m hkm u v')
    (fun j hj => complPack_congr (I := I) (O := O) k m hkm u v v' hv j hj)
    (Fin.natAdd (n + 2) t.castSucc) ?_)
  intro h
  have hv2 := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hv2
  omega

/-! ### The plain-form snoc packing of the composite output tuple -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The plain-form output component of a successor-form truncated point. -/
private def snocP (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (o : ∀ j : Fin (n - m), O (compOutS k m hkm j.castSucc))
    (z : O (compOutS k m hkm (Fin.last (n - m))))
    (j : Fin (n + 1 - m)) : O (compOut k m j) :=
  Fin.snoc (α := fun i : Fin (n - m + 1) => O (compOutS k m hkm i)) o z
    ((compIdxEquiv (n := n) k m hkm).symm j)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the plain last tooth the snoc-packing reads off the final value. -/
private theorem snocP_last (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (o : ∀ j : Fin (n - m), O (compOutS k m hkm j.castSucc))
    (z : O (compOutS k m hkm (Fin.last (n - m)))) :
    snocP (O := O) k m hkm o z ⟨n - m, by omega⟩ = z := by
  show Fin.snoc (α := fun i : Fin (n - m + 1) => O (compOutS k m hkm i)) o z
      (Fin.last (n - m)) = z
  exact Fin.snoc_last (α := fun i : Fin (n - m + 1) => O (compOutS k m hkm i))
    (p := o) (x := z)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Away from the plain last tooth the snoc-packing is independent of the
final value. -/
private theorem snocP_ne (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (o : ∀ j : Fin (n - m), O (compOutS k m hkm j.castSucc))
    (z z' : O (compOutS k m hkm (Fin.last (n - m))))
    (j : Fin (n + 1 - m)) (hj : (j : Nat) ≠ n - m) :
    snocP (O := O) k m hkm o z j = snocP (O := O) k m hkm o z' j := by
  have he : (compIdxEquiv (n := n) k m hkm).symm j ≠ Fin.last (n - m) := by
    intro hlast
    apply hj
    have hv := congrArg Fin.val hlast
    simp only [compIdxEquiv_symm_val, Fin.val_last] at hv
    exact hv
  show Fin.snoc (α := fun i : Fin (n - m + 1) => O (compOutS k m hkm i)) o z
      ((compIdxEquiv (n := n) k m hkm).symm j)
    = Fin.snoc (α := fun i : Fin (n - m + 1) => O (compOutS k m hkm i)) o z'
      ((compIdxEquiv (n := n) k m hkm).symm j)
  rcases ((compIdxEquiv (n := n) k m hkm).symm j).eq_castSucc_or_eq_last with ⟨s, h⟩ | h
  · rw [h, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · exact absurd h he

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Row identification of the outer readback at a snoc-packed composite output:
the flattened configuration is the snoc of its tail and the transported final
value. -/
private theorem splitRead₂_snoc_eq (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (zc : ∀ i, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ i)
    (u : ∀ j, I (compIn k m j))
    (o : ∀ j : Fin (n - m), O (compOutS k m hkm j.castSucc))
    (z : O (compOutS k m hkm (Fin.last (n - m)))) :
    splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u (snocP (O := O) k m hkm o z)))
      = ((splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
            (complPack (I := I) (O := O) k m hkm u
              (snocP (O := O) k m hkm o z)))).1,
        Fin.snoc (α := fun t : Fin (n + 2) => O t)
          (fun t : Fin (n + 1) => (splitAppendEquiv I O
              ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
                (complPack (I := I) (O := O) k m hkm u
                  (snocP (O := O) k m hkm o z)))).2 t.castSucc)
          (cast (congrArg O (compOut_last k m hkm)) z)) := by
  have hslot : (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) k m hkm).read₂ zc
        (complPack (I := I) (O := O) k m hkm u (snocP (O := O) k m hkm o z)))).2
        (Fin.last (n + 1))
      = cast (congrArg O (compOut_last k m hkm)) z := by
    rw [splitRead₂_lastOut (I := I) (O := O) k m hkm zc u
        (snocP (O := O) k m hkm o z),
      snocP_last (O := O) k m hkm o z]
  rw [← hslot, snoc_tail_eq]

/-! ### Snoc-point entry expansion of the successor-form composite -/

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- Entrywise expansion of the successor-form composite at snoc-shaped points,
at the base depth: the entry is the window contraction with the private
configuration induced by the transported successor point. -/
private theorem suffixCompS_entry_snoc (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (ic ic' : ∀ j : Fin (n - m + 1), I (compInS (n := n) k m hkm j))
    (oc oc' : ∀ j : Fin (n - m), O (compOutS (n := n) k m hkm j.castSucc))
    (w : O (compOutS (n := n) k m hkm (Fin.last (n - m)))) :
    suffixCompS (I := I) (O := O) (n := n) k m hkm J X (ic, Fin.snoc oc w) (ic', Fin.snoc oc' w)
      = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n) k m hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n) k m hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n) k m hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n) k m hkm).symm zz) *
          J (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := n) k m hkm).read₂ zz'
              (complPack (I := I) (O := O) (n := n) k m hkm
                ((spaceIdxEquiv (I := I) (O := O) (n := n) k m hkm (ic, Fin.snoc oc w)).1)
                ((spaceIdxEquiv (I := I) (O := O) (n := n) k m hkm (ic, Fin.snoc oc w)).2))))
            (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := n) k m hkm).read₂ zz
              (complPack (I := I) (O := O) (n := n) k m hkm
                ((spaceIdxEquiv (I := I) (O := O) (n := n) k m hkm (ic', Fin.snoc oc' w)).1)
                ((spaceIdxEquiv (I := I) (O := O) (n := n) k m hkm (ic', Fin.snoc oc' w)).2)))) := by
  refine (suffixComp_apply (I := I) (O := O) (n := n) k m hkm J X
      (spaceIdxEquiv (I := I) (O := O) (n := n) k m hkm (ic, Fin.snoc oc w))
      (spaceIdxEquiv (I := I) (O := O) (n := n) k m hkm (ic', Fin.snoc oc' w))).trans
    (Finset.sum_congr rfl fun zz _ => Finset.sum_congr rfl fun zz' _ => ?_)
  refine congrArg₂ (fun (a b : ℂ) => a * b) ?_ ?_
  · exact congrArg₂ X
      (congrArg ((XFlatEquiv (I := I) (O := O) (n := n) k m hkm).symm)
        (suffixRead₁ (I := I) (O := O) (n := n) k m hkm _ zz'))
      (congrArg ((XFlatEquiv (I := I) (O := O) (n := n) k m hkm).symm)
        (suffixRead₁ (I := I) (O := O) (n := n) k m hkm _ zz))
  · exact congrArg₂ J rfl rfl

/-! ### Depth-shift coherence and the family-tail reindex

The truncation step of the normalization induction compares the composite at
depth `n + 1` (outer families `Fin (n + 3)`) with the truncated composite at
depth `n` (families `Fin (n + 2)`, read back through `Fin.castSucc`).  All
statements below are staged with the two depths side by side, so no `n - 1`
arithmetic ever appears. -/

section TailShift

variable {n : Nat} {I O : Fin (n + 3) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Depth-shift coherence of the composite input map: the untruncated
composite's tail entry at `j` is the truncated composite's entry at `j`,
embedded by `Fin.castSucc`. -/
private theorem compIn_tail_eq (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (j : Fin (n + 1 - m)) :
    compInS (n := n + 1) k m hkm j.castSucc
      = Fin.castSucc (compInS (n := n) k m hkm' ⟨(j : Nat), by omega⟩) := by
  apply Fin.ext
  simp only [compInS_val, Fin.val_castSucc]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Depth-shift coherence of the composite output map. -/
private theorem compOut_tail_eq (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (j : Fin (n + 1 - m)) :
    compOutS (n := n + 1) k m hkm j.castSucc
      = Fin.castSucc (compOutS (n := n) k m hkm' ⟨(j : Nat), by omega⟩) := by
  apply Fin.ext
  simp only [compOutS_val, Fin.val_castSucc]

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- Window stability under truncation: the truncated composition accepts the
same inner Choi matrix, because the window families at the two depths are
definitionally the same outer wires. -/
noncomputable example (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc) (fun j : Fin (n + 2) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))) :
    CMatrix (Space (fun j : Fin (n - m + 1) => (fun t : Fin (n + 2) => I t.castSucc)
        (compInS (n := n) k m hkm' j))
      (fun j : Fin (n - m + 1) => (fun t : Fin (n + 2) => O t.castSucc)
        (compOutS (n := n) k m hkm' j))) :=
  suffixCompS (n := n) (I := fun j : Fin (n + 2) => I j.castSucc)
    (O := fun j : Fin (n + 2) => O j.castSucc) k m hkm' K X

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Tail family equation, input wires: the truncated composite's input family
at `j` reads the same type as the untruncated composite's tail entry. -/
private theorem famTailEqI (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (j : Fin (n + 1 - m)) :
    (fun t : Fin (n + 2) => I t.castSucc) (compInS (n := n) k m hkm' ⟨(j : Nat), by omega⟩)
      = I (compInS (n := n + 1) k m hkm j.castSucc) :=
  (congrArg I (compIn_tail_eq k m hkm hkm' j)).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Tail family equation, output wires. -/
private theorem famTailEqO (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (j : Fin (n + 1 - m)) :
    (fun t : Fin (n + 2) => O t.castSucc) (compOutS (n := n) k m hkm' ⟨(j : Nat), by omega⟩)
      = O (compOutS (n := n + 1) k m hkm j.castSucc) :=
  (congrArg O (compOut_tail_eq k m hkm hkm' j)).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Tail family equation, input wires, inverse direction: reading the
untruncated composite's tail entry through the value-preserving bridge. -/
private theorem famTailEqI' (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (i : Fin (n - m + 1)) :
    I (compInS (n := n + 1) k m hkm (⟨(i : Nat), by omega⟩ : Fin (n + 1 - m)).castSucc)
      = (fun t : Fin (n + 2) => I t.castSucc) (compInS (n := n) k m hkm' i) :=
  congrArg I (compIn_tail_eq k m hkm hkm' ⟨(i : Nat), by omega⟩)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Tail family equation, output wires, inverse direction. -/
private theorem famTailEqO' (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (i : Fin (n - m + 1)) :
    O (compOutS (n := n + 1) k m hkm (⟨(i : Nat), by omega⟩ : Fin (n + 1 - m)).castSucc)
      = (fun t : Fin (n + 2) => O t.castSucc) (compOutS (n := n) k m hkm' i) :=
  congrArg O (compOut_tail_eq k m hkm hkm' ⟨(i : Nat), by omega⟩)

/-- The family-tail reindex: the truncated composite's wire families read the
same types as the untruncated composite's castSucc tail. -/
private def famTailEquiv (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1) :
    Space (fun j : Fin (n - m + 1) => (fun t : Fin (n + 2) => I t.castSucc)
        (compInS (n := n) k m hkm' j))
      (fun j : Fin (n - m + 1) => (fun t : Fin (n + 2) => O t.castSucc)
        (compOutS (n := n) k m hkm' j)) ≃
    Space (fun j : Fin (n + 1 - m) => I (compInS (n := n + 1) k m hkm j.castSucc))
      (fun j : Fin (n + 1 - m) => O (compOutS (n := n + 1) k m hkm j.castSucc)) where
  toFun p :=
    ((fun j => cast (famTailEqI (I := I) k m hkm hkm' j) (p.1 ⟨(j : Nat), by omega⟩)),
      (fun j => cast (famTailEqO (O := O) k m hkm hkm' j) (p.2 ⟨(j : Nat), by omega⟩)))
  invFun q :=
    ((fun i => cast (famTailEqI' (I := I) k m hkm hkm' i)
        (q.1 ⟨(i : Nat), by omega⟩)),
      (fun i => cast (famTailEqO' (O := O) k m hkm hkm' i)
        (q.2 ⟨(i : Nat), by omega⟩)))
  left_inv p := by
    apply Prod.ext
    · funext i
      exact cast_cast_cancel (famTailEqI' (I := I) k m hkm hkm' i) (p.1 i)
    · funext i
      exact cast_cast_cancel (famTailEqO' (O := O) k m hkm hkm' i) (p.2 i)
  right_inv q := by
    apply Prod.ext
    · funext j
      exact cast_cast_cancel (famTailEqI (I := I) k m hkm hkm' j) (q.1 j)
    · funext j
      exact cast_cast_cancel (famTailEqO (O := O) k m hkm hkm' j) (q.2 j)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Depth-shift coherence of the outer configuration readback, input side: at
every truncated input wire, the truncated composite's private configuration
entry equals the untruncated composite's entry. -/
private theorem read₂_tail_in (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ q)
    (u : ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j))
    (v : ∀ j : Fin ((n + 1) + 1 - m), O (compOut (n := n + 1) k m j))
    (s : Fin (n + 2)) :
    cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc) s)
        ((suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').read₂ zz
          (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
            (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
                (u ⟨(j : Nat), by omega⟩))
            (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
                (v ⟨(j : Nat), by omega⟩)))
          (Fin.castAdd (n + 2) s))
      = cast (append_castAdd I O s.castSucc)
          ((suffixMatch (I := I) (O := O) k m hkm).read₂ zz
            (complPack (I := I) (O := O) k m hkm u v)
            (Fin.castAdd (n + 3) s.castSucc)) := by
  have hs := s.isLt
  rcases Nat.lt_or_ge (s : Nat) (k + 1) with hA | hA'
  · -- below the window: private input wire at both depths
    have hltT : (s : Nat) < n + 1 - m := by omega
    have hltP : (s : Nat) < (n + 1) + 1 - m := by omega
    have hposT : complEmb (suffixConnIdx (n := n) k m hkm')
        (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂ ⟨(s : Nat), by omega⟩
        = Fin.castAdd (n + 2) s := by
      rw [suffixComplEmb k m hkm' (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc) (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂ ⟨(s : Nat), by omega⟩,
        suffixComplIdx_of_lt_le k m hkm' ⟨(s : Nat), by omega⟩ hltT
          (by show (s : Nat) ≤ k; omega)]
    have hcT := read₂_congr_pos (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' zz
      (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) hposT
    have hposP : complEmb (suffixConnIdx (n := n + 1) k m hkm)
        (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨(s : Nat), by omega⟩
        = Fin.castAdd (n + 3) s.castSucc := by
      rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨(s : Nat), by omega⟩,
        suffixComplIdx_of_lt_le k m hkm ⟨(s : Nat), by omega⟩ hltP
          (by show (s : Nat) ≤ k; omega)]
      exact congrArg (Fin.castAdd (n + 3)) (Fin.ext (by simp))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k m hkm zz
      (complPack (I := I) (O := O) k m hkm u v) hposP
    refine Eq.trans (congrArg (cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_castAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_compl (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' zz
        (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) ⟨(s : Nat), by omega⟩,
      complPack_lt (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩)) ⟨(s : Nat), by omega⟩ hltT,
      suffixRead₂_compl (I := I) (O := O) k m hkm zz
        (complPack (I := I) (O := O) k m hkm u v) ⟨(s : Nat), by omega⟩,
      complPack_lt (I := I) (O := O) k m hkm u v ⟨(s : Nat), by omega⟩ hltP]
    exact (cast4 (congrArg I (compIn_tail_eq k m hkm hkm' ⟨(s : Nat), by omega⟩))
      (complFam₂_eq_lt (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' ⟨(s : Nat), by omega⟩ hltT).symm
      (congrArg (append (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc)) hposT)
      (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)
      (u ⟨(s : Nat), by omega⟩)).trans
      (cast3 (complFam₂_eq_lt (I := I) (O := O) k m hkm ⟨(s : Nat), by omega⟩ hltP).symm
        (congrArg (append I O) hposP) (append_castAdd I O s.castSucc)
        (u ⟨(s : Nat), by omega⟩)).symm
  rcases Nat.lt_or_ge (s : Nat) (k + m + 2) with hB | hB'
  · -- inside the window: connected entry at both depths
    have ht : (s : Nat) - (k + 1) < m + 1 := by omega
    have hposT : suffixConnIdx (n := n) k m hkm' (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = Fin.castAdd (n + 2) s := by
      rw [suffixConnIdx_natAdd]
      exact congrArg (Fin.castAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' zz
      (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) hposT
    have hposP : suffixConnIdx (n := n + 1) k m hkm
        (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩) = Fin.castAdd (n + 3) s.castSucc := by
      rw [suffixConnIdx_natAdd]
      exact congrArg (Fin.castAdd (n + 3))
        (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k m hkm zz
      (complPack (I := I) (O := O) k m hkm u v) hposP
    refine Eq.trans (congrArg (cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_castAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_conn_natAdd (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' zz
        (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) ⟨(s : Nat) - (k + 1), ht⟩,
      suffixRead₂_conn_natAdd (I := I) (O := O) k m hkm zz
        (complPack (I := I) (O := O) k m hkm u v) ⟨(s : Nat) - (k + 1), ht⟩]
    have hEqT : (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').connFam₁
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)
          (suffixConnIdx (n := n) k m hkm'
            (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)) := by
      show append (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm')
          (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm')
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩) = _
      rw [append_natAdd, suffixConnIdx_natAdd, append_castAdd]
      rfl
    have hEqP : (suffixMatch (I := I) (O := O) k m hkm).connFam₁
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = append I O
          (suffixConnIdx (n := n + 1) k m hkm
            (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)) := by
      show append (suffixOut O k m hkm) (suffixIn I k m hkm)
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩) = _
      rw [append_natAdd, suffixConnIdx_natAdd, append_castAdd]
      rfl
    rw [show (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').eRelabel zz
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = cast hEqT (zz (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)) from rfl,
      show (suffixMatch (I := I) (O := O) k m hkm).eRelabel zz
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = cast hEqP (zz (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)) from rfl]
    exact (cast3 hEqT
        (congrArg (append (fun t : Fin (n + 2) => I t.castSucc)
            (fun t : Fin (n + 2) => O t.castSucc)) hposT)
        (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc) s)
        (zz (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩))).trans
      (cast3 hEqP (congrArg (append I O) hposP) (append_castAdd I O s.castSucc)
        (zz (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩))).symm
  · -- above the window: private input wire at both depths
    have hltT : (s : Nat) - (m + 1) < n + 1 - m := by omega
    have hltP : (s : Nat) - (m + 1) < (n + 1) + 1 - m := by omega
    have hposT : complEmb (suffixConnIdx (n := n) k m hkm')
        (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂
        ⟨(s : Nat) - (m + 1), by omega⟩ = Fin.castAdd (n + 2) s := by
      rw [suffixComplEmb k m hkm' (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc) (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂ ⟨(s : Nat) - (m + 1), by omega⟩,
        suffixComplIdx_of_lt_gt k m hkm' ⟨(s : Nat) - (m + 1), by omega⟩
          hltT (by show k < (s : Nat) - (m + 1); omega)]
      exact congrArg (Fin.castAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' zz
      (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) hposT
    have hposP : complEmb (suffixConnIdx (n := n + 1) k m hkm)
        (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨(s : Nat) - (m + 1), by omega⟩
        = Fin.castAdd (n + 3) s.castSucc := by
      rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨(s : Nat) - (m + 1), by omega⟩,
        suffixComplIdx_of_lt_gt k m hkm ⟨(s : Nat) - (m + 1), by omega⟩
          hltP (by show k < (s : Nat) - (m + 1); omega)]
      exact congrArg (Fin.castAdd (n + 3))
        (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k m hkm zz
      (complPack (I := I) (O := O) k m hkm u v) hposP
    refine Eq.trans (congrArg (cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_castAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_compl (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' zz
        (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) ⟨(s : Nat) - (m + 1), by omega⟩,
      complPack_lt (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩)) ⟨(s : Nat) - (m + 1), by omega⟩
        hltT,
      suffixRead₂_compl (I := I) (O := O) k m hkm zz
        (complPack (I := I) (O := O) k m hkm u v) ⟨(s : Nat) - (m + 1), by omega⟩,
      complPack_lt (I := I) (O := O) k m hkm u v ⟨(s : Nat) - (m + 1), by omega⟩ hltP]
    exact (cast4 (congrArg I
        (compIn_tail_eq k m hkm hkm' ⟨(s : Nat) - (m + 1), by omega⟩))
      (complFam₂_eq_lt (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
          ⟨(s : Nat) - (m + 1), by omega⟩ hltT).symm
      (congrArg (append (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc)) hposT)
      (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)
      (u ⟨(s : Nat) - (m + 1), by omega⟩)).trans
      (cast3 (complFam₂_eq_lt (I := I) (O := O) k m hkm
          ⟨(s : Nat) - (m + 1), by omega⟩ hltP).symm
        (congrArg (append I O) hposP) (append_castAdd I O s.castSucc)
        (u ⟨(s : Nat) - (m + 1), by omega⟩)).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Depth-shift coherence of the outer configuration readback, output side: at
every truncated output wire, the truncated composite's private configuration
entry equals the untruncated composite's entry. -/
private theorem read₂_tail_out (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ q)
    (u : ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j))
    (v : ∀ j : Fin ((n + 1) + 1 - m), O (compOut (n := n + 1) k m j))
    (s : Fin (n + 2)) :
    cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc) s)
        ((suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').read₂ zz
          (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
            (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
                (u ⟨(j : Nat), by omega⟩))
            (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
                (v ⟨(j : Nat), by omega⟩)))
          (Fin.natAdd (n + 2) s))
      = cast (append_natAdd I O s.castSucc)
          ((suffixMatch (I := I) (O := O) k m hkm).read₂ zz
            (complPack (I := I) (O := O) k m hkm u v)
            (Fin.natAdd (n + 3) s.castSucc)) := by
  have hs := s.isLt
  rcases Nat.lt_or_ge (s : Nat) k with hA | hA'
  · -- below the window: private output wire at both depths
    have hposT : complEmb (suffixConnIdx (n := n) k m hkm')
        (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂
        ⟨(n + 1 - m) + (s : Nat), by omega⟩ = Fin.natAdd (n + 2) s := by
      rw [suffixComplEmb k m hkm' (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc) (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂ ⟨(n + 1 - m) + (s : Nat), by omega⟩,
        suffixComplIdx_of_ge_lt k m hkm' ⟨(n + 1 - m) + (s : Nat), by omega⟩
          (by show ¬((n + 1 - m) + (s : Nat) < n + 1 - m); omega)
          (by show (n + 1 - m) + (s : Nat) - (n + 1 - m) < k; omega)]
      exact congrArg (Fin.natAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' zz
      (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) hposT
    have hposP : complEmb (suffixConnIdx (n := n + 1) k m hkm)
        (suffixMatch (I := I) (O := O) k m hkm).hι₂
        ⟨((n + 1) + 1 - m) + (s : Nat), by omega⟩ = Fin.natAdd (n + 3) s.castSucc := by
      rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨((n + 1) + 1 - m) + (s : Nat), by omega⟩,
        suffixComplIdx_of_ge_lt k m hkm ⟨((n + 1) + 1 - m) + (s : Nat), by omega⟩
          (by show ¬(((n + 1) + 1 - m) + (s : Nat) < (n + 1) + 1 - m); omega)
          (by show ((n + 1) + 1 - m) + (s : Nat) - ((n + 1) + 1 - m) < k; omega)]
      exact congrArg (Fin.natAdd (n + 3)) (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k m hkm zz
      (complPack (I := I) (O := O) k m hkm u v) hposP
    refine Eq.trans (congrArg (cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_natAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_compl (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' zz
        (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩)))
        ⟨(n + 1 - m) + (s : Nat), by omega⟩,
      complPack_ge' (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))
        ⟨(s : Nat), by omega⟩,
      suffixRead₂_compl (I := I) (O := O) k m hkm zz
        (complPack (I := I) (O := O) k m hkm u v)
        ⟨((n + 1) + 1 - m) + (s : Nat), by omega⟩,
      complPack_ge' (I := I) (O := O) k m hkm u v ⟨(s : Nat), by omega⟩]
    exact (cast4 (congrArg O (compOut_tail_eq k m hkm hkm' ⟨(s : Nat), by omega⟩))
      (complFam₂_eq_ge' (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' ⟨(s : Nat), by omega⟩).symm
      (congrArg (append (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc)) hposT)
      (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)
      (v ⟨(s : Nat), by omega⟩)).trans
      (cast3 (complFam₂_eq_ge' (I := I) (O := O) k m hkm ⟨(s : Nat), by omega⟩).symm
        (congrArg (append I O) hposP) (append_natAdd I O s.castSucc)
        (v ⟨(s : Nat), by omega⟩)).symm
  rcases Nat.lt_or_ge (s : Nat) (k + m + 1) with hB | hB'
  · -- inside the window: connected entry at both depths
    have ht : (s : Nat) - k < m + 1 := by omega
    have hposT : suffixConnIdx (n := n) k m hkm' (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = Fin.natAdd (n + 2) s := by
      rw [suffixConnIdx_castAdd]
      exact congrArg (Fin.natAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' zz
      (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) hposT
    have hposP : suffixConnIdx (n := n + 1) k m hkm
        (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩) = Fin.natAdd (n + 3) s.castSucc := by
      rw [suffixConnIdx_castAdd]
      exact congrArg (Fin.natAdd (n + 3)) (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k m hkm zz
      (complPack (I := I) (O := O) k m hkm u v) hposP
    refine Eq.trans (congrArg (cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_natAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_conn_castAdd (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' zz
        (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) ⟨(s : Nat) - k, ht⟩,
      suffixRead₂_conn_castAdd (I := I) (O := O) k m hkm zz
        (complPack (I := I) (O := O) k m hkm u v) ⟨(s : Nat) - k, ht⟩]
    have hEqT : (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').connFam₁
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)
          (suffixConnIdx (n := n) k m hkm'
            (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)) := by
      show append (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm')
          (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm')
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩) = _
      rw [append_castAdd, suffixConnIdx_castAdd, append_natAdd]
      rfl
    have hEqP : (suffixMatch (I := I) (O := O) k m hkm).connFam₁
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = append I O
          (suffixConnIdx (n := n + 1) k m hkm
            (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)) := by
      show append (suffixOut O k m hkm) (suffixIn I k m hkm)
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩) = _
      rw [append_castAdd, suffixConnIdx_castAdd, append_natAdd]
      rfl
    rw [show (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').eRelabel zz
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = cast hEqT (zz (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)) from rfl,
      show (suffixMatch (I := I) (O := O) k m hkm).eRelabel zz
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = cast hEqP (zz (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)) from rfl]
    exact (cast3 hEqT
        (congrArg (append (fun t : Fin (n + 2) => I t.castSucc)
            (fun t : Fin (n + 2) => O t.castSucc)) hposT)
        (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc) s)
        (zz (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩))).trans
      (cast3 hEqP (congrArg (append I O) hposP) (append_natAdd I O s.castSucc)
        (zz (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩))).symm
  · -- above the window: private output wire at both depths
    have hposT : complEmb (suffixConnIdx (n := n) k m hkm')
        (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂
        ⟨(n + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩ = Fin.natAdd (n + 2) s := by
      rw [suffixComplEmb k m hkm' (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc) (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').hι₂ ⟨(n + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩,
        suffixComplIdx_of_ge_ge k m hkm' ⟨(n + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩
          (by show ¬((n + 1 - m) + ((s : Nat) - (m + 1)) < n + 1 - m); omega)
          (by show k ≤ (n + 1 - m) + ((s : Nat) - (m + 1)) - (n + 1 - m); omega)]
      exact congrArg (Fin.natAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' zz
      (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))) hposT
    have hposP : complEmb (suffixConnIdx (n := n + 1) k m hkm)
        (suffixMatch (I := I) (O := O) k m hkm).hι₂
        ⟨((n + 1) + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩
        = Fin.natAdd (n + 3) s.castSucc := by
      rw [suffixComplEmb k m hkm (suffixMatch (I := I) (O := O) k m hkm).hι₂ ⟨((n + 1) + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩,
        suffixComplIdx_of_ge_ge k m hkm
          ⟨((n + 1) + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩
          (by show ¬(((n + 1) + 1 - m) + ((s : Nat) - (m + 1)) < (n + 1) + 1 - m); omega)
          (by show k ≤ ((n + 1) + 1 - m) + ((s : Nat) - (m + 1)) - ((n + 1) + 1 - m); omega)]
      exact congrArg (Fin.natAdd (n + 3)) (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k m hkm zz
      (complPack (I := I) (O := O) k m hkm u v) hposP
    refine Eq.trans (congrArg (cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_natAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_compl (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' zz
        (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩)))
        ⟨(n + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩,
      complPack_ge' (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j)) (u ⟨(j : Nat), by omega⟩)) (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j)) (v ⟨(j : Nat), by omega⟩))
        ⟨(s : Nat) - (m + 1), by omega⟩,
      suffixRead₂_compl (I := I) (O := O) k m hkm zz
        (complPack (I := I) (O := O) k m hkm u v)
        ⟨((n + 1) + 1 - m) + ((s : Nat) - (m + 1)), by omega⟩,
      complPack_ge' (I := I) (O := O) k m hkm u v ⟨(s : Nat) - (m + 1), by omega⟩]
    exact (cast4 (congrArg O
        (compOut_tail_eq k m hkm hkm' ⟨(s : Nat) - (m + 1), by omega⟩))
      (complFam₂_eq_ge' (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
          ⟨(s : Nat) - (m + 1), by omega⟩).symm
      (congrArg (append (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc)) hposT)
      (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc) s)
      (v ⟨(s : Nat) - (m + 1), by omega⟩)).trans
      (cast3 (complFam₂_eq_ge' (I := I) (O := O) k m hkm
          ⟨(s : Nat) - (m + 1), by omega⟩).symm
        (congrArg (append I O) hposP) (append_natAdd I O s.castSucc)
        (v ⟨(s : Nat) - (m + 1), by omega⟩)).symm

/-- Sum transport along a type cast: summing a cast-value function equals
summing the function itself. -/
private theorem sum_cast_equiv {a b : Type u} [Fintype a] [Fintype b] (h : a = b) (F : b → ℂ) :
    ∑ x : a, F (cast h x) = ∑ y : b, F y :=
  Equiv.sum_comp (Equiv.cast h) F

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Depth-shift coherence of the flattened outer configuration: the truncated
composite's flattened configuration is the `castSucc` compression of the
untruncated composite's, componentwise on input and output wires. -/
private theorem read₂_tail (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) k m hkm).connFam₁ q)
    (u : ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j))
    (v : ∀ j : Fin ((n + 1) + 1 - m), O (compOut (n := n + 1) k m j)) :
    splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc)
        (fun t : Fin (n + 2) => O t.castSucc)
        ((suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').read₂ zz
          (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
            (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
                (u ⟨(j : Nat), by omega⟩))
            (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
                (v ⟨(j : Nat), by omega⟩))))
      = ((fun s : Fin (n + 2) => cast (append_castAdd I O s.castSucc)
            ((suffixMatch (I := I) (O := O) k m hkm).read₂ zz
              (complPack (I := I) (O := O) k m hkm u v) (Fin.castAdd (n + 3) s.castSucc))),
        (fun s : Fin (n + 2) => cast (append_natAdd I O s.castSucc)
            ((suffixMatch (I := I) (O := O) k m hkm).read₂ zz
              (complPack (I := I) (O := O) k m hkm u v) (Fin.natAdd (n + 3) s.castSucc)))) := by
  apply Prod.ext
  · funext s
    show cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc) s)
        ((suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').read₂ zz
          (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
            (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
                (u ⟨(j : Nat), by omega⟩))
            (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
                (v ⟨(j : Nat), by omega⟩)))
          (Fin.castAdd (n + 2) s)) = _
    exact read₂_tail_in k m hkm hkm' hk zz u v s
  · funext s
    show cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc) s)
        ((suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').read₂ zz
          (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
            (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
                (u ⟨(j : Nat), by omega⟩))
            (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
                (v ⟨(j : Nat), by omega⟩)))
          (Fin.natAdd (n + 2) s)) = _
    exact read₂_tail_out k m hkm hkm' zz u v s

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Plain-form bridge for the truncated composite's configuration at a tail
point: pushing the `Normalized` tail point back through the family-tail and
successor-form equivalences yields exactly the tail-shifted cast lambdas that
the depth-coherent readback consumes. -/
private theorem tailConfig_eq (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (i : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    spaceIdxEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm'
      ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i j.castSucc), o))
    = ((fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
          (i ((compIdxEquiv (n := n + 1) k m hkm).symm ⟨(j : Nat), by omega⟩))),
       (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
          (snocP (O := O) (n := n + 1) k m hkm o z ⟨(j : Nat), by omega⟩))) := by
  apply Prod.ext
  · funext j
    rfl
  · funext j
    have hj : ((compIdxEquiv (n := n) k m hkm').symm j : Nat) = (j : Nat) :=
      compIdxEquiv_symm_val k m hkm' j
    have h2 : snocP (O := O) (n := n + 1) k m hkm o z ⟨(j : Nat), by omega⟩
        = o ⟨(j : Nat), by omega⟩ :=
      Fin.snoc_castSucc (α := fun t : Fin ((n + 1) - m + 1) => O (compOutS (n := n + 1) k m hkm t))
        z o ⟨(j : Nat), by omega⟩
    show cast (famTailEqO' (O := O) k m hkm hkm' ((compIdxEquiv (n := n) k m hkm').symm j))
        (o ⟨((compIdxEquiv (n := n) k m hkm').symm j : Nat), by omega⟩)
        = cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
          (snocP (O := O) (n := n + 1) k m hkm o z ⟨(j : Nat), by omega⟩)
    rw [h2]
    rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Row-shape of the peeled configuration: flattening the outer readback of a
snoc-packed composite output at summation value `z` agrees with the
configuration at any reference value `z₀` away from the last output wire, and
carries `z` (transported to the outer last output wire) at the last position. -/
private theorem trunc_row_eq (k m : Nat) (hkm : k + m + 1 ≤ n + 2)
    (zc : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q)
    (u : ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j))
    (o : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z z₀ : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).read₂ zc
        (complPack (I := I) (O := O) (n := n + 1) k m hkm u
          (snocP (O := O) (n := n + 1) k m hkm o z))) =
      ((splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).read₂ zc
            (complPack (I := I) (O := O) (n := n + 1) k m hkm u
              (snocP (O := O) (n := n + 1) k m hkm o z₀)))).1,
        Fin.snoc (α := fun t : Fin (n + 3) => O t)
          (fun t : Fin (n + 2) => (splitAppendEquiv I O
              ((suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).read₂ zc
                (complPack (I := I) (O := O) (n := n + 1) k m hkm u
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)))).2 t.castSucc)
          (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z)) := by
  have hv : ∀ t : Fin ((n + 1) + 1 - m), (t : Nat) ≠ (n + 1) - m →
      snocP (O := O) (n := n + 1) k m hkm o z t = snocP (O := O) (n := n + 1) k m hkm o z₀ t :=
    fun t ht => snocP_ne (n := n + 1) k m hkm o z z₀ t ht
  have h2 : Fin.snoc (α := fun t : Fin (n + 3) => O t)
        (fun t : Fin (n + 2) => (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := n + 1)
              k m hkm).read₂ zc (complPack (I := I) (O := O) (n := n + 1) k m hkm u
            (snocP (O := O) (n := n + 1) k m hkm o z)))).2 t.castSucc)
        (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z)
      = Fin.snoc (α := fun t : Fin (n + 3) => O t)
        (fun t : Fin (n + 2) => (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := n + 1)
              k m hkm).read₂ zc (complPack (I := I) (O := O) (n := n + 1) k m hkm u
            (snocP (O := O) (n := n + 1) k m hkm o z₀)))).2 t.castSucc)
        (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z) := by
    funext t
    rcases t.eq_castSucc_or_eq_last with ⟨s, ht⟩ | ht
    · rw [ht, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact splitRead₂_out_congr (n := n + 1) k m hkm zc u
        (snocP (O := O) (n := n + 1) k m hkm o z) (snocP (O := O) (n := n + 1) k m hkm o z₀) hv s
    · rw [ht, Fin.snoc_last, Fin.snoc_last]
  rw [splitRead₂_snoc_eq (n := n + 1) k m hkm zc u o z]
  exact Prod.ext (splitRead₂_fst_congr (n := n + 1) k m hkm zc u
      (snocP (O := O) (n := n + 1) k m hkm o z) (snocP (O := O) (n := n + 1) k m hkm o z₀) hv) h2

/-- The plain-form input tuple of a peeled successor-form point: the successor
indices are read back through the value-preserving index equivalence. -/
private def peelU (k m : Nat) (hkm : k + m + 1 ≤ n + 2)
    (i : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j)) :
    ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j) :=
  fun j => i ((compIdxEquiv (n := n + 1) k m hkm).symm j)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The flattened outer configuration induced by a connected configuration and
a packed private configuration. -/
private noncomputable def rowFlat (k m : Nat) (hkm : k + m + 1 ≤ n + 2)
    (zc : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q)
    (u : ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j))
    (v : ∀ j : Fin ((n + 1) + 1 - m), O (compOut (n := n + 1) k m j)) :
    Space I O :=
  splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).read₂ zc
    (complPack (I := I) (O := O) (n := n + 1) k m hkm u v))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Folded form of the row-shape equation. -/
private theorem trunc_row_eq' (k m : Nat) (hkm : k + m + 1 ≤ n + 2)
    (zc : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q)
    (u : ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j))
    (o : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z z₀ : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    rowFlat (I := I) (O := O) k m hkm zc u (snocP (O := O) (n := n + 1) k m hkm o z)
      = ((rowFlat (I := I) (O := O) k m hkm zc u (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
        Fin.snoc (α := fun t : Fin (n + 3) => O t)
          (fun t : Fin (n + 2) =>
            (rowFlat (I := I) (O := O) k m hkm zc u
              (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
          (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z)) :=
  trunc_row_eq (I := I) (O := O) k m hkm zc u o z z₀

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (O j)] in
/-- Inner truncation sum: summing the composite's outer-matrix entries over the
last output value applies the outer comb's normalization peel, with the
condition transferred to the successor-form last input and the K-entry read at
the reference-`z₀` compressed configurations. -/
private theorem trunc_inner (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (_hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (zc zc' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q)
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
        J (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
            (snocP (O := O) (n := n + 1) k m hkm o z))
          (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
            (snocP (O := O) (n := n + 1) k m hkm o' z)))
      = if i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m)) then
          K ((fun j => (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
          ((fun j => (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
          else 0 := by
  have hs1 : (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
          J (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z))
            (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z)))
        = ∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
            J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                    (peelU (I := I) k m hkm i)
                    (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z))
            ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                    (peelU (I := I) k m hkm i')
                    (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z)) :=
    Finset.sum_congr rfl fun z _ => congrArg₂ J
      (trunc_row_eq' (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i) o z z₀)
      (trunc_row_eq' (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i') o' z z₀)
  have hs2 : (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
            J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                    (peelU (I := I) k m hkm i)
                    (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z))
            ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                    (peelU (I := I) k m hkm i')
                    (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z)))
        = ∑ y : O (Fin.last (n + 2)),
            J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                    (peelU (I := I) k m hkm i)
                    (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc) y)
            ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                    (peelU (I := I) k m hkm i')
                    (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc) y) :=
    sum_cast_equiv (congrArg O (compOutS_last (n := n + 1) k m hkm))
      (fun y => J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
            Fin.snoc (α := fun t : Fin (n + 3) => O t)
              (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                  (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc) y)
          ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
            Fin.snoc (α := fun t : Fin (n + 3) => O t)
              (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                  (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc) y))
  have hp := hpeel ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
        (snocP (O := O) (n := n + 1) k m hkm o z₀)).1)
      ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
        (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1)
      (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
        (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
      (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
        (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
  refine (hs1.trans hs2).trans ?_
  rw [hp]
  have hI : (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
        (snocP (O := O) (n := n + 1) k m hkm o z₀)).1 (Fin.last (n + 2))
      = cast (congrArg I (compIn_last (n := n + 1) k m hkm hk))
          (i (Fin.last ((n + 1) - m))) :=
    splitRead₂_lastIn (n := n + 1) k m hkm hk zc' (peelU (I := I) k m hkm i)
      (snocP (O := O) (n := n + 1) k m hkm o z₀)
  have hI' : (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
        (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1 (Fin.last (n + 2))
      = cast (congrArg I (compIn_last (n := n + 1) k m hkm hk))
          (i' (Fin.last ((n + 1) - m))) :=
    splitRead₂_lastIn (n := n + 1) k m hkm hk zc (peelU (I := I) k m hkm i')
      (snocP (O := O) (n := n + 1) k m hkm o' z₀)
  by_cases hcond : i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m))
  · rw [ite_eq_left hcond, ite_eq_left]
    rw [hI, hI']
    exact congrArg _ hcond
  · rw [ite_eq_right hcond, ite_eq_right]
    rw [hI, hI']
    exact fun hcc => hcond ((Equiv.cast
        (congrArg I (compIn_last (n := n + 1) k m hkm hk))).injective hcc)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Depth-coherent row form: the `castSucc` compression of the flattened outer
configuration equals the truncated composite's flattened configuration, read
through the re-embedded private packing of the depth-shift coherence. -/
private theorem trunc_entry (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q)
    (u : ∀ j : Fin ((n + 1) + 1 - m), I (compIn (n := n + 1) k m j))
    (v : ∀ j : Fin ((n + 1) + 1 - m), O (compOut (n := n + 1) k m j)) :
    ((fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz u v).1 t.castSucc),
      fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz u v).2 t.castSucc)
      = splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc)
          (fun t : Fin (n + 2) => O t.castSucc)
          ((suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').read₂ zz
            (complPack (I := fun t : Fin (n + 2) => I t.castSucc)
                (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm'
              (fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
                (u ⟨(j : Nat), by omega⟩))
              (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
                (v ⟨(j : Nat), by omega⟩)))) := by
  rw [read₂_tail (I := I) (O := O) k m hkm hkm' hk zz u v]
  apply Prod.ext
  · funext t
    rfl
  · funext t
    rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Window stability of the inner flattening: the depth-`n` flattening
equivalence of the re-embedded families reads a connected configuration
exactly as the depth-`n + 1` flattening equivalence does. -/
private theorem xflat_tail (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q) :
    (XFlatEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').symm zz
      = (XFlatEquiv (I := I) (O := O) k m hkm).symm zz := by
  rfl

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- True-branch entry expansion: the truncated composite's entry at the peeled
tail points is the window contraction of the tail witness `K` against the
inner comb `X`, with the `K`-entries read at the reference-`z₀` compressed
configurations. -/
private theorem trunc_true_entry (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    WireFam.matReindex (famTailEquiv (I := I) (O := O) k m hkm hkm')
        (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X)
        ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o')
      = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz) *
          K ((fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz'
                  (peelU (I := I) k m hkm i) (snocP (O := O) (n := n + 1) k m hkm o z₀)).1
                t.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz'
                (peelU (I := I) k m hkm i) (snocP (O := O) (n := n + 1) k m hkm o z₀)).2
              t.castSucc)
          ((fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz
                  (peelU (I := I) k m hkm i') (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1
                t.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz
                (peelU (I := I) k m hkm i') (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2
              t.castSucc) := by
  have hA := WireFam.matReindex_apply (famTailEquiv (I := I) (O := O) k m hkm hkm')
    (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X)
    ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o')
  rw [hA]
  have hB : suffixCompS (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' K X
      ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i j.castSucc), o))
      ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i' j.castSucc), o'))
      = suffixComp (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' K X
          (spaceIdxEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm'
            ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i j.castSucc), o)))
          (spaceIdxEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm'
            ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i' j.castSucc), o'))) :=
    rfl
  rw [hB]
  rw [tailConfig_eq (I := I) (O := O) k m hkm hkm' i o z₀,
    tailConfig_eq (I := I) (O := O) k m hkm hkm' i' o' z₀]
  have hC := suffixComp_apply (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' K X
      ((fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
          (i ((compIdxEquiv (n := n + 1) k m hkm).symm ⟨(j : Nat), by omega⟩))),
        (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
          (snocP (O := O) (n := n + 1) k m hkm o z₀ ⟨(j : Nat), by omega⟩)))
      ((fun j => cast (congrArg I (compIn_tail_eq k m hkm hkm' j))
          (i' ((compIdxEquiv (n := n + 1) k m hkm).symm ⟨(j : Nat), by omega⟩))),
        (fun j => cast (congrArg O (compOut_tail_eq k m hkm hkm' j))
          (snocP (O := O) (n := n + 1) k m hkm o' z₀ ⟨(j : Nat), by omega⟩)))
  have hR : ∀ z : ∀ i, (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm').connFam₁ i,
      (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm').read₁
        ((fun j => absurd j.isLt (by simp only [suffixMatch]; omega)), z) = z := by
    intro z
    funext i
    exact WireMatch.read₁_conn (suffixMatch (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm')
      (fun j => absurd j.isLt (by simp only [suffixMatch]; omega)) z i
  refine hC.trans (Finset.sum_congr rfl fun zz _ => Finset.sum_congr rfl fun zz' _ => ?_)
  refine congrArg₂ (fun (a b : ℂ) => a * b) ?_ ?_
  · exact congrArg₂ X
      ((congrArg ((XFlatEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').symm)
        (hR zz')).trans
        (xflat_tail (I := I) (O := O) k m hkm hkm' zz'))
      ((congrArg ((XFlatEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm').symm)
        (hR zz)).trans
        (xflat_tail (I := I) (O := O) k m hkm hkm' zz))
  · exact (congrArg₂ K
      (trunc_entry (I := I) (O := O) k m hkm hkm' hk zz'
        (peelU (I := I) k m hkm i) (snocP (O := O) (n := n + 1) k m hkm o z₀))
      (trunc_entry (I := I) (O := O) k m hkm hkm' hk zz
        (peelU (I := I) k m hkm i') (snocP (O := O) (n := n + 1) k m hkm o' z₀))).symm

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- Per-`z` expansion of the untruncated composite entry: peeling the
successor-form packaging and applying the entrywise suffix composition at
depth `n + 1`. -/
private theorem trunc_eq_expand (k m : Nat) (hkm : k + m + 1 ≤ n + 2)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    suffixCompS (I := I) (O := O) (n := n + 1) k m hkm J X
        (i, Fin.snoc o z) (i', Fin.snoc o' z)
      = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz) *
          J (rowFlat (I := I) (O := O) k m hkm zz' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z))
            (rowFlat (I := I) (O := O) k m hkm zz (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z)) := by
  refine (suffixComp_apply (I := I) (O := O) (n := n + 1) k m hkm J X
      (spaceIdxEquiv (I := I) (O := O) (n := n + 1) k m hkm (i, Fin.snoc o z))
      (spaceIdxEquiv (I := I) (O := O) (n := n + 1) k m hkm (i', Fin.snoc o' z))).trans
    (Finset.sum_congr rfl fun zz _ => Finset.sum_congr rfl fun zz' _ => ?_)
  refine congrArg₂ (fun (a b : ℂ) => a * b) ?_ ?_
  · exact congrArg₂ X
      (congrArg (XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm
        (suffixRead₁ (I := I) (O := O) (n := n + 1) k m hkm _ zz'))
      (congrArg (XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm
        (suffixRead₁ (I := I) (O := O) (n := n + 1) k m hkm _ zz))
  · exact congrArg₂ J rfl rfl

omit [∀ j, DecidableEq (O j)] in
/-- Sum rearrangement: pulling the last-output sum inside the window
contraction and applying the outer peel per connected configuration. -/
private theorem trunc_eq_swap (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
        ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz) *
          J (rowFlat (I := I) (O := O) k m hkm zz' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z))
            (rowFlat (I := I) (O := O) k m hkm zz (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z)))
      = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz) *
          (if i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m)) then
            K ((fun j => (rowFlat (I := I) (O := O) k m hkm zz' (peelU (I := I) k m hkm i)
                    (snocP (O := O) (n := n + 1) k m hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz' (peelU (I := I) k m hkm i)
                (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k m hkm zz (peelU (I := I) k m hkm i')
                    (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz (peelU (I := I) k m hkm i')
                (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
          else 0) := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun zz _ =>
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun zz' _ => ?_)))
  refine (Finset.mul_sum _ _ _).symm.trans ?_
  exact congrArg _ (trunc_inner k m hkm hkm' hk J K hpeel zz zz' i i' o o' z₀)

omit [∀ j, DecidableEq (O j)] in
/-- The truncation equation, nonempty corner: summing the untruncated
composite over the last output value applies the outer comb's peel, leaving
the truncated composite of the tail witness `K` against `X`. -/
private theorem trunc_eq_core (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
        suffixCompS (I := I) (O := O) (n := n + 1) k m hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = if i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m)) then
          WireFam.matReindex (famTailEquiv (I := I) (O := O) k m hkm hkm')
            (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X)
            ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o')
        else 0 := by
  have hSum : (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
          suffixCompS (I := I) (O := O) (n := n + 1) k m hkm J X
            (i, Fin.snoc o z) (i', Fin.snoc o' z))
        = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
          ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q,
            X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz')
                ((XFlatEquiv (I := I) (O := O) (n := n + 1) k m hkm).symm zz) *
            (if i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m)) then
              K ((fun j => (rowFlat (I := I) (O := O) k m hkm zz' (peelU (I := I) k m hkm i)
                      (snocP (O := O) (n := n + 1) k m hkm o z₀)).1 j.castSucc),
                fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
              ((fun j => (rowFlat (I := I) (O := O) k m hkm zz (peelU (I := I) k m hkm i')
                      (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1 j.castSucc),
                fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zz (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
            else 0) :=
    (Finset.sum_congr rfl fun z _ =>
      trunc_eq_expand (I := I) (O := O) k m hkm J X i i' o o' z).trans
      (trunc_eq_swap (I := I) (O := O) k m hkm hkm' hk J K hpeel X i i' o o' z₀)
  refine hSum.trans ?_
  by_cases hcond : i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m))
  · rw [ite_eq_left hcond]
    refine (Finset.sum_congr rfl fun zz _ => Finset.sum_congr rfl fun zz' _ => ?_).trans
      (trunc_true_entry k m hkm hkm' hk K X i i' o o' z₀).symm
    rw [ite_eq_left hcond]
  · rw [ite_eq_right hcond]
    refine Finset.sum_eq_zero fun zz _ => Finset.sum_eq_zero fun zz' _ => ?_
    rw [ite_eq_right hcond, mul_zero]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (O j)] in
/-- Vanishing of the tail witness in the empty corner: if the composite's
last output type is empty, the peel hypothesis forces every entry of `K`
to vanish. -/
private theorem kzero_of_empty (k m : Nat) (hkm : k + m + 1 ≤ n + 2)
    (hk : k < (n + 1) - m)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (i : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (hE : IsEmpty (O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))))
    (A B : Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)) :
    K A B = 0 := by
  have hE' : IsEmpty (O (Fin.last (n + 2))) :=
    congrArg O (compOutS_last (n := n + 1) k m hkm) ▸ hE
  have xI : I (Fin.last (n + 2)) :=
    cast (congrArg I (compInS_last (n := n + 1) k m hkm hk)) (i (Fin.last ((n + 1) - m)))
  exact peel_zero_of_empty_output J K hpeel hE' xI A B

omit [∀ j, DecidableEq (O j)] in
/-- The truncation equation, empty corner: if the composite's last output
type is empty, both sides vanish — the left sum is over an empty type and
the truncated composite vanishes entrywise because `K` does. -/
private theorem trunc_eq_empty (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (hE : IsEmpty (O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))))) :
    (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
        suffixCompS (I := I) (O := O) (n := n + 1) k m hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = if i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m)) then
          WireFam.matReindex (famTailEquiv (I := I) (O := O) k m hkm hkm')
            (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X)
            ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o')
        else 0 := by
  have hL : (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
        suffixCompS (I := I) (O := O) (n := n + 1) k m hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z)) = 0 :=
    Finset.sum_eq_zero fun z _ => hE.elim z
  refine hL.trans ?_
  by_cases hcond : i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m))
  · rw [ite_eq_left hcond]
    refine Eq.symm ?_
    refine (WireFam.matReindex_apply (famTailEquiv (I := I) (O := O) k m hkm hkm')
        (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X)
        ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o')).trans ?_
    have hB : suffixCompS (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' K X
        ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i j.castSucc), o))
        ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i' j.castSucc), o'))
        = suffixComp (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' K X
            (spaceIdxEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
                (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm'
              ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i j.castSucc), o)))
            (spaceIdxEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
                (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm'
              ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i' j.castSucc), o'))) :=
      rfl
    refine hB.trans ?_
    have hC := suffixComp_apply (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm' K X
        (spaceIdxEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm'
          ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i j.castSucc), o)))
        (spaceIdxEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm'
          ((famTailEquiv (I := I) (O := O) k m hkm hkm').symm ((fun j => i' j.castSucc), o')))
    refine hC.trans ?_
    exact Finset.sum_eq_zero fun zz _ => Finset.sum_eq_zero fun zz' _ =>
      mul_eq_zero.mpr (Or.inr (kzero_of_empty k m hkm hk J K hpeel i hE _ _))
  · rw [ite_eq_right hcond]

omit [∀ j, DecidableEq (O j)] in
/-- The truncation equation: summing the untruncated composite over the last
output value applies the outer comb's normalization peel, leaving the
truncated composite of the tail witness `K` against the inner comb `X`. -/
private theorem trunc_eq (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc)) :
    (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
        suffixCompS (I := I) (O := O) (n := n + 1) k m hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = if i (Fin.last ((n + 1) - m)) = i' (Fin.last ((n + 1) - m)) then
          WireFam.matReindex (famTailEquiv (I := I) (O := O) k m hkm hkm')
            (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X)
            ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o')
        else 0 := by
  rcases isEmpty_or_nonempty (O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))))
    with hE | hNE
  · exact trunc_eq_empty k m hkm hkm' hk J K hpeel X i i' o o' hE
  · obtain ⟨z₀⟩ := hNE
    exact trunc_eq_core k m hkm hkm' hk J K hpeel X i i' o o' z₀

/-- The normalization induction step: if the truncated composite of the tail
witness `K` against `X` is normalized, then the untruncated composite is
normalized, with that truncated composite as its own tail witness. -/
private theorem normalized_succ_of_trunc (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkm' : k + m + 1 ≤ n + 1)
    (hk : k < (n + 1) - m)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (hJpos : J.PosSemidef)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (hXpos : X.PosSemidef)
    (hKWnorm : Normalized
      (fun j : Fin (n + 1 - m) => I (compInS (n := n + 1) k m hkm j.castSucc))
      (fun j : Fin (n + 1 - m) => O (compOutS (n := n + 1) k m hkm j.castSucc))
      (WireFam.matReindex (famTailEquiv (I := I) (O := O) k m hkm hkm')
        (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X))) :
    Normalized
      (fun j : Fin (n + 1 - m + 1) => I (compInS (n := n + 1) k m hkm j))
      (fun j : Fin (n + 1 - m + 1) => O (compOutS (n := n + 1) k m hkm j))
      (suffixCompS (I := I) (O := O) (n := n + 1) k m hkm J X) := by
  refine ⟨?_, _, hKWnorm, ?_⟩
  · exact matReindex_posSemidef _
      (suffixComp_posSemidef (n := n + 1) k m hkm J X hJpos hXpos)
  · intro ii ii' oo oo'
    exact trunc_eq k m hkm hkm' hk J K hpeel X ii ii' oo oo'

omit [∀ j, Fintype (I j)] in
/-- Inner truncation sum at the boundary: summing the composite's outer-matrix
entries over the last output value applies the outer comb's normalization peel,
with the condition transferred to the connected configurations' last
input-side entries (the window's top output wire is the outer last input). -/
private theorem bnd_inner (k m : Nat) (hkm : k + m + 1 ≤ n + 2) (hkb : k + m + 1 = n + 2)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (zc zc' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k m hkm).connFam₁ q)
    (i i' : ∀ j : Fin ((n + 1) - m + 1), I (compInS (n := n + 1) k m hkm j))
    (o o' : ∀ j : Fin ((n + 1) - m), O (compOutS (n := n + 1) k m hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m)))) :
    (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
        J (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
            (snocP (O := O) (n := n + 1) k m hkm o z))
          (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
            (snocP (O := O) (n := n + 1) k m hkm o' z)))
      = if zc' (Fin.natAdd (m + 1) (Fin.last m)) = zc (Fin.natAdd (m + 1) (Fin.last m)) then
          K ((fun j => (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
          ((fun j => (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
          else 0 := by
  have hs1 : (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
          J (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z))
            (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z)))
        = ∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
            J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                    (peelU (I := I) k m hkm i)
                    (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z))
            ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                    (peelU (I := I) k m hkm i')
                    (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z)) :=
    Finset.sum_congr rfl fun z _ => congrArg₂ J
      (trunc_row_eq' (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i) o z z₀)
      (trunc_row_eq' (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i') o' z z₀)
  have hs2 : (∑ z : O (compOutS (n := n + 1) k m hkm (Fin.last ((n + 1) - m))),
            J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                    (peelU (I := I) k m hkm i)
                    (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z))
            ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                    (peelU (I := I) k m hkm i')
                    (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := n + 1) k m hkm)) z)))
        = ∑ y : O (Fin.last (n + 2)),
            J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                    (peelU (I := I) k m hkm i)
                    (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc) y)
            ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (n + 3) => O t)
                (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                    (peelU (I := I) k m hkm i')
                    (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc) y) :=
    sum_cast_equiv (congrArg O (compOutS_last (n := n + 1) k m hkm))
      (fun y => J ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
              (snocP (O := O) (n := n + 1) k m hkm o z₀)).1,
            Fin.snoc (α := fun t : Fin (n + 3) => O t)
              (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc'
                  (peelU (I := I) k m hkm i)
                  (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc) y)
          ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
              (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1,
            Fin.snoc (α := fun t : Fin (n + 3) => O t)
              (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc
                  (peelU (I := I) k m hkm i')
                  (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc) y))
  have hp := hpeel ((rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
        (snocP (O := O) (n := n + 1) k m hkm o z₀)).1)
      ((rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
        (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1)
      (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
        (snocP (O := O) (n := n + 1) k m hkm o z₀)).2 t.castSucc)
      (fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
        (snocP (O := O) (n := n + 1) k m hkm o' z₀)).2 t.castSucc)
  refine (hs1.trans hs2).trans ?_
  rw [hp]
  have hI : (rowFlat (I := I) (O := O) k m hkm zc' (peelU (I := I) k m hkm i)
        (snocP (O := O) (n := n + 1) k m hkm o z₀)).1 (Fin.last (n + 2))
      = cast (connFam₁_natAdd_last_bnd (I := I) (O := O) (n := n + 1) k m hkm hkb)
          (zc' (Fin.natAdd (m + 1) (Fin.last m))) :=
    splitRead₂_lastIn_bnd (n := n + 1) k m hkm hkb zc' (peelU (I := I) k m hkm i)
      (snocP (O := O) (n := n + 1) k m hkm o z₀)
  have hI' : (rowFlat (I := I) (O := O) k m hkm zc (peelU (I := I) k m hkm i')
        (snocP (O := O) (n := n + 1) k m hkm o' z₀)).1 (Fin.last (n + 2))
      = cast (connFam₁_natAdd_last_bnd (I := I) (O := O) (n := n + 1) k m hkm hkb)
          (zc (Fin.natAdd (m + 1) (Fin.last m))) :=
    splitRead₂_lastIn_bnd (n := n + 1) k m hkm hkb zc (peelU (I := I) k m hkm i')
      (snocP (O := O) (n := n + 1) k m hkm o' z₀)
  by_cases hcond : zc' (Fin.natAdd (m + 1) (Fin.last m)) = zc (Fin.natAdd (m + 1) (Fin.last m))
  · rw [ite_eq_left hcond, ite_eq_left]
    rw [hI, hI']
    exact congrArg _ hcond
  · rw [ite_eq_right hcond, ite_eq_right]
    rw [hI, hI']
    exact fun hcc => hcond ((Equiv.cast
        (connFam₁_natAdd_last_bnd (I := I) (O := O) (n := n + 1) k m hkm hkb)).injective hcc)

/-- Snoc decomposition of a sum over a paired configuration space: the outer
block family first, then the inner one, each split at its last wire. -/
private theorem sum_space_snoc {N : Nat} {W₁ W₂ : Fin (N + 1) → Type u}
    [∀ j, Fintype (W₁ j)] [∀ j, DecidableEq (W₁ j)]
    [∀ j, Fintype (W₂ j)] [∀ j, DecidableEq (W₂ j)]
    {β : Type*} [AddCommMonoid β] (F : Space W₁ W₂ → β) :
    (∑ v : Space W₁ W₂, F v) =
      ∑ zcO : ∀ j : Fin N, W₁ j.castSucc, ∑ wO : W₁ (Fin.last N),
        ∑ zcI : ∀ j : Fin N, W₂ j.castSucc, ∑ wI : W₂ (Fin.last N),
          F (Fin.snoc zcO wO, Fin.snoc zcI wI) := by
  rw [Fintype.sum_prod_type]
  refine Eq.trans (sum_pi_snoc (α := W₁) (F := fun ob => ∑ ib : ∀ j, W₂ j, F (ob, ib))) ?_
  exact Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun wO _ =>
    sum_pi_snoc (α := W₂) (F := fun ib => F (Fin.snoc zcO wO, ib))

/-- Double snoc decomposition: both the row and the column configuration
spaces of a two-level sum split into their four-wire form. -/
private theorem sum_space_snoc2 {N : Nat} {W₁ W₂ : Fin (N + 1) → Type u}
    [∀ j, Fintype (W₁ j)] [∀ j, DecidableEq (W₁ j)]
    [∀ j, Fintype (W₂ j)] [∀ j, DecidableEq (W₂ j)]
    {β : Type*} [AddCommMonoid β] (G : Space W₁ W₂ → Space W₁ W₂ → β) :
    (∑ v₁ : Space W₁ W₂, ∑ v₂ : Space W₁ W₂, G v₁ v₂) =
      ∑ zcO : ∀ j : Fin N, W₁ j.castSucc, ∑ wO : W₁ (Fin.last N),
        ∑ zcI : ∀ j : Fin N, W₂ j.castSucc, ∑ zcO' : ∀ j : Fin N, W₁ j.castSucc,
        ∑ wO' : W₁ (Fin.last N), ∑ zcI' : ∀ j : Fin N, W₂ j.castSucc,
        ∑ wI : W₂ (Fin.last N), ∑ wI' : W₂ (Fin.last N),
          G (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.snoc zcO' wO', Fin.snoc zcI' wI') := by
  rw [sum_space_snoc (F := fun v₁ => ∑ v₂, G v₁ v₂)]
  refine Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun wO _ =>
    Finset.sum_congr rfl fun zcI _ => ?_
  refine Eq.trans (Finset.sum_congr rfl fun wI _ =>
      sum_space_snoc (F := fun v₂ => G (Fin.snoc zcO wO, Fin.snoc zcI wI) v₂)) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun zcO' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun wO' _ => ?_
  rw [Finset.sum_comm]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary depth-shift coherence of the composite input map: at the boundary
only the prefix branch fires, so the deeper composite's input index agrees with
the truncated composite's, embedded by `Fin.castSucc`. -/
private theorem compInS_bnd_tail_eq (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1) (j : Fin (n - m + 1)) :
    compInS (n := n + 1) k (m + 1) hkm (Fin.cast (by omega) j)
      = Fin.castSucc (compInS (n := n) k m hkm0 j) := by
  apply Fin.ext
  simp only [compInS_val, Fin.val_cast, Fin.val_castSucc]
  split
  · rfl
  · omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary depth-shift coherence of the composite output map at the
non-final teeth: only the prefix branch fires there. -/
private theorem compOutS_bnd_tail_eq (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1) (j : Fin (n - m)) :
    compOutS (n := n + 1) k (m + 1) hkm (Fin.cast (by omega) j.castSucc)
      = Fin.castSucc (compOutS (n := n) k m hkm0 j.castSucc) := by
  apply Fin.ext
  simp only [compOutS_val, Fin.val_cast, Fin.val_castSucc, Fin.val_castSucc]
  split
  · rfl
  · omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation: the level-one connected tuple at a non-final
output-side index reads off the truncated output block. -/
private theorem zcBnd_castAdd (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
    (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1))) (t : Fin (m + 2))
    (ht : (t : Nat) < m + 1) :
    XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.castAdd (m + 2) t)
      = cast (append_castAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          t).symm (zcO ⟨(t : Nat), ht⟩) := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_left, Equiv.cast_apply]
  have hs : Fin.snoc zcO wO t = zcO ⟨(t : Nat), ht⟩ := by
    rcases t with ⟨tv, htv⟩
    exact Fin.snoc_castSucc wO zcO ⟨tv, ht⟩
  rw [hs]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation: the level-one connected tuple at the final
output-side index reads off the pending output value. -/
private theorem zcBnd_castAdd_last (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
    (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1))) :
    XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.castAdd (m + 2) (Fin.last (m + 1)))
      = cast (append_castAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          (Fin.last (m + 1))).symm wO := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_left,
    Fin.snoc_last, Equiv.cast_apply]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation: the level-one connected tuple at a non-final
input-side index reads off the truncated input block. -/
private theorem zcBnd_natAdd (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
    (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1))) (t : Fin (m + 2))
    (ht : (t : Nat) < m + 1) :
    XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.natAdd (m + 2) t)
      = cast (append_natAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          t).symm (zcI ⟨(t : Nat), ht⟩) := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_right, Equiv.cast_apply]
  have hs : Fin.snoc zcI wI t = zcI ⟨(t : Nat), ht⟩ := by
    rcases t with ⟨tv, htv⟩
    exact Fin.snoc_castSucc wI zcI ⟨tv, ht⟩
  rw [hs]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation: the level-one connected tuple at the final
input-side index reads off the pending input value. -/
private theorem zcBnd_natAdd_last (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
    (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1))) :
    XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.natAdd (m + 2) (Fin.last (m + 1)))
      = cast (append_natAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          (Fin.last (m + 1))).symm wI := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_right,
    Fin.snoc_last, Equiv.cast_apply]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation at the reduced depth: the connected tuple at
an output-side index reads off the truncated output block. -/
private theorem zcBnd0_castAdd (k m : Nat) (hkm0 : k + m + 1 ≤ n + 1)
    (zcO0 : ∀ j : Fin (m + 1),
      suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0 j)
    (zcI0 : ∀ j : Fin (m + 1),
      suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0 j) (t : Fin (m + 1)) :
    XFlatEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0 (zcO0, zcI0)
        (Fin.castAdd (m + 1) t)
      = cast (append_castAdd (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0)
          (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0) t).symm (zcO0 t) := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_left, Equiv.cast_apply]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation at the reduced depth: the connected tuple at
an input-side index reads off the truncated input block. -/
private theorem zcBnd0_natAdd (k m : Nat) (hkm0 : k + m + 1 ≤ n + 1)
    (zcO0 : ∀ j : Fin (m + 1),
      suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0 j)
    (zcI0 : ∀ j : Fin (m + 1),
      suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0 j) (t : Fin (m + 1)) :
    XFlatEquiv (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0 (zcO0, zcI0)
        (Fin.natAdd (m + 1) t)
      = cast (append_natAdd (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0)
          (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0) t).symm (zcI0 t) := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_right, Equiv.cast_apply]

/-- Boundary-transported truncated free input tuple: at the boundary the
deeper composite's input family agrees with the truncated composite's, so the
free input point drops a depth by a cast along `compInS_bnd_tail_eq`. -/
private def bndI0 (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (i : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j)) :
    ∀ j : Fin (n - m + 1), I (Fin.castSucc (compInS (n := n) k m hkm0 j)) :=
  fun j => cast (congrArg I (compInS_bnd_tail_eq k m hkm hkb hkm0 j))
    (i (Fin.cast (by omega) j))

/-- Boundary-transported truncated free output tuple. -/
private def bndO0 (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc)) :
    ∀ j : Fin (n - m), O (Fin.castSucc (compOutS (n := n) k m hkm0 j.castSucc)) :=
  fun j => cast (congrArg O (compOutS_bnd_tail_eq k m hkm hkb hkm0 j))
    (o (Fin.cast (by omega) j))

/-- Boundary depth-shift coherence of the pending output wire: the inner
comb's last input wire is the truncated composite's last output wire. -/
private theorem bnd_pending_eq (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1) :
    suffixOutIdx (n := n + 1) k (m + 1) hkm (Fin.last (m + 1))
      = Fin.castSucc (compOutS (n := n) k m hkm0 (Fin.last (n - m))) := by
  apply Fin.ext
  have hlast := congrArg Fin.val (compOutS_last (n := n) k m hkm0)
  simp only [suffixOutIdx, Fin.val_last, Fin.val_castSucc] at hlast ⊢
  omega

/-- Boundary-transported pending output value. -/
private def bndW0 (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1))) :
    O (Fin.castSucc (compOutS (n := n) k m hkm0 (Fin.last (n - m)))) :=
  cast (congrArg O (bnd_pending_eq k m hkm hkb hkm0)) wO

/-- The reduced-depth plain-form input tuple: the boundary-transported
successor point read back through the value-preserving index equivalence. -/
private def bndU0 (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (i : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j)) :
    ∀ j : Fin (n + 1 - m), (fun t : Fin (n + 2) => I t.castSucc) (compIn (n := n) k m j) :=
  fun j => bndI0 k m hkm hkb hkm0 i ((compIdxEquiv (n := n) k m hkm0).symm j)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Unfolding the reduced-depth input tuple. -/
private theorem bndU0_apply (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (i : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (j : Fin (n + 1 - m)) :
    bndU0 k m hkm hkb hkm0 i j
      = cast (congrArg I (compInS_bnd_tail_eq k m hkm hkb hkm0
          ((compIdxEquiv (n := n) k m hkm0).symm j)))
        (i (Fin.cast (by omega) ((compIdxEquiv (n := n) k m hkm0).symm j))) := rfl

/-- The reduced-depth plain-form output tuple: the boundary-transported
snoc-packing with the pending output value in the last slot. -/
private def bndV0 (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1))) :
    ∀ j : Fin (n + 1 - m), (fun t : Fin (n + 2) => O t.castSucc) (compOut (n := n) k m j) :=
  snocP (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0
    (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary readback coherence at input-side positions: the reduced-depth
readback at a truncated input position agrees with the boundary-depth
readback, with the packing collapsed onto the truncated blocks. -/
private theorem read₂_bnd_castAdd (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
    (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1)))
    (i : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1)))))
    (s : Fin (n + 2)) :
    cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)
        ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).read₂
          (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
          (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
            (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO))
          (Fin.castAdd (n + 2) s))
      = cast (append_castAdd I O s.castSucc)
          ((suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).read₂
            (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
              (Fin.snoc zcO wO, Fin.snoc zcI wI))
            (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
              (peelU (I := I) k (m + 1) hkm i)
              (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀))
            (Fin.castAdd (n + 3) s.castSucc)) := by
  have hs := s.isLt
  rcases Nat.lt_or_ge (s : Nat) (k + 1) with hA | hA'
  · -- below the window: private input wire at both depths
    have hltT : (s : Nat) < n + 1 - m := by omega
    have hltP : (s : Nat) < (n + 1) + 1 - (m + 1) := by omega
    have hposT : complEmb (suffixConnIdx (n := n) k m hkm0)
        (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).hι₂ ⟨(s : Nat), by omega⟩
        = Fin.castAdd (n + 2) s := by
      rw [suffixComplEmb k m hkm0 (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).hι₂
          ⟨(s : Nat), by omega⟩,
        suffixComplIdx_of_lt_le k m hkm0 ⟨(s : Nat), by omega⟩ hltT
          (by show (s : Nat) ≤ k; omega)]
    have hcT := read₂_congr_pos (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
      (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
      (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) hposT
    have hposP : complEmb (suffixConnIdx (n := n + 1) k (m + 1) hkm)
        (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).hι₂ ⟨(s : Nat), by omega⟩
        = Fin.castAdd (n + 3) s.castSucc := by
      rw [suffixComplEmb (n := n + 1) k (m + 1) hkm
          (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).hι₂ ⟨(s : Nat), by omega⟩,
        suffixComplIdx_of_lt_le (n := n + 1) k (m + 1) hkm ⟨(s : Nat), by omega⟩ hltP
          (by show (s : Nat) ≤ k; omega)]
      exact congrArg (Fin.castAdd (n + 3)) (Fin.ext (by simp))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k (m + 1) hkm
      (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI))
      (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (peelU (I := I) k (m + 1) hkm i)
        (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) hposP
    refine Eq.trans (congrArg (cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_castAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_compl (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
        (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
          (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) ⟨(s : Nat), by omega⟩,
      complPack_lt (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO) ⟨(s : Nat), by omega⟩ hltT,
      suffixRead₂_compl (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (Fin.snoc zcO wO, Fin.snoc zcI wI))
        (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (peelU (I := I) k (m + 1) hkm i)
          (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) ⟨(s : Nat), by omega⟩,
      complPack_lt (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (peelU (I := I) k (m + 1) hkm i) (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)
        ⟨(s : Nat), by omega⟩ hltP,
      bndU0_apply k m hkm hkb hkm0 i ⟨(s : Nat), by omega⟩]
    have hvalP : peelU (I := I) k (m + 1) hkm i ⟨(s : Nat), by omega⟩
        = i ((compIdxEquiv (n := n + 1) k (m + 1) hkm).symm ⟨(s : Nat), by omega⟩) := rfl
    rw [hvalP]
    exact (cast4 (congrArg I (compInS_bnd_tail_eq k m hkm hkb hkm0
            ((compIdxEquiv (n := n) k m hkm0).symm ⟨(s : Nat), by omega⟩)))
        (complFam₂_eq_lt (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0 ⟨(s : Nat), by omega⟩ hltT).symm
        (congrArg (append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)) hposT)
        (append_castAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)
        (i (Fin.cast (by omega) ((compIdxEquiv (n := n) k m hkm0).symm ⟨(s : Nat), by omega⟩)))).trans
      (cast3 (complFam₂_eq_lt (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          ⟨(s : Nat), by omega⟩ hltP).symm
        (congrArg (append I O) hposP) (append_castAdd I O s.castSucc)
        (i ((compIdxEquiv (n := n + 1) k (m + 1) hkm).symm ⟨(s : Nat), by omega⟩))).symm
  · -- inside the window: connected input wire at both depths
    have ht : (s : Nat) - (k + 1) < m + 1 := by omega
    have htP : (s : Nat) - (k + 1) < m + 2 := by omega
    have hposT : suffixConnIdx (n := n) k m hkm0 (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = Fin.castAdd (n + 2) s := by
      rw [suffixConnIdx_natAdd]
      exact congrArg (Fin.castAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
      (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
      (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) hposT
    have hposP : suffixConnIdx (n := n + 1) k (m + 1) hkm
        (Fin.natAdd (m + 2) ⟨(s : Nat) - (k + 1), htP⟩) = Fin.castAdd (n + 3) s.castSucc := by
      rw [suffixConnIdx_natAdd]
      exact congrArg (Fin.castAdd (n + 3))
        (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k (m + 1) hkm
      (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI))
      (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (peelU (I := I) k (m + 1) hkm i)
        (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) hposP
    refine Eq.trans (congrArg (cast (append_castAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_castAdd I O s.castSucc)) hcP)
    have hEq0 : (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).connFam₁
        (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) (suffixConnIdx (n := n) k m hkm0
            (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)) := by
      show append (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0) (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0)
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩) = _
      rw [append_natAdd, suffixConnIdx_natAdd, append_castAdd]
      rfl
    have hEq1 : (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁
        (Fin.natAdd (m + 2) ⟨(s : Nat) - (k + 1), htP⟩)
        = append I O (suffixConnIdx (n := n + 1) k (m + 1) hkm
            (Fin.natAdd (m + 2) ⟨(s : Nat) - (k + 1), htP⟩)) := by
      show append (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          (Fin.natAdd (m + 2) ⟨(s : Nat) - (k + 1), htP⟩) = _
      rw [append_natAdd, suffixConnIdx_natAdd, append_castAdd]
      rfl
    rw [suffixRead₂_conn_natAdd (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
        (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
          (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) ⟨(s : Nat) - (k + 1), ht⟩,
      suffixRead₂_conn_natAdd (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (Fin.snoc zcO wO, Fin.snoc zcI wI))
        (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (peelU (I := I) k (m + 1) hkm i)
          (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) ⟨(s : Nat) - (k + 1), htP⟩,
      show (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).eRelabel
          (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
          (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)
        = cast hEq0 (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI)
            (Fin.natAdd (m + 1) ⟨(s : Nat) - (k + 1), ht⟩)) from rfl,
      zcBnd0_natAdd k m hkm0 zcO zcI ⟨(s : Nat) - (k + 1), ht⟩,
      show (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).eRelabel
          (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
            (Fin.snoc zcO wO, Fin.snoc zcI wI))
          (Fin.natAdd (m + 2) ⟨(s : Nat) - (k + 1), htP⟩)
        = cast hEq1 (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
            (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.natAdd (m + 2) ⟨(s : Nat) - (k + 1), htP⟩))
          from rfl,
      zcBnd_natAdd k m hkm zcO wO zcI wI ⟨(s : Nat) - (k + 1), htP⟩ (by omega)]
    exact (cast4 (append_natAdd (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0) (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0)
          ⟨(s : Nat) - (k + 1), ht⟩).symm hEq0
        (congrArg (append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)) hposT) (append_castAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)
        (zcI ⟨(s : Nat) - (k + 1), ht⟩)).trans
      (cast4 (append_natAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          ⟨(s : Nat) - (k + 1), htP⟩).symm hEq1
        (congrArg (append I O) hposP) (append_castAdd I O s.castSucc)
        (zcI ⟨(s : Nat) - (k + 1), by omega⟩)).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The reduced-depth output packing at a non-final index reads off the
boundary-transported truncated output tuple. -/
private theorem bndV0_lt (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1))) (j : Fin (n + 1 - m))
    (hj : (j : Nat) < n - m) :
    bndV0 k m hkm hkb hkm0 o wO j
      = cast (congrArg O (compOutS_bnd_tail_eq k m hkm hkb hkm0 ⟨(j : Nat), hj⟩))
          (o (Fin.cast (by omega) ⟨(j : Nat), hj⟩)) := by
  exact Fin.snoc_castSucc
    (α := fun i : Fin (n - m + 1) => O (Fin.castSucc (compOutS (n := n) k m hkm0 i)))
    (bndW0 k m hkm hkb hkm0 wO) (bndO0 k m hkm hkb hkm0 o) ⟨(j : Nat), hj⟩

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The reduced-depth output packing at the final index reads off the pending
output value. -/
private theorem bndV0_last (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1))) :
    bndV0 k m hkm hkb hkm0 o wO ⟨n - m, by omega⟩
      = cast (congrArg O (bnd_pending_eq k m hkm hkb hkm0)) wO :=
  snocP_last (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary readback coherence at output-side positions: the reduced-depth
readback at a truncated output position agrees with the boundary-depth
readback; at the boundary position the pending value moves from the connected
block to the private final slot. -/
private theorem read₂_bnd_natAdd (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
    (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1)))
    (i : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1)))))
    (s : Fin (n + 2)) :
    cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)
        ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).read₂
          (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
          (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
            (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO))
          (Fin.natAdd (n + 2) s))
      = cast (append_natAdd I O s.castSucc)
          ((suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).read₂
            (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
              (Fin.snoc zcO wO, Fin.snoc zcI wI))
            (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
              (peelU (I := I) k (m + 1) hkm i)
              (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀))
            (Fin.natAdd (n + 3) s.castSucc)) := by
  have hs := s.isLt
  rcases Nat.lt_or_ge (s : Nat) k with hA | hA'
  · -- below the window: private output wire at both depths
    have hltT : (s : Nat) < n + 1 - m := by omega
    have hltT' : (s : Nat) < n - m := by omega
    have hltP : (s : Nat) < (n + 1) + 1 - (m + 1) := by omega
    have hltP' : (s : Nat) < (n + 1) - (m + 1) := by omega
    have hposT : complEmb (suffixConnIdx (n := n) k m hkm0)
        (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).hι₂ ⟨(n + 1 - m) + (s : Nat), by omega⟩
        = Fin.natAdd (n + 2) s := by
      rw [suffixComplEmb k m hkm0 (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).hι₂
          ⟨(n + 1 - m) + (s : Nat), by omega⟩,
        suffixComplIdx_of_ge_lt k m hkm0 ⟨(n + 1 - m) + (s : Nat), by omega⟩
          (by show ¬((n + 1 - m) + (s : Nat) < n + 1 - m); omega)
          (by show (n + 1 - m) + (s : Nat) - (n + 1 - m) < k; omega)]
      exact congrArg (Fin.natAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
      (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
      (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) hposT
    have hposP : complEmb (suffixConnIdx (n := n + 1) k (m + 1) hkm)
        (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).hι₂
        ⟨((n + 1) + 1 - (m + 1)) + (s : Nat), by omega⟩ = Fin.natAdd (n + 3) s.castSucc := by
      rw [suffixComplEmb (n := n + 1) k (m + 1) hkm
          (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).hι₂
          ⟨((n + 1) + 1 - (m + 1)) + (s : Nat), by omega⟩,
        suffixComplIdx_of_ge_lt (n := n + 1) k (m + 1) hkm ⟨((n + 1) + 1 - (m + 1)) + (s : Nat), by omega⟩
          (by show ¬(((n + 1) + 1 - (m + 1)) + (s : Nat) < (n + 1) + 1 - (m + 1)); omega)
          (by show ((n + 1) + 1 - (m + 1)) + (s : Nat) - ((n + 1) + 1 - (m + 1)) < k; omega)]
      exact congrArg (Fin.natAdd (n + 3)) (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k (m + 1) hkm
      (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI))
      (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (peelU (I := I) k (m + 1) hkm i)
        (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) hposP
    refine Eq.trans (congrArg (cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_natAdd I O s.castSucc)) hcP)
    rw [suffixRead₂_compl (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
        (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
          (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO))
        ⟨(n + 1 - m) + (s : Nat), by omega⟩,
      complPack_ge' (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO) ⟨(s : Nat), hltT⟩,
      bndV0_lt k m hkm hkb hkm0 o wO ⟨(s : Nat), hltT⟩ hltT',
      suffixRead₂_compl (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (Fin.snoc zcO wO, Fin.snoc zcI wI))
        (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (peelU (I := I) k (m + 1) hkm i)
          (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀))
        ⟨((n + 1) + 1 - (m + 1)) + (s : Nat), by omega⟩,
      complPack_ge' (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (peelU (I := I) k (m + 1) hkm i) (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)
        ⟨(s : Nat), hltP⟩]
    have hvalP : snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀ ⟨(s : Nat), hltP⟩
        = o ⟨(s : Nat), hltP'⟩ :=
      Fin.snoc_castSucc
        (α := fun j : Fin ((n + 1) - (m + 1) + 1) => O (compOutS (n := n + 1) k (m + 1) hkm j))
        z₀ o ⟨(s : Nat), hltP'⟩
    rw [hvalP]
    exact (cast4 (congrArg O (compOutS_bnd_tail_eq k m hkm hkb hkm0 ⟨(s : Nat), hltT'⟩))
        (complFam₂_eq_ge' (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0 ⟨(s : Nat), hltT⟩).symm
        (congrArg (append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)) hposT)
        (append_natAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)
        (o (Fin.cast (by omega) ⟨(s : Nat), hltT'⟩))).trans
      (cast3 (complFam₂_eq_ge' (I := I) (O := O) (n := n + 1) k (m + 1) hkm ⟨(s : Nat), hltP⟩).symm
        (congrArg (append I O) hposP) (append_natAdd I O s.castSucc)
        (o ⟨(s : Nat), hltP'⟩)).symm
  rcases Nat.lt_or_ge (s : Nat) (k + (m + 1)) with hB | hB'
  · -- inside the window: connected output wire at both depths
    have ht : (s : Nat) - k < m + 1 := by omega
    have htP : (s : Nat) - k < m + 2 := by omega
    have hposT : suffixConnIdx (n := n) k m hkm0 (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = Fin.natAdd (n + 2) s := by
      rw [suffixConnIdx_castAdd]
      exact congrArg (Fin.natAdd (n + 2)) (Fin.ext (by simp only; omega))
    have hcT := read₂_congr_pos (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
      (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
      (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) hposT
    have hposP : suffixConnIdx (n := n + 1) k (m + 1) hkm (Fin.castAdd (m + 2) ⟨(s : Nat) - k, htP⟩)
        = Fin.natAdd (n + 3) s.castSucc := by
      rw [suffixConnIdx_castAdd]
      exact congrArg (Fin.natAdd (n + 3))
        (Fin.ext (by simp only [Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k (m + 1) hkm
      (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI))
      (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (peelU (I := I) k (m + 1) hkm i)
        (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) hposP
    refine Eq.trans (congrArg (cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_natAdd I O s.castSucc)) hcP)
    have hEq0 : (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).connFam₁
        (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) (suffixConnIdx (n := n) k m hkm0
            (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)) := by
      show append (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0) (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0)
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩) = _
      rw [append_castAdd, suffixConnIdx_castAdd, append_natAdd]
      rfl
    have hEq1 : (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁
        (Fin.castAdd (m + 2) ⟨(s : Nat) - k, htP⟩)
        = append I O (suffixConnIdx (n := n + 1) k (m + 1) hkm
            (Fin.castAdd (m + 2) ⟨(s : Nat) - k, htP⟩)) := by
      show append (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          (Fin.castAdd (m + 2) ⟨(s : Nat) - k, htP⟩) = _
      rw [append_castAdd, suffixConnIdx_castAdd, append_natAdd]
      rfl
    rw [suffixRead₂_conn_castAdd (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
        (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
          (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) ⟨(s : Nat) - k, ht⟩,
      suffixRead₂_conn_castAdd (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (Fin.snoc zcO wO, Fin.snoc zcI wI))
        (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (peelU (I := I) k (m + 1) hkm i)
          (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) ⟨(s : Nat) - k, htP⟩,
      show (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).eRelabel
          (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
          (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)
        = cast hEq0 (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI)
            (Fin.castAdd (m + 1) ⟨(s : Nat) - k, ht⟩)) from rfl,
      zcBnd0_castAdd k m hkm0 zcO zcI ⟨(s : Nat) - k, ht⟩,
      show (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).eRelabel
          (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
            (Fin.snoc zcO wO, Fin.snoc zcI wI))
          (Fin.castAdd (m + 2) ⟨(s : Nat) - k, htP⟩)
        = cast hEq1 (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
            (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.castAdd (m + 2) ⟨(s : Nat) - k, htP⟩))
          from rfl,
      zcBnd_castAdd k m hkm zcO wO zcI wI ⟨(s : Nat) - k, htP⟩ (by omega)]
    exact (cast4 (append_castAdd (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0) (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0)
          ⟨(s : Nat) - k, ht⟩).symm hEq0
        (congrArg (append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)) hposT) (append_natAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)
        (zcO ⟨(s : Nat) - k, ht⟩)).trans
      (cast4 (append_castAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          ⟨(s : Nat) - k, htP⟩).symm hEq1
        (congrArg (append I O) hposP) (append_natAdd I O s.castSucc)
        (zcO ⟨(s : Nat) - k, by omega⟩)).symm
  · -- the boundary position: connected at depth one, private final at depth zero
    have hts : (s : Nat) = n + 1 := by omega
    have hposT : complEmb (suffixConnIdx (n := n) k m hkm0)
        (suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0).hι₂ ⟨(n + 1 - m) + (n - m), by omega⟩
        = Fin.natAdd (n + 2) s := by
      rw [complEmb_lastOut (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0]
      exact congrArg (Fin.natAdd (n + 2)) (Fin.ext (by simp only [Fin.val_last]; omega))
    have hcT := read₂_congr_pos (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
      (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
      (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)) hposT
    have hposP : suffixConnIdx (n := n + 1) k (m + 1) hkm (Fin.castAdd (m + 2) (Fin.last (m + 1)))
        = Fin.natAdd (n + 3) s.castSucc := by
      rw [suffixConnIdx_castAdd]
      exact congrArg (Fin.natAdd (n + 3))
        (Fin.ext (by simp only [Fin.val_last, Fin.val_castSucc]; omega))
    have hcP := read₂_congr_pos (I := I) (O := O) (n := n + 1) k (m + 1) hkm
      (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI))
      (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (peelU (I := I) k (m + 1) hkm i)
        (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) hposP
    refine Eq.trans (congrArg (cast (append_natAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s)) hcT.symm) ?_
    refine Eq.trans ?_ (congrArg (cast (append_natAdd I O s.castSucc)) hcP)
    have hEq1 : (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁
        (Fin.castAdd (m + 2) (Fin.last (m + 1)))
        = append I O (suffixConnIdx (n := n + 1) k (m + 1) hkm
            (Fin.castAdd (m + 2) (Fin.last (m + 1)))) := by
      show append (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          (Fin.castAdd (m + 2) (Fin.last (m + 1))) = _
      rw [append_castAdd, suffixConnIdx_castAdd, append_natAdd]
      rfl
    rw [suffixRead₂_compl (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
        (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
          (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO))
        ⟨(n + 1 - m) + (n - m), by omega⟩,
      complPack_ge' (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0
        (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO) ⟨n - m, by omega⟩,
      bndV0_last k m hkm hkb hkm0 o wO,
      suffixRead₂_conn_castAdd (I := I) (O := O) (n := n + 1) k (m + 1) hkm
        (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (Fin.snoc zcO wO, Fin.snoc zcI wI))
        (complPack (I := I) (O := O) (n := n + 1) k (m + 1) hkm
          (peelU (I := I) k (m + 1) hkm i)
          (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)) (Fin.last (m + 1)),
      show (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).eRelabel
          (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
            (Fin.snoc zcO wO, Fin.snoc zcI wI))
          (Fin.castAdd (m + 2) (Fin.last (m + 1)))
        = cast hEq1 (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
            (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.castAdd (m + 2) (Fin.last (m + 1))))
          from rfl,
      zcBnd_castAdd_last k m hkm zcO wO zcI wI]
    exact (cast4 (congrArg O (bnd_pending_eq k m hkm hkb hkm0))
        (complFam₂_eq_ge' (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) k m hkm0 ⟨n - m, by omega⟩).symm
        (congrArg (append (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)) hposT)
        (append_natAdd (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) s) wO).trans
      (cast4 (append_castAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
          (Fin.last (m + 1))).symm hEq1
        (congrArg (append I O) hposP) (append_natAdd I O s.castSucc) wO).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary row fold: the `castSucc` compression of the boundary-depth
flattened configuration at a snoc-decomposed connected configuration equals
the reduced-depth flattened configuration at the truncated connected
configuration, with the private packings transported across the boundary. -/
private theorem rowFlat_bnd_fold (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
    (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1)))
    (i : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1))))) :
    ((fun j : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
            (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
              (Fin.snoc zcO wO, Fin.snoc zcI wI))
            (peelU (I := I) k (m + 1) hkm i)
            (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
      fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
            (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
              (Fin.snoc zcO wO, Fin.snoc zcI wI))
            (peelU (I := I) k (m + 1) hkm i)
            (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
      = splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)
          ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).read₂
            (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
            (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
              (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO))) := by
  apply Prod.ext
  · funext s
    exact (read₂_bnd_castAdd k m hkm hkb hkm0 zcO wO zcI wI i o z₀ s).symm
  · funext s
    exact (read₂_bnd_natAdd k m hkm hkb hkm0 zcO wO zcI wI i o z₀ s).symm

/-! ### The boundary peel equation

Summing the boundary-window composite over the last output value peels the
outer comb, and the surviving configurations reassemble into the
reduced-depth boundary composite of the tail witness `K` against the inner
comb's tail witness `XW`.  The reduction is stated left side to left side:
no conditional appears at this level, because the reduced-depth composite's
own normalization peel (supplied by the depth induction) reintroduces the
condition on the transported last input wire. -/

/-- Boundary sum rearrangement: pulling the last-output sum inside the window
contraction and applying the outer peel per connected configuration. -/
private theorem bnd_eq_swap (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)))
    (i i' : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o o' : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1))))) :
    (∑ z : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1)))),
        ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz) *
          J (rowFlat (I := I) (O := O) k (m + 1) hkm zz' (peelU (I := I) k (m + 1) hkm i)
              (snocP (O := O) (n := n + 1) k (m + 1) hkm o z))
            (rowFlat (I := I) (O := O) k (m + 1) hkm zz (peelU (I := I) k (m + 1) hkm i')
              (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z)))
      = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz) *
          (if zz' (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1)))
              = zz (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1))) then
            K ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm zz' (peelU (I := I) k (m + 1) hkm i)
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm zz'
                (peelU (I := I) k (m + 1) hkm i)
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm zz (peelU (I := I) k (m + 1) hkm i')
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm zz
                (peelU (I := I) k (m + 1) hkm i')
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).2 t.castSucc)
          else 0) := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun zz _ =>
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun zz' _ => ?_)))
  refine (Finset.mul_sum _ _ _).symm.trans ?_
  exact congrArg _ (bnd_inner k (m + 1) hkm hkb J K hpeel zz zz' i i' o o' z₀)

/-- Two-level sum reindex along an equivalence: both the row and the column
configurations move to the flattened side simultaneously. -/
private theorem sum_reindex_two {α β : Type u} [Fintype α] [Fintype β] (e : β ≃ α)
    (F : α → α → ℂ) :
    (∑ zz : α, ∑ zz' : α, F zz' zz) = ∑ q : β, ∑ p : β, F (e p) (e q) := by
  refine Eq.trans (Finset.sum_congr rfl fun zz _ =>
    (Equiv.sum_comp e (fun zz' => F zz' zz)).symm) ?_
  exact (Equiv.sum_comp e (fun zz => ∑ p : β, F (e p) zz)).symm

/-- Boundary split form: reindexing the connected window configurations of
the swapped boundary equation by the flattening equivalence and splitting each
window block at its last wire exhibits the shared-trace structure — the outer
peel's condition becomes equality of the row and column pending input values. -/
private theorem bnd_eq_split (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)))
    (i i' : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o o' : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1))))) :
    (∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz) *
          (if zz' (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1)))
              = zz (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1))) then
            K ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm zz' (peelU (I := I) k (m + 1) hkm i)
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm zz'
                (peelU (I := I) k (m + 1) hkm i)
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm zz (peelU (I := I) k (m + 1) hkm i')
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm zz
                (peelU (I := I) k (m + 1) hkm i')
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).2 t.castSucc)
          else 0))
      = ∑ zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)),
        ∑ zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ wO' : suffixOut O k (m + 1) hkm (Fin.last (m + 1)),
        ∑ zcI' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
        ∑ wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
        ∑ wI' : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
          X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k (m + 1) hkm i)
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k (m + 1) hkm i)
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k (m + 1) hkm i')
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k (m + 1) hkm i')
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).2 t.castSucc)
          else 0) := by
  refine Eq.trans (sum_reindex_two (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm)
    (fun (zz' zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k (m + 1) hkm).connFam₁ q) =>
      X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz')
          ((XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm).symm zz) *
        (if zz' (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1)))
            = zz (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1))) then
          K ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm zz' (peelU (I := I) k (m + 1) hkm i)
                  (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm zz'
              (peelU (I := I) k (m + 1) hkm i)
              (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
          ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm zz (peelU (I := I) k (m + 1) hkm i')
                  (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm zz
              (peelU (I := I) k (m + 1) hkm i')
              (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).2 t.castSucc)
        else 0))) ?_
  simp only [Equiv.symm_apply_apply]
  rw [sum_space_snoc2]
  have hpt : ∀ (zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
      (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
      (zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
      (wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1)))
      (zcO' : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc)
      (wO' : suffixOut O k (m + 1) hkm (Fin.last (m + 1)))
      (zcI' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
      (wI' : suffixIn I k (m + 1) hkm (Fin.last (m + 1))),
      X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                (Fin.snoc zcO' wO', Fin.snoc zcI' wI')) (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1)))
              = (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI)) (Fin.natAdd (m + 1 + 1) (Fin.last (m + 1))) then
            K ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k (m + 1) hkm i)
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k (m + 1) hkm i)
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k (m + 1) hkm i')
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k (m + 1) hkm i')
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).2 t.castSucc)
          else 0)
        = X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k (m + 1) hkm i)
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k (m + 1) hkm i)
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k (m + 1) hkm i')
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k (m + 1) hkm i')
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).2 t.castSucc)
          else 0) := by
    intro zcO wO zcI wI zcO' wO' zcI' wI'
    have h1 := zcBnd_natAdd_last k m hkm zcO' wO' zcI' wI'
    have h2 := zcBnd_natAdd_last k m hkm zcO wO zcI wI
    by_cases hcc : wI' = wI
    · subst hcc
      rw [ite_eq_left (by rw [h1, h2]), ite_eq_left rfl]
    · rw [ite_eq_right (fun heq => hcc ((Equiv.cast
          (append_natAdd (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)
            (Fin.last (m + 1))).symm).injective (h1.symm.trans (heq.trans h2)))),
        ite_eq_right hcc]
  exact Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun wO _ =>
    Finset.sum_congr rfl fun zcI _ => Finset.sum_congr rfl fun zcO' _ =>
      Finset.sum_congr rfl fun wO' _ => Finset.sum_congr rfl fun zcI' _ =>
        Finset.sum_congr rfl fun wI _ => Finset.sum_congr rfl fun wI' _ =>
          hpt zcO wO zcI wI zcO' wO' zcI' wI'

omit [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] in
/-- A normalization peel equation absorbs a constant right factor: summing
the peeled entries against a fixed coefficient equals the peeled witness
against the same coefficient, off the diagonal the zeros absorb the factor. -/
private theorem sum_peel_mul (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (X : CMatrix (Space (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)))
    (XW : CMatrix (Space (fun j : Fin (m + 1) => suffixOut O k (m + 1) hkm j.castSucc)
      (fun j : Fin (m + 1) => suffixIn I k (m + 1) hkm j.castSucc)))
    (hpeelX : ∀ (ii ii' : ∀ j, suffixOut O k (m + 1) hkm j)
      (oo oo' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc),
      (∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
          X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (m + 1)) = ii' (Fin.last (m + 1)) then
          XW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (ii ii' : ∀ j, suffixOut O k (m + 1) hkm j)
    (oo oo' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc)
    (c : ℂ) :
    (∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
        X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z) * c) =
      if ii (Fin.last (m + 1)) = ii' (Fin.last (m + 1)) then
        XW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') * c else 0 := by
  have hfac : (∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
        X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) * c =
      ∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
        X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z) * c := Finset.sum_mul Finset.univ _ _
  rw [← hfac, hpeelX ii ii' oo oo', ite_mul, zero_mul]

/-- Boundary collapse: folding the boundary-depth row configurations to the
reduced depth, contracting the inner comb's pending input through its own
normalization peel, and collapsing the two Kronecker deltas leaves the
reduced-depth composite of the outer tail witness against the inner tail
witness, with the surviving pending output value shared by the row and
column arguments. -/
private theorem bnd_eq_collapse (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)))
    (XW : CMatrix (Space (fun j : Fin (m + 1) => suffixOut O k (m + 1) hkm j.castSucc)
      (fun j : Fin (m + 1) => suffixIn I k (m + 1) hkm j.castSucc)))
    (hpeelX : ∀ (ii ii' : ∀ j, suffixOut O k (m + 1) hkm j)
      (oo oo' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc),
      (∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
          X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (m + 1)) = ii' (Fin.last (m + 1)) then
          XW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (i i' : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o o' : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1))))) :
    (∑ zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)),
        ∑ zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ wO' : suffixOut O k (m + 1) hkm (Fin.last (m + 1)),
        ∑ zcI' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
        ∑ wI : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
        ∑ wI' : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
          X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k (m + 1) hkm i)
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k (m + 1) hkm i)
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k (m + 1) hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k (m + 1) hkm i')
                    (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k (m + 1) hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k (m + 1) hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k (m + 1) hkm i')
                (snocP (O := O) (n := n + 1) k (m + 1) hkm o' z₀)).2 t.castSucc)
          else 0))
      = ∑ zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)),
        ∑ zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ zcI' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
          XW ((fun j : Fin (m + 1) => (Fin.snoc zcO' wO) j.castSucc), zcI')
              ((fun j : Fin (m + 1) => (Fin.snoc zcO wO) j.castSucc), zcI) *
          K (splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc)
              (fun t : Fin (n + 2) => O t.castSucc)
              ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc))
                  (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).read₂
                (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc))
                  (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO', zcI'))
                (complPack (I := (fun t : Fin (n + 2) => I t.castSucc))
                  (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
                  (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO))))
            (splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc)
              (fun t : Fin (n + 2) => O t.castSucc)
              ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc))
                  (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).read₂
                (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc))
                  (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (zcO, zcI))
                (complPack (I := (fun t : Fin (n + 2) => I t.castSucc))
                  (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0
                  (bndU0 k m hkm hkb hkm0 i') (bndV0 k m hkm hkb hkm0 o' wO)))) := by
  simp only [rowFlat_bnd_fold k m hkm hkb hkm0]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [sum_peel_mul k m hkm X XW hpeelX, Fin.snoc_last]
  refine Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun wO _ =>
    Finset.sum_congr rfl fun zcI _ => Finset.sum_congr rfl fun zcO' _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- Boundary D-side entry expansion: the reduced-depth successor-form composite
of the outer tail witness against the inner tail witness, at the
boundary-transported snoc point, equals its window contraction read in the
split block coordinates — the column configuration against the transported row
point and vice versa, with the pending output value shared by both. -/
private theorem bnd_eq_entry (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (XW : CMatrix (Space (fun j : Fin (m + 1) => suffixOut O k (m + 1) hkm j.castSucc)
      (fun j : Fin (m + 1) => suffixIn I k (m + 1) hkm j.castSucc)))
    (i i' : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o o' : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc))
    (wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1))) :
    suffixCompS (I := (fun t : Fin (n + 2) => I t.castSucc))
        (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 K XW
        (bndI0 k m hkm hkb hkm0 i,
          Fin.snoc (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO))
        (bndI0 k m hkm hkb hkm0 i',
          Fin.snoc (bndO0 k m hkm hkb hkm0 o') (bndW0 k m hkm hkb hkm0 wO))
      = ∑ zcO : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ zcI : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin (m + 1), suffixOut O k (m + 1) hkm j.castSucc,
        ∑ zcI' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc,
          XW (zcO', zcI') (zcO, zcI) * K (splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).read₂ ((XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0) (zcO', zcI')) (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (bndU0 k m hkm hkb hkm0 i) (bndV0 k m hkm hkb hkm0 o wO)))) (splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).read₂ ((XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0) (zcO, zcI)) (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (bndU0 k m hkm hkb hkm0 i') (bndV0 k m hkm hkb hkm0 o' wO)))) := by
  have hE := suffixCompS_entry_snoc (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0 K XW
      (bndI0 k m hkm hkb hkm0 i) (bndI0 k m hkm hkb hkm0 i')
      (bndO0 k m hkm hkb hkm0 o) (bndO0 k m hkm hkb hkm0 o')
      (bndW0 k m hkm hkb hkm0 wO)
  rw [hE]
  refine Eq.trans (sum_reindex_two (XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0)
      (fun (zz' zz : ∀ i : Fin (m + 1 + (m + 1)),
          append (suffixOut (fun t : Fin (n + 2) => O t.castSucc) k m hkm0) (suffixIn (fun t : Fin (n + 2) => I t.castSucc) k m hkm0) i) =>
        XW ((XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).symm zz') ((XFlatEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).symm zz) * K (splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).read₂ zz' (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (spaceIdxEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (bndI0 k m hkm hkb hkm0 i, Fin.snoc (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO))).1 (spaceIdxEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (bndI0 k m hkm hkb hkm0 i, Fin.snoc (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO))).2))) (splitAppendEquiv (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc) ((suffixMatch (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0).read₂ zz (complPack (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (spaceIdxEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (bndI0 k m hkm hkb hkm0 i', Fin.snoc (bndO0 k m hkm hkb hkm0 o') (bndW0 k m hkm hkb hkm0 wO))).1 (spaceIdxEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0 (bndI0 k m hkm hkb hkm0 i', Fin.snoc (bndO0 k m hkm hkb hkm0 o') (bndW0 k m hkm hkb hkm0 wO))).2))))) ?_
  simp only [Equiv.symm_apply_apply]
  have hS : (spaceIdxEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0) (bndI0 k m hkm hkb hkm0 i,
        Fin.snoc (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO))
      = (bndU0 k m hkm hkb hkm0 i, bndV0 k m hkm hkb hkm0 o wO) := by
    rw [spaceIdxEquiv_apply (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0
      (bndI0 k m hkm hkb hkm0 i,
        Fin.snoc (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO))]
    rfl
  have hS' : (spaceIdxEquiv (I := (fun t : Fin (n + 2) => I t.castSucc)) (O := (fun t : Fin (n + 2) => O t.castSucc)) (n := n) k m hkm0) (bndI0 k m hkm hkb hkm0 i',
        Fin.snoc (bndO0 k m hkm hkb hkm0 o') (bndW0 k m hkm hkb hkm0 wO))
      = (bndU0 k m hkm hkb hkm0 i', bndV0 k m hkm hkb hkm0 o' wO) := by
    rw [spaceIdxEquiv_apply (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0
      (bndI0 k m hkm hkb hkm0 i',
        Fin.snoc (bndO0 k m hkm hkb hkm0 o') (bndW0 k m hkm hkb hkm0 wO))]
    rfl
  rw [congrArg Prod.fst hS, congrArg Prod.snd hS, congrArg Prod.fst hS', congrArg Prod.snd hS']
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun zcI _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun zcO' _ => Finset.sum_congr rfl fun zcI' _ => ?_
  rfl

/-- Boundary assembly: summing the successor-form composite over the pending
output of the outer comb's last tooth and peeling the outer comb's own
normalization through the chain of expansion, swap, split, and collapse,
leaves exactly the reduced-depth composite of the outer witness against the
inner witness, summed over the transported pending output value. -/
private theorem bnd_eq (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2) (hkb : k + (m + 1) + 1 = n + 2)
    (hkm0 : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)))
    (XW : CMatrix (Space (fun j : Fin (m + 1) => suffixOut O k (m + 1) hkm j.castSucc)
      (fun j : Fin (m + 1) => suffixIn I k (m + 1) hkm j.castSucc)))
    (hpeelX : ∀ (ii ii' : ∀ j, suffixOut O k (m + 1) hkm j)
      (oo oo' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc),
      (∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
          X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (m + 1)) = ii' (Fin.last (m + 1)) then
          XW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (i i' : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o o' : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc)) :
    (∑ z : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1)))),
        suffixCompS (I := I) (O := O) (n := n + 1) k (m + 1) hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = ∑ wO : suffixOut O k (m + 1) hkm (Fin.last (m + 1)),
        suffixCompS (I := fun t : Fin (n + 2) => I t.castSucc)
          (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0 K XW
          (bndI0 k m hkm hkb hkm0 i,
            Fin.snoc (bndO0 k m hkm hkb hkm0 o) (bndW0 k m hkm hkb hkm0 wO))
          (bndI0 k m hkm hkb hkm0 i',
            Fin.snoc (bndO0 k m hkm hkb hkm0 o') (bndW0 k m hkm hkb hkm0 wO)) := by
  classical
  rcases isEmpty_or_nonempty
      (O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1))))) with hE | hNE
  · have hEO : IsEmpty (O (Fin.last (n + 2))) :=
      congrArg O (compOutS_last (n := n + 1) k (m + 1) hkm) ▸ hE
    have hWI : suffixIn I k (m + 1) hkm (Fin.last (m + 1)) = I (Fin.last (n + 2)) :=
      congrArg I (Fin.ext (by simp only [suffixInIdx, Fin.val_last]; omega))
    refine (Finset.sum_eq_zero (fun z _ => hE.elim z)).trans ?_
    symm
    refine Finset.sum_eq_zero fun wO _ => ?_
    rw [bnd_eq_entry k m hkm hkb hkm0 K XW i i' o o' wO]
    refine Finset.sum_eq_zero fun zcO _ => Finset.sum_eq_zero fun zcI _ =>
      Finset.sum_eq_zero fun zcO' _ => Finset.sum_eq_zero fun zcI' _ => ?_
    rcases isEmpty_or_nonempty (I (Fin.last (n + 2))) with hEI | hNI
    · rw [peel_zero_of_empty_output X XW hpeelX (hWI.symm ▸ hEI) wO _ _, zero_mul]
    · obtain ⟨a⟩ := hNI
      rw [peel_zero_of_empty_output J K hpeel hEO a _ _, mul_zero]
  · obtain ⟨z₀⟩ := hNE
    refine Eq.trans (Finset.sum_congr rfl fun z _ =>
      trunc_eq_expand k (m + 1) hkm J X i i' o o' z) ?_
    refine Eq.trans (bnd_eq_swap k m hkm hkb J K hpeel X i i' o o' z₀) ?_
    refine Eq.trans (bnd_eq_split k m hkm K X i i' o o' z₀) ?_
    refine Eq.trans (bnd_eq_collapse k m hkm hkb hkm0 K X XW hpeelX i i' o o' z₀) ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun wO _ => ?_
    rw [bnd_eq_entry k m hkm hkb hkm0 K XW i i' o o' wO]
    refine Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun zcI _ =>
      Finset.sum_congr rfl fun zcO' _ => Finset.sum_congr rfl fun zcI' _ => ?_
    simp only [Fin.snoc_castSucc]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary witness family equation, input wires: the truncated composite's
witness input family at a rewrapped index reads the same type as the
untruncated composite's witness input family. -/
private theorem famBndEqI (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 1) - (m + 1))) :
    I (Fin.castSucc (compInS (n := n) k m hkm0 (⟨(j : Nat), by omega⟩ : Fin (n - m)).castSucc))
      = I (compInS (n := n + 1) k (m + 1) hkm j.castSucc) :=
  (congrArg I (compInS_bnd_tail_eq k m hkm hkb hkm0
    (⟨(j : Nat), by omega⟩ : Fin (n - m)).castSucc)).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary witness family equation, output wires. -/
private theorem famBndEqO (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (j : Fin ((n + 1) - (m + 1))) :
    O (Fin.castSucc (compOutS (n := n) k m hkm0 (⟨(j : Nat), by omega⟩ : Fin (n - m)).castSucc))
      = O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc) :=
  (congrArg O (compOutS_bnd_tail_eq k m hkm hkb hkm0 ⟨(j : Nat), by omega⟩)).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary witness family equation, input wires, inverse direction. -/
private theorem famBndEqI' (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1) (i : Fin (n - m)) :
    I (compInS (n := n + 1) k (m + 1) hkm (⟨(i : Nat), by omega⟩ : Fin ((n + 1) - (m + 1))).castSucc)
      = I (Fin.castSucc (compInS (n := n) k m hkm0 i.castSucc)) :=
  congrArg I (compInS_bnd_tail_eq k m hkm hkb hkm0 i.castSucc)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary witness family equation, output wires, inverse direction. -/
private theorem famBndEqO' (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1) (i : Fin (n - m)) :
    O (compOutS (n := n + 1) k (m + 1) hkm (⟨(i : Nat), by omega⟩ : Fin ((n + 1) - (m + 1))).castSucc)
      = O (Fin.castSucc (compOutS (n := n) k m hkm0 i.castSucc)) :=
  congrArg O (compOutS_bnd_tail_eq k m hkm hkb hkm0 i)

/-- The boundary witness family reindex: the truncated composite's witness wire
families read the same types as the untruncated composite's witness families. -/
private def famBndEquiv (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1) :
    Space (fun j : Fin (n - m) => I (Fin.castSucc (compInS (n := n) k m hkm0 j.castSucc)))
      (fun j : Fin (n - m) => O (Fin.castSucc (compOutS (n := n) k m hkm0 j.castSucc))) ≃
    Space (fun j : Fin ((n + 1) - (m + 1)) =>
        I (compInS (n := n + 1) k (m + 1) hkm j.castSucc))
      (fun j : Fin ((n + 1) - (m + 1)) =>
        O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc)) where
  toFun p :=
    ((fun j => cast (famBndEqI (I := I) k m hkm hkb hkm0 j) (p.1 ⟨(j : Nat), by omega⟩)),
      (fun j => cast (famBndEqO (O := O) k m hkm hkb hkm0 j) (p.2 ⟨(j : Nat), by omega⟩)))
  invFun q :=
    ((fun i => cast (famBndEqI' (I := I) k m hkm hkb hkm0 i) (q.1 ⟨(i : Nat), by omega⟩)),
      (fun i => cast (famBndEqO' (O := O) k m hkm hkb hkm0 i) (q.2 ⟨(i : Nat), by omega⟩)))
  left_inv p := by
    apply Prod.ext
    · funext i
      exact cast_cast_cancel (famBndEqI' (I := I) k m hkm hkb hkm0 i) (p.1 i)
    · funext i
      exact cast_cast_cancel (famBndEqO' (O := O) k m hkm hkb hkm0 i) (p.2 i)
  right_inv q := by
    apply Prod.ext
    · funext j
      exact cast_cast_cancel (famBndEqI (I := I) k m hkm hkb hkm0 j) (q.1 j)
    · funext j
      exact cast_cast_cancel (famBndEqO (O := O) k m hkm hkb hkm0 j) (q.2 j)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The boundary family reindex carries the restricted composite point to the
boundary-transported truncated point. -/
private theorem bndConfig_eq (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (i : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc)) :
    (famBndEquiv (I := I) (O := O) k m hkm hkb hkm0).symm
        ((fun j : Fin ((n + 1) - (m + 1)) => i j.castSucc), o)
      = ((fun j : Fin (n - m) => bndI0 k m hkm hkb hkm0 i j.castSucc),
        bndO0 k m hkm hkb hkm0 o) := by
  rfl

/-- Cast-based family reindex between omega-equal index spellings: given
pointwise wire equations at rewrapped indices, the two `Space`s are
equivalent. -/
private def castIdxEquiv {N M : Nat} (hNM : N = M) {F G : Fin N → Type u} {F' G' : Fin M → Type u}
    (eF : ∀ j : Fin N, F j = F' ⟨(j : Nat), by omega⟩)
    (eG : ∀ j : Fin N, G j = G' ⟨(j : Nat), by omega⟩) :
    Space F G ≃ Space F' G' where
  toFun p :=
    ((fun j' => cast (eF ⟨(j' : Nat), by omega⟩) (p.1 ⟨(j' : Nat), by omega⟩)),
      (fun j' => cast (eG ⟨(j' : Nat), by omega⟩) (p.2 ⟨(j' : Nat), by omega⟩)))
  invFun q :=
    ((fun i => cast (eF i).symm (q.1 ⟨(i : Nat), by omega⟩)),
      (fun i => cast (eG i).symm (q.2 ⟨(i : Nat), by omega⟩)))
  left_inv p := by
    apply Prod.ext
    · funext i
      exact cast_cast_cancel' (eF i) (p.1 i)
    · funext i
      exact cast_cast_cancel' (eG i) (p.2 i)
  right_inv q := by
    apply Prod.ext
    · funext j
      exact cast_cast_cancel (eF ⟨(j : Nat), by omega⟩) (q.1 j)
    · funext j
      exact cast_cast_cancel (eG ⟨(j : Nat), by omega⟩) (q.2 j)

/-- Normalization transports across omega-equal index spellings: a normalized
operator on `F G` reindexes to a normalized operator on `F' G'`. -/
private theorem normalized_castIdx (N : Nat) :
    ∀ (M : Nat) (hNM : N = M) {F G : Fin N → Type u} {F' G' : Fin M → Type u}
      [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
      [∀ j, Fintype (G j)] [∀ j, DecidableEq (G j)]
      [∀ j, Fintype (F' j)] [∀ j, DecidableEq (F' j)]
      [∀ j, Fintype (G' j)] [∀ j, DecidableEq (G' j)]
      (eF : ∀ j : Fin N, F j = F' ⟨(j : Nat), by omega⟩)
      (eG : ∀ j : Fin N, G j = G' ⟨(j : Nat), by omega⟩)
      (W : CMatrix (Space F G)), Normalized F G W →
      Normalized F' G' (matReindex (castIdxEquiv hNM eF eG) W) := by
  induction N with
  | zero =>
    intro M hNM F G F' G' _ _ _ _ _ _ _ _ eF eG W h
    subst hNM
    rw [normalized_zero] at h ⊢
    rw [h, matReindex_one]
  | succ n ih =>
    intro M hNM F G F' G' iF iFd iG iGd iF' iF'd iG' iG'd eF eG W h
    subst hNM
    let : ∀ j : Fin n, Fintype (F j.castSucc) := fun j => iF j.castSucc
    let : ∀ j : Fin n, DecidableEq (F j.castSucc) := fun j => iFd j.castSucc
    let : ∀ j : Fin n, Fintype (G j.castSucc) := fun j => iG j.castSucc
    let : ∀ j : Fin n, DecidableEq (G j.castSucc) := fun j => iGd j.castSucc
    let : ∀ j : Fin n, Fintype (F' j.castSucc) := fun j => iF' j.castSucc
    let : ∀ j : Fin n, DecidableEq (F' j.castSucc) := fun j => iF'd j.castSucc
    let : ∀ j : Fin n, Fintype (G' j.castSucc) := fun j => iG' j.castSucc
    let : ∀ j : Fin n, DecidableEq (G' j.castSucc) := fun j => iG'd j.castSucc
    rcases h with ⟨hpos, K, hK, hpeel⟩
    have eF₀ : ∀ j : Fin n,
        (fun t : Fin n => F t.castSucc) j =
          (fun t : Fin n => F' t.castSucc) ⟨(j : Nat), by omega⟩ :=
      fun j => eF j.castSucc
    have eG₀ : ∀ j : Fin n,
        (fun t : Fin n => G t.castSucc) j =
          (fun t : Fin n => G' t.castSucc) ⟨(j : Nat), by omega⟩ :=
      fun j => eG j.castSucc
    refine ⟨matReindex_posSemidef _ hpos,
      matReindex (castIdxEquiv (rfl : n = n) eF₀ eG₀) K,
      ih n (rfl : n = n) eF₀ eG₀ K hK, ?_⟩
    intro i₁ i₂ o₁ o₂
    have key : ∀ z : G (Fin.last n),
        matReindex (castIdxEquiv (rfl : n + 1 = n + 1) eF eG) W
            (i₁, Fin.snoc o₁ (cast (eG (Fin.last n)) z))
            (i₂, Fin.snoc o₂ (cast (eG (Fin.last n)) z)) =
        W ((fun j => cast (eF j).symm (i₁ j)),
            Fin.snoc (fun j : Fin n => cast (eG j.castSucc).symm (o₁ j)) z)
          ((fun j => cast (eF j).symm (i₂ j)),
            Fin.snoc (fun j : Fin n => cast (eG j.castSucc).symm (o₂ j)) z) := by
      intro z
      rw [matReindex_apply]
      refine congrArg₂ W ?_ ?_
      · apply Prod.ext
        · rfl
        · funext i
          rcases i.eq_castSucc_or_eq_last with ⟨j₀, rfl⟩ | rfl
          · show cast (eG j₀.castSucc).symm
                ((Fin.snoc o₁ (cast (eG (Fin.last n)) z)) j₀.castSucc) =
              (Fin.snoc (fun j : Fin n => cast (eG j.castSucc).symm (o₁ j)) z) j₀.castSucc
            simp only [Fin.snoc_castSucc]
          · show cast (eG (Fin.last n)).symm
                ((Fin.snoc o₁ (cast (eG (Fin.last n)) z)) (Fin.last n)) =
              (Fin.snoc (fun j : Fin n => cast (eG j.castSucc).symm (o₁ j)) z) (Fin.last n)
            simp only [Fin.snoc_last]
            exact cast_cast_cancel' (eG (Fin.last n)) z
      · apply Prod.ext
        · rfl
        · funext i
          rcases i.eq_castSucc_or_eq_last with ⟨j₀, rfl⟩ | rfl
          · show cast (eG j₀.castSucc).symm
                ((Fin.snoc o₂ (cast (eG (Fin.last n)) z)) j₀.castSucc) =
              (Fin.snoc (fun j : Fin n => cast (eG j.castSucc).symm (o₂ j)) z) j₀.castSucc
            simp only [Fin.snoc_castSucc]
          · show cast (eG (Fin.last n)).symm
                ((Fin.snoc o₂ (cast (eG (Fin.last n)) z)) (Fin.last n)) =
              (Fin.snoc (fun j : Fin n => cast (eG j.castSucc).symm (o₂ j)) z) (Fin.last n)
            simp only [Fin.snoc_last]
            exact cast_cast_cancel' (eG (Fin.last n)) z
    have hcond : (fun j => cast (eF j).symm (i₁ j)) (Fin.last n) =
          (fun j => cast (eF j).symm (i₂ j)) (Fin.last n) ↔
        i₁ (Fin.last n) = i₂ (Fin.last n) := by
      constructor
      · intro h
        have hg := congrArg (cast (eF (Fin.last n))) h
        rwa [cast_cast_cancel, cast_cast_cancel] at hg
      · intro h
        show cast (eF (Fin.last n)).symm (i₁ (Fin.last n)) =
          cast (eF (Fin.last n)).symm (i₂ (Fin.last n))
        rw [h]
    refine Eq.trans ((Equiv.sum_comp (Equiv.cast (eG (Fin.last n)))
      (fun z' => matReindex _ W (i₁, Fin.snoc o₁ z') (i₂, Fin.snoc o₂ z'))).symm) ?_
    refine Eq.trans (Finset.sum_congr rfl (fun z _ => key z)) ?_
    rw [hpeel (fun j => cast (eF j).symm (i₁ j)) (fun j => cast (eF j).symm (i₂ j))
      (fun j : Fin n => cast (eG j.castSucc).symm (o₁ j))
      (fun j : Fin n => cast (eG j.castSucc).symm (o₂ j))]
    by_cases hc : i₁ (Fin.last n) = i₂ (Fin.last n)
    · rw [ite_eq_left (hcond.2 hc), ite_eq_left hc]
      rw [matReindex_apply]
      rfl
    · rw [ite_eq_right (fun h' => hc (hcond.1 h')), ite_eq_right hc]

/-- Boundary peel equation for the successor-form composite: summing the
composite over its pending output and peeling the outer comb's normalization
through the boundary chain leaves the reindexed reduced-depth witness entry,
with the condition transported across the boundary index spellings. The
empty-output case is discharged in the boundary assembly identity. -/
private theorem bnd_trunc_eq_core (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)))
    (XW : CMatrix (Space (fun j : Fin (m + 1) => suffixOut O k (m + 1) hkm j.castSucc)
      (fun j : Fin (m + 1) => suffixIn I k (m + 1) hkm j.castSucc)))
    (hpeelX : ∀ (ii ii' : ∀ j, suffixOut O k (m + 1) hkm j)
      (oo oo' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc),
      (∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
          X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (m + 1)) = ii' (Fin.last (m + 1)) then
          XW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (W₂ : CMatrix (Space
      (fun j : Fin (n - m) => I (Fin.castSucc (compInS (n := n) k m hkm0 j.castSucc)))
      (fun j : Fin (n - m) => O (Fin.castSucc (compOutS (n := n) k m hkm0 j.castSucc)))))
    (hpeelD : ∀ (ii ii' : ∀ j : Fin (n - m + 1), I (Fin.castSucc (compInS (n := n) k m hkm0 j)))
      (oo oo' : ∀ j : Fin (n - m), O (Fin.castSucc (compOutS (n := n) k m hkm0 j.castSucc))),
      (∑ z : O (Fin.castSucc (compOutS (n := n) k m hkm0 (Fin.last (n - m)))),
          suffixCompS (I := fun t : Fin (n + 2) => I t.castSucc)
            (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0 K XW
            (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z))
        = if ii (Fin.last (n - m)) = ii' (Fin.last (n - m)) then
          W₂ ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (i i' : ∀ j : Fin ((n + 1) - (m + 1) + 1), I (compInS (n := n + 1) k (m + 1) hkm j))
    (o o' : ∀ j : Fin ((n + 1) - (m + 1)), O (compOutS (n := n + 1) k (m + 1) hkm j.castSucc)) :
    (∑ z : O (compOutS (n := n + 1) k (m + 1) hkm (Fin.last ((n + 1) - (m + 1)))),
        suffixCompS (I := I) (O := O) (n := n + 1) k (m + 1) hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = if i (Fin.last ((n + 1) - (m + 1))) = i' (Fin.last ((n + 1) - (m + 1))) then
          (matReindex (famBndEquiv (I := I) (O := O) k m hkm hkb hkm0) W₂)
            ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o')
        else 0 := by
  rw [bnd_eq k m hkm hkb hkm0 J K hpeel X XW hpeelX i i' o o']
  refine Eq.trans (Equiv.sum_comp (Equiv.cast (congrArg O (bnd_pending_eq k m hkm hkb hkm0)))
    (fun z => suffixCompS (I := fun t : Fin (n + 2) => I t.castSucc)
      (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0 K XW
      (bndI0 k m hkm hkb hkm0 i, Fin.snoc (bndO0 k m hkm hkb hkm0 o) z)
      (bndI0 k m hkm hkb hkm0 i', Fin.snoc (bndO0 k m hkm hkb hkm0 o') z))) ?_
  rw [hpeelD (bndI0 k m hkm hkb hkm0 i) (bndI0 k m hkm hkb hkm0 i')
    (bndO0 k m hkm hkb hkm0 o) (bndO0 k m hkm hkb hkm0 o')]
  have hrew : Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m))
      = Fin.last ((n + 1) - (m + 1)) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_last]
    omega
  have hcast2 : ∀ (N : Nat) (Fam : Fin N → Type u) (j₁ j₂ : Fin N) (hj : j₁ = j₂)
      (iv : ∀ j, Fam j), cast (congrArg Fam hj) (iv j₁) = iv j₂ := by
    intro N Fam j₁ j₂ hj iv
    subst hj
    rfl
  have hI : cast (congrArg (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx)) hrew)
        (i (Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m))))
      = i (Fin.last ((n + 1) - (m + 1))) :=
    hcast2 ((n + 1) - (m + 1) + 1) (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx))
      (Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m)))
      (Fin.last ((n + 1) - (m + 1))) hrew i
  have hI' : cast (congrArg (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx)) hrew)
        (i' (Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m))))
      = i' (Fin.last ((n + 1) - (m + 1))) :=
    hcast2 ((n + 1) - (m + 1) + 1) (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx))
      (Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m)))
      (Fin.last ((n + 1) - (m + 1))) hrew i'
  have hbI : ∀ (iv : ∀ j : Fin ((n + 1) - (m + 1) + 1),
        I (compInS (n := n + 1) k (m + 1) hkm j)),
      (bndI0 k m hkm hkb hkm0 iv) (Fin.last (n - m))
        = cast (congrArg I (compInS_bnd_tail_eq k m hkm hkb hkm0 (Fin.last (n - m))))
            (iv (Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m)))) := by
    intro iv
    simp only [bndI0]
  by_cases hc : i (Fin.last ((n + 1) - (m + 1))) = i' (Fin.last ((n + 1) - (m + 1)))
  · have hif : (bndI0 k m hkm hkb hkm0 i) (Fin.last (n - m)) =
        (bndI0 k m hkm hkb hkm0 i') (Fin.last (n - m)) := by
      rw [hbI i, hbI i']
      have h2 : cast (congrArg (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx)) hrew)
            (i (Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m))))
          = cast (congrArg (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx)) hrew)
            (i' (Fin.cast (by omega : n - m + 1 = (n + 1) - (m + 1) + 1) (Fin.last (n - m)))) := by
        rw [hI, hI', hc]
      have h3 := congrArg (cast
        (congrArg (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx)) hrew).symm) h2
      rw [cast_cast_cancel', cast_cast_cancel'] at h3
      exact congrArg (cast (congrArg I (compInS_bnd_tail_eq k m hkm hkb hkm0 (Fin.last (n - m))))) h3
    rw [ite_eq_left hif, ite_eq_left hc]
    rw [matReindex_apply]
    rw [bndConfig_eq (I := I) (O := O) k m hkm hkb hkm0 i o,
      bndConfig_eq (I := I) (O := O) k m hkm hkb hkm0 i' o']
  · rw [ite_eq_right (fun h' => hc (by
      rw [hbI i, hbI i'] at h'
      have hg := congrArg (cast (congrArg I
        (compInS_bnd_tail_eq k m hkm hkb hkm0 (Fin.last (n - m)))).symm) h'
      rw [cast_cast_cancel', cast_cast_cancel'] at hg
      rw [← hI, ← hI']
      exact congrArg (cast (congrArg (fun idx => I (compInS (n := n + 1) k (m + 1) hkm idx)) hrew)) hg)), ite_eq_right hc]

/-- Boundary normalization step: composing the outer comb with a normalized
window at the boundary depth preserves normalization, with the reindexed
reduced-depth composite as the tail witness. The recursion consumer supplies
the window's own witness and peel, plus the normalized reduced-depth
composite. The boundary trace identity also covers empty pending wires. -/
private theorem normalized_bnd_succ (k m : Nat) (hkm : k + (m + 1) + 1 ≤ n + 2)
    (hkb : k + (m + 1) + 1 = n + 2) (hkm0 : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (hJpos : J.PosSemidef)
    (X : CMatrix (Space (suffixOut O k (m + 1) hkm) (suffixIn I k (m + 1) hkm)))
    (hXpos : X.PosSemidef)
    (XW : CMatrix (Space (fun j : Fin (m + 1) => suffixOut O k (m + 1) hkm j.castSucc)
      (fun j : Fin (m + 1) => suffixIn I k (m + 1) hkm j.castSucc)))
    (hpeelX : ∀ (ii ii' : ∀ j, suffixOut O k (m + 1) hkm j)
      (oo oo' : ∀ j : Fin (m + 1), suffixIn I k (m + 1) hkm j.castSucc),
      (∑ z : suffixIn I k (m + 1) hkm (Fin.last (m + 1)),
          X (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (m + 1)) = ii' (Fin.last (m + 1)) then
          XW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (hDWnorm : Normalized
      (fun j : Fin (n - m + 1) => I (Fin.castSucc (compInS (n := n) k m hkm0 j)))
      (fun j : Fin (n - m + 1) => O (Fin.castSucc (compOutS (n := n) k m hkm0 j)))
      (suffixCompS (I := fun t : Fin (n + 2) => I t.castSucc)
        (O := fun t : Fin (n + 2) => O t.castSucc) (n := n) k m hkm0 K XW)) :
    Normalized
      (fun j : Fin ((n + 1) - (m + 1) + 1) => I (compInS (n := n + 1) k (m + 1) hkm j))
      (fun j : Fin ((n + 1) - (m + 1) + 1) => O (compOutS (n := n + 1) k (m + 1) hkm j))
      (suffixCompS (I := I) (O := O) (n := n + 1) k (m + 1) hkm J X) := by
  rcases hDWnorm with ⟨-, W₂, hW₂, hpeelD⟩
  refine ⟨matReindex_posSemidef _
      (suffixComp_posSemidef (n := n + 1) k (m + 1) hkm J X hJpos hXpos),
    matReindex (famBndEquiv (I := I) (O := O) k m hkm hkb hkm0) W₂, ?_, ?_⟩
  · exact normalized_castIdx (n - m) ((n + 1) - (m + 1)) (by omega)
      (fun j : Fin (n - m) => famBndEqI (I := I) k m hkm hkb hkm0 ⟨(j : Nat), by omega⟩)
      (fun j : Fin (n - m) => famBndEqO (O := O) k m hkm hkb hkm0 ⟨(j : Nat), by omega⟩)
      W₂ hW₂
  · intro i i' o o'
    exact bnd_trunc_eq_core k m hkm hkb hkm0 J K hpeel X XW hpeelX W₂ hpeelD i i' o o'

/-! ### The tight `m = 0` boundary: index degeneration and row computation -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the tight `m = 0` boundary the window sits directly before the last
tooth, and the composite input index map degenerates to the value-preserving
embedding. -/
private theorem compInS_m0 (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (j : Fin ((n + 1) - 0 + 1)) :
    compInS (n := n + 1) k 0 hkm j = Fin.castSucc j := by
  apply Fin.ext
  have hj := j.isLt
  simp only [compInS_val, Fin.val_castSucc]
  split <;> omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The composite output index at a below-window successor index degenerates to
the value-preserving embedding. -/
private theorem compOutS_m0_castSucc (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (j : Fin ((n + 1) - 0)) :
    compOutS (n := n + 1) k 0 hkm j.castSucc
      = Fin.castSucc (⟨(j : Nat), by omega⟩ : Fin (n + 2)) := by
  apply Fin.ext
  have hj := j.isLt
  simp only [compOutS_val, Fin.val_castSucc]
  split <;> omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The snoc-packed output tuple at the tight `m = 0` boundary reads the
successor-form entry below the window. -/
private theorem snocP_m0_lt (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (o : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0))))
    (j : Fin ((n + 1) + 1 - 0)) (hj : (j : Nat) < k) :
    snocP (O := O) (n := n + 1) k 0 hkm o z j = o ⟨(j : Nat), by omega⟩ := by
  show Fin.snoc (α := fun i : Fin ((n + 1) - 0 + 1) => O (compOutS (n := n + 1) k 0 hkm i)) o z
      ((compIdxEquiv (n := n + 1) k 0 hkm).symm j) = _
  exact Fin.snoc_castSucc (α := fun i : Fin ((n + 1) - 0 + 1) =>
      O (compOutS (n := n + 1) k 0 hkm i)) z o ⟨(j : Nat), by omega⟩

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The window's input-side connected wire at the tight `m = 0` boundary is the
outer comb's penultimate output wire. -/
private theorem connFam₁_m0_castAdd (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2) :
    (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ (Fin.castAdd 1 (Fin.last 0))
      = O (Fin.castSucc (Fin.last (n + 1))) := by
  show append (suffixOut O k 0 hkm) (suffixIn I k 0 hkm) (Fin.castAdd 1 (Fin.last 0)) = _
  rw [append_castAdd]
  exact congrArg O (Fin.ext (by simp only [suffixOutIdx, Fin.val_last, Fin.val_castSucc]; omega))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Row computation, input side, at the tight `m = 0` boundary: reading the
flattened outer configuration at a below-window input position returns the
successor-form composite input entry. -/
private theorem m0_flat_in (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (zc : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q)
    (i : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0))))
    (j : Fin (n + 2)) :
    (rowFlat (I := I) (O := O) k 0 hkm zc (peelU (I := I) k 0 hkm i)
        (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc
      = cast (congrArg I (compInS_m0 k hkm hkb j)) (i j) := by
  have hj := j.isLt
  show cast (append_castAdd I O j.castSucc)
      ((suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).read₂ zc
        (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
          (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀))
        (Fin.castAdd (n + 3) j.castSucc)) = _
  have hpos : complEmb (suffixConnIdx (n := n + 1) k 0 hkm)
      (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).hι₂ ⟨(j : Nat), by omega⟩
      = Fin.castAdd (n + 3) j.castSucc := by
    rw [suffixComplEmb (n := n + 1) k 0 hkm
      (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).hι₂ ⟨(j : Nat), by omega⟩,
      suffixComplIdx_of_lt_le (n := n + 1) k 0 hkm ⟨(j : Nat), by omega⟩
        (by show (j : Nat) < (n + 1) + 1 - 0; omega) (by show (j : Nat) ≤ k; omega)]
    rfl
  have hc1 := read₂_congr_pos (I := I) (O := O) (n := n + 1) k 0 hkm zc
    (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
      (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀)) hpos
  refine Eq.trans (congrArg (cast (append_castAdd I O j.castSucc)) hc1.symm) ?_
  rw [suffixRead₂_compl (I := I) (O := O) (n := n + 1) k 0 hkm zc
      (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
        (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀))
      ⟨(j : Nat), by omega⟩,
    complPack_lt (I := I) (O := O) (n := n + 1) k 0 hkm
      (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀)
      ⟨(j : Nat), by omega⟩ (by show (j : Nat) < (n + 1) + 1 - 0; omega),
    show peelU (I := I) k 0 hkm i ⟨(j : Nat), by omega⟩ = i j from rfl]
  exact (cast3 (complFam₂_eq_lt (I := I) (O := O) (n := n + 1) k 0 hkm
      ⟨(j : Nat), by omega⟩ (by show (j : Nat) < (n + 1) + 1 - 0; omega)).symm
    (congrArg (append I O) hpos) (append_castAdd I O j.castSucc) (i j)).trans rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Row computation, output side, at the tight `m = 0` boundary: reading the
flattened outer configuration at a below-window output position returns the
successor-form composite output entry. -/
private theorem m0_flat_out_lt (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (zc : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q)
    (i : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0))))
    (t : Fin (n + 2)) (ht : (t : Nat) < k) :
    (rowFlat (I := I) (O := O) k 0 hkm zc (peelU (I := I) k 0 hkm i)
        (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc
      = cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
          (o ⟨(t : Nat), by omega⟩) := by
  have ht' := t.isLt
  show cast (append_natAdd I O t.castSucc)
      ((suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).read₂ zc
        (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
          (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀))
        (Fin.natAdd (n + 3) t.castSucc)) = _
  have hpos : complEmb (suffixConnIdx (n := n + 1) k 0 hkm)
      (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).hι₂
      ⟨(n + 1) + 1 - 0 + (t : Nat), by omega⟩
      = Fin.natAdd (n + 3) t.castSucc := by
    rw [suffixComplEmb (n := n + 1) k 0 hkm
      (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).hι₂
      ⟨(n + 1) + 1 - 0 + (t : Nat), by omega⟩,
      suffixComplIdx_of_ge_lt (n := n + 1) k 0 hkm ⟨(n + 1) + 1 - 0 + (t : Nat), by omega⟩
        (by show ¬((n + 1) + 1 - 0 + (t : Nat) < (n + 1) + 1 - 0); omega)
        (by show (n + 1) + 1 - 0 + (t : Nat) - ((n + 1) + 1 - 0) < k; omega)]
    apply Fin.ext
    show (n + 3) + ((n + 1) + 1 - 0 + (t : Nat) - ((n + 1) + 1 - 0)) = (n + 3) + (t : Nat)
    omega
  have hc1 := read₂_congr_pos (I := I) (O := O) (n := n + 1) k 0 hkm zc
    (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
      (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀)) hpos
  refine Eq.trans (congrArg (cast (append_natAdd I O t.castSucc)) hc1.symm) ?_
  rw [suffixRead₂_compl (I := I) (O := O) (n := n + 1) k 0 hkm zc
      (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
        (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀))
      ⟨(n + 1) + 1 - 0 + (t : Nat), by omega⟩,
    complPack_ge' (I := I) (O := O) (n := n + 1) k 0 hkm
      (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀)
      ⟨(t : Nat), by omega⟩,
    snocP_m0_lt (O := O) k hkm hkb o z₀ ⟨(t : Nat), by omega⟩ ht]
  exact (cast3 (complFam₂_eq_ge' (I := I) (O := O) (n := n + 1) k 0 hkm
      ⟨(t : Nat), by omega⟩).symm
    (congrArg (append I O) hpos) (append_natAdd I O t.castSucc) (o ⟨(t : Nat), by omega⟩)).trans rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Row computation, output side, at the window position of the tight `m = 0`
boundary: the flattened outer configuration reads the connected wire entry. -/
private theorem m0_flat_out_last (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (zc : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q)
    (i : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0)))) :
    (rowFlat (I := I) (O := O) k 0 hkm zc (peelU (I := I) k 0 hkm i)
        (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 (Fin.last (n + 1)).castSucc
      = cast (connFam₁_m0_castAdd (I := I) (O := O) k hkm hkb)
          (zc (Fin.castAdd 1 (Fin.last 0))) := by
  show cast (append_natAdd I O (Fin.last (n + 1)).castSucc)
      ((suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).read₂ zc
        (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
          (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀))
        (Fin.natAdd (n + 3) (Fin.last (n + 1)).castSucc)) = _
  have hpos : suffixConnIdx (n := n + 1) k 0 hkm (Fin.castAdd 1 (Fin.last 0))
      = Fin.natAdd (n + 3) (Fin.last (n + 1)).castSucc := by
    rw [suffixConnIdx_castAdd]
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_last, Fin.val_castSucc]
    omega
  have hc1 := read₂_congr_pos (I := I) (O := O) (n := n + 1) k 0 hkm zc
    (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
      (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀)) hpos
  refine Eq.trans (congrArg (cast (append_natAdd I O (Fin.last (n + 1)).castSucc)) hc1.symm) ?_
  rw [suffixRead₂_conn_castAdd (I := I) (O := O) (n := n + 1) k 0 hkm zc
      (complPack (I := I) (O := O) (n := n + 1) k 0 hkm
        (peelU (I := I) k 0 hkm i) (snocP (O := O) (n := n + 1) k 0 hkm o z₀))
      (Fin.last 0)]
  have hEq : (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁
      (Fin.castAdd 1 (Fin.last 0))
      = append I O (suffixConnIdx (n := n + 1) k 0 hkm (Fin.castAdd 1 (Fin.last 0))) := by
    show append (suffixOut O k 0 hkm) (suffixIn I k 0 hkm) (Fin.castAdd 1 (Fin.last 0)) = _
    rw [append_castAdd, suffixConnIdx_castAdd, append_natAdd]
    show O (suffixOutIdx k 0 hkm (Fin.last 0)) = O ⟨k + (Fin.last 0 : Fin 1), by omega⟩
    rfl
  rw [show (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).eRelabel zc
        (Fin.castAdd 1 (Fin.last 0))
      = cast hEq (zc (Fin.castAdd 1 (Fin.last 0))) from rfl]
  exact (cast3 hEq (congrArg (append I O) hpos)
      (append_natAdd I O (Fin.last (n + 1)).castSucc) (zc (Fin.castAdd 1 (Fin.last 0)))).trans rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The window's top output wire at the tight `m = 0` boundary is the outer
comb's penultimate output wire. -/
private theorem m0_wO_eq (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2) :
    suffixOut O k 0 hkm (Fin.last 0) = O (Fin.castSucc (Fin.last (n + 1))) := by
  show O (suffixOutIdx k 0 hkm (Fin.last 0)) = _
  exact congrArg O (Fin.ext (by simp only [suffixOutIdx, Fin.val_last, Fin.val_castSucc]; omega))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation at the tight `m = 0` boundary: the flattened
inner configuration at the single output-side index reads off the pending
output value. -/
private theorem m0_XFlat_castAdd_last (k : Nat) (hkm : k + 0 + 1 ≤ n + 2)
    (zcO : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc)
    (wO : suffixOut O k 0 hkm (Fin.last 0))
    (zcI : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc)
    (wI : suffixIn I k 0 hkm (Fin.last 0)) :
    XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.castAdd 1 (Fin.last 0))
      = cast (append_castAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
          (Fin.last 0)).symm wO := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_left,
    Fin.snoc_last, Equiv.cast_apply]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Boundary packing computation at the tight `m = 0` boundary: the flattened
inner configuration at the single input-side index reads off the pending
input value. -/
private theorem m0_XFlat_natAdd_last (k : Nat) (hkm : k + 0 + 1 ≤ n + 2)
    (zcO : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc)
    (wO : suffixOut O k 0 hkm (Fin.last 0))
    (zcI : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc)
    (wI : suffixIn I k 0 hkm (Fin.last 0)) :
    XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
        (Fin.snoc zcO wO, Fin.snoc zcI wI) (Fin.natAdd 1 (Fin.last 0))
      = cast (append_natAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
          (Fin.last 0)).symm wI := by
  simp only [XFlatEquiv, splitAppendEquiv_symm_apply, Fin.addCases_right,
    Fin.snoc_last, Equiv.cast_apply]

/-- A sum over an empty block family collapses to the single term. -/
private theorem sum_pi_fin0 {F : Fin 0 → Type u} [∀ j, Fintype (F j)] (f : (∀ j, F j) → ℂ)
    (g : ∀ j, F j) :
    ∑ x : ∀ j, F j, f x = f g := by
  refine Finset.sum_eq_single g (fun b _ hb => absurd (Subsingleton.elim b g) hb)
    (fun hb => absurd (Finset.mem_univ g) hb)

/-- Boundary sum rearrangement at the tight `m = 0` boundary: pulling the
last-output sum inside the window contraction and applying the outer peel per
connected configuration. -/
private theorem m0_swap (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)))
    (i i' : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o o' : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0)))) :
    (∑ z : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0))),
        ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz) *
          J (rowFlat (I := I) (O := O) k 0 hkm zz' (peelU (I := I) k 0 hkm i)
              (snocP (O := O) (n := n + 1) k 0 hkm o z))
            (rowFlat (I := I) (O := O) k 0 hkm zz (peelU (I := I) k 0 hkm i')
              (snocP (O := O) (n := n + 1) k 0 hkm o' z)))
      = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz) *
          (if zz' (Fin.natAdd (0 + 1) (Fin.last 0)) = zz (Fin.natAdd (0 + 1) (Fin.last 0)) then
            K ((fun j => (rowFlat (I := I) (O := O) k 0 hkm zz' (peelU (I := I) k 0 hkm i)
                    (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zz'
                (peelU (I := I) k 0 hkm i)
                (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k 0 hkm zz (peelU (I := I) k 0 hkm i')
                    (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zz
                (peelU (I := I) k 0 hkm i')
                (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
          else 0) := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun zz _ =>
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun zz' _ => ?_)))
  refine (Finset.mul_sum _ _ _).symm.trans ?_
  exact congrArg _ (bnd_inner k 0 hkm hkb J K hpeel zz zz' i i' o o' z₀)

/-- Boundary split form at the tight `m = 0` boundary: reindexing the
connected window configurations of the swapped boundary equation by the
flattening equivalence and splitting each window block at its last wire
exhibits the shared-trace structure — the outer peel's condition becomes
equality of the row and column pending input values; the truncated blocks
are empty. -/
private theorem m0_split (k : Nat) (hkm : k + 0 + 1 ≤ n + 2)
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)))
    (i i' : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o o' : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0)))) :
    (∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz) *
          (if zz' (Fin.natAdd (0 + 1) (Fin.last 0)) = zz (Fin.natAdd (0 + 1) (Fin.last 0)) then
            K ((fun j => (rowFlat (I := I) (O := O) k 0 hkm zz' (peelU (I := I) k 0 hkm i)
                    (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zz'
                (peelU (I := I) k 0 hkm i)
                (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k 0 hkm zz (peelU (I := I) k 0 hkm i')
                    (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zz
                (peelU (I := I) k 0 hkm i')
                (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
          else 0))
      = ∑ zcO : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc,
        ∑ wO : suffixOut O k 0 hkm (Fin.last 0),
        ∑ zcI : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc,
        ∑ wO' : suffixOut O k 0 hkm (Fin.last 0),
        ∑ zcI' : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc,
        ∑ wI : suffixIn I k 0 hkm (Fin.last 0),
        ∑ wI' : suffixIn I k 0 hkm (Fin.last 0),
          X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k 0 hkm i)
                    (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k 0 hkm i)
                (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k 0 hkm i')
                    (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k 0 hkm i')
                (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
          else 0) := by
  refine Eq.trans (sum_reindex_two (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm)
    (fun (zz' zz : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q) =>
      X ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz')
          ((XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm).symm zz) *
        (if zz' (Fin.natAdd (0 + 1) (Fin.last 0)) = zz (Fin.natAdd (0 + 1) (Fin.last 0)) then
          K ((fun j => (rowFlat (I := I) (O := O) k 0 hkm zz' (peelU (I := I) k 0 hkm i)
                  (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zz'
              (peelU (I := I) k 0 hkm i)
              (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
          ((fun j => (rowFlat (I := I) (O := O) k 0 hkm zz (peelU (I := I) k 0 hkm i')
                  (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
            fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zz
              (peelU (I := I) k 0 hkm i')
              (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
        else 0))) ?_
  simp only [Equiv.symm_apply_apply]
  rw [sum_space_snoc2]
  have hpt : ∀ (zcO : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc)
      (wO : suffixOut O k 0 hkm (Fin.last 0))
      (zcI : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc)
      (wI : suffixIn I k 0 hkm (Fin.last 0))
      (zcO' : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc)
      (wO' : suffixOut O k 0 hkm (Fin.last 0))
      (zcI' : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc)
      (wI' : suffixIn I k 0 hkm (Fin.last 0)),
      X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                (Fin.snoc zcO' wO', Fin.snoc zcI' wI')) (Fin.natAdd (0 + 1) (Fin.last 0))
              = (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI)) (Fin.natAdd (0 + 1) (Fin.last 0)) then
            K ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k 0 hkm i)
                    (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k 0 hkm i)
                (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k 0 hkm i')
                    (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k 0 hkm i')
                (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
          else 0)
        = X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k 0 hkm i)
                    (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k 0 hkm i)
                (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k 0 hkm i')
                    (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k 0 hkm i')
                (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
          else 0) := by
    intro zcO wO zcI wI zcO' wO' zcI' wI'
    have h1 := m0_XFlat_natAdd_last k hkm zcO' wO' zcI' wI'
    have h2 := m0_XFlat_natAdd_last k hkm zcO wO zcI wI
    by_cases hcc : wI' = wI
    · subst hcc
      rw [ite_eq_left (by rw [h1, h2]), ite_eq_left rfl]
    · rw [ite_eq_right (fun heq => hcc ((Equiv.cast
          (append_natAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
            (Fin.last 0)).symm).injective (h1.symm.trans (heq.trans h2)))),
        ite_eq_right hcc]
  exact Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun wO _ =>
    Finset.sum_congr rfl fun zcI _ => Finset.sum_congr rfl fun zcO' _ =>
      Finset.sum_congr rfl fun wO' _ => Finset.sum_congr rfl fun zcI' _ =>
        Finset.sum_congr rfl fun wI _ => Finset.sum_congr rfl fun wI' _ =>
          hpt zcO wO zcI wI zcO' wO' zcI' wI'

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Row folding at the tight `m = 0` boundary: reading the flattened outer
configuration in the boundary peel's witness entry reduces to the
successor-form composite entries below the window plus the pending output
value at the window position; the pending input value drops out because the
witness entry never reads the outer last input wire. -/
private theorem m0_row_fold (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (zc : ∀ q, (suffixMatch (I := I) (O := O) (n := n + 1) k 0 hkm).connFam₁ q)
    (ii : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (oo : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0))))
    (wO : suffixOut O k 0 hkm (Fin.last 0))
    (hzc : zc (Fin.castAdd 1 (Fin.last 0))
      = cast (append_castAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
          (Fin.last 0)).symm wO) :
    ((fun j : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zc
            (peelU (I := I) k 0 hkm ii)
            (snocP (O := O) (n := n + 1) k 0 hkm oo z₀)).1 j.castSucc),
      fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm zc
          (peelU (I := I) k 0 hkm ii)
          (snocP (O := O) (n := n + 1) k 0 hkm oo z₀)).2 t.castSucc)
      = ((fun j : Fin (n + 2) => cast (congrArg I (compInS_m0 k hkm hkb j)) (ii j)),
        Fin.snoc (fun t : Fin (n + 1) =>
            cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
              (oo ⟨(t : Nat), by omega⟩))
          (cast (connFam₁_m0_castAdd (I := I) (O := O) k hkm hkb)
            (cast (append_castAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
              (Fin.last 0)).symm wO))) := by
  apply Prod.ext
  · funext j
    exact m0_flat_in k hkm hkb zc ii oo z₀ j
  · funext t
    rcases t.eq_castSucc_or_eq_last with ⟨t₀, rfl⟩ | rfl
    · rw [m0_flat_out_lt k hkm hkb zc ii oo z₀ t₀.castSucc
        (by show (t₀ : Nat) < k; omega)]
      simp only [Fin.snoc_castSucc]
      rfl
    · rw [m0_flat_out_last k hkm hkb zc ii oo z₀, hzc]
      simp only [Fin.snoc_last]
      rfl

/-- Boundary collapse at the tight `m = 0` boundary: folding the window row
configurations to the composite entries, contracting the inner comb's pending
input through its own normalization peel (whose scalar witness is one), and
collapsing the two Kronecker deltas leaves the outer witness entry with the
surviving pending output value shared by the row and column arguments. -/
private theorem m0_collapse (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)))
    (hX : Normalized (suffixOut O k 0 hkm) (suffixIn I k 0 hkm) X)
    (i i' : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o o' : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0)))) :
    (∑ zcO : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc,
        ∑ wO : suffixOut O k 0 hkm (Fin.last 0),
        ∑ zcI : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc,
        ∑ wO' : suffixOut O k 0 hkm (Fin.last 0),
        ∑ zcI' : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc,
        ∑ wI : suffixIn I k 0 hkm (Fin.last 0),
        ∑ wI' : suffixIn I k 0 hkm (Fin.last 0),
          X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (peelU (I := I) k 0 hkm i)
                    (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (peelU (I := I) k 0 hkm i)
                (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (rowFlat (I := I) (O := O) k 0 hkm
                    (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (peelU (I := I) k 0 hkm i')
                    (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
                (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (peelU (I := I) k 0 hkm i')
                (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
          else 0))
      = ∑ wO : suffixOut O k 0 hkm (Fin.last 0),
          K ((fun j : Fin (n + 2) => cast (congrArg I (compInS_m0 k hkm hkb j)) (i j)),
            Fin.snoc (fun t : Fin (n + 1) =>
                cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                  (o ⟨(t : Nat), by omega⟩))
              (cast (connFam₁_m0_castAdd (I := I) (O := O) k hkm hkb)
                (cast (append_castAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
                  (Fin.last 0)).symm wO)))
          ((fun j : Fin (n + 2) => cast (congrArg I (compInS_m0 k hkm hkb j)) (i' j)),
            Fin.snoc (fun t : Fin (n + 1) =>
                cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                  (o' ⟨(t : Nat), by omega⟩))
              (cast (connFam₁_m0_castAdd (I := I) (O := O) k hkm hkb)
                (cast (append_castAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
                  (Fin.last 0)).symm wO))) := by
  rcases hX with ⟨-, XW, hXW, hpeelX⟩
  have hXWeq : XW = 1 := (normalized_zero _ _ XW).mp hXW
  have eO : ∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc := fun j => Fin.elim0 j
  have eI : ∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc := fun j => Fin.elim0 j
  have hm0pm : ∀ (wO wO' : suffixOut O k 0 hkm (Fin.last 0)) (c : ℂ),
      (∑ wI : suffixIn I k 0 hkm (Fin.last 0),
          X (Fin.snoc eO wO', Fin.snoc eI wI)
              (Fin.snoc eO wO, Fin.snoc eI wI) * c) =
        if wO' = wO then 1 * c else 0 := by
    intro wO wO' c
    have hf : (∑ wI : suffixIn I k 0 hkm (Fin.last 0),
          X (Fin.snoc eO wO', Fin.snoc eI wI)
              (Fin.snoc eO wO, Fin.snoc eI wI)) * c =
        ∑ wI : suffixIn I k 0 hkm (Fin.last 0),
          X (Fin.snoc eO wO', Fin.snoc eI wI)
              (Fin.snoc eO wO, Fin.snoc eI wI) * c :=
      Finset.sum_mul Finset.univ _ _
    rw [← hf, hpeelX (Fin.snoc eO wO') (Fin.snoc eO wO) eI eI,
      ite_mul, zero_mul, hXWeq]
    simp only [Fin.snoc_last, Matrix.one_apply]
    by_cases hw : wO' = wO
    · subst hw
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right hw, ite_eq_right hw]
  have hrow : ∀ (wO' : suffixOut O k 0 hkm (Fin.last 0)) (wI : suffixIn I k 0 hkm (Fin.last 0)),
      ((fun j : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
              (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                (Fin.snoc eO wO', Fin.snoc eI wI))
              (peelU (I := I) k 0 hkm i)
              (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).1 j.castSucc),
        fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
            (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
              (Fin.snoc eO wO', Fin.snoc eI wI))
            (peelU (I := I) k 0 hkm i)
            (snocP (O := O) (n := n + 1) k 0 hkm o z₀)).2 t.castSucc)
        = ((fun j : Fin (n + 2) => cast (congrArg I (compInS_m0 k hkm hkb j)) (i j)),
          Fin.snoc (fun t : Fin (n + 1) =>
              cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                (o ⟨(t : Nat), by omega⟩))
            (cast (connFam₁_m0_castAdd (I := I) (O := O) k hkm hkb)
              (cast (append_castAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
                (Fin.last 0)).symm wO'))) :=
    fun wO' wI => m0_row_fold k hkm hkb _ i o z₀ wO'
      (m0_XFlat_castAdd_last k hkm eO wO' eI wI)
  have hcol : ∀ (wO : suffixOut O k 0 hkm (Fin.last 0)) (wI : suffixIn I k 0 hkm (Fin.last 0)),
      ((fun j : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
              (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
                (Fin.snoc eO wO, Fin.snoc eI wI))
              (peelU (I := I) k 0 hkm i')
              (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).1 j.castSucc),
        fun t : Fin (n + 2) => (rowFlat (I := I) (O := O) k 0 hkm
            (XFlatEquiv (I := I) (O := O) (n := n + 1) k 0 hkm
              (Fin.snoc eO wO, Fin.snoc eI wI))
            (peelU (I := I) k 0 hkm i')
            (snocP (O := O) (n := n + 1) k 0 hkm o' z₀)).2 t.castSucc)
        = ((fun j : Fin (n + 2) => cast (congrArg I (compInS_m0 k hkm hkb j)) (i' j)),
          Fin.snoc (fun t : Fin (n + 1) =>
              cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                (o' ⟨(t : Nat), by omega⟩))
            (cast (connFam₁_m0_castAdd (I := I) (O := O) k hkm hkb)
              (cast (append_castAdd (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)
                (Fin.last 0)).symm wO))) :=
    fun wO wI => m0_row_fold k hkm hkb _ i' o' z₀ wO
      (m0_XFlat_castAdd_last k hkm eO wO eI wI)
  have hzO : ∀ f : (∀ j : Fin 0, suffixOut O k 0 hkm j.castSucc) → ℂ,
      ∑ x, f x = f eO := fun f => sum_pi_fin0 f eO
  have hzI : ∀ f : (∀ j : Fin 0, suffixIn I k 0 hkm j.castSucc) → ℂ,
      ∑ x, f x = f eI := fun f => sum_pi_fin0 f eI
  simp only [hzO, hzI]
  simp only [hrow, hcol]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hm0pm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul]
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Witness reindex computation at the tight `m = 0` boundary: pulling the
target-side witness arguments back through the cast reindex produces the
folded boundary entries. -/
private theorem m0_witness_eq (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (i : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc)) :
    (castIdxEquiv (by omega : n + 1 = (n + 1) - 0)
        (fun j : Fin (n + 1) => (congrArg I (compInS_m0 k hkm hkb j.castSucc)).symm)
        (fun j : Fin (n + 1) =>
          (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(j : Nat), by omega⟩)).symm)).symm
        ((fun j : Fin ((n + 1) - 0) => i j.castSucc), o)
      = ((fun j : Fin (n + 1) =>
          cast (congrArg I (compInS_m0 k hkm hkb j.castSucc)) (i j.castSucc)),
        fun j : Fin (n + 1) =>
          cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(j : Nat), by omega⟩))
            (o ⟨(j : Nat), by omega⟩)) := by
  rfl

/-- Boundary peel at the tight `m = 0` boundary: summing the composite over
its pending output and contracting through the boundary chain leaves the
reindexed witness entry, with the peel condition transported across the
boundary index spellings, including an empty pending output. -/
private theorem m0_peel (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)))
    (hX : Normalized (suffixOut O k 0 hkm) (suffixIn I k 0 hkm) X)
    (KW : CMatrix (Space (fun j : Fin (n + 1) => I (Fin.castSucc (Fin.castSucc j)))
      (fun j : Fin (n + 1) => O (Fin.castSucc (Fin.castSucc j)))))
    (hpeelK : ∀ (ii ii' : ∀ j : Fin (n + 2), I (Fin.castSucc j))
      (oo oo' : ∀ j : Fin (n + 1), O (Fin.castSucc (Fin.castSucc j))),
      (∑ z : O (Fin.castSucc (Fin.last (n + 1))),
          K (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 1)) = ii' (Fin.last (n + 1)) then
          KW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (i i' : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j))
    (o o' : ∀ j : Fin ((n + 1) - 0), O (compOutS (n := n + 1) k 0 hkm j.castSucc)) :
    (∑ z : O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0))),
        suffixCompS (I := I) (O := O) (n := n + 1) k 0 hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = if i (Fin.last ((n + 1) - 0)) = i' (Fin.last ((n + 1) - 0)) then
          (matReindex (castIdxEquiv (by omega : n + 1 = (n + 1) - 0)
            (fun j : Fin (n + 1) => (congrArg I (compInS_m0 k hkm hkb j.castSucc)).symm)
            (fun j : Fin (n + 1) =>
              (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(j : Nat), by omega⟩)).symm))
            KW) ((fun j : Fin ((n + 1) - 0) => i j.castSucc), o)
            ((fun j : Fin ((n + 1) - 0) => i' j.castSucc), o')
        else 0 := by
  classical
  trans (∑ z : O (Fin.castSucc (Fin.last (n + 1))), K ((fun j : Fin (n + 2) =>
            cast (congrArg I (compInS_m0 k hkm hkb j)) (i j)),
          Fin.snoc (fun t : Fin (n + 1) =>
              cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                (o ⟨(t : Nat), by omega⟩)) z)
        ((fun j : Fin (n + 2) =>
            cast (congrArg I (compInS_m0 k hkm hkb j)) (i' j)),
          Fin.snoc (fun t : Fin (n + 1) =>
              cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                (o' ⟨(t : Nat), by omega⟩)) z))
  · rcases isEmpty_or_nonempty
        (O (compOutS (n := n + 1) k 0 hkm (Fin.last ((n + 1) - 0)))) with hE | hNE
    · have hEO : IsEmpty (O (Fin.last (n + 2))) :=
        congrArg O (compOutS_last (n := n + 1) k 0 hkm) ▸ hE
      refine (Finset.sum_eq_zero (fun z _ => hE.elim z)).trans ?_
      symm
      refine Finset.sum_eq_zero fun wO _ => ?_
      obtain ⟨wI⟩ := normalized_one_output_nonempty hX (cast (m0_wO_eq k hkm hkb).symm wO)
      have hWI : suffixIn I k 0 hkm (Fin.last 0) = I (Fin.last (n + 2)) :=
        congrArg I (Fin.ext (by simp only [suffixInIdx, Fin.val_last]; omega))
      exact peel_zero_of_empty_output J K hpeel hEO (cast hWI wI) _ _
    · obtain ⟨z₀⟩ := hNE
      refine Eq.trans (Finset.sum_congr rfl fun z _ =>
        trunc_eq_expand k 0 hkm J X i i' o o' z) ?_
      refine Eq.trans (m0_swap k hkm hkb J K hpeel X i i' o o' z₀) ?_
      refine Eq.trans (m0_split k hkm K X i i' o o' z₀) ?_
      refine Eq.trans (m0_collapse k hkm hkb K X hX i i' o o' z₀) ?_
      exact Equiv.sum_comp (Equiv.cast (m0_wO_eq k hkm hkb))
        (fun z => K ((fun j : Fin (n + 2) =>
                cast (congrArg I (compInS_m0 k hkm hkb j)) (i j)),
              Fin.snoc (fun t : Fin (n + 1) =>
                  cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                    (o ⟨(t : Nat), by omega⟩)) z)
            ((fun j : Fin (n + 2) =>
                cast (congrArg I (compInS_m0 k hkm hkb j)) (i' j)),
              Fin.snoc (fun t : Fin (n + 1) =>
                  cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
                    (o' ⟨(t : Nat), by omega⟩)) z))
  · rw [hpeelK (fun j : Fin (n + 2) => cast (congrArg I (compInS_m0 k hkm hkb j)) (i j))
      (fun j : Fin (n + 2) => cast (congrArg I (compInS_m0 k hkm hkb j)) (i' j))
      (fun t : Fin (n + 1) =>
        cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
          (o ⟨(t : Nat), by omega⟩))
      (fun t : Fin (n + 1) =>
        cast (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(t : Nat), by omega⟩))
          (o' ⟨(t : Nat), by omega⟩))]
    have hcI : ∀ (iv iv' : ∀ j : Fin ((n + 1) - 0 + 1), I (compInS (n := n + 1) k 0 hkm j)),
        cast (congrArg I (compInS_m0 k hkm hkb (Fin.last (n + 1)))) (iv (Fin.last (n + 1)))
          = cast (congrArg I (compInS_m0 k hkm hkb (Fin.last (n + 1)))) (iv' (Fin.last (n + 1)))
      ↔ iv (Fin.last (n + 1)) = iv' (Fin.last (n + 1)) := by
      intro iv iv'
      constructor
      · intro h
        exact (Equiv.cast (congrArg I (compInS_m0 k hkm hkb (Fin.last (n + 1))))).injective h
      · intro h
        rw [h]
    by_cases hc : i (Fin.last ((n + 1) - 0)) = i' (Fin.last ((n + 1) - 0))
    · rw [ite_eq_left hc, ite_eq_left ((hcI i i').mpr hc)]
      rw [matReindex_apply]
      rw [m0_witness_eq (I := I) (O := O) k hkm hkb i o,
        m0_witness_eq (I := I) (O := O) k hkm hkb i' o']
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((hcI i i').mp h'))]

/-- Boundary normalization step at the tight `m = 0` boundary: composing the
outer comb with a normalized single-output window at the boundary depth
preserves normalization, with the reindexed reduced-depth witness as the tail
witness. Empty pending outputs use the same witness and a vanishing trace. -/
private theorem normalized_m0_succ (k : Nat) (hkm : k + 0 + 1 ≤ n + 2) (hkb : k + 0 + 1 = n + 2)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc)))
    (hJpos : J.PosSemidef)
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (n + 2), O j.castSucc),
      (∑ z : O (Fin.last (n + 2)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (n + 2)) = ii' (Fin.last (n + 2)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (hK : Normalized (fun j : Fin (n + 2) => I j.castSucc)
      (fun j : Fin (n + 2) => O j.castSucc) K)
    (X : CMatrix (Space (suffixOut O k 0 hkm) (suffixIn I k 0 hkm)))
    (hXpos : X.PosSemidef)
    (hX : Normalized (suffixOut O k 0 hkm) (suffixIn I k 0 hkm) X) :
    Normalized
      (fun j : Fin ((n + 1) - 0 + 1) => I (compInS (n := n + 1) k 0 hkm j))
      (fun j : Fin ((n + 1) - 0 + 1) => O (compOutS (n := n + 1) k 0 hkm j))
      (suffixCompS (I := I) (O := O) (n := n + 1) k 0 hkm J X) := by
  rcases hK with ⟨-, KW, hKW', hpeelK⟩
  refine ⟨matReindex_posSemidef _
      (suffixComp_posSemidef (n := n + 1) k 0 hkm J X hJpos hXpos),
    matReindex (castIdxEquiv (by omega : n + 1 = (n + 1) - 0)
      (fun j : Fin (n + 1) => (congrArg I (compInS_m0 k hkm hkb j.castSucc)).symm)
      (fun j : Fin (n + 1) =>
        (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(j : Nat), by omega⟩)).symm))
      KW, ?_, ?_⟩
  · exact normalized_castIdx (n + 1) ((n + 1) - 0) (by omega)
      (fun j : Fin (n + 1) => (congrArg I (compInS_m0 k hkm hkb j.castSucc)).symm)
      (fun j : Fin (n + 1) =>
        (congrArg O (compOutS_m0_castSucc k hkm hkb ⟨(j : Nat), by omega⟩)).symm)
      KW hKW'
  · intro i i' o o'
    exact m0_peel k hkm hkb J K hpeel X hX KW hpeelK i i' o o'

end TailShift

set_option maxHeartbeats 1200000 in
/-- Normalization closure of suffix composition, by strong recursion on the
window budget `T = n + 1 - (k + m + 1) + m`: composing a normalized comb with
a normalized window at any feasible position preserves normalization. The
degenerate two-wire base case is supplied as a hypothesis so that the
recursion plumbing can be validated independently. Every recursive step
consumes one unit of budget: the slack step shortens the outer comb, the
boundary step shortens the window, and the tight `m = 0` boundary closes
directly. -/
theorem normalized_suffix_comp (T : Nat)
    (hBase : ∀ (I O : Fin (0 + 2) → Type u)
      [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
      [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
      (hkm : 0 + 0 + 1 ≤ 0 + 1)
      (J : CMatrix (Space I O)) (_hJ : Normalized I O J)
      (X : CMatrix (Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)))
      (_hX : Normalized (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm) X),
      Normalized (fun j : Fin (0 - 0 + 1) => I (compInS (n := 0) 0 0 hkm j))
        (fun j : Fin (0 - 0 + 1) => O (compOutS (n := 0) 0 0 hkm j))
        (suffixCompS (I := I) (O := O) (n := 0) 0 0 hkm J X)) :
    ∀ (n : Nat) (I O : Fin (n + 2) → Type u)
      [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
      [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
      (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
      (_hT : n + 1 - (k + m + 1) + m < T)
      (J : CMatrix (Space I O)) (_hJ : Normalized I O J)
      (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
      (_hX : Normalized (suffixOut O k m hkm) (suffixIn I k m hkm) X),
      Normalized (fun j : Fin (n - m + 1) => I (compInS (n := n) k m hkm j))
        (fun j : Fin (n - m + 1) => O (compOutS (n := n) k m hkm j))
        (suffixCompS (I := I) (O := O) (n := n) k m hkm J X) := by
  induction T with
  | zero =>
    intro n I O iI iId iO iOd k m hkm hT _ _ _ _
    exact absurd hT (by omega)
  | succ T ih =>
    intro n I O iI iId iO iOd k m hkm _hT J hJ X hX
    by_cases hslack : k + m + 1 ≤ n
    · -- slack: peel the untouched last tooth
      rcases n with _ | n
      · exact absurd hslack (by omega)
      · rcases hJ with ⟨hJpos, K, hK, hpeel⟩
        have hkm' : k + m + 1 ≤ n + 1 := by omega
        have hk : k < (n + 1) - m := by omega
        have hT' : n + 1 - (k + m + 1) + m < T := by omega
        let iIt : ∀ j : Fin (n + 2), Fintype ((fun t : Fin (n + 2) => I t.castSucc) j) :=
          fun j => iI j.castSucc
        let iItD : ∀ j : Fin (n + 2), DecidableEq ((fun t : Fin (n + 2) => I t.castSucc) j) :=
          fun j => iId j.castSucc
        let iOt : ∀ j : Fin (n + 2), Fintype ((fun t : Fin (n + 2) => O t.castSucc) j) :=
          fun j => iO j.castSucc
        let iOtD : ∀ j : Fin (n + 2), DecidableEq ((fun t : Fin (n + 2) => O t.castSucc) j) :=
          fun j => iOd j.castSucc
        have hIH : Normalized
            (fun j : Fin (n - m + 1) => (fun t : Fin (n + 2) => I t.castSucc)
              (compInS (n := n) k m hkm' j))
            (fun j : Fin (n - m + 1) => (fun t : Fin (n + 2) => O t.castSucc)
              (compOutS (n := n) k m hkm' j))
            (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
              (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X) :=
          @ih n (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)
            iIt iItD iOt iOtD k m hkm' hT' K hK X hX
        have hBridge : Normalized
            (fun j : Fin (n + 1 - m) => I (compInS (n := n + 1) k m hkm j.castSucc))
            (fun j : Fin (n + 1 - m) => O (compOutS (n := n + 1) k m hkm j.castSucc))
            (WireFam.matReindex (famTailEquiv (I := I) (O := O) k m hkm hkm')
              (suffixCompS (n := n) (I := fun t : Fin (n + 2) => I t.castSucc)
                (O := fun t : Fin (n + 2) => O t.castSucc) k m hkm' K X)) :=
          normalized_castIdx (n - m + 1) (n + 1 - m) (by omega)
            (fun j : Fin (n - m + 1) =>
              famTailEqI (I := I) (n := n) k m hkm hkm' ⟨(j : Nat), by omega⟩)
            (fun j : Fin (n - m + 1) =>
              famTailEqO (O := O) (n := n) k m hkm hkm' ⟨(j : Nat), by omega⟩)
            _ hIH
        exact normalized_succ_of_trunc (n := n) (I := I) (O := O) k m hkm hkm' hk J K hpeel
          hJpos X (Normalized.posSemidef hX) hBridge
    · -- tight: the window ends at the last tooth
      rcases n with _ | n
      · -- degenerate two-wire comb: the window covers everything
        obtain ⟨rfl, rfl⟩ : k = 0 ∧ m = 0 := by omega
        exact hBase I O hkm J hJ X hX
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · -- tight m = 0: the boundary chain closes directly
          rcases hJ with ⟨hJpos, K, hK, hpeel⟩
          exact normalized_m0_succ (n := n) (I := I) (O := O) k hkm (by omega) J K hJpos hpeel
            hK X (Normalized.posSemidef hX) hX
        · -- tight m ≥ 1: shorten the window through its own normalization
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rcases hJ with ⟨hJpos, K, hK, hpeel⟩
          rcases hX with ⟨hXpos, XW, hXW, hpeelX⟩
          have hkb : k + (m' + 1) + 1 = n + 2 := by omega
          have hkm0 : k + m' + 1 ≤ n + 1 := by omega
          have hT' : n + 1 - (k + m' + 1) + m' < T := by omega
          let iIt : ∀ j : Fin (n + 2), Fintype ((fun t : Fin (n + 2) => I t.castSucc) j) :=
            fun j => iI j.castSucc
          let iItD : ∀ j : Fin (n + 2), DecidableEq ((fun t : Fin (n + 2) => I t.castSucc) j) :=
            fun j => iId j.castSucc
          let iOt : ∀ j : Fin (n + 2), Fintype ((fun t : Fin (n + 2) => O t.castSucc) j) :=
            fun j => iO j.castSucc
          let iOtD : ∀ j : Fin (n + 2), DecidableEq ((fun t : Fin (n + 2) => O t.castSucc) j) :=
            fun j => iOd j.castSucc
          exact normalized_bnd_succ (n := n) (I := I) (O := O) k m' hkm hkb hkm0 J K hpeel hJpos
            X hXpos XW hpeelX
            (@ih n (fun t : Fin (n + 2) => I t.castSucc) (fun t : Fin (n + 2) => O t.castSucc)
              iIt iItD iOt iOtD k m' hkm0 hT' K hK XW hXW)

/-! ### Degenerate base case: depth-zero evaluations -/

section Base00

variable (I O : Fin (0 + 2) → Type u)
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the degenerate depth-zero suffix match, the flat position `0` is the
first private (composite input) position of the complement enumeration. -/
private theorem base_complEmb_zero (hkm : 0 + 0 + 1 ≤ 0 + 1) :
    complEmb (suffixConnIdx (n := 0) 0 0 hkm)
        (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).hι₂ ⟨0, by omega⟩
      = (⟨0, by omega⟩ : Fin (0 + 2 + (0 + 2))) := by
  rw [suffixComplEmb 0 0 hkm
    (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).hι₂ ⟨0, by omega⟩]
  rw [suffixComplIdx_of_lt_le 0 0 hkm ⟨0, by omega⟩ (by decide) (by decide)]
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Flat-position form of the window input readback: the transparent cast
along the connected type equality is the identity. -/
private theorem base_eRelabel_inW (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (z : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q) :
    (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).eRelabel z
        (Fin.natAdd (0 + 1) (Fin.last 0))
      = z (Fin.natAdd (0 + 1) (Fin.last 0)) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Flat-position form of the window output readback: the transparent cast
along the connected type equality is the identity. -/
private theorem base_eRelabel_outW (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (z : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q) :
    (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).eRelabel z
        (Fin.castAdd (0 + 1) (Fin.last 0))
      = z (Fin.castAdd (0 + 1) (Fin.last 0)) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate readback at the window input position: the value is the
relabeled connected window input entry. -/
private theorem base_read₂_inW (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (z : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (w : ∀ j, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).complFam₂ j) :
    (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ z w
        (suffixConnIdx (n := 0) 0 0 hkm (Fin.natAdd (0 + 1) (Fin.last 0)))
      = (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).eRelabel z
          (Fin.natAdd (0 + 1) (Fin.last 0)) :=
  WireMatch.read₂_conn (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm) z w
    (Fin.natAdd (0 + 1) (Fin.last 0))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate readback at the window output position: the value is the
relabeled connected window output entry. -/
private theorem base_read₂_outW (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (z : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (w : ∀ j, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).complFam₂ j) :
    (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ z w
        (suffixConnIdx (n := 0) 0 0 hkm (Fin.castAdd (0 + 1) (Fin.last 0)))
      = (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).eRelabel z
          (Fin.castAdd (0 + 1) (Fin.last 0)) :=
  WireMatch.read₂_conn (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm) z w
    (Fin.castAdd (0 + 1) (Fin.last 0))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate flattening at the window output position: reading a flattened
window configuration at the window output position gives the window output
component. -/
private theorem base_XFlat_outW (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (P : Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)) :
    (XFlatEquiv (I := I) (O := O) 0 0 hkm) P (Fin.castAdd (0 + 1) (Fin.last 0))
      = P.1 (Fin.last 0) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate flattening at the window input position: reading a flattened
window configuration at the window input position gives the window input
component. -/
private theorem base_XFlat_inW (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (P : Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)) :
    (XFlatEquiv (I := I) (O := O) 0 0 hkm) P (Fin.natAdd (0 + 1) (Fin.last 0))
      = P.2 (Fin.last 0) := rfl
/-- The flattened outer configuration induced by a connected configuration and
a packed composite configuration, at the degenerate depth. -/
private noncomputable def baseRow (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (u : ∀ j : Fin (0 + 1), I (compIn (n := 0) 0 0 j))
    (v : ∀ j : Fin (0 + 1), O (compOut (n := 0) 0 0 j)) : Space I O :=
  splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ zz
    (complPack (I := I) (O := O) 0 0 hkm u v))

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate row readback at the private composite input slot: the value is
the packed composite input entry, read through the region equation. -/
private theorem baseRow_fst_zero (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (u : ∀ j : Fin (0 + 1), I (compIn (n := 0) 0 0 j))
    (v : ∀ j : Fin (0 + 1), O (compOut (n := 0) 0 0 j)) :
    (baseRow (I := I) (O := O) hkm zz u v).1 (⟨0, by omega⟩ : Fin (0 + 2))
      = u ⟨0, by omega⟩ := by
  show cast (append_castAdd I O (⟨0, by omega⟩ : Fin (0 + 2)))
      ((suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ zz
        (complPack (I := I) (O := O) 0 0 hkm u v)
        (Fin.castAdd (0 + 2) (⟨0, by omega⟩ : Fin (0 + 2)))) = _
  have hpos : complEmb (suffixConnIdx (n := 0) 0 0 hkm)
      (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).hι₂ ⟨0, by omega⟩
      = Fin.castAdd (0 + 2) (⟨0, by omega⟩ : Fin (0 + 2)) := by
    rw [base_complEmb_zero I O hkm]
    rfl
  have hc1 := read₂_congr_pos (I := I) (O := O) (n := 0) 0 0 hkm zz
    (complPack (I := I) (O := O) 0 0 hkm u v) hpos
  have hlt : (0 : Nat) < 0 + 1 - 0 := by decide
  refine Eq.trans (congrArg (cast (append_castAdd I O (⟨0, by omega⟩ : Fin (0 + 2)))) hc1.symm) ?_
  rw [suffixRead₂_compl (I := I) (O := O) (n := 0) 0 0 hkm zz
      (complPack (I := I) (O := O) 0 0 hkm u v) ⟨0, by omega⟩,
    complPack_lt (I := I) (O := O) 0 0 hkm u v ⟨0, by omega⟩ hlt]
  exact (cast3 ((complFam₂_eq_lt (I := I) (O := O) 0 0 hkm ⟨0, by omega⟩
      hlt).symm)
    (congrArg (append I O) hpos) (append_castAdd I O (⟨0, by omega⟩ : Fin (0 + 2)))
    (u ⟨0, by omega⟩)).trans rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate row readback at the window input slot: the value is the
connected window input entry. -/
private theorem baseRow_fst_last (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (u : ∀ j : Fin (0 + 1), I (compIn (n := 0) 0 0 j))
    (v : ∀ j : Fin (0 + 1), O (compOut (n := 0) 0 0 j)) :
    (baseRow (I := I) (O := O) hkm zz u v).1 (Fin.last (0 + 1))
      = zz (Fin.natAdd (0 + 1) (Fin.last 0)) := by
  show (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ zz
        (complPack (I := I) (O := O) 0 0 hkm u v))).1 (Fin.last (0 + 1)) = _
  rw [splitAppendEquiv_apply]
  show cast (append_castAdd I O (Fin.last (0 + 1)))
      ((suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ zz
        (complPack (I := I) (O := O) 0 0 hkm u v)
        (suffixConnIdx (n := 0) 0 0 hkm (Fin.natAdd (0 + 1) (Fin.last 0)))) = _
  rw [base_read₂_inW I O hkm zz (complPack (I := I) (O := O) 0 0 hkm u v),
    base_eRelabel_inW I O hkm zz]
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate row readback at the window output slot: the value is the
connected window output entry. -/
private theorem baseRow_snd_zero (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (u : ∀ j : Fin (0 + 1), I (compIn (n := 0) 0 0 j))
    (v : ∀ j : Fin (0 + 1), O (compOut (n := 0) 0 0 j)) :
    (baseRow (I := I) (O := O) hkm zz u v).2 (⟨0, by omega⟩ : Fin (0 + 2))
      = zz (Fin.castAdd (0 + 1) (Fin.last 0)) := by
  show (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ zz
        (complPack (I := I) (O := O) 0 0 hkm u v))).2 (⟨0, by omega⟩ : Fin (0 + 2)) = _
  rw [splitAppendEquiv_apply]
  show cast (append_natAdd I O (⟨0, by omega⟩ : Fin (0 + 2)))
      ((suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ zz
        (complPack (I := I) (O := O) 0 0 hkm u v)
        (suffixConnIdx (n := 0) 0 0 hkm (Fin.castAdd (0 + 1) (Fin.last 0)))) = _
  rw [base_read₂_outW I O hkm zz (complPack (I := I) (O := O) 0 0 hkm u v),
    base_eRelabel_outW I O hkm zz]
  rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate row readback at the pending composite output slot: the value is
the transported pending output entry. -/
private theorem baseRow_snd_last (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (u : ∀ j : Fin (0 + 1), I (compIn (n := 0) 0 0 j))
    (o : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc))
    (z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0)))) :
    (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z)).2
        (Fin.last (0 + 1))
      = cast (congrArg O (compOut_last (n := 0) 0 0 hkm)) z := by
  have h := splitRead₂_snoc_eq (I := I) (O := O) (n := 0) 0 0 hkm zz u o z
  have h2 := congrArg (fun p : Space I O => p.2 (Fin.last (0 + 1))) h
  show (splitAppendEquiv I O ((suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).read₂ zz
        (complPack (I := I) (O := O) 0 0 hkm u
          (snocP (O := O) (n := 0) 0 0 hkm o z)))).2 (Fin.last (0 + 1)) = _
  simpa only [Fin.snoc_last] using h2

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Row stability in the pending output value at the degenerate depth: the
flattened configuration induced by a snoc-packed composite output equals the
snoc of the fixed row's components and the transported final value, so every
component except the final slot is independent of the pending value. -/
private theorem base_row_eq (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (u : ∀ j : Fin (0 + 1), I (compIn (n := 0) 0 0 j))
    (o : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc))
    (z z₀ : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0)))) :
    baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z)
      = ((baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1,
        Fin.snoc (α := fun t : Fin (0 + 2) => O t)
          (fun t : Fin (0 + 1) =>
            (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2
              t.castSucc)
          (cast (congrArg O (compOut_last (n := 0) 0 0 hkm)) z)) := by
  refine Prod.ext ?_ ?_
  · funext j
    rcases j.eq_castSucc_or_eq_last with ⟨j₀, rfl⟩ | rfl
    · obtain rfl : j₀ = ⟨0, by omega⟩ := Fin.ext (by have := j₀.isLt; omega)
      show (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z)).1
          (⟨0, by omega⟩ : Fin (0 + 2))
        = (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1
            (⟨0, by omega⟩ : Fin (0 + 2))
      rw [baseRow_fst_zero I O hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z),
        baseRow_fst_zero I O hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)]
    · show (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z)).1
          (Fin.last (0 + 1))
        = (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1
            (Fin.last (0 + 1))
      rw [baseRow_fst_last I O hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z),
        baseRow_fst_last I O hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)]
  · funext t
    rcases t.eq_castSucc_or_eq_last with ⟨t₀, rfl⟩ | rfl
    · obtain rfl : t₀ = ⟨0, by omega⟩ := Fin.ext (by have := t₀.isLt; omega)
      show (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z)).2
          (⟨0, by omega⟩ : Fin (0 + 2))
        = (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2
            (⟨0, by omega⟩ : Fin (0 + 2))
      rw [baseRow_snd_zero I O hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z),
        baseRow_snd_zero I O hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z₀)]
    · show (baseRow (I := I) (O := O) hkm zz u (snocP (O := O) (n := 0) 0 0 hkm o z)).2
          (Fin.last (0 + 1))
        = cast (congrArg O (compOut_last (n := 0) 0 0 hkm)) z
      exact baseRow_snd_last I O hkm zz u o z
/-- Successor-point input component at the degenerate depth: the packed
composite input family induced by the successor-form point. -/
private def basePeelU (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (i : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j)) :
    ∀ j : Fin (0 + 1), I (compIn (n := 0) 0 0 j) :=
  fun j => i ((compIdxEquiv (n := 0) 0 0 hkm).symm j)

set_option maxHeartbeats 1200000 in
omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- Entrywise expansion of the degenerate composite at snoc-shaped points: the
entry is the window contraction with the private configuration induced by the
transported successor point. -/
private theorem base_expand (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)))
    (i i' : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j))
    (o o' : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc)) :
    (∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
        suffixCompS (I := I) (O := O) (n := 0) 0 0 hkm J X (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = ∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
        ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz) *
          J (baseRow (I := I) (O := O) hkm zz' (basePeelU (I := I) hkm i)
              (snocP (O := O) (n := 0) 0 0 hkm o z))
            (baseRow (I := I) (O := O) hkm zz (basePeelU (I := I) hkm i')
              (snocP (O := O) (n := 0) 0 0 hkm o' z)) := by
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (suffixCompS_entry_snoc (I := I) (O := O) (n := 0) 0 0 hkm J X i i' o o' z).trans
    (Finset.sum_congr rfl fun zz _ => Finset.sum_congr rfl fun zz' _ => rfl)

omit [∀ j, Fintype (I j)] in
/-- Inner degenerate sum: summing the composite's outer-matrix entries over
the last output value applies the outer comb's normalization peel, with the
condition transferred to the connected configurations' last input-side
entries (the window's top output wire is the outer last input). -/
private theorem base_inner (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (0 + 1) => I j.castSucc)
      (fun j : Fin (0 + 1) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (0 + 1), O j.castSucc),
      (∑ z : O (Fin.last (0 + 1)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (0 + 1)) = ii' (Fin.last (0 + 1)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (zc zc' : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q)
    (i i' : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j))
    (o o' : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0)))) :
    (∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
        J (baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
            (snocP (O := O) (n := 0) 0 0 hkm o z))
          (baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
            (snocP (O := O) (n := 0) 0 0 hkm o' z)))
      = if zc' (Fin.natAdd (0 + 1) (Fin.last 0)) = zc (Fin.natAdd (0 + 1) (Fin.last 0)) then
          K ((fun j => (baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
                  (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
            fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
              (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
          ((fun j => (baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
                  (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
            fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
              (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
          else 0 := by
  have hs1 : (∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
          J (baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
              (snocP (O := O) (n := 0) 0 0 hkm o z))
            (baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
              (snocP (O := O) (n := 0) 0 0 hkm o' z)))
        = ∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
            J ((baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
                  (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (0 + 2) => O t)
                (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc'
                    (basePeelU (I := I) hkm i) (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := 0) 0 0 hkm)) z))
            ((baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
                  (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (0 + 2) => O t)
                (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc
                    (basePeelU (I := I) hkm i') (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := 0) 0 0 hkm)) z)) :=
    Finset.sum_congr rfl fun z _ => congrArg₂ J
      (base_row_eq I O hkm zc' (basePeelU (I := I) hkm i) o z z₀)
      (base_row_eq I O hkm zc (basePeelU (I := I) hkm i') o' z z₀)
  have hs2 : (∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
            J ((baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
                  (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (0 + 2) => O t)
                (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc'
                    (basePeelU (I := I) hkm i) (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := 0) 0 0 hkm)) z))
            ((baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
                  (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (0 + 2) => O t)
                (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc
                    (basePeelU (I := I) hkm i') (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
                (cast (congrArg O (compOut_last (n := 0) 0 0 hkm)) z)))
        = ∑ y : O (Fin.last (0 + 1)),
            J ((baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
                  (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1,
              Fin.snoc (α := fun t : Fin (0 + 2) => O t)
                (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc'
                    (basePeelU (I := I) hkm i) (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc) y)
            ((baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
                  (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1,
              Fin.snoc (α := fun t : Fin (0 + 2) => O t)
                (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc
                    (basePeelU (I := I) hkm i') (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc) y) :=
    sum_cast_equiv (congrArg O (compOutS_last (n := 0) 0 0 hkm))
      (fun y => J ((baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
              (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1,
            Fin.snoc (α := fun t : Fin (0 + 2) => O t)
              (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc'
                  (basePeelU (I := I) hkm i) (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc) y)
          ((baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
              (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1,
            Fin.snoc (α := fun t : Fin (0 + 2) => O t)
              (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc
                  (basePeelU (I := I) hkm i') (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc) y))
  have hp := hpeel ((baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
        (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1)
      ((baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
        (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1)
      (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc' (basePeelU (I := I) hkm i)
        (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
      (fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zc (basePeelU (I := I) hkm i')
        (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
  refine (hs1.trans hs2).trans ?_
  rw [hp]
  rw [baseRow_fst_last I O hkm zc' (basePeelU (I := I) hkm i)
      (snocP (O := O) (n := 0) 0 0 hkm o z₀),
    baseRow_fst_last I O hkm zc (basePeelU (I := I) hkm i')
      (snocP (O := O) (n := 0) 0 0 hkm o' z₀)]
  rfl

/-- Degenerate sum rearrangement: pulling the last-output sum inside the
window contraction and applying the outer peel per connected configuration. -/
private theorem base_swap (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (0 + 1) => I j.castSucc)
      (fun j : Fin (0 + 1) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (0 + 1), O j.castSucc),
      (∑ z : O (Fin.last (0 + 1)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (0 + 1)) = ii' (Fin.last (0 + 1)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)))
    (i i' : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j))
    (o o' : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0)))) :
    (∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
        ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz) *
          J (baseRow (I := I) (O := O) hkm zz' (basePeelU (I := I) hkm i)
              (snocP (O := O) (n := 0) 0 0 hkm o z))
            (baseRow (I := I) (O := O) hkm zz (basePeelU (I := I) hkm i')
              (snocP (O := O) (n := 0) 0 0 hkm o' z)))
      = ∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz) *
          (if zz' (Fin.natAdd (0 + 1) (Fin.last 0)) = zz (Fin.natAdd (0 + 1) (Fin.last 0)) then
            K ((fun j => (baseRow (I := I) (O := O) hkm zz' (basePeelU (I := I) hkm i)
                    (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zz' (basePeelU (I := I) hkm i)
                (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (baseRow (I := I) (O := O) hkm zz (basePeelU (I := I) hkm i')
                    (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zz (basePeelU (I := I) hkm i')
                (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
          else 0) := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun zz _ =>
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun zz' _ => ?_)))
  refine (Finset.mul_sum _ _ _).symm.trans ?_
  exact congrArg _ (base_inner I O hkm J K hpeel zz zz' i i' o o' z₀)
/-- Boundary split at the degenerate depth: reindexing the connected window
configurations of the swapped boundary equation by the flattening equivalence
and splitting each window block at its last wire exhibits the shared-trace
structure — the outer peel's condition becomes equality of the row and column
pending input values; the truncated blocks are empty. -/
private theorem base_split (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (K : CMatrix (Space (fun j : Fin (0 + 1) => I j.castSucc)
      (fun j : Fin (0 + 1) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)))
    (i i' : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j))
    (o o' : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0)))) :
    (∑ zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
        ∑ zz' : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q,
          X ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz')
              ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz) *
          (if zz' (Fin.natAdd (0 + 1) (Fin.last 0)) = zz (Fin.natAdd (0 + 1) (Fin.last 0)) then
            K ((fun j => (baseRow (I := I) (O := O) hkm zz' (basePeelU (I := I) hkm i)
                    (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zz'
                (basePeelU (I := I) hkm i)
                (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (baseRow (I := I) (O := O) hkm zz (basePeelU (I := I) hkm i')
                    (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zz
                (basePeelU (I := I) hkm i')
                (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
          else 0))
      = ∑ zcO : ∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc,
        ∑ wO : suffixOut O 0 0 hkm (Fin.last 0),
        ∑ zcI : ∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc,
        ∑ wO' : suffixOut O 0 0 hkm (Fin.last 0),
        ∑ zcI' : ∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc,
        ∑ wI : suffixIn I 0 0 hkm (Fin.last 0),
        ∑ wI' : suffixIn I 0 0 hkm (Fin.last 0),
          X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (basePeelU (I := I) hkm i)
                    (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (basePeelU (I := I) hkm i)
                (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (basePeelU (I := I) hkm i')
                    (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (basePeelU (I := I) hkm i')
                (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
          else 0) := by
  refine Eq.trans (sum_reindex_two (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm)
    (fun (zz' zz : ∀ q, (suffixMatch (I := I) (O := O) (n := 0) 0 0 hkm).connFam₁ q) =>
      X ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz')
          ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm).symm zz) *
        (if zz' (Fin.natAdd (0 + 1) (Fin.last 0)) = zz (Fin.natAdd (0 + 1) (Fin.last 0)) then
          K ((fun j => (baseRow (I := I) (O := O) hkm zz' (basePeelU (I := I) hkm i)
                  (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
            fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zz'
              (basePeelU (I := I) hkm i)
              (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
          ((fun j => (baseRow (I := I) (O := O) hkm zz (basePeelU (I := I) hkm i')
                  (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
            fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm zz
              (basePeelU (I := I) hkm i')
              (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
        else 0))) ?_
  simp only [Equiv.symm_apply_apply]
  rw [sum_space_snoc2]
  have hpt : ∀ (zcO : ∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc)
      (wO : suffixOut O 0 0 hkm (Fin.last 0))
      (zcI : ∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc)
      (wI : suffixIn I 0 0 hkm (Fin.last 0))
      (zcO' : ∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc)
      (wO' : suffixOut O 0 0 hkm (Fin.last 0))
      (zcI' : ∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc)
      (wI' : suffixIn I 0 0 hkm (Fin.last 0)),
      X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                (Fin.snoc zcO' wO', Fin.snoc zcI' wI')) (Fin.natAdd (0 + 1) (Fin.last 0))
              = (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI)) (Fin.natAdd (0 + 1) (Fin.last 0)) then
            K ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (basePeelU (I := I) hkm i)
                    (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (basePeelU (I := I) hkm i)
                (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (basePeelU (I := I) hkm i')
                    (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (basePeelU (I := I) hkm i')
                (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
          else 0)
        = X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (basePeelU (I := I) hkm i)
                    (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (basePeelU (I := I) hkm i)
                (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (basePeelU (I := I) hkm i')
                    (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (basePeelU (I := I) hkm i')
                (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
          else 0) := by
    intro zcO wO zcI wI zcO' wO' zcI' wI'
    have h1 : (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
          (Fin.snoc zcO' wO', Fin.snoc zcI' wI')) (Fin.natAdd (0 + 1) (Fin.last 0))
          = wI' := by
      rw [base_XFlat_inW I O hkm (Fin.snoc zcO' wO', Fin.snoc zcI' wI')]
      rfl
    have h2 : (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
          (Fin.snoc zcO wO, Fin.snoc zcI wI)) (Fin.natAdd (0 + 1) (Fin.last 0))
          = wI := by
      rw [base_XFlat_inW I O hkm (Fin.snoc zcO wO, Fin.snoc zcI wI)]
      rfl
    by_cases hcc : wI' = wI
    · subst hcc
      rw [ite_eq_left (by rw [h1, h2]), ite_eq_left rfl]
    · rw [ite_eq_right (fun heq => hcc (h1.symm.trans (heq.trans h2))), ite_eq_right hcc]
  exact Finset.sum_congr rfl fun zcO _ => Finset.sum_congr rfl fun wO _ =>
    Finset.sum_congr rfl fun zcI _ => Finset.sum_congr rfl fun zcO' _ =>
      Finset.sum_congr rfl fun wO' _ => Finset.sum_congr rfl fun zcI' _ =>
        Finset.sum_congr rfl fun wI _ => Finset.sum_congr rfl fun wI' _ =>
          hpt zcO wO zcI wI zcO' wO' zcI' wI'

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Degenerate composite input index equation: at depth zero every composite
input slot is the single private input wire. -/
private theorem base_compInS_castSucc (hkm : 0 + 0 + 1 ≤ 0 + 1) (j : Fin (0 + 1)) :
    compInS (n := 0) 0 0 hkm j = j.castSucc := by
  obtain rfl : j = ⟨0, by omega⟩ := Fin.ext (by have := j.isLt; omega)
  rfl

/-- Boundary collapse at the degenerate depth: the inner window being an
identity on its single pending wire, the split boundary equation collapses to
the trace form of the outer witness — a single sum over the shared window
output value, with row and column arguments folded to the composite
configuration. -/
private theorem base_collapse (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (K : CMatrix (Space (fun j : Fin (0 + 1) => I j.castSucc)
      (fun j : Fin (0 + 1) => O j.castSucc)))
    (X : CMatrix (Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)))
    (hX : Normalized (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm) X)
    (i i' : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j))
    (o o' : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc))
    (z₀ : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0)))) :
    (∑ zcO : ∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc,
        ∑ wO : suffixOut O 0 0 hkm (Fin.last 0),
        ∑ zcI : ∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc,
        ∑ zcO' : ∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc,
        ∑ wO' : suffixOut O 0 0 hkm (Fin.last 0),
        ∑ zcI' : ∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc,
        ∑ wI : suffixIn I 0 0 hkm (Fin.last 0),
        ∑ wI' : suffixIn I 0 0 hkm (Fin.last 0),
          X (Fin.snoc zcO' wO', Fin.snoc zcI' wI') (Fin.snoc zcO wO, Fin.snoc zcI wI) *
          (if wI' = wI then
            K ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                    (basePeelU (I := I) hkm i)
                    (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO' wO', Fin.snoc zcI' wI'))
                (basePeelU (I := I) hkm i)
                (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
            ((fun j => (baseRow (I := I) (O := O) hkm
                    (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                      (Fin.snoc zcO wO, Fin.snoc zcI wI))
                    (basePeelU (I := I) hkm i')
                    (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
              fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
                (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                  (Fin.snoc zcO wO, Fin.snoc zcI wI))
                (basePeelU (I := I) hkm i')
                (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
          else 0))
      = ∑ wO : suffixOut O 0 0 hkm (Fin.last 0),
          K ((fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i j)),
            Fin.snoc (α := fun t : Fin (0 + 1) => O t.castSucc)
              (fun t : Fin 0 => Fin.elim0 t) wO)
          ((fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i' j)),
            Fin.snoc (α := fun t : Fin (0 + 1) => O t.castSucc)
              (fun t : Fin 0 => Fin.elim0 t) wO) := by
  rcases hX with ⟨-, XW, hXW, hpeelX⟩
  have hXWeq : XW = 1 := (normalized_zero _ _ XW).mp hXW
  have eO : ∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc := fun j => Fin.elim0 j
  have eI : ∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc := fun j => Fin.elim0 j
  have hpm : ∀ (wO wO' : suffixOut O 0 0 hkm (Fin.last 0)) (c : ℂ),
      (∑ wI : suffixIn I 0 0 hkm (Fin.last 0),
          X (Fin.snoc eO wO', Fin.snoc eI wI)
              (Fin.snoc eO wO, Fin.snoc eI wI) * c) =
        if wO' = wO then 1 * c else 0 := by
    intro wO wO' c
    have hf : (∑ wI : suffixIn I 0 0 hkm (Fin.last 0),
          X (Fin.snoc eO wO', Fin.snoc eI wI)
              (Fin.snoc eO wO, Fin.snoc eI wI)) * c =
        ∑ wI : suffixIn I 0 0 hkm (Fin.last 0),
          X (Fin.snoc eO wO', Fin.snoc eI wI)
              (Fin.snoc eO wO, Fin.snoc eI wI) * c :=
      Finset.sum_mul Finset.univ _ _
    rw [← hf, hpeelX (Fin.snoc eO wO') (Fin.snoc eO wO) eI eI,
      ite_mul, zero_mul, hXWeq]
    simp only [Fin.snoc_last, Matrix.one_apply]
    by_cases hw : wO' = wO
    · subst hw
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right hw, ite_eq_right hw]
  have hrow : ∀ (wO' : suffixOut O 0 0 hkm (Fin.last 0))
      (wI : suffixIn I 0 0 hkm (Fin.last 0)),
      ((fun j : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
              (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                (Fin.snoc eO wO', Fin.snoc eI wI))
              (basePeelU (I := I) hkm i)
              (snocP (O := O) (n := 0) 0 0 hkm o z₀)).1 j.castSucc),
        fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
            (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
              (Fin.snoc eO wO', Fin.snoc eI wI))
            (basePeelU (I := I) hkm i)
            (snocP (O := O) (n := 0) 0 0 hkm o z₀)).2 t.castSucc)
      = ((fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i j)),
        Fin.snoc (α := fun t : Fin (0 + 1) => O t.castSucc)
          (fun t : Fin 0 => Fin.elim0 t) wO') := by
    intro wO' wI
    refine Prod.ext ?_ ?_
    · funext j
      obtain rfl : j = ⟨0, by omega⟩ := Fin.ext (by have := j.isLt; omega)
      show (baseRow (I := I) (O := O) hkm _ (basePeelU (I := I) hkm i) _).1
          (⟨0, by omega⟩ : Fin (0 + 2)) = _
      rw [baseRow_fst_zero I O hkm
          ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm)
            (Fin.snoc eO wO', Fin.snoc eI wI))
          (basePeelU (I := I) hkm i)
          (snocP (O := O) (n := 0) 0 0 hkm o z₀)]
      rfl
    · funext t
      obtain rfl : t = ⟨0, by omega⟩ := Fin.ext (by have := t.isLt; omega)
      show (baseRow (I := I) (O := O) hkm _ (basePeelU (I := I) hkm i) _).2
          (⟨0, by omega⟩ : Fin (0 + 2)) = _
      rw [baseRow_snd_zero I O hkm
          ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm)
            (Fin.snoc eO wO', Fin.snoc eI wI))
          (basePeelU (I := I) hkm i)
          (snocP (O := O) (n := 0) 0 0 hkm o z₀),
        base_XFlat_outW I O hkm (Fin.snoc eO wO', Fin.snoc eI wI)]
      rfl
  have hcol : ∀ (wO : suffixOut O 0 0 hkm (Fin.last 0))
      (wI : suffixIn I 0 0 hkm (Fin.last 0)),
      ((fun j : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
              (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
                (Fin.snoc eO wO, Fin.snoc eI wI))
              (basePeelU (I := I) hkm i')
              (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).1 j.castSucc),
        fun t : Fin (0 + 1) => (baseRow (I := I) (O := O) hkm
            (XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm
              (Fin.snoc eO wO, Fin.snoc eI wI))
            (basePeelU (I := I) hkm i')
            (snocP (O := O) (n := 0) 0 0 hkm o' z₀)).2 t.castSucc)
      = ((fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i' j)),
        Fin.snoc (α := fun t : Fin (0 + 1) => O t.castSucc)
          (fun t : Fin 0 => Fin.elim0 t) wO) := by
    intro wO wI
    refine Prod.ext ?_ ?_
    · funext j
      obtain rfl : j = ⟨0, by omega⟩ := Fin.ext (by have := j.isLt; omega)
      show (baseRow (I := I) (O := O) hkm _ (basePeelU (I := I) hkm i') _).1
          (⟨0, by omega⟩ : Fin (0 + 2)) = _
      rw [baseRow_fst_zero I O hkm
          ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm)
            (Fin.snoc eO wO, Fin.snoc eI wI))
          (basePeelU (I := I) hkm i')
          (snocP (O := O) (n := 0) 0 0 hkm o' z₀)]
      rfl
    · funext t
      obtain rfl : t = ⟨0, by omega⟩ := Fin.ext (by have := t.isLt; omega)
      show (baseRow (I := I) (O := O) hkm _ (basePeelU (I := I) hkm i') _).2
          (⟨0, by omega⟩ : Fin (0 + 2)) = _
      rw [baseRow_snd_zero I O hkm
          ((XFlatEquiv (I := I) (O := O) (n := 0) 0 0 hkm)
            (Fin.snoc eO wO, Fin.snoc eI wI))
          (basePeelU (I := I) hkm i')
          (snocP (O := O) (n := 0) 0 0 hkm o' z₀),
        base_XFlat_outW I O hkm (Fin.snoc eO wO, Fin.snoc eI wI)]
      rfl
  have hzO : ∀ f : (∀ j : Fin 0, suffixOut O 0 0 hkm j.castSucc) → ℂ,
      ∑ x, f x = f eO := fun f => sum_pi_fin0 f eO
  have hzI : ∀ f : (∀ j : Fin 0, suffixIn I 0 0 hkm j.castSucc) → ℂ,
      ∑ x, f x = f eI := fun f => sum_pi_fin0 f eI
  simp only [hzO, hzI]
  simp only [hrow, hcol]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hpm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul]

/-- Boundary peel at the degenerate depth: summing the composite over its
single pending output value and contracting through the boundary chain
leaves the scalar identity witness, with the peel condition transported
across the boundary index spellings, including an empty pending output. -/
private theorem base_peel (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (J : CMatrix (Space I O))
    (K : CMatrix (Space (fun j : Fin (0 + 1) => I j.castSucc)
      (fun j : Fin (0 + 1) => O j.castSucc)))
    (hpeel : ∀ (ii ii' : ∀ j, I j) (oo oo' : ∀ j : Fin (0 + 1), O j.castSucc),
      (∑ z : O (Fin.last (0 + 1)), J (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last (0 + 1)) = ii' (Fin.last (0 + 1)) then
          K ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (X : CMatrix (Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)))
    (hX : Normalized (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm) X)
    (KW : CMatrix (Space (fun j : Fin 0 => I (Fin.castSucc (Fin.castSucc j)))
      (fun j : Fin 0 => O (Fin.castSucc (Fin.castSucc j)))))
    (hKWeq : KW = 1)
    (hpeelK : ∀ (ii ii' : ∀ j : Fin (0 + 1), I (Fin.castSucc j))
      (oo oo' : ∀ j : Fin 0, O (Fin.castSucc (Fin.castSucc j))),
      (∑ z : O (Fin.castSucc (Fin.last 0)),
          K (ii, Fin.snoc oo z) (ii', Fin.snoc oo' z)) =
        if ii (Fin.last 0) = ii' (Fin.last 0) then
          KW ((fun j => ii j.castSucc), oo) ((fun j => ii' j.castSucc), oo') else 0)
    (i i' : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j))
    (o o' : ∀ j : Fin (0 - 0), O (compOutS (n := 0) 0 0 hkm j.castSucc)) :
    (∑ z : O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0))),
        suffixCompS (I := I) (O := O) (n := 0) 0 0 hkm J X
          (i, Fin.snoc o z) (i', Fin.snoc o' z))
      = if i (Fin.last (0 - 0)) = i' (Fin.last (0 - 0)) then
          (1 : CMatrix (Space (fun j : Fin 0 => I (compInS (n := 0) 0 0 hkm j.castSucc))
            (fun j : Fin 0 => O (compOutS (n := 0) 0 0 hkm j.castSucc))))
            ((fun j : Fin (0 - 0) => i j.castSucc), o)
            ((fun j : Fin (0 - 0) => i' j.castSucc), o')
        else 0 := by
  classical
  trans (∑ z : O (Fin.castSucc (Fin.last 0)),
        K ((fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i j)),
          Fin.snoc (fun t : Fin 0 => Fin.elim0 t) z)
        ((fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i' j)),
          Fin.snoc (fun t : Fin 0 => Fin.elim0 t) z))
  · rcases isEmpty_or_nonempty
        (O (compOutS (n := 0) 0 0 hkm (Fin.last (0 - 0)))) with hE | hNE
    · have hEO : IsEmpty (O (Fin.last 1)) :=
        congrArg O (compOutS_last (n := 0) 0 0 hkm) ▸ hE
      refine (Finset.sum_eq_zero (fun z _ => hE.elim z)).trans ?_
      symm
      refine Finset.sum_eq_zero fun wO _ => ?_
      obtain ⟨wI⟩ := normalized_one_output_nonempty hX wO
      exact peel_zero_of_empty_output J K hpeel hEO wI _ _
    · obtain ⟨z₀⟩ := hNE
      refine Eq.trans (base_expand I O hkm J X i i' o o') ?_
      refine Eq.trans (base_swap I O hkm J K hpeel X i i' o o' z₀) ?_
      refine Eq.trans (base_split I O hkm K X i i' o o' z₀) ?_
      exact base_collapse I O hkm K X hX i i' o o' z₀
  ·
    rw [hpeelK (fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i j))
      (fun j : Fin (0 + 1) => cast (congrArg I (base_compInS_castSucc hkm j)) (i' j))
      (fun t : Fin 0 => Fin.elim0 t) (fun t : Fin 0 => Fin.elim0 t)]
    have hcI : ∀ (iv iv' : ∀ j : Fin (0 - 0 + 1), I (compInS (n := 0) 0 0 hkm j)),
        cast (congrArg I (base_compInS_castSucc hkm (Fin.last 0))) (iv (Fin.last 0))
          = cast (congrArg I (base_compInS_castSucc hkm (Fin.last 0))) (iv' (Fin.last 0))
      ↔ iv (Fin.last 0) = iv' (Fin.last 0) := by
      intro iv iv'
      constructor
      · intro h
        exact (Equiv.cast (congrArg I (base_compInS_castSucc hkm (Fin.last 0)))).injective h
      · intro h
        rw [h]
    by_cases hc : i (Fin.last (0 - 0)) = i' (Fin.last (0 - 0))
    · rw [ite_eq_left hc, ite_eq_left ((hcI i i').mpr hc), hKWeq]
      rfl
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((hcI i i').mp h'))]

set_option maxHeartbeats 1200000 in
/-- Normalization closure at the degenerate two-wire base depth: composing a
normalized two-wire comb with a normalized single-output window preserves
normalization, with the scalar identity as the tail witness. -/
private theorem normalized_suffix_comp_base (hkm : 0 + 0 + 1 ≤ 0 + 1)
    (J : CMatrix (Space I O)) (hJ : Normalized I O J)
    (X : CMatrix (Space (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm)))
    (hX : Normalized (suffixOut O 0 0 hkm) (suffixIn I 0 0 hkm) X) :
    Normalized (fun j : Fin (0 - 0 + 1) => I (compInS (n := 0) 0 0 hkm j))
      (fun j : Fin (0 - 0 + 1) => O (compOutS (n := 0) 0 0 hkm j))
      (suffixCompS (I := I) (O := O) (n := 0) 0 0 hkm J X) := by
  rcases hJ with ⟨hJpos, K, hK, hpeel⟩
  rcases hK with ⟨-, KW, hKW2, hpeelK⟩
  have hKWeq : KW = 1 := (normalized_zero _ _ KW).mp hKW2
  refine ⟨matReindex_posSemidef _
      (suffixComp_posSemidef 0 0 hkm J X hJpos hX.1),
    1, (normalized_zero _ _ 1).mpr rfl, ?_⟩
  intro i i' o o'
  exact base_peel I O hkm J K hpeel X hX KW hKWeq hpeelK i i' o o'

end Base00

/-- Normalization closure of suffix composition, budget-free form: composing a
normalized comb with a normalized window at any feasible position preserves
normalization. The recursion budget is supplied internally from the window
geometry. -/
theorem normalized_suffix_comp_final {n : Nat} {I O : Fin (n + 2) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O)) (hJ : Normalized I O J)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (hX : Normalized (suffixOut O k m hkm) (suffixIn I k m hkm) X) :
    Normalized (fun j : Fin (n - m + 1) => I (compInS (n := n) k m hkm j))
      (fun j : Fin (n - m + 1) => O (compOutS (n := n) k m hkm j))
      (suffixCompS (I := I) (O := O) (n := n) k m hkm J X) :=
  normalized_suffix_comp (n + 1 - (k + m + 1) + m + 1) normalized_suffix_comp_base
    n I O k m hkm (by omega) J hJ X hX

end CompositionClosure

section ProbabilisticClosure

/-! ### Loewner transport through matrix reindexing -/

/-- Loewner domination transports through matrix reindexing. -/
theorem matReindex_le {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {M N : CMatrix ι} (h : M ≤ N) :
    matReindex e M ≤ matReindex e N := by
  rw [Matrix.le_iff] at h ⊢
  have hdiff : (matReindex e N - matReindex e M) = matReindex e (N - M) := by
    ext k k'
    rfl
  rw [hdiff]
  exact matReindex_posSemidef _ h

/-- Loewner domination pulls back along any index function: the compressed
matrices inherit the order. -/
theorem matPullback_le {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (f : κ → ι) {M N : CMatrix ι} (h : M ≤ N) :
    M.submatrix f f ≤ N.submatrix f f := by
  rw [Matrix.le_iff]
  exact (Matrix.le_iff.mp h).submatrix f

/-! ### Probabilistic closure of the suffix composition -/

variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The suffix composition is monotone in the outer comb whenever the inner
window is positive semidefinite: Loewner domination transports through the
link product and the space packing. -/
theorem suffixComp_le (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    {J K : CMatrix (Space I O)} (hJK : J ≤ K)
    (X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm)))
    (hX : X.PosSemidef) :
    suffixComp (I := I) (O := O) k m hkm J X
      ≤ suffixComp (I := I) (O := O) k m hkm K X := by
  rw [suffixComp_eq_reindex, suffixComp_eq_reindex]
  refine matReindex_le _ ?_
  rw [WireMatch.linkProduct_eq_core, WireMatch.linkProduct_eq_core]
  refine linkProduct_mono_right ?_ ?_
  · exact matReindex_posSemidef _ (matReindex_posSemidef _ hX)
  · exact matReindex_le _ (matReindex_le _ hJK)

/-- The suffix composition is monotone in the window whenever the outer
comb is positive semidefinite. This transports a probabilistic window's
domination by its deterministic completion. -/
theorem suffixComp_mono_window (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    (J : CMatrix (Space I O)) (hJ : J.PosSemidef)
    {X Y : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))}
    (hXY : X ≤ Y) :
    suffixComp (I := I) (O := O) k m hkm J X ≤
      suffixComp (I := I) (O := O) k m hkm J Y := by
  rw [suffixComp_eq_reindex, suffixComp_eq_reindex]
  refine matReindex_le _ ?_
  rw [WireMatch.linkProduct_eq_core, WireMatch.linkProduct_eq_core]
  exact linkProduct_mono_left (matReindex_le _ (matReindex_le _ hXY))
    (matReindex_posSemidef _ (matReindex_posSemidef _ hJ))

/-- Probabilistic closure of the suffix composition: composing a probabilistic
outer comb with a normalized window yields a probabilistic composite, whose
deterministic completion is the composite of any deterministic completion of
the outer factor. -/
theorem IsProbabilistic.suffix_comp (k m : Nat) (hkm : k + m + 1 ≤ n + 1)
    {J : CMatrix (Space I O)} (hJ : IsProbabilistic (n := n + 1) I O J)
    {X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))}
    (hX : Normalized (suffixOut O k m hkm) (suffixIn I k m hkm) X) :
    IsProbabilistic (fun j : Fin (n - m + 1) => I (compInS (n := n) k m hkm j))
      (fun j : Fin (n - m + 1) => O (compOutS (n := n) k m hkm j))
      (suffixCompS (I := I) (O := O) k m hkm J X) := by
  obtain ⟨hJpsd, K, hK, hle⟩ := hJ
  refine ⟨matReindex_posSemidef _ (suffixComp_posSemidef k m hkm J X hJpsd hX.posSemidef),
    suffixCompS (I := I) (O := O) k m hkm K X,
    normalized_suffix_comp_final k m hkm K hK X hX, ?_⟩
  exact matReindex_le _ (suffixComp_le k m hkm hle X hX.posSemidef)

/-- Two probabilistic combs have a probabilistic suffix composite. Its
deterministic completion composes a deterministic completion of each
factor; neither factor is required to be normalized. -/
theorem IsProbabilistic.suffix_comp_probabilistic (k m : Nat)
    (hkm : k + m + 1 ≤ n + 1)
    {J : CMatrix (Space I O)} (hJ : IsProbabilistic I O J)
    {X : CMatrix (Space (suffixOut O k m hkm) (suffixIn I k m hkm))}
    (hX : IsProbabilistic (suffixOut O k m hkm) (suffixIn I k m hkm) X) :
    IsProbabilistic (fun j : Fin (n - m + 1) => I (compInS k m hkm j))
      (fun j : Fin (n - m + 1) => O (compOutS k m hkm j))
      (suffixCompS (I := I) (O := O) k m hkm J X) := by
  obtain ⟨hJpsd, K, hK, hJK⟩ := hJ
  obtain ⟨hXpsd, Y, hY, hXY⟩ := hX
  refine ⟨matReindex_posSemidef _ (suffixComp_posSemidef k m hkm J X hJpsd hXpsd),
    suffixCompS (I := I) (O := O) k m hkm K Y,
    normalized_suffix_comp_final k m hkm K hK Y hY, ?_⟩
  exact matReindex_le _ ((suffixComp_le k m hkm hJK X hXpsd).trans
    (suffixComp_mono_window k m hkm K hK.posSemidef hXY))

/-! ### Monotonicity of the link action -/

section ActionMono

variable {n : Nat} {I O : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The empty boundary family of the link action. -/
private abbrev empFam : Fin 0 → Type u := fun _ => PUnit

/-- The aggregate window family of the link action. -/
private abbrev aggWin (I O : Fin (n + 1) → Type u) : Fin 1 → Type u :=
  fun _ => Space (innerInput (O := O)) (innerOutput (I := I))

/-- The aggregate channel family of the link action. -/
private abbrev aggChan (I O : Fin (n + 1) → Type u) : Fin 1 → Type u :=
  fun _ => I 0 × O (Fin.last n)

/-- Packing equivalence for the link action's output space: the aggregate
channel space is the append of the empty boundary with the channel family. -/
private def linkPackEquiv (I O : Fin (n + 1) → Type u) :
    (I 0 × O (Fin.last n)) ≃ (∀ i, WireFam.append empFam (aggChan I O) i) :=
  { toFun := fun p => (WireFam.splitAppendEquiv empFam (aggChan I O)).symm
      ((fun j => Fin.elim0 j), (fun _ => p))
    invFun := fun p' =>
      ((WireFam.splitAppendEquiv empFam (aggChan I O)) p').2 ⟨0, by omega⟩
    left_inv := fun p => congrArg (fun z => z.2 ⟨0, by omega⟩)
      (Equiv.apply_symm_apply (WireFam.splitAppendEquiv empFam (aggChan I O))
        ((fun j => Fin.elim0 j), (fun _ => p)))
    right_inv := fun p' => by
      funext i
      have hi : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      subst hi
      rfl }

/-- Reading equivalence for the link action's window family: the aggregate
window space is the append of the empty boundary with the window family. -/
private def linkWinEquiv (I O : Fin (n + 1) → Type u) :
    (∀ i, WireFam.append empFam (aggWin I O) i) ≃
      Space (innerInput (O := O)) (innerOutput (I := I)) :=
  { toFun := fun p => ((WireFam.splitAppendEquiv empFam (aggWin I O) p).2 ⟨0, by omega⟩)
    invFun := fun y => (WireFam.splitAppendEquiv empFam (aggWin I O)).symm
      ((fun j => Fin.elim0 j), (fun _ => y))
    left_inv := fun p => by
      funext i
      have hi : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      subst hi
      rfl
    right_inv := fun y => congrArg (fun z => z.2 ⟨0, by omega⟩)
      (Equiv.apply_symm_apply (WireFam.splitAppendEquiv empFam (aggWin I O))
        ((fun j => Fin.elim0 j), (fun _ => y))) }

set_option maxHeartbeats 1200000 in
/-- The link action is monotone in the outer comb: Loewner domination of the
outer combs transports to the composed channel whenever the inserted window
is positive semidefinite. -/
theorem linkAction_le {J K : CMatrix (Space I O)} (hJK : J ≤ K)
    {X : CMatrix (Space (innerInput (O := O)) (innerOutput (I := I)))}
    (hX : X.PosSemidef) :
    linkAction (I := I) (O := O) J X ≤ linkAction (I := I) (O := O) K X := by
  have hEq : ∀ (L : CMatrix (Space I O)), linkAction (I := I) (O := O) L X =
      matReindex (linkPackEquiv I O).symm (WireFam.linkProduct empFam (aggWin I O)
        (aggChan I O)
        (fun p q => X ((WireFam.splitAppendEquiv empFam (aggWin I O) p).2 0)
          ((WireFam.splitAppendEquiv empFam (aggWin I O) q).2 0))
        (fun p q => WireFam.matReindex (actionEquiv (I := I) (O := O)) L
            ((WireFam.splitAppendEquiv (aggWin I O) (aggChan I O) p).1 0,
              (WireFam.splitAppendEquiv (aggWin I O) (aggChan I O) p).2 0)
            ((WireFam.splitAppendEquiv (aggWin I O) (aggChan I O) q).1 0,
              (WireFam.splitAppendEquiv (aggWin I O) (aggChan I O) q).2 0))) :=
    fun L => rfl
  rw [hEq J, hEq K]
  refine matReindex_le _ ?_
  refine linkProduct_mono_right ?_ ?_
  · have hM : (fun p q : ∀ i, WireFam.append empFam (aggWin I O) i => X
            ((WireFam.splitAppendEquiv empFam (aggWin I O) p).2 0)
            ((WireFam.splitAppendEquiv empFam (aggWin I O) q).2 0))
          = matReindex (linkWinEquiv I O).symm X := by
      ext p q
      rfl
    rw [hM]
    exact matReindex_posSemidef _ hX
  · exact matPullback_le
      (fun p => ((WireFam.splitAppendEquiv (aggWin I O) (aggChan I O) p).1 0,
        (WireFam.splitAppendEquiv (aggWin I O) (aggChan I O) p).2 0))
      (matReindex_le (actionEquiv (I := I) (O := O)) hJK)

/-- The action of a probabilistic comb on a positive semidefinite window is
dominated by the action of its deterministic completion. -/
theorem IsProbabilistic.actionMap_le {J : CMatrix (Space I O)}
    (hJ : IsProbabilistic (I := I) (O := O) J)
    {X : CMatrix (Space (innerInput (O := O)) (innerOutput (I := I)))}
    (hX : X.PosSemidef) :
    ∃ K, Normalized (I := I) (O := O) K ∧
      actionMap (I := I) (O := O) J X ≤ actionMap (I := I) (O := O) K X := by
  obtain ⟨-, K, hK, hle⟩ := hJ
  refine ⟨K, hK, ?_⟩
  rw [actionMap_eq_linkAction (I := I) (O := O) J X,
    actionMap_eq_linkAction (I := I) (O := O) K X]
  exact linkAction_le hle hX

end ActionMono

end ProbabilisticClosure

section EndPoint

variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-! ### Endpoint index computations (k = 0, m = n) -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The single index of `Fin (n + 1 - n)` is zero. -/
private theorem endFin1ext (j : Fin (n + 1 - n)) : j = ⟨0, by omega⟩ :=
  Fin.ext (by have := j.isLt; omega)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the endpoint the composite's single input wire is the outer comb's
initial input wire. -/
theorem compIn_end : compIn (n := n) 0 n ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin (n + 2)) := by
  apply Fin.ext
  show (compIn (n := n) 0 n ⟨0, by omega⟩ : Nat) = 0
  rw [compIn_val]
  split <;> omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the endpoint the composite's single output wire is the outer comb's
final output wire. -/
theorem compOut_end : compOut (n := n) 0 n ⟨0, by omega⟩ = Fin.last (n + 1) := by
  apply Fin.ext
  show (compOut (n := n) 0 n ⟨0, by omega⟩ : Nat) = n + 1
  rw [compOut_val]
  split <;> omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Wire equality between the window's output family and `innerInput`. -/
theorem endWinOEq (hkm : 0 + n + 1 ≤ n + 1) (t : Fin (n + 1)) :
    O (suffixOutIdx 0 n hkm t) = O (Fin.castSucc t) := by
  apply congrArg O
  apply Fin.ext
  show (0 : Nat) + t = (t : Nat)
  omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Wire equality between the window's input family and `innerOutput`. -/
theorem endWinIEq (hkm : 0 + n + 1 ≤ n + 1) (t : Fin (n + 1)) :
    I (suffixInIdx 0 n hkm t) = I (Fin.succ t) := by
  apply congrArg I
  apply Fin.ext
  show (0 : Nat) + 1 + t = (t : Nat) + 1
  omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Wire equality for the composite's input family at the endpoint. -/
theorem endInEq (j : Fin (n + 1 - n)) :
    I (compIn (n := n) 0 n j) = I (compIn (n := n) 0 n ⟨0, by omega⟩) := by
  rw [endFin1ext j]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Wire equality for the composite's output family at the endpoint. -/
theorem endOutEq (j : Fin (n + 1 - n)) :
    O (compOut (n := n) 0 n j) = O (compOut (n := n) 0 n ⟨0, by omega⟩) := by
  rw [endFin1ext j]

/-! ### Endpoint equivalences -/

/-- The window's Choi space at the endpoint is the link action's inner space,
wire by wire. -/
def endWinEquiv (hkm : 0 + n + 1 ≤ n + 1) :
    Space (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) ≃
      Space (innerInput (O := O)) (innerOutput (I := I)) :=
  Equiv.prodCongr
    (Equiv.piCongrRight fun t => Equiv.cast (endWinOEq hkm t))
    (Equiv.piCongrRight fun t => Equiv.cast (endWinIEq hkm t))

/-- The shared (connected) configurations at the endpoint, identified with the
link action's inner space. -/
private def endSharedEquiv (hkm : 0 + n + 1 ≤ n + 1) :
    (∀ i, (suffixMatch (I := I) (O := O) 0 n hkm).connFam₁ i) ≃
      Space (innerInput (O := O)) (innerOutput (I := I)) :=
  (XFlatEquiv (I := I) (O := O) 0 n hkm).symm.trans (endWinEquiv hkm)

/-- The shared configurations at the endpoint, aggregated to the link action's
single-window index. -/
private def endAggEquiv (hkm : 0 + n + 1 ≤ n + 1) :
    (∀ i, (suffixMatch (I := I) (O := O) 0 n hkm).connFam₁ i) ≃
      (Fin 1 → Space (innerInput (O := O)) (innerOutput (I := I))) :=
  (endSharedEquiv (I := I) (O := O) hkm).trans
    (Equiv.piUnique (fun _ : Fin 1 => Space (innerInput (O := O)) (innerOutput (I := I)))).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Reading the aggregated shared configuration at the unique index. -/
private theorem endAggEquiv_apply_zero (hkm : 0 + n + 1 ≤ n + 1)
    (z : ∀ i, (suffixMatch (I := I) (O := O) 0 n hkm).connFam₁ i) :
    endAggEquiv (I := I) (O := O) hkm z ⟨0, by omega⟩
      = endWinEquiv hkm ((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z) :=
  rfl

/-- The composite's Choi space at the endpoint is the link action's channel
space, packaging the single input and output wires. -/
def endPackEquiv : Space (fun j => I (compIn (n := n) 0 n j))
      (fun j => O (compOut (n := n) 0 n j)) ≃
      I (compIn (n := n) 0 n ⟨0, by omega⟩) × O (compOut (n := n) 0 n ⟨0, by omega⟩) where
  toFun p := (p.1 ⟨0, by omega⟩, p.2 ⟨0, by omega⟩)
  invFun q := ((fun j => cast (endInEq j).symm q.1),
    (fun j => cast (endOutEq j).symm q.2))
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> funext j <;> rw [endFin1ext j] <;> rfl
  right_inv q := by
    refine Prod.ext ?_ ?_ <;> rfl

/-! ### The endpoint readback equation -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The first private outer wire at the endpoint is the initial input. -/
private theorem complEmb_end_zero (hkm : 0 + n + 1 ≤ n + 1) :
    complEmb (suffixConnIdx 0 n hkm) (suffixMatch (I := I) (O := O) 0 n hkm).hι₂
        ⟨0, by omega⟩ = Fin.castAdd (n + 2) (⟨0, by omega⟩ : Fin (n + 2)) := by
  rw [suffixComplEmb 0 n hkm (suffixMatch (I := I) (O := O) 0 n hkm).hι₂ ⟨0, by omega⟩]
  simp only [suffixComplIdx]
  split
  · rw [compIn_end]
  · omega

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The second private outer wire at the endpoint is the final output. -/
private theorem complEmb_end_one (hkm : 0 + n + 1 ≤ n + 1) :
    complEmb (suffixConnIdx 0 n hkm) (suffixMatch (I := I) (O := O) 0 n hkm).hι₂
        ⟨1, by omega⟩ = Fin.natAdd (n + 2) (Fin.last (n + 1)) := by
  rw [suffixComplEmb 0 n hkm (suffixMatch (I := I) (O := O) 0 n hkm).hι₂ ⟨1, by omega⟩]
  simp only [suffixComplIdx]
  split
  · omega
  · rw [endFin1ext ⟨(1 : Nat) - (n + 1 - n), by omega⟩, compOut_end]

/-- The link action's channel space at the endpoint, cast wire by wire to the
composite comb's packaged input and output wires. -/
def endChanEquiv :
    I (⟨0, by omega⟩ : Fin (n + 2)) × O (Fin.last (n + 1)) ≃
      I (compIn (n := n) 0 n ⟨0, by omega⟩) × O (compOut (n := n) 0 n ⟨0, by omega⟩) :=
  Equiv.prodCongr (Equiv.cast (congrArg I compIn_end).symm)
    (Equiv.cast (congrArg O compOut_end).symm)

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the endpoint, the flattened inner configuration's input entry is the
window input entry transported along the append equation. -/
private theorem endXFlat_symm_two (hkm : 0 + n + 1 ≤ n + 1)
    (z : ∀ i : Fin (n + 1 + (n + 1)), append (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) i)
    (t : Fin (n + 1)) :
    (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).2 t)
      = cast (append_natAdd (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) t)
        (z (Fin.natAdd (n + 1) t)) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the endpoint, the flattened inner configuration's output entry is the
window output entry transported along the append equation. -/
private theorem endXFlat_symm_one (hkm : 0 + n + 1 ≤ n + 1)
    (z : ∀ i : Fin (n + 1 + (n + 1)), append (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) i)
    (t : Fin (n + 1)) :
    (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).1 t)
      = cast (append_castAdd (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) t)
        (z (Fin.castAdd (n + 1) t)) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the endpoint, the relabeled connected value on the window's input side
is the flattened inner configuration's input entry, transported to the outer
comb's input wire. -/
private theorem end_eRelabel_natAdd (hkm : 0 + n + 1 ≤ n + 1)
    (z : ∀ i : Fin (n + 1 + (n + 1)), append (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) i)
    (t : Fin (n + 1)) :
    ((suffixMatch (I := I) (O := O) 0 n hkm).eRelabel z (Fin.natAdd (n + 1) t) :
        append I O (suffixConnIdx 0 n hkm (Fin.natAdd (n + 1) t)))
      = cast ((show suffixIn I 0 n hkm t = I ⟨0 + 1 + (t : Nat), by omega⟩ from rfl).trans
          ((append_castAdd I O ⟨0 + 1 + (t : Nat), by omega⟩).symm.trans
            (congrArg (append I O) (suffixConnIdx_natAdd 0 n hkm t).symm)))
        (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).2 t) := by
  rw [endXFlat_symm_two hkm z t]
  exact (cast2 (append_natAdd (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) t)
    ((show suffixIn I 0 n hkm t = I ⟨0 + 1 + (t : Nat), by omega⟩ from rfl).trans
      ((append_castAdd I O ⟨0 + 1 + (t : Nat), by omega⟩).symm.trans
        (congrArg (append I O) (suffixConnIdx_natAdd 0 n hkm t).symm)))
    (z (Fin.natAdd (n + 1) t))).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- At the endpoint, the relabeled connected value on the window's output side
is the flattened inner configuration's output entry, transported to the outer
comb's output wire. -/
private theorem end_eRelabel_castAdd (hkm : 0 + n + 1 ≤ n + 1)
    (z : ∀ i : Fin (n + 1 + (n + 1)), append (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) i)
    (t : Fin (n + 1)) :
    ((suffixMatch (I := I) (O := O) 0 n hkm).eRelabel z (Fin.castAdd (n + 1) t) :
        append I O (suffixConnIdx 0 n hkm (Fin.castAdd (n + 1) t)))
      = cast ((show suffixOut O 0 n hkm t = O ⟨0 + (t : Nat), by omega⟩ from rfl).trans
          ((append_natAdd I O ⟨0 + (t : Nat), by omega⟩).symm.trans
            (congrArg (append I O) (suffixConnIdx_castAdd 0 n hkm t).symm)))
        (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).1 t) := by
  rw [endXFlat_symm_one hkm z t]
  exact (cast2 (append_castAdd (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) t)
    ((show suffixOut O 0 n hkm t = O ⟨0 + (t : Nat), by omega⟩ from rfl).trans
      ((append_natAdd I O ⟨0 + (t : Nat), by omega⟩).symm.trans
        (congrArg (append I O) (suffixConnIdx_castAdd 0 n hkm t).symm)))
    (z (Fin.castAdd (n + 1) t))).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Endpoint readback equation: reading the outer configuration (window part
`z`, private part packaged from `u`) and splitting it into input and output
blocks reproduces the initial input consed onto the transported window output
block, and the transported window input block snoced with the final output. -/
private theorem end_read₂_eq (hkm : 0 + n + 1 ≤ n + 1)
    (z : ∀ i : Fin (n + 1 + (n + 1)), append (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) i)
    (u : Space (fun j => I (compIn (n := n) 0 n j)) (fun j => O (compOut (n := n) 0 n j))) :
    splitAppendEquiv I O ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
        (complPack (I := I) (O := O) 0 n hkm u.1 u.2))
      = (Fin.cons (cast (congrArg I compIn_end) (u.1 ⟨0, by omega⟩))
          (fun t => cast (endWinIEq hkm t)
            (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).2 t)),
        Fin.snoc (fun t => cast (endWinOEq hkm t)
            (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).1 t))
          (cast (congrArg O compOut_end) (u.2 ⟨0, by omega⟩))) := by
  classical
  rw [splitAppendEquiv_apply]
  apply Prod.ext
  · funext j
    cases j using Fin.cases with
    | zero =>
      have hr : (suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
          (complEmb (suffixConnIdx 0 n hkm)
            (suffixMatch (I := I) (O := O) 0 n hkm).hι₂ ⟨0, by omega⟩)
        = complPack (I := I) (O := O) 0 n hkm u.1 u.2 ⟨0, by omega⟩ :=
        suffixRead₂_compl 0 n hkm z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2) ⟨0, by omega⟩
      show cast (append_castAdd I O (⟨0, by omega⟩ : Fin (n + 2)))
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
            (Fin.castAdd (n + 2) ⟨0, by omega⟩))
        = cast (congrArg I compIn_end) (u.1 ⟨0, by omega⟩)
      rw [← cast_congrArg_apply (complEmb_end_zero (I := I) (O := O) hkm)
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)),
        hr, complPack_lt 0 n hkm u.1 u.2 ⟨0, by omega⟩
          (by show (0 : Nat) < n + 1 - n; omega)]
      exact cast3 (complFam₂_eq_lt (I := I) (O := O) 0 n hkm ⟨0, by omega⟩
          (by show (0 : Nat) < n + 1 - n; omega)).symm
        (congrArg (append I O) (complEmb_end_zero (I := I) (O := O) hkm))
        (append_castAdd I O (⟨0, by omega⟩ : Fin (n + 2)))
        (u.1 ⟨(⟨0, by omega⟩ : Fin (n + 2 + (n + 2) - ((n + 1) + (n + 1)))).val,
          by show (0 : Nat) < n + 1 - n; omega⟩)
    | succ t =>
      have hb : suffixConnIdx 0 n hkm (Fin.natAdd (n + 1) t)
          = Fin.castAdd (n + 2) (Fin.succ t) := by
        simp only [suffixConnIdx_natAdd]
        apply congrArg (Fin.castAdd (n + 2))
        apply Fin.ext
        show (0 : Nat) + 1 + (t : Nat) = (t : Nat) + 1
        omega
      have hr : (suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
          (suffixConnIdx 0 n hkm (Fin.natAdd (n + 1) t))
        = (suffixMatch (I := I) (O := O) 0 n hkm).eRelabel z (Fin.natAdd (n + 1) t) :=
        suffixRead₂_conn_natAdd 0 n hkm z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2) t
      show cast (append_castAdd I O (Fin.succ t))
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
            (Fin.castAdd (n + 2) (Fin.succ t)))
        = cast (endWinIEq hkm t)
            (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).2 t)
      rw [← cast_congrArg_apply hb
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)),
        hr, end_eRelabel_natAdd hkm z t, cast2, cast2]
  · funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · have hb : suffixConnIdx 0 n hkm (Fin.castAdd (n + 1) j)
          = Fin.natAdd (n + 2) (Fin.castSucc j) := by
        simp only [suffixConnIdx_castAdd]
        apply congrArg (Fin.natAdd (n + 2))
        apply Fin.ext
        show (0 : Nat) + (j : Nat) = (j : Nat)
        omega
      have hr : (suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
          (suffixConnIdx 0 n hkm (Fin.castAdd (n + 1) j))
        = (suffixMatch (I := I) (O := O) 0 n hkm).eRelabel z (Fin.castAdd (n + 1) j) :=
        suffixRead₂_conn_castAdd 0 n hkm z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2) j
      show cast (append_natAdd I O (Fin.castSucc j))
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
            (Fin.natAdd (n + 2) (Fin.castSucc j)))
        = Fin.snoc (fun t => cast (endWinOEq hkm t)
            (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).1 t))
            (cast (congrArg O compOut_end) (u.2 ⟨0, by omega⟩)) (Fin.castSucc j)
      rw [Fin.snoc_castSucc, ← cast_congrArg_apply hb
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)),
        hr, end_eRelabel_castAdd hkm z j, cast2, cast2]
    · have hr : (suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
          (complEmb (suffixConnIdx 0 n hkm)
            (suffixMatch (I := I) (O := O) 0 n hkm).hι₂ ⟨1, by omega⟩)
        = complPack (I := I) (O := O) 0 n hkm u.1 u.2 ⟨1, by omega⟩ :=
        suffixRead₂_compl 0 n hkm z
          (complPack (I := I) (O := O) 0 n hkm u.1 u.2) ⟨1, by omega⟩
      have hid : (⟨(1 : Nat) - (n + 1 - n), by omega⟩ : Fin (n + 1 - n))
          = ⟨0, by omega⟩ := by
        apply Fin.ext
        show (1 : Nat) - (n + 1 - n) = 0
        omega
      show cast (append_natAdd I O (Fin.last (n + 1)))
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)
            (Fin.natAdd (n + 2) (Fin.last (n + 1))))
        = Fin.snoc (fun t => cast (endWinOEq hkm t)
            (((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z).1 t))
            (cast (congrArg O compOut_end) (u.2 ⟨0, by omega⟩)) (Fin.last (n + 1))
      rw [Fin.snoc_last, ← cast_congrArg_apply (complEmb_end_one (I := I) (O := O) hkm)
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)),
        hr, complPack_ge 0 n hkm u.1 u.2 ⟨1, by omega⟩
          (by show ¬((1 : Nat) < n + 1 - n); omega),
        ← cast_congrArg_apply hid u.2]
      exact (cast3 (complFam₂_eq_ge (I := I) (O := O) 0 n hkm ⟨1, by omega⟩
            (by show ¬((1 : Nat) < n + 1 - n); omega)).symm
          (congrArg (append I O) (complEmb_end_one (I := I) (O := O) hkm))
          (append_natAdd I O (Fin.last (n + 1)))
          (u.2 ⟨(⟨1, by omega⟩ : Fin (n + 2 + (n + 2) - ((n + 1) + (n + 1)))).val
              - (n + 1 - n), by omega⟩)).trans
        (cast2 (congrArg (fun j => O (compOut (n := n) 0 n j)) hid)
          (congrArg O (compOut_end (n := n)))
          (u.2 ⟨(1 : Nat) - (n + 1 - n), by omega⟩)).symm

/-! ### The endpoint factorization -/

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- Per-summand form of the endpoint factorization: for literal flat
configurations `z z'`, the suffix-composition summand equals the link-action
summand transported along the aggregated shared-wire equivalence. -/
private theorem end_summand_eq (hkm : 0 + n + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O 0 n hkm) (suffixIn I 0 n hkm)))
    (u u' : Space (fun j => I (compIn (n := n) 0 n j)) (fun j => O (compOut (n := n) 0 n j)))
    (z z' : ∀ i : Fin (n + 1 + (n + 1)), append (suffixOut O 0 n hkm) (suffixIn I 0 n hkm) i) :
    X ((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z')
        ((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z) *
      J (splitAppendEquiv I O
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z'
            (complPack (I := I) (O := O) 0 n hkm u.1 u.2)))
        (splitAppendEquiv I O
          ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
            (complPack (I := I) (O := O) 0 n hkm u'.1 u'.2)))
    = (matReindex (endWinEquiv (I := I) (O := O) hkm) X)
        (endAggEquiv (I := I) (O := O) hkm z' ⟨0, by omega⟩)
        (endAggEquiv (I := I) (O := O) hkm z ⟨0, by omega⟩) *
      matReindex (actionEquiv (I := I) (O := O)) J
        (endAggEquiv (I := I) (O := O) hkm z' ⟨0, by omega⟩,
          (cast (congrArg I compIn_end) (u.1 ⟨0, by omega⟩),
            cast (congrArg O compOut_end) (u.2 ⟨0, by omega⟩)))
        (endAggEquiv (I := I) (O := O) hkm z ⟨0, by omega⟩,
          (cast (congrArg I compIn_end) (u'.1 ⟨0, by omega⟩),
            cast (congrArg O compOut_end) (u'.2 ⟨0, by omega⟩))) := by
  rw [endAggEquiv_apply_zero (I := I) (O := O) hkm z',
    endAggEquiv_apply_zero (I := I) (O := O) hkm z]
  simp only [matReindex_apply]
  simp only [Equiv.symm_apply_apply]
  rw [end_read₂_eq (I := I) (O := O) hkm z' u, end_read₂_eq (I := I) (O := O) hkm z u']
  rfl

omit [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- At the endpoint `k = 0`, `m = n`, suffix composition of the outer comb
with the inner window is exactly the outer comb's link action on the window
operator, transported to the composite's packaged channel space. -/
theorem suffixComp_eq_linkAction (hkm : 0 + n + 1 ≤ n + 1)
    (J : CMatrix (Space I O))
    (X : CMatrix (Space (suffixOut O 0 n hkm) (suffixIn I 0 n hkm))) :
    suffixComp (I := I) (O := O) 0 n hkm J X
      = matReindex ((endChanEquiv (I := I) (O := O)).trans
          (endPackEquiv (I := I) (O := O)).symm)
        (linkAction I O J (matReindex (endWinEquiv (I := I) (O := O) hkm) X)) := by
  classical
  ext u u'
  rw [suffixComp_apply (I := I) (O := O) 0 n hkm J X u u']
  conv_rhs =>
    simp only [matReindex_apply, linkAction, WireFam.linkProduct, Equiv.apply_symm_apply]
  simp only [suffixRead₁]
  show (∑ z : ∀ i, (suffixMatch (I := I) (O := O) 0 n hkm).connFam₁ i,
      ∑ z' : ∀ i, (suffixMatch (I := I) (O := O) 0 n hkm).connFam₁ i,
        X ((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z')
          ((XFlatEquiv (I := I) (O := O) 0 n hkm).symm z) *
        J (splitAppendEquiv I O
            ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z'
              (complPack (I := I) (O := O) 0 n hkm u.1 u.2)))
          (splitAppendEquiv I O
            ((suffixMatch (I := I) (O := O) 0 n hkm).read₂ z
              (complPack (I := I) (O := O) 0 n hkm u'.1 u'.2))))
    = ∑ z₂ : Fin 1 → Space (innerInput (O := O)) (innerOutput (I := I)),
      ∑ z₂' : Fin 1 → Space (innerInput (O := O)) (innerOutput (I := I)),
        (matReindex (endWinEquiv (I := I) (O := O) hkm) X)
          (z₂' ⟨0, by omega⟩) (z₂ ⟨0, by omega⟩) *
        matReindex (actionEquiv (I := I) (O := O)) J
          (z₂' ⟨0, by omega⟩,
            (cast (congrArg I compIn_end) (u.1 ⟨0, by omega⟩),
              cast (congrArg O compOut_end) (u.2 ⟨0, by omega⟩)))
          (z₂ ⟨0, by omega⟩,
            (cast (congrArg I compIn_end) (u'.1 ⟨0, by omega⟩),
              cast (congrArg O compOut_end) (u'.2 ⟨0, by omega⟩)))
  apply Fintype.sum_equiv (endAggEquiv (I := I) (O := O) hkm)
  intro z
  apply Fintype.sum_equiv (endAggEquiv (I := I) (O := O) hkm)
  intro z'
  exact end_summand_eq hkm J X u u' z z'

/-- Cast round trip along an equality and its inverse (forward form). -/
private theorem cast_cast_symm_self {α β : Type u} (h : α = β) (a : α) :
    cast h.symm (cast h a) = a := by
  subst h; rfl

/-- Cast round trip along an equality and its inverse (backward form). -/
private theorem cast_symm_cast_self {α β : Type u} (h : α = β) (b : β) :
    cast h (cast h.symm b) = b := by
  subst h; rfl

/-- Casts along an equality are injective. -/
private theorem cast_inj' {α β : Type u} (h : α = β) {a b : α} (he : cast h a = cast h b) :
    a = b := by
  subst h; exact he

/-! ### The normalized endpoint: the link action is a channel -/

/-- At the endpoint the composite has a single tooth, so endpoint
normalization is the ordinary channel constraint. -/
private theorem normalized_end_iff :
    ∀ (I₁ O₁ : Fin (n - n + 1) → Type u) [∀ j, Fintype (I₁ j)] [∀ j, DecidableEq (I₁ j)]
      [∀ j, Fintype (O₁ j)] [∀ j, DecidableEq (O₁ j)] (M : CMatrix (Space I₁ O₁)),
      Normalized I₁ O₁ M ↔ M.PosSemidef ∧ partialTraceB M = 1 := by
  rw [show n - n + 1 = 1 from by omega]
  intro I₁ O₁ hI₁ hI₁d hO₁ hO₁d M
  exact normalized_one_iff M

/-- The endpoint channel output unpacks to the composite's single output
wire tuple. -/
private def endEOutEquiv (hkm : 0 + n + 1 ≤ n + 1) :
    O (Fin.last (n + 1)) ≃ (∀ j : Fin (n - n + 1), O (compOutS (n := n) 0 n hkm j)) where
  toFun z := fun j => cast (endOutEq (compIdxEquiv (n := n) 0 n hkm j)).symm
    (cast (congrArg O compOut_end).symm z)
  invFun w := cast (congrArg O compOut_end)
    (cast (endOutEq (compIdxEquiv (n := n) 0 n hkm ⟨0, by omega⟩)) (w ⟨0, by omega⟩))
  left_inv z :=
    (congrArg (fun x => cast (congrArg O compOut_end) x)
      (cast_symm_cast_self (endOutEq (compIdxEquiv (n := n) 0 n hkm ⟨0, by omega⟩))
        (cast (congrArg O compOut_end).symm z))).trans
      (cast_symm_cast_self (congrArg O compOut_end) z)
  right_inv w := by
    funext j
    have hj : j = ⟨0, by omega⟩ := Fin.ext (by have := j.isLt; omega)
    subst hj
    exact (congrArg
        (fun x => cast (endOutEq (compIdxEquiv (n := n) 0 n hkm ⟨0, by omega⟩)).symm x)
        (cast_cast_symm_self (congrArg O compOut_end)
          (cast (endOutEq (compIdxEquiv (n := n) 0 n hkm ⟨0, by omega⟩)) (w ⟨0, by omega⟩)))).trans
      (cast_cast_symm_self (endOutEq (compIdxEquiv (n := n) 0 n hkm ⟨0, by omega⟩))
        (w ⟨0, by omega⟩))

/-- The endpoint channel input packs into the composite's single input wire
tuple. -/
private def endEIn (hkm : 0 + n + 1 ≤ n + 1) (i : I (⟨0, by omega⟩ : Fin (n + 2))) :
    ∀ j : Fin (n - n + 1), I (compInS (n := n) 0 n hkm j) :=
  fun j => cast (endInEq (compIdxEquiv (n := n) 0 n hkm j)).symm
    (cast (congrArg I compIn_end).symm i)

/-- The endpoint channel space packs into the composite's Choi space. -/
private def endChanPackEquiv (hkm : 0 + n + 1 ≤ n + 1) :
    I (⟨0, by omega⟩ : Fin (n + 2)) × O (Fin.last (n + 1)) ≃
      Space (fun j : Fin (n - n + 1) => I (compInS (n := n) 0 n hkm j))
        (fun j : Fin (n - n + 1) => O (compOutS (n := n) 0 n hkm j)) :=
  ((endChanEquiv (I := I) (O := O)).trans (endPackEquiv (I := I) (O := O)).symm).trans
    (spaceIdxEquiv (I := I) (O := O) 0 n hkm).symm

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The channel-space packing is componentwise: input pack and output unpack. -/
private theorem endE_prod (hkm : 0 + n + 1 ≤ n + 1) (i : I (⟨0, by omega⟩ : Fin (n + 2)))
    (z : O (Fin.last (n + 1))) :
    endChanPackEquiv (I := I) (O := O) hkm (i, z)
      = (endEIn (I := I) hkm i, endEOutEquiv (O := O) hkm z) := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
/-- The endpoint input packing is injective. -/
private theorem endEIn_injective (hkm : 0 + n + 1 ≤ n + 1) :
    Function.Injective (endEIn (I := I) hkm) := by
  intro i i' h
  have h0 := congrFun h ⟨0, by omega⟩
  exact cast_inj' (congrArg I compIn_end).symm
    (cast_inj' (endInEq (compIdxEquiv (n := n) 0 n hkm ⟨0, by omega⟩)).symm h0)

/-- The link action of a normalized comb on a normalized window is a channel:
positive semidefinite with unit input partial trace. This is the endpoint
reading of the suffix-composition closure. -/
theorem normalized_linkAction
    (J : CMatrix (Space I O)) (hJ : Normalized I O J)
    (X : CMatrix (Space (innerInput (O := O)) (innerOutput (I := I))))
    (hX : Normalized (innerInput (O := O)) (innerOutput (I := I)) X) :
    (linkAction I O J X).PosSemidef ∧ partialTraceB (linkAction I O J X) = 1 := by
  classical
  have hkm : 0 + n + 1 ≤ n + 1 := by omega
  have hconv : matReindex (spaceEquiv (fun t => Equiv.cast (endWinOEq hkm t))
      (fun t => Equiv.cast (endWinIEq hkm t)))
      ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X) = X := by
    rw [show spaceEquiv (fun t => Equiv.cast (endWinOEq hkm t))
        (fun t => Equiv.cast (endWinIEq hkm t)) = endWinEquiv (I := I) (O := O) hkm from rfl]
    exact Equiv.apply_symm_apply _ X
  have hXr : Normalized (suffixOut O 0 n hkm) (suffixIn I 0 n hkm)
      ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X) :=
    (Normalized.reindex_iff (fun t => Equiv.cast (endWinOEq hkm t))
      (fun t => Equiv.cast (endWinIEq hkm t))
      ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)).mpr (hconv.symm ▸ hX)
  obtain ⟨hposS, htraceS⟩ := (normalized_end_iff _ _ _).mp
    (normalized_suffix_comp_final (I := I) (O := O) 0 n hkm J hJ _ hXr)
  have hsc : suffixComp (I := I) (O := O) 0 n hkm J
        ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)
      = matReindex ((endChanEquiv (I := I) (O := O)).trans
          (endPackEquiv (I := I) (O := O)).symm) (linkAction I O J X) := by
    rw [suffixComp_eq_linkAction (I := I) (O := O) hkm J
      ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X), Equiv.apply_symm_apply]
  have hS : suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
        ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)
      = matReindex (endChanPackEquiv (I := I) (O := O) hkm) (linkAction I O J X) :=
    (congrArg (fun M => matReindex (spaceIdxEquiv (I := I) (O := O) 0 n hkm).symm M) hsc).trans
      ((congrArg (fun f => f (linkAction I O J X))
        (matReindex_trans ((endChanEquiv (I := I) (O := O)).trans (endPackEquiv (I := I) (O := O)).symm)
          (spaceIdxEquiv (I := I) (O := O) 0 n hkm).symm)).symm)
  have hLA : linkAction I O J X
      = (matReindex (endChanPackEquiv (I := I) (O := O) hkm)).symm
        (suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
          ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)) :=
    ((congrArg (fun M => (matReindex (endChanPackEquiv (I := I) (O := O) hkm)).symm M) hS).trans
      (Equiv.symm_apply_apply (matReindex (endChanPackEquiv (I := I) (O := O) hkm))
        (linkAction I O J X))).symm
  have hent : ∀ p q : I (⟨0, by omega⟩ : Fin (n + 2)) × O (Fin.last (n + 1)),
      linkAction I O J X p q
        = suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
            ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)
            (endChanPackEquiv (I := I) (O := O) hkm p)
            (endChanPackEquiv (I := I) (O := O) hkm q) :=
    fun p q => (congrArg (fun M : CMatrix (I (⟨0, by omega⟩ : Fin (n + 2)) × O (Fin.last (n + 1))) =>
        M p q) hLA).trans (matReindex_symm_apply _ _ p q)
  refine ⟨?_, ?_⟩
  · rw [hLA]
    exact (Matrix.posSemidef_submatrix_equiv (endChanPackEquiv (I := I) (O := O) hkm)).mpr hposS
  · ext i i'
    calc partialTraceB (linkAction I O J X) i i'
        = ∑ z : O (Fin.last (n + 1)), linkAction I O J X (i, z) (i', z) := rfl
      _ = ∑ z : O (Fin.last (n + 1)),
            suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
              ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)
              (endChanPackEquiv (I := I) (O := O) hkm (i, z))
              (endChanPackEquiv (I := I) (O := O) hkm (i', z)) :=
          Finset.sum_congr rfl (fun z _ => hent (i, z) (i', z))
      _ = ∑ z : O (Fin.last (n + 1)),
            suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
              ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)
              (endEIn (I := I) hkm i, endEOutEquiv (O := O) hkm z)
              (endEIn (I := I) hkm i', endEOutEquiv (O := O) hkm z) :=
          Finset.sum_congr rfl (fun z _ =>
            congrArg₂ (fun a b => suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
                ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X) a b)
              (endE_prod (I := I) (O := O) hkm i z) (endE_prod (I := I) (O := O) hkm i' z))
      _ = ∑ w : (∀ j : Fin (n - n + 1), O (compOutS (n := n) 0 n hkm j)),
            suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
              ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)
              (endEIn (I := I) hkm i, w)
              (endEIn (I := I) hkm i', w) :=
          Equiv.sum_comp (endEOutEquiv (O := O) hkm)
            (fun w => suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
              ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X)
              (endEIn (I := I) hkm i, w) (endEIn (I := I) hkm i', w))
      _ = partialTraceB (suffixCompS (I := I) (O := O) (n := n) 0 n hkm J
              ((matReindex (endWinEquiv (I := I) (O := O) hkm)).symm X))
            (endEIn (I := I) hkm i) (endEIn (I := I) hkm i') := rfl
      _ = (1 : CMatrix (∀ j : Fin (n - n + 1), I (compInS (n := n) 0 n hkm j)))
            (endEIn (I := I) hkm i) (endEIn (I := I) hkm i') :=
          congrArg (fun M : CMatrix (∀ j : Fin (n - n + 1), I (compInS (n := n) 0 n hkm j)) =>
            M (endEIn (I := I) hkm i) (endEIn (I := I) hkm i')) htraceS
      _ = (1 : CMatrix (I (⟨0, by omega⟩ : Fin (n + 2)))) i i' := by
          have h1 : (1 : CMatrix (∀ j : Fin (n - n + 1), I (compInS (n := n) 0 n hkm j)))
                (endEIn (I := I) hkm i) (endEIn (I := I) hkm i')
              = if i = i' then 1 else 0 := by
            rw [Matrix.one_apply]
            by_cases h : i = i'
            · rw [ite_eq_left (congrArg (endEIn (I := I) hkm) h), ite_eq_left h]
            · rw [ite_eq_right (fun he => h ((endEIn_injective (I := I) hkm) he)),
                ite_eq_right h]
          have h2 : (1 : CMatrix (I (⟨0, by omega⟩ : Fin (n + 2)))) i i'
              = if i = i' then 1 else 0 := Matrix.one_apply
          exact h1.trans h2.symm

end EndPoint

end Comb

end QIT.HigherOrder

end
