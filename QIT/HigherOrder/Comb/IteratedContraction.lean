/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.ForwardContraction
public import QIT.HigherOrder.Comb.ScheduledTensor
public import QIT.HigherOrder.Comb.CausalJoin

/-!
# Iterated forward connections

A causal join consumes several ports at once. This module iterates the
single-connection primitive `forwardContraction`: a finite sequence of forward
contractions on a fixed family length, with consumed positions recorded as
membership lists and each consumed port replaced by a unit type at its
position. Position uniqueness is required per port, not per tooth, so an event
may carry both an incoming and an outgoing connection.

The iteration is part of the network composition described in
[Chiribella2009Networks, comblong-pub.tex:1279-1286], whose join conditions at
lines 1233-1243 of the same source require acyclic composition. Identifying the
iterated contraction with the raw matched-wire link product remains a separate
obligation; this module does not assert that integration theorem.
-/

@[expose] public section
noncomputable section
open QIT
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder.Comb
open QIT.WireFam

/-- Replace the wire at every position of a membership list by a unit type. -/
def consumeList {n : Nat} (W : Fin n → Type u) (L : List (Fin n)) : Fin n → Type u :=
  fun t => if t ∈ L then PUnit else W t

instance consumeListFintype {n : Nat} (W : Fin n → Type u) [∀ j, Fintype (W j)]
    (L : List (Fin n)) (t : Fin n) : Fintype (consumeList W L t) := by
  unfold consumeList
  split <;> infer_instance

instance consumeListDecidableEq {n : Nat} (W : Fin n → Type u) [∀ j, DecidableEq (W j)]
    (L : List (Fin n)) (t : Fin n) : DecidableEq (consumeList W L t) := by
  unfold consumeList
  split <;> infer_instance

/-- Families with the same consumed positions agree. -/
theorem consumeList_ext {n : Nat} (W : Fin n → Type u) {L L' : List (Fin n)}
    (h : ∀ t, t ∈ L ↔ t ∈ L') : consumeList W L = consumeList W L' := by
  funext t
  simp only [consumeList]
  by_cases h1 : t ∈ L
  · have h2 : t ∈ L' := (h t).mp h1
    simp [h1, h2]
  · have h2 : t ∉ L' := fun hm => h1 ((h t).mpr hm)
    simp [h1, h2]

/-- An unconsumed position retains its original wire. -/
theorem consumeList_apply_not_mem {n : Nat} (W : Fin n → Type u) (L : List (Fin n))
    (t : Fin n) (h : t ∉ L) : consumeList W L t = W t := by
  simp [consumeList, h]

/-- Consuming one more position extends the consumed list, with the port
replaced by a unit type at its own position. -/
theorem erasePort_consumeList {n : Nat} (W : Fin n → Type u) (L : List (Fin n))
    (b : Fin n) : erasePort (consumeList W L) b.val = consumeList W (b :: L) := by
  funext t
  by_cases h1 : t.val = b.val
  · simp [erasePort, consumeList, List.mem_cons, Fin.ext h1]
  · by_cases h2 : t ∈ L <;>
      simp [erasePort, consumeList, h1, h2, List.mem_cons, Fin.ne_of_val_ne h1]

/-- A single forward connection at the original families. -/
structure Connection {n : Nat} (I O : Fin n → Type u) where
  /-- Position of the consumed output port. -/
  a : Fin n
  /-- Position of the consumed input port. -/
  b : Fin n
  /-- The connection is strictly forward. -/
  hab : a < b
  /-- Basis identification of the consumed ports. -/
  e : O a ≃ I b

/-- A finite sequence of forward contractions. The parameters record the
consumed-input and consumed-output position lists the sequence aims to consume;
the indices record the positions consumed so far. Each connection's basis
equivalence is stated at the current, partly consumed families, so the sequence
composes with `forwardContraction` step by step. No freshness constraint is
imposed by the type: distinct positions per side are a property of particular
sequences. -/
inductive Consumptions {n : Nat} (I O : Fin n → Type u) (SIn SOut : List (Fin n)) :
    List (Fin n) → List (Fin n) → Type u where
  /-- The sequence stops, having consumed exactly its target positions. -/
  | done {SI SO : List (Fin n)} (hSI : ∀ t, t ∈ SI ↔ t ∈ SIn)
      (hSO : ∀ t, t ∈ SO ↔ t ∈ SOut) :
      Consumptions I O SIn SOut SI SO
  /-- Consume the output at `a` and the input at `b`, then continue. -/
  | cons {SI SO : List (Fin n)} (a b : Fin n) (hab : a < b)
      (e : (consumeList O SO) a ≃ (consumeList I SI) b) :
      Consumptions I O SIn SOut (b :: SI) (a :: SO) →
      Consumptions I O SIn SOut SI SO

namespace Consumptions

variable {n : Nat} {I O : Fin n → Type u}

/-- Apply a sequence of forward contractions, transporting across the family
equalities that identify single-position erasure with list consumption. -/
def run [∀ j, Fintype (O j)] {SIn SOut : List (Fin n)} {SI SO : List (Fin n)}
    (c : Consumptions I O SIn SOut SI SO) :
    CMatrix (Space (consumeList I SI) (consumeList O SO)) →
    CMatrix (Space (consumeList I SIn) (consumeList O SOut)) := by
  induction c with
  | @done SI SO hSI hSO =>
      have hI : consumeList I SI = consumeList I SIn := consumeList_ext I hSI
      have hO : consumeList O SO = consumeList O SOut := consumeList_ext O hSO
      intro J
      exact matReindex (spaceEquiv
        (fun j => Equiv.cast (congrFun hI j)) (fun j => Equiv.cast (congrFun hO j))) J
  | @cons SI SO a b hab e rest ih =>
      intro J
      exact ih (matReindex (spaceEquiv
        (fun j => Equiv.cast (congrFun (erasePort_consumeList I SI b) j))
        (fun j => Equiv.cast (congrFun (erasePort_consumeList O SO a) j)))
        (forwardContraction a b e J))

/-- Iterated forward contraction preserves recursive normalization, starting
from the current families and ending at the target consumed positions. -/
theorem run_normalized {SIn SOut SI SO : List (Fin n)}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (c : Consumptions I O SIn SOut SI SO)
    {J : CMatrix (Space (consumeList I SI) (consumeList O SO))}
    (hJ : Normalized (consumeList I SI) (consumeList O SO) J) :
    Normalized (consumeList I SIn) (consumeList O SOut) (c.run J) := by
  induction c with
  | @done SI SO hSI hSO =>
      exact (Normalized.reindex_iff _ _ _).mp hJ
  | @cons SI SO a b hab e rest ih =>
      show Normalized (consumeList I SIn) (consumeList O SOut)
        (rest.run (matReindex (spaceEquiv
          (fun j => Equiv.cast (congrFun (erasePort_consumeList I SI b) j))
          (fun j => Equiv.cast (congrFun (erasePort_consumeList O SO a) j)))
          (forwardContraction a b e J)))
      exact ih ((Normalized.reindex_iff
        (fun j => Equiv.cast (congrFun (erasePort_consumeList I SI b) j))
        (fun j => Equiv.cast (congrFun (erasePort_consumeList O SO a) j)) _).mp
        (hJ.forwardContraction a b hab e))

private theorem ofListAuxFresh {n : Nat} {I O : Fin n → Type u} (c : Connection I O)
    (cs : List (Connection I O)) (SI SO : List (Fin n))
    (hdisIn : ((c :: cs).map Connection.b).Nodup)
    (hdisOut : ((c :: cs).map Connection.a).Nodup)
    (hfresh : ∀ c' ∈ c :: cs, c'.a ∉ SO ∧ c'.b ∉ SI) :
    ∀ c' ∈ cs, c'.a ∉ c.a :: SO ∧ c'.b ∉ c.b :: SI := by
  intro c' hc'
  have hf := hfresh c' (by simp [hc'])
  refine ⟨?_, ?_⟩
  · intro hmem
    rcases List.mem_cons.1 hmem with h | h
    · exact (List.nodup_cons.1 hdisOut).1 (h ▸ (List.mem_map.2 ⟨c', hc', rfl⟩))
    · exact hf.1 h
  · intro hmem
    rcases List.mem_cons.1 hmem with h | h
    · exact (List.nodup_cons.1 hdisIn).1 (h ▸ (List.mem_map.2 ⟨c', hc', rfl⟩))
    · exact hf.2 h

private theorem ofListAuxCoverIn {n : Nat} {I O : Fin n → Type u} (c : Connection I O)
    (cs : List (Connection I O)) (SIn SI : List (Fin n))
    (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c' ∈ c :: cs, c'.b = t) :
    ∀ t, t ∈ SIn ↔ t ∈ c.b :: SI ∨ ∃ c' ∈ cs, c'.b = t := by
  intro t
  rw [List.mem_cons]
  constructor
  · intro ht
    rcases (hcoverIn t).mp ht with hSI | ⟨c', hc', hcb'⟩
    · exact Or.inl (Or.inr hSI)
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · exact Or.inl (Or.inl hcb'.symm)
      · exact Or.inr ⟨c', hc', hcb'⟩
  · intro ht
    rcases ht with ht | ⟨c', hc', hcb'⟩
    · rcases ht with ht | hSI
      · exact (hcoverIn t).mpr (Or.inr ⟨c, List.mem_cons.2 (Or.inl rfl), ht.symm⟩)
      · exact (hcoverIn t).mpr (Or.inl hSI)
    · exact (hcoverIn t).mpr (Or.inr ⟨c', List.mem_cons.2 (Or.inr hc'), hcb'⟩)

private theorem ofListAuxCoverOut {n : Nat} {I O : Fin n → Type u} (c : Connection I O)
    (cs : List (Connection I O)) (SOut SO : List (Fin n))
    (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c' ∈ c :: cs, c'.a = t) :
    ∀ t, t ∈ SOut ↔ t ∈ c.a :: SO ∨ ∃ c' ∈ cs, c'.a = t := by
  intro t
  rw [List.mem_cons]
  constructor
  · intro ht
    rcases (hcoverOut t).mp ht with hSO | ⟨c', hc', hca'⟩
    · exact Or.inl (Or.inr hSO)
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · exact Or.inl (Or.inl hca'.symm)
      · exact Or.inr ⟨c', hc', hca'⟩
  · intro ht
    rcases ht with ht | ⟨c', hc', hca'⟩
    · rcases ht with ht | hSO
      · exact (hcoverOut t).mpr (Or.inr ⟨c, List.mem_cons.2 (Or.inl rfl), ht.symm⟩)
      · exact (hcoverOut t).mpr (Or.inl hSO)
    · exact (hcoverOut t).mpr (Or.inr ⟨c', List.mem_cons.2 (Or.inr hc'), hca'⟩)

/-- Build a sequence from a list of connections, consuming them in list order.
The distinctness hypotheses are per port: outputs must be pairwise distinct
among themselves, inputs likewise; no constraint ties an input position to an
output position. Coverage says every target position is either already consumed
or still queued in the list.

The definition pattern-matches on the connection list alone, and each branch
body is a constructor-headed term whose subproofs sit in argument positions,
so the sequence reduces definitionally on a literal list spine. -/
def ofListAux (SIn SOut : List (Fin n)) :
    (SI SO : List (Fin n)) → (cs : List (Connection I O)) →
    (hdisIn : (cs.map Connection.b).Nodup) →
    (hdisOut : (cs.map Connection.a).Nodup) →
    (hfresh : ∀ c ∈ cs, c.a ∉ SO ∧ c.b ∉ SI) →
    (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c ∈ cs, c.b = t) →
    (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c ∈ cs, c.a = t) →
    Consumptions I O SIn SOut SI SO
  | _, _, [], _, _, _, hcoverIn, hcoverOut =>
      Consumptions.done (fun t => by simpa using (hcoverIn t).symm)
        (fun t => by simpa using (hcoverOut t).symm)
  | SI, SO, c :: cs, hdisIn, hdisOut, hfresh, hcoverIn, hcoverOut =>
      Consumptions.cons c.a c.b c.hab
        ((Equiv.cast (consumeList_apply_not_mem O SO c.a
            ((hfresh c (by simp)).1))).trans
          (c.e.trans (Equiv.cast (consumeList_apply_not_mem I SI c.b
            ((hfresh c (by simp)).2)).symm)))
        (ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
          ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
          (by
            intro c' hc'
            have hf := hfresh c' (by simp [hc'])
            refine ⟨?_, ?_⟩
            · intro hmem
              rcases List.mem_cons.1 hmem with h | h
              · exact (List.nodup_cons.1 hdisOut).1
                  (h ▸ (List.mem_map.2 ⟨c', hc', rfl⟩))
              · exact hf.1 h
            · intro hmem
              rcases List.mem_cons.1 hmem with h | h
              · exact (List.nodup_cons.1 hdisIn).1
                  (h ▸ (List.mem_map.2 ⟨c', hc', rfl⟩))
              · exact hf.2 h)
          (by
            intro t
            rw [List.mem_cons]
            constructor
            · intro ht
              rcases (hcoverIn t).mp ht with hSI | ⟨c', hc', hcb'⟩
              · exact Or.inl (Or.inr hSI)
              · rcases List.mem_cons.1 hc' with rfl | hc'
                · exact Or.inl (Or.inl hcb'.symm)
                · exact Or.inr ⟨c', hc', hcb'⟩
            · intro ht
              rcases ht with ht | ⟨c', hc', hcb'⟩
              · rcases ht with ht | hSI
                · exact (hcoverIn t).mpr
                    (Or.inr ⟨c, List.mem_cons.2 (Or.inl rfl), ht.symm⟩)
                · exact (hcoverIn t).mpr (Or.inl hSI)
              · exact (hcoverIn t).mpr
                  (Or.inr ⟨c', List.mem_cons.2 (Or.inr hc'), hcb'⟩))
          (by
            intro t
            rw [List.mem_cons]
            constructor
            · intro ht
              rcases (hcoverOut t).mp ht with hSO | ⟨c', hc', hca'⟩
              · exact Or.inl (Or.inr hSO)
              · rcases List.mem_cons.1 hc' with rfl | hc'
                · exact Or.inl (Or.inl hca'.symm)
                · exact Or.inr ⟨c', hc', hca'⟩
            · intro ht
              rcases ht with ht | ⟨c', hc', hca'⟩
              · rcases ht with ht | hSO
                · exact (hcoverOut t).mpr
                    (Or.inr ⟨c, List.mem_cons.2 (Or.inl rfl), ht.symm⟩)
                · exact (hcoverOut t).mpr (Or.inl hSO)
              · exact (hcoverOut t).mpr
                  (Or.inr ⟨c', List.mem_cons.2 (Or.inr hc'), hca'⟩)))

/-- The sequence consuming a whole list of connections, starting from the
untouched families and ending with exactly the list's input and output
positions replaced by unit types. -/
def ofList (cs : List (Connection I O))
    (hdisIn : (cs.map Connection.b).Nodup)
    (hdisOut : (cs.map Connection.a).Nodup) :
    Consumptions I O (cs.map Connection.b) (cs.map Connection.a) [] [] :=
  ofListAux _ _ [] [] cs hdisIn hdisOut (fun _ _ => ⟨by simp, by simp⟩)
    (fun _ => by simp) (fun _ => by simp)

/-! ### Entrywise readback -/

/-- The independent consumed output values of a contraction sequence: one value
per consumed pair, carried at the family in force when that pair is consumed. -/
def fillValues {SIn SOut : List (Fin n)} :
    {SI SO : List (Fin n)} → (c : Consumptions I O SIn SOut SI SO) → Type u
  | _, _, done _ _ => PUnit
  | _, _, @cons _ _ _ _ _ SI SO a _ _ _ rest => rest.fillValues × (consumeList O SO) a

instance fillValuesFintype {SIn SOut SI SO : List (Fin n)} [∀ j, Fintype (O j)]
    (c : Consumptions I O SIn SOut SI SO) : Fintype c.fillValues := by
  induction c with
  | done => exact inferInstanceAs (Fintype PUnit)
  | @cons SI SO a b hab e rest ih =>
      exact inferInstanceAs (Fintype (rest.fillValues × (consumeList O SO) a))

/-- Restore the full input configuration from the boundary configuration and
the consumed output values, reading each consumed input through the
connection's basis equivalence. -/
def fillIn {SIn SOut SI SO : List (Fin n)} :
    (c : Consumptions I O SIn SOut SI SO) → c.fillValues →
    (∀ t, consumeList I SIn t) → (∀ t, consumeList I SI t)
  | done hSI _, _, p =>
      (Equiv.piCongrRight fun t => (Equiv.cast (congrFun (consumeList_ext I hSI) t)).symm) p
  | @cons _ _ _ _ _ SI SO _ b _ e rest, vz, p =>
      fillPort (consumeList I SI) b
        ((Equiv.piCongrRight fun t =>
          (Equiv.cast (congrFun (erasePort_consumeList I SI b) t)).symm) (rest.fillIn vz.1 p))
        (e vz.2)

/-- Restore the full output configuration from the boundary configuration and
the consumed output values. -/
def fillOut {SIn SOut SI SO : List (Fin n)} :
    (c : Consumptions I O SIn SOut SI SO) → c.fillValues →
    (∀ t, consumeList O SOut t) → (∀ t, consumeList O SO t)
  | done _ hSO, _, p =>
      (Equiv.piCongrRight fun t => (Equiv.cast (congrFun (consumeList_ext O hSO) t)).symm) p
  | @cons _ _ _ _ _ SI SO a _ _ _ rest, vz, p =>
      fillPort (consumeList O SO) a
        ((Equiv.piCongrRight fun t =>
          (Equiv.cast (congrFun (erasePort_consumeList O SO a) t)).symm) (rest.fillOut vz.1 p))
        vz.2

/-- A sum over the consumed values of a completed sequence collapses to the
single trivial value. -/
theorem fillValues_sum_done {SIn SOut SI SO : List (Fin n)} [∀ j, Fintype (O j)]
    {hSI : ∀ t, t ∈ SI ↔ t ∈ SIn} {hSO : ∀ t, t ∈ SO ↔ t ∈ SOut}
    (F : (Consumptions.done hSI hSO : Consumptions I O SIn SOut SI SO).fillValues → ℂ) :
    ∑ v : (Consumptions.done hSI hSO : Consumptions I O SIn SOut SI SO).fillValues, F v =
      F PUnit.unit := by
  have hsub : Subsingleton
      (Consumptions.done hSI hSO : Consumptions I O SIn SOut SI SO).fillValues :=
    inferInstanceAs (Subsingleton PUnit)
  exact Fintype.sum_subsingleton F PUnit.unit

/-- A sum over the consumed values of an extended sequence splits along the
recursive product into the earlier values and the newly consumed value. -/
theorem fillValues_sum_cons {SIn SOut SI SO : List (Fin n)} [∀ j, Fintype (O j)]
    {a b : Fin n} {hab : a < b}
    {e : (consumeList O SO) a ≃ (consumeList I SI) b}
    {rest : Consumptions I O SIn SOut (b :: SI) (a :: SO)}
    (F : (Consumptions.cons a b hab e rest).fillValues → ℂ) :
    ∑ v : (Consumptions.cons a b hab e rest).fillValues, F v =
      ∑ x : rest.fillValues, ∑ y : (consumeList O SO) a, F (x, y) :=
  Fintype.sum_prod_type F


theorem run_apply {SIn SOut SI SO : List (Fin n)} [∀ j, Fintype (O j)]
    (c : Consumptions I O SIn SOut SI SO)
    (p q : Space (consumeList I SIn) (consumeList O SOut)) :
    ∀ (T : CMatrix (Space (consumeList I SI) (consumeList O SO))),
      (c.run T) p q = ∑ v : c.fillValues, ∑ v' : c.fillValues,
        T (c.fillIn v p.1, c.fillOut v p.2) (c.fillIn v' q.1, c.fillOut v' q.2) := by
  induction c with
  | @done SI SO hSI hSO =>
      intro T
      simp only [run, matReindex_apply, spaceEquiv_symm_apply, piCongrRight_symm,
        fillIn, fillOut]
      rw [fillValues_sum_done, fillValues_sum_done]
  | @cons SI SO a b hab e rest ih =>
      intro T
      show (rest.run (matReindex (spaceEquiv
        (fun j => Equiv.cast (congrFun (erasePort_consumeList I SI b) j))
        (fun j => Equiv.cast (congrFun (erasePort_consumeList O SO a) j)))
        (forwardContraction a b e T))) p q = _
      rw [ih]
      simp only [matReindex_apply, spaceEquiv_symm_apply, piCongrRight_symm,
        forwardContraction_apply, fillIn, fillOut]
      have hswap : ∀ v : rest.fillValues,
          (∑ v' : rest.fillValues, ∑ z : (consumeList O SO) a, ∑ z' : (consumeList O SO) a,
              T (fillPort (consumeList I SI) b
                  ((Equiv.piCongrRight fun t =>
                    (Equiv.cast (congrFun (erasePort_consumeList I SI b) t)).symm)
                    (rest.fillIn v p.1)) (e z),
                fillPort (consumeList O SO) a
                  ((Equiv.piCongrRight fun t =>
                    (Equiv.cast (congrFun (erasePort_consumeList O SO a) t)).symm)
                    (rest.fillOut v p.2)) z)
            (fillPort (consumeList I SI) b
                ((Equiv.piCongrRight fun t =>
                  (Equiv.cast (congrFun (erasePort_consumeList I SI b) t)).symm)
                  (rest.fillIn v' q.1)) (e z'),
              fillPort (consumeList O SO) a
                ((Equiv.piCongrRight fun t =>
                  (Equiv.cast (congrFun (erasePort_consumeList O SO a) t)).symm)
                  (rest.fillOut v' q.2)) z')) =
          (∑ z : (consumeList O SO) a, ∑ v' : rest.fillValues, ∑ z' : (consumeList O SO) a,
              T (fillPort (consumeList I SI) b
                  ((Equiv.piCongrRight fun t =>
                    (Equiv.cast (congrFun (erasePort_consumeList I SI b) t)).symm)
                    (rest.fillIn v p.1)) (e z),
                fillPort (consumeList O SO) a
                  ((Equiv.piCongrRight fun t =>
                    (Equiv.cast (congrFun (erasePort_consumeList O SO a) t)).symm)
                    (rest.fillOut v p.2)) z)
            (fillPort (consumeList I SI) b
                ((Equiv.piCongrRight fun t =>
                  (Equiv.cast (congrFun (erasePort_consumeList I SI b) t)).symm)
                  (rest.fillIn v' q.1)) (e z'),
              fillPort (consumeList O SO) a
                ((Equiv.piCongrRight fun t =>
                  (Equiv.cast (congrFun (erasePort_consumeList O SO a) t)).symm)
                  (rest.fillOut v' q.2)) z')) :=
        fun v => Finset.sum_comm
      simp only [hswap]
      simp only [fillValues_sum_cons]

/-! ### Reduction and value packs of list-built sequences -/

/-- The consumed output values of a list-built sequence, repacked in list
order at the original output wires. -/
def ofListAux_valuesEquiv {SIn SOut : List (Fin n)} :
    (SI SO : List (Fin n)) → (cs : List (Connection I O)) →
    (hdisIn : (cs.map Connection.b).Nodup) →
    (hdisOut : (cs.map Connection.a).Nodup) →
    (hfresh : ∀ c ∈ cs, c.a ∉ SO ∧ c.b ∉ SI) →
    (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c ∈ cs, c.b = t) →
    (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c ∈ cs, c.a = t) →
    (ofListAux SIn SOut SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut).fillValues ≃
      (∀ i : Fin cs.length, O ((cs.get i).a))
  | _, _, [], _, _, _, _, _ => by
      show PUnit ≃ (∀ i : Fin ([] : List (Connection I O)).length,
        O ((([] : List (Connection I O)).get i).a))
      exact ⟨fun _ i => Fin.elim0 i, fun _ => PUnit.unit,
        fun _ => Subsingleton.elim _ _,
        fun f => funext fun i => absurd i.isLt (Nat.not_lt_zero _)⟩
  | SI, SO, c :: cs, hdisIn, hdisOut, hfresh, hcoverIn, hcoverOut => by
      have ih' : (ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
          ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
                  (by
                    intro c' hc'
                    have hf := hfresh c' (by simp [hc'])
                    refine ⟨?_, ?_⟩
                    · intro hmem
                      rcases List.mem_cons.1 hmem with h | h
                      · exact (List.nodup_cons.1 hdisOut).1
                          (h ▸ (List.mem_map.2 ⟨c', hc', rfl⟩))
                      · exact hf.1 h
                    · intro hmem
                      rcases List.mem_cons.1 hmem with h | h
                      · exact (List.nodup_cons.1 hdisIn).1
                          (h ▸ (List.mem_map.2 ⟨c', hc', rfl⟩))
                      · exact hf.2 h)
                  (by
                    intro t
                    rw [List.mem_cons]
                    constructor
                    · intro ht
                      rcases (hcoverIn t).mp ht with hSI | ⟨c', hc', hcb'⟩
                      · exact Or.inl (Or.inr hSI)
                      · rcases List.mem_cons.1 hc' with rfl | hc'
                        · exact Or.inl (Or.inl hcb'.symm)
                        · exact Or.inr ⟨c', hc', hcb'⟩
                    · intro ht
                      rcases ht with ht | ⟨c', hc', hcb'⟩
                      · rcases ht with ht | hSI
                        · exact (hcoverIn t).mpr
                            (Or.inr ⟨c, List.mem_cons.2 (Or.inl rfl), ht.symm⟩)
                        · exact (hcoverIn t).mpr (Or.inl hSI)
                      · exact (hcoverIn t).mpr
                          (Or.inr ⟨c', List.mem_cons.2 (Or.inr hc'), hcb'⟩))
                  (by
                    intro t
                    rw [List.mem_cons]
                    constructor
                    · intro ht
                      rcases (hcoverOut t).mp ht with hSO | ⟨c', hc', hca'⟩
                      · exact Or.inl (Or.inr hSO)
                      · rcases List.mem_cons.1 hc' with rfl | hc'
                        · exact Or.inl (Or.inl hca'.symm)
                        · exact Or.inr ⟨c', hc', hca'⟩
                    · intro ht
                      rcases ht with ht | ⟨c', hc', hca'⟩
                      · rcases ht with ht | hSO
                        · exact (hcoverOut t).mpr
                            (Or.inr ⟨c, List.mem_cons.2 (Or.inl rfl), ht.symm⟩)
                        · exact (hcoverOut t).mpr (Or.inl hSO)
                      · exact (hcoverOut t).mpr
                          (Or.inr ⟨c', List.mem_cons.2 (Or.inr hc'), hca'⟩))).fillValues ≃
          (∀ i : Fin cs.length, O ((cs.get i).a)) :=
        ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _
      exact (Equiv.refl _).trans
        ((ih'.prodCongr
          (Equiv.cast (consumeList_apply_not_mem O SO c.a ((hfresh c (by simp)).1)))).trans
        ((Equiv.prodComm _ _).trans
          (Fin.consEquiv
            (fun i : Fin ((c :: cs).length) => O ((c :: cs).get i).a))))

private theorem cast_comp {α β γ : Type u} (h₁ : α = β) (h₂ : β = γ) (x : α) :
    cast h₂ (cast h₁ x) = cast (h₁.trans h₂) x := by
  cases h₁; cases h₂; rfl

private theorem cast_symm_cancel {α β : Type u} (h : α = β) (x : β) :
    cast h (cast h.symm x) = x := by
  cases h; rfl

private theorem cast_eq_of_eq {α β : Type u} (h₁ h₂ : α = β) (x : α) :
    cast h₁ x = cast h₂ x := by
  rw [Subsingleton.elim h₁ h₂]

/-- Reading the repacked value list backward splits at the head connection: the
tail reconstructs the shorter sequence's value pack and the head entry is the
newly consumed output value at its own wire family. -/
private theorem ofListAux_valuesEquiv_symm_cons {SIn SOut : List (Fin n)}
    (c : Connection I O) (cs : List (Connection I O)) (SI SO : List (Fin n))
    (hdisIn : ((c :: cs).map Connection.b).Nodup)
    (hdisOut : ((c :: cs).map Connection.a).Nodup)
    (hfresh : ∀ c' ∈ c :: cs, c'.a ∉ SO ∧ c'.b ∉ SI)
    (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c' ∈ c :: cs, c'.b = t)
    (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c' ∈ c :: cs, c'.a = t)
    (z : ∀ i : Fin (c :: cs).length, O ((c :: cs).get i).a) :
    (ofListAux_valuesEquiv SI SO (c :: cs) hdisIn hdisOut hfresh hcoverIn
        hcoverOut).symm z =
      ((ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _).symm
          (Fin.tail z),
        cast (consumeList_apply_not_mem O SO c.a ((hfresh c (by simp)).1)).symm (z 0)) := by
  simp only [ofListAux_valuesEquiv]
  rfl

/-- Boundary readback on inputs: at a position outside the consumed input list
that is not itself a consumed input, restoring the configuration returns the
boundary value unchanged. -/
theorem ofListAux_fillIn_not_mem {SIn SOut : List (Fin n)} :
    ∀ (SI SO : List (Fin n)) (cs : List (Connection I O))
      (hdisIn : (cs.map Connection.b).Nodup) (hdisOut : (cs.map Connection.a).Nodup)
      (hfresh : ∀ c ∈ cs, c.a ∉ SO ∧ c.b ∉ SI)
      (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c ∈ cs, c.b = t)
      (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c ∈ cs, c.a = t)
      (t : Fin n) (ht1 : t ∉ SI) (ht2 : t ∉ cs.map Connection.b)
      (v : (ofListAux SIn SOut SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut).fillValues)
      (p : ∀ t, consumeList I SIn t),
    (ofListAux SIn SOut SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut).fillIn v p t =
      cast ((consumeList_apply_not_mem I SIn t
          (fun hmem => ((hcoverIn t).mp hmem).elim ht1
            (fun ⟨c, hc, hcb⟩ => ht2 (List.mem_map.2 ⟨c, hc, hcb⟩)))).trans
        (consumeList_apply_not_mem I SI t ht1).symm) (p t) := by
  intro SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut
  induction cs generalizing SI SO with
  | nil =>
      intro t ht1 ht2 v p
      simp only [ofListAux, fillIn]
      exact cast_eq_of_eq _ _ _
  | cons c cs ih =>
      intro t ht1 ht2 v p
      have htb : t ≠ c.b := fun h => ht2 (List.mem_cons.2 (Or.inl h))
      have ht2' : t ∉ cs.map Connection.b := fun h => ht2 (List.mem_cons.2 (Or.inr h))
      have ht1' : t ∉ c.b :: SI := fun h =>
        (List.mem_cons.1 h).elim (fun hcb => htb hcb) ht1
      have htbne : t.val ≠ c.b.val := fun h => htb (Fin.ext h)
      show fillPort (consumeList I SI) c.b
          ((Equiv.piCongrRight fun t' =>
            (Equiv.cast (congrFun (erasePort_consumeList I SI c.b) t')).symm)
            ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
              ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
              (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
              (ofListAuxCoverIn c cs SIn SI hcoverIn)
              (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillIn v.1 p))
          (((Equiv.cast (consumeList_apply_not_mem O SO c.a
            ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1))).trans
            (c.e.trans (Equiv.cast (consumeList_apply_not_mem I SI c.b
              ((hfresh c (List.mem_cons.2 (Or.inl rfl))).2)).symm))) v.2) t = _
      rw [fillPort_of_ne (consumeList I SI) c.b t _ _ htbne]
      show cast (by simp [erasePort, htbne])
          (cast (congrFun (erasePort_consumeList I SI c.b) t).symm
            ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
              ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
              (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
              (ofListAuxCoverIn c cs SIn SI hcoverIn)
              (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillIn v.1 p t)) = _
      rw [ih (c.b :: SI) (c.a :: SO)
        ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
        (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
        (ofListAuxCoverIn c cs SIn SI hcoverIn)
        (ofListAuxCoverOut c cs SOut SO hcoverOut) t ht1' ht2' v.1 p]
      rw [cast_comp, cast_comp]

/-- Boundary readback on outputs: at a position outside the consumed output list
that is not itself a consumed output, restoring the configuration returns the
boundary value unchanged. -/
theorem ofListAux_fillOut_not_mem {SIn SOut : List (Fin n)} :
    ∀ (SI SO : List (Fin n)) (cs : List (Connection I O))
      (hdisIn : (cs.map Connection.b).Nodup) (hdisOut : (cs.map Connection.a).Nodup)
      (hfresh : ∀ c ∈ cs, c.a ∉ SO ∧ c.b ∉ SI)
      (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c ∈ cs, c.b = t)
      (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c ∈ cs, c.a = t)
      (t : Fin n) (ht1 : t ∉ SO) (ht2 : t ∉ cs.map Connection.a)
      (v : (ofListAux SIn SOut SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut).fillValues)
      (p : ∀ t, consumeList O SOut t),
    (ofListAux SIn SOut SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut).fillOut v p t =
      cast ((consumeList_apply_not_mem O SOut t
          (fun hmem => ((hcoverOut t).mp hmem).elim ht1
            (fun ⟨c, hc, hca⟩ => ht2 (List.mem_map.2 ⟨c, hc, hca⟩)))).trans
        (consumeList_apply_not_mem O SO t ht1).symm) (p t) := by
  intro SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut
  induction cs generalizing SI SO with
  | nil =>
      intro t ht1 ht2 v p
      simp only [ofListAux, fillOut]
      exact cast_eq_of_eq _ _ _
  | cons c cs ih =>
      intro t ht1 ht2 v p
      have hta : t ≠ c.a := fun h => ht2 (List.mem_cons.2 (Or.inl h))
      have ht2' : t ∉ cs.map Connection.a := fun h => ht2 (List.mem_cons.2 (Or.inr h))
      have ht1' : t ∉ c.a :: SO := fun h =>
        (List.mem_cons.1 h).elim (fun hca => hta hca) ht1
      have htane : t.val ≠ c.a.val := fun h => hta (Fin.ext h)
      show fillPort (consumeList O SO) c.a
          ((Equiv.piCongrRight fun t' =>
            (Equiv.cast (congrFun (erasePort_consumeList O SO c.a) t')).symm)
            ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
              ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
              (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
              (ofListAuxCoverIn c cs SIn SI hcoverIn)
              (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillOut v.1 p))
          v.2 t = _
      rw [fillPort_of_ne (consumeList O SO) c.a t _ _ htane]
      show cast (by simp [erasePort, htane])
          (cast (congrFun (erasePort_consumeList O SO c.a) t).symm
            ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
              ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
              (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
              (ofListAuxCoverIn c cs SIn SI hcoverIn)
              (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillOut v.1 p t)) = _
      rw [ih (c.b :: SI) (c.a :: SO)
        ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
        (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
        (ofListAuxCoverIn c cs SIn SI hcoverIn)
        (ofListAuxCoverOut c cs SOut SO hcoverOut) t ht1' ht2' v.1 p]
      rw [cast_comp, cast_comp]

/-- Consumed-position readback on inputs: at the consumed input position of the
`i`-th connection, restoring the configuration reads the connection's basis
equivalence applied to the `i`-th repacked consumed output value. -/
theorem ofListAux_fillIn_get {SIn SOut : List (Fin n)} :
    ∀ (SI SO : List (Fin n)) (cs : List (Connection I O))
      (hdisIn : (cs.map Connection.b).Nodup) (hdisOut : (cs.map Connection.a).Nodup)
      (hfresh : ∀ c ∈ cs, c.a ∉ SO ∧ c.b ∉ SI)
      (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c ∈ cs, c.b = t)
      (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c ∈ cs, c.a = t)
      (i : Fin cs.length)
      (z : ∀ i' : Fin cs.length, O ((cs.get i').a))
      (p : ∀ t, consumeList I SIn t),
    (ofListAux SIn SOut SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut).fillIn
        ((ofListAux_valuesEquiv SI SO cs hdisIn hdisOut hfresh hcoverIn
          hcoverOut).symm z) p ((cs.get i).b) =
      cast ((consumeList_apply_not_mem I SI ((cs.get i).b)
          ((hfresh (cs.get i) (List.getElem_mem i.isLt)).2)).symm)
        ((cs.get i).e (z i)) := by
  intro SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut
  induction cs generalizing SI SO with
  | nil => intro i; exact absurd i.isLt (Nat.not_lt_zero _)
  | cons c cs ih =>
      intro i z p
      have hG3 := ofListAux_valuesEquiv_symm_cons c cs SI SO hdisIn hdisOut hfresh
        hcoverIn hcoverOut z
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
      · show (ofListAux SIn SOut SI SO (c :: cs) hdisIn hdisOut hfresh hcoverIn
            hcoverOut).fillIn ((ofListAux_valuesEquiv SI SO (c :: cs) hdisIn
            hdisOut hfresh hcoverIn hcoverOut).symm z) p c.b =
          cast ((consumeList_apply_not_mem I SI c.b
            ((hfresh c (List.mem_cons.2 (Or.inl rfl))).2)).symm) (c.e (z 0))
        rw [hG3]
        show fillPort (consumeList I SI) c.b
            ((Equiv.piCongrRight fun t' =>
              (Equiv.cast (congrFun (erasePort_consumeList I SI c.b) t')).symm)
              ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
                ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
                (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
                (ofListAuxCoverIn c cs SIn SI hcoverIn)
                (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillIn
                ((ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _).symm
                  (Fin.tail z)) p))
            (((Equiv.cast (consumeList_apply_not_mem O SO c.a
              ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1))).trans
              (c.e.trans (Equiv.cast (consumeList_apply_not_mem I SI c.b
                ((hfresh c (List.mem_cons.2 (Or.inl rfl))).2)).symm)))
              (cast (consumeList_apply_not_mem O SO c.a
                ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1)).symm (z 0))) c.b = _
        rw [fillPort_at]
        rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.cast_apply, Equiv.cast_apply]
        exact congrArg (cast ((consumeList_apply_not_mem I SI c.b
          ((hfresh c (List.mem_cons.2 (Or.inl rfl))).2)).symm))
            (congrArg c.e (cast_symm_cancel _ _))
      · have hnk : (cs.get k).b ≠ c.b := fun h =>
          (List.nodup_cons.1 hdisIn).1 (by
            rw [← h]
            exact List.mem_map.2 ⟨cs.get k, List.getElem_mem k.isLt, rfl⟩)
        have hnkne : (cs.get k).b.val ≠ c.b.val := fun h => hnk (Fin.ext h)
        show (ofListAux SIn SOut SI SO (c :: cs) hdisIn hdisOut hfresh hcoverIn
            hcoverOut).fillIn ((ofListAux_valuesEquiv SI SO (c :: cs) hdisIn
            hdisOut hfresh hcoverIn hcoverOut).symm z) p (cs.get k).b =
          cast ((consumeList_apply_not_mem I SI (cs.get k).b
            ((hfresh (cs.get k) (List.mem_cons.2 (Or.inr (List.getElem_mem k.isLt)))).2)).symm)
            ((cs.get k).e (z k.succ))
        rw [hG3]
        show fillPort (consumeList I SI) c.b
            ((Equiv.piCongrRight fun t' =>
              (Equiv.cast (congrFun (erasePort_consumeList I SI c.b) t')).symm)
              ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
                ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
                (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
                (ofListAuxCoverIn c cs SIn SI hcoverIn)
                (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillIn
                ((ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _).symm
                  (Fin.tail z)) p))
            (((Equiv.cast (consumeList_apply_not_mem O SO c.a
              ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1))).trans
              (c.e.trans (Equiv.cast (consumeList_apply_not_mem I SI c.b
                ((hfresh c (List.mem_cons.2 (Or.inl rfl))).2)).symm)))
              (cast (consumeList_apply_not_mem O SO c.a
                ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1)).symm (z 0)))
            (cs.get k).b = _
        rw [fillPort_of_ne (consumeList I SI) c.b (cs.get k).b _ _ hnkne]
        have hEq : erasePort (consumeList I SI) c.b.val (cs.get k).b =
            consumeList I SI (cs.get k).b := by
          unfold erasePort
          split
          · exact absurd (by assumption) hnkne
          · rfl
        show cast hEq
            (cast (congrFun (erasePort_consumeList I SI c.b) (cs.get k).b).symm
              ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
                ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
                (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
                (ofListAuxCoverIn c cs SIn SI hcoverIn)
                (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillIn
                ((ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _).symm
                  (Fin.tail z)) p (cs.get k).b)) = _
        rw [ih (c.b :: SI) (c.a :: SO)
          ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
          (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
          (ofListAuxCoverIn c cs SIn SI hcoverIn)
          (ofListAuxCoverOut c cs SOut SO hcoverOut) k (Fin.tail z) p]
        rw [cast_comp, cast_comp]
        rfl

/-- Consumed-position readback on outputs: at the consumed output position of
the `i`-th connection, restoring the configuration returns the `i`-th repacked
consumed output value at its own wire family. -/
theorem ofListAux_fillOut_get {SIn SOut : List (Fin n)} :
    ∀ (SI SO : List (Fin n)) (cs : List (Connection I O))
      (hdisIn : (cs.map Connection.b).Nodup) (hdisOut : (cs.map Connection.a).Nodup)
      (hfresh : ∀ c ∈ cs, c.a ∉ SO ∧ c.b ∉ SI)
      (hcoverIn : ∀ t, t ∈ SIn ↔ t ∈ SI ∨ ∃ c ∈ cs, c.b = t)
      (hcoverOut : ∀ t, t ∈ SOut ↔ t ∈ SO ∨ ∃ c ∈ cs, c.a = t)
      (i : Fin cs.length)
      (z : ∀ i' : Fin cs.length, O ((cs.get i').a))
      (p : ∀ t, consumeList O SOut t),
    (ofListAux SIn SOut SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut).fillOut
        ((ofListAux_valuesEquiv SI SO cs hdisIn hdisOut hfresh hcoverIn
          hcoverOut).symm z) p ((cs.get i).a) =
      cast ((consumeList_apply_not_mem O SO ((cs.get i).a)
          ((hfresh (cs.get i) (List.getElem_mem i.isLt)).1)).symm) (z i) := by
  intro SI SO cs hdisIn hdisOut hfresh hcoverIn hcoverOut
  induction cs generalizing SI SO with
  | nil => intro i; exact absurd i.isLt (Nat.not_lt_zero _)
  | cons c cs ih =>
      intro i z p
      have hG3 := ofListAux_valuesEquiv_symm_cons c cs SI SO hdisIn hdisOut hfresh
        hcoverIn hcoverOut z
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
      · show (ofListAux SIn SOut SI SO (c :: cs) hdisIn hdisOut hfresh hcoverIn
            hcoverOut).fillOut ((ofListAux_valuesEquiv SI SO (c :: cs) hdisIn
            hdisOut hfresh hcoverIn hcoverOut).symm z) p c.a =
          cast ((consumeList_apply_not_mem O SO c.a
            ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1)).symm) (z 0)
        rw [hG3]
        show fillPort (consumeList O SO) c.a
            ((Equiv.piCongrRight fun t' =>
              (Equiv.cast (congrFun (erasePort_consumeList O SO c.a) t')).symm)
              ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
                ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
                (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
                (ofListAuxCoverIn c cs SIn SI hcoverIn)
                (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillOut
                ((ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _).symm
                  (Fin.tail z)) p))
            (cast (consumeList_apply_not_mem O SO c.a
              ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1)).symm (z 0)) c.a = _
        rw [fillPort_at]
      · have hnk : (cs.get k).a ≠ c.a := fun h =>
          (List.nodup_cons.1 hdisOut).1 (by
            rw [← h]
            exact List.mem_map.2 ⟨cs.get k, List.getElem_mem k.isLt, rfl⟩)
        have hnkne : (cs.get k).a.val ≠ c.a.val := fun h => hnk (Fin.ext h)
        show (ofListAux SIn SOut SI SO (c :: cs) hdisIn hdisOut hfresh hcoverIn
            hcoverOut).fillOut ((ofListAux_valuesEquiv SI SO (c :: cs) hdisIn
            hdisOut hfresh hcoverIn hcoverOut).symm z) p (cs.get k).a =
          cast ((consumeList_apply_not_mem O SO (cs.get k).a
            ((hfresh (cs.get k) (List.mem_cons.2 (Or.inr (List.getElem_mem k.isLt)))).1)).symm) (z k.succ)
        rw [hG3]
        show fillPort (consumeList O SO) c.a
            ((Equiv.piCongrRight fun t' =>
              (Equiv.cast (congrFun (erasePort_consumeList O SO c.a) t')).symm)
              ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
                ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
                (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
                (ofListAuxCoverIn c cs SIn SI hcoverIn)
                (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillOut
                ((ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _).symm
                  (Fin.tail z)) p))
            (cast (consumeList_apply_not_mem O SO c.a
              ((hfresh c (List.mem_cons.2 (Or.inl rfl))).1)).symm (z 0))
            (cs.get k).a = _
        rw [fillPort_of_ne (consumeList O SO) c.a (cs.get k).a _ _ hnkne]
        have hEq : erasePort (consumeList O SO) c.a.val (cs.get k).a =
            consumeList O SO (cs.get k).a := by
          unfold erasePort
          split
          · exact absurd (by assumption) hnkne
          · rfl
        show cast hEq
            (cast (congrFun (erasePort_consumeList O SO c.a) (cs.get k).a).symm
              ((ofListAux SIn SOut (c.b :: SI) (c.a :: SO) cs
                ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
                (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
                (ofListAuxCoverIn c cs SIn SI hcoverIn)
                (ofListAuxCoverOut c cs SOut SO hcoverOut)).fillOut
                ((ofListAux_valuesEquiv (c.b :: SI) (c.a :: SO) cs _ _ _ _ _).symm
                  (Fin.tail z)) p (cs.get k).a)) = _
        rw [ih (c.b :: SI) (c.a :: SO)
          ((List.nodup_cons.1 hdisIn).2) ((List.nodup_cons.1 hdisOut).2)
          (ofListAuxFresh c cs SI SO hdisIn hdisOut hfresh)
          (ofListAuxCoverIn c cs SIn SI hcoverIn)
          (ofListAuxCoverOut c cs SOut SO hcoverOut) k (Fin.tail z) p]
        rw [cast_comp, cast_comp]
        rfl

end Consumptions

namespace CausalJoin

variable {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}

/-- All connections of a causal join as forward connections on the joint
scheduled family, first comb to second comb first. -/
def connections (j : CausalJoin I O P Q) :
    List (Connection (j.schedule.family I P) (j.schedule.family O Q)) :=
  (List.finRange j.ab).map (fun k =>
    { a := j.schedule.leftRank (j.outA k)
      b := j.schedule.rightRank (j.inB k)
      hab := j.forwardAB k
      e := (j.schedule.leftFamilyEquiv O Q (j.outA k)).symm.trans
        ((j.equivAB k).trans (j.schedule.rightFamilyEquiv I P (j.inB k))) } :
      Fin j.ab → Connection (j.schedule.family I P) (j.schedule.family O Q))
  ++ (List.finRange j.ba).map (fun l =>
    { a := j.schedule.rightRank (j.outB l)
      b := j.schedule.leftRank (j.inA l)
      hab := j.forwardBA l
      e := (j.schedule.rightFamilyEquiv O Q (j.outB l)).symm.trans
        ((j.equivBA l).trans (j.schedule.leftFamilyEquiv I P (j.inA l))) } :
      Fin j.ba → Connection (j.schedule.family I P) (j.schedule.family O Q))

theorem connections_disIn (j : CausalJoin I O P Q) :
    (j.connections.map Connection.b).Nodup := by
  have h1 : j.connections.map Connection.b =
      (List.finRange j.ab).map (fun k => j.schedule.rightRank (j.inB k)) ++
      (List.finRange j.ba).map (fun l => j.schedule.leftRank (j.inA l)) := by
    simp only [connections, List.map_append, List.map_map]
    rfl
  rw [h1]
  refine List.Nodup.append ?_ ?_ ?_
  · exact List.Nodup.map
      (fun k k' h => j.inB_injective (j.schedule.rightRank_injective h))
      (List.nodup_finRange j.ab)
  · exact List.Nodup.map
      (fun k k' h => j.inA_injective (j.schedule.leftRank_injective h))
      (List.nodup_finRange j.ba)
  · intro x hx hy
    rw [List.mem_map] at hx hy
    obtain ⟨k, _, hk⟩ := hx
    obtain ⟨l, _, hl⟩ := hy
    exact j.schedule.leftRank_ne_rightRank _ _ (hl.trans hk.symm)

theorem connections_disOut (j : CausalJoin I O P Q) :
    (j.connections.map Connection.a).Nodup := by
  have h1 : j.connections.map Connection.a =
      (List.finRange j.ab).map (fun k => j.schedule.leftRank (j.outA k)) ++
      (List.finRange j.ba).map (fun l => j.schedule.rightRank (j.outB l)) := by
    simp only [connections, List.map_append, List.map_map]
    rfl
  rw [h1]
  refine List.Nodup.append ?_ ?_ ?_
  · exact List.Nodup.map
      (fun k k' h => j.outA_injective (j.schedule.leftRank_injective h))
      (List.nodup_finRange j.ab)
  · exact List.Nodup.map
      (fun k k' h => j.outB_injective (j.schedule.rightRank_injective h))
      (List.nodup_finRange j.ba)
  · intro x hx hy
    rw [List.mem_map] at hx hy
    obtain ⟨k, _, hk⟩ := hx
    obtain ⟨l, _, hl⟩ := hy
    exact j.schedule.leftRank_ne_rightRank _ _ (hk.trans hl.symm)

/-- The join's connections as an iterated forward contraction on the scheduled
tensor family, consuming exactly the join's connected input and output
positions. -/
def consumptions (j : CausalJoin I O P Q) :
    Consumptions (j.schedule.family I P) (j.schedule.family O Q)
      (j.connections.map Connection.b) (j.connections.map Connection.a) [] [] :=
  Consumptions.ofList j.connections j.connections_disIn j.connections_disOut

/-- The input positions consumed by the join's connections are exactly the
scheduled events whose input is matched. -/
theorem connections_mem_b (j : CausalJoin I O P Q) (t : Fin (nA + nB)) :
    t ∈ j.connections.map Connection.b ↔ j.inputConnected t := by
  have h1 : j.connections.map Connection.b =
      (List.finRange j.ab).map (fun k => j.schedule.rightRank (j.inB k)) ++
      (List.finRange j.ba).map (fun l => j.schedule.leftRank (j.inA l)) := by
    simp only [connections, List.map_append, List.map_map]
    rfl
  rw [h1, List.mem_append]
  constructor
  · rintro (h | h)
    · rw [List.mem_map] at h
      obtain ⟨k, _, hk⟩ := h
      rw [← hk]
      simp [inputConnected]
    · rw [List.mem_map] at h
      obtain ⟨l, _, hl⟩ := h
      rw [← hl]
      simp [inputConnected]
  · intro hconn
    cases h : j.schedule.order t with
    | inl i =>
        have ht : j.schedule.leftRank i = t := by
          rw [show j.schedule.leftRank i = j.schedule.order.symm (Sum.inl i) from rfl, ← h,
          Equiv.symm_apply_apply]
        have hconn' : j.inputConnected (j.schedule.leftRank i) := by
          rw [ht]; exact hconn
        have hi : i ∈ Set.range j.inA := by
          simpa [inputConnected] using hconn'
        obtain ⟨l, hl⟩ := Set.mem_range.mp hi
        refine Or.inr (List.mem_map.2 ⟨l, List.mem_finRange l, ?_⟩)
        rw [hl]; exact ht
    | inr i =>
        have ht : j.schedule.rightRank i = t := by
          rw [show j.schedule.rightRank i = j.schedule.order.symm (Sum.inr i) from rfl, ← h,
          Equiv.symm_apply_apply]
        have hconn' : j.inputConnected (j.schedule.rightRank i) := by
          rw [ht]; exact hconn
        have hi : i ∈ Set.range j.inB := by
          simpa [inputConnected] using hconn'
        obtain ⟨k, hk⟩ := Set.mem_range.mp hi
        refine Or.inl (List.mem_map.2 ⟨k, List.mem_finRange k, ?_⟩)
        rw [hk]; exact ht

/-- The output positions consumed by the join's connections are exactly the
scheduled events whose output is matched. -/
theorem connections_mem_a (j : CausalJoin I O P Q) (t : Fin (nA + nB)) :
    t ∈ j.connections.map Connection.a ↔ j.outputConnected t := by
  have h1 : j.connections.map Connection.a =
      (List.finRange j.ab).map (fun k => j.schedule.leftRank (j.outA k)) ++
      (List.finRange j.ba).map (fun l => j.schedule.rightRank (j.outB l)) := by
    simp only [connections, List.map_append, List.map_map]
    rfl
  rw [h1, List.mem_append]
  constructor
  · rintro (h | h)
    · rw [List.mem_map] at h
      obtain ⟨k, _, hk⟩ := h
      rw [← hk]
      simp [outputConnected]
    · rw [List.mem_map] at h
      obtain ⟨l, _, hl⟩ := h
      rw [← hl]
      simp [outputConnected]
  · intro hconn
    cases h : j.schedule.order t with
    | inl i =>
        have ht : j.schedule.leftRank i = t := by
          rw [show j.schedule.leftRank i = j.schedule.order.symm (Sum.inl i) from rfl, ← h,
          Equiv.symm_apply_apply]
        have hconn' : j.outputConnected (j.schedule.leftRank i) := by
          rw [ht]; exact hconn
        have hi : i ∈ Set.range j.outA := by
          simpa [outputConnected] using hconn'
        obtain ⟨k, hk⟩ := Set.mem_range.mp hi
        refine Or.inl (List.mem_map.2 ⟨k, List.mem_finRange k, ?_⟩)
        rw [hk]; exact ht
    | inr i =>
        have ht : j.schedule.rightRank i = t := by
          rw [show j.schedule.rightRank i = j.schedule.order.symm (Sum.inr i) from rfl, ← h,
          Equiv.symm_apply_apply]
        have hconn' : j.outputConnected (j.schedule.rightRank i) := by
          rw [ht]; exact hconn
        have hi : i ∈ Set.range j.outB := by
          simpa [outputConnected] using hconn'
        obtain ⟨l, hl⟩ := Set.mem_range.mp hi
        refine Or.inr (List.mem_map.2 ⟨l, List.mem_finRange l, ?_⟩)
        rw [hl]; exact ht

/-- The iterated contraction's end input family is the join's scheduled input
boundary. -/
theorem consumeList_connections_input (j : CausalJoin I O P Q) :
    consumeList (j.schedule.family I P) (j.connections.map Connection.b) =
      j.boundaryInput := by
  funext t
  have hm := connections_mem_b j t
  cases h : j.schedule.order t with
  | inl i =>
      have ht : j.schedule.leftRank i = t := by
        rw [show j.schedule.leftRank i = j.schedule.order.symm (Sum.inl i) from rfl, ← h,
          Equiv.symm_apply_apply]
      by_cases hi : ∃ y, j.inA y = i
      · have hmem : t ∈ j.connections.map Connection.b := by
          refine hm.mpr ?_
          rw [← ht]; simpa [inputConnected] using Set.mem_range.2 hi
        simp [consumeList, hmem, boundaryInput, padded, hi, h]
      · have hmem : t ∉ j.connections.map Connection.b := fun hc => hi (Set.mem_range.1 (by
          have hconn := hm.mp hc
          rw [← ht] at hconn
          simpa [inputConnected] using hconn))
        simp [consumeList, hmem, boundaryInput, padded, hi, EventSchedule.family, h]
  | inr i =>
      have ht : j.schedule.rightRank i = t := by
        rw [show j.schedule.rightRank i = j.schedule.order.symm (Sum.inr i) from rfl, ← h,
          Equiv.symm_apply_apply]
      by_cases hi : ∃ y, j.inB y = i
      · have hmem : t ∈ j.connections.map Connection.b := by
          refine hm.mpr ?_
          rw [← ht]; simpa [inputConnected] using Set.mem_range.2 hi
        simp [consumeList, hmem, boundaryInput, padded, hi, h]
      · have hmem : t ∉ j.connections.map Connection.b := fun hc => hi (Set.mem_range.1 (by
          have hconn := hm.mp hc
          rw [← ht] at hconn
          simpa [inputConnected] using hconn))
        simp [consumeList, hmem, boundaryInput, padded, hi, EventSchedule.family, h]

/-- The iterated contraction's end output family is the join's scheduled
output boundary. -/
theorem consumeList_connections_output (j : CausalJoin I O P Q) :
    consumeList (j.schedule.family O Q) (j.connections.map Connection.a) =
      j.boundaryOutput := by
  funext t
  have hm := connections_mem_a j t
  cases h : j.schedule.order t with
  | inl i =>
      have ht : j.schedule.leftRank i = t := by
        rw [show j.schedule.leftRank i = j.schedule.order.symm (Sum.inl i) from rfl, ← h,
          Equiv.symm_apply_apply]
      by_cases hi : ∃ y, j.outA y = i
      · have hmem : t ∈ j.connections.map Connection.a := by
          refine hm.mpr ?_
          rw [← ht]; simpa [outputConnected] using Set.mem_range.2 hi
        simp [consumeList, hmem, boundaryOutput, padded, hi, h]
      · have hmem : t ∉ j.connections.map Connection.a := fun hc => hi (Set.mem_range.1 (by
          have hconn := hm.mp hc
          rw [← ht] at hconn
          simpa [outputConnected] using hconn))
        simp [consumeList, hmem, boundaryOutput, padded, hi, EventSchedule.family, h]
  | inr i =>
      have ht : j.schedule.rightRank i = t := by
        rw [show j.schedule.rightRank i = j.schedule.order.symm (Sum.inr i) from rfl, ← h,
          Equiv.symm_apply_apply]
      by_cases hi : ∃ y, j.outB y = i
      · have hmem : t ∈ j.connections.map Connection.a := by
          refine hm.mpr ?_
          rw [← ht]; simpa [outputConnected] using Set.mem_range.2 hi
        simp [consumeList, hmem, boundaryOutput, padded, hi, h]
      · have hmem : t ∉ j.connections.map Connection.a := fun hc => hi (Set.mem_range.1 (by
          have hconn := hm.mp hc
          rw [← ht] at hconn
          simpa [outputConnected] using hconn))
        simp [consumeList, hmem, boundaryOutput, padded, hi, EventSchedule.family, h]
/-- The connection list has one entry per matched pair, first comb to second
comb first. -/
theorem connections_length (j : CausalJoin I O P Q) :
    j.connections.length = j.ab + j.ba := by
  simp [connections]

/-- The first block of consumed output positions, in connection-list order. -/
theorem connections_a_castAdd (j : CausalJoin I O P Q) (k : Fin j.ab) :
    (j.connections.get
        (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k))).a =
      j.schedule.leftRank (j.outA k) := by
  have hv : (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k)).val = k.val := by
    simp
  have hlt : k.val < j.connections.length := by
    have h := connections_length j
    simp only [connections, List.length_append, List.length_map, List.length_finRange] at h ⊢
    omega
  rw [show Fin.cast (connections_length j).symm (Fin.castAdd j.ba k) = ⟨k.val, hlt⟩ from
    Fin.ext hv]
  simp [connections, List.length_map, List.length_finRange]

/-- The second block of consumed output positions, in connection-list order. -/
theorem connections_a_natAdd (j : CausalJoin I O P Q) (l : Fin j.ba) :
    (j.connections.get
        (Fin.cast (connections_length j).symm (Fin.natAdd j.ab l))).a =
      j.schedule.rightRank (j.outB l) := by
  have hv : (Fin.cast (connections_length j).symm (Fin.natAdd j.ab l)).val = j.ab + l.val := by
    simp
  have hlt : j.ab + l.val < j.connections.length := by
    have h := connections_length j
    simp only [connections, List.length_append, List.length_map, List.length_finRange] at h ⊢
    omega
  rw [show Fin.cast (connections_length j).symm (Fin.natAdd j.ab l) = ⟨j.ab + l.val, hlt⟩ from
    Fin.ext hv]
  simp [connections, List.length_map, List.length_finRange]

/-- The first block of the matching's connected first-comb wires carries the
first comb's matched outputs. -/
theorem connFam₁_castAdd (j : CausalJoin I O P Q) (k : Fin j.ab) :
    j.toWireJoin.toWireMatch.connFam₁ (Fin.castAdd j.ba k) = O (j.outA k) := by
  rw [show j.toWireJoin.toWireMatch.connFam₁ (Fin.castAdd j.ba k)
      = append I O (j.toWireJoin.toWireMatch.ι₁ (Fin.castAdd j.ba k)) from rfl,
    WireJoin.toWireMatch_outA, append_natAdd]

/-- The second block of the matching's connected first-comb wires carries the
first comb's matched inputs. -/
theorem connFam₁_natAdd (j : CausalJoin I O P Q) (l : Fin j.ba) :
    j.toWireJoin.toWireMatch.connFam₁ (Fin.natAdd j.ab l) = I (j.inA l) := by
  rw [show j.toWireJoin.toWireMatch.connFam₁ (Fin.natAdd j.ab l)
      = append I O (j.toWireJoin.toWireMatch.ι₁ (Fin.natAdd j.ab l)) from rfl,
    WireJoin.toWireMatch_inA, append_castAdd]

/-- The consumed output values of the join's iterated contraction, identified
with the matching's connected first-comb wires: the forward-connected outputs
and the backward-connected inputs. -/
def valuesJoinEquiv (j : CausalJoin I O P Q) :
    (∀ k : Fin (j.ab + j.ba), j.toWireJoin.toWireMatch.connFam₁ k) ≃
      j.consumptions.fillValues := by
  have e1 : (∀ k : Fin (j.ab + j.ba), j.toWireJoin.toWireMatch.connFam₁ k) ≃
      (∀ k : Fin j.ab, O (j.outA k)) × (∀ l : Fin j.ba, Q (j.outB l)) :=
    (splitEquiv j.toWireJoin.toWireMatch.connFam₁).trans
      ((Equiv.piCongrRight fun k : Fin j.ab =>
        Equiv.cast (connFam₁_castAdd j k)).prodCongr
        (Equiv.piCongrRight fun l : Fin j.ba =>
          (Equiv.cast (connFam₁_natAdd j l)).trans (j.equivBA l).symm))
  have e2 : (∀ k : Fin j.ab, O (j.outA k)) × (∀ l : Fin j.ba, Q (j.outB l)) ≃
      (∀ i : Fin (j.ab + j.ba), j.schedule.family O Q
        ((j.connections.get (Fin.cast (connections_length j).symm i)).a)) :=
    ((Equiv.piCongrRight fun k : Fin j.ab =>
      (j.schedule.leftFamilyEquiv O Q (j.outA k)).trans
        (Equiv.cast (congrArg (j.schedule.family O Q)
          (connections_a_castAdd j k).symm))).prodCongr
      (Equiv.piCongrRight fun l : Fin j.ba =>
        (j.schedule.rightFamilyEquiv O Q (j.outB l)).trans
          (Equiv.cast (congrArg (j.schedule.family O Q)
            (connections_a_natAdd j l).symm)))).trans
      ((splitEquiv fun i : Fin (j.ab + j.ba) =>
        j.schedule.family O Q
          ((j.connections.get (Fin.cast (connections_length j).symm i)).a)).symm)
  have e3 : (∀ i : Fin (j.ab + j.ba), j.schedule.family O Q
        ((j.connections.get (Fin.cast (connections_length j).symm i)).a)) ≃
      (∀ i : Fin j.connections.length,
        j.schedule.family O Q ((j.connections.get i).a)) :=
    (Equiv.piCongrLeft
      (fun i : Fin j.connections.length =>
        j.schedule.family O Q ((j.connections.get i).a)
      : Fin j.connections.length → Type u)
      ⟨Fin.cast (connections_length j).symm, Fin.cast (connections_length j),
        fun _ => Fin.ext rfl, fun _ => Fin.ext rfl⟩)
  have e4 : (∀ i : Fin j.connections.length,
      j.schedule.family O Q ((j.connections.get i).a)) ≃
    j.consumptions.fillValues :=
    (Consumptions.ofListAux_valuesEquiv [] [] j.connections
      j.connections_disIn j.connections_disOut
      (fun _ _ => ⟨by simp, by simp⟩) (fun _ => by simp) (fun _ => by simp)).symm
  exact (e1.trans e2).trans (e3.trans e4)

/-- The iterated contraction's end space, reindexed to the join's scheduled
boundary families. -/
def boundaryIndexEquiv (j : CausalJoin I O P Q) :
    Space (consumeList (j.schedule.family I P) (j.connections.map Connection.b))
      (consumeList (j.schedule.family O Q) (j.connections.map Connection.a)) ≃
    Space j.boundaryInput j.boundaryOutput :=
  spaceEquiv (fun t => Equiv.cast (congrFun (consumeList_connections_input j) t))
    (fun t => Equiv.cast (congrFun (consumeList_connections_output j) t))

/-- The consumed values of a join read in the contraction sequence's own
coordinates: the matching's connected configuration transported to the
scheduled output families of the consumed positions, in connection-list
order. -/
def connValues (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (i : Fin j.connections.length) :
    j.schedule.family O Q ((j.connections.get i).a) :=
  (Equiv.piCongrLeft
      (fun i : Fin j.connections.length =>
        j.schedule.family O Q ((j.connections.get i).a)
      : Fin j.connections.length → Type u)
      ⟨Fin.cast (connections_length j).symm, Fin.cast (connections_length j),
        fun _ => Fin.ext rfl, fun _ => Fin.ext rfl⟩)
    ((splitEquiv fun i : Fin (j.ab + j.ba) => j.schedule.family O Q
        ((j.connections.get (Fin.cast (connections_length j).symm i)).a)).symm
      (((Equiv.piCongrRight fun k : Fin j.ab =>
          (j.schedule.leftFamilyEquiv O Q (j.outA k)).trans
            (Equiv.cast (congrArg (j.schedule.family O Q)
              (connections_a_castAdd j k).symm))).prodCongr
        (Equiv.piCongrRight fun l : Fin j.ba =>
          (j.schedule.rightFamilyEquiv O Q (j.outB l)).trans
            (Equiv.cast (congrArg (j.schedule.family O Q)
              (connections_a_natAdd j l).symm))))
        ((splitEquiv j.toWireJoin.toWireMatch.connFam₁).trans
          ((Equiv.piCongrRight fun k : Fin j.ab =>
            Equiv.cast (connFam₁_castAdd j k)).prodCongr
            (Equiv.piCongrRight fun l : Fin j.ba =>
              (Equiv.cast (connFam₁_natAdd j l)).trans (j.equivBA l).symm)) z))) i

end CausalJoin

end QIT.HigherOrder.Comb
end
