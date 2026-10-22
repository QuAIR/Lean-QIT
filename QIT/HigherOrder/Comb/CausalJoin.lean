/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.WireJoin
public import QIT.HigherOrder.Comb.EventSchedule

/-!
# Causal joins and their actual free boundary

Every connection advances an event schedule which preserves both comb orders.
Consumed ports become one-dimensional padding; all unmatched ports retain their
original type at their scheduled event. The boundary equivalence only reindexes
these free configurations and makes no normalization assertion.
-/

@[expose] public section
noncomputable section
universe u
namespace QIT.HigherOrder.Comb
open QIT.WireFam

/-- A directional matching with a topological schedule extending both original
comb orders. -/
structure CausalJoin {nA nB : Nat} (I O : Fin nA → Type u) (P Q : Fin nB → Type u)
    extends WireJoin I O P Q where
  schedule : EventSchedule nA nB
  forwardAB : ∀ k, schedule.leftRank (outA k) < schedule.rightRank (inB k)
  forwardBA : ∀ k, schedule.rightRank (outB k) < schedule.leftRank (inA k)

namespace CausalJoin

/-- Replace a consumed port by a unit type, keeping any free port unchanged. -/
def padded (p : Prop) (W : Type u) : Type u :=
  @ite (Type u) p (Classical.propDecidable p) PUnit W

instance paddedFintype (p : Prop) (W : Type u) [Fintype W] : Fintype (padded p W) := by
  classical
  unfold padded
  split <;> infer_instance

instance paddedDecidableEq (p : Prop) (W : Type u) [DecidableEq W] :
    DecidableEq (padded p W) := by
  classical
  unfold padded
  split <;> infer_instance

/-- Erasing unit padding leaves exactly the configurations on free indices. -/
def paddingEquiv {α : Type} (p : α → Prop) (W : α → Type u) :
    (∀ i : {i // ¬ p i}, W i) ≃ (∀ i, padded (p i) (W i)) where
  toFun g i := by
    classical
    by_cases h : p i
    · exact cast (by simp [padded, h]) PUnit.unit
    · exact cast (by simp [padded, h]) (g ⟨i, h⟩)
  invFun f i := cast (by simp [padded, i.property]) (f i)
  left_inv g := by
    funext i
    simp [i.property]
  right_inv f := by
    funext i
    dsimp
    split
    · rename_i h
      have : Subsingleton (padded (p i) (W i)) := by
        simp only [padded, ite_eq_left h]
        infer_instance
      exact Subsingleton.elim _ _
    · simp

/-- The complement enumeration is an equivalence to the subtype of free ports. -/
def complementIndexEquiv {a s : Nat} (ι : Fin s → Fin a)
    (hι : Function.Injective ι) : Fin (a - s) ≃ {i // i ∉ Set.range ι} :=
  Equiv.ofBijective
    (fun k => ⟨complEmb ι hι k, by
      rintro ⟨l, hl⟩
      exact disjoint_conn_compl ι hι l k hl⟩)
    (by
      constructor
      · intro k l h
        have hh : complEmb ι hι k = complEmb ι hι l := congrArg (fun x : {i : Fin a // i ∉ Set.range ι} => x.val) h
        exact (Finset.orderEmbOfFin (complFinset ι hι) (card_complFinset ι hι)).injective hh
      · intro ⟨i, hi⟩
        rcases exists_conn_or_compl ι hι i with h | ⟨k, hk⟩
        · exact (hi h).elim
        · exact ⟨k, Subtype.ext hk⟩)

/-- The array of complement configurations is precisely the full port array
with unit padding at every connected index. -/
def complementPaddingEquiv {a s : Nat} (W : Fin a → Type u)
    (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    (∀ k, W (complEmb ι hι k)) ≃ (∀ i, padded (i ∈ Set.range ι) (W i)) :=
  (Equiv.piCongrLeft (fun i : {i // i ∉ Set.range ι} => W i)
    (complementIndexEquiv ι hι)).trans (paddingEquiv (fun i => i ∈ Set.range ι) W)

/-! ### Position readback of the padding transports -/

/-- The complement index of a free port: the inverse of the complement
enumeration at the subtype of free ports. -/
def freeIndex {a s : Nat} (ι : Fin s → Fin a) (hι : Function.Injective ι)
    (t : {i // i ∉ Set.range ι}) : Fin (a - s) :=
  (complementIndexEquiv ι hι).symm t

/-- The complement enumeration reads back the free index of a free port. -/
theorem complEmb_freeIndex {a s : Nat} (ι : Fin s → Fin a) (hι : Function.Injective ι)
    (t : {i // i ∉ Set.range ι}) :
    complEmb ι hι (freeIndex ι hι t) = t.val := by
  have h : (complementIndexEquiv ι hι) (freeIndex ι hι t) = t :=
    Equiv.apply_symm_apply _ _
  exact congrArg Subtype.val h

/-- A free port retains its original configuration value, read through the
unit-padding transport. -/
theorem paddingEquiv_apply_free {α : Type} (p : α → Prop) (W : α → Type u)
    (c : ∀ i : {i // ¬ p i}, W i.val) (i : α) (hi : ¬ p i) :
    (paddingEquiv p W c) i = cast (by simp [padded, hi]) (c ⟨i, hi⟩) := by
  classical
  change (dite (p i) (fun h => cast (by simp [padded, h]) PUnit.unit)
      (fun h => cast (by simp [padded, h]) (c ⟨i, h⟩))) = _
  split
  · rename_i h
    exact absurd h hi
  · rfl

/-- Reading a padded configuration back at a free port yields the original
value, definitionally. -/
theorem paddingEquiv_symm_apply {α : Type} (p : α → Prop) (W : α → Type u)
    (f : ∀ i, padded (p i) (W i)) (i : {i // ¬ p i}) :
    (paddingEquiv p W).symm f i = cast (by simp [padded, i.property]) (f i.val) := rfl

/-- Reading a padded complement configuration back at a complement index yields
the value at the enumerated free port. -/
theorem complementPaddingEquiv_symm_apply {a s : Nat} (W : Fin a → Type u)
    (ι : Fin s → Fin a) (hι : Function.Injective ι)
    (f : ∀ i, padded (i ∈ Set.range ι) (W i)) (k : Fin (a - s)) :
    (complementPaddingEquiv W ι hι).symm f k =
      cast (by
        have hmem : complEmb ι hι k ∉ Set.range ι := by
          rintro ⟨l, hl⟩
          exact disjoint_conn_compl ι hι l k hl
        simp [padded, hmem]) (f (complEmb ι hι k)) := by
  show ((Equiv.piCongrLeft (fun i : {i // i ∉ Set.range ι} => W i)
      (complementIndexEquiv ι hι)).symm
      ((paddingEquiv (fun i => i ∈ Set.range ι) W).symm f)) k = _
  rw [Equiv.piCongrLeft_symm_apply]
  rfl

variable {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}

/-- Whether an event's input is consumed by a matched connection. -/
def inputConnected (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : Prop :=
  Sum.elim (fun i => i ∈ Set.range j.inA) (fun i => i ∈ Set.range j.inB)
    (j.schedule.order t)

/-- Whether an event's output is consumed by a matched connection. -/
def outputConnected (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : Prop :=
  Sum.elim (fun i => i ∈ Set.range j.outA) (fun i => i ∈ Set.range j.outB)
    (j.schedule.order t)

/-- Scheduled input boundary: original free inputs, unit padding at consumed inputs. -/
def boundaryInput (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : Type u :=
  Sum.elim (fun i => padded (i ∈ Set.range j.inA) (I i))
    (fun i => padded (i ∈ Set.range j.inB) (P i)) (j.schedule.order t)

/-- Scheduled output boundary: original free outputs, unit padding at consumed outputs. -/
def boundaryOutput (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : Type u :=
  Sum.elim (fun i => padded (i ∈ Set.range j.outA) (O i))
    (fun i => padded (i ∈ Set.range j.outB) (Q i)) (j.schedule.order t)

@[simp] theorem boundaryInput_leftRank (j : CausalJoin I O P Q) (i : Fin nA) :
    j.boundaryInput (j.schedule.leftRank i) = padded (i ∈ Set.range j.inA) (I i) := by
  simp [boundaryInput]

@[simp] theorem boundaryInput_rightRank (j : CausalJoin I O P Q) (i : Fin nB) :
    j.boundaryInput (j.schedule.rightRank i) = padded (i ∈ Set.range j.inB) (P i) := by
  simp [boundaryInput]

@[simp] theorem boundaryOutput_leftRank (j : CausalJoin I O P Q) (i : Fin nA) :
    j.boundaryOutput (j.schedule.leftRank i) = padded (i ∈ Set.range j.outA) (O i) := by
  simp [boundaryOutput]

@[simp] theorem boundaryOutput_rightRank (j : CausalJoin I O P Q) (i : Fin nB) :
    j.boundaryOutput (j.schedule.rightRank i) = padded (i ∈ Set.range j.outB) (Q i) := by
  simp [boundaryOutput]

instance boundaryInputFintype [∀ i, Fintype (I i)] [∀ i, Fintype (P i)]
    (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : Fintype (j.boundaryInput t) := by
  unfold boundaryInput
  cases j.schedule.order t <;> dsimp <;> infer_instance

instance boundaryOutputFintype [∀ i, Fintype (O i)] [∀ i, Fintype (Q i)]
    (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : Fintype (j.boundaryOutput t) := by
  unfold boundaryOutput
  cases j.schedule.order t <;> dsimp <;> infer_instance

instance boundaryInputDecidableEq [∀ i, DecidableEq (I i)] [∀ i, DecidableEq (P i)]
    (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : DecidableEq (j.boundaryInput t) := by
  unfold boundaryInput
  cases j.schedule.order t <;> dsimp <;> infer_instance

instance boundaryOutputDecidableEq [∀ i, DecidableEq (O i)] [∀ i, DecidableEq (Q i)]
    (j : CausalJoin I O P Q) (t : Fin (nA + nB)) : DecidableEq (j.boundaryOutput t) := by
  unfold boundaryOutput
  cases j.schedule.order t <;> dsimp <;> infer_instance

private theorem range_addCases {a b : Nat} {α : Type}
    (f : Fin a → α) (g : Fin b → α) (x : α) :
    x ∈ Set.range (Fin.addCases f g) ↔ x ∈ Set.range f ∨ x ∈ Set.range g := by
  constructor
  · rintro ⟨k, hk⟩
    induction k using Fin.addCases with
    | left k => exact Or.inl ⟨k, by simpa using hk⟩
    | right k => exact Or.inr ⟨k, by simpa using hk⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨Fin.castAdd b k, by simpa using hk⟩
    · exact ⟨Fin.natAdd a k, by simpa using hk⟩

private theorem natAdd_ne_castAdd {a b : Nat} (i : Fin b) (j : Fin a) :
    Fin.natAdd a i ≠ Fin.castAdd b j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

private theorem castAdd_ne_natAdd {a b : Nat} (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := Ne.symm (natAdd_ne_castAdd j i)

/-- The first comb's input wires occupy exactly the input-side positions of the
first wire match. -/
theorem first_input_range (j : CausalJoin I O P Q) (i : Fin nA) :
    Fin.castAdd nA i ∈ Set.range j.toWireJoin.toWireMatch.ι₁ ↔ i ∈ Set.range j.inA := by
  simp only [WireJoin.toWireMatch, range_addCases]
  simp only [Set.mem_range, natAdd_ne_castAdd, Fin.castAdd_inj, exists_false, false_or]

/-- The first comb's output wires occupy exactly the output-side positions of
the first wire match. -/
theorem first_output_range (j : CausalJoin I O P Q) (i : Fin nA) :
    Fin.natAdd nA i ∈ Set.range j.toWireJoin.toWireMatch.ι₁ ↔ i ∈ Set.range j.outA := by
  simp only [WireJoin.toWireMatch, range_addCases]
  simp only [Set.mem_range, castAdd_ne_natAdd, Fin.natAdd_inj, exists_false, or_false]

/-- The second comb's input wires occupy exactly the input-side positions of
the second wire match. -/
theorem second_input_range (j : CausalJoin I O P Q) (i : Fin nB) :
    Fin.castAdd nB i ∈ Set.range j.toWireJoin.toWireMatch.ι₂ ↔ i ∈ Set.range j.inB := by
  simp only [WireJoin.toWireMatch, range_addCases]
  simp only [Set.mem_range, natAdd_ne_castAdd, Fin.castAdd_inj, exists_false, or_false]

/-- The second comb's output wires occupy exactly the output-side positions of
the second wire match. -/
theorem second_output_range (j : CausalJoin I O P Q) (i : Fin nB) :
    Fin.natAdd nB i ∈ Set.range j.toWireJoin.toWireMatch.ι₂ ↔ i ∈ Set.range j.outB := by
  simp only [WireJoin.toWireMatch, range_addCases]
  simp only [Set.mem_range, castAdd_ne_natAdd, Fin.natAdd_inj, exists_false, false_or]

/-- The first comb's complement configuration, split into padded inputs and outputs. -/
def firstBoundaryEquiv (j : CausalJoin I O P Q) :
    (∀ i, j.toWireJoin.toWireMatch.complFam₁ i) ≃
      (∀ i, padded (i ∈ Set.range j.inA) (I i)) ×
      (∀ i, padded (i ∈ Set.range j.outA) (O i)) :=
  (complementPaddingEquiv (append I O) j.toWireJoin.toWireMatch.ι₁
    j.toWireJoin.toWireMatch.hι₁).trans
    ((Equiv.piCongrRight (fun t => Equiv.cast (by
      induction t using Fin.addCases with
      | left i => simp only [append_castAdd, first_input_range]
      | right i => simp only [append_natAdd, first_output_range]))).trans
      (splitAppendEquiv (fun i => padded (i ∈ Set.range j.inA) (I i))
        (fun i => padded (i ∈ Set.range j.outA) (O i))))

/-- The second comb's complement configuration, split into padded inputs and outputs. -/
def secondBoundaryEquiv (j : CausalJoin I O P Q) :
    (∀ i, j.toWireJoin.toWireMatch.complFam₂ i) ≃
      (∀ i, padded (i ∈ Set.range j.inB) (P i)) ×
      (∀ i, padded (i ∈ Set.range j.outB) (Q i)) :=
  (complementPaddingEquiv (append P Q) j.toWireJoin.toWireMatch.ι₂
    j.toWireJoin.toWireMatch.hι₂).trans
    ((Equiv.piCongrRight (fun t => Equiv.cast (by
      induction t using Fin.addCases with
      | left i => simp only [append_castAdd, second_input_range]
      | right i => simp only [append_natAdd, second_output_range]))).trans
      (splitAppendEquiv (fun i => padded (i ∈ Set.range j.inB) (P i))
        (fun i => padded (i ∈ Set.range j.outB) (Q i))))

/-- Interleave two configuration families in the schedule's event order. -/
def scheduleEquiv (s : EventSchedule nA nB) (A : Fin nA → Type u)
    (B : Fin nB → Type u) :
    (∀ i, A i) × (∀ i, B i) ≃ (∀ t, Sum.elim A B (s.order t)) :=
  (Equiv.sumPiEquivProdPi (Sum.elim A B)).symm.trans
    (Equiv.piCongrLeft (Sum.elim A B) s.order).symm

/-- Reading a scheduled configuration back through the schedule order gives,
at each event of the first comb, the first factor's value, and at each event
of the second comb, the second factor's value. -/
theorem scheduleEquiv_symm_apply (s : EventSchedule nA nB) (A : Fin nA → Type u)
    (B : Fin nB → Type u) (u : ∀ t, Sum.elim A B (s.order t)) :
    (scheduleEquiv s A B).symm u =
      (fun i => cast (show Sum.elim A B (s.order (s.leftRank i)) = A i from by
          rw [EventSchedule.order_leftRank]; rfl) (u (s.leftRank i)),
       fun j => cast (show Sum.elim A B (s.order (s.rightRank j)) = B j from by
          rw [EventSchedule.order_rightRank]; rfl) (u (s.rightRank j))) := by
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · funext x
    show (Equiv.sumPiEquivProdPi (Sum.elim A B)
        (Equiv.piCongrLeft (Sum.elim A B) s.order u)).1 x = _
    exact Equiv.piCongrLeft_apply_eq_cast u (Sum.inl x)
  · funext x
    show (Equiv.sumPiEquivProdPi (Sum.elim A B)
        (Equiv.piCongrLeft (Sum.elim A B) s.order u)).2 x = _
    exact Equiv.piCongrLeft_apply_eq_cast u (Sum.inr x)

/-- Actual free-port configurations in the link product's complement layout
are equivalent to scheduled input/output configurations with unit padding.
This transport retains each original free port and assumes no causal semantics
or normalization theorem. -/
def boundaryEquiv (j : CausalJoin I O P Q) :
    j.toWireJoin.RawSpace ≃ Space j.boundaryInput j.boundaryOutput :=
  (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
    j.toWireJoin.toWireMatch.complFam₂).trans
    (((firstBoundaryEquiv j).prodCongr (secondBoundaryEquiv j)).trans
      ((Equiv.prodProdProdComm _ _ _ _).trans
        ((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
          (fun i => padded (i ∈ Set.range j.inB) (P i))).prodCongr
        (scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
          (fun i => padded (i ∈ Set.range j.outB) (Q i))))))

/-! ### Position readback of the boundary transport

Cast shift: a tower of casts along composable type equations collapses to a
single cast along the composed equation. -/
private theorem cast_shift3 {A B C D : Type u} {h1 : A = B} {h2 : B = C} {h3 : C = D}
    {h4 : A = D} (x : A) :
    cast h3 (cast h2 (cast h1 x)) = cast h4 x := by
  cases h1; cases h2; cases h3; cases h4; rfl

private theorem cast_shift4 {A B C D E : Type u} {h1 : A = B} {h2 : B = C} {h3 : C = D}
    {h4 : D = E} {h5 : A = E} (x : A) :
    cast h4 (cast h3 (cast h2 (cast h1 x))) = cast h5 x := by
  cases h1; cases h2; cases h3; cases h4; cases h5; rfl

/-! Pointwise readback of a pointwise-`cast` congruence transport, in the
reverse direction. -/
private theorem piCast_symm_apply {n : Nat} {X Y : Fin (n + n) → Type u}
    (h : ∀ t, X t = Y t) (g : ∀ t, Y t) (t : Fin (n + n)) :
    (Equiv.piCongrRight (fun t' => Equiv.cast (h t'))).symm g t
      = cast (h t).symm (g t) := by
  rw [Equiv.piCongrRight_symm_apply, Pi.map_apply, ← Equiv.cast_symm, Equiv.cast_apply]

/-! Evaluation of an `Fin.addCases` branch selector at a position known only
propositionally: the branch value is transported along the induced family
equation. -/
private theorem addCases_left_cast {n : Nat} {A : Fin (n + n) → Type u}
    (f₁ : ∀ i : Fin n, A (Fin.castAdd n i)) (f₂ : ∀ i : Fin n, A (Fin.natAdd n i))
    {b : Fin (n + n)} {i : Fin n} (hb : b = Fin.castAdd n i) :
    Fin.addCases f₁ f₂ b = cast (congrArg A hb).symm (f₁ i) := by
  cases hb
  rw [Fin.addCases_left]
  rfl

private theorem addCases_right_cast {n : Nat} {A : Fin (n + n) → Type u}
    (f₁ : ∀ i : Fin n, A (Fin.castAdd n i)) (f₂ : ∀ i : Fin n, A (Fin.natAdd n i))
    {b : Fin (n + n)} {i : Fin n} (hb : b = Fin.natAdd n i) :
    Fin.addCases f₁ f₂ b = cast (congrArg A hb).symm (f₂ i) := by
  cases hb
  rw [Fin.addCases_right]
  rfl

/-- Reading the first comb's split boundary back at a free input port yields
the padded input configuration at that port. -/
theorem firstBoundaryEquiv_symm_input (j : CausalJoin I O P Q)
    (a : ∀ i, padded (i ∈ Set.range j.inA) (I i))
    (o : ∀ i, padded (i ∈ Set.range j.outA) (O i)) {i : Fin nA}
    (hi : i ∉ Set.range j.inA) :
    (firstBoundaryEquiv j).symm (a, o)
        (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
          ⟨Fin.castAdd nA i, fun h => hi ((first_input_range j i).mp h)⟩) =
      cast (by simp [WireMatch.complFam₁, complEmb_freeIndex, append_castAdd,
        padded, hi]) (a i) := by
  classical
  show ((complementPaddingEquiv (append I O) j.toWireJoin.toWireMatch.ι₁
      j.toWireJoin.toWireMatch.hι₁).symm
    ((Equiv.piCongrRight (fun t => Equiv.cast (by
        induction t using Fin.addCases with
        | left i' => simp only [append_castAdd, first_input_range]
        | right i' => simp only [append_natAdd, first_output_range]))).symm
      ((splitAppendEquiv (fun i => padded (i ∈ Set.range j.inA) (I i))
        (fun i => padded (i ∈ Set.range j.outA) (O i))).symm (a, o))))
    (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
      ⟨Fin.castAdd nA i, fun h => hi ((first_input_range j i).mp h)⟩) = _
  rw [complementPaddingEquiv_symm_apply, piCast_symm_apply, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [addCases_left_cast _ _ (complEmb_freeIndex _ _ _)]
  exact cast_shift4 _

/-- Reading the first comb's split boundary back at a free output port yields
the padded output configuration at that port. -/
theorem firstBoundaryEquiv_symm_output (j : CausalJoin I O P Q)
    (a : ∀ i, padded (i ∈ Set.range j.inA) (I i))
    (o : ∀ i, padded (i ∈ Set.range j.outA) (O i)) {i : Fin nA}
    (hi : i ∉ Set.range j.outA) :
    (firstBoundaryEquiv j).symm (a, o)
        (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
          ⟨Fin.natAdd nA i, fun h => hi ((first_output_range j i).mp h)⟩) =
      cast (by
        show padded (i ∈ Set.range j.outA) (O i) = append I O
          (complEmb j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
            (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
              ⟨Fin.natAdd nA i, fun h => hi ((first_output_range j i).mp h)⟩))
        rw [complEmb_freeIndex, append_natAdd]
        simp [padded, hi]) (o i) := by
  classical
  show ((complementPaddingEquiv (append I O) j.toWireJoin.toWireMatch.ι₁
      j.toWireJoin.toWireMatch.hι₁).symm
    ((Equiv.piCongrRight (fun t => Equiv.cast (by
        induction t using Fin.addCases with
        | left i' => simp only [append_castAdd, first_input_range]
        | right i' => simp only [append_natAdd, first_output_range]))).symm
      ((splitAppendEquiv (fun i => padded (i ∈ Set.range j.inA) (I i))
        (fun i => padded (i ∈ Set.range j.outA) (O i))).symm (a, o))))
    (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
      ⟨Fin.natAdd nA i, fun h => hi ((first_output_range j i).mp h)⟩) = _
  rw [complementPaddingEquiv_symm_apply, piCast_symm_apply, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [addCases_right_cast _ _ (complEmb_freeIndex _ _ _)]
  exact cast_shift4 _

/-- Reading the second comb's split boundary back at a free input port yields
the padded input configuration at that port. -/
theorem secondBoundaryEquiv_symm_input (j : CausalJoin I O P Q)
    (p : ∀ i, padded (i ∈ Set.range j.inB) (P i))
    (q : ∀ i, padded (i ∈ Set.range j.outB) (Q i)) {i : Fin nB}
    (hi : i ∉ Set.range j.inB) :
    (secondBoundaryEquiv j).symm (p, q)
        (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
          ⟨Fin.castAdd nB i, fun h => hi ((second_input_range j i).mp h)⟩) =
      cast (by simp [WireMatch.complFam₂, complEmb_freeIndex, append_castAdd,
        padded, hi]) (p i) := by
  classical
  show ((complementPaddingEquiv (append P Q) j.toWireJoin.toWireMatch.ι₂
      j.toWireJoin.toWireMatch.hι₂).symm
    ((Equiv.piCongrRight (fun t => Equiv.cast (by
        induction t using Fin.addCases with
        | left i' => simp only [append_castAdd, second_input_range]
        | right i' => simp only [append_natAdd, second_output_range]))).symm
      ((splitAppendEquiv (fun i => padded (i ∈ Set.range j.inB) (P i))
        (fun i => padded (i ∈ Set.range j.outB) (Q i))).symm (p, q))))
    (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
      ⟨Fin.castAdd nB i, fun h => hi ((second_input_range j i).mp h)⟩) = _
  rw [complementPaddingEquiv_symm_apply, piCast_symm_apply, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [addCases_left_cast _ _ (complEmb_freeIndex _ _ _)]
  exact cast_shift4 _

/-- Reading the second comb's split boundary back at a free output port yields
the padded output configuration at that port. -/
theorem secondBoundaryEquiv_symm_output (j : CausalJoin I O P Q)
    (p : ∀ i, padded (i ∈ Set.range j.inB) (P i))
    (q : ∀ i, padded (i ∈ Set.range j.outB) (Q i)) {i : Fin nB}
    (hi : i ∉ Set.range j.outB) :
    (secondBoundaryEquiv j).symm (p, q)
        (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
          ⟨Fin.natAdd nB i, fun h => hi ((second_output_range j i).mp h)⟩) =
      cast (by
        show padded (i ∈ Set.range j.outB) (Q i) = append P Q
          (complEmb j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
            (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
              ⟨Fin.natAdd nB i, fun h => hi ((second_output_range j i).mp h)⟩))
        rw [complEmb_freeIndex, append_natAdd]
        simp [padded, hi]) (q i) := by
  classical
  show ((complementPaddingEquiv (append P Q) j.toWireJoin.toWireMatch.ι₂
      j.toWireJoin.toWireMatch.hι₂).symm
    ((Equiv.piCongrRight (fun t => Equiv.cast (by
        induction t using Fin.addCases with
        | left i' => simp only [append_castAdd, second_input_range]
        | right i' => simp only [append_natAdd, second_output_range]))).symm
      ((splitAppendEquiv (fun i => padded (i ∈ Set.range j.inB) (P i))
        (fun i => padded (i ∈ Set.range j.outB) (Q i))).symm (p, q))))
    (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
      ⟨Fin.natAdd nB i, fun h => hi ((second_output_range j i).mp h)⟩) = _
  rw [complementPaddingEquiv_symm_apply, piCast_symm_apply, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [addCases_right_cast _ _ (complEmb_freeIndex _ _ _)]
  exact cast_shift4 _

/-! The reversed boundary transport, normalized to the pair of reversed split
boundary transports on the two combs' scheduled configurations. -/
private theorem boundaryEquiv_symm_pair (j : CausalJoin I O P Q)
    (p : Space j.boundaryInput j.boundaryOutput) :
    ((firstBoundaryEquiv j).prodCongr (secondBoundaryEquiv j)).symm
      ((Equiv.prodProdProdComm _ _ _ _).symm
        (((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
            (fun i => padded (i ∈ Set.range j.inB) (P i))).prodCongr
          (scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
            (fun i => padded (i ∈ Set.range j.outB) (Q i)))).symm p)) =
    ((firstBoundaryEquiv j).symm
        (((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
            (fun i => padded (i ∈ Set.range j.inB) (P i))).symm p.1).1,
      ((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
          (fun i => padded (i ∈ Set.range j.outB) (Q i))).symm p.2).1),
      (secondBoundaryEquiv j).symm
        (((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
            (fun i => padded (i ∈ Set.range j.inB) (P i))).symm p.1).2,
        ((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
            (fun i => padded (i ∈ Set.range j.outB) (Q i))).symm p.2).2)) := rfl

/-- Reading the full boundary transport back at the first comb's free input
ports yields the scheduled input configuration at the corresponding event. -/
theorem boundaryEquiv_symm_input_left (j : CausalJoin I O P Q)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nA}
    (hi : i ∉ Set.range j.inA) :
    j.boundaryEquiv.symm p
        (Fin.castAdd ((nB + nB) - j.toWireJoin.toWireMatch.s)
          (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
            ⟨Fin.castAdd nA i, fun h => hi ((first_input_range j i).mp h)⟩)) =
      cast (by
        rw [boundaryInput_leftRank, append_castAdd]
        dsimp only [WireMatch.complFam₁]
        rw [complEmb_freeIndex, append_castAdd]
        simp [padded, hi]) (p.1 (j.schedule.leftRank i)) := by
  classical
  show (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂).symm
    (((firstBoundaryEquiv j).prodCongr (secondBoundaryEquiv j)).symm
      ((Equiv.prodProdProdComm _ _ _ _).symm
        (((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
            (fun i => padded (i ∈ Set.range j.inB) (P i))).prodCongr
          (scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
            (fun i => padded (i ∈ Set.range j.outB) (Q i)))).symm p)))
    (Fin.castAdd ((nB + nB) - j.toWireJoin.toWireMatch.s)
      (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
        ⟨Fin.castAdd nA i, fun h => hi ((first_input_range j i).mp h)⟩)) = _
  rw [boundaryEquiv_symm_pair, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [Fin.addCases_left, firstBoundaryEquiv_symm_input]
  rw [congrFun (congrArg Prod.fst (scheduleEquiv_symm_apply j.schedule
    (fun i => padded (i ∈ Set.range j.inA) (I i))
    (fun i => padded (i ∈ Set.range j.inB) (P i)) p.1)) i]
  exact cast_shift3 _

/-- Reading the full boundary transport back at the first comb's free output
ports yields the scheduled output configuration at the corresponding event. -/
theorem boundaryEquiv_symm_output_left (j : CausalJoin I O P Q)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nA}
    (hi : i ∉ Set.range j.outA) :
    j.boundaryEquiv.symm p
        (Fin.castAdd ((nB + nB) - j.toWireJoin.toWireMatch.s)
          (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
            ⟨Fin.natAdd nA i, fun h => hi ((first_output_range j i).mp h)⟩)) =
      cast (by
        rw [boundaryOutput_leftRank, append_castAdd]
        dsimp only [WireMatch.complFam₁]
        rw [complEmb_freeIndex, append_natAdd]
        simp [padded, hi]) (p.2 (j.schedule.leftRank i)) := by
  classical
  show (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂).symm
    (((firstBoundaryEquiv j).prodCongr (secondBoundaryEquiv j)).symm
      ((Equiv.prodProdProdComm _ _ _ _).symm
        (((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
            (fun i => padded (i ∈ Set.range j.inB) (P i))).prodCongr
          (scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
            (fun i => padded (i ∈ Set.range j.outB) (Q i)))).symm p)))
    (Fin.castAdd ((nB + nB) - j.toWireJoin.toWireMatch.s)
      (freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
        ⟨Fin.natAdd nA i, fun h => hi ((first_output_range j i).mp h)⟩)) = _
  rw [boundaryEquiv_symm_pair, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [Fin.addCases_left, firstBoundaryEquiv_symm_output]
  rw [congrFun (congrArg Prod.fst (scheduleEquiv_symm_apply j.schedule
    (fun i => padded (i ∈ Set.range j.outA) (O i))
    (fun i => padded (i ∈ Set.range j.outB) (Q i)) p.2)) i]
  exact cast_shift3 _

/-- Reading the full boundary transport back at the second comb's free input
ports yields the scheduled input configuration at the corresponding event. -/
theorem boundaryEquiv_symm_input_right (j : CausalJoin I O P Q)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nB}
    (hi : i ∉ Set.range j.inB) :
    j.boundaryEquiv.symm p
        (Fin.natAdd ((nA + nA) - j.toWireJoin.toWireMatch.s)
          (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
            ⟨Fin.castAdd nB i, fun h => hi ((second_input_range j i).mp h)⟩)) =
      cast (by
        rw [boundaryInput_rightRank, append_natAdd]
        dsimp only [WireMatch.complFam₂]
        rw [complEmb_freeIndex, append_castAdd]
        simp [padded, hi]) (p.1 (j.schedule.rightRank i)) := by
  classical
  show (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂).symm
    (((firstBoundaryEquiv j).prodCongr (secondBoundaryEquiv j)).symm
      ((Equiv.prodProdProdComm _ _ _ _).symm
        (((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
            (fun i => padded (i ∈ Set.range j.inB) (P i))).prodCongr
          (scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
            (fun i => padded (i ∈ Set.range j.outB) (Q i)))).symm p)))
    (Fin.natAdd ((nA + nA) - j.toWireJoin.toWireMatch.s)
      (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
        ⟨Fin.castAdd nB i, fun h => hi ((second_input_range j i).mp h)⟩)) = _
  rw [boundaryEquiv_symm_pair, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [Fin.addCases_right, secondBoundaryEquiv_symm_input]
  rw [congrFun (congrArg Prod.snd (scheduleEquiv_symm_apply j.schedule
    (fun i => padded (i ∈ Set.range j.inA) (I i))
    (fun i => padded (i ∈ Set.range j.inB) (P i)) p.1)) i]
  exact cast_shift3 _

/-- Reading the full boundary transport back at the second comb's free output
ports yields the scheduled output configuration at the corresponding event. -/
theorem boundaryEquiv_symm_output_right (j : CausalJoin I O P Q)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nB}
    (hi : i ∉ Set.range j.outB) :
    j.boundaryEquiv.symm p
        (Fin.natAdd ((nA + nA) - j.toWireJoin.toWireMatch.s)
          (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
            ⟨Fin.natAdd nB i, fun h => hi ((second_output_range j i).mp h)⟩)) =
      cast (by
        rw [boundaryOutput_rightRank, append_natAdd]
        dsimp only [WireMatch.complFam₂]
        rw [complEmb_freeIndex, append_natAdd]
        simp [padded, hi]) (p.2 (j.schedule.rightRank i)) := by
  classical
  show (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂).symm
    (((firstBoundaryEquiv j).prodCongr (secondBoundaryEquiv j)).symm
      ((Equiv.prodProdProdComm _ _ _ _).symm
        (((scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.inA) (I i))
            (fun i => padded (i ∈ Set.range j.inB) (P i))).prodCongr
          (scheduleEquiv j.schedule (fun i => padded (i ∈ Set.range j.outA) (O i))
            (fun i => padded (i ∈ Set.range j.outB) (Q i)))).symm p)))
    (Fin.natAdd ((nA + nA) - j.toWireJoin.toWireMatch.s)
      (freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
        ⟨Fin.natAdd nB i, fun h => hi ((second_output_range j i).mp h)⟩)) = _
  rw [boundaryEquiv_symm_pair, splitAppendEquiv_symm_apply]
  beta_reduce
  rw [Fin.addCases_right, secondBoundaryEquiv_symm_output]
  rw [congrFun (congrArg Prod.snd (scheduleEquiv_symm_apply j.schedule
    (fun i => padded (i ∈ Set.range j.outA) (O i))
    (fun i => padded (i ∈ Set.range j.outB) (Q i)) p.2)) i]
  exact cast_shift3 _

end CausalJoin
end QIT.HigherOrder.Comb
end
