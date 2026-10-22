/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Order-preserving schedules of two combs

A schedule lists every tooth of both combs exactly once, preserving both
original tooth orders. Directed wire connections can be required to increase
schedule rank. This gives a topological witness for the composite network,
including connections that skip teeth, without permuting either comb's causal
order. The network requirement, whose join conditions at lines 1233-1243 of
the source demand an acyclic composite graph, is described in
[Chiribella2009Networks, comblong-pub.tex:1279-1286].

This module contains only finite scheduling facts, independent of wire types,
operators, and normalization.
-/

@[expose] public section

namespace QIT.HigherOrder.Comb

/-- A total order on the events of two combs that extends each original order. -/
structure EventSchedule (nA nB : Nat) where
  order : Fin (nA + nB) ≃ (Fin nA ⊕ Fin nB)
  left_strictMono : StrictMono (fun i => order.symm (Sum.inl i))
  right_strictMono : StrictMono (fun i => order.symm (Sum.inr i))

namespace EventSchedule

variable {nA nB : Nat}

/-- Position of a tooth of the first comb in the joint schedule. -/
def leftRank (s : EventSchedule nA nB) (i : Fin nA) : Fin (nA + nB) :=
  s.order.symm (Sum.inl i)

/-- Position of a tooth of the second comb in the joint schedule. -/
def rightRank (s : EventSchedule nA nB) (j : Fin nB) : Fin (nA + nB) :=
  s.order.symm (Sum.inr j)

theorem leftRank_strictMono (s : EventSchedule nA nB) : StrictMono s.leftRank :=
  s.left_strictMono

theorem rightRank_strictMono (s : EventSchedule nA nB) : StrictMono s.rightRank :=
  s.right_strictMono

theorem leftRank_injective (s : EventSchedule nA nB) : Function.Injective s.leftRank :=
  s.leftRank_strictMono.injective

theorem rightRank_injective (s : EventSchedule nA nB) : Function.Injective s.rightRank :=
  s.rightRank_strictMono.injective

/-- A tooth of one comb is never the same event as a tooth of the other. -/
theorem leftRank_ne_rightRank (s : EventSchedule nA nB) (i : Fin nA) (j : Fin nB) :
    s.leftRank i ≠ s.rightRank j := by
  intro h
  have := s.order.symm.injective h
  cases this

@[simp] theorem order_leftRank (s : EventSchedule nA nB) (i : Fin nA) :
    s.order (s.leftRank i) = Sum.inl i := s.order.apply_symm_apply _

@[simp] theorem order_rightRank (s : EventSchedule nA nB) (j : Fin nB) :
    s.order (s.rightRank j) = Sum.inr j := s.order.apply_symm_apply _

/-- Construct a schedule from disjoint strictly increasing rank assignments.
Because there are exactly as many events as positions, injectivity also gives
surjectivity; no additional coverage hypothesis is needed. -/
noncomputable def ofRanks (l : Fin nA → Fin (nA + nB))
    (r : Fin nB → Fin (nA + nB)) (hl : StrictMono l) (hr : StrictMono r)
    (hd : ∀ i j, l i ≠ r j) : EventSchedule nA nB where
  order := (Equiv.ofBijective (Sum.elim l r) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · intro x y h
      cases x with
      | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (hl.injective h)
        | inr j => exact (hd i j h).elim
      | inr i =>
        cases y with
        | inl j => exact (hd j i h.symm).elim
        | inr j => exact congrArg Sum.inr (hr.injective h)
    · simp)).symm
  left_strictMono := hl
  right_strictMono := hr

@[simp] theorem ofRanks_leftRank (l : Fin nA → Fin (nA + nB))
    (r : Fin nB → Fin (nA + nB)) (hl : StrictMono l) (hr : StrictMono r)
    (hd : ∀ i j, l i ≠ r j) (i : Fin nA) :
    (ofRanks l r hl hr hd).leftRank i = l i := rfl

@[simp] theorem ofRanks_rightRank (l : Fin nA → Fin (nA + nB))
    (r : Fin nB → Fin (nA + nB)) (hl : StrictMono l) (hr : StrictMono r)
    (hd : ∀ i j, l i ≠ r j) (j : Fin nB) :
    (ofRanks l r hl hr hd).rightRank j = r j := rfl

/-- A directed trip from the first comb through the second cannot return to
an earlier or equal tooth of the first comb. -/
theorem no_left_feedback (s : EventSchedule nA nB) {i j : Fin nA} {q : Fin nB}
    (hji : j ≤ i) (hiq : s.leftRank i < s.rightRank q)
    (hqj : s.rightRank q < s.leftRank j) : False :=
  (not_lt_of_ge (s.leftRank_strictMono.monotone hji)) (lt_trans hiq hqj)

/-- The symmetric exclusion of backward feedback through the first comb. -/
theorem no_right_feedback (s : EventSchedule nA nB) {i j : Fin nB} {q : Fin nA}
    (hji : j ≤ i) (hiq : s.rightRank i < s.leftRank q)
    (hqj : s.leftRank q < s.rightRank j) : False :=
  (not_lt_of_ge (s.rightRank_strictMono.monotone hji)) (lt_trans hiq hqj)

/-- If a left event is the final event, it is the last tooth of its comb. -/
theorem left_eq_last_of_rank_max (s : EventSchedule (nA + 1) nB)
    {i : Fin (nA + 1)} (h : (s.leftRank i).val + 1 = nA + 1 + nB) :
    i = Fin.last nA := by
  by_contra hi
  have hlt : i < Fin.last nA := lt_of_le_of_ne (Fin.le_last i) hi
  have := s.leftRank_strictMono hlt
  have := (s.leftRank (Fin.last nA)).isLt
  simp only [Fin.lt_def] at *
  omega

/-- If a right event is the final event, it is the last tooth of its comb. -/
theorem right_eq_last_of_rank_max (s : EventSchedule nA (nB + 1))
    {j : Fin (nB + 1)} (h : (s.rightRank j).val + 1 = nA + (nB + 1)) :
    j = Fin.last nB := by
  by_contra hj
  have hlt : j < Fin.last nB := lt_of_le_of_ne (Fin.le_last j) hj
  have := s.rightRank_strictMono hlt
  have := (s.rightRank (Fin.last nB)).isLt
  simp only [Fin.lt_def] at *
  omega

/-- The joint final event belongs to one of the two component combs. -/
theorem exists_final (s : EventSchedule nA nB) (h : 0 < nA + nB) :
    (∃ i, (s.leftRank i).val + 1 = nA + nB) ∨
      (∃ j, (s.rightRank j).val + 1 = nA + nB) := by
  let k : Fin (nA + nB) := ⟨nA + nB - 1, by omega⟩
  have hk : k.val + 1 = nA + nB := by dsimp [k]; omega
  cases he : s.order k with
  | inl i =>
      left
      refine ⟨i, ?_⟩
      have : s.leftRank i = k := by rw [leftRank, ← he, s.order.symm_apply_apply]
      simpa only [this] using hk
  | inr j =>
      right
      refine ⟨j, ?_⟩
      have : s.rightRank j = k := by rw [rightRank, ← he, s.order.symm_apply_apply]
      simpa only [this] using hk

/-- Earlier left teeth survive deletion of a final left event. -/
theorem leftRank_castSucc_lt_of_last_left (s : EventSchedule (nA + 1) nB)
    (h : (s.leftRank (Fin.last nA)).val = nA + nB) (i : Fin nA) :
    (s.leftRank i.castSucc).val < nA + nB := by
  have := s.leftRank_strictMono (Fin.castSucc_lt_last i)
  simpa only [Fin.lt_def, h] using this

/-- Every right tooth survives deletion of a final left event. -/
theorem rightRank_lt_of_last_left (s : EventSchedule (nA + 1) nB)
    (h : (s.leftRank (Fin.last nA)).val = nA + nB) (j : Fin nB) :
    (s.rightRank j).val < nA + nB := by
  have hne := s.leftRank_ne_rightRank (Fin.last nA) j
  have hval : (s.rightRank j).val ≠ nA + nB := by
    intro heq
    exact hne (Fin.ext (h.trans heq.symm))
  have := (s.rightRank j).isLt
  omega

/-- Delete the globally final event when it is the last left tooth.
All surviving ranks retain their values, making this usable in reverse
schedule induction. -/
noncomputable def dropLastLeft (s : EventSchedule (nA + 1) nB)
    (h : (s.leftRank (Fin.last nA)).val = nA + nB) : EventSchedule nA nB :=
  ofRanks
    (fun i => ⟨(s.leftRank i.castSucc).val, s.leftRank_castSucc_lt_of_last_left h i⟩)
    (fun j => ⟨(s.rightRank j).val, s.rightRank_lt_of_last_left h j⟩)
    (by intro i j hij; exact s.leftRank_strictMono hij)
    (by intro i j hij; exact s.rightRank_strictMono hij)
    (by intro i j heq; exact s.leftRank_ne_rightRank i.castSucc j
          (Fin.ext (congrArg (fun x : Fin (nA + nB) => x.val) heq)))

@[simp] theorem dropLastLeft_leftRank_val (s : EventSchedule (nA + 1) nB)
    (h : (s.leftRank (Fin.last nA)).val = nA + nB) (i : Fin nA) :
    ((s.dropLastLeft h).leftRank i).val = (s.leftRank i.castSucc).val := rfl

@[simp] theorem dropLastLeft_rightRank_val (s : EventSchedule (nA + 1) nB)
    (h : (s.leftRank (Fin.last nA)).val = nA + nB) (j : Fin nB) :
    ((s.dropLastLeft h).rightRank j).val = (s.rightRank j).val := rfl

/-- Every left tooth survives deletion of a final right event. -/
theorem leftRank_lt_of_last_right (s : EventSchedule nA (nB + 1))
    (h : (s.rightRank (Fin.last nB)).val = nA + nB) (i : Fin nA) :
    (s.leftRank i).val < nA + nB := by
  have hne := s.leftRank_ne_rightRank i (Fin.last nB)
  have hval : (s.leftRank i).val ≠ nA + nB := by
    intro heq
    exact hne (Fin.ext (heq.trans h.symm))
  have := (s.leftRank i).isLt
  omega

/-- Earlier right teeth survive deletion of a final right event. -/
theorem rightRank_castSucc_lt_of_last_right (s : EventSchedule nA (nB + 1))
    (h : (s.rightRank (Fin.last nB)).val = nA + nB) (j : Fin nB) :
    (s.rightRank j.castSucc).val < nA + nB := by
  have := s.rightRank_strictMono (Fin.castSucc_lt_last j)
  simpa only [Fin.lt_def, h] using this

/-- Delete the globally final event when it is the last right tooth. -/
noncomputable def dropLastRight (s : EventSchedule nA (nB + 1))
    (h : (s.rightRank (Fin.last nB)).val = nA + nB) : EventSchedule nA nB :=
  ofRanks
    (fun i => ⟨(s.leftRank i).val, s.leftRank_lt_of_last_right h i⟩)
    (fun j => ⟨(s.rightRank j.castSucc).val, s.rightRank_castSucc_lt_of_last_right h j⟩)
    (by intro i j hij; exact s.leftRank_strictMono hij)
    (by intro i j hij; exact s.rightRank_strictMono hij)
    (by intro i j heq; exact s.leftRank_ne_rightRank i j.castSucc
          (Fin.ext (congrArg (fun x : Fin (nA + nB) => x.val) heq)))

@[simp] theorem dropLastRight_leftRank_val (s : EventSchedule nA (nB + 1))
    (h : (s.rightRank (Fin.last nB)).val = nA + nB) (i : Fin nA) :
    ((s.dropLastRight h).leftRank i).val = (s.leftRank i).val := rfl

@[simp] theorem dropLastRight_rightRank_val (s : EventSchedule nA (nB + 1))
    (h : (s.rightRank (Fin.last nB)).val = nA + nB) (j : Fin nB) :
    ((s.dropLastRight h).rightRank j).val = (s.rightRank j.castSucc).val := rfl

/-- A concrete interleaving `[A₀, A₁, B₀, A₂]`. In particular a path
`A₀ → B₀ → A₂` can skip `A₁` without reversing either comb's tooth order. -/
noncomputable def threeOneInterleaving : EventSchedule 3 1 :=
  ofRanks (fun i => ⟨if i.val = 2 then 3 else i.val, by split <;> omega⟩)
    (fun _ => 2)
    (by
      intro i j hij
      simp only [Fin.lt_def] at *
      split <;> split <;> omega)
    (by intro i j hij; have := i.isLt; have := j.isLt; simp only [Fin.lt_def] at hij; omega)
    (by
      intro i j heq
      have hv := congrArg Fin.val heq
      dsimp at hv
      split at hv <;> omega)

/-- The skipped-tooth path is strictly forward in the example schedule. -/
theorem threeOneInterleaving_forward :
    threeOneInterleaving.leftRank 0 < threeOneInterleaving.rightRank 0 ∧
      threeOneInterleaving.rightRank 0 < threeOneInterleaving.leftRank 2 := by
  decide +kernel

end EventSchedule
end QIT.HigherOrder.Comb
