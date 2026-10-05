/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Finset.Powerset

/-!
# Binomial coefficients of sums of commuting idempotents

The elementary symmetric products of commuting idempotents give the binomial
coefficients of their sum
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:554-566].
-/

@[expose] public section

open Polynomial Finset
open scoped BigOperators

namespace QIT

/-- An idempotent has zero binomial coefficients in degrees at least two. -/
theorem choose_idempotent_eq_zero {R : Type*} [Ring R] [BinomialRing R]
    (e : R) (he : e * e = e) (n : ℕ) : Ring.choose e (n + 2) = 0 := by
  let := BinomialRing.toIsAddTorsionFree (R := R)
  have hp : ∀ n : ℕ, (descPochhammer ℤ (n + 2)).smeval e = 0 := by
    intro n
    induction n with
    | zero =>
      simp [descPochhammer_succ_right, smeval_mul, smeval_sub, smeval_X,
        mul_sub, he]
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, descPochhammer_succ_right,
        smeval_mul, ih, zero_mul]
  apply (nsmul_right_inj (Nat.factorial_ne_zero (n + 2))).mp
  rw [← Ring.descPochhammer_eq_factorial_smul_choose, hp, nsmul_zero]

/-- Adding a commuting idempotent gives Pascal's recurrence. -/
theorem choose_add_idempotent_succ {R : Type*} [Ring R] [BinomialRing R]
    (r e : R) (hcomm : Commute r e) (he : e * e = e) (s : ℕ) :
    Ring.choose (r + e) (s + 1) = Ring.choose r (s + 1) + e * Ring.choose r s := by
  rw [add_comm r e, Ring.add_choose_eq _ hcomm.symm, Finset.Nat.sum_antidiagonal_succ]
  simp only [Ring.choose_zero_right, one_mul]
  congr 1
  rw [Finset.sum_eq_single (0, s)]
  · simp
  · intro ij hij hne
    have hi : ij.1 ≠ 0 := by
      intro hz
      apply hne
      ext <;> simp_all [Finset.mem_antidiagonal]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [hn, show n.succ + 1 = n + 2 by omega, choose_idempotent_eq_zero e he, zero_mul]
  · simp

/-- Binomial coefficients of a finite sum of commuting idempotents are the
sums of the corresponding products over subsets of fixed cardinality.
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:554-566]. -/
theorem choose_sum_idempotent_eq_sum_noncommProd {R ι : Type*}
    [Ring R] [BinomialRing R] (t : Finset ι) (f : ι → R)
    (hcomm : ∀ i ∈ t, ∀ j ∈ t, Commute (f i) (f j))
    (hidem : ∀ i ∈ t, f i * f i = f i) (s : ℕ) :
    Ring.choose (∑ i ∈ t, f i) s =
      ∑ u ∈ (t.powersetCard s).attach, u.val.noncommProd f
        (fun i hi j hj _ => hcomm i ((mem_powersetCard.mp u.property).1 hi)
          j ((mem_powersetCard.mp u.property).1 hj)) := by
  classical
  induction t using Finset.induction_on generalizing s with
  | empty =>
    have hp : (∑ u ∈ ((∅ : Finset ι).powersetCard s).attach,
        u.val.noncommProd f
          (fun i hi j hj _ => hcomm i ((mem_powersetCard.mp u.property).1 hi)
            j ((mem_powersetCard.mp u.property).1 hj))) =
        ∑ _u ∈ ((∅ : Finset ι).powersetCard s).attach, (1 : R) := by
      apply sum_congr rfl
      intro u hu
      have he : u.val = ∅ := subset_empty.mp (mem_powersetCard.mp u.property).1
      exact noncommProd_congr he (fun _ _ => rfl) _
    rw [hp]
    cases s <;> simp
  | @insert a t ha ih =>
    have htcomm : ∀ i ∈ t, ∀ j ∈ t, Commute (f i) (f j) :=
      fun i hi j hj => hcomm i (mem_insert_of_mem hi) j (mem_insert_of_mem hj)
    have htidem : ∀ i ∈ t, f i * f i = f i :=
      fun i hi => hidem i (mem_insert_of_mem hi)
    let prod : Finset ι → R := fun u => if hu : u ⊆ insert a t then
      u.noncommProd f (fun i hi j hj _ => hcomm i (hu hi) j (hu hj)) else 0
    have hsum (v : Finset ι) (hv : v ⊆ insert a t)
        (hc : ∀ i ∈ v, ∀ j ∈ v, Commute (f i) (f j)) (k : ℕ) :
        (∑ u ∈ (v.powersetCard k).attach, u.val.noncommProd f
          (fun i hi j hj _ => hc i ((mem_powersetCard.mp u.property).1 hi)
            j ((mem_powersetCard.mp u.property).1 hj))) =
          ∑ u ∈ v.powersetCard k, prod u := by
      rw [← sum_attach (v.powersetCard k) prod]
      apply sum_congr rfl
      intro u hu
      dsimp [prod]
      rw [dite_eq_left ((mem_powersetCard.mp u.property).1.trans hv)]
    rw [hsum (insert a t) Subset.rfl hcomm]
    cases s with
    | zero =>
      simp [prod]
      rfl
    | succ s =>
      have hdisj : Disjoint (t.powersetCard (s + 1))
          ((t.powersetCard s).image (insert a)) := by
        apply disjoint_left.mpr
        intro u hu hu'
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hu'
        exact ha ((mem_powersetCard.mp hu).1 (mem_insert_self _ _))
      rw [sum_insert ha, add_comm (f a), choose_add_idempotent_succ
        (∑ i ∈ t, f i) (f a)
        (Commute.sum_left t f (f a) (fun i hi =>
          hcomm i (mem_insert_of_mem hi) a (mem_insert_self _ _)))
        (hidem a (mem_insert_self _ _)), ih htcomm htidem, ih htcomm htidem,
        hsum t (subset_insert _ _) htcomm, hsum t (subset_insert _ _) htcomm,
        powersetCard_succ_insert ha, sum_union hdisj]
      congr 1
      rw [sum_image]
      · rw [mul_sum]
        apply sum_congr rfl
        intro u hu
        have hut : u ⊆ t := (mem_powersetCard.mp hu).1
        have hau : a ∉ u := fun h => ha (hut h)
        dsimp [prod]
        rw [dite_eq_left (insert_subset_insert a hut),
          dite_eq_left (hut.trans (subset_insert _ _))]
        exact (noncommProd_insert_of_notMem u a f _ hau).symm
      · intro u hu v hv huv
        have hau : a ∉ u := fun h => ha ((mem_powersetCard.mp hu).1 h)
        have hav : a ∉ v := fun h => ha ((mem_powersetCard.mp hv).1 h)
        simpa [hau, hav] using congrArg (fun w => w.erase a) huv

end QIT
