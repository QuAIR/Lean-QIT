/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Admissible

/-!
# Finite superinstruments

A finite superinstrument is a finite family of probabilistic combs on fixed
wires whose operators sum to one deterministic comb, as in
[Chiribella2009Networks, comblong-pub.tex:3266-3268]; the source also calls
such a family a generalized N-instrument. Each branch is a probabilistic
comb in the domination sense of
[Chiribella2009Networks, comblong-pub.tex:1425-1433]. Feeding an inner comb
through one branch uses the link product of
[Chiribella2009Networks, comblong-pub.tex:315-327], and positivity of that
outcome action is the link-product positivity of
[Chiribella2009Networks, comblong-pub.tex:342-355]. Outcome families are
finite but not assumed inhabited. For an empty outcome family the sum is
zero; whether it can be normalized depends on the wire systems. In
particular, the tester specialization excludes empty outcomes when a
deterministic input comb exists.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder.Comb

/-- The link action of a positive operator on a positive inner comb is
positive; no normalization of either operator is used. -/
theorem linkAction_posSemidef {n : Nat} (I O : Fin (n + 1) → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (J : CMatrix (Space I O)) (X : CMatrix (Space (innerInput O) (innerOutput I)))
    (hJ : J.PosSemidef) (hX : X.PosSemidef) :
    (linkAction I O J X).PosSemidef := by
  rw [← actionMap_eq_linkAction]
  exact MatrixMap.isCompletelyPositive_mapsPositive _
    ((actionMap_cp_iff I O J).mpr hJ) X hX

/-- A finite superinstrument: a finite family of probabilistic combs on
fixed wires whose operators sum to one deterministic comb of the same
shape. The source also calls such a family a generalized N-instrument.
[Chiribella2009Networks, comblong-pub.tex:3266-3268]. -/
structure Superinstrument {n : Nat} (I O : Fin (n + 1) → Type u) (ι : Type v)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι] where
  branch : ι → CMatrix (Space I O)
  branch_isProbabilistic : ∀ i, IsProbabilistic I O (branch i)
  total : DeterministicComb I O
  sum_branch_eq_total : (∑ i, branch i) = total.choi

/-- Every branch operator of a superinstrument is positive semidefinite. -/
theorem Superinstrument.branch_posSemidef {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) (i : ι) :
    (M.branch i).PosSemidef := (M.branch_isProbabilistic i).1

/-- Every branch of a superinstrument is dominated by the total
deterministic comb; the domination is a consequence of the family sum, not
an extra field. -/
theorem Superinstrument.branch_le_total {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) (i : ι) :
    M.branch i ≤ M.total.choi := by
  classical
  rw [Matrix.le_iff, ← M.sum_branch_eq_total]
  have hsum : (∑ j, M.branch j) - M.branch i =
      ∑ other ∈ Finset.univ.erase i, M.branch other := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    abel
  rw [hsum]
  exact Matrix.posSemidef_sum (Finset.univ.erase i) fun other _ =>
    (M.branch_isProbabilistic other).1

/-- The branch operators of a superinstrument sum to a recursively
normalized operator. -/
theorem Superinstrument.sum_branch_normalized {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) :
    Normalized I O (∑ i, M.branch i) := by
  rw [M.sum_branch_eq_total]
  exact M.total.normalized

/-- The total comb of a superinstrument is probabilistic through its own
normalization. -/
theorem Superinstrument.total_isProbabilistic {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) :
    IsProbabilistic I O M.total.choi := M.total.normalized.isProbabilistic

/-- With a single outcome, that outcome's branch is the total comb. -/
theorem Superinstrument.branch_eq_total {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    [Unique ι] (M : Superinstrument I O ι) :
    M.branch default = M.total.choi := by
  rw [← M.sum_branch_eq_total, Finset.univ_unique, Finset.sum_singleton]

/-- With a single outcome, that outcome's branch is itself a deterministic
normalized operator. -/
theorem Superinstrument.branch_normalized_of_unique {n : Nat}
    {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    [Unique ι] (M : Superinstrument I O ι) :
    Normalized I O (M.branch default) := by
  rw [M.branch_eq_total]
  exact M.total.normalized

/-- The one-outcome superinstrument carried by a deterministic comb. -/
def Superinstrument.ofDeterministicComb {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (R : DeterministicComb I O) : Superinstrument I O (Fin 1) where
  branch _ := R.choi
  branch_isProbabilistic _ := R.normalized.isProbabilistic
  total := R
  sum_branch_eq_total := by simp

@[simp] theorem Superinstrument.ofDeterministicComb_total {n : Nat}
    {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (R : DeterministicComb I O) :
    (ofDeterministicComb R).total = R := rfl

/-- The Choi operator of one outcome's action on an inner comb: the link
action of that outcome's branch. The source order inserts the inner comb
first and contracts the shared inner wires.
[Chiribella2009Networks, comblong-pub.tex:315-327]. -/
def Superinstrument.outcomeChoi {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) (i : ι)
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    CMatrix (I 0 × O (Fin.last n)) :=
  linkAction I O (M.branch i) X

/-- The outcome action of a superinstrument on a positive inner comb is
positive; each branch operator is positive by construction, so the outcome
action inherits link-product positivity.
[Chiribella2009Networks, comblong-pub.tex:342-355]. -/
theorem Superinstrument.outcomeChoi_posSemidef {n : Nat}
    {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) (i : ι)
    (X : CMatrix (Space (innerInput O) (innerOutput I)))
    (hX : X.PosSemidef) :
    (M.outcomeChoi i X).PosSemidef :=
  linkAction_posSemidef I O (M.branch i) X (M.branch_posSemidef i) hX

end QIT.HigherOrder.Comb
