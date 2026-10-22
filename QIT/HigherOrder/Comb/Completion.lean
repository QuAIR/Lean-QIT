/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Instrument
public import QIT.HigherOrder.Comb.Closure

/-!
# Completion of dominated combs

A positive operator below a deterministic comb completes to the two-outcome
instrument consisting of that operator and its complement. This is derived
from probabilistic-comb domination and the finite-instrument definition in
[Chiribella2009Networks, comblong-pub.tex:1425-1433] and
[Chiribella2009Networks, comblong-pub.tex:3266-3268]. No inverse or strict
positivity is needed. The action uses the source link product
[Chiribella2009Networks, comblong-pub.tex:315-327]; complete admissibility of
the total supplies the deterministic completion of each branch action.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder.Comb

section Completion
variable {n : Nat} {I O : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The complement of a dominated positive operator is probabilistic with
the same deterministic completion, including singular completions. -/
theorem isProbabilistic_complement (S : DeterministicComb I O)
    (R : CMatrix (Space I O)) (hR : R.PosSemidef) (hRS : R ≤ S.choi) :
    IsProbabilistic I O (S.choi - R) := by
  refine ⟨Matrix.le_iff.mp hRS, S.choi, S.normalized, ?_⟩
  apply Matrix.le_iff.mpr
  simpa only [sub_sub_cancel] using hR

/-- Complete a dominated comb to a two-outcome instrument. Outcome `false`
is the given operator and outcome `true` is its positive complement. -/
def Superinstrument.ofDominated (S : DeterministicComb I O)
    (R : CMatrix (Space I O)) (hR : R.PosSemidef) (hRS : R ≤ S.choi) :
    Superinstrument I O Bool where
  branch b := if b then S.choi - R else R
  branch_isProbabilistic b := by
    cases b
    · exact ⟨hR, S.choi, S.normalized, hRS⟩
    · exact isProbabilistic_complement S R hR hRS
  total := S
  sum_branch_eq_total := by simp

@[simp] theorem Superinstrument.ofDominated_branch_false (S : DeterministicComb I O)
    (R : CMatrix (Space I O)) (hR : R.PosSemidef) (hRS : R ≤ S.choi) :
    (ofDominated S R hR hRS).branch false = R := rfl

@[simp] theorem Superinstrument.ofDominated_branch_true (S : DeterministicComb I O)
    (R : CMatrix (Space I O)) (hR : R.PosSemidef) (hRS : R ≤ S.choi) :
    (ofDominated S R hR hRS).branch true = S.choi - R := rfl

@[simp] theorem Superinstrument.ofDominated_total (S : DeterministicComb I O)
    (R : CMatrix (Space I O)) (hR : R.PosSemidef) (hRS : R ≤ S.choi) :
    (ofDominated S R hR hRS).total = S := rfl

/-- Every probabilistic comb occurs as an outcome of a finite instrument. -/
theorem IsProbabilistic.exists_superinstrument {R : CMatrix (Space I O)}
    (hR : IsProbabilistic I O R) :
    ∃ M : Superinstrument I O Bool, M.branch false = R := by
  obtain ⟨hpos, S, hS, hRS⟩ := hR
  exact ⟨Superinstrument.ofDominated ⟨S, hS⟩ R hpos hRS, rfl⟩

/-- Choi-space action respects subtraction of outer operators. -/
theorem actionMap_sub (A B : CMatrix (Space I O)) :
    actionMap I O (A - B) = actionMap I O A - actionMap I O B := by
  apply MatrixMap.choi_inj
  rw [choi_actionMap]
  change WireFam.matReindex (actionEquiv I O) (A - B) =
    MatrixMap.choi (actionMap I O A) - MatrixMap.choi (actionMap I O B)
  rw [choi_actionMap, choi_actionMap, WireFam.matReindex_sub]

/-- The complement acts by subtracting the original action from the total. -/
theorem linkAction_sub (A B : CMatrix (Space I O))
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    linkAction I O (A - B) X = linkAction I O A X - linkAction I O B X := by
  simp only [← actionMap_eq_linkAction, actionMap_sub, LinearMap.sub_apply]

/-- The original completion outcome acts by the original operator. -/
@[simp] theorem Superinstrument.ofDominated_outcomeChoi_false (S : DeterministicComb I O)
    (R : CMatrix (Space I O)) (hR : R.PosSemidef) (hRS : R ≤ S.choi)
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    (ofDominated S R hR hRS).outcomeChoi false X = linkAction I O R X := rfl

/-- The complementary outcome is exactly the difference of link actions. -/
@[simp] theorem Superinstrument.ofDominated_outcomeChoi_true (S : DeterministicComb I O)
    (R : CMatrix (Space I O)) (hR : R.PosSemidef) (hRS : R ≤ S.choi)
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    (ofDominated S R hR hRS).outcomeChoi true X =
      linkAction I O S.choi X - linkAction I O R X :=
  linkAction_sub S.choi R X

/-- Summing all outcomes recovers the action of the deterministic total. -/
theorem Superinstrument.sum_outcomeChoi {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι)
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    (∑ i, M.outcomeChoi i X) = linkAction I O M.total.choi X := by
  rw [← M.sum_branch_eq_total]
  simp only [Superinstrument.outcomeChoi, ← actionMap_eq_linkAction]
  ext p q
  simp only [actionMap, MatrixMap.ofChoiMatrix_apply, WireFam.matReindex_apply,
    Matrix.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext a
  rw [Finset.sum_comm]

end Completion

section Action
variable {n : Nat} {I O : Fin (n + 2) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- Domination gives a common deterministic completion of the higher-order
map, including on joint inputs with arbitrary boundary spectators. -/
theorem IsProbabilistic.isProbabilisticMap {R : CMatrix (Space I O)}
    (hR : IsProbabilistic I O R) : IsProbabilisticMap I O (actionMap I O R) := by
  obtain ⟨hpos, S, hS, hRS⟩ := hR
  refine ⟨(actionMap_cp_iff I O R).mpr hpos, actionMap I O S,
    hS.isDeterministicMap, ?_⟩
  rw [← actionMap_sub]
  exact (actionMap_cp_iff I O (S - R)).mpr (Matrix.le_iff.mp hRS)

/-- Each instrument branch is a source-shaped probabilistic higher-order map. -/
theorem Superinstrument.branch_isProbabilisticMap {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) (i : ι) :
    IsProbabilisticMap I O (actionMap I O (M.branch i)) :=
  (M.branch_isProbabilistic i).isProbabilisticMap

/-- On a deterministic inner comb, each outcome is the Choi operator of an
actual trace-nonincreasing CP operation. -/
theorem Superinstrument.outcomeChoi_operation {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι) (i : ι)
    (X : CMatrix (Space (innerInput O) (innerOutput I)))
    (hX : Normalized (innerInput O) (innerOutput I) X) :
    MatrixMap.TraceNonincreasingCP (MatrixMap.ofChoiMatrix (M.outcomeChoi i X)) := by
  apply (MatrixMap.traceNonincreasingCP_iff_choi _).mpr
  rw [MatrixMap.choi_ofChoiMatrix]
  refine ⟨M.outcomeChoi_posSemidef i X hX.posSemidef, ?_⟩
  have hle := partialTraceB_mono (linkAction_le (M.branch_le_total i) hX.posSemidef)
  rwa [(normalized_linkAction M.total.choi M.total.normalized X hX).2] at hle

/-- Forgetting the outcome recovers the normalization of a channel. -/
theorem Superinstrument.sum_outcomeChoi_trace {ι : Type v} [Fintype ι]
    (M : Superinstrument I O ι)
    (X : CMatrix (Space (innerInput O) (innerOutput I)))
    (hX : Normalized (innerInput O) (innerOutput I) X) :
    partialTraceB (∑ i, M.outcomeChoi i X) = 1 := by
  rw [M.sum_outcomeChoi]
  exact (normalized_linkAction M.total.choi M.total.normalized X hX).2

end Action
end QIT.HigherOrder.Comb
