/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Tester.Characterization
public import QIT.HigherOrder.Tester.BoundaryTransport

/-!
# Tester and instrument equivalence

Every finite tester is an actual `Comb.Superinstrument` after inserting
one-dimensional boundary wires, and removing those wires recovers every
operator and its Born action. This is the two-way source statement
[Chiribella2009Networks, comblong-pub.tex:3431-3437].
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder
open Tester

namespace QuantumTester
variable {n : Nat} {I O : Fin (n+1) → Type u} {ι : Type v}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι]

/-- A tester is determined by its outcome operators. -/
@[ext] theorem ext {T U : QuantumTester I O ι} (h : T.operator = U.operator) : T = U := by
  cases T
  cases U
  cases h
  rfl

/-- Each positive branch is below the total: the difference is exactly the
sum of the other PSD operators, before constructing any instrument. -/
theorem operator_le_sum (T : QuantumTester I O ι) (i : ι) :
    T.operator i ≤ ∑ j, T.operator j := by
  classical
  rw [Matrix.le_iff]
  have hs : (∑ j, T.operator j) - T.operator i =
      ∑ j ∈ Finset.univ.erase i, T.operator j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    abel
  rw [hs]
  exact Matrix.posSemidef_sum _ (fun j _ => T.operator_posSemidef j)

/-- The source tester as the existing finite comb instrument, with exactly
the same operators transported by a wire equivalence. -/
def toSuperinstrument (T : QuantumTester I O ι) :
    Comb.Superinstrument (paddedInput O) (paddedOutput I) ι where
  branch i := pad I O (T.operator i)
  branch_isProbabilistic i := ⟨(pad_posSemidef_iff I O _).mpr (T.operator_posSemidef i),
    pad I O (∑ j, T.operator j), (normalized_pad_iff I O _).mpr T.normalized,
    Comb.matReindex_le _ (T.operator_le_sum i)⟩
  total := ⟨pad I O (∑ j, T.operator j), (normalized_pad_iff I O _).mpr T.normalized⟩
  sum_branch_eq_total := (pad_sum I O Finset.univ T.operator).symm

@[simp] theorem toSuperinstrument_branch (T : QuantumTester I O ι) (i : ι) :
    T.toSuperinstrument.branch i = pad I O (T.operator i) := rfl

@[simp] theorem toSuperinstrument_total (T : QuantumTester I O ι) :
    T.toSuperinstrument.total.choi = pad I O (∑ i, T.operator i) := rfl

/-- The complete scalar action equals the original full-transpose pairing. -/
theorem toSuperinstrument_outcomeChoi_apply (T : QuantumTester I O ι) (i : ι)
    (R : CMatrix (Comb.Space I O))
    (a b : paddedInput O 0 × paddedOutput I (Fin.last (n+1))) :
    T.toSuperinstrument.outcomeChoi i (innerPad I O R) a b =
      Tester.pairing (T.operator i) R :=
  linkAction_pad_apply I O (T.operator i) R a b

/-- On a deterministic input, every scalar instrument outcome is precisely
the tester probability, including its zero imaginary part. -/
theorem toSuperinstrument_outcomeChoi_probability (T : QuantumTester I O ι) (i : ι)
    (R : DeterministicComb I O)
    (a b : paddedInput O 0 × paddedOutput I (Fin.last (n+1))) :
    T.toSuperinstrument.outcomeChoi i (innerPad I O R.choi) a b =
      (T.probability i R : ℂ) := by
  rw [T.toSuperinstrument_outcomeChoi_apply, Tester.pairing_eq_trace, T.probability_eq_born]

end QuantumTester

namespace Tester
variable {n : Nat} {I O : Fin (n+1) → Type u} {ι : Type v}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι]

/-- Remove singleton boundaries from every branch of an existing instrument.
Normalization is derived from its total, without an extra tester witness. -/
def ofSuperinstrument (M : Comb.Superinstrument (paddedInput O) (paddedOutput I) ι) :
    QuantumTester I O ι where
  operator i := unpad I O (M.branch i)
  operator_posSemidef i := (unpad_posSemidef_iff I O _).mpr (M.branch_posSemidef i)
  normalized := by
    apply (normalized_pad_iff I O _).mp
    rw [pad_sum]
    simp only [pad_unpad]
    rw [M.sum_branch_eq_total]
    exact M.total.normalized

@[simp] theorem ofSuperinstrument_operator
    (M : Comb.Superinstrument (paddedInput O) (paddedOutput I) ι) (i : ι) :
    (ofSuperinstrument M).operator i = unpad I O (M.branch i) := rfl

/-- Removing the boundary wires from the total recovers the tester total. -/
theorem ofSuperinstrument_sum
    (M : Comb.Superinstrument (paddedInput O) (paddedOutput I) ι) :
    (∑ i, (ofSuperinstrument M).operator i) = unpad I O M.total.choi := by
  apply (pad I O).injective
  rw [pad_sum, pad_unpad]
  simp only [ofSuperinstrument_operator, pad_unpad]
  exact M.sum_branch_eq_total

@[simp] theorem ofSuperinstrument_toSuperinstrument (T : QuantumTester I O ι) :
    ofSuperinstrument T.toSuperinstrument = T := by
  apply QuantumTester.ext
  funext i
  exact unpad_pad I O (T.operator i)

/-- Finite instruments are determined by their branches; the total is their sum. -/
theorem superinstrument_ext
    {M N : Comb.Superinstrument I O ι}
    (h : M.branch = N.branch) : M = N := by
  cases M with
  | mk branch hp total hs =>
    cases N with
    | mk branch' hp' total' hs' =>
      dsimp only at h
      cases h
      have ht : total = total' := by
        cases total with
        | mk choi hn =>
          cases total' with
          | mk choi' hn' =>
            dsimp only at hs hs'
            have hc := hs.symm.trans hs'
            cases hc
            rfl
      cases ht
      rfl

@[simp] theorem toSuperinstrument_ofSuperinstrument
    (M : Comb.Superinstrument (paddedInput O) (paddedOutput I) ι) :
    (ofSuperinstrument M).toSuperinstrument = M := by
  apply superinstrument_ext
  funext i
  exact pad_unpad I O (M.branch i)

/-- A branch-preserving equivalence of the actual bundled types. -/
def equivSuperinstrument :
    QuantumTester I O ι ≃ Comb.Superinstrument (paddedInput O) (paddedOutput I) ι where
  toFun := QuantumTester.toSuperinstrument
  invFun := ofSuperinstrument
  left_inv := ofSuperinstrument_toSuperinstrument
  right_inv := toSuperinstrument_ofSuperinstrument

/-- The complete source equivalence, starting with the PSD-qualified real
Born probabilities of a fixed operator family and preserving each branch. -/
theorem exists_superinstrument_iff_born (P : ι → CMatrix (Comb.Space I O)) :
    (∃ M : Comb.Superinstrument (paddedInput O) (paddedOutput I) ι,
      ∀ i, M.branch i = pad I O (P i)) ↔
      (∀ i, (P i).PosSemidef) ∧
      ∀ R, Comb.Normalized I O R →
        (∀ i, 0 ≤ (pairing (P i) R).re) ∧ (∑ i, (pairing (P i) R).re) = 1 := by
  rw [← QuantumTester.exists_iff_born]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨ofSuperinstrument M, ?_⟩
    funext i
    simp only [ofSuperinstrument_operator, hM, unpad_pad]
  · rintro ⟨T, rfl⟩
    exact ⟨T.toSuperinstrument, fun _ => rfl⟩

section ArbitraryBoundary
variable (A B : Type u) [Fintype A] [DecidableEq A] [Unique A]
  [Fintype B] [DecidableEq B] [Unique B]

/-- The same tester/instrument equivalence on any two one-dimensional boundary
carriers, preserving the original operators by singleton wire identification. -/
def equivSuperinstrumentWith : QuantumTester I O ι ≃
    Comb.Superinstrument (boundaryInput A O) (boundaryOutput B I) ι where
  toFun T := {
    branch := fun i => padWith I O A B (T.operator i)
    branch_isProbabilistic := fun i =>
      ⟨(padWith_posSemidef_iff I O A B _).mpr (T.operator_posSemidef i),
        padWith I O A B (∑ j, T.operator j),
        (normalized_padWith_iff I O A B _).mpr T.normalized,
        Comb.matReindex_le _ (T.operator_le_sum i)⟩
    total := ⟨padWith I O A B (∑ j, T.operator j),
      (normalized_padWith_iff I O A B _).mpr T.normalized⟩
    sum_branch_eq_total := (padWith_sum I O A B Finset.univ T.operator).symm }
  invFun M := {
    operator := fun i => unpadWith I O A B (M.branch i)
    operator_posSemidef := fun i =>
      (unpadWith_posSemidef_iff I O A B _).mpr (M.branch_posSemidef i)
    normalized := by
      apply (normalized_padWith_iff I O A B _).mp
      rw [padWith_sum]
      simp only [padWith_unpadWith]
      rw [M.sum_branch_eq_total]
      exact M.total.normalized }
  left_inv T := by
    apply QuantumTester.ext
    funext i
    exact unpadWith_padWith I O A B (T.operator i)
  right_inv M := by
    apply superinstrument_ext
    funext i
    exact padWith_unpadWith I O A B (M.branch i)

@[simp] theorem equivSuperinstrumentWith_branch (T : QuantumTester I O ι) (i : ι) :
    (equivSuperinstrumentWith A B T).branch i = padWith I O A B (T.operator i) := rfl

@[simp] theorem equivSuperinstrumentWith_total (T : QuantumTester I O ι) :
    (equivSuperinstrumentWith A B T).total.choi =
      padWith I O A B (∑ i, T.operator i) := rfl

@[simp] theorem equivSuperinstrumentWith_symm_operator
    (M : Comb.Superinstrument (boundaryInput A O) (boundaryOutput B I) ι) (i : ι) :
    ((equivSuperinstrumentWith A B).symm M).operator i =
      unpadWith I O A B (M.branch i) := rfl

/-- Generic boundary identification preserves the complete complex scalar action. -/
theorem equivSuperinstrumentWith_outcomeChoi_apply (T : QuantumTester I O ι) (i : ι)
    (R : CMatrix (Comb.Space I O))
    (a b : boundaryInput A O 0 × boundaryOutput B I (Fin.last (n+1))) :
    (equivSuperinstrumentWith A B T).outcomeChoi i (innerPadWith I O A B R) a b =
      pairing (T.operator i) R :=
  linkAction_padWith_apply I O A B (T.operator i) R a b

/-- The source-shaped operational equivalence also holds for arbitrary
singleton boundary types, with every branch fixed to its source operator. -/
theorem exists_superinstrumentWith_iff_born (P : ι → CMatrix (Comb.Space I O)) :
    (∃ M : Comb.Superinstrument (boundaryInput A O) (boundaryOutput B I) ι,
      ∀ i, M.branch i = padWith I O A B (P i)) ↔
      (∀ i, (P i).PosSemidef) ∧
      ∀ R, Comb.Normalized I O R →
        (∀ i, 0 ≤ (pairing (P i) R).re) ∧ (∑ i, (pairing (P i) R).re) = 1 := by
  rw [← QuantumTester.exists_iff_born]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨(equivSuperinstrumentWith A B).symm M, ?_⟩
    funext i
    simp only [equivSuperinstrumentWith_symm_operator, hM, unpadWith_padWith]
  · rintro ⟨T, rfl⟩
    exact ⟨equivSuperinstrumentWith A B T, fun _ => rfl⟩

end ArbitraryBoundary
end Tester
end QIT.HigherOrder
