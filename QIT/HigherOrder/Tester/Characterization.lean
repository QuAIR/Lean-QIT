/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Tester.Boundary

/-!
# Operational characterization of quantum testers

For positive source operators the full-transpose Born probabilities on every
deterministic input characterize the existing dual recursive normalization.
The converse pads by scalar boundary wires and uses the necessary direction of
comb normalization. This is the argument of
[Chiribella2009Networks, comblong-pub.tex:3431-3437], applied to the operational
definition [Chiribella2009Networks, comblong-pub.tex:3422-3427].
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder
namespace Tester

/-- The Born pairing commutes with a finite sum of source operators. -/
theorem pairing_sum_left {α : Type u} [Fintype α] {ι : Type v} [Fintype ι]
    (P : ι → CMatrix α) (R : CMatrix α) :
    pairing (∑ i, P i) R = ∑ i, pairing (P i) R := by
  simp only [pairing, Matrix.sum_apply, Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2; ext p
    rw [Finset.sum_comm]

/-- Positive source and input operators give real complex Born traces. -/
theorem pairing_im_eq_zero {α : Type u} [Fintype α]
    {P R : CMatrix α} (hP : P.PosSemidef) (hR : R.PosSemidef) :
    (pairing P R).im = 0 := by
  rw [pairing_eq_trace]
  exact trace_mul_isHermitian_im_eq_zero hP.transpose.isHermitian hR.isHermitian

/-- The real Born value is nonnegative under the explicit PSD premises. -/
theorem pairing_re_nonneg {α : Type u} [Fintype α]
    {P R : CMatrix α} (hP : P.PosSemidef) (hR : R.PosSemidef) :
    0 ≤ (pairing P R).re := by
  classical
  rw [pairing_eq_trace]
  exact cMatrix_trace_mul_posSemidef_re_nonneg hP.transpose hR

section Characterization
variable {n : Nat} {I O : Fin (n+1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- Ordinary normalization of Born values, with PSD explicit, forces the
actual tester recursion. No ancillary preservation premise is supplied. -/
theorem normalized_of_pairing_eq_one {T : CMatrix (Comb.Space I O)}
    (hT : T.PosSemidef)
    (h : ∀ R, Comb.Normalized I O R → pairing T R = 1) : Normalized I O T := by
  apply (normalized_pad_iff I O T).mp
  apply Comb.normalized_of_actionTrace (pad I O T) ((pad_posSemidef_iff I O T).mpr hT)
  intro X hX
  have hR : Comb.Normalized I O (innerUnpad I O X) :=
    (normalized_innerPad_iff I O _).mp (by simpa using hX)
  rw [← innerPad_innerUnpad I O X]
  ext a b
  rw [actionTrace_pad_apply]
  simpa [Matrix.one_apply, Subsingleton.elim a b] using h _ hR

/-- The source operational normalization is equivalent to the existing
recursive normalization for PSD operators. -/
theorem normalized_iff_pairing_eq_one {T : CMatrix (Comb.Space I O)}
    (hT : T.PosSemidef) : Normalized I O T ↔
      ∀ R, Comb.Normalized I O R → pairing T R = 1 :=
  ⟨fun h _ hR => h.pairing_eq_one hR, normalized_of_pairing_eq_one hT⟩

/-- For a positive finite family, real probability normalization is exactly
normalization of its sum; imaginary parts vanish rather than being discarded. -/
theorem normalized_sum_iff_born {ι : Type v} [Fintype ι]
    (P : ι → CMatrix (Comb.Space I O)) (hP : ∀ i, (P i).PosSemidef) :
    Normalized I O (∑ i, P i) ↔
      ∀ R, Comb.Normalized I O R → (∑ i, (pairing (P i) R).re) = 1 := by
  rw [normalized_iff_pairing_eq_one (Matrix.posSemidef_sum Finset.univ (fun i _ => hP i))]
  constructor
  · intro h R hR
    have he := congrArg Complex.re (h R hR)
    simpa only [pairing_sum_left, Complex.re_sum, Complex.one_re] using he
  · intro h R hR
    rw [pairing_sum_left]
    apply Complex.ext
    · simpa only [Complex.re_sum, Complex.one_re] using h R hR
    · simp only [Complex.im_sum, pairing_im_eq_zero (hP _) hR.posSemidef,
        Finset.sum_const_zero, Complex.one_im]

end Characterization
end Tester

namespace QuantumTester
variable {n : Nat} {I O : Fin (n+1) → Type u} {ι : Type v}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι]

/-- Construct a tester directly from the operational Born assumptions. -/
def ofBorn (P : ι → CMatrix (Comb.Space I O)) (hP : ∀ i, (P i).PosSemidef)
    (h : ∀ R, Comb.Normalized I O R → (∑ i, (Tester.pairing (P i) R).re) = 1) :
    QuantumTester I O ι where
  operator := P
  operator_posSemidef := hP
  normalized := (Tester.normalized_sum_iff_born P hP).mpr h

@[simp] theorem ofBorn_operator (P : ι → CMatrix (Comb.Space I O))
    (hP : ∀ i, (P i).PosSemidef)
    (h : ∀ R, Comb.Normalized I O R → (∑ i, (Tester.pairing (P i) R).re) = 1) :
    (ofBorn P hP h).operator = P := rfl

/-- The full source definition: positivity is separate from the real Born
probabilities, and the resulting tester preserves every original operator. -/
theorem exists_iff_born (P : ι → CMatrix (Comb.Space I O)) :
    (∃ T : QuantumTester I O ι, T.operator = P) ↔
      (∀ i, (P i).PosSemidef) ∧
      ∀ R, Comb.Normalized I O R →
        (∀ i, 0 ≤ (Tester.pairing (P i) R).re) ∧
          (∑ i, (Tester.pairing (P i) R).re) = 1 := by
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨T.operator_posSemidef, fun R hR => ⟨?_, ?_⟩⟩
    · exact fun i => Tester.pairing_re_nonneg (T.operator_posSemidef i) hR.posSemidef
    · exact (Tester.normalized_sum_iff_born T.operator T.operator_posSemidef).mp T.normalized R hR
  · rintro ⟨hP, h⟩
    exact ⟨ofBorn P hP (fun R hR => (h R hR).2), rfl⟩

end QuantumTester
end QIT.HigherOrder
