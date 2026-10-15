/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Instrument
public import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# Finite quantum testers

Source operators use the full-transpose Born convention `Tr[Pᵀ R]` of
[Chiribella2009Networks, comblong-pub.tex:3422-3427]. Wires have the same
input-block/output-block order as `Comb.Normalized`. Tester normalization
is its dual recursion: the final output is an identity factor, and tracing
the final input of the remaining positive operator gives the preceding
tester. The internal empty prefix is scalar one. This is the tester
specialization of the comb trace constraints in
[Chiribella2009Networks, comblong-pub.tex:1504-1514].

In zero-based physical wire labels, the identity is on `O (N-1)` (wire
`2N-1`), followed by a trace over `I (N-1)` (wire `2N-2`). This explicit
ordering resolves the inconsistent endpoint/subscript labels in the source's
`normtest` display; for one tooth its entries are `ρ[i,i′] δ[o,o′]`, with
`Tr ρ = 1`, in our input-first storage order.

Normalization of Born probabilities is proved by contraction of these two
recursions. No physical realization or converse characterization is asserted.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder
namespace Tester

/-- Dual comb normalization, with no assumption that a wire is inhabited.
At each step `Θ` is positive, the final output is an identity factor, and
its final-input trace is a recursively normalized tester total. -/
def Normalized : {n : Nat} → (I O : Fin n → Type u) →
    [∀ j, Fintype (I j)] → [∀ j, DecidableEq (I j)] →
    [∀ j, Fintype (O j)] → [∀ j, DecidableEq (O j)] → CMatrix (Comb.Space I O) → Prop
  | 0, _, _, _, _, _, _, T => T = 1
  | n + 1, I, O, _, _, _, _, T =>
      ∃ Θ : CMatrix ((∀ j, I j) × (∀ j : Fin n, O j.castSucc)),
        Θ.PosSemidef ∧
        (∀ i i' o o', T (i, o) (i', o') =
          if o (Fin.last n) = o' (Fin.last n) then
            Θ (i, Fin.init o) (i', Fin.init o') else 0) ∧
        Normalized (fun j : Fin n => I j.castSucc) (fun j => O j.castSucc)
          (fun p q => ∑ z, Θ (Fin.snoc p.1 z, p.2) (Fin.snoc q.1 z, q.2))

/-- Entrywise contraction, equivalently the full-transpose trace pairing. -/
def pairing {α : Type*} [Fintype α] (T R : CMatrix α) : ℂ :=
  ∑ p, ∑ q, T p q * R p q

theorem pairing_eq_trace {α : Type*} [Fintype α] (T R : CMatrix α) :
    pairing T R = Matrix.trace (T.transpose * R) := by
  simp only [pairing, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

private theorem sum_snoc {n : Nat} (A : Fin (n+1) → Type u)
    [∀ j, Fintype (A j)] (f : (∀ j, A j) → ℂ) :
    (∑ x, f x) = ∑ a, ∑ x, f (Fin.snoc x a) := by
  rw [← (Fin.snocEquiv A).sum_comp f, Fintype.sum_prod_type]
  rfl

/-- Dual recursive constraints contract to scalar one against every comb. -/
theorem Normalized.pairing_eq_one {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {T R : CMatrix (Comb.Space I O)} (hT : Normalized I O T)
    (hR : Comb.Normalized I O R) : pairing T R = 1 := by
  classical
  induction n with
  | zero =>
      change T = 1 at hT
      change R = 1 at hR
      subst T; subst R
      simp [pairing, Matrix.one_apply]
  | succ n ih =>
      obtain ⟨Θ, _, hT, hΘ⟩ := hT
      obtain ⟨_, K, hK, hR⟩ := hR
      have hrec := ih hΘ hK
      have hout (i i' : ∀ j, I j) :
          (∑ o, ∑ o', T (i,o) (i',o') * R (i,o) (i',o')) =
          ∑ o, ∑ o', Θ (i,o) (i',o') *
            (if i (Fin.last n) = i' (Fin.last n) then
              K ((fun j => i j.castSucc),o) ((fun j => i' j.castSucc),o') else 0) := by
        simp_rw [sum_snoc O, hT, Fin.snoc_last, Fin.init_snoc, ite_mul, zero_mul,
          Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro o _
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hR]
      unfold pairing
      simp only [Fintype.sum_prod_type]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      simp_rw [hout]
      simp_rw [sum_snoc I, Fin.snoc_last, Fin.snoc_castSucc, mul_ite, mul_zero,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2; ext i
        rw [Finset.sum_comm]
        arg 2; ext i'
        rw [Finset.sum_comm]
        arg 2; ext o
        rw [Finset.sum_comm]
      simp only [pairing, Fintype.sum_prod_type, Finset.sum_mul] at hrec
      conv at hrec => lhs; arg 2; ext i; rw [Finset.sum_comm]
      exact hrec

end Tester

/-- A finite positive-length quantum tester. `operator` stores the source
operators `Pᵢ`, not the transposed measurement effects. Normalization is the
explicit dual comb recursion, not an assumption about Born probabilities. -/
structure QuantumTester {n : Nat} (I O : Fin (n+1) → Type u) (ι : Type v)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι] where
  operator : ι → CMatrix (Comb.Space I O)
  operator_posSemidef : ∀ a, (operator a).PosSemidef
  normalized : Tester.Normalized I O (∑ a, operator a)

namespace QuantumTester
variable {n : Nat} {I O : Fin (n+1) → Type u} {ι : Type v}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι]

/-- Measurement effects are the full transposes of the source operators. -/
def effect (T : QuantumTester I O ι) (a : ι) : CMatrix (Comb.Space I O) :=
  (T.operator a).transpose

/-- Full transpose preserves positivity. -/
theorem effect_posSemidef (T : QuantumTester I O ι) (a : ι) :
    (T.effect a).PosSemidef := (T.operator_posSemidef a).transpose

/-- Generalized Born probability. Its complex trace is proved real below. -/
def probability (T : QuantumTester I O ι) (a : ι) (R : DeterministicComb I O) : ℝ :=
  (Matrix.trace (T.effect a * R.choi)).re

/-- The real-valued probability equals the source's complex Born trace. -/
theorem probability_eq_born (T : QuantumTester I O ι) (a : ι)
    (R : DeterministicComb I O) :
    (T.probability a R : ℂ) = Matrix.trace ((T.operator a).transpose * R.choi) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im, effect] using
      (trace_mul_isHermitian_im_eq_zero (T.effect_posSemidef a).1 R.posSemidef.1).symm

/-- Every generalized Born probability is nonnegative. -/
theorem probability_nonneg (T : QuantumTester I O ι) (a : ι)
    (R : DeterministicComb I O) : 0 ≤ T.probability a R :=
  cMatrix_trace_mul_posSemidef_re_nonneg (T.effect_posSemidef a) R.posSemidef

/-- The generalized Born probabilities sum to one for every deterministic comb. -/
theorem sum_probability (T : QuantumTester I O ι) (R : DeterministicComb I O) :
    (∑ a, T.probability a R) = 1 := by
  have h := T.normalized.pairing_eq_one R.normalized
  have hsum : Tester.pairing (∑ a, T.operator a) R.choi =
      ∑ a, Tester.pairing (T.operator a) R.choi := by
    simp only [Tester.pairing, Matrix.sum_apply, Finset.sum_mul]
    conv_rhs =>
      rw [Finset.sum_comm]
      arg 2; ext p
      rw [Finset.sum_comm]
  rw [hsum] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.re_sum, Tester.pairing_eq_trace, Complex.one_re,
    probability, effect] using hre

/-- Each outcome is bounded above by one, including zero effects. -/
theorem probability_le_one (T : QuantumTester I O ι) (a : ι)
    (R : DeterministicComb I O) : T.probability a R ≤ 1 := by
  rw [← T.sum_probability R]
  exact Finset.single_le_sum (fun b _ => T.probability_nonneg b R) (Finset.mem_univ a)

end QuantumTester
end QIT.HigherOrder
