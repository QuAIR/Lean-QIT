/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.PiNorm
public import QIT.Util.TensorPower
public import QIT.Util.NewtonBinomial
public import QIT.Util.CommutingBinomial
public import QIT.Information.Entropy.BinaryEntropy

/-!
# Polynomial approximation of tensor-power projectors

The scalar input is the reflected AND approximant of
[Sherstov2020AlgorithmicPolynomials, algopoly.tex:2000-2020]. Only its
integer-grid properties are retained. The operator definitions and bounds
follow [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530].
-/

@[expose] public section

namespace QIT.QuantumPolyApprox

noncomputable section

open scoped QIT.Matrix Matrix.Norms.L2Operator

/-- The exact exponential error used for the NOR approximation. -/
def approximationError (c : ℝ) (n D : ℕ) : ℝ :=
  (2 : ℝ) ^ (-c * (D : ℝ)^2 / (n : ℝ))

/-- The projective-norm budget, with binary entropy measured in bits. -/
def approximationGamma (κ : ℝ) (n D : ℕ) : ℝ :=
  (2 * κ)^D * (2 : ℝ)^((n : ℝ) * binaryEntropy ((D : ℝ) / (n : ℝ)))

/-- Scalar NOR approximation supplied as an explicit external witness.
The grid bound is weaker than the interval bound in
[Sherstov2020AlgorithmicPolynomials, algopoly.tex:2000-2020].
This is Fact 2 in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:513-519].
Reflection of the variable and a change of exponential base give this form;
no coefficient estimate or operator conclusion is part of the input. -/
structure SherstovNORWitness (c : ℝ) : Prop where
  pos : 0 < c
  polynomial : ∀ n D : ℕ, 3 ≤ D → D ≤ n →
    ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ p.eval 0 = 1 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ n → |p.eval (k : ℝ)| ≤ approximationError c n D) ∧
      (∀ k : ℕ, k ≤ n → |p.eval (k : ℝ)| ≤ 1)

universe u
variable {b e : Type u} [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]

/-- Regroup joint channel-use registers into the receiver/environment bipartition. -/
def pairReindex (n : ℕ) :
    CMatrix (Fin n → b × e) ≃ₐ[ℂ] CMatrix ((Fin n → b) × (Fin n → e)) :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => b) (fun _ => e))

/-- One local complementary projector, in the receiver/environment bipartition. -/
def localDefect (P : CMatrix (b × e)) {n : ℕ} (i : Fin (n + 1)) :
    CMatrix ((Fin (n + 1) → b) × (Fin (n + 1) → e)) :=
  pairReindex (n + 1) (WireFam.deltaAt (fun _ : Fin (n + 1) => b × e) i P)

/-- The number of local complementary-projector excitations. -/
def countingOperator (P : CMatrix (b × e)) :
    (n : ℕ) → CMatrix ((Fin n → b) × (Fin n → e))
  | 0 => 0
  | n + 1 => ∑ i : Fin (n + 1), localDefect P i

/-- Apply a real polynomial to the counting operator through the canonical real algebra. -/
def projectorApproximation (p : Polynomial ℝ) (P : CMatrix (b × e)) (n : ℕ) :
    CMatrix ((Fin n → b) × (Fin n → e)) :=
  Polynomial.aeval (countingOperator P n) p

end

end QIT.QuantumPolyApprox
