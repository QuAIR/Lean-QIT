/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.PosSqrt
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Quantum entropy

Von Neumann entropy (spectral-sum), quantum relative entropy, conditional
entropy, and conditional mutual information, plus the trace norm (Schatten
1-norm) used by fidelity and Fuchs-van de Graaf. Entropy is defined via the
eigenvalue sum (0 log 0 := 0 convention), avoiding the CFC.log eigenvalue-0
boundary. Relative entropy is exposed in bits, matching the base-2 entropy
convention used by conditional entropy and conditional mutual information.
The source definitions are registered from [Tomamichel2015FiniteResources,
renyi.tex:679-693], [Tomamichel2015FiniteResources, cond.tex:28-39], and
[SutterFawziRenner2015Recovery, universalRecMap.tex:166-169].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- log base 2. -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- x log_2 x with the 0 log 0 := 0 convention. -/
def xlog2 (x : ℝ) : ℝ := if x = 0 then 0 else x * log2 x

/-- The trace norm (Schatten 1-norm) ‖M‖₁ = Tr √(Mᴴ M). -/
def traceNorm (M : CMatrix a) : ℝ :=
  (psdSqrt (Mᴴ * M)).trace.re

namespace State

/-- Von Neumann entropy S(ρ) = -Σ λᵢ log₂ λᵢ over the eigenvalues of ρ,
with 0 log 0 := 0. -/
def vonNeumann (ρ : State a) : ℝ :=
  -(Finset.univ.sum fun i => xlog2 ((ρ.pos.isHermitian).eigenvalues i))

/-- The natural log of a positive-definite matrix via continuous functional
calculus. Requires `PosDef` (invertible, strictly positive spectrum) so that
`Real.log` is continuous on the spectrum. -/
def psdLog (M : CMatrix a) (_hM : M.PosDef) : CMatrix a :=
  cfc Real.log M

/-- Quantum relative entropy D(ρ‖σ) in bits.

Both states must be positive-definite (full-rank) for CFC.log to apply. The
CFC logarithm is the natural logarithm, so the trace expression is divided by
`Real.log 2` to match the base-2 entropy convention. -/
def relativeEntropy (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) : ℝ :=
  ((ρ.matrix * psdLog ρ.matrix hρ).trace.re
    - (ρ.matrix * psdLog σ.matrix hσ).trace.re) / Real.log 2

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Conditional von Neumann entropy `H(A|B)_ρ = H(AB)_ρ - H(B)_ρ`. -/
def conditionalEntropy (ρ : State (Prod a b)) : ℝ :=
  vonNeumann ρ - vonNeumann ρ.marginalB

@[simp]
theorem conditionalEntropy_eq (ρ : State (Prod a b)) :
    ρ.conditionalEntropy = vonNeumann ρ - vonNeumann ρ.marginalB := rfl

variable {c : Type w} [Fintype c] [DecidableEq c]

/-- Conditional mutual information
`I(A:C|B)_ρ = H(AB)_ρ + H(BC)_ρ - H(B)_ρ - H(ABC)_ρ`
for a left-associated tripartite state `ρ : State ((A × B) × C)`. -/
def condMutualInfo (ρ : State (Prod (Prod a b) c)) : ℝ :=
  vonNeumann ρ.marginalAB + vonNeumann ρ.marginalBC
    - vonNeumann ρ.marginalBOfABC - vonNeumann ρ

@[simp]
theorem condMutualInfo_eq (ρ : State (Prod (Prod a b) c)) :
    ρ.condMutualInfo =
      vonNeumann ρ.marginalAB + vonNeumann ρ.marginalBC
        - vonNeumann ρ.marginalBOfABC - vonNeumann ρ := rfl

end State

end

end QIT
