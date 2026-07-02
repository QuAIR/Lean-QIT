/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import QIT.States.TraceNorm.Distance
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Quantum entropy

Von Neumann entropy (spectral-sum), quantum relative entropy, conditional
entropy, and conditional mutual information. The trace norm is defined in
`QIT.States.TraceNorm.Distance`. Entropy is defined via the
eigenvalue sum (0 log 0 := 0 convention), avoiding the CFC.log eigenvalue-0
boundary. Relative entropy is exposed in bits, matching the base-2 entropy
convention used by conditional entropy and conditional mutual information.
The source definitions are registered from [Tomamichel2015FiniteResources,
renyi.tex:679-693], [Tomamichel2015FiniteResources, cond.tex:28-39], and
[SutterFawziRenner2015Recovery, universalRecMap.tex:166-169].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

noncomputable local instance matrixCStarAlgebra {n : Type u} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where

noncomputable local instance matrixNormalCFC {n : Type u} [Fintype n] [DecidableEq n] :
    ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance matrixNormalIsometricCFC {n : Type u} [Fintype n] [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instIsometricContinuousFunctionalCalculus

/-- log base 2. -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- x log_2 x with the 0 log 0 := 0 convention. -/
def xlog2 (x : ℝ) : ℝ := if x = 0 then 0 else x * log2 x

/-- States carry the topology induced by their density matrices. -/
instance State.instTopologicalSpace {a : Type u} [Fintype a] [DecidableEq a] :
    TopologicalSpace (State a) :=
  TopologicalSpace.induced State.matrix inferInstance

namespace State

/-- Von Neumann entropy S(ρ) = -Σ λᵢ log₂ λᵢ over the eigenvalues of ρ,
with 0 log 0 := 0. -/
def vonNeumann (ρ : State a) : ℝ :=
  -(Finset.univ.sum fun i => xlog2 ((ρ.pos.isHermitian).eigenvalues i))

@[fun_prop]
theorem continuous_matrix : Continuous (fun ρ : State a => ρ.matrix) :=
  continuous_induced_dom

private noncomputable def entropyCfcScalar (x : ℝ) : ℝ :=
  -(x * Real.log x / Real.log 2)

private noncomputable def entropyCfcComplex (z : ℂ) : ℂ :=
  (entropyCfcScalar z.re : ℂ)

private theorem entropyCfcScalar_eq_neg_xlog2 (x : ℝ) :
    entropyCfcScalar x = -xlog2 x := by
  unfold entropyCfcScalar xlog2 log2
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]
    ring

private theorem continuous_entropyCfcScalar : Continuous entropyCfcScalar := by
  unfold entropyCfcScalar
  exact (Real.continuous_mul_log.div_const _).neg

private theorem continuous_entropyCfcComplex : Continuous entropyCfcComplex := by
  unfold entropyCfcComplex
  exact Complex.continuous_ofReal.comp (continuous_entropyCfcScalar.comp Complex.continuous_re)

private theorem vonNeumann_eq_cfc_trace (ρ : State a) :
    ρ.vonNeumann = ((cfc entropyCfcComplex ρ.matrix).trace).re := by
  rw [State.vonNeumann]
  have hreal :
      cfc entropyCfcScalar ρ.matrix = cfc entropyCfcComplex ρ.matrix := by
    simpa [entropyCfcComplex] using
      (cfc_real_eq_complex (a := ρ.matrix) entropyCfcScalar
        (ha := ρ.pos.isHermitian.isSelfAdjoint))
  rw [← hreal]
  have hcfc :
      cfc entropyCfcScalar ρ.matrix =
        ρ.pos.isHermitian.cfc entropyCfcScalar :=
    Matrix.IsHermitian.cfc_eq (𝕜 := ℂ) ρ.pos.isHermitian entropyCfcScalar
  rw [hcfc]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  rw [Matrix.trace_diagonal]
  simp only [Function.comp_apply, entropyCfcScalar_eq_neg_xlog2]
  simp [Finset.sum_neg_distrib]

/-- Eigenvalues of a state sum to one. -/
private lemma eigenvalue_sum (ρ : State a) :
    ∑ i, ρ.pos.isHermitian.eigenvalues i = 1 := by
  have hc : (∑ i, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 := by
    exact ρ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
  exact Complex.ofReal_injective (by simpa using hc)

/-- Eigenvalues of a state are bounded above by one. -/
private lemma eigenvalue_le_one (ρ : State a) (i : a) :
    ρ.pos.isHermitian.eigenvalues i ≤ 1 := by
  have hnonneg (j : a) : 0 ≤ ρ.pos.isHermitian.eigenvalues j :=
    ρ.pos.eigenvalues_nonneg j
  have hsum : ∑ j, ρ.pos.isHermitian.eigenvalues j = 1 :=
    eigenvalue_sum ρ
  calc ρ.pos.isHermitian.eigenvalues i
      ≤ ρ.pos.isHermitian.eigenvalues i
        + ∑ j ∈ Finset.univ.erase i, ρ.pos.isHermitian.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
    _ = ∑ j, ρ.pos.isHermitian.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.pos.isHermitian.eigenvalues j) (Finset.mem_univ i)
    _ = 1 := hsum

private theorem spectrum_subset_stateInterval (ρ : State a) :
    spectrum ℂ ρ.matrix ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  intro z hz
  rw [ρ.pos.isHermitian.spectrum_eq_image_range] at hz
  rcases hz with ⟨x, ⟨i, rfl⟩, rfl⟩
  exact ⟨ρ.pos.isHermitian.eigenvalues i,
    ⟨ρ.pos.eigenvalues_nonneg i, eigenvalue_le_one ρ i⟩, rfl⟩

/-- Von Neumann entropy is continuous on finite-dimensional density states. -/
theorem vonNeumann_continuous : Continuous (fun ρ : State a => ρ.vonNeumann) := by
  let K : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    CompactIccSpace.isCompact_Icc.image Complex.continuous_ofReal
  have hcfc : Continuous fun ρ : State a =>
      (cfc entropyCfcComplex (ρ.matrix : Matrix a a ℂ) : Matrix a a ℂ) := by
    exact Continuous.cfc' (A := Matrix a a ℂ) (p := IsStarNormal)
      (s := K) hK entropyCfcComplex State.continuous_matrix
      (fun ρ => spectrum_subset_stateInterval ρ)
      (continuous_entropyCfcComplex.continuousOn)
      (fun ρ => ρ.pos.isHermitian.isSelfAdjoint.isStarNormal)
  have htrace : Continuous fun ρ : State a =>
      ((cfc entropyCfcComplex ρ.matrix).trace).re :=
    Complex.continuous_re.comp (Continuous.matrix_trace hcfc)
  exact htrace.congr fun ρ => (vonNeumann_eq_cfc_trace ρ).symm

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

/-- The matrix-log trace expression for a positive-definite state expands to
the spectral `λ log λ` sum. -/
theorem trace_mul_psdLog_eq_sum_eigenvalues_mul_log
    (ρ : State a) (hρ : ρ.matrix.PosDef) :
    ((ρ.matrix * psdLog ρ.matrix hρ).trace).re =
      ∑ i, hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hρ.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)
  let L : CMatrix a := Matrix.diagonal fun i => ((Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ)
  have hmat : ρ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hρ.1.spectral_theorem
  have hlog : psdLog ρ.matrix hρ = (U : CMatrix a) * L * star (U : CMatrix a) := by
    rw [psdLog, hρ.1.cfc_eq]
    simp [U, L, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]
  calc
    ((ρ.matrix * psdLog ρ.matrix hρ).trace).re =
        ((ρ.matrix * ((U : CMatrix a) * L * star (U : CMatrix a))).trace).re := by
      rw [hlog]
    _ = ((((U : CMatrix a) * D * star (U : CMatrix a)) *
          ((U : CMatrix a) * L * star (U : CMatrix a))).trace).re := by
      rw [hmat]
    _ = ((D * L).trace).re := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (U : CMatrix a)) (U : CMatrix a)
        (L * star (U : CMatrix a))]
      rw [Unitary.coe_star_mul_self]
      simp only [one_mul]
      rw [Matrix.trace_mul_comm (U : CMatrix a) (D * (L * star (U : CMatrix a)))]
      rw [← Matrix.mul_assoc D L (star (U : CMatrix a))]
      rw [Matrix.mul_assoc (D * L) (star (U : CMatrix a)) (U : CMatrix a)]
      rw [Unitary.coe_star_mul_self]
      simp
    _ = (∑ i, ((hρ.1.eigenvalues i : ℝ) : ℂ) *
          ((Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ)).re := by
      simp [D, L, Matrix.diagonal_mul_diagonal]
    _ = ∑ i, hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) := by
      simp

/-- Positive-definite states have the expected matrix-log trace formula for
von Neumann entropy. -/
theorem vonNeumann_eq_neg_trace_mul_psdLog_div_log_two
    (ρ : State a) (hρ : ρ.matrix.PosDef) :
    ρ.vonNeumann =
      -((ρ.matrix * psdLog ρ.matrix hρ).trace.re) / Real.log 2 := by
  classical
  have htrace := trace_mul_psdLog_eq_sum_eigenvalues_mul_log ρ hρ
  have hHerm : hρ.1 = ρ.pos.isHermitian := Subsingleton.elim _ _
  have hxlog (i : a) :
      xlog2 (ρ.pos.isHermitian.eigenvalues i) =
        hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) / Real.log 2 := by
    rw [← hHerm]
    unfold xlog2 log2
    have hpos : 0 < hρ.1.eigenvalues i := Matrix.PosDef.eigenvalues_pos hρ i
    simp [ne_of_gt hpos]
    ring
  rw [htrace]
  unfold vonNeumann
  simp_rw [hxlog]
  rw [← Finset.sum_div]
  ring

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Conditional von Neumann entropy `H(A|B)_ρ = H(AB)_ρ - H(B)_ρ`. -/
def conditionalEntropy (ρ : State (Prod a b)) : ℝ :=
  vonNeumann ρ - vonNeumann ρ.marginalB

@[simp]
theorem conditionalEntropy_eq (ρ : State (Prod a b)) :
    ρ.conditionalEntropy = vonNeumann ρ - vonNeumann ρ.marginalB := rfl

theorem marginalA_continuous :
    Continuous (fun ρ : State (Prod a b) => ρ.marginalA) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State (Prod a b) =>
    partialTraceB (a := a) (b := b) ρ.matrix
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro i'
  simp only [partialTraceB]
  refine continuous_finsetSum Finset.univ ?_
  intro j _
  exact (continuous_apply (i', j)).comp
    ((continuous_apply (i, j)).comp State.continuous_matrix)

theorem marginalB_continuous :
    Continuous (fun ρ : State (Prod a b) => ρ.marginalB) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State (Prod a b) =>
    partialTraceA (a := a) (b := b) ρ.matrix
  refine continuous_pi ?_
  intro j
  refine continuous_pi ?_
  intro j'
  simp only [partialTraceA]
  refine continuous_finsetSum Finset.univ ?_
  intro i _
  exact (continuous_apply (i, j')).comp
    ((continuous_apply (i, j)).comp State.continuous_matrix)

/-- Conditional entropy is continuous on finite-dimensional bipartite states. -/
theorem conditionalEntropy_continuous :
    Continuous (fun ρ : State (Prod a b) => ρ.conditionalEntropy) := by
  unfold conditionalEntropy
  exact State.vonNeumann_continuous.sub
    (State.vonNeumann_continuous.comp State.marginalB_continuous)

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
