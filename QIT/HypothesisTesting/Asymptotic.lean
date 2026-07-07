/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HypothesisTesting.Basic
public import QIT.HypothesisTesting.Audenaert
public import QIT.Information.Renyi.Renyi
public import QIT.Symmetry.SymmetricSubspace
public import QIT.States.Schatten
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Asymptotic binary hypothesis-testing notation

This module provides the statement-level asymptotic API needed for binary
discrimination over IID tensor powers.  It reuses the binary-test convention
from `QIT.HypothesisTesting` and the tensor-power state API.

The optimal equal-prior error and Chernoff coefficient are represented in
extended nonnegative/extended real types so zero error or zero coefficient maps
to the extended exponent `⊤`.  This matches the asymptotic exponent shape in
[Tomamichel2015FiniteResources, apps.tex:53-60],
[Tomamichel2015FiniteResources, apps.tex:68-71], and
[Audenaert2006QuantumChernoff, audenaert-2006-quantum-chernoff.tex:265-280]
without asserting the QCB proof.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal ENNReal Topology
open Filter Matrix Polynomial

namespace QIT

universe u v

noncomputable section

private theorem asymptotic_spectrum_real_diagonal_ofReal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> ℝ) :
    spectrum ℝ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) = Set.range d := by
  ext r
  rw [← spectrum.algebraMap_mem_iff ℂ]
  change (r : ℂ) ∈ spectrum ℂ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) ↔
    r ∈ Set.range d
  rw [spectrum_diagonal]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Complex.ofReal_injective hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

private theorem asymptotic_aeval_diagonal_ofReal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> ℝ) (p : ℝ[X]) :
    aeval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) p =
      Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  let dC : n -> ℂ := fun i => (d i : ℂ)
  change aeval (Matrix.diagonal dC) p =
    Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ))
  rw [show Matrix.diagonal dC = Matrix.diagonalAlgHom (R := ℝ) dC by rfl]
  rw [Polynomial.aeval_algHom (Matrix.diagonalAlgHom (R := ℝ)) dC]
  rw [Polynomial.aeval_pi]
  ext i j
  by_cases h : i = j
  · subst j
    simpa [Matrix.diagonal, dC, Polynomial.aeval_def] using
      (Polynomial.eval₂_at_apply (p := p) (algebraMap ℝ ℂ) (d i))
  · simp [Matrix.diagonal, h]

private theorem asymptotic_cfc_diagonal_ofReal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> ℝ) (f : ℝ -> ℝ) :
    cfc f (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) =
      Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  obtain ⟨p, hp⟩ :=
    (Polynomial.exists_eval_eq_iff d (fun i => f (d i))).mpr (by
      intro i j hij
      simp [hij])
  calc
    cfc f (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) =
        cfc p.eval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) := by
      apply cfc_congr
      intro x hx
      rw [asymptotic_spectrum_real_diagonal_ofReal d] at hx
      rcases hx with ⟨i, rfl⟩
      exact (hp i).symm
    _ = aeval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) p := by
      exact cfc_polynomial (q := p)
        (a := (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n))
        (ha := by
          rw [isSelfAdjoint_iff, star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
          ext i j
          by_cases h : i = j
          · subst j
            simp
          · simp [Matrix.diagonal, h])
    _ = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
      rw [asymptotic_aeval_diagonal_ofReal d p]
      ext i j
      by_cases h : i = j
      · subst j
        simp [hp i]
      · simp [Matrix.diagonal, h]

private theorem rpow_diagonal_ofReal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> ℝ) (hd : ∀ i, 0 ≤ d i) (s : ℝ) :
    CFC.rpow (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) s =
      Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) := by
  change ((Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) ^ s) =
    Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))
  have hnonneg : 0 ≤ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n) :=
    Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (d i : ℂ)
        exact_mod_cast hd i))
  rw [CFC.rpow_eq_cfc_real (a := (Matrix.diagonal fun i => (d i : ℂ) : CMatrix n))
    (y := s) hnonneg]
  exact asymptotic_cfc_diagonal_ofReal d (fun x => x ^ s)

private theorem rpow_conjStarAlgAut {n : Type u} [Fintype n] [DecidableEq n]
    (u : Matrix.unitaryGroup n ℂ) {A : CMatrix n} (hA : A.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Unitary.conjStarAlgAut ℂ _ u A) s =
      Unitary.conjStarAlgAut ℂ _ u (CFC.rpow A s) := by
  change (Unitary.conjStarAlgAut ℂ _ u A) ^ s =
    Unitary.conjStarAlgAut ℂ _ u (A ^ s)
  have hmap_nonneg : 0 ≤ Unitary.conjStarAlgAut ℂ (CMatrix n) u A := by
    rw [Unitary.conjStarAlgAut_apply]
    exact Matrix.nonneg_iff_posSemidef.mpr
      (hA.mul_mul_conjTranspose_same (u : CMatrix n))
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.rpow_eq_cfc_real (a := Unitary.conjStarAlgAut ℂ (CMatrix n) u A) (y := s)
    hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa using
    (StarAlgHomClass.map_cfc
      (Unitary.conjStarAlgAut ℂ (CMatrix n) u)
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix n => (u : CMatrix n) * A * star (u : CMatrix n)
        fun_prop)).symm

theorem cMatrix_rpow_kronecker
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) :=
  cMatrix_rpow_kronecker_nonneg hA hB hs0

private theorem unitary_row_normSq_sum_local {n : Type u} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, Complex.normSq ((U : CMatrix n) i j) = 1 := by
  have hunit : (U : CMatrix n) * star (U : CMatrix n) = 1 := by
    exact Unitary.coe_mul_star_self U
  have hij := congrFun (congrFun hunit i) i
  have hre := congrArg Complex.re hij
  simpa [Matrix.mul_apply, Matrix.one_apply, Complex.normSq_eq_conj_mul_self,
    mul_comm] using hre

private theorem unitary_col_normSq_sum_local {n : Type u} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (j : n) :
    ∑ i, Complex.normSq ((U : CMatrix n) i j) = 1 := by
  have hunit : star (U : CMatrix n) * (U : CMatrix n) = 1 := by
    exact Unitary.coe_star_mul_self U
  have hij := congrFun (congrFun hunit j) j
  have hre := congrArg Complex.re hij
  simpa [Matrix.mul_apply, Matrix.one_apply, Complex.normSq_eq_conj_mul_self,
    mul_comm] using hre

private theorem trace_mul_two_unitary_conj_diagonal_ofReal_re {n : Type u}
    [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n ℂ) (d e : n → ℝ) :
    ((((U : CMatrix n) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix n)) *
      ((V : CMatrix n) * (Matrix.diagonal fun i => (e i : ℂ)) *
        star (V : CMatrix n))).trace).re =
      ∑ i : n, ∑ j : n,
        d i * e j * Complex.normSq ((star (U : CMatrix n) * (V : CMatrix n)) i j) := by
  let D : CMatrix n := Matrix.diagonal fun i => (d i : ℂ)
  let E : CMatrix n := Matrix.diagonal fun i => (e i : ℂ)
  let W : CMatrix n := star (U : CMatrix n) * (V : CMatrix n)
  have htrace :
      (((U : CMatrix n) * D * star (U : CMatrix n)) *
        ((V : CMatrix n) * E * star (V : CMatrix n))).trace =
        (D * W * E * star W).trace := by
    calc
      (((U : CMatrix n) * D * star (U : CMatrix n)) *
        ((V : CMatrix n) * E * star (V : CMatrix n))).trace =
          ((U : CMatrix n) *
            (D * star (U : CMatrix n) * ((V : CMatrix n) * E * star (V : CMatrix n)))).trace := by
            congr 1
            noncomm_ring
      _ = ((D * star (U : CMatrix n) * ((V : CMatrix n) * E * star (V : CMatrix n))) *
            (U : CMatrix n)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (D * (star (U : CMatrix n) * (V : CMatrix n)) *
            E * (star (V : CMatrix n) * (U : CMatrix n))).trace := by
            congr 1
            noncomm_ring
      _ = (D * W * E * star W).trace := by
            simp [W, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  rw [htrace]
  change ((D * W * E * star W).trace).re =
    ∑ i : n, ∑ j : n, d i * e j * Complex.normSq (W i j)
  simp [D, E, Matrix.trace, Matrix.mul_apply, Matrix.diagonal,
    Matrix.star_apply, Complex.normSq_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

private theorem matrix_mul_star_diag_re_eq_normSq_sum {n : Type u}
    [Fintype n] [DecidableEq n] (A : CMatrix n) (i : n) :
    ((A * star A) i i).re = ∑ j, Complex.normSq (A i j) := by
  simp [Matrix.mul_apply, Complex.normSq]

private theorem projection_conjugate_diag_re_eq_row_normSq {n : Type u}
    [Fintype n] [DecidableEq n] (P : CMatrix n)
    (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (U V : Matrix.unitaryGroup n ℂ) (i : n) :
    ((star (U : CMatrix n) * P * (U : CMatrix n)) i i).re =
      ∑ j, Complex.normSq ((star (U : CMatrix n) * P * (V : CMatrix n)) i j) := by
  let A : CMatrix n := star (U : CMatrix n) * P * (V : CMatrix n)
  have hAA :
      A * star A = star (U : CMatrix n) * P * (U : CMatrix n) := by
    have hV : (V : CMatrix n) * star (V : CMatrix n) = 1 :=
      Unitary.coe_mul_star_self V
    have hPstar : star P = P := hPherm
    simp [A, Matrix.mul_assoc]
    calc
      star (U : CMatrix n) * (P * ((V : CMatrix n) *
          (star (V : CMatrix n) * (star P * (U : CMatrix n))))) =
          star (U : CMatrix n) * (P *
            (((V : CMatrix n) * star (V : CMatrix n)) * (star P * (U : CMatrix n)))) := by
            rw [Matrix.mul_assoc]
      _ = star (U : CMatrix n) * (P * (1 * (star P * (U : CMatrix n)))) := by
            rw [hV]
      _ = star (U : CMatrix n) * (P * (P * (U : CMatrix n))) := by
            rw [hPstar]
            simp
      _ = star (U : CMatrix n) * ((P * P) * (U : CMatrix n)) := by
            rw [Matrix.mul_assoc]
      _ = star (U : CMatrix n) * (P * (U : CMatrix n)) := by
            rw [hPidem]
  have hdiag := congrFun (congrFun hAA i) i
  have hre := congrArg Complex.re hdiag
  rw [← hre]
  exact matrix_mul_star_diag_re_eq_normSq_sum A i

private theorem trace_mul_unitary_conj_diagonal_ofReal_arbitrary_re {n : Type u}
    [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) (B : CMatrix n) :
    ((((U : CMatrix n) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix n)) * B).trace).re =
      ∑ i : n, d i *
        ((star (U : CMatrix n) * B * (U : CMatrix n)) i i).re := by
  let D : CMatrix n := Matrix.diagonal fun i => (d i : ℂ)
  let B' : CMatrix n := star (U : CMatrix n) * B * (U : CMatrix n)
  have htrace :
      (((U : CMatrix n) * D * star (U : CMatrix n)) * B).trace =
        (D * B').trace := by
    calc
      (((U : CMatrix n) * D * star (U : CMatrix n)) * B).trace =
          ((U : CMatrix n) * (D * (star (U : CMatrix n) * B))).trace := by
            congr 1
            noncomm_ring
      _ = ((D * (star (U : CMatrix n) * B)) * (U : CMatrix n)).trace := by
            exact Matrix.trace_mul_comm (U : CMatrix n)
              (D * (star (U : CMatrix n) * B))
      _ = (D * B').trace := by
            simp [B', Matrix.mul_assoc]
  have hdiag :
      (D * B').trace = ∑ i, ((d i : ℝ) : ℂ) * B' i i := by
    simp [D, Matrix.trace, Matrix.diagonal_mul]
  have hre := congrArg Complex.re (htrace.trans hdiag)
  simpa [B', Complex.mul_re] using hre

private theorem complex_normSq_add_le_two_sum (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hnorm : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hzw : 0 ≤ ‖z + w‖ := norm_nonneg (z + w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖), mul_self_nonneg (‖z + w‖), hnorm]

private theorem half_min_weight_normSq_add_le_weighted_normSq
    {A B u v w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw0 : 0 ≤ w)
    (hw : w ≤ 2 * (u + v)) :
    (1 / 2 : ℝ) * min (A * w) (B * w) ≤ A * u + B * v := by
  by_cases hAB : A ≤ B
  · have hmin : min (A * w) (B * w) = A * w := by
      exact min_eq_left (mul_le_mul_of_nonneg_right hAB hw0)
    rw [hmin]
    have hAw : A * w ≤ A * (2 * (u + v)) :=
      mul_le_mul_of_nonneg_left hw hA
    nlinarith
  · have hBA : B ≤ A := le_of_not_ge hAB
    have hmin : min (A * w) (B * w) = B * w := by
      exact min_eq_right (mul_le_mul_of_nonneg_right hBA hw0)
    rw [hmin]
    have hBw : B * w ≤ B * (2 * (u + v)) :=
      mul_le_mul_of_nonneg_left hw hB
    nlinarith


variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- The Petz/Renyi Chernoff trace objective is real. -/
theorem petzRenyi_trace_im_eq_zero (rho sigma : State a) (s : ℝ) :
    ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).im = 0 :=
  trace_mul_posSemidef_im_eq_zero (rho.rpowMatrix_posSemidef s)
    (sigma.rpowMatrix_posSemidef (1 - s))

/-- The Petz/Renyi Chernoff trace objective is nonnegative. -/
theorem petzRenyi_trace_re_nonneg (rho sigma : State a) (s : ℝ) :
    0 ≤ ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re :=
  trace_mul_posSemidef_re_nonneg (rho.rpowMatrix_posSemidef s)
    (sigma.rpowMatrix_posSemidef (1 - s))

/-- Nonnegative real coefficient `Tr(ρ^s σ^(1-s))` used by the Chernoff objective. -/
def petzRenyiCoefficient (rho sigma : State a) (s : ℝ) : ℝ≥0 :=
  ⟨((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re,
    rho.petzRenyi_trace_re_nonneg sigma s⟩

/-- Under full-rank hypotheses, the Petz/Renyi Chernoff coefficient is strictly positive. -/
theorem petzRenyiCoefficient_pos_of_posDef (rho sigma : State a)
    (hρ : rho.matrix.PosDef) (hσ : sigma.matrix.PosDef) (s : ℝ) :
    0 < rho.petzRenyiCoefficient sigma s := by
  haveI : Nonempty a := rho.nonempty
  dsimp [petzRenyiCoefficient]
  exact trace_mul_posDef_re_pos
    (rho.rpowMatrix_posDef_of_posDef hρ s)
    (sigma.rpowMatrix_posDef_of_posDef hσ (1 - s))

/-- The nonnegative coefficient is exactly the complex trace objective. -/
theorem petzRenyiCoefficient_trace_eq (rho sigma : State a) (s : ℝ) :
    ((rho.petzRenyiCoefficient sigma s : ℝ) : ℂ) =
      (CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace := by
  apply Complex.ext
  · rfl
  · simpa [petzRenyiCoefficient] using (rho.petzRenyi_trace_im_eq_zero sigma s).symm

theorem petzRenyiCoefficient_prod {b : Type v} [Fintype b] [DecidableEq b]
    (rho₁ sigma₁ : State a) (rho₂ sigma₂ : State b)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (rho₁.prod rho₂).petzRenyiCoefficient (sigma₁.prod sigma₂) s =
      rho₁.petzRenyiCoefficient sigma₁ s * rho₂.petzRenyiCoefficient sigma₂ s := by
  apply NNReal.eq
  apply Complex.ofReal_injective
  calc
    (((rho₁.prod rho₂).petzRenyiCoefficient (sigma₁.prod sigma₂) s : ℝ) : ℂ) =
        (CFC.rpow (rho₁.prod rho₂).matrix s *
          CFC.rpow (sigma₁.prod sigma₂).matrix (1 - s)).trace := by
      exact State.petzRenyiCoefficient_trace_eq (rho₁.prod rho₂) (sigma₁.prod sigma₂) s
    _ =
        ((CFC.rpow rho₁.matrix s * CFC.rpow sigma₁.matrix (1 - s)).trace) *
          ((CFC.rpow rho₂.matrix s * CFC.rpow sigma₂.matrix (1 - s)).trace) := by
      rw [prod_matrix_kronecker rho₁ rho₂, prod_matrix_kronecker sigma₁ sigma₂]
      rw [cMatrix_rpow_kronecker rho₁.pos rho₂.pos hs0]
      rw [cMatrix_rpow_kronecker sigma₁.pos sigma₂.pos (sub_nonneg.mpr hs1)]
      change
        (Matrix.kroneckerMap (fun x y => x * y)
            (CFC.rpow rho₁.matrix s) (CFC.rpow rho₂.matrix s) *
          Matrix.kroneckerMap (fun x y => x * y)
            (CFC.rpow sigma₁.matrix (1 - s)) (CFC.rpow sigma₂.matrix (1 - s))).trace =
        (CFC.rpow rho₁.matrix s * CFC.rpow sigma₁.matrix (1 - s)).trace *
          (CFC.rpow rho₂.matrix s * CFC.rpow sigma₂.matrix (1 - s)).trace
      rw [← Matrix.mul_kronecker_mul]
      rw [Matrix.trace_kronecker]
    _ = (((rho₁.petzRenyiCoefficient sigma₁ s *
          rho₂.petzRenyiCoefficient sigma₂ s : ℝ≥0) : ℝ) : ℂ) := by
      rw [← State.petzRenyiCoefficient_trace_eq rho₁ sigma₁ s]
      rw [← State.petzRenyiCoefficient_trace_eq rho₂ sigma₂ s]
      simp

theorem petzRenyiCoefficient_tensorPower (rho sigma : State a)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    (rho.tensorPower n).petzRenyiCoefficient (sigma.tensorPower n) s =
      rho.petzRenyiCoefficient sigma s ^ n := by
  induction n with
  | zero =>
      rw [State.tensorPower_zero, State.tensorPower_zero]
      apply NNReal.eq
      apply Complex.ofReal_injective
      rw [State.petzRenyiCoefficient_trace_eq]
      change (((1 : CMatrix PUnit) ^ s * (1 : CMatrix PUnit) ^ (1 - s)).trace) = 1
      rw [CFC.one_rpow, CFC.one_rpow, one_mul, Matrix.trace_one]
      norm_num
  | succ n ih =>
      rw [State.tensorPower_succ, State.tensorPower_succ]
      calc
        (rho.prod (rho.tensorPower n)).petzRenyiCoefficient
            (sigma.prod (sigma.tensorPower n)) s =
            rho.petzRenyiCoefficient sigma s *
              (rho.tensorPower n).petzRenyiCoefficient (sigma.tensorPower n) s := by
          exact petzRenyiCoefficient_prod rho sigma (rho.tensorPower n) (sigma.tensorPower n)
            hs0 hs1
        _ = rho.petzRenyiCoefficient sigma s ^ (n + 1) := by
          rw [ih]
          simp [pow_succ, mul_comm]

/-- Audenaert's trace inequality gives the one-shot Chernoff coefficient lower bound.

This is the equal-prior direct-bound bridge:
`1 - D(ρ,σ) ≤ Tr(ρ^s σ^(1-s))` for `0 ≤ s ≤ 1`, with `D` the repository's
normalized trace distance.  It is derived from the registered Audenaert
primitive [Audenaert2006QuantumChernoff, audenaert-2006-quantum-chernoff.tex:296-306]. -/
theorem one_sub_normalizedTraceDistance_le_petzRenyiCoefficient
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 - rho.normalizedTraceDistance sigma ≤
      (rho.petzRenyiCoefficient sigma s : ℝ) := by
  have hAud := audenaertTraceInequality (a := a) (s := s) hs0 hs1 rho.pos sigma.pos
  have hcoeff :
      (rho.petzRenyiCoefficient sigma s : ℝ) =
        ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re := rfl
  have htraceNorm :
      traceNorm (rho.matrix - sigma.matrix) =
        (CFC.abs (rho.matrix - sigma.matrix)).trace.re := rfl
  have hrhs :
      ((rho.matrix + sigma.matrix - CFC.abs (rho.matrix - sigma.matrix)).trace).re / 2 =
        1 - rho.normalizedTraceDistance sigma := by
    rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq]
    simp [QIT.traceDistance]
    rw [htraceNorm]
    simp [rho.trace_eq_one, sigma.trace_eq_one]
    ring
  rw [hcoeff]
  exact hrhs ▸ hAud

/-- Extended-real Chernoff exponent `-log Tr(ρ^s σ^(1-s))`. -/
def petzChernoffExponent (rho sigma : State a) (s : ℝ) : EReal :=
  - ENNReal.log (rho.petzRenyiCoefficient sigma s : ℝ≥0∞)

/-- A zero Petz/Renyi coefficient gives infinite extended Chernoff exponent. -/
theorem petzChernoffExponent_eq_top_of_petzRenyiCoefficient_eq_zero
    (rho sigma : State a) (s : ℝ)
    (h : rho.petzRenyiCoefficient sigma s = 0) :
    rho.petzChernoffExponent sigma s = ⊤ := by
  simp [petzChernoffExponent, h]

/-- A positive Petz/Renyi coefficient gives the finite real-log Chernoff exponent. -/
theorem petzChernoffExponent_eq_coe_neg_log_of_petzRenyiCoefficient_pos
    (rho sigma : State a) (s : ℝ)
    (h : 0 < rho.petzRenyiCoefficient sigma s) :
    rho.petzChernoffExponent sigma s =
      ((- Real.log (rho.petzRenyiCoefficient sigma s : ℝ) : ℝ) : EReal) := by
  have h0 : (rho.petzRenyiCoefficient sigma s : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast h.ne'
  have htop : ((rho.petzRenyiCoefficient sigma s : ℝ≥0∞) ≠ ⊤) := by
    simp
  simp [petzChernoffExponent, ENNReal.log_pos_real h0 htop, EReal.coe_neg]

theorem petzChernoffExponent_tensorPower (rho sigma : State a)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    (rho.tensorPower n).petzChernoffExponent (sigma.tensorPower n) s =
      (n : EReal) * rho.petzChernoffExponent sigma s := by
  unfold State.petzChernoffExponent
  rw [State.petzRenyiCoefficient_tensorPower rho sigma hs0 hs1 n]
  rw [show ((rho.petzRenyiCoefficient sigma s ^ n : ℝ≥0) : ℝ≥0∞) =
      (rho.petzRenyiCoefficient sigma s : ℝ≥0∞) ^ n by norm_num]
  rw [ENNReal.log_pow]
  rw [mul_neg]

/-- Base-2 Chernoff exponent `-log₂ Tr(ρ^s σ^(1-s))`.

The existing `petzChernoffExponent` uses natural logarithms through
`ENNReal.log`; this real-valued companion uses the repository's `log2`
convention so it can be compared directly with `State.petzRenyi`. -/
def petzChernoffExponentLog2 (rho sigma : State a) (s : ℝ) : ℝ :=
  - log2 (rho.petzRenyiCoefficient sigma s : ℝ)

/-- The base-2 Chernoff exponent is `(1-s)` times the Petz Renyi divergence. -/
theorem petzChernoffExponentLog2_eq_one_sub_mul_petzRenyi
    (rho sigma : State a) (hρ : rho.matrix.PosDef) (hσ : sigma.matrix.PosDef)
    (s : ℝ) (hs_pos : 0 < s) (hs_ne_one : s ≠ 1) :
    rho.petzChernoffExponentLog2 sigma s =
      (1 - s) * rho.petzRenyi sigma hρ hσ s hs_pos hs_ne_one := by
  unfold petzChernoffExponentLog2 petzRenyi
  change
    - log2 ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace.re) =
      (1 - s) *
        ((1 / (s - 1)) *
          log2 ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace.re))
  unfold log2
  field_simp [hs_ne_one]
  ring

/-- Chernoff distance as the supremum of the extended-real Chernoff exponent over `0 ≤ s ≤ 1`. -/
def chernoffDistance (rho sigma : State a) : EReal :=
  ⨆ s : Set.Icc (0 : ℝ) 1, rho.petzChernoffExponent sigma s.1

end State

namespace BinaryHypothesisTest

/-- The normalized extended negative log `-(1/(n+1)) log x`. -/
def normalizedNegLog (n : Nat) (x : ℝ≥0∞) : EReal :=
  -(((((n + 1 : Nat) : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log x)

/-- The finite real counterpart of `normalizedNegLog`, using `ENNReal.toReal`. -/
def normalizedNegLogReal (n : Nat) (x : ℝ≥0∞) : ℝ :=
  -((((n + 1 : Nat) : ℝ)⁻¹ : ℝ) * Real.log x.toReal)

/-- A zero input makes the normalized extended negative log equal to `⊤`. -/
theorem normalizedNegLog_eq_top_of_eq_zero (n : Nat) (x : ℝ≥0∞) (hx : x = 0) :
    normalizedNegLog n x = ⊤ := by
  have hpos : 0 < ((↑n + 1 : ℝ)⁻¹ : ℝ) := by
    exact inv_pos.mpr (by positivity)
  simp [normalizedNegLog, hx, EReal.coe_mul_bot_of_pos hpos]

/-- On positive finite inputs, `normalizedNegLog` is the coercion of its real counterpart. -/
theorem normalizedNegLog_eq_coe_real_of_ne_zero_ne_top
    (n : Nat) (x : ℝ≥0∞) (h0 : x ≠ 0) (htop : x ≠ ⊤) :
    normalizedNegLog n x = ((normalizedNegLogReal n x : ℝ) : EReal) := by
  simp [normalizedNegLog, normalizedNegLogReal, ENNReal.log_pos_real h0 htop,
    EReal.coe_mul, EReal.coe_neg]

/-- Positive real inputs reduce the normalized extended negative log to the
ordinary natural-log expression. -/
theorem normalizedNegLog_ofReal_eq_coe_real (n : Nat) {x : ℝ}
    (hx : 0 < x) :
    normalizedNegLog n (ENNReal.ofReal x) =
      ((-((((n + 1 : Nat) : ℝ)⁻¹) * Real.log x) : ℝ) : EReal) := by
  rw [normalizedNegLog_eq_coe_real_of_ne_zero_ne_top]
  · unfold normalizedNegLogReal
    rw [ENNReal.toReal_ofReal hx.le]
  · exact ENNReal.ofReal_ne_zero_iff.mpr hx
  · exact ENNReal.ofReal_ne_top

/-- The normalized extended negative log is order reversing in its error input. -/
theorem normalizedNegLog_antitone (n : Nat) {x y : ℝ≥0∞} (hxy : x ≤ y) :
    normalizedNegLog n y ≤ normalizedNegLog n x := by
  unfold normalizedNegLog
  have hlog : ENNReal.log x ≤ ENNReal.log y := ENNReal.log_le_log hxy
  have hcoef : (0 : EReal) ≤ (((((n + 1 : Nat) : ℝ)⁻¹ : ℝ) : EReal)) := by
    positivity
  apply EReal.neg_le_neg_iff.mpr
  exact mul_le_mul_of_nonneg_left hlog hcoef

/-- A probability-valued `ℝ≥0∞` input bounded by one is finite. -/
theorem ennreal_ne_top_of_le_one (x : ℝ≥0∞) (hx : x ≤ 1) : x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top hx

/-- Finite real normalized logs lift to finite `EReal` limits. -/
theorem normalizedNegLog_tendsto_coe_of_eventually_ne_zero_ne_top_real_tendsto
    {x : Nat → ℝ≥0∞} {L : ℝ}
    (hfinite : ∀ᶠ n in atTop, x n ≠ 0 ∧ x n ≠ ⊤)
    (hlim : Tendsto (fun n : Nat => normalizedNegLogReal n (x n)) atTop (𝓝 L)) :
    Tendsto (fun n : Nat => normalizedNegLog n (x n)) atTop (𝓝 (L : EReal)) := by
  refine (EReal.tendsto_coe.mpr hlim).congr' (hfinite.mono ?_)
  intro n hn
  exact (normalizedNegLog_eq_coe_real_of_ne_zero_ne_top n (x n) hn.1 hn.2).symm

/-- Real normalized logs tending to `+∞` lift to the `EReal` top limit. -/
theorem normalizedNegLog_tendsto_top_of_eventually_ne_top_real_tendsto_atTop
    {x : Nat → ℝ≥0∞}
    (htop : ∀ᶠ n in atTop, x n ≠ ⊤)
    (hlim : Tendsto (fun n : Nat => normalizedNegLogReal n (x n)) atTop atTop) :
    Tendsto (fun n : Nat => normalizedNegLog n (x n)) atTop (𝓝 (⊤ : EReal)) := by
  have hnonzero : ∀ᶠ n in atTop, x n ≠ 0 := by
    have hgt : ∀ᶠ n in atTop, (0 : ℝ) < normalizedNegLogReal n (x n) :=
      hlim.eventually_gt_atTop 0
    filter_upwards [hgt] with n hn hx
    have hz : normalizedNegLogReal n (x n) = 0 := by
      simp [normalizedNegLogReal, hx]
    linarith
  refine (EReal.tendsto_coe_nhds_top_iff.mpr hlim).congr'
    ((hnonzero.and htop).mono ?_)
  intro n hn
  exact (normalizedNegLog_eq_coe_real_of_ne_zero_ne_top n (x n) hn.1 hn.2).symm

/-- If the input sequence is eventually zero, the normalized extended negative log tends to `⊤`. -/
theorem normalizedNegLog_tendsto_top_of_eventually_eq_zero
    {x : Nat → ℝ≥0∞}
    (hzero : ∀ᶠ n in atTop, x n = 0) :
    Tendsto (fun n : Nat => normalizedNegLog n (x n)) atTop (𝓝 (⊤ : EReal)) := by
  refine tendsto_const_nhds.congr' (hzero.mono ?_)
  intro n hn
  exact (normalizedNegLog_eq_top_of_eq_zero n (x n) hn).symm

/-- Optimal equal-prior error over all binary tests on `n` IID copies. -/
def optimalEqualPriorTensorPowerError (rho sigma : State a) (n : Nat) : ℝ≥0∞ :=
  ⨅ T : TensorPowerHypothesisTest a n, (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞)

/-- The optimal tensor-power equal-prior error is bounded by one. -/
theorem optimalEqualPriorTensorPowerError_le_one (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerError rho sigma n ≤ 1 := by
  classical
  have hT :
      (BinaryHypothesisTest.equalPriorTensorPowerError
        ((State.tensorPower rho n).helstromTest (State.tensorPower sigma n))
        rho sigma : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (BinaryHypothesisTest.equalPriorError_le_one
      ((State.tensorPower rho n).helstromTest (State.tensorPower sigma n))
      (State.tensorPower rho n) (State.tensorPower sigma n))
  exact (iInf_le _ ((State.tensorPower rho n).helstromTest (State.tensorPower sigma n))).trans hT

/-- The optimal tensor-power equal-prior error is finite. -/
theorem optimalEqualPriorTensorPowerError_ne_top (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerError rho sigma n ≠ ⊤ :=
  ennreal_ne_top_of_le_one
    (optimalEqualPriorTensorPowerError rho sigma n)
    (optimalEqualPriorTensorPowerError_le_one rho sigma n)

/-- Audenaert-derived finite-`n` upper bound for the optimal equal-prior error.

For every `0 ≤ s ≤ 1`, the optimal error on `n` IID copies is bounded by
`1/2 * (Tr(ρ^s σ^(1-s)))^n`, matching the direct finite-copy route registered
from [Gour2024Resources, BookQRT.tex:15887-15909].  The asymptotic squeeze and
converse are intentionally downstream. -/
theorem optimalEqualPriorTensorPowerError_le_half_petzRenyiCoefficient_pow
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    optimalEqualPriorTensorPowerError rho sigma n ≤
      (((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ n : ℝ≥0) : ℝ≥0∞) := by
  classical
  let T : TensorPowerHypothesisTest a n :=
    (State.tensorPower rho n).helstromTest (State.tensorPower sigma n)
  have hChernoff :
      1 - (State.tensorPower rho n).normalizedTraceDistance (State.tensorPower sigma n) ≤
        ((rho.petzRenyiCoefficient sigma s) ^ n : ℝ) := by
    have h :=
      State.one_sub_normalizedTraceDistance_le_petzRenyiCoefficient
        (rho.tensorPower n) (sigma.tensorPower n) hs0 hs1
    rwa [State.petzRenyiCoefficient_tensorPower rho sigma hs0 hs1 n] at h
  have hHelstrom :
      (T.equalPriorTensorPowerError rho sigma : ℝ) =
        (1 / 2 : ℝ) *
          (1 - (State.tensorPower rho n).normalizedTraceDistance (State.tensorPower sigma n)) := by
    simpa [T, BinaryHypothesisTest.equalPriorTensorPowerError] using
      State.helstromTest_equalPriorError_eq (rho.tensorPower n) (sigma.tensorPower n)
  have hTest :
      (T.equalPriorTensorPowerError rho sigma : ℝ) ≤
        ((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ n : ℝ≥0) := by
    rw [hHelstrom]
    exact mul_le_mul_of_nonneg_left hChernoff (by norm_num)
  have hTestENN :
      (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞) ≤
        (((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ n : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hTest
  exact (iInf_le _ T).trans hTestENN

/-- The `1 / 2` finite-copy prefactor does not change the direct Chernoff exponent lift.

For copy number `n + 1`, the inequality is proved by taking the
`1 / (n + 1)`-power of `(1 / 2) * c ^ (n + 1)` and using
`((1 / 2) * c ^ (n + 1)) ^ (1 / (n + 1)) ≤ c`. This explicitly covers the
zero-coefficient case, where both logarithmic sides are infinite after negation. -/
theorem petzChernoffExponent_le_normalizedNegLog_half_petzRenyiCoefficient_pow
    (rho sigma : State a) (s : ℝ) (n : Nat) :
    rho.petzChernoffExponent sigma s ≤
      normalizedNegLog n
        ((((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ (n + 1) : ℝ≥0) :
          ℝ≥0∞)) := by
  let c : ℝ≥0 := rho.petzRenyiCoefficient sigma s
  have hroot :
      (((((1 / 2 : ℝ≥0) * c ^ (n + 1) : ℝ≥0) : ℝ≥0∞) ^
          (((n + 1 : Nat) : ℝ)⁻¹)) ≤ (c : ℝ≥0∞)) := by
    have hN : (n + 1 : Nat) ≠ 0 := by omega
    have ha_nonneg : 0 ≤ (((n + 1 : Nat) : ℝ)⁻¹) := by positivity
    calc
      ((((1 / 2 : ℝ≥0) * c ^ (n + 1) : ℝ≥0) : ℝ≥0∞) ^
          (((n + 1 : Nat) : ℝ)⁻¹))
          = (((1 / 2 : ℝ≥0) : ℝ≥0∞) * ((c : ℝ≥0∞) ^ (n + 1))) ^
              (((n + 1 : Nat) : ℝ)⁻¹) := by
            norm_num
      _ = (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ (((n + 1 : Nat) : ℝ)⁻¹)) *
            (((c : ℝ≥0∞) ^ (n + 1)) ^ (((n + 1 : Nat) : ℝ)⁻¹)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ha_nonneg]
      _ = (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ (((n + 1 : Nat) : ℝ)⁻¹)) *
            (c : ℝ≥0∞) := by
          rw [ENNReal.pow_rpow_inv_natCast hN]
      _ ≤ 1 * (c : ℝ≥0∞) := by
          gcongr
          exact ENNReal.rpow_le_one (by norm_num) ha_nonneg
      _ = (c : ℝ≥0∞) := by simp
  have hlogroot := ENNReal.log_le_log hroot
  unfold normalizedNegLog
  apply EReal.neg_le_neg_iff.mpr
  simpa [State.petzChernoffExponent, c, ENNReal.log_rpow] using hlogroot

/-- Exact exponent sequence `n ↦ -(1/(n+1)) log P*_{e,n+1}`. -/
def optimalEqualPriorTensorPowerErrorExponent (rho sigma : State a) (n : Nat) : EReal :=
  normalizedNegLog n (optimalEqualPriorTensorPowerError rho sigma (n + 1))

/-- The optimal-error exponent is the normalized extended negative log at index `n + 1`. -/
theorem optimalEqualPriorTensorPowerErrorExponent_eq_normalizedNegLog
    (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n =
      normalizedNegLog n (optimalEqualPriorTensorPowerError rho sigma (n + 1)) := rfl

/-- Direct finite-copy exponent lift from Audenaert's upper bound.

The exponent index `n` uses exactly `n + 1` tensor copies through
`optimalEqualPriorTensorPowerErrorExponent`, so the finite-copy theorem is
instantiated at copy number `n + 1`. -/
theorem petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    rho.petzChernoffExponent sigma s ≤
      optimalEqualPriorTensorPowerErrorExponent rho sigma n := by
  have hfinite :
      optimalEqualPriorTensorPowerError rho sigma (n + 1) ≤
        ((((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ (n + 1) : ℝ≥0) :
          ℝ≥0∞)) :=
    optimalEqualPriorTensorPowerError_le_half_petzRenyiCoefficient_pow
      rho sigma hs0 hs1 (n + 1)
  have hnormalized :
      normalizedNegLog n
          ((((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ (n + 1) :
            ℝ≥0) : ℝ≥0∞)) ≤
        optimalEqualPriorTensorPowerErrorExponent rho sigma n := by
    simpa [optimalEqualPriorTensorPowerErrorExponent] using
      normalizedNegLog_antitone n hfinite
  exact
    (petzChernoffExponent_le_normalizedNegLog_half_petzRenyiCoefficient_pow
      rho sigma s n).trans hnormalized

/-- The direct QCB upper-side exponent hypothesis supplied unconditionally by the
finite-copy Audenaert bound.

This is the direct-side hypothesis consumed by the liminf bridge. -/
theorem eventually_petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
    (rho sigma : State a) :
    ∀ s : Set.Icc (0 : ℝ) 1,
      ∀ᶠ n in atTop,
        rho.petzChernoffExponent sigma s.1 ≤
          optimalEqualPriorTensorPowerErrorExponent rho sigma n := by
  intro s
  exact Filter.Eventually.of_forall fun n =>
    petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
      rho sigma s.2.1 s.2.2 n

/-- Nussbaum--Szkola alphabet size used by the source-backed quantum-to-classical
Chernoff converse route.

For spectral decompositions of two states on a `d`-dimensional space, the
classical comparison distributions are indexed by eigenvector pairs, so the
finite alphabet has `d * d` letters
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
def nussbaumSzkolaAlphabetCard {a : Type u} [Fintype a] : Nat :=
  Fintype.card a * Fintype.card a

/-- The method-of-types polynomial prefactor `(n+1)^(-m)`.

Here `m` is the Nussbaum--Szkola alphabet size.  This records the exact
finite-copy polynomial loss required by the classical Chernoff converse
[Gour2024Resources, BookQRT.tex:15414-15469]. -/
def methodOfTypesPolynomialPrefactor {a : Type u} [Fintype a] (n : Nat) : ℝ≥0∞ :=
  (((n + 1 : Nat) : ℝ≥0∞) ^ nussbaumSzkolaAlphabetCard (a := a))⁻¹

/-- The normalized logarithmic penalty contributed by the method-of-types prefactor.

For the exponent sequence indexed as `n ↦ error (n + 1)`, the source prefactor
`(N + 1)^(-m)` is evaluated at `N = n + 1`, giving the vanishing term
`m * log(n + 2) / (n + 1)`.  The finite alphabet size is the
Nussbaum--Szkola alphabet cardinality `m`
[Gour2024Resources, BookQRT.tex:15414-15469]. -/
def methodOfTypesPolynomialPenalty {a : Type u} [Fintype a] (n : Nat) : EReal :=
  (((nussbaumSzkolaAlphabetCard (a := a) : ℝ) *
      Real.log (((n + 2 : Nat) : ℝ))) / (((n + 1 : Nat) : ℝ)) : ℝ)

/-- Generic finite-alphabet method-of-types prefactor `(n+1)^(-|α|)`.

This is the source prefactor from the classical method-of-types proof before
specializing the alphabet to the Nussbaum--Szkola pair alphabet
[Gour2024Resources, BookQRT.tex:15414-15469]. -/
def finiteAlphabetMethodOfTypesPolynomialPrefactor
    (α : Type u) [Fintype α] (n : Nat) : ℝ≥0∞ :=
  ((((n + 1 : Nat) : ℝ≥0∞) ^ Fintype.card α)⁻¹)

/-- Real form of the generic finite-alphabet method-of-types prefactor. -/
theorem finiteAlphabetMethodOfTypesPolynomialPrefactor_toReal
    (α : Type u) [Fintype α] (n : Nat) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α n).toReal =
      ((((n + 1 : Nat) : ℝ) ^ Fintype.card α)⁻¹) := by
  have hbase :
      (((n + 1 : Nat) : ℝ≥0∞).toReal) =
        ((((n + 1 : Nat) : ℝ≥0) : ℝ)) := by
    rw [show ((n + 1 : Nat) : ℝ≥0∞) = (n : ℝ≥0∞) + 1 by norm_num]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top]
    simp [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
  unfold finiteAlphabetMethodOfTypesPolynomialPrefactor
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, hbase]
  simp

/-- A positive lower bound of the form `c * exp (-R*d) ≤ E` converts to the
normalized negative-log upper bound with prefactor penalty. -/
theorem neg_log_div_le_of_mul_exp_neg_le
    {E c d R : ℝ}
    (hR : 0 < R)
    (hc : 0 < c)
    (hE : 0 < E)
    (hbound : c * Real.exp (-R * d) ≤ E) :
    -Real.log E / R ≤ d + (-Real.log c) / R := by
  have hce : 0 < c * Real.exp (-R * d) :=
    mul_pos hc (Real.exp_pos _)
  have hlogle : Real.log (c * Real.exp (-R * d)) ≤ Real.log E :=
    (Real.log_le_log_iff hce hE).mpr hbound
  have hlogeq :
      Real.log (c * Real.exp (-R * d)) =
        Real.log c + (-R * d) := by
    rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlinear : Real.log c + (-R * d) ≤ Real.log E := by
    rw [hlogeq] at hlogle
    exact hlogle
  have hnum : -Real.log E ≤ R * d + (-Real.log c) := by
    linarith
  rw [div_le_iff₀ hR]
  calc
    -Real.log E ≤ R * d + (-Real.log c) := hnum
    _ = (d + (-Real.log c) / R) * R := by
      field_simp [hR.ne']

/-- The exact natural-log penalty produced by the equal-prior factor and the
finite-alphabet method-of-types prefactor. -/
theorem equalPriorMethodOfTypesPrefactor_log_penalty
    (α : Type u) [Fintype α] {N : Nat} (hN : 0 < N) :
    (-Real.log
        ((1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal)) / (N : ℝ) =
      (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
        Real.log 2 / (N : ℝ) := by
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have hNp1_pos : 0 < (((N + 1 : Nat) : ℝ)) := by
    positivity
  have hpow_pos :
      0 < (((N + 1 : Nat) : ℝ) ^ Fintype.card α) :=
    pow_pos hNp1_pos _
  have hinv_pos :
      0 < ((((N + 1 : Nat) : ℝ) ^ Fintype.card α)⁻¹) :=
    inv_pos.mpr hpow_pos
  rw [finiteAlphabetMethodOfTypesPolynomialPrefactor_toReal]
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    rw [Real.log_inv]
  have hlog_inv :
      Real.log ((((N + 1 : Nat) : ℝ) ^ Fintype.card α)⁻¹) =
        -((Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ))) := by
    rw [Real.log_inv]
    rw [Real.log_pow]
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) hinv_pos.ne',
    hlog_half, hlog_inv]
  field_simp [hN_ne]
  ring

/-- Empirical binomial mass at the observed count `k`.

This is the binomial probability of observing `k` successes in `N` trials under
the empirical success probability `k / N`. -/
def empiricalBinomialMass (N k : Nat) : ℝ≥0 :=
  (Nat.choose N k : ℝ≥0) *
    (((k : ℝ≥0) / (N : ℝ≥0)) ^ k) *
    ((((N - k : Nat) : ℝ≥0) / (N : ℝ≥0)) ^ (N - k))

/-- Binomial mass at an arbitrary count `j`, using the empirical parameter
selected by the count `k`. -/
def binomialMassAt (N k j : Nat) : ℝ≥0 :=
  (Nat.choose N j : ℝ≥0) *
    (((k : ℝ≥0) / (N : ℝ≥0)) ^ j) *
    ((((N - k : Nat) : ℝ≥0) / (N : ℝ≥0)) ^ (N - j))

private theorem binomialMassAt_succ_cross {N k j : Nat} (hk : k ≤ N) (hj : j < N) :
    binomialMassAt N k (j + 1) *
        (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) =
      binomialMassAt N k j *
        (((N - j : Nat) * k : Nat) : ℝ≥0) := by
  unfold binomialMassAt
  have hchoose := Nat.choose_succ_right_eq N j
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le j) hj))
  have hsub : N - j = N - (j + 1) + 1 := by omega
  have hchooseR :
      ((Nat.choose N (j + 1) : ℝ) * ((j + 1 : Nat) : ℝ)) =
        ((Nat.choose N j : ℝ) * ((N - j : Nat) : ℝ)) := by
    exact_mod_cast hchoose
  have hchooseR' :
      ((Nat.choose N (j + 1) : ℝ) * ((j : ℝ) + 1)) =
        ((Nat.choose N j : ℝ) * ((N : ℝ) - (j : ℝ))) := by
    simpa [Nat.cast_add, Nat.cast_one, Nat.cast_sub hj.le] using hchooseR
  have hchooseRnn :
      ((Nat.choose N (j + 1) : ℝ) * ((j : ℝ) + 1)) =
        ((Nat.choose N j : ℝ) *
          ((((N : ℝ≥0) - (j : ℝ≥0)) : ℝ≥0) : ℝ)) := by
    have hjnn : (j : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hj.le
    simpa [NNReal.coe_sub hjnn] using hchooseR'
  have hfrac :
      ((k : ℝ) / (N : ℝ) *
          ((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ)) =
        ((((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) * (k : ℝ)) := by
    have hknn : (k : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hk
    rw [NNReal.coe_sub hknn]
    field_simp [hN0]
  apply NNReal.eq
  norm_num
  rw [pow_succ']
  rw [hsub, pow_succ']
  rw [show
      ((Nat.choose N (j + 1) : ℝ) *
          ((k : ℝ) / (N : ℝ) * ((k : ℝ) / (N : ℝ)) ^ j) *
          (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1)) *
          (((j : ℝ) + 1) *
            (((N : ℝ≥0) - (k : ℝ≥0) : ℝ≥0) : ℝ))) =
        (((Nat.choose N (j + 1) : ℝ) * ((j : ℝ) + 1)) *
          ((k : ℝ) / (N : ℝ)) ^ j *
          (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1)) *
          (((k : ℝ) / (N : ℝ)) *
            (((N : ℝ≥0) - (k : ℝ≥0) : ℝ≥0) : ℝ))) by ring]
  rw [show
      ((Nat.choose N j : ℝ) * ((k : ℝ) / (N : ℝ)) ^ j *
          ((((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) *
            (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1))) *
          (((((N : ℝ≥0) - (j : ℝ≥0)) : ℝ≥0) : ℝ) * (k : ℝ))) =
        (((Nat.choose N j : ℝ) *
            ((((N : ℝ≥0) - (j : ℝ≥0)) : ℝ≥0) : ℝ)) *
          ((k : ℝ) / (N : ℝ)) ^ j *
          (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1)) *
          ((((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) * (k : ℝ))) by ring]
  rw [hchooseRnn, hfrac]

private theorem binomial_left_cross_le_right {N k j : Nat} (hjk : j < k) :
    (j + 1) * (N - k) ≤ (N - j) * k := by
  have hjk_succ : j + 1 ≤ k := Nat.succ_le_of_lt hjk
  have hNk_le_Nj : N - k ≤ N - j := Nat.sub_le_sub_left (Nat.le_of_lt hjk) N
  calc
    (j + 1) * (N - k) ≤ k * (N - k) := Nat.mul_le_mul_right _ hjk_succ
    _ = (N - k) * k := Nat.mul_comm _ _
    _ ≤ (N - j) * k := Nat.mul_le_mul_right _ hNk_le_Nj

private theorem binomial_right_cross_le_left {N k j : Nat} (hkj : k ≤ j) :
    (N - j) * k ≤ (j + 1) * (N - k) := by
  have hkj_succ : k ≤ j + 1 := hkj.trans (Nat.le_succ j)
  have hNj_le_Nk : N - j ≤ N - k := Nat.sub_le_sub_left hkj N
  calc
    (N - j) * k ≤ (N - j) * (j + 1) := Nat.mul_le_mul_left _ hkj_succ
    _ = (j + 1) * (N - j) := Nat.mul_comm _ _
    _ ≤ (j + 1) * (N - k) := Nat.mul_le_mul_left _ hNj_le_Nk

private theorem binomialMassAt_le_succ {N k j : Nat}
    (hk : k ≤ N) (hj : j < N) (hjk : j < k) :
    binomialMassAt N k j ≤ binomialMassAt N k (j + 1) := by
  have hcross := binomialMassAt_succ_cross (N := N) (k := k) (j := j) hk hj
  have hc_le_d :
      (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) ≤
        (((N - j : Nat) * k : Nat) : ℝ≥0) := by
    exact_mod_cast binomial_left_cross_le_right (N := N) (k := k) (j := j) hjk
  have hd_pos : 0 < ((((N - j : Nat) * k : Nat) : ℝ≥0)) := by
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hj) (Nat.lt_of_le_of_lt (Nat.zero_le j) hjk)
  have hmul :
      binomialMassAt N k j * ((((N - j : Nat) * k : Nat) : ℝ≥0)) ≤
        binomialMassAt N k (j + 1) * ((((N - j : Nat) * k : Nat) : ℝ≥0)) := by
    calc
      binomialMassAt N k j * ((((N - j : Nat) * k : Nat) : ℝ≥0))
          = binomialMassAt N k (j + 1) *
              (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) := hcross.symm
      _ ≤ binomialMassAt N k (j + 1) *
            ((((N - j : Nat) * k : Nat) : ℝ≥0)) :=
          mul_le_mul_of_nonneg_left hc_le_d (by positivity)
  exact (mul_le_mul_iff_right₀ hd_pos).mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)

private theorem binomialMassAt_succ_le {N k j : Nat}
    (hk : k ≤ N) (hj : j < N) (hkj : k ≤ j) :
    binomialMassAt N k (j + 1) ≤ binomialMassAt N k j := by
  have hcross := binomialMassAt_succ_cross (N := N) (k := k) (j := j) hk hj
  have hd_le_c :
      (((N - j : Nat) * k : Nat) : ℝ≥0) ≤
        (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) := by
    exact_mod_cast binomial_right_cross_le_left (N := N) (k := k) (j := j) hkj
  have hc_pos : 0 < ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) := by
    have hk_lt_N : k < N := hkj.trans_lt hj
    exact_mod_cast Nat.mul_pos (Nat.succ_pos j) (Nat.sub_pos_of_lt hk_lt_N)
  have hmul :
      binomialMassAt N k (j + 1) *
          ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) ≤
        binomialMassAt N k j *
          ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) := by
    calc
      binomialMassAt N k (j + 1) *
          ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0))
          = binomialMassAt N k j *
              (((N - j : Nat) * k : Nat) : ℝ≥0) := hcross
      _ ≤ binomialMassAt N k j *
            ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) :=
          mul_le_mul_of_nonneg_left hd_le_c (by positivity)
  exact (mul_le_mul_iff_right₀ hc_pos).mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)

/-- The empirical binomial mass is a mode of the binomial distribution with
parameter `k / N`. -/
theorem binomialMassAt_le_empiricalBinomialMass {N k j : Nat} (hk : k ≤ N) (hj : j ≤ N) :
    binomialMassAt N k j ≤ empiricalBinomialMass N k := by
  have hmode : binomialMassAt N k k = empiricalBinomialMass N k := by
    simp [binomialMassAt, empiricalBinomialMass]
  by_cases hjk : j ≤ k
  · have hchain : binomialMassAt N k j ≤ binomialMassAt N k k := by
      have haux :
          ∀ n (hjn : j ≤ n), n ≤ k -> binomialMassAt N k j ≤ binomialMassAt N k n := by
        intro n hjn
        induction n, hjn using Nat.le_induction with
        | base =>
            intro _
            rfl
        | succ n _ ih =>
            intro hn_succ_le
            have hn_le_k : n ≤ k := Nat.le_of_succ_le hn_succ_le
            have hn_lt_k : n < k := Nat.lt_of_succ_le hn_succ_le
            have hn_lt_N : n < N := hn_lt_k.trans_le hk
            exact (ih hn_le_k).trans (binomialMassAt_le_succ hk hn_lt_N hn_lt_k)
      exact haux k hjk le_rfl
    simpa [hmode] using hchain
  · have hkj : k ≤ j := Nat.le_of_not_ge hjk
    have hchain : binomialMassAt N k j ≤ binomialMassAt N k k := by
      have haux :
          ∀ n (hkn : k ≤ n), n ≤ N -> binomialMassAt N k n ≤ binomialMassAt N k k := by
        intro n hkn
        induction n, hkn using Nat.le_induction with
        | base =>
            intro _
            rfl
        | succ n hkn ih =>
            intro hn_succ_le_N
            have hn_lt_N : n < N := Nat.lt_of_succ_le hn_succ_le_N
            have hn_le_N : n ≤ N := hn_lt_N.le
            exact (binomialMassAt_succ_le hk hn_lt_N hkn).trans (ih hn_le_N)
      exact haux j hkj hj
    simpa [hmode] using hchain

private theorem binomialMassAt_sum_eq_one {N k : Nat} (hN : 0 < N) (hk : k ≤ N) :
    (∑ j : Fin (N + 1), binomialMassAt N k j) = 1 := by
  have hsum :
      (((k : ℝ≥0) / (N : ℝ≥0)) +
        (((N - k : Nat) : ℝ≥0) / (N : ℝ≥0))) = 1 := by
    rw [← add_div]
    have hsum : (k : ℝ≥0) + ((N - k : Nat) : ℝ≥0) = (N : ℝ≥0) := by
      exact_mod_cast (Nat.add_sub_of_le hk)
    rw [hsum]
    exact div_self (by exact_mod_cast hN.ne')
  calc
    (∑ j : Fin (N + 1), binomialMassAt N k j)
        = (((k : ℝ≥0) / (N : ℝ≥0)) +
            (((N - k : Nat) : ℝ≥0) / (N : ℝ≥0))) ^ N := by
          rw [show (((k : ℝ≥0) / (N : ℝ≥0)) +
              (((N - k : Nat) : ℝ≥0) / (N : ℝ≥0))) ^ N =
              ∑ m ∈ Finset.range (N + 1),
                (((k : ℝ≥0) / (N : ℝ≥0)) ^ m *
                  ((((N - k : Nat) : ℝ≥0) / (N : ℝ≥0)) ^ (N - m)) *
                  (Nat.choose N m : ℝ≥0)) by
            rw [add_pow]]
          rw [Finset.sum_fin_eq_sum_range]
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.mem_range] at hj
          simp [binomialMassAt, hj]
          ring
    _ = 1 := by rw [hsum]; simp

/-- Source-level empirical binomial mode lower bound:
one of the `N+1` binomial masses is at least the average mass. -/
theorem inv_succ_le_empiricalBinomialMass {N k : Nat}
    (hN : 0 < N) (hk : k ≤ N) :
    ((N + 1 : ℝ≥0)⁻¹) ≤ empiricalBinomialMass N k := by
  have hsum := binomialMassAt_sum_eq_one (N := N) (k := k) hN hk
  have hsum_le :
      (∑ j : Fin (N + 1), binomialMassAt N k j) ≤
        ∑ _j : Fin (N + 1), empiricalBinomialMass N k := by
    refine Finset.sum_le_sum ?_
    intro j _
    exact binomialMassAt_le_empiricalBinomialMass
      (N := N) (k := k) (j := j) hk (Nat.le_of_lt_succ j.2)
  have hone_le :
      (1 : ℝ≥0) ≤ (N + 1 : ℝ≥0) * empiricalBinomialMass N k := by
    calc
      (1 : ℝ≥0) = ∑ j : Fin (N + 1), binomialMassAt N k j := hsum.symm
      _ ≤ ∑ _j : Fin (N + 1), empiricalBinomialMass N k := hsum_le
      _ = (N + 1 : ℝ≥0) * empiricalBinomialMass N k := by
        simp [Finset.card_univ]
  have hpos : 0 < (N + 1 : ℝ≥0) := by exact_mod_cast Nat.succ_pos N
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    (N + 1 : ℝ≥0) * ((N + 1 : ℝ≥0)⁻¹)
        = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    _ ≤ (N + 1 : ℝ≥0) * empiricalBinomialMass N k := hone_le

/-- Empirical multinomial mass at the profile itself.

This is the multinomial probability of a type/profile under its empirical
distribution. -/
def empiricalMultinomialMass {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (profile : TensorPowerProfile α N) : ℝ≥0 :=
  (Nat.multinomial Finset.univ profile.1 : ℝ≥0) *
    ∏ z : α, (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z)

private def empiricalMultinomialMassFin {m N : Nat} (f : Fin m → Nat) : ℝ≥0 :=
  (Nat.multinomial Finset.univ f : ℝ≥0) *
    ∏ z : Fin m, (((f z : ℝ≥0) / (N : ℝ≥0)) ^ f z)

private def finTailCounts {m : Nat} (f : Fin (m + 1) → Nat) : Fin m → Nat :=
  fun i => f i.castSucc

private theorem fin_multinomial_last_factor {m : Nat} (f : Fin (m + 1) → Nat) :
    Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) f =
      Nat.choose (∑ i : Fin (m + 1), f i) (f (Fin.last m)) *
        Nat.multinomial (Finset.univ : Finset (Fin m)) (finTailCounts f) := by
  classical
  let s : Finset (Fin (m + 1)) := (Finset.univ : Finset (Fin m)).map Fin.castSuccEmb
  have hlast_not : Fin.last m ∉ s := by
    simp [s]
  have huniv : (Finset.univ : Finset (Fin (m + 1))) = insert (Fin.last m) s := by
    ext i
    constructor
    · intro _
      by_cases hi : i = Fin.last m
      · simp [hi]
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        simp [s]
    · intro _
      simp
  have hsum_s :
      ∑ x ∈ s, f x = ∑ i : Fin m, finTailCounts f i := by
    simp [s, finTailCounts]
  have hchoose :
      f (Fin.last m) + ∑ x ∈ s, f x = ∑ i : Fin (m + 1), f i := by
    rw [hsum_s, Fin.sum_univ_castSucc]
    simp [finTailCounts, add_comm]
  have hmult_s :
      Nat.multinomial s f =
        Nat.multinomial (Finset.univ : Finset (Fin m)) (finTailCounts f) := by
    unfold Nat.multinomial
    simp [s, finTailCounts]
  rw [huniv, Nat.multinomial_insert hlast_not]
  rw [hmult_s]
  congr 1
  rw [Finset.sum_insert hlast_not]

private theorem fin_empirical_tail_product_factor {m N : Nat} (f : Fin (m + 1) → Nat)
    (hN : 0 < N)
    (htail_sum : ∑ i : Fin m, finTailCounts f i = N - f (Fin.last m)) :
    (∏ i : Fin m, (((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) ^ f i.castSucc)) =
      ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
          (N - f (Fin.last m))) *
        ∏ i : Fin m,
          ((((f i.castSucc : ℝ≥0) /
              ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc)) := by
  classical
  by_cases htail0 : N - f (Fin.last m) = 0
  · have hsum0 : ∑ i : Fin m, finTailCounts f i = 0 := by
      simpa [htail0] using htail_sum
    have hcounts0_fun : finTailCounts f = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun i => Nat.zero_le (finTailCounts f i))).mp hsum0
    have hcounts0 : ∀ i : Fin m, finTailCounts f i = 0 := by
      intro i
      exact congrFun hcounts0_fun i
    have hleft :
        (∏ i : Fin m, (((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) ^ f i.castSucc)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hi : f i.castSucc = 0 := by simpa [finTailCounts] using hcounts0 i
      simp [hi]
    have hright :
        ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
            (N - f (Fin.last m))) *
          ∏ i : Fin m,
            ((((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc)) = 1 := by
      rw [htail0]
      simp only [pow_zero, one_mul]
      apply Finset.prod_eq_one
      intro i _
      have hi : f i.castSucc = 0 := by simpa [finTailCounts] using hcounts0 i
      simp [hi]
    exact hleft.trans hright.symm
  · have htail_pos : 0 < N - f (Fin.last m) := Nat.pos_of_ne_zero htail0
    have hterm : ∀ i : Fin m,
        ((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) =
          (((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) *
            ((f i.castSucc : ℝ≥0) /
              ((N - f (Fin.last m) : Nat) : ℝ≥0)) := by
      intro i
      apply NNReal.eq
      have hN_real : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      have htail_real : ((N - f (Fin.last m) : Nat) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt htail_pos
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
      field_simp [hN_real, htail_real]
    calc
      (∏ i : Fin m, (((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) ^ f i.castSucc)) =
          ∏ i : Fin m,
            ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) *
              ((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0))) ^ f i.castSucc := by
        simp [hterm]
      _ =
          ∏ i : Fin m,
            (((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
                f i.castSucc) *
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc)) := by
        simp [mul_pow]
      _ =
          (∏ i : Fin m,
            ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
              f i.castSucc)) *
            ∏ i : Fin m,
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc) := by
        rw [Finset.prod_mul_distrib]
      _ =
          ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
              (∑ i : Fin m, f i.castSucc)) *
            ∏ i : Fin m,
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ =
          ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
              (N - f (Fin.last m))) *
            ∏ i : Fin m,
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc) := by
        rw [show (∑ i : Fin m, f i.castSucc) = N - f (Fin.last m) by
          simpa [finTailCounts] using htail_sum]

private theorem empiricalMultinomialMassFin_last_factor {m N : Nat} (f : Fin (m + 1) → Nat)
    (hN : 0 < N)
    (hsum : ∑ i : Fin (m + 1), f i = N) :
    empiricalMultinomialMassFin (N := N) f =
      empiricalBinomialMass N (f (Fin.last m)) *
        empiricalMultinomialMassFin (N := N - f (Fin.last m)) (finTailCounts f) := by
  classical
  have htail_sum :
      ∑ i : Fin m, finTailCounts f i = N - f (Fin.last m) := by
    have hsplit :
        (∑ i : Fin (m + 1), f i) =
          (∑ i : Fin m, finTailCounts f i) + f (Fin.last m) := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hsum] at hsplit
    omega
  unfold empiricalMultinomialMassFin empiricalBinomialMass
  rw [fin_multinomial_last_factor f, hsum]
  rw [Fin.prod_univ_castSucc]
  simp only [finTailCounts]
  rw [fin_empirical_tail_product_factor (N := N) f hN htail_sum]
  simp only [Nat.cast_mul]
  ring_nf
  rw [show
      (∏ x : Fin m,
          (↑(f x.castSucc) : ℝ≥0) ^ f x.castSucc *
            (↑(N - f (Fin.last m)) : ℝ≥0)⁻¹ ^ f x.castSucc) =
        ∏ x : Fin m,
          (↑(N - f (Fin.last m)) : ℝ≥0)⁻¹ ^ f x.castSucc *
            (↑(f x.castSucc) : ℝ≥0) ^ f x.castSucc by
    apply Finset.prod_congr rfl
    intro x _
    ring]
  ring_nf

private theorem inv_pow_succ_le_inv_mul_inv_pow {N k m : Nat} :
    (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ ≤
      (((N + 1 : Nat) : ℝ≥0))⁻¹ *
        ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) := by
  have hbase :
      (((N - k + 1 : Nat) : ℝ≥0)) ≤ (((N + 1 : Nat) : ℝ≥0)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.sub_le N k)
  have hpow :
      (((N - k + 1 : Nat) : ℝ≥0) ^ m) ≤
        (((N + 1 : Nat) : ℝ≥0) ^ m) :=
    pow_le_pow_left₀ (by positivity) hbase m
  have hden :
      (((N + 1 : Nat) : ℝ≥0) * (((N - k + 1 : Nat) : ℝ≥0) ^ m)) ≤
        (((N + 1 : Nat) : ℝ≥0) * (((N + 1 : Nat) : ℝ≥0) ^ m)) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hleft_pos :
      0 < (((N + 1 : Nat) : ℝ≥0) * (((N + 1 : Nat) : ℝ≥0) ^ m)) := by
    positivity
  have hright_pos :
      0 < (((N + 1 : Nat) : ℝ≥0) * (((N - k + 1 : Nat) : ℝ≥0) ^ m)) := by
    positivity
  calc
    (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ =
        ((((N + 1 : Nat) : ℝ≥0) * (((N + 1 : Nat) : ℝ≥0) ^ m))⁻¹) := by
      rw [pow_succ']
    _ ≤ ((((N + 1 : Nat) : ℝ≥0) *
          (((N - k + 1 : Nat) : ℝ≥0) ^ m))⁻¹) :=
      (inv_le_inv₀ hleft_pos hright_pos).mpr hden
    _ = (((N + 1 : Nat) : ℝ≥0))⁻¹ *
        ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) := by
      rw [_root_.mul_inv_rev, mul_comm]

private theorem inv_pow_card_le_empiricalMultinomialMassFin {m N : Nat}
    (hN : 0 < N) (f : Fin m → Nat)
    (hsum : ∑ i : Fin m, f i = N) :
    (((N + 1 : Nat) : ℝ≥0) ^ m)⁻¹ ≤
      empiricalMultinomialMassFin (N := N) f := by
  induction m generalizing N with
  | zero =>
      simp [empiricalMultinomialMassFin]
  | succ m ih =>
      let k := f (Fin.last m)
      have hk : k ≤ N := by
        rw [← hsum, Fin.sum_univ_castSucc]
        exact Nat.le_add_left _ _
      have htail_sum :
          ∑ i : Fin m, finTailCounts f i = N - k := by
        have hsplit :
            (∑ i : Fin (m + 1), f i) =
              (∑ i : Fin m, finTailCounts f i) + k := by
          rw [Fin.sum_univ_castSucc]
          rfl
        rw [hsum] at hsplit
        omega
      rw [empiricalMultinomialMassFin_last_factor (N := N) f hN hsum]
      have hbin : (((N + 1 : Nat) : ℝ≥0))⁻¹ ≤ empiricalBinomialMass N k :=
        by simpa [Nat.cast_add, Nat.cast_one] using
          inv_succ_le_empiricalBinomialMass hN hk
      by_cases htail0 : N - k = 0
      · have hsum0 : ∑ i : Fin m, finTailCounts f i = 0 := by
          simpa [htail0] using htail_sum
        have hcounts0_fun : finTailCounts f = 0 :=
          (Fintype.sum_eq_zero_iff_of_nonneg
            (fun i => Nat.zero_le (finTailCounts f i))).mp hsum0
        have hcounts0 : ∀ i : Fin m, finTailCounts f i = 0 := by
          intro i
          exact congrFun hcounts0_fun i
        have htail_mass :
            empiricalMultinomialMassFin (N := N - k) (finTailCounts f) = 1 := by
          unfold empiricalMultinomialMassFin
          have hmulti :
              Nat.multinomial (Finset.univ : Finset (Fin m)) (finTailCounts f) = 1 := by
            unfold Nat.multinomial
            simp [hcounts0]
          rw [hmulti]
          simp [htail0, hcounts0]
        have hpref :
            (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ ≤
              (((N + 1 : Nat) : ℝ≥0))⁻¹ := by
          simpa [htail0] using
            (inv_pow_succ_le_inv_mul_inv_pow (N := N) (k := k) (m := m))
        exact hpref.trans (by simpa [htail_mass] using hbin)
      · have htail_pos : 0 < N - k := Nat.pos_of_ne_zero htail0
        have htail :
            ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) ≤
              empiricalMultinomialMassFin (N := N - k) (finTailCounts f) :=
          ih htail_pos (finTailCounts f) htail_sum
        have hpref :
            (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ ≤
              (((N + 1 : Nat) : ℝ≥0))⁻¹ *
                ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) :=
          inv_pow_succ_le_inv_mul_inv_pow (N := N) (k := k) (m := m)
        have hprod :
            (((N + 1 : Nat) : ℝ≥0))⁻¹ *
                ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) ≤
              empiricalBinomialMass N k *
                empiricalMultinomialMassFin (N := N - k) (finTailCounts f) :=
          mul_le_mul' hbin htail
        exact hpref.trans hprod

/-- Source-level empirical multinomial mass lower bound:
one of the finitely many type classes has mass at least the average
`(N+1)^(-|α|)`. -/
theorem inv_pow_card_le_empiricalMultinomialMass {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (hN : 0 < N) (profile : TensorPowerProfile α N) :
    ((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹) ≤
      empiricalMultinomialMass (α := α) profile := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let f : Fin (Fintype.card α) → Nat := fun i => profile.1 (e.symm i)
  have hprofile_sum : ∑ z : α, profile.1 z = N :=
    tensorPowerTypeProfile_sum_of_mem_profiles (a := α) N profile.2
  have hsum : ∑ i : Fin (Fintype.card α), f i = N := by
    have hreindex :
        (∑ i : Fin (Fintype.card α), profile.1 (e.symm i)) =
          ∑ z : α, profile.1 z :=
      Equiv.sum_comp e.symm profile.1
    simpa [f] using hreindex.trans hprofile_sum
  have hfin :=
    inv_pow_card_le_empiricalMultinomialMassFin
      (N := N) (m := Fintype.card α) hN f hsum
  have hmulti :
      Nat.multinomial (Finset.univ : Finset α) profile.1 =
        Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card α))) f := by
    have hsum_reindex :
        (∑ i : Fin (Fintype.card α), f i) = ∑ z : α, profile.1 z := by
      simpa [f] using Equiv.sum_comp e.symm profile.1
    have hprod_reindex :
        (∏ i : Fin (Fintype.card α), Nat.factorial (f i)) =
          ∏ z : α, Nat.factorial (profile.1 z) := by
      simpa [f] using
        Equiv.prod_comp e.symm (fun z : α => Nat.factorial (profile.1 z))
    unfold Nat.multinomial
    simp [hsum_reindex, hprod_reindex]
  have hprod :
      (∏ z : α, (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z)) =
        ∏ i : Fin (Fintype.card α), (((f i : ℝ≥0) / (N : ℝ≥0)) ^ f i) := by
    have hreindex :
        (∏ i : Fin (Fintype.card α),
            (((profile.1 (e.symm i) : ℝ≥0) / (N : ℝ≥0)) ^
              profile.1 (e.symm i))) =
          ∏ z : α, (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z) :=
      Equiv.prod_comp e.symm
        (fun z : α => (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z))
    simpa [f] using hreindex.symm
  simpa [empiricalMultinomialMass, empiricalMultinomialMassFin, hmulti, hprod,
    Nat.cast_add, Nat.cast_one] using hfin

theorem empiricalProfileProduct_toReal_eq_exp_sum_log
    {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (hN : 0 < N) (profile : TensorPowerProfile α N) :
    ((∏ z : α,
      (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ (profile.1 z)) : ℝ) =
        Real.exp
          (∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) := by
  classical
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let nnTerm : α → ℝ≥0 := fun z =>
    (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ (profile.1 z))
  let realTerm : α → ℝ := fun z =>
    (((profile.1 z : ℝ) / (N : ℝ)) ^ (profile.1 z))
  let expTerm : α → ℝ := fun z =>
    Real.exp
      ((profile.1 z : ℝ) *
        Real.log ((profile.1 z : ℝ) / (N : ℝ)))
  have hcoe :
      ((Finset.univ.prod nnTerm : ℝ≥0) : ℝ) = Finset.univ.prod realTerm := by
    simp [nnTerm, realTerm, NNReal.coe_div]
  have hterms :
      Finset.univ.prod realTerm = Finset.univ.prod expTerm := by
    apply Finset.prod_congr rfl
    intro z _
    by_cases hz : profile.1 z = 0
    · simp [realTerm, expTerm, hz]
    · have hzreal : 0 < (profile.1 z : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      have hx : 0 < (profile.1 z : ℝ) / (N : ℝ) := div_pos hzreal hNreal
      calc
        realTerm z =
            ((profile.1 z : ℝ) / (N : ℝ)) ^ (profile.1 z) := by
          rfl
        _ =
            (Real.exp (Real.log ((profile.1 z : ℝ) / (N : ℝ)))) ^ (profile.1 z) := by
          rw [Real.exp_log hx]
        _ =
            expTerm z := by
          unfold expTerm
          rw [← Real.exp_nat_mul]
  have hexp :
      Finset.univ.prod expTerm =
        Real.exp
          (∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ))) := by
    unfold expTerm
    rw [Real.exp_sum]
  simpa [nnTerm] using hcoe.trans (hterms.trans hexp)

/-- Source-backed type-class cardinality lower bound with the exact
`(N+1)^(-|α|)` polynomial prefactor. -/
theorem tensorPowerProfileClass_card_source_lower_bound
    {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (hN : 0 < N) (profile : TensorPowerProfile α N) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) ≤
      ((tensorPowerProfileClass (a := α) profile).card : ℝ) := by
  classical
  let S : ℝ :=
    ∑ z : α,
      (profile.1 z : ℝ) *
        Real.log ((profile.1 z : ℝ) / (N : ℝ))
  have hprob := inv_pow_card_le_empiricalMultinomialMass (α := α) hN profile
  have hprob_real0 :
      (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) ≤
        (((Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ≥0) *
          ∏ z : α,
            (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z) : ℝ≥0) : ℝ) := by
    exact_mod_cast (by
      simpa [empiricalMultinomialMass] using hprob)
  have hprodlog := empiricalProfileProduct_toReal_eq_exp_sum_log (α := α) hN profile
  have hprodlogR :
      (∏ z : α, (((profile.1 z : ℝ) / (N : ℝ)) ^ profile.1 z)) =
        Real.exp S := by
    simpa [S, NNReal.coe_div] using hprodlog
  have hprob_real :
      (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) ≤
        (Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) * Real.exp S := by
    simpa [S, NNReal.coe_mul, hprodlogR] using hprob_real0
  have hpref :
      (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal =
        (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) := by
    have hbase :
        (((N + 1 : Nat) : ℝ≥0∞).toReal) =
          ((((N + 1 : Nat) : ℝ≥0) : ℝ)) := by
      rw [show ((N + 1 : Nat) : ℝ≥0∞) = (N : ℝ≥0∞) + 1 by norm_num]
      rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
      simp [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
    unfold finiteAlphabetMethodOfTypesPolynomialPrefactor
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow, hbase]
    simp
  have hcard :
      ((tensorPowerProfileClass (a := α) profile).card : ℝ) =
        (Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) := by
    exact_mod_cast tensorPowerProfileClass_card_eq_multinomial (a := α) profile
  have hmul := mul_le_mul_of_nonneg_right hprob_real (Real.exp_pos (-S)).le
  calc
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) =
        (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) *
          Real.exp (-S) := by
      simp [hpref, S]
    _ ≤ ((Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) *
          Real.exp S) * Real.exp (-S) := hmul
    _ = (Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) := by
      rw [mul_assoc, ← Real.exp_add]
      simp [S]
    _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ) := hcard.symm

/-- Generic finite-alphabet normalized logarithmic method-of-types penalty.

For exponent index `n`, the source copy number is `N = n + 1`, so the source
factor `(N+1)^(-m)` contributes `m * log(n+2) / (n+1)` in natural-log
normalization. -/
def finiteAlphabetMethodOfTypesPolynomialPenalty
    (α : Type u) [Fintype α] (n : Nat) : EReal :=
  (((Fintype.card α : ℝ) * Real.log (((n + 2 : Nat) : ℝ))) /
    (((n + 1 : Nat) : ℝ)) : ℝ)

/-- Extra finite-copy logarithmic penalty introduced when the source error
probability is converted to the repository's equal-prior average convention. -/
def equalPriorAverageLogPenalty (n : Nat) : EReal :=
  ((Real.log 2) / (((n + 1 : Nat) : ℝ)) : ℝ)

/-- The generic finite-alphabet polynomial penalty vanishes after
normalization. -/
theorem finiteAlphabetMethodOfTypesPolynomialPenalty_tendsto_zero
    (α : Type u) [Fintype α] :
    Tendsto (fun n : Nat => finiteAlphabetMethodOfTypesPolynomialPenalty α n)
      atTop (𝓝 (0 : EReal)) := by
  have hlog :
      Tendsto
        (fun x : ℝ => Real.log x ^ (1 : Nat) / (1 * x + (-1)))
        atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have harg : Tendsto (fun n : Nat => (((n + 2 : Nat) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right _ (2 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbase :
      Tendsto
        (fun n : Nat =>
          Real.log (((n + 2 : Nat) : ℝ)) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    convert hlog.comp harg using 1
    ext n
    simp [one_mul, Nat.cast_add]
    ring
  have hreal :
      Tendsto
        (fun n : Nat =>
          ((Fintype.card α : ℝ) *
            Real.log (((n + 2 : Nat) : ℝ))) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    simpa [mul_div_assoc] using hbase.const_mul (Fintype.card α : ℝ)
  exact EReal.tendsto_coe.mpr hreal

/-- The equal-prior `log 2 / (n+1)` normalization penalty vanishes. -/
theorem equalPriorAverageLogPenalty_tendsto_zero :
    Tendsto (fun n : Nat => equalPriorAverageLogPenalty n)
      atTop (𝓝 (0 : EReal)) := by
  have hden :
      Tendsto (fun n : Nat => (((n + 1 : Nat) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right _ (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hreal :
      Tendsto (fun n : Nat => (Real.log 2) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden) :
        Tendsto (fun n : Nat => (Real.log 2) * ((((n + 1 : Nat) : ℝ))⁻¹))
          atTop (𝓝 (Real.log 2 * 0)))
  exact EReal.tendsto_coe.mpr hreal

/-- Multiplying a finite `ℝ≥0` error by the quantum-to-classical `1 / 2`
constant can increase the normalized negative log by at most
`log 2 / (n+1)`. -/
theorem normalizedNegLog_half_mul_coe_le_add_equalPriorAverageLogPenalty
    (n : Nat) (x : ℝ≥0) :
    normalizedNegLog n ((((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞)) ≤
      normalizedNegLog n (x : ℝ≥0∞) + equalPriorAverageLogPenalty n := by
  by_cases hx : x = 0
  · subst x
    rw [normalizedNegLog_eq_top_of_eq_zero n
        ((((1 / 2 : ℝ≥0) * 0 : ℝ≥0) : ℝ≥0∞)) (by simp),
      normalizedNegLog_eq_top_of_eq_zero n ((0 : ℝ≥0) : ℝ≥0∞) (by simp)]
    simp [equalPriorAverageLogPenalty]
  · have hxpos_nn : 0 < x := lt_of_le_of_ne (by positivity) (Ne.symm hx)
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast hxpos_nn
    have hmul_ne_zero :
        (((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast mul_ne_zero (by norm_num : (1 / 2 : ℝ≥0) ≠ 0) hx
    have hx_ne_zero : (x : ℝ≥0∞) ≠ 0 := by exact_mod_cast hx
    have hmul_ne_top :
        ((((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.coe_ne_top
    rw [normalizedNegLog_eq_coe_real_of_ne_zero_ne_top
          n ((((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞))
          hmul_ne_zero hmul_ne_top,
        normalizedNegLog_eq_coe_real_of_ne_zero_ne_top
          n (x : ℝ≥0∞) hx_ne_zero (by simp)]
    unfold equalPriorAverageLogPenalty
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    unfold normalizedNegLogReal
    simp only [ENNReal.coe_toReal, NNReal.coe_mul]
    have hhalf_ne : (((1 / 2 : ℝ≥0) : ℝ) ≠ 0) := by norm_num
    have hlog_half : Real.log (((1 / 2 : ℝ≥0) : ℝ)) = -Real.log 2 := by
      rw [show (((1 / 2 : ℝ≥0) : ℝ)) = (2 : ℝ)⁻¹ by norm_num]
      rw [Real.log_inv]
    rw [Real.log_mul hhalf_ne hxpos.ne', hlog_half]
    ring_nf
    rfl

/-- The method-of-types polynomial penalty vanishes after normalization. -/
theorem methodOfTypesPolynomialPenalty_tendsto_zero {a : Type u} [Fintype a] :
    Tendsto (fun n : Nat => methodOfTypesPolynomialPenalty (a := a) n)
      atTop (𝓝 (0 : EReal)) := by
  have hlog :
      Tendsto
        (fun x : ℝ => Real.log x ^ (1 : Nat) / (1 * x + (-1)))
        atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have harg : Tendsto (fun n : Nat => (((n + 2 : Nat) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right _ (2 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbase :
      Tendsto
        (fun n : Nat =>
          Real.log (((n + 2 : Nat) : ℝ)) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    convert hlog.comp harg using 1
    ext n
    simp [one_mul, Nat.cast_add]
    ring
  have hreal :
      Tendsto
        (fun n : Nat =>
          ((nussbaumSzkolaAlphabetCard (a := a) : ℝ) *
            Real.log (((n + 2 : Nat) : ℝ))) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    simpa [mul_div_assoc] using hbase.const_mul (nussbaumSzkolaAlphabetCard (a := a) : ℝ)
  exact EReal.tendsto_coe.mpr hreal

/-- The quantum-to-classical converse comparison constant from the Gour route.

Gour's Nussbaum--Szkola comparison lower-bounds the quantum symmetric error by
one half of the associated classical error
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
def quantumChernoffConverseComparisonConstant : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞)

/-- A finite classical probability distribution. -/
structure ClassicalDistribution (α : Type u) [Fintype α] where
  prob : α → ℝ≥0
  sum_eq_one : ∑ x, prob x = 1

namespace ClassicalDistribution

variable {α : Type u} [Fintype α]

/-- Support containment for finite classical distributions. -/
def SupportedBy (r : ClassicalDistribution α) (p : α → ℝ≥0) : Prop :=
  ∀ x, r.prob x ≠ 0 → p x ≠ 0

@[simp]
theorem supportedBy_self (r : ClassicalDistribution α) :
    r.SupportedBy r.prob := by
  intro x hx
  exact hx

/-- Support containment is transitive. -/
theorem SupportedBy.trans {r p : ClassicalDistribution α} {q : α → ℝ≥0}
    (hrp : r.SupportedBy p.prob) (hpq : p.SupportedBy q) :
    r.SupportedBy q := by
  intro x hx
  exact hpq x (hrp x hx)

/-- A finite probability distribution has at least one nonzero mass point. -/
theorem exists_prob_ne_zero (r : ClassicalDistribution α) :
    ∃ x : α, r.prob x ≠ 0 := by
  by_contra h
  have hall : ∀ x : α, r.prob x = 0 := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hsum0 : ∑ x : α, r.prob x = 0 := by
    simp [hall]
  have : (0 : ℝ≥0) = 1 := by
    simpa [hsum0] using r.sum_eq_one
  norm_num at this

/-- A chosen nonzero support point of a finite distribution. -/
noncomputable def supportPoint (r : ClassicalDistribution α) : α :=
  Classical.choose (exists_prob_ne_zero r)

theorem supportPoint_prob_ne_zero (r : ClassicalDistribution α) :
    r.prob r.supportPoint ≠ 0 :=
  Classical.choose_spec (exists_prob_ne_zero r)

/-- The floors of scaled probabilities have total mass at most the scale. -/
theorem floor_scaled_sum_le (r : ClassicalDistribution α) (N : Nat) :
    ∑ x : α, Nat.floor ((N : ℝ) * (r.prob x : ℝ)) ≤ N := by
  exact_mod_cast (show
    (∑ x : α, (Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : ℝ)) ≤ (N : ℝ) from by
      have hterm : ∀ x : α,
          (Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : ℝ) ≤
            (N : ℝ) * (r.prob x : ℝ) := by
        intro x
        exact Nat.floor_le (mul_nonneg (by positivity) (by positivity))
      calc
        (∑ x : α, (Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : ℝ))
            ≤ ∑ x : α, (N : ℝ) * (r.prob x : ℝ) :=
              Finset.sum_le_sum fun x _ => hterm x
        _ = (N : ℝ) := by
          rw [← Finset.mul_sum]
          have hsum : ∑ x : α, (r.prob x : ℝ) = 1 := by
            exact_mod_cast r.sum_eq_one
          rw [hsum]
          ring)

/-- Empirical counts obtained by flooring every non-base coordinate and placing
the remaining mass on a fixed support point.  This gives exact total count `N`
while keeping the support contained in the original distribution's support. -/
noncomputable def roundedCounts [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) : α → Nat :=
  fun x =>
    if x = r.supportPoint then
      N - ∑ y ∈ (Finset.univ.erase r.supportPoint),
        Nat.floor ((N : ℝ) * (r.prob y : ℝ))
    else
      Nat.floor ((N : ℝ) * (r.prob x : ℝ))

theorem roundedCounts_sum [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) :
    ∑ x : α, r.roundedCounts N x = N := by
  classical
  let x0 := r.supportPoint
  have hsubset :
      ∑ y ∈ (Finset.univ.erase x0), Nat.floor ((N : ℝ) * (r.prob y : ℝ)) ≤ N := by
    calc
      ∑ y ∈ (Finset.univ.erase x0), Nat.floor ((N : ℝ) * (r.prob y : ℝ))
          ≤ ∑ y : α, Nat.floor ((N : ℝ) * (r.prob y : ℝ)) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro y hy; simp at hy ⊢)
              (by intro y _ _; exact Nat.zero_le _)
      _ ≤ N := floor_scaled_sum_le r N
  have hsum_erase :
      ∑ x ∈ (Finset.univ.erase x0), r.roundedCounts N x =
        ∑ x ∈ (Finset.univ.erase x0),
          Nat.floor ((N : ℝ) * (r.prob x : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : x ≠ x0 := by
      simpa using (Finset.mem_erase.mp hx).1
    simp [roundedCounts, x0, hxne]
  have hsplit :
      ∑ x : α, r.roundedCounts N x =
        r.roundedCounts N x0 +
          ∑ x ∈ (Finset.univ.erase x0), r.roundedCounts N x := by
    rw [← Finset.sum_insert]
    · simp
    · simp
  rw [hsplit, hsum_erase]
  let S := ∑ y ∈ Finset.univ.erase x0,
    Nat.floor ((N : ℝ) * (r.prob y : ℝ))
  have hx0 : r.roundedCounts N x0 = N - S := by
    simp [roundedCounts, x0, S]
  have hS : S ≤ N := hsubset
  rw [hx0]
  exact Nat.sub_add_cancel hS

@[simp]
theorem roundedCounts_supportPoint [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) :
    r.roundedCounts N r.supportPoint =
      N - ∑ y ∈ (Finset.univ.erase r.supportPoint),
        Nat.floor ((N : ℝ) * (r.prob y : ℝ)) := by
  simp [roundedCounts]

theorem roundedCounts_of_ne_supportPoint [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) {x : α}
    (hx : x ≠ r.supportPoint) :
    r.roundedCounts N x =
      Nat.floor ((N : ℝ) * (r.prob x : ℝ)) := by
  simp [roundedCounts, hx]

theorem roundedCounts_of_ne_supportPoint_abs_sub_le_inv [DecidableEq α]
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N)
    {x : α} (hx : x ≠ r.supportPoint) :
    |((r.roundedCounts N x : ℝ) / (N : ℝ)) - (r.prob x : ℝ)| ≤
      1 / (N : ℝ) := by
  rw [roundedCounts_of_ne_supportPoint r N hx]
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha_nonneg : 0 ≤ (N : ℝ) * (r.prob x : ℝ) := by
    positivity
  have hfloor_le :
      ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) ≤
        (N : ℝ) * (r.prob x : ℝ) :=
    Nat.floor_le ha_nonneg
  have hlt_floor :
      (N : ℝ) * (r.prob x : ℝ) <
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1 :=
    Nat.lt_floor_add_one ((N : ℝ) * (r.prob x : ℝ))
  have hleft :
      ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) -
          (r.prob x : ℝ) ≤
        1 / (N : ℝ) := by
    have hfloor_le' :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) ≤
          (r.prob x : ℝ) * (N : ℝ) := by
      nlinarith [hfloor_le]
    have hdiv_le :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) ≤
          (r.prob x : ℝ) := by
      exact (div_le_iff₀ hNreal).mpr hfloor_le'
    have hnonpos :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) -
            (r.prob x : ℝ) ≤ 0 := by
      exact sub_nonpos.mpr hdiv_le
    have hpos : 0 ≤ 1 / (N : ℝ) := by positivity
    exact hnonpos.trans hpos
  have hright :
      (r.prob x : ℝ) -
          ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) ≤
        1 / (N : ℝ) := by
    have hle_num :
        (r.prob x : ℝ) * (N : ℝ) ≤
          ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1 := by
      nlinarith [hlt_floor]
    have hp_le :
        (r.prob x : ℝ) ≤
          (((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1) /
            (N : ℝ) := by
      exact (le_div_iff₀ hNreal).mpr hle_num
    have hsum :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) +
            1 / (N : ℝ) =
          (((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1) /
            (N : ℝ) := by
      field_simp [hNreal.ne']
    exact (sub_le_iff_le_add'.mpr (by simpa [← hsum] using hp_le))
  exact abs_sub_le_iff.mpr ⟨hleft, hright⟩

theorem roundedCounts_supportPoint_abs_sub_le_card_div [DecidableEq α]
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) :
    |((r.roundedCounts N r.supportPoint : ℝ) / (N : ℝ)) -
        (r.prob r.supportPoint : ℝ)| ≤
      (Fintype.card α : ℝ) / (N : ℝ) := by
  classical
  let x0 := r.supportPoint
  let S : Nat := ∑ y ∈ (Finset.univ.erase x0),
    Nat.floor ((N : ℝ) * (r.prob y : ℝ))
  let Sreal : ℝ := ∑ y ∈ (Finset.univ.erase x0),
    ((Nat.floor ((N : ℝ) * (r.prob y : ℝ)) : Nat) : ℝ)
  let Psum : ℝ := ∑ y ∈ (Finset.univ.erase x0),
    (N : ℝ) * (r.prob y : ℝ)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hSleN : S ≤ N := by
    calc
      S ≤ ∑ y : α, Nat.floor ((N : ℝ) * (r.prob y : ℝ)) := by
        unfold S
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro y hy; simp at hy ⊢)
          (by intro y _ _; exact Nat.zero_le _)
      _ ≤ N := floor_scaled_sum_le r N
  have hSreal : (S : ℝ) = Sreal := by
    simp [S, Sreal]
  have hcount :
      (r.roundedCounts N x0 : ℝ) = (N : ℝ) - Sreal := by
    rw [roundedCounts_supportPoint]
    change ((N - S : Nat) : ℝ) = (N : ℝ) - Sreal
    rw [Nat.cast_sub hSleN]
    rw [hSreal]
  have hsum_all : ∑ x : α, (r.prob x : ℝ) = 1 := by
    exact_mod_cast r.sum_eq_one
  have hsum_split :
      ∑ x : α, (r.prob x : ℝ) =
        (r.prob x0 : ℝ) +
          ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) := by
    calc
      ∑ x : α, (r.prob x : ℝ)
          = ∑ x ∈ insert x0 (Finset.univ.erase x0), (r.prob x : ℝ) := by
            simp
      _ = (r.prob x0 : ℝ) +
            ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) := by
            rw [Finset.sum_insert]
            simp [x0]
  have hsum_prob :
      (r.prob x0 : ℝ) +
          ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) = 1 := by
    rw [← hsum_split, hsum_all]
  have hPsum :
      Psum = (N : ℝ) *
        ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) := by
    unfold Psum
    rw [Finset.mul_sum]
  have hscaled_sum :
      (r.prob x0 : ℝ) * (N : ℝ) + Psum = (N : ℝ) := by
    rw [hPsum]
    nlinarith [hsum_prob, hNreal]
  have hSreal_le_Psum : Sreal ≤ Psum := by
    unfold Sreal Psum
    exact Finset.sum_le_sum fun y _ => by
      exact Nat.floor_le (by positivity :
        0 ≤ (N : ℝ) * (r.prob y : ℝ))
  have hPsum_le_Sreal_add_cardErase :
      Psum ≤ Sreal + ((Finset.univ.erase x0).card : ℝ) := by
    unfold Sreal Psum
    calc
      ∑ y ∈ Finset.univ.erase x0, (N : ℝ) * (r.prob y : ℝ)
          ≤ ∑ y ∈ Finset.univ.erase x0,
              (((Nat.floor ((N : ℝ) * (r.prob y : ℝ)) : Nat) : ℝ) + 1) := by
            exact Finset.sum_le_sum fun y _ =>
              le_of_lt (Nat.lt_floor_add_one
                ((N : ℝ) * (r.prob y : ℝ)))
      _ =
          (∑ y ∈ Finset.univ.erase x0,
            ((Nat.floor ((N : ℝ) * (r.prob y : ℝ)) : Nat) : ℝ)) +
            ((Finset.univ.erase x0).card : ℝ) := by
            simp [Finset.sum_add_distrib]
  have hcard_erase :
      ((Finset.univ.erase x0).card : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast Finset.card_le_univ (Finset.univ.erase x0)
  have hprob_le_count_div :
      (r.prob x0 : ℝ) ≤ (r.roundedCounts N x0 : ℝ) / (N : ℝ) := by
    have hnum :
        (r.prob x0 : ℝ) * (N : ℝ) ≤ (r.roundedCounts N x0 : ℝ) := by
      rw [hcount]
      nlinarith [hscaled_sum, hSreal_le_Psum]
    exact (le_div_iff₀ hNreal).mpr hnum
  have hcount_sub_prob_le_card :
      (r.roundedCounts N x0 : ℝ) - (r.prob x0 : ℝ) * (N : ℝ) ≤
        (Fintype.card α : ℝ) := by
    rw [hcount]
    nlinarith [hscaled_sum, hPsum_le_Sreal_add_cardErase, hcard_erase]
  have hcount_div_le :
      (r.roundedCounts N x0 : ℝ) / (N : ℝ) ≤
        (r.prob x0 : ℝ) + (Fintype.card α : ℝ) / (N : ℝ) := by
    have hnum :
        (r.roundedCounts N x0 : ℝ) ≤
          ((r.prob x0 : ℝ) + (Fintype.card α : ℝ) / (N : ℝ)) *
            (N : ℝ) := by
      have hright :
          ((r.prob x0 : ℝ) + (Fintype.card α : ℝ) / (N : ℝ)) *
              (N : ℝ) =
            (r.prob x0 : ℝ) * (N : ℝ) + (Fintype.card α : ℝ) := by
        field_simp [hNreal.ne']
      rw [hright]
      linarith [hcount_sub_prob_le_card]
    exact (div_le_iff₀ hNreal).mpr hnum
  have hleft :
      (r.roundedCounts N x0 : ℝ) / (N : ℝ) -
          (r.prob x0 : ℝ) ≤
        (Fintype.card α : ℝ) / (N : ℝ) :=
    sub_le_iff_le_add'.mpr hcount_div_le
  have hright :
      (r.prob x0 : ℝ) -
          (r.roundedCounts N x0 : ℝ) / (N : ℝ) ≤
        (Fintype.card α : ℝ) / (N : ℝ) := by
    have hnonpos :
        (r.prob x0 : ℝ) -
            (r.roundedCounts N x0 : ℝ) / (N : ℝ) ≤ 0 :=
      sub_nonpos.mpr hprob_le_count_div
    have hnonneg : 0 ≤ (Fintype.card α : ℝ) / (N : ℝ) := by
      positivity
    exact hnonpos.trans hnonneg
  simpa [x0] using abs_sub_le_iff.mpr ⟨hleft, hright⟩

theorem roundedCounts_abs_sub_le_card_div [DecidableEq α]
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) (x : α) :
    |((r.roundedCounts N x : ℝ) / (N : ℝ)) - (r.prob x : ℝ)| ≤
      (Fintype.card α : ℝ) / (N : ℝ) := by
  classical
  by_cases hx : x = r.supportPoint
  · simpa [hx] using roundedCounts_supportPoint_abs_sub_le_card_div
      (r := r) hN
  · have hfloor :=
      roundedCounts_of_ne_supportPoint_abs_sub_le_inv
        (r := r) hN hx
    have hcard_pos : 0 < Fintype.card α :=
      Fintype.card_pos_iff.mpr ⟨r.supportPoint⟩
    have hcard_ge_one : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
      exact_mod_cast hcard_pos
    have hNreal_nonneg : 0 ≤ (N : ℝ) := by
      exact le_of_lt (by exact_mod_cast hN : 0 < (N : ℝ))
    have hscale :
        1 / (N : ℝ) ≤ (Fintype.card α : ℝ) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right hcard_ge_one hNreal_nonneg
    exact hfloor.trans hscale

/-- The tensor-power profile associated with `roundedCounts`. -/
noncomputable def roundedProfile [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) : TensorPowerProfile α N :=
  (TensorPowerProfile.equivWeakCompositions (a := α) (n := N)).symm
    ⟨r.roundedCounts N, roundedCounts_sum r N⟩

end ClassicalDistribution

/-- One real KL summand, with the standard `0 log 0 = 0` convention on the
first argument.  Unsupported positive mass is handled by the EReal wrapper
below, not by this real-valued expression. -/
def relativeEntropySummandReal {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (x : α) : ℝ :=
  if r.prob x = 0 then
    0
  else
    (r.prob x : ℝ) * Real.log ((r.prob x : ℝ) / (p.prob x : ℝ))

/-- Finite real-valued classical relative entropy on a fixed support. -/
def relativeEntropyReal {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) : ℝ :=
  ∑ x, relativeEntropySummandReal r p x

/-- Support-aware extended-real classical relative entropy.  It is `⊤` when
`r` assigns positive mass outside the support of `p`. -/
def relativeEntropy {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) : EReal := by
  classical
  exact
    if r.SupportedBy p.prob then
      (relativeEntropyReal r p : EReal)
    else
      ⊤

@[simp]
theorem relativeEntropySummandReal_zero_mass {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) {x : α} (hx : r.prob x = 0) :
    relativeEntropySummandReal r p x = 0 := by
  simp [relativeEntropySummandReal, hx]

theorem relativeEntropy_eq_top_of_not_supported {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : ¬ r.SupportedBy p.prob) :
    relativeEntropy r p = ⊤ := by
  classical
  simp [relativeEntropy, h]

theorem relativeEntropy_eq_coe_of_supported {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : r.SupportedBy p.prob) :
    relativeEntropy r p = (relativeEntropyReal r p : EReal) := by
  classical
  simp [relativeEntropy, h]

/-- Pointwise Gibbs inequality with the `0 log 0 = 0` convention. -/
theorem relativeEntropySummandReal_ge_sub {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : r.SupportedBy p.prob) (x : α) :
    (r.prob x : ℝ) - (p.prob x : ℝ) ≤
      relativeEntropySummandReal r p x := by
  by_cases hr0 : r.prob x = 0
  · have hp_nonneg : 0 ≤ (p.prob x : ℝ) := by positivity
    simp [relativeEntropySummandReal, hr0]
  · have hp0 : p.prob x ≠ 0 := h x hr0
    have hrr : 0 < (r.prob x : ℝ) := by
      have hrr_nn : (0 : ℝ≥0) < r.prob x :=
        lt_of_le_of_ne (by positivity) (Ne.symm hr0)
      exact_mod_cast hrr_nn
    have hpp : 0 < (p.prob x : ℝ) := by
      have hpp_nn : (0 : ℝ≥0) < p.prob x :=
        lt_of_le_of_ne (by positivity) (Ne.symm hp0)
      exact_mod_cast hpp_nn
    have hratio : 0 < (r.prob x : ℝ) / (p.prob x : ℝ) :=
      div_pos hrr hpp
    have hlog := Real.one_sub_inv_le_log_of_pos hratio
    have hmul :
        (r.prob x : ℝ) * (1 - (((r.prob x : ℝ) / (p.prob x : ℝ))⁻¹)) ≤
          (r.prob x : ℝ) *
            Real.log ((r.prob x : ℝ) / (p.prob x : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hrr)
    calc
      (r.prob x : ℝ) - (p.prob x : ℝ)
          = (r.prob x : ℝ) *
              (1 - (((r.prob x : ℝ) / (p.prob x : ℝ))⁻¹)) := by
            field_simp [hrr.ne', hpp.ne']
      _ ≤ (r.prob x : ℝ) *
            Real.log ((r.prob x : ℝ) / (p.prob x : ℝ)) := hmul
      _ = relativeEntropySummandReal r p x := by
            simp [relativeEntropySummandReal, hr0]

/-- Classical relative entropy is nonnegative on a fixed support. -/
theorem relativeEntropyReal_nonneg {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : r.SupportedBy p.prob) :
    0 ≤ relativeEntropyReal r p := by
  have hterm :
      ∀ x : α,
        (r.prob x : ℝ) - (p.prob x : ℝ) ≤
          relativeEntropySummandReal r p x :=
    relativeEntropySummandReal_ge_sub r p h
  have hsum_lower :
      (∑ x : α, ((r.prob x : ℝ) - (p.prob x : ℝ))) ≤
        ∑ x : α, relativeEntropySummandReal r p x :=
    Finset.sum_le_sum fun x _ => hterm x
  have hsumr : ∑ x : α, (r.prob x : ℝ) = 1 := by
    exact_mod_cast r.sum_eq_one
  have hsump : ∑ x : α, (p.prob x : ℝ) = 1 := by
    exact_mod_cast p.sum_eq_one
  have hzero :
      (∑ x : α, ((r.prob x : ℝ) - (p.prob x : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib, hsumr, hsump]
    ring
  unfold relativeEntropyReal
  linarith

end BinaryHypothesisTest

namespace TensorPowerProfile

variable {α : Type u} [DecidableEq α] [Fintype α]

/-- The empirical distribution associated with a positive-length tensor-power
profile. -/
noncomputable def empiricalDistribution {N : Nat} (profile : TensorPowerProfile α N)
    (hN : 0 < N) : BinaryHypothesisTest.ClassicalDistribution α :=
  { prob := fun z => (profile.1 z : ℝ≥0) / (N : ℝ≥0)
    sum_eq_one := by
      apply NNReal.eq
      change (↑(∑ z : α, (profile.1 z : ℝ≥0) / (N : ℝ≥0)) : ℝ) = (1 : ℝ)
      rw [NNReal.coe_sum]
      simp only [NNReal.coe_div, NNReal.coe_natCast]
      rw [← Finset.sum_div]
      have hsum_nat :
          ∑ z : α, profile.1 z = N :=
        tensorPowerTypeProfile_sum_of_mem_profiles (a := α) N profile.2
      have hsum_real : ∑ z : α, (profile.1 z : ℝ) = (N : ℝ) := by
        exact_mod_cast hsum_nat
      rw [hsum_real]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)] }

@[simp]
theorem empiricalDistribution_prob {N : Nat} (profile : TensorPowerProfile α N)
    (hN : 0 < N) :
    (profile.empiricalDistribution hN).prob =
      fun z => (profile.1 z : ℝ≥0) / (N : ℝ≥0) := rfl

end TensorPowerProfile

namespace BinaryHypothesisTest

namespace ClassicalDistribution

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem roundedCounts_support
    (r : ClassicalDistribution α) (N : Nat) {x : α}
    (hcount : r.roundedCounts N x ≠ 0) :
    r.prob x ≠ 0 := by
  classical
  by_cases hx : x = r.supportPoint
  · rw [hx]
    exact supportPoint_prob_ne_zero r
  · simp [roundedCounts, hx] at hcount
    by_contra hp0
    simp [hp0] at hcount
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hcount

/-- The empirical distribution obtained from rounded counts has support
contained in the original finite distribution. -/
theorem roundedProfile_empiricalDistribution_supportedBy
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) :
    ((r.roundedProfile N).empiricalDistribution hN).SupportedBy r.prob := by
  intro x hx
  have hprofile : (r.roundedProfile N).1 = r.roundedCounts N := by
    unfold roundedProfile
    rfl
  have hcount : (r.roundedProfile N).1 x ≠ 0 := by
    by_contra hzero
    rw [TensorPowerProfile.empiricalDistribution_prob] at hx
    simp [hzero] at hx
  exact roundedCounts_support r N (by simpa [hprofile] using hcount)

theorem roundedProfile_empiricalDistribution_prob_abs_sub_le_card_div
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) (x : α) :
    |(((r.roundedProfile N).empiricalDistribution hN).prob x : ℝ) -
        (r.prob x : ℝ)| ≤
      (Fintype.card α : ℝ) / (N : ℝ) := by
  have hprofile : (r.roundedProfile N).1 = r.roundedCounts N := by
    unfold roundedProfile
    rfl
  simpa [TensorPowerProfile.empiricalDistribution_prob, hprofile,
    NNReal.coe_div, NNReal.coe_natCast] using
      roundedCounts_abs_sub_le_card_div (r := r) hN x

theorem roundedProfile_empiricalDistribution_prob_tendsto
    (r : ClassicalDistribution α) (x : α) :
    Tendsto
      (fun n : Nat =>
        (((r.roundedProfile (n + 1)).empiricalDistribution
          (Nat.succ_pos n)).prob x : ℝ))
      atTop (𝓝 (r.prob x : ℝ)) := by
  have hden :
      Tendsto (fun n : Nat => ((n + 1 : Nat) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hbound :
      ∀ n : Nat,
        |(((r.roundedProfile (n + 1)).empiricalDistribution
            (Nat.succ_pos n)).prob x : ℝ) - (r.prob x : ℝ)| ≤
          (Fintype.card α : ℝ) / ((n + 1 : Nat) : ℝ) := by
    intro n
    exact roundedProfile_empiricalDistribution_prob_abs_sub_le_card_div
      (r := r) (N := n + 1) (Nat.succ_pos n) x
  have hpenalty :
      Tendsto
        (fun n : Nat => (Fintype.card α : ℝ) / ((n + 1 : Nat) : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have habs :
      Tendsto
        (fun n : Nat =>
          |(((r.roundedProfile (n + 1)).empiricalDistribution
              (Nat.succ_pos n)).prob x : ℝ) - (r.prob x : ℝ)|)
        atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg _)
      hbound
      hpenalty
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq, abs_sub_comm] using habs

theorem roundedProfile_empiricalDistribution_prob_eq_zero_of_prob_eq_zero
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N)
    {x : α} (hx : r.prob x = 0) :
    ((r.roundedProfile N).empiricalDistribution hN).prob x = 0 := by
  by_contra hne
  exact ((roundedProfile_empiricalDistribution_supportedBy r hN) x hne) hx

theorem relativeEntropySummandReal_roundedProfile_tendsto
    (r p : ClassicalDistribution α) (hp : r.SupportedBy p.prob) (x : α) :
    Tendsto
      (fun n : Nat =>
        relativeEntropySummandReal
          ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
          p x)
      atTop (𝓝 (relativeEntropySummandReal r p x)) := by
  by_cases hr0 : r.prob x = 0
  · have hzero :
      ∀ n : Nat,
        (((r.roundedProfile (n + 1)).empiricalDistribution
          (Nat.succ_pos n)).prob x) = 0 := by
      intro n
      exact roundedProfile_empiricalDistribution_prob_eq_zero_of_prob_eq_zero
        (r := r) (N := n + 1) (Nat.succ_pos n) hr0
    have heq :
        (fun n : Nat =>
          relativeEntropySummandReal
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
            p x) = fun _n : Nat => 0 := by
      funext n
      simp [relativeEntropySummandReal, hzero n]
    rw [heq]
    simp [relativeEntropySummandReal, hr0]
  · let f : Nat → ℝ := fun n =>
      (((r.roundedProfile (n + 1)).empiricalDistribution
        (Nat.succ_pos n)).prob x : ℝ)
    let a : ℝ := (r.prob x : ℝ)
    have hf : Tendsto f atTop (𝓝 a) := by
      simpa [f, a] using
        roundedProfile_empiricalDistribution_prob_tendsto (r := r) x
    have ha : a ≠ 0 := by
      exact NNReal.coe_ne_zero.mpr hr0
    have hp0_nn : p.prob x ≠ 0 := hp x hr0
    have hp0 : (p.prob x : ℝ) ≠ 0 :=
      NNReal.coe_ne_zero.mpr hp0_nn
    have hcont :
        ContinuousAt
          (fun t : ℝ => t * Real.log (t / (p.prob x : ℝ))) a := by
      exact continuousAt_id.mul
        ((continuousAt_id.div_const (p.prob x : ℝ)).log
          (div_ne_zero ha hp0))
    have hmain :
        Tendsto
          (fun n : Nat => f n * Real.log (f n / (p.prob x : ℝ)))
          atTop
          (𝓝 (a * Real.log (a / (p.prob x : ℝ)))) :=
      hcont.tendsto.comp hf
    have hne_eventually : ∀ᶠ n : Nat in atTop, f n ≠ 0 :=
      hf.eventually_ne ha
    have htarget :
        relativeEntropySummandReal r p x =
          a * Real.log (a / (p.prob x : ℝ)) := by
      simp [relativeEntropySummandReal, hr0, a]
    rw [htarget]
    refine hmain.congr' ?_
    filter_upwards [hne_eventually] with n hn
    have hprob_ne :
        ((r.roundedProfile (n + 1)).empiricalDistribution
          (Nat.succ_pos n)).prob x ≠ 0 := by
      exact NNReal.coe_ne_zero.mp (by simpa [f] using hn)
    rw [relativeEntropySummandReal, if_neg hprob_ne]

theorem relativeEntropyReal_roundedProfile_tendsto
    (r p : ClassicalDistribution α) (hp : r.SupportedBy p.prob) :
    Tendsto
      (fun n : Nat =>
        relativeEntropyReal
          ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
          p)
      atTop (𝓝 (relativeEntropyReal r p)) := by
  unfold relativeEntropyReal
  simpa using
    tendsto_finsetSum (Finset.univ : Finset α)
      (fun x _ => relativeEntropySummandReal_roundedProfile_tendsto
        (r := r) (p := p) hp x)

end ClassicalDistribution

end BinaryHypothesisTest

namespace BinaryHypothesisTest

/-- A finite classical binary discrimination model with two probability vectors
on the same finite alphabet. -/
structure ClassicalBinaryModel (α : Type u) [Fintype α] where
  p : α → ℝ≥0
  q : α → ℝ≥0
  p_sum : ∑ x, p x = 1
  q_sum : ∑ x, q x = 1

namespace ClassicalBinaryModel

variable {α : Type u} [Fintype α]

/-- The `p` side as a finite classical distribution. -/
def pDistribution (M : ClassicalBinaryModel α) : ClassicalDistribution α :=
  { prob := M.p
    sum_eq_one := M.p_sum }

/-- The `q` side as a finite classical distribution. -/
def qDistribution (M : ClassicalBinaryModel α) : ClassicalDistribution α :=
  { prob := M.q
    sum_eq_one := M.q_sum }

@[simp]
theorem pDistribution_prob (M : ClassicalBinaryModel α) :
    M.pDistribution.prob = M.p := rfl

@[simp]
theorem qDistribution_prob (M : ClassicalBinaryModel α) :
    M.qDistribution.prob = M.q := rfl

/-- Equal-prior classical error `sum_x min{p_x/2, q_x/2}`. -/
def equalPriorError (M : ClassicalBinaryModel α) : ℝ≥0 :=
  ∑ x, min ((1 / 2 : ℝ≥0) * M.p x) ((1 / 2 : ℝ≥0) * M.q x)

/-- Equal-prior classical error as an `ℝ≥0∞` quantity. -/
def equalPriorErrorENNReal (M : ClassicalBinaryModel α) : ℝ≥0∞ :=
  (M.equalPriorError : ℝ≥0∞)

/-- IID tensor power of a finite classical binary model. -/
def tensorPower (M : ClassicalBinaryModel α) : (n : Nat) → ClassicalBinaryModel (TensorPower α n)
  | 0 =>
      { p := fun _ => 1
        q := fun _ => 1
        p_sum := by
          change (∑ _x : PUnit, (1 : ℝ≥0)) = 1
          simp
        q_sum := by
          change (∑ _x : PUnit, (1 : ℝ≥0)) = 1
          simp }
  | n + 1 =>
      let Mn := M.tensorPower n
      { p := fun x => M.p x.1 * Mn.p x.2
        q := fun x => M.q x.1 * Mn.q x.2
        p_sum := by
          change (∑ x : Prod α (TensorPower α n), M.p x.1 * Mn.p x.2) = 1
          rw [Fintype.sum_prod_type]
          calc
            (∑ x : α, ∑ xs : TensorPower α n, M.p x * Mn.p xs)
                = ∑ x : α, M.p x * ∑ xs : TensorPower α n, Mn.p xs := by
                  simp [Finset.mul_sum]
            _ = ∑ x : α, M.p x := by simp [Mn.p_sum]
            _ = 1 := M.p_sum
        q_sum := by
          change (∑ x : Prod α (TensorPower α n), M.q x.1 * Mn.q x.2) = 1
          rw [Fintype.sum_prod_type]
          calc
            (∑ x : α, ∑ xs : TensorPower α n, M.q x * Mn.q xs)
                = ∑ x : α, M.q x * ∑ xs : TensorPower α n, Mn.q xs := by
                  simp [Finset.mul_sum]
            _ = ∑ x : α, M.q x := by simp [Mn.q_sum]
            _ = 1 := M.q_sum }

@[simp]
theorem tensorPower_zero_p (M : ClassicalBinaryModel α) (x : TensorPower α 0) :
    (M.tensorPower 0).p x = 1 := by
  cases x
  simp [tensorPower]

@[simp]
theorem tensorPower_zero_q (M : ClassicalBinaryModel α) (x : TensorPower α 0) :
    (M.tensorPower 0).q x = 1 := by
  cases x
  simp [tensorPower]

@[simp]
theorem tensorPower_succ_p (M : ClassicalBinaryModel α) (n : Nat)
    (x : α) (xs : TensorPower α n) :
    (M.tensorPower (n + 1)).p (x, xs) = M.p x * (M.tensorPower n).p xs := by
  simp [tensorPower]

@[simp]
theorem tensorPower_succ_q (M : ClassicalBinaryModel α) (n : Nat)
    (x : α) (xs : TensorPower α n) :
    (M.tensorPower (n + 1)).q (x, xs) = M.q x * (M.tensorPower n).q xs := by
  simp [tensorPower]

/-- Classical Petz/Chernoff coefficient `sum_x p_x^s q_x^(1-s)`. -/
def petzChernoffCoefficient (M : ClassicalBinaryModel α) (s : ℝ) : ℝ≥0 :=
  ∑ x, (M.p x) ^ s * (M.q x) ^ (1 - s)

/-- Classical Chernoff exponent for a fixed `s`, using natural logarithms. -/
def chernoffExponent (M : ClassicalBinaryModel α) (s : ℝ) : EReal :=
  - ENNReal.log (M.petzChernoffCoefficient s : ℝ≥0∞)

/-- Classical Chernoff distance as the supremum of fixed-`s` exponents over
`0 ≤ s ≤ 1`. -/
def chernoffDistance (M : ClassicalBinaryModel α) : EReal :=
  ⨆ s : Set.Icc (0 : ℝ) 1, M.chernoffExponent s.1

/-- The unnormalized tilted Chernoff weight `p_x^s q_x^(1-s)`. -/
noncomputable def tiltedWeight (M : ClassicalBinaryModel α) (s : ℝ) (x : α) : ℝ≥0 :=
  M.p x ^ s * M.q x ^ (1 - s)

/-- Tilted weights sum to the classical Petz/Chernoff coefficient. -/
theorem tiltedWeight_sum (M : ClassicalBinaryModel α) (s : ℝ) :
    ∑ x : α, M.tiltedWeight s x = M.petzChernoffCoefficient s := by
  rfl

/-- The normalized tilted distribution associated with a nonzero Chernoff
coefficient. -/
noncomputable def tiltedDistribution (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.petzChernoffCoefficient s ≠ 0) : ClassicalDistribution α :=
  { prob := fun x => M.tiltedWeight s x / M.petzChernoffCoefficient s
    sum_eq_one := by
      rw [← Finset.sum_div]
      exact div_self hZ }

@[simp]
theorem tiltedDistribution_prob (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.petzChernoffCoefficient s ≠ 0) (x : α) :
    (M.tiltedDistribution s hZ).prob x =
      M.tiltedWeight s x / M.petzChernoffCoefficient s := rfl

/-- Away from the endpoint `s = 0`, the tilted distribution is supported on
the `p` support. -/
theorem tiltedDistribution_supportedBy_p
    (M : ClassicalBinaryModel α) {s : ℝ} (hs : s ≠ 0)
    (hZ : M.petzChernoffCoefficient s ≠ 0) :
    (M.tiltedDistribution s hZ).SupportedBy M.p := by
  intro x hx
  rw [tiltedDistribution_prob] at hx
  have hweight : M.tiltedWeight s x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  unfold tiltedWeight at hweight
  have hp_pow : M.p x ^ s ≠ 0 := by
    intro hp0
    simp [hp0] at hweight
  exact fun hp0 => hp_pow ((NNReal.rpow_eq_zero hs).mpr hp0)

/-- Away from the endpoint `s = 1`, the tilted distribution is supported on
the `q` support. -/
theorem tiltedDistribution_supportedBy_q
    (M : ClassicalBinaryModel α) {s : ℝ} (hs : 1 - s ≠ 0)
    (hZ : M.petzChernoffCoefficient s ≠ 0) :
    (M.tiltedDistribution s hZ).SupportedBy M.q := by
  intro x hx
  rw [tiltedDistribution_prob] at hx
  have hweight : M.tiltedWeight s x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  unfold tiltedWeight at hweight
  have hq_pow : M.q x ^ (1 - s) ≠ 0 := by
    intro hq0
    simp [hq0] at hweight
  exact fun hq0 => hq_pow ((NNReal.rpow_eq_zero hs).mpr hq0)

/-- The finite common support of the two classical distributions.  The direct
classical Chernoff variational proof works on this support so all logarithms
and real powers have strictly positive bases. -/
noncomputable def commonSupport (M : ClassicalBinaryModel α) : Type u :=
  {x : α // M.p x ≠ 0 ∧ M.q x ≠ 0}

noncomputable instance commonSupportFintype
    (M : ClassicalBinaryModel α) : Fintype M.commonSupport := by
  unfold commonSupport
  infer_instance

/-- The common-support Chernoff partition function, using the repository's
orientation `p^s q^(1-s)` from `petzChernoffCoefficient`. -/
noncomputable def chernoffPartition (M : ClassicalBinaryModel α) (s : ℝ) : ℝ :=
  ∑ x : M.commonSupport,
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s))

/-- Nonnegative-real version of the common-support Chernoff partition.  This is
used to normalize the tilted distribution without endpoint support artifacts
from the full alphabet. -/
noncomputable def chernoffPartitionNNReal (M : ClassicalBinaryModel α) (s : ℝ) : ℝ≥0 :=
  ∑ x : M.commonSupport, M.p x.1 ^ s * M.q x.1 ^ (1 - s)

@[simp]
theorem chernoffPartitionNNReal_coe (M : ClassicalBinaryModel α) (s : ℝ) :
    (M.chernoffPartitionNNReal s : ℝ) = M.chernoffPartition s := by
  simp [chernoffPartitionNNReal, chernoffPartition]

/-- A nonempty common support makes the common-support partition strictly
positive for every real Chernoff parameter. -/
theorem chernoffPartitionNNReal_pos_of_commonSupport_nonempty
    (M : ClassicalBinaryModel α) (h : Nonempty M.commonSupport) (s : ℝ) :
    0 < M.chernoffPartitionNNReal s := by
  classical
  rcases h with ⟨x⟩
  unfold chernoffPartitionNNReal
  apply Finset.sum_pos'
  · intro y _hy
    positivity
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    have hp : 0 < M.p x.1 := by
      exact lt_of_le_of_ne (by positivity) (Ne.symm x.2.1)
    have hq : 0 < M.q x.1 := by
      exact lt_of_le_of_ne (by positivity) (Ne.symm x.2.2)
    positivity

/-- On the open interval `(0,1)`, the common-support partition agrees with
the full classical Petz/Chernoff coefficient.  Terms outside common support
vanish because both exponents are nonzero there. -/
theorem chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
    (M : ClassicalBinaryModel α) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    M.chernoffPartitionNNReal s = M.petzChernoffCoefficient s := by
  classical
  let f : α → ℝ≥0 := fun x => M.p x ^ s * M.q x ^ (1 - s)
  have hfilter :
      (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0, f x) = M.chernoffPartitionNNReal s := by
    unfold chernoffPartitionNNReal commonSupport f
    exact Finset.sum_bij
      (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
      (by intro x hx; simp)
      (by intro a _ b _ h; simpa using h)
      (by
        intro y _hy
        refine ⟨y.1, ?_, rfl⟩
        simp [y.2])
      (by intro x hx; rfl)
  have hfull_filter :
      (∑ x : α, f x) =
        ∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0, f x := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0) (f := f)]
    have hzero :
        (∑ x with ¬(M.p x ≠ 0 ∧ M.q x ≠ 0), f x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxnot : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0) := (Finset.mem_filter.mp hx).2
      unfold f
      by_cases hp : M.p x = 0
      · simp [hp, NNReal.zero_rpow hs0.ne']
      · have hq : M.q x = 0 := by
          by_contra hq
          exact hxnot ⟨hp, hq⟩
        have h1s : 1 - s ≠ 0 := by linarith
        simp [hq, NNReal.zero_rpow h1s]
    rw [hzero, add_zero]
  rw [← hfilter, ← hfull_filter]
  rfl

/-- A positive classical Petz/Chernoff coefficient gives the finite real-log
form of the fixed-`s` exponent. -/
theorem chernoffExponent_eq_coe_neg_log_of_petzChernoffCoefficient_pos
    (M : ClassicalBinaryModel α) (s : ℝ)
    (h : 0 < M.petzChernoffCoefficient s) :
    M.chernoffExponent s =
      ((- Real.log (M.petzChernoffCoefficient s : ℝ) : ℝ) : EReal) := by
  have h0 : (M.petzChernoffCoefficient s : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast h.ne'
  have htop : ((M.petzChernoffCoefficient s : ℝ≥0∞) ≠ ⊤) := by
    simp
  simp [chernoffExponent, ENNReal.log_pos_real h0 htop, EReal.coe_neg]

/-- Interior common-support negative log partitions are bounded by the public
classical Chernoff distance. -/
theorem neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
    (M : ClassicalBinaryModel α) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    ((-Real.log (M.chernoffPartition s) : ℝ) : EReal) ≤ M.chernoffDistance := by
  have hpart :
      M.chernoffPartitionNNReal s = M.petzChernoffCoefficient s :=
    chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
      (M := M) hs0 hs1
  have hpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hpetzpos : 0 < M.petzChernoffCoefficient s := by
    rwa [← hpart]
  have hcoeff :
      M.chernoffExponent s =
        ((-Real.log (M.chernoffPartition s) : ℝ) : EReal) := by
    rw [chernoffExponent_eq_coe_neg_log_of_petzChernoffCoefficient_pos
      (M := M) (s := s) hpetzpos]
    rw [← hpart]
    simp
  rw [← hcoeff]
  exact le_iSup (fun t : Set.Icc (0 : ℝ) 1 => M.chernoffExponent t.1)
    ⟨s, le_of_lt hs0, le_of_lt hs1⟩

/-- Finite classical Chernoff distance excludes disjoint support. -/
theorem commonSupport_nonempty_of_chernoffDistance_ne_top
    (M : ClassicalBinaryModel α) (hfinite : M.chernoffDistance ≠ ⊤) :
    Nonempty M.commonSupport := by
  classical
  by_contra hnone
  have hcoeff : M.petzChernoffCoefficient (1 / 2 : ℝ) = 0 := by
    unfold petzChernoffCoefficient
    apply Finset.sum_eq_zero
    intro x _hx
    have hnot : ¬ (M.p x ≠ 0 ∧ M.q x ≠ 0) := by
      intro h
      exact hnone ⟨⟨x, h⟩⟩
    have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have honehalf : (1 - (1 / 2 : ℝ)) ≠ 0 := by norm_num
    by_cases hp : M.p x = 0
    · rw [hp, NNReal.zero_rpow hhalf, zero_mul]
    · have hq : M.q x = 0 := by
        by_contra hq
        exact hnot ⟨hp, hq⟩
      rw [hq, NNReal.zero_rpow honehalf, mul_zero]
  have hexp : M.chernoffExponent (1 / 2 : ℝ) = ⊤ := by
    unfold chernoffExponent
    rw [hcoeff]
    simp
  have hle : (⊤ : EReal) ≤ M.chernoffDistance := by
    rw [← hexp]
    exact le_iSup
      (fun t : Set.Icc (0 : ℝ) 1 => M.chernoffExponent t.1)
      ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  exact hfinite (le_antisymm le_top hle)

/-- Finite classical Chernoff distance gives a nonzero common-support
partition at every parameter. -/
theorem chernoffPartitionNNReal_ne_zero_of_chernoffDistance_ne_top
    (M : ClassicalBinaryModel α) (hfinite : M.chernoffDistance ≠ ⊤) (s : ℝ) :
    M.chernoffPartitionNNReal s ≠ 0 :=
  ne_of_gt
    (chernoffPartitionNNReal_pos_of_commonSupport_nonempty (M := M)
      (commonSupport_nonempty_of_chernoffDistance_ne_top (M := M) hfinite) s)

/-- Real log-partition for the common-support classical Chernoff function. -/
noncomputable def chernoffLogPartition (M : ClassicalBinaryModel α) (s : ℝ) : ℝ :=
  Real.log (M.chernoffPartition s)

/-- Derivative of the common-support Chernoff partition. -/
noncomputable def chernoffPartitionDeriv (M : ClassicalBinaryModel α) (s : ℝ) : ℝ :=
  ∑ x : M.commonSupport,
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s)) *
      (Real.log (M.p x.1 : ℝ) - Real.log (M.q x.1 : ℝ))

/-- The tilted distribution supported on the common support, normalized by the
common-support partition. -/
noncomputable def commonSupportTiltedDistribution
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) : ClassicalDistribution α :=
  { prob := fun x =>
      if M.p x ≠ 0 ∧ M.q x ≠ 0 then
        M.p x ^ s * M.q x ^ (1 - s) / M.chernoffPartitionNNReal s
      else 0
    sum_eq_one := by
      classical
      rw [← Finset.sum_filter
        (s := Finset.univ)
        (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0)
        (f := fun x : α => M.p x ^ s * M.q x ^ (1 - s) /
          M.chernoffPartitionNNReal s)]
      rw [← Finset.sum_div]
      have hsum :
          (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0,
            M.p x ^ s * M.q x ^ (1 - s)) = M.chernoffPartitionNNReal s := by
        unfold chernoffPartitionNNReal commonSupport
        exact Finset.sum_bij (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
          (by intro x hx; simp)
          (by intro a _ b _ h; simpa using h)
          (by
            intro y _hy
            refine ⟨y.1, ?_, rfl⟩
            simp [y.2])
          (by intro x hx; rfl)
      rw [hsum]
      exact div_self hZ }

@[simp]
theorem commonSupportTiltedDistribution_prob
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) (x : α) :
    (M.commonSupportTiltedDistribution s hZ).prob x =
      if M.p x ≠ 0 ∧ M.q x ≠ 0 then
        M.p x ^ s * M.q x ^ (1 - s) / M.chernoffPartitionNNReal s
      else 0 := rfl

theorem commonSupportTiltedDistribution_prob_toReal_of_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : M.p x ≠ 0 ∧ M.q x ≠ 0) :
    ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) =
      ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
        M.chernoffPartition s := by
  have hZr : (M.chernoffPartitionNNReal s : ℝ) = M.chernoffPartition s := by
    simp
  simp [commonSupportTiltedDistribution_prob, hx, hZr]

theorem commonSupportTiltedDistribution_prob_toReal_of_not_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0)) :
    ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) = 0 := by
  simp [commonSupportTiltedDistribution_prob, hx]

private theorem sum_div_mul_sub_const_eq {ι : Type u} [Fintype ι]
    (W A : ι → ℝ) {Z c : ℝ} (hZ : Z ≠ 0) (hW : (∑ x, W x) = Z) :
    (∑ x, (W x / Z) * (c * A x - Real.log Z)) =
      c * (∑ x, W x * A x) / Z - Real.log Z := by
  calc
    (∑ x, (W x / Z) * (c * A x - Real.log Z))
        = (∑ x, ((c * (W x * A x)) / Z - (Real.log Z * W x) / Z)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          field_simp [hZ]
    _ = (∑ x, (c * (W x * A x)) / Z) -
        (∑ x, (Real.log Z * W x) / Z) := by
          rw [Finset.sum_sub_distrib]
    _ = c * (∑ x, W x * A x) / Z -
        Real.log Z * (∑ x, W x) / Z := by
          congr 2
          · rw [← Finset.sum_div]
            congr 1
            rw [Finset.mul_sum]
          · rw [← Finset.sum_div]
            congr 1
            rw [Finset.mul_sum]
    _ = c * (∑ x, W x * A x) / Z - Real.log Z := by
          rw [hW]
          field_simp [hZ]

/-- Pointwise KL summand of the common-support tilted distribution against
the `p` side. -/
theorem relativeEntropySummandReal_commonSupportTilted_p_of_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : M.p x ≠ 0 ∧ M.q x ≠ 0) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x =
      (((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        ((1 - s) * (Real.log (M.q x : ℝ) - Real.log (M.p x : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
  classical
  have hp : 0 < (M.p x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.1)
  have hq : 0 < (M.q x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.2)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) =
      ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
        M.chernoffPartition s :=
    commonSupportTiltedDistribution_prob_toReal_of_mem (M := M) (s := s) hZ hx
  have hrpos :
      0 < ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) := by
    rw [hr]
    positivity
  have hrne_nn : (M.commonSupportTiltedDistribution s hZ).prob x ≠ 0 := by
    exact_mod_cast hrpos.ne'
  rw [relativeEntropySummandReal, if_neg hrne_nn]
  rw [hr]
  congr 1
  simp [pDistribution]
  rw [Real.log_div
      (div_ne_zero
        (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
          (Real.rpow_pos_of_pos hq (1 - s)).ne')
        hZpos.ne')
      hp.ne',
    Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne') hZpos.ne',
    Real.log_mul (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne',
    Real.log_rpow hp, Real.log_rpow hq]
  ring

/-- Pointwise KL summand of the common-support tilted distribution against
the `q` side. -/
theorem relativeEntropySummandReal_commonSupportTilted_q_of_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : M.p x ≠ 0 ∧ M.q x ≠ 0) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x =
      (((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        (s * (Real.log (M.p x : ℝ) - Real.log (M.q x : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
  classical
  have hp : 0 < (M.p x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.1)
  have hq : 0 < (M.q x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.2)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) =
      ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
        M.chernoffPartition s :=
    commonSupportTiltedDistribution_prob_toReal_of_mem (M := M) (s := s) hZ hx
  have hrpos :
      0 < ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) := by
    rw [hr]
    positivity
  have hrne_nn : (M.commonSupportTiltedDistribution s hZ).prob x ≠ 0 := by
    exact_mod_cast hrpos.ne'
  rw [relativeEntropySummandReal, if_neg hrne_nn]
  rw [hr]
  congr 1
  simp [qDistribution]
  rw [Real.log_div
      (div_ne_zero
        (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
          (Real.rpow_pos_of_pos hq (1 - s)).ne')
        hZpos.ne')
      hq.ne',
    Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne') hZpos.ne',
    Real.log_mul (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne',
    Real.log_rpow hp, Real.log_rpow hq]
  ring

/-- Outside the common support, the `p` KL summand of the common-support tilted
distribution is zero. -/
theorem relativeEntropySummandReal_commonSupportTilted_p_of_not_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0)) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x = 0 := by
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) = 0 :=
    commonSupportTiltedDistribution_prob_toReal_of_not_mem (M := M) (s := s) hZ hx
  have hrnn : (M.commonSupportTiltedDistribution s hZ).prob x = 0 := by
    exact_mod_cast hr
  rw [relativeEntropySummandReal, if_pos hrnn]

/-- Outside the common support, the `q` KL summand of the common-support tilted
distribution is zero. -/
theorem relativeEntropySummandReal_commonSupportTilted_q_of_not_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0)) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x = 0 := by
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) = 0 :=
    commonSupportTiltedDistribution_prob_toReal_of_not_mem (M := M) (s := s) hZ hx
  have hrnn : (M.commonSupportTiltedDistribution s hZ).prob x = 0 := by
    exact_mod_cast hr
  rw [relativeEntropySummandReal, if_pos hrnn]

/-- Common-support sum algebra for the tilted KL against `p`. -/
theorem commonSupportTilted_relativeEntropy_p_sum_algebra
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (∑ x : M.commonSupport,
      (((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        ((1 - s) * (Real.log (M.q x.1 : ℝ) - Real.log (M.p x.1 : ℝ)) -
          Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  unfold chernoffPartition chernoffPartitionDeriv
  let W : M.commonSupport → ℝ := fun x =>
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s))
  let A : M.commonSupport → ℝ := fun x =>
    Real.log (M.q x.1 : ℝ) - Real.log (M.p x.1 : ℝ)
  have halg := sum_div_mul_sub_const_eq
    (W := W) (A := A) (Z := M.chernoffPartition s) (c := 1 - s)
    hZpos.ne' (by simp [W, chernoffPartition])
  have hderiv :
      (∑ x : M.commonSupport, W x * A x) = -M.chernoffPartitionDeriv s := by
    unfold W A chernoffPartitionDeriv
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  change
    (∑ x, (W x / M.chernoffPartition s) *
      ((1 - s) * A x - Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s
  rw [halg, hderiv]
  ring

/-- Common-support sum algebra for the tilted KL against `q`. -/
theorem commonSupportTilted_relativeEntropy_q_sum_algebra
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (∑ x : M.commonSupport,
      (((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        (s * (Real.log (M.p x.1 : ℝ) - Real.log (M.q x.1 : ℝ)) -
          Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  unfold chernoffPartition chernoffPartitionDeriv
  let W : M.commonSupport → ℝ := fun x =>
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s))
  let A : M.commonSupport → ℝ := fun x =>
    Real.log (M.p x.1 : ℝ) - Real.log (M.q x.1 : ℝ)
  have halg := sum_div_mul_sub_const_eq
    (W := W) (A := A) (Z := M.chernoffPartition s) (c := s)
    hZpos.ne' (by simp [W, chernoffPartition])
  have hderiv :
      (∑ x : M.commonSupport, W x * A x) = M.chernoffPartitionDeriv s := by
    unfold W A chernoffPartitionDeriv
    rfl
  change
    (∑ x, (W x / M.chernoffPartition s) *
      (s * A x - Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s
  rw [halg, hderiv]
  ring

/-- KL identity for the common-support tilted distribution against `p`. -/
theorem relativeEntropyReal_commonSupportTilted_p
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    relativeEntropyReal (M.commonSupportTiltedDistribution s hZ) M.pDistribution =
      -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  classical
  unfold relativeEntropyReal
  have hrestrict :
      (∑ x, relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x) =
        Finset.sum Finset.univ (fun x : α =>
          if M.p x ≠ 0 ∧ M.q x ≠ 0 then
            relativeEntropySummandReal
              (M.commonSupportTiltedDistribution s hZ) M.pDistribution x
          else 0) := by
    apply Finset.sum_congr rfl
    intro x _hxmem
    by_cases hx : M.p x ≠ 0 ∧ M.q x ≠ 0
    · simp [hx]
    · rw [if_neg hx]
      rw [relativeEntropySummandReal_commonSupportTilted_p_of_not_mem (M := M) (s := s) hZ hx]
  rw [hrestrict]
  rw [← Finset.sum_filter
    (s := Finset.univ)
    (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0)
    (f := fun x : α => relativeEntropySummandReal
      (M.commonSupportTiltedDistribution s hZ) M.pDistribution x)]
  calc
    (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0,
      relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x)
        =
      ∑ y : M.commonSupport,
        relativeEntropySummandReal
          (M.commonSupportTiltedDistribution s hZ) M.pDistribution y.1 := by
          unfold commonSupport
          exact Finset.sum_bij (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
            (by intro x hx; simp)
            (by intro a _ b _ h; simpa using h)
            (by
              intro y _hy
              refine ⟨y.1, ?_, rfl⟩
              simp [y.2])
            (by intro x hx; rfl)
    _ =
      ∑ y : M.commonSupport,
        (((M.p y.1 : ℝ) ^ s) * ((M.q y.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        ((1 - s) * (Real.log (M.q y.1 : ℝ) - Real.log (M.p y.1 : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
          apply Finset.sum_congr rfl
          intro y _hy
          exact relativeEntropySummandReal_commonSupportTilted_p_of_mem
            (M := M) (s := s) hZ y.2
    _ = -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s :=
          commonSupportTilted_relativeEntropy_p_sum_algebra (M := M) (s := s) hZ

/-- KL identity for the common-support tilted distribution against `q`. -/
theorem relativeEntropyReal_commonSupportTilted_q
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    relativeEntropyReal (M.commonSupportTiltedDistribution s hZ) M.qDistribution =
      -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  classical
  unfold relativeEntropyReal
  have hrestrict :
      (∑ x, relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x) =
        Finset.sum Finset.univ (fun x : α =>
          if M.p x ≠ 0 ∧ M.q x ≠ 0 then
            relativeEntropySummandReal
              (M.commonSupportTiltedDistribution s hZ) M.qDistribution x
          else 0) := by
    apply Finset.sum_congr rfl
    intro x _hxmem
    by_cases hx : M.p x ≠ 0 ∧ M.q x ≠ 0
    · simp [hx]
    · rw [if_neg hx]
      rw [relativeEntropySummandReal_commonSupportTilted_q_of_not_mem (M := M) (s := s) hZ hx]
  rw [hrestrict]
  rw [← Finset.sum_filter
    (s := Finset.univ)
    (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0)
    (f := fun x : α => relativeEntropySummandReal
      (M.commonSupportTiltedDistribution s hZ) M.qDistribution x)]
  calc
    (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0,
      relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x)
        =
      ∑ y : M.commonSupport,
        relativeEntropySummandReal
          (M.commonSupportTiltedDistribution s hZ) M.qDistribution y.1 := by
          unfold commonSupport
          exact Finset.sum_bij (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
            (by intro x hx; simp)
            (by intro a _ b _ h; simpa using h)
            (by
              intro y _hy
              refine ⟨y.1, ?_, rfl⟩
              simp [y.2])
            (by intro x hx; rfl)
    _ =
      ∑ y : M.commonSupport,
        (((M.p y.1 : ℝ) ^ s) * ((M.q y.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        (s * (Real.log (M.p y.1 : ℝ) - Real.log (M.q y.1 : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
          apply Finset.sum_congr rfl
          intro y _hy
          exact relativeEntropySummandReal_commonSupportTilted_q_of_mem
            (M := M) (s := s) hZ y.2
    _ = -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s :=
          commonSupportTilted_relativeEntropy_q_sum_algebra (M := M) (s := s) hZ

/-- The common-support tilted distribution is supported on `p`. -/
theorem commonSupportTiltedDistribution_supportedBy_p
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (M.commonSupportTiltedDistribution s hZ).SupportedBy M.p := by
  intro x hx
  rw [commonSupportTiltedDistribution_prob] at hx
  by_contra hp0
  simp [hp0] at hx

/-- The common-support tilted distribution is supported on `q`. -/
theorem commonSupportTiltedDistribution_supportedBy_q
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (M.commonSupportTiltedDistribution s hZ).SupportedBy M.q := by
  intro x hx
  rw [commonSupportTiltedDistribution_prob] at hx
  by_contra hq0
  simp [hq0] at hx

/-- The common-support partition is differentiable, with derivative determined
by the orientation `p^s q^(1-s)`. -/
theorem hasDerivAt_chernoffPartition
    (M : ClassicalBinaryModel α) (s : ℝ) :
    HasDerivAt (fun t : ℝ => M.chernoffPartition t)
      (M.chernoffPartitionDeriv s) s := by
  unfold chernoffPartition chernoffPartitionDeriv
  refine HasDerivAt.fun_sum (u := Finset.univ) ?_
  intro i _hi
  let a : ℝ := (M.p i.1 : ℝ)
  let b : ℝ := (M.q i.1 : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (pos_iff_ne_zero.mpr i.2.1)
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast (pos_iff_ne_zero.mpr i.2.2)
  have hpowa :
      HasDerivAt (fun t : ℝ => a ^ t) (Real.log a * a ^ s) s := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
    simpa using hid.const_rpow ha
  have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    simpa using (hasDerivAt_const (x := s) (c := (1 : ℝ))).sub (hasDerivAt_id s)
  have hpowb :
      HasDerivAt (fun t : ℝ => b ^ (1 - t))
        (-(Real.log b * b ^ (1 - s))) s := by
    simpa using hlin.const_rpow hb
  have hmul := hpowa.mul hpowb
  change HasDerivAt (fun t : ℝ => a ^ t * b ^ (1 - t))
    (a ^ s * b ^ (1 - s) * (Real.log a - Real.log b)) s
  convert hmul using 1
  ring

/-- The common-support Chernoff partition is continuous. -/
theorem continuous_chernoffPartition (M : ClassicalBinaryModel α) :
    Continuous (fun s : ℝ => M.chernoffPartition s) := by
  unfold chernoffPartition
  refine continuous_finsetSum Finset.univ ?_
  intro i _hi
  let a : ℝ := (M.p i.1 : ℝ)
  let b : ℝ := (M.q i.1 : ℝ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast i.2.1
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast i.2.2
  exact (Real.continuous_const_rpow ha).mul
    ((Real.continuous_const_rpow hb).comp (continuous_const.sub continuous_id))

/-- The common-support Chernoff partition attains a minimum on `[0,1]`. -/
theorem exists_isMinOn_chernoffPartition_Icc
    (M : ClassicalBinaryModel α) :
    ∃ sStar : Set.Icc (0 : ℝ) 1,
      IsMinOn (fun s : Set.Icc (0 : ℝ) 1 => M.chernoffPartition s.1)
        Set.univ sStar := by
  have hcont : ContinuousOn (fun s : Set.Icc (0 : ℝ) 1 =>
      M.chernoffPartition s.1) Set.univ :=
    ((continuous_chernoffPartition M).comp continuous_subtype_val).continuousOn
  obtain ⟨sStar, _hmem, hmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty) hcont
  exact ⟨sStar, hmin⟩

/-- Real-valued version of the common-support partition minimizer on `[0,1]`. -/
theorem exists_isMinOn_chernoffPartition_Icc_real
    (M : ClassicalBinaryModel α) :
    ∃ sStar ∈ Set.Icc (0 : ℝ) 1,
      IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar := by
  have hcont : ContinuousOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) :=
    (continuous_chernoffPartition M).continuousOn
  exact isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hcont

/-- At a left-endpoint minimum of the common-support partition on `[0,1]`,
the one-sided derivative is nonnegative. -/
theorem chernoffPartitionDeriv_nonneg_at_left_min
    (M : ClassicalBinaryModel α) {sStar : ℝ}
    (hs : sStar = 0)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar) :
    0 ≤ M.chernoffPartitionDeriv sStar := by
  subst sStar
  have hdir : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    have hseg : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [segment_eq_Icc zero_le_one]
    simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg :
      0 ≤
        (ContinuousLinearMap.toSpanSingleton ℝ (M.chernoffPartitionDeriv 0)) (1 : ℝ) :=
    hmin.localize.hasFDerivWithinAt_nonneg
      ((hasDerivAt_chernoffPartition M 0).hasDerivWithinAt) hdir
  simpa [ContinuousLinearMap.toSpanSingleton_apply] using hnonneg

/-- At a right-endpoint minimum of the common-support partition on `[0,1]`,
the one-sided derivative is nonpositive. -/
theorem chernoffPartitionDeriv_nonpos_at_right_min
    (M : ClassicalBinaryModel α) {sStar : ℝ}
    (hs : sStar = 1)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar) :
    M.chernoffPartitionDeriv sStar ≤ 0 := by
  subst sStar
  have hdir : (-1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 1 := by
    simpa using
      (sub_mem_posTangentConeAt_of_segment_subset
        (x := (1 : ℝ)) (y := (0 : ℝ))
        (by rw [segment_symm, segment_eq_Icc zero_le_one]))
  have hnonneg :
      0 ≤
        (ContinuousLinearMap.toSpanSingleton ℝ (M.chernoffPartitionDeriv 1)) (-1 : ℝ) :=
    hmin.localize.hasFDerivWithinAt_nonneg
      ((hasDerivAt_chernoffPartition M 1).hasDerivWithinAt) hdir
  simpa [ContinuousLinearMap.toSpanSingleton_apply] using hnonneg

/-- At an interior minimum of the common-support partition on `[0,1]`,
the derivative vanishes. -/
theorem chernoffPartitionDeriv_eq_zero_at_interior_min
    (M : ClassicalBinaryModel α) {sStar : ℝ}
    (hs0 : 0 < sStar) (hs1 : sStar < 1)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar) :
    M.chernoffPartitionDeriv sStar = 0 := by
  have hnhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 sStar :=
    Icc_mem_nhds hs0 hs1
  exact hmin.isLocalMin hnhds |>.hasDerivAt_eq_zero
    (hasDerivAt_chernoffPartition M sStar)

/-- The left endpoint common-support log partition is bounded by the public
Chernoff distance by approaching it from the open interval. -/
theorem neg_log_commonPartition_left_le_chernoffDistance
    (M : ClassicalBinaryModel α)
    (hZ : M.chernoffPartitionNNReal 0 ≠ 0) :
    ((-Real.log (M.chernoffPartition 0) : ℝ) : EReal) ≤
      M.chernoffDistance := by
  classical
  let sseq : Nat → ℝ := fun n => (((n + 2 : Nat) : ℝ)⁻¹)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal 0 := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition 0 := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hsseq_tend : Tendsto sseq atTop (𝓝 (0 : ℝ)) := by
    simpa [sseq, Function.comp_def, one_div, Nat.cast_add,
      add_comm, add_left_comm, add_assoc] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
  have hpart_tend :
      Tendsto (fun n : Nat => M.chernoffPartition (sseq n))
        atTop (𝓝 (M.chernoffPartition 0)) :=
    (continuous_chernoffPartition M).continuousAt.tendsto.comp hsseq_tend
  have hpart_pos_eventual :
      ∀ᶠ n in atTop, 0 < M.chernoffPartition (sseq n) :=
    hpart_tend.eventually (lt_mem_nhds hZpos)
  have hineq_eventual :
      ∀ᶠ n in atTop,
        ((-Real.log (M.chernoffPartition (sseq n)) : ℝ) : EReal) ≤
          M.chernoffDistance := by
    filter_upwards [hpart_pos_eventual] with n hpos
    have hs0 : 0 < sseq n := by
      have hpos_nat : (0 : ℝ) < (n + 2 : Nat) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      exact inv_pos.mpr hpos_nat
    have hs1 : sseq n < 1 := by
      have hlt : (1 : ℝ) < (n + 2 : Nat) := by
        have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        norm_num
        linarith
      simpa [sseq] using inv_lt_one_of_one_lt₀ hlt
    have hZseq : M.chernoffPartitionNNReal (sseq n) ≠ 0 := by
      have hpos_nn : 0 < M.chernoffPartitionNNReal (sseq n) := by
        rw [← chernoffPartitionNNReal_coe] at hpos
        exact_mod_cast hpos
      exact ne_of_gt hpos_nn
    exact neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
      (M := M) hs0 hs1 hZseq
  have hlog_tend :
      Tendsto (fun n : Nat => -Real.log (M.chernoffPartition (sseq n)))
        atTop (𝓝 (-Real.log (M.chernoffPartition 0))) := by
    have hcont :
        ContinuousAt (fun x : ℝ => -Real.log x) (M.chernoffPartition 0) :=
      (Real.continuousAt_log hZpos.ne').neg
    exact hcont.tendsto.comp hpart_tend
  exact le_of_tendsto (EReal.tendsto_coe.mpr hlog_tend) hineq_eventual

/-- The right endpoint common-support log partition is bounded by the public
Chernoff distance by approaching it from the open interval. -/
theorem neg_log_commonPartition_right_le_chernoffDistance
    (M : ClassicalBinaryModel α)
    (hZ : M.chernoffPartitionNNReal 1 ≠ 0) :
    ((-Real.log (M.chernoffPartition 1) : ℝ) : EReal) ≤
      M.chernoffDistance := by
  classical
  let sseq : Nat → ℝ := fun n => (1 : ℝ) - (((n + 2 : Nat) : ℝ)⁻¹)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal 1 := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition 1 := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hinv_tend :
      Tendsto (fun n : Nat => (((n + 2 : Nat) : ℝ)⁻¹))
        atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def, one_div, Nat.cast_add,
      add_comm, add_left_comm, add_assoc] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
  have hsseq_tend : Tendsto sseq atTop (𝓝 (1 : ℝ)) := by
    simpa [sseq] using tendsto_const_nhds.sub hinv_tend
  have hpart_tend :
      Tendsto (fun n : Nat => M.chernoffPartition (sseq n))
        atTop (𝓝 (M.chernoffPartition 1)) :=
    (continuous_chernoffPartition M).continuousAt.tendsto.comp hsseq_tend
  have hpart_pos_eventual :
      ∀ᶠ n in atTop, 0 < M.chernoffPartition (sseq n) :=
    hpart_tend.eventually (lt_mem_nhds hZpos)
  have hineq_eventual :
      ∀ᶠ n in atTop,
        ((-Real.log (M.chernoffPartition (sseq n)) : ℝ) : EReal) ≤
          M.chernoffDistance := by
    filter_upwards [hpart_pos_eventual] with n hpos
    have hinv_pos : 0 < (((n + 2 : Nat) : ℝ)⁻¹) := by
      have hpos_nat : (0 : ℝ) < (n + 2 : Nat) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      exact inv_pos.mpr hpos_nat
    have hinv_lt_one : (((n + 2 : Nat) : ℝ)⁻¹) < 1 := by
      have hlt : (1 : ℝ) < (n + 2 : Nat) := by
        have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        norm_num
        linarith
      exact inv_lt_one_of_one_lt₀ hlt
    have hs0 : 0 < sseq n := by
      dsimp [sseq]
      linarith
    have hs1 : sseq n < 1 := by
      dsimp [sseq]
      linarith
    have hZseq : M.chernoffPartitionNNReal (sseq n) ≠ 0 := by
      have hpos_nn : 0 < M.chernoffPartitionNNReal (sseq n) := by
        rw [← chernoffPartitionNNReal_coe] at hpos
        exact_mod_cast hpos
      exact ne_of_gt hpos_nn
    exact neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
      (M := M) hs0 hs1 hZseq
  have hlog_tend :
      Tendsto (fun n : Nat => -Real.log (M.chernoffPartition (sseq n)))
        atTop (𝓝 (-Real.log (M.chernoffPartition 1))) := by
    have hcont :
        ContinuousAt (fun x : ℝ => -Real.log x) (M.chernoffPartition 1) :=
      (Real.continuousAt_log hZpos.ne').neg
    exact hcont.tendsto.comp hpart_tend
  exact le_of_tendsto (EReal.tendsto_coe.mpr hlog_tend) hineq_eventual

/-- Any nonzero common-support log partition on `[0,1]` is bounded by the
public classical Chernoff distance.  Endpoint cases are obtained as limits from
the open interval because the full Petz coefficient has endpoint artifacts
from `0^0`. -/
theorem neg_log_commonPartition_le_chernoffDistance
    (M : ClassicalBinaryModel α) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    ((-Real.log (M.chernoffPartition s) : ℝ) : EReal) ≤
      M.chernoffDistance := by
  rcases lt_or_eq_of_le hs.1 with hs0 | hs0eq
  · rcases lt_or_eq_of_le hs.2 with hs1 | hs1eq
    · exact neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
        (M := M) hs0 hs1 hZ
    · subst s
      exact neg_log_commonPartition_right_le_chernoffDistance (M := M) hZ
  · subst s
    exact neg_log_commonPartition_left_le_chernoffDistance (M := M) hZ

/-- IID tensor powers multiply classical Petz/Chernoff coefficients. -/
theorem tensorPower_petzChernoffCoefficient
    (M : ClassicalBinaryModel α) (s : ℝ) (n : Nat) :
    (M.tensorPower n).petzChernoffCoefficient s =
      M.petzChernoffCoefficient s ^ n := by
  induction n with
  | zero =>
      change
        (∑ _x : PUnit, (1 : ℝ≥0) ^ s * (1 : ℝ≥0) ^ (1 - s)) =
          M.petzChernoffCoefficient s ^ 0
      simp
  | succ n ih =>
      change
        (∑ x : Prod α (TensorPower α n),
            ((M.p x.1 * (M.tensorPower n).p x.2) ^ s) *
              ((M.q x.1 * (M.tensorPower n).q x.2) ^ (1 - s))) =
          M.petzChernoffCoefficient s ^ (n + 1)
      rw [Fintype.sum_prod_type]
      calc
        (∑ x : α, ∑ xs : TensorPower α n,
            ((M.p x * (M.tensorPower n).p xs) ^ s) *
              ((M.q x * (M.tensorPower n).q xs) ^ (1 - s)))
            = ∑ x : α, ∑ xs : TensorPower α n,
                (M.p x ^ s * M.q x ^ (1 - s)) *
                  ((M.tensorPower n).p xs ^ s *
                    (M.tensorPower n).q xs ^ (1 - s)) := by
              simp [NNReal.mul_rpow, mul_assoc, mul_left_comm]
        _ = ∑ x : α,
              (M.p x ^ s * M.q x ^ (1 - s)) *
                (∑ xs : TensorPower α n,
                  (M.tensorPower n).p xs ^ s *
                    (M.tensorPower n).q xs ^ (1 - s)) := by
              simp [Finset.mul_sum]
        _ =
            (∑ x : α, M.p x ^ s * M.q x ^ (1 - s)) *
              (∑ xs : TensorPower α n,
                (M.tensorPower n).p xs ^ s *
                  (M.tensorPower n).q xs ^ (1 - s)) := by
              rw [Finset.sum_mul]
        _ = M.petzChernoffCoefficient s * (M.tensorPower n).petzChernoffCoefficient s := by
              rfl
        _ = M.petzChernoffCoefficient s * M.petzChernoffCoefficient s ^ n := by
              rw [ih]
        _ = M.petzChernoffCoefficient s ^ (n + 1) := by
              rw [pow_succ]
              rw [mul_comm]

variable [DecidableEq α]

/-- Product probability of a tensor word, expressed over the canonical
`Fin n -> α` tensor-power equivalence. -/
def tensorPowerProbabilityP (M : ClassicalBinaryModel α) (n : Nat)
    (x : TensorPower α n) : ℝ≥0 :=
  ∏ i : Fin n, M.p (tensorPowerEquiv (a := α) n x i)

/-- Product `q`-probability of a tensor word, expressed over the canonical
`Fin n -> α` tensor-power equivalence. -/
def tensorPowerProbabilityQ (M : ClassicalBinaryModel α) (n : Nat)
    (x : TensorPower α n) : ℝ≥0 :=
  ∏ i : Fin n, M.q (tensorPowerEquiv (a := α) n x i)

omit [DecidableEq α] in
@[simp]
theorem tensorPower_p_eq_tensorPowerProbabilityP
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).p x = M.tensorPowerProbabilityP n x := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerProbabilityP]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      change M.p x0 * (M.tensorPower n).p xs =
        ∏ i : Fin (n + 1), M.p (tensorPowerEquiv (a := α) (n + 1) (x0, xs) i)
      rw [ih xs, Fin.prod_univ_succ]
      rfl

omit [DecidableEq α] in
@[simp]
theorem tensorPower_q_eq_tensorPowerProbabilityQ
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).q x = M.tensorPowerProbabilityQ n x := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerProbabilityQ]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      change M.q x0 * (M.tensorPower n).q xs =
        ∏ i : Fin (n + 1), M.q (tensorPowerEquiv (a := α) (n + 1) (x0, xs) i)
      rw [ih xs, Fin.prod_univ_succ]
      rfl

@[simp]
theorem tensorPowerProbabilityP_permEquiv
    (M : ClassicalBinaryModel α) (n : Nat) (σ : Equiv.Perm (Fin n))
    (x : TensorPower α n) :
    M.tensorPowerProbabilityP n (permEquiv (a := α) n σ x) =
      M.tensorPowerProbabilityP n x := by
  unfold tensorPowerProbabilityP
  rw [tensorPowerEquiv_permEquiv]
  exact Equiv.prod_comp σ.symm (fun i => M.p (tensorPowerEquiv (a := α) n x i))

@[simp]
theorem tensorPowerProbabilityQ_permEquiv
    (M : ClassicalBinaryModel α) (n : Nat) (σ : Equiv.Perm (Fin n))
    (x : TensorPower α n) :
    M.tensorPowerProbabilityQ n (permEquiv (a := α) n σ x) =
      M.tensorPowerProbabilityQ n x := by
  unfold tensorPowerProbabilityQ
  rw [tensorPowerEquiv_permEquiv]
  exact Equiv.prod_comp σ.symm (fun i => M.q (tensorPowerEquiv (a := α) n x i))

/-- Product `p`-probability is constant on tensor-power type classes. -/
theorem tensorPower_p_eq_of_typeProfile_eq
    (M : ClassicalBinaryModel α) {n : Nat} {x y : TensorPower α n}
    (hxy :
      tensorPowerTypeProfile (a := α) n x =
        tensorPowerTypeProfile (a := α) n y) :
    (M.tensorPower n).p x = (M.tensorPower n).p y := by
  rw [tensorPower_p_eq_tensorPowerProbabilityP,
    tensorPower_p_eq_tensorPowerProbabilityP]
  obtain ⟨σ, hσ⟩ := exists_permEquiv_of_tensorPowerTypeProfile_eq
    (a := α) n x y hxy
  rw [← hσ]
  exact (tensorPowerProbabilityP_permEquiv M n σ x).symm

/-- Product `q`-probability is constant on tensor-power type classes. -/
theorem tensorPower_q_eq_of_typeProfile_eq
    (M : ClassicalBinaryModel α) {n : Nat} {x y : TensorPower α n}
    (hxy :
      tensorPowerTypeProfile (a := α) n x =
        tensorPowerTypeProfile (a := α) n y) :
    (M.tensorPower n).q x = (M.tensorPower n).q y := by
  rw [tensorPower_q_eq_tensorPowerProbabilityQ,
    tensorPower_q_eq_tensorPowerProbabilityQ]
  obtain ⟨σ, hσ⟩ := exists_permEquiv_of_tensorPowerTypeProfile_eq
    (a := α) n x y hxy
  rw [← hσ]
  exact (tensorPowerProbabilityQ_permEquiv M n σ x).symm

/-- The `p`-mass of one type class. -/
def profileClassMassP
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) : ℝ≥0 :=
  (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).p x)

/-- The `q`-mass of one type class. -/
def profileClassMassQ
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) : ℝ≥0 :=
  (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).q x)

/-- Type-class `p`-mass is cardinality times any representative probability. -/
theorem profileClassMassP_eq_card_mul
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) :
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).p x) =
      ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).p profile.rep := by
  calc
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).p x)
        = (tensorPowerProfileClass (a := α) profile).sum
            (fun _x => (M.tensorPower n).p profile.rep) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          apply tensorPower_p_eq_of_typeProfile_eq
          exact ((mem_tensorPowerProfileClass (a := α) profile x).mp hx).trans
            (TensorPowerProfile.rep_typeProfile (a := α) profile).symm
    _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).p profile.rep := by
          simp

/-- Type-class `q`-mass is cardinality times any representative probability. -/
theorem profileClassMassQ_eq_card_mul
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) :
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).q x) =
      ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).q profile.rep := by
  calc
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).q x)
        = (tensorPowerProfileClass (a := α) profile).sum
            (fun _x => (M.tensorPower n).q profile.rep) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          apply tensorPower_q_eq_of_typeProfile_eq
          exact ((mem_tensorPowerProfileClass (a := α) profile x).mp hx).trans
            (TensorPowerProfile.rep_typeProfile (a := α) profile).symm
    _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).q profile.rep := by
          simp

/-- Tensor-power `p` probability as a product over the type profile. -/
theorem tensorPower_p_eq_profile_prod
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).p x =
      ∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) n x z := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerTypeProfile]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rw [tensorPower_succ_p, ih xs]
      rw [show
          (∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) (n + 1) (x0, xs) z) =
            ∏ z : α, M.p z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) by
        refine Finset.prod_congr rfl ?_
        intro z _
        rw [tensorPowerTypeProfile_succ]]
      have hsingle :
          (∏ z : α, M.p z ^ (if x0 = z then 1 else 0)) = M.p x0 := by
        rw [Finset.prod_eq_single x0]
        · simp
        · intro z _ hz
          have hx0z : x0 ≠ z := fun h => hz h.symm
          simp [hx0z]
        · intro hx
          simp at hx
      calc
        M.p x0 * ∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) n xs z =
            (∏ z : α, M.p z ^ (if x0 = z then 1 else 0)) *
              ∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) n xs z := by
              rw [hsingle]
        _ = ∏ z : α, (M.p z ^ (if x0 = z then 1 else 0)) *
              (M.p z ^ tensorPowerTypeProfile (a := α) n xs z) := by
              rw [Finset.prod_mul_distrib]
        _ = ∏ z : α, M.p z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) := by
              refine Finset.prod_congr rfl ?_
              intro z _
              rw [pow_add]

/-- Tensor-power `q` probability as a product over the type profile. -/
theorem tensorPower_q_eq_profile_prod
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).q x =
      ∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) n x z := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerTypeProfile]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rw [tensorPower_succ_q, ih xs]
      rw [show
          (∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) (n + 1) (x0, xs) z) =
            ∏ z : α, M.q z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) by
        refine Finset.prod_congr rfl ?_
        intro z _
        rw [tensorPowerTypeProfile_succ]]
      have hsingle :
          (∏ z : α, M.q z ^ (if x0 = z then 1 else 0)) = M.q x0 := by
        rw [Finset.prod_eq_single x0]
        · simp
        · intro z _ hz
          have hx0z : x0 ≠ z := fun h => hz h.symm
          simp [hx0z]
        · intro hx
          simp at hx
      calc
        M.q x0 * ∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) n xs z =
            (∏ z : α, M.q z ^ (if x0 = z then 1 else 0)) *
              ∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) n xs z := by
              rw [hsingle]
        _ = ∏ z : α, (M.q z ^ (if x0 = z then 1 else 0)) *
              (M.q z ^ tensorPowerTypeProfile (a := α) n xs z) := by
              rw [Finset.prod_mul_distrib]
        _ = ∏ z : α, M.q z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) := by
              refine Finset.prod_congr rfl ?_
              intro z _
              rw [pow_add]

/-- Product-form lower bound for the `p`-mass of one type class. -/
theorem profileClassMassP_source_lower_bound_product
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) ≤
      (M.profileClassMassP profile : ℝ) := by
  have hcard :=
    tensorPowerProfileClass_card_source_lower_bound (α := α) hN profile
  have hprob :
      (M.tensorPower N).p profile.rep =
        ∏ z : α, M.p z ^ profile.1 z := by
    rw [← TensorPowerProfile.rep_typeProfile (a := α) profile]
    exact tensorPower_p_eq_profile_prod (M := M) N profile.rep
  have hmass :
      (M.profileClassMassP profile : ℝ) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ) *
          (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    rw [profileClassMassP, profileClassMassP_eq_card_mul, hprob]
    simp
  rw [hmass]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- Product-form lower bound for the `q`-mass of one type class. -/
theorem profileClassMassQ_source_lower_bound_product
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) ≤
      (M.profileClassMassQ profile : ℝ) := by
  have hcard :=
    tensorPowerProfileClass_card_source_lower_bound (α := α) hN profile
  have hprob :
      (M.tensorPower N).q profile.rep =
        ∏ z : α, M.q z ^ profile.1 z := by
    rw [← TensorPowerProfile.rep_typeProfile (a := α) profile]
    exact tensorPower_q_eq_profile_prod (M := M) N profile.rep
  have hmass :
      (M.profileClassMassQ profile : ℝ) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ) *
          (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    rw [profileClassMassQ, profileClassMassQ_eq_card_mul, hprob]
    simp
  rw [hmass]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- The contribution of one type class to equal-prior error is the minimum of
the two equal-prior type-class masses. -/
theorem profileClassErrorContribution_eq_min_mass
    (M : ClassicalBinaryModel α) {N : Nat}
    (profile : TensorPowerProfile α N) :
    ((tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x))) =
      min ((1 / 2 : ℝ≥0) * M.profileClassMassP profile)
        ((1 / 2 : ℝ≥0) * M.profileClassMassQ profile) := by
  have hp :
      (tensorPowerProfileClass (a := α) profile).sum
          (fun x => (M.tensorPower N).p x) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          (M.tensorPower N).p profile.rep :=
    profileClassMassP_eq_card_mul M profile
  have hq :
      (tensorPowerProfileClass (a := α) profile).sum
          (fun x => (M.tensorPower N).q x) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          (M.tensorPower N).q profile.rep :=
    profileClassMassQ_eq_card_mul M profile
  have hsum :
      (tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x)) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep) := by
    calc
      (tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x))
          =
        (tensorPowerProfileClass (a := α) profile).sum
          (fun _x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hprof :
                tensorPowerTypeProfile (a := α) N x = profile.1 :=
              (mem_tensorPowerProfileClass (a := α) profile x).mp hx
            have hprof_rep :
                tensorPowerTypeProfile (a := α) N profile.rep = profile.1 :=
              TensorPowerProfile.rep_typeProfile (a := α) profile
            have hp_eq :
                (M.tensorPower N).p x = (M.tensorPower N).p profile.rep :=
              tensorPower_p_eq_of_typeProfile_eq M (hprof.trans hprof_rep.symm)
            have hq_eq :
                (M.tensorPower N).q x = (M.tensorPower N).q profile.rep :=
              tensorPower_q_eq_of_typeProfile_eq M (hprof.trans hprof_rep.symm)
            change
              min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
                  ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x) =
                min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
                  ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)
            rw [hp_eq, hq_eq]
      _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep) := by
            simp
  rw [hsum]
  rw [profileClassMassP, profileClassMassQ, hp, hq]
  rw [← mul_assoc, ← mul_assoc]
  rw [show
      ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep) =
        min (((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
              ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep))
          (((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
              ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)) by
    exact mul_min_of_nonneg
      ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
      ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)
      (show (0 : ℝ≥0) ≤ ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) by
        positivity)]
  congr 1 <;> ring

/-- A single type class contributes no more than the total classical
equal-prior error. -/
theorem profileClassErrorContribution_le_equalPriorError
    (M : ClassicalBinaryModel α) {N : Nat}
    (profile : TensorPowerProfile α N) :
    ((tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x))) ≤
      (M.tensorPower N).equalPriorError := by
  unfold equalPriorError
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro x hx
      simp)
    (by
      intro x _ _
      positivity)

/-- Source-backed product-form lower bound contributed by one type class to the
classical equal-prior error. -/
theorem equalPriorError_source_lower_bound_profile_product
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    (1 / 2 : ℝ) *
        min
          ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
            Real.exp
              (-(∑ z : α,
                (profile.1 z : ℝ) *
                  Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
            (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
          ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
            Real.exp
              (-(∑ z : α,
                (profile.1 z : ℝ) *
                  Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
            (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
      ≤ ((M.tensorPower N).equalPriorError : ℝ) := by
  let Lp : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
      (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  let Lq : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
      (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  have hLp :
      Lp ≤ (M.profileClassMassP profile : ℝ) := by
    simpa [Lp] using
      profileClassMassP_source_lower_bound_product (M := M) hN profile
  have hLq :
      Lq ≤ (M.profileClassMassQ profile : ℝ) := by
    simpa [Lq] using
      profileClassMassQ_source_lower_bound_product (M := M) hN profile
  have hmin :
      (1 / 2 : ℝ) * min Lp Lq ≤
        (min ((1 / 2 : ℝ≥0) * M.profileClassMassP profile)
          ((1 / 2 : ℝ≥0) * M.profileClassMassQ profile) : ℝ) := by
    have hhalfP :
        (1 / 2 : ℝ) * Lp ≤
          (((1 / 2 : ℝ≥0) * M.profileClassMassP profile : ℝ≥0) : ℝ) := by
      simpa [NNReal.coe_mul, NNReal.coe_div] using
        mul_le_mul_of_nonneg_left hLp (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))
    have hhalfQ :
        (1 / 2 : ℝ) * Lq ≤
          (((1 / 2 : ℝ≥0) * M.profileClassMassQ profile : ℝ≥0) : ℝ) := by
      simpa [NNReal.coe_mul, NNReal.coe_div] using
        mul_le_mul_of_nonneg_left hLq (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))
    have hmulmin :
        (1 / 2 : ℝ) * min Lp Lq =
          min ((1 / 2 : ℝ) * Lp) ((1 / 2 : ℝ) * Lq) := by
      rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))]
    rw [hmulmin]
    exact min_le_min hhalfP hhalfQ
  have hclass :=
    profileClassErrorContribution_eq_min_mass (M := M) profile
  have hclass_le :=
    profileClassErrorContribution_le_equalPriorError (M := M) profile
  exact hmin.trans (by
    have htarget :
        ((min ((1 / 2 : ℝ≥0) * M.profileClassMassP profile)
            ((1 / 2 : ℝ≥0) * M.profileClassMassQ profile) : ℝ≥0) : ℝ) ≤
          ((M.tensorPower N).equalPriorError : ℝ) := by
      rw [← hclass]
      exact_mod_cast hclass_le
    simpa [NNReal.coe_mul, NNReal.coe_div] using htarget)

/-- Source product-form lower bound attached to one finite type/profile. -/
def profileProductErrorLowerBound
    (M : ClassicalBinaryModel α) {N : Nat} (profile : TensorPowerProfile α N) : ℝ :=
  (1 / 2 : ℝ) *
    min
      ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
      ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))

/-- Finite-type Chernoff value obtained by minimizing the source product-form
type-class lower bound over all `N`-types. -/
def finiteTypeChernoffValue (M : ClassicalBinaryModel α) (N : Nat) : EReal :=
  ⨅ profile : TensorPowerProfile α N,
    normalizedNegLog (N - 1)
      (ENNReal.ofReal (M.profileProductErrorLowerBound profile))

theorem profileProductErrorLowerBound_nonneg
    (M : ClassicalBinaryModel α) {N : Nat} (profile : TensorPowerProfile α N) :
    0 ≤ M.profileProductErrorLowerBound profile := by
  unfold profileProductErrorLowerBound
  positivity

/-- On common support, the source profile lower bound is strictly positive. -/
theorem profileProductErrorLowerBound_pos_of_supported
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (hp : (profile.empiricalDistribution hN).SupportedBy M.p)
    (hq : (profile.empiricalDistribution hN).SupportedBy M.q) :
    0 < M.profileProductErrorLowerBound profile := by
  have hN_nn : (0 : ℝ≥0) < (N : ℝ≥0) := by
    exact_mod_cast hN
  have hp_pos_factor :
      ∀ z : α, 0 < M.p z ^ profile.1 z := by
    intro z
    by_cases hz : profile.1 z = 0
    · simp [hz]
    · have hz_nat : 0 < profile.1 z :=
        Nat.pos_of_ne_zero hz
      have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
        exact_mod_cast hz_nat
      have he :
          (profile.empiricalDistribution hN).prob z ≠ 0 := by
        rw [TensorPowerProfile.empiricalDistribution_prob]
        exact ne_of_gt (div_pos hz_nn hN_nn)
      have hpz : M.p z ≠ 0 := hp z he
      have hpz_pos : 0 < M.p z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hpz)
      exact pow_pos hpz_pos _
  have hq_pos_factor :
      ∀ z : α, 0 < M.q z ^ profile.1 z := by
    intro z
    by_cases hz : profile.1 z = 0
    · simp [hz]
    · have hz_nat : 0 < profile.1 z :=
        Nat.pos_of_ne_zero hz
      have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
        exact_mod_cast hz_nat
      have he :
          (profile.empiricalDistribution hN).prob z ≠ 0 := by
        rw [TensorPowerProfile.empiricalDistribution_prob]
        exact ne_of_gt (div_pos hz_nn hN_nn)
      have hqz : M.q z ≠ 0 := hq z he
      have hqz_pos : 0 < M.q z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hqz)
      exact pow_pos hqz_pos _
  have hp_prod_nn : 0 < ∏ z : α, M.p z ^ profile.1 z :=
    Finset.prod_pos fun z _ => hp_pos_factor z
  have hq_prod_nn : 0 < ∏ z : α, M.q z ^ profile.1 z :=
    Finset.prod_pos fun z _ => hq_pos_factor z
  have hp_prod : 0 < ((∏ z : α, M.p z ^ profile.1 z : ℝ≥0) : ℝ) := by
    exact_mod_cast hp_prod_nn
  have hq_prod : 0 < ((∏ z : α, M.q z ^ profile.1 z : ℝ≥0) : ℝ) := by
    exact_mod_cast hq_prod_nn
  have hp_prod' :
      0 < ∏ z : α, (((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    simpa using hp_prod
  have hq_prod' :
      0 < ∏ z : α, (((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    simpa using hq_prod
  have hpref :
      0 < (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal := by
    unfold finiteAlphabetMethodOfTypesPolynomialPrefactor
    apply ENNReal.toReal_pos
    · exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · apply ENNReal.inv_ne_top.mpr
      apply ENNReal.pow_ne_zero
      norm_num
  let common : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ))))
  have hcommon : 0 < common := by
    unfold common
    positivity
  have hpterm :
      0 < common * (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) :=
    mul_pos hcommon hp_prod'
  have hqterm :
      0 < common * (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) :=
    mul_pos hcommon hq_prod'
  unfold profileProductErrorLowerBound
  change 0 <
    (1 / 2 : ℝ) *
      min
        (common * (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
        (common * (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
  exact mul_pos (by positivity) (lt_min hpterm hqterm)

/-- The real KL of a supported empirical profile expands as the expected
log-ratio. -/
theorem profileEmpirical_relativeEntropyReal_eq_sum_log_ratio
    {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (p : ClassicalDistribution α)
    (hp : (profile.empiricalDistribution hN).SupportedBy p.prob) :
    relativeEntropyReal (profile.empiricalDistribution hN) p =
      ∑ z : α,
        ((profile.1 z : ℝ) / (N : ℝ)) *
          (Real.log ((profile.1 z : ℝ) / (N : ℝ)) -
            Real.log (p.prob z : ℝ)) := by
  classical
  unfold relativeEntropyReal relativeEntropySummandReal
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : profile.1 z = 0
  · have hemp : (profile.empiricalDistribution hN).prob z = 0 := by
      rw [TensorPowerProfile.empiricalDistribution_prob]
      simp [hz]
    simp [hemp, hz]
  · have hN_nn : (0 : ℝ≥0) < (N : ℝ≥0) := by
      exact_mod_cast hN
    have hz_nat : 0 < profile.1 z := Nat.pos_of_ne_zero hz
    have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
      exact_mod_cast hz_nat
    have hemp_ne : (profile.empiricalDistribution hN).prob z ≠ 0 := by
      rw [TensorPowerProfile.empiricalDistribution_prob]
      exact ne_of_gt (div_pos hz_nn hN_nn)
    have hpz_ne : p.prob z ≠ 0 := hp z hemp_ne
    have hemp_pos : 0 < ((profile.empiricalDistribution hN).prob z : ℝ) := by
      have hemp_nn : (0 : ℝ≥0) < (profile.empiricalDistribution hN).prob z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hemp_ne)
      exact_mod_cast hemp_nn
    have hpz_pos : 0 < (p.prob z : ℝ) := by
      have hpz_nn : (0 : ℝ≥0) < p.prob z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hpz_ne)
      exact_mod_cast hpz_nn
    have hlog :
        Real.log (((profile.empiricalDistribution hN).prob z : ℝ) /
            (p.prob z : ℝ)) =
          Real.log ((profile.empiricalDistribution hN).prob z : ℝ) -
            Real.log (p.prob z : ℝ) := by
      rw [Real.log_div hemp_pos.ne' hpz_pos.ne']
    rw [TensorPowerProfile.empiricalDistribution_prob] at hlog
    simp [TensorPowerProfile.empiricalDistribution_prob, hz, Nat.ne_of_gt hN,
      NNReal.coe_div]
    simpa [NNReal.coe_div] using hlog

/-- Multiplying the empirical-profile KL by the copy number removes the
empirical normalization. -/
theorem profileEmpirical_mul_relativeEntropyReal_eq_sum_log_sub
    {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (p : ClassicalDistribution α)
    (hp : (profile.empiricalDistribution hN).SupportedBy p.prob) :
    (N : ℝ) * relativeEntropyReal (profile.empiricalDistribution hN) p =
      (∑ z : α,
        (profile.1 z : ℝ) *
          Real.log ((profile.1 z : ℝ) / (N : ℝ))) -
        ∑ z : α, (profile.1 z : ℝ) * Real.log (p.prob z : ℝ) := by
  classical
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  rw [profileEmpirical_relativeEntropyReal_eq_sum_log_ratio hN profile p hp]
  calc
    (N : ℝ) *
        (∑ z : α,
          (↑(profile.1 z) / ↑N) *
            (Real.log (↑(profile.1 z) / ↑N) - Real.log ↑(p.prob z)))
        =
      ∑ z : α,
        (N : ℝ) *
          ((↑(profile.1 z) / ↑N) *
            (Real.log (↑(profile.1 z) / ↑N) - Real.log ↑(p.prob z))) := by
          rw [Finset.mul_sum]
    _ =
      ∑ z : α,
        ((profile.1 z : ℝ) * Real.log ((profile.1 z : ℝ) / (N : ℝ)) -
          (profile.1 z : ℝ) * Real.log (p.prob z : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro z _
        field_simp [hN_ne]
    _ =
      (∑ z : α,
        (profile.1 z : ℝ) *
          Real.log ((profile.1 z : ℝ) / (N : ℝ))) -
        ∑ z : α, (profile.1 z : ℝ) * Real.log (p.prob z : ℝ) := by
        rw [Finset.sum_sub_distrib]

/-- Supported profile probabilities rewrite the KL exponent into the product
probability factor used by the method-of-types lower bound. -/
theorem exp_neg_mul_profileEmpirical_relativeEntropyReal_eq_prod
    {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (p : ClassicalDistribution α)
    (hp : (profile.empiricalDistribution hN).SupportedBy p.prob) :
    Real.exp
        (-(N : ℝ) *
          relativeEntropyReal (profile.empiricalDistribution hN) p) =
      Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
  classical
  let S : ℝ :=
    ∑ z : α,
      (profile.1 z : ℝ) *
        Real.log ((profile.1 z : ℝ) / (N : ℝ))
  let L : ℝ := ∑ z : α, (profile.1 z : ℝ) * Real.log (p.prob z : ℝ)
  have hmul :=
    profileEmpirical_mul_relativeEntropyReal_eq_sum_log_sub
      hN profile p hp
  have hprod :
      Real.exp L =
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    let realTerm : α → ℝ := fun z => ((p.prob z : ℝ) ^ profile.1 z)
    let expTerm : α → ℝ := fun z =>
      Real.exp ((profile.1 z : ℝ) * Real.log (p.prob z : ℝ))
    have hcoe :
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) =
          ∏ z : α, realTerm z := by
      simp [realTerm]
    have hterms : Finset.univ.prod realTerm = Finset.univ.prod expTerm := by
      refine Finset.prod_congr rfl ?_
      intro z _
      by_cases hz : profile.1 z = 0
      · simp [realTerm, expTerm, hz]
      · have hN_nn : (0 : ℝ≥0) < (N : ℝ≥0) := by
          exact_mod_cast hN
        have hz_nat : 0 < profile.1 z := Nat.pos_of_ne_zero hz
        have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
          exact_mod_cast hz_nat
        have hemp_ne : (profile.empiricalDistribution hN).prob z ≠ 0 := by
          rw [TensorPowerProfile.empiricalDistribution_prob]
          exact ne_of_gt (div_pos hz_nn hN_nn)
        have hpz_ne : p.prob z ≠ 0 := hp z hemp_ne
        have hpz_pos : 0 < (p.prob z : ℝ) := by
          have hpz_nn : (0 : ℝ≥0) < p.prob z :=
            lt_of_le_of_ne (by positivity) (Ne.symm hpz_ne)
          exact_mod_cast hpz_nn
        calc
          realTerm z = ((p.prob z : ℝ) ^ profile.1 z) := by
            rfl
          _ = (Real.exp (Real.log (p.prob z : ℝ))) ^ profile.1 z := by
            rw [Real.exp_log hpz_pos]
          _ = expTerm z := by
            unfold expTerm
            rw [← Real.exp_nat_mul]
    have hexp : Finset.univ.prod expTerm = Real.exp L := by
      unfold expTerm L
      rw [Real.exp_sum]
    exact (hcoe.trans (hterms.trans hexp)).symm
  have hmul' :
      (N : ℝ) * relativeEntropyReal (profile.empiricalDistribution hN) p =
        S - L := by
    simpa [S, L] using hmul
  calc
    Real.exp
        (-(N : ℝ) *
          relativeEntropyReal (profile.empiricalDistribution hN) p)
        = Real.exp (-(S - L)) := by
          congr 1
          rw [neg_mul, hmul']
    _ = Real.exp (-S) * Real.exp L := by
          rw [show -(S - L) = -S + L by ring, Real.exp_add]
    _ = Real.exp (-S) *
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
          rw [hprod]

/-- Source-shaped positive lower bound used before taking logarithms. -/
theorem profileProductErrorLowerBound_source_exp_lower_bound
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (hp : (profile.empiricalDistribution hN).SupportedBy M.p)
    (hq : (profile.empiricalDistribution hN).SupportedBy M.q) :
    (1 / 2 : ℝ) *
        (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(N : ℝ) *
            max
              (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
              (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution))
      ≤ M.profileProductErrorLowerBound profile := by
  classical
  let Dp : ℝ :=
    relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution
  let Dq : ℝ :=
    relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution
  let common : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ))))
  let P : ℝ :=
    (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  let Q : ℝ :=
    (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp' : (profile.empiricalDistribution hN).SupportedBy M.pDistribution.prob := by
    simpa [pDistribution] using hp
  have hq' : (profile.empiricalDistribution hN).SupportedBy M.qDistribution.prob := by
    simpa [qDistribution] using hq
  have hp_exp :
      Real.exp (-(N : ℝ) * Dp) =
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) * P := by
    simpa [Dp, P, pDistribution] using
      exp_neg_mul_profileEmpirical_relativeEntropyReal_eq_prod
        hN profile M.pDistribution hp'
  have hq_exp :
      Real.exp (-(N : ℝ) * Dq) =
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) * Q := by
    simpa [Dq, Q, qDistribution] using
      exp_neg_mul_profileEmpirical_relativeEntropyReal_eq_prod
        hN profile M.qDistribution hq'
  have hpmax :
      Real.exp (-(N : ℝ) * max Dp Dq) ≤ Real.exp (-(N : ℝ) * Dp) := by
    exact Real.exp_le_exp.mpr (by
      have hle : Dp ≤ max Dp Dq := le_max_left _ _
      nlinarith)
  have hqmax :
      Real.exp (-(N : ℝ) * max Dp Dq) ≤ Real.exp (-(N : ℝ) * Dq) := by
    exact Real.exp_le_exp.mpr (by
      have hle : Dq ≤ max Dp Dq := le_max_right _ _
      nlinarith)
  have hc_nonneg :
      0 ≤ (1 / 2 : ℝ) *
        (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal := by
    positivity
  have hp_bound :
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq) ≤
        (1 / 2 : ℝ) * (common * P) := by
    calc
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq)
          ≤
        (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * Dp) := by
            exact mul_le_mul_of_nonneg_left hpmax hc_nonneg
      _ = (1 / 2 : ℝ) * (common * P) := by
            rw [hp_exp]
            simp [common, P]
            ring
  have hq_bound :
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq) ≤
        (1 / 2 : ℝ) * (common * Q) := by
    calc
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq)
          ≤
        (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * Dq) := by
            exact mul_le_mul_of_nonneg_left hqmax hc_nonneg
      _ = (1 / 2 : ℝ) * (common * Q) := by
            rw [hq_exp]
            simp [common, Q]
            ring
  have hmin :
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq) ≤
        min ((1 / 2 : ℝ) * (common * P))
          ((1 / 2 : ℝ) * (common * Q)) :=
    le_min hp_bound hq_bound
  have hmin_half :
      min ((1 / 2 : ℝ) * (common * P))
          ((1 / 2 : ℝ) * (common * Q)) =
        (1 / 2 : ℝ) * min (common * P) (common * Q) := by
    rw [← mul_min_of_nonneg (common * P) (common * Q)
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))]
  calc
    (1 / 2 : ℝ) *
        (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp (-(N : ℝ) * max Dp Dq)
        ≤ min ((1 / 2 : ℝ) * (common * P))
            ((1 / 2 : ℝ) * (common * Q)) := hmin
    _ = M.profileProductErrorLowerBound profile := by
          rw [hmin_half]
          simp [profileProductErrorLowerBound, common, P, Q]

/-- Supported-profile real logarithmic method-of-types bound. -/
theorem normalizedNegLog_profileProductErrorLowerBound_le
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (hp : (profile.empiricalDistribution hN).SupportedBy M.p)
    (hq : (profile.empiricalDistribution hN).SupportedBy M.q) :
    -Real.log (M.profileProductErrorLowerBound profile) / (N : ℝ) ≤
      max
          (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
          (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution) +
        (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
        Real.log 2 / (N : ℝ) := by
  classical
  let c : ℝ :=
    (1 / 2 : ℝ) *
      (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal
  let d : ℝ :=
    max
      (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
      (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution)
  have hR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : 0 < c := by
    unfold c
    have hpref :
        0 < (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal := by
      rw [finiteAlphabetMethodOfTypesPolynomialPrefactor_toReal]
      positivity
    positivity
  have hE :
      0 < M.profileProductErrorLowerBound profile :=
    profileProductErrorLowerBound_pos_of_supported (M := M) hN profile hp hq
  have hbound : c * Real.exp (-(N : ℝ) * d) ≤
      M.profileProductErrorLowerBound profile := by
    simpa [c, d, mul_assoc] using
      profileProductErrorLowerBound_source_exp_lower_bound
        (M := M) hN profile hp hq
  have hlog :=
    neg_log_div_le_of_mul_exp_neg_le (E := M.profileProductErrorLowerBound profile)
      (c := c) (d := d) (R := (N : ℝ)) hR hc hE hbound
  have hpen :=
    equalPriorMethodOfTypesPrefactor_log_penalty (α := α) hN
  calc
    -Real.log (M.profileProductErrorLowerBound profile) / (N : ℝ)
        ≤ d + (-Real.log c) / (N : ℝ) := hlog
    _ =
      d +
        ((Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
          Real.log 2 / (N : ℝ)) := by
          rw [show (-Real.log c) / (N : ℝ) =
              (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
                Real.log 2 / (N : ℝ) by
            simpa [c] using hpen]
    _ =
      max
          (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
          (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution) +
        (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
        Real.log 2 / (N : ℝ) := by
          simp [d]
          ring_nf

/-- The source product-form lower bound is below the actual classical
equal-prior error. -/
theorem profileProductErrorLowerBound_le_equalPriorError
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    ENNReal.ofReal (M.profileProductErrorLowerBound profile) ≤
      (M.tensorPower N).equalPriorErrorENNReal := by
  have hreal :=
    equalPriorError_source_lower_bound_profile_product (M := M) hN profile
  unfold equalPriorErrorENNReal
  rw [ENNReal.ofReal_le_iff_le_toReal]
  · simpa [profileProductErrorLowerBound] using hreal
  · simp

/-- Pointwise finite-copy method-of-types bound through the finite-type value. -/
theorem normalizedNegLog_le_finiteTypeChernoffValue
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N) :
    normalizedNegLog (N - 1) ((M.tensorPower N).equalPriorErrorENNReal) ≤
      M.finiteTypeChernoffValue N := by
  unfold finiteTypeChernoffValue
  refine le_iInf ?_
  intro profile
  exact normalizedNegLog_antitone (N - 1)
    (profileProductErrorLowerBound_le_equalPriorError (M := M) hN profile)

/-- The KL minimax objective appearing in the classical Chernoff converse. -/
def distributionKLMax
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α) : EReal :=
  max (relativeEntropy r M.pDistribution) (relativeEntropy r M.qDistribution)

/-- On common support, the support-aware KL maximum is the real KL maximum
embedded into `EReal`. -/
theorem distributionKLMax_eq_coe_real_of_supported
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    (hp : r.SupportedBy M.p) (hq : r.SupportedBy M.q) :
    M.distributionKLMax r =
      ((max (relativeEntropyReal r M.pDistribution)
          (relativeEntropyReal r M.qDistribution) : ℝ) : EReal) := by
  classical
  have hp' : r.SupportedBy M.pDistribution.prob := by
    simpa [pDistribution] using hp
  have hq' : r.SupportedBy M.qDistribution.prob := by
    simpa [qDistribution] using hq
  unfold distributionKLMax
  rw [relativeEntropy_eq_coe_of_supported _ _ hp',
    relativeEntropy_eq_coe_of_supported _ _ hq']
  by_cases hle :
      relativeEntropyReal r M.pDistribution ≤
        relativeEntropyReal r M.qDistribution
  · rw [max_eq_right hle, max_eq_right (EReal.coe_le_coe_iff.mpr hle)]
  · have hge :
        relativeEntropyReal r M.qDistribution ≤
          relativeEntropyReal r M.pDistribution := le_of_not_ge hle
    rw [max_eq_left hge, max_eq_left (EReal.coe_le_coe_iff.mpr hge)]

/-- A common-support tilted distribution at a common-support partition
minimizer has KL maximum bounded by the negative log of the partition. -/
theorem commonSupportTilted_distributionKLMax_le_neg_log_partition_at_min
    (M : ClassicalBinaryModel α) [DecidableEq α] {sStar : ℝ}
    (hs : sStar ∈ Set.Icc (0 : ℝ) 1)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar)
    (hZ : M.chernoffPartitionNNReal sStar ≠ 0) :
    M.distributionKLMax (M.commonSupportTiltedDistribution sStar hZ) ≤
      ((-Real.log (M.chernoffPartition sStar) : ℝ) : EReal) := by
  classical
  have hZpos_nn : 0 < M.chernoffPartitionNNReal sStar := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition sStar := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hs0 : 0 ≤ sStar := hs.1
  have hs1 : sStar ≤ 1 := hs.2
  have hdist :
      M.distributionKLMax (M.commonSupportTiltedDistribution sStar hZ) =
        ((max
            (relativeEntropyReal (M.commonSupportTiltedDistribution sStar hZ) M.pDistribution)
            (relativeEntropyReal (M.commonSupportTiltedDistribution sStar hZ) M.qDistribution)
          : ℝ) : EReal) :=
    distributionKLMax_eq_coe_real_of_supported (M := M)
      (r := M.commonSupportTiltedDistribution sStar hZ)
      (commonSupportTiltedDistribution_supportedBy_p M sStar hZ)
      (commonSupportTiltedDistribution_supportedBy_q M sStar hZ)
  rw [hdist, EReal.coe_le_coe_iff]
  refine max_le ?_ ?_
  · rw [relativeEntropyReal_commonSupportTilted_p (M := M) (s := sStar) hZ]
    rcases lt_or_eq_of_le hs0 with hs0lt | hs0eq
    · rcases lt_or_eq_of_le hs1 with hs1lt | hs1eq
      · have hD :
            M.chernoffPartitionDeriv sStar = 0 :=
          chernoffPartitionDeriv_eq_zero_at_interior_min (M := M)
            hs0lt hs1lt hmin
        rw [hD]
        have hzero :
            (1 - sStar) * 0 / M.chernoffPartition sStar = 0 := by ring
        rw [hzero]
        simp
      · have hD :
            M.chernoffPartitionDeriv sStar ≤ 0 :=
          chernoffPartitionDeriv_nonpos_at_right_min (M := M) hs1eq hmin
        have hcoeff : 0 ≤ (1 - sStar) := by linarith
        have hterm :
            0 ≤ (1 - sStar) * M.chernoffPartitionDeriv sStar /
              M.chernoffPartition sStar := by
          have hm : 0 ≤ (1 - sStar) * M.chernoffPartitionDeriv sStar := by
            nlinarith [hcoeff, hD]
          exact div_nonneg hm hZpos.le
        nlinarith
    · subst sStar
      have hD :
          0 ≤ M.chernoffPartitionDeriv 0 :=
        chernoffPartitionDeriv_nonneg_at_left_min (M := M) rfl hmin
      have hterm :
          0 ≤ (1 - (0 : ℝ)) * M.chernoffPartitionDeriv 0 /
            M.chernoffPartition 0 := by
        have hm : 0 ≤ (1 - (0 : ℝ)) * M.chernoffPartitionDeriv 0 := by
          nlinarith
        exact div_nonneg hm hZpos.le
      nlinarith
  · rw [relativeEntropyReal_commonSupportTilted_q (M := M) (s := sStar) hZ]
    rcases lt_or_eq_of_le hs0 with hs0lt | hs0eq
    · rcases lt_or_eq_of_le hs1 with hs1lt | hs1eq
      · have hD :
            M.chernoffPartitionDeriv sStar = 0 :=
          chernoffPartitionDeriv_eq_zero_at_interior_min (M := M)
            hs0lt hs1lt hmin
        rw [hD]
        have hzero :
            sStar * 0 / M.chernoffPartition sStar = 0 := by ring
        rw [hzero]
        simp
      · have hD :
            M.chernoffPartitionDeriv sStar ≤ 0 :=
          chernoffPartitionDeriv_nonpos_at_right_min (M := M) hs1eq hmin
        have hterm :
            sStar * M.chernoffPartitionDeriv sStar /
              M.chernoffPartition sStar ≤ 0 := by
          have hm : sStar * M.chernoffPartitionDeriv sStar ≤ 0 := by
            nlinarith [hs0, hD]
          exact div_nonpos_of_nonpos_of_nonneg hm hZpos.le
        nlinarith
    · subst sStar
      have hzero :
          (0 : ℝ) * M.chernoffPartitionDeriv 0 /
            M.chernoffPartition 0 = 0 := by ring
      rw [hzero]
      simp

/-- Direct tilted-distribution variational witness for the classical Chernoff
bound.  In the finite-distance case the common support is nonempty, so the
common-support tilted distribution at a partition minimizer is well-defined and
has KL maximum at most the public Chernoff distance. -/
theorem exists_distribution_klMax_le_chernoffDistance
    (M : ClassicalBinaryModel α) [DecidableEq α]
    (hfinite : M.chernoffDistance ≠ ⊤) :
    ∃ r : ClassicalDistribution α,
      r.SupportedBy M.p ∧
      r.SupportedBy M.q ∧
      M.distributionKLMax r ≤ M.chernoffDistance := by
  classical
  obtain ⟨sStar, hs, hmin⟩ := exists_isMinOn_chernoffPartition_Icc_real M
  let hZ : M.chernoffPartitionNNReal sStar ≠ 0 :=
    chernoffPartitionNNReal_ne_zero_of_chernoffDistance_ne_top
      (M := M) hfinite sStar
  refine ⟨M.commonSupportTiltedDistribution sStar hZ,
    commonSupportTiltedDistribution_supportedBy_p M sStar hZ,
    commonSupportTiltedDistribution_supportedBy_q M sStar hZ, ?_⟩
  exact
    (commonSupportTilted_distributionKLMax_le_neg_log_partition_at_min
      (M := M) hs hmin hZ).trans
      (neg_log_commonPartition_le_chernoffDistance (M := M) hs hZ)

/-- EReal lift of the supported-profile logarithmic method-of-types bound,
with unsupported profiles handled by the support-aware `⊤` convention. -/
theorem normalizedNegLog_profileProductErrorLowerBound_le_distributionKLMax
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    normalizedNegLog (N - 1)
        (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) ≤
      M.distributionKLMax (profile.empiricalDistribution hN) +
        finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
        equalPriorAverageLogPenalty (N - 1) := by
  classical
  have hcoe_max : ∀ x y : ℝ,
      max (x : EReal) (y : EReal) = ((max x y : ℝ) : EReal) := by
    intro x y
    by_cases hxy : x ≤ y
    · rw [max_eq_right (EReal.coe_le_coe_iff.mpr hxy), max_eq_right hxy]
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [max_eq_left (EReal.coe_le_coe_iff.mpr hyx), max_eq_left hyx]
  by_cases hp :
      (profile.empiricalDistribution hN).SupportedBy M.pDistribution.prob
  · have hp' : (profile.empiricalDistribution hN).SupportedBy M.p := by
      simpa [pDistribution] using hp
    by_cases hq :
        (profile.empiricalDistribution hN).SupportedBy M.qDistribution.prob
    · have hq' : (profile.empiricalDistribution hN).SupportedBy M.q := by
        simpa [qDistribution] using hq
      have hpos :
          0 < M.profileProductErrorLowerBound profile :=
        profileProductErrorLowerBound_pos_of_supported (M := M) hN profile hp' hq'
      have hNreal : (N : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hN
      have hleft :
          normalizedNegLog (N - 1)
              (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) =
            ((-Real.log (M.profileProductErrorLowerBound profile) / (N : ℝ) : ℝ) :
              EReal) := by
        rw [normalizedNegLog_ofReal_eq_coe_real (N - 1) hpos]
        rw [Nat.sub_add_cancel hN]
        congr 1
        field_simp [hNreal]
      have hrhs :
          M.distributionKLMax (profile.empiricalDistribution hN) +
              finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
              equalPriorAverageLogPenalty (N - 1) =
            ((max
                (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
                (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution) +
              (Fintype.card α : ℝ) *
                Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
              Real.log 2 / (N : ℝ) : ℝ) : EReal) := by
        unfold distributionKLMax relativeEntropy
        simp [pDistribution, qDistribution, hp', hq',
          finiteAlphabetMethodOfTypesPolynomialPenalty,
          equalPriorAverageLogPenalty, hcoe_max, EReal.coe_add]
        have hsub_real : ((N - 1 : Nat) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.succ_le_of_lt hN)]
          norm_num
        rw [hsub_real]
        field_simp [hNreal]
        ring_nf
      rw [hleft, hrhs, EReal.coe_le_coe_iff]
      exact normalizedNegLog_profileProductErrorLowerBound_le (M := M) hN profile hp' hq'
    · have hq' : ¬(profile.empiricalDistribution hN).SupportedBy M.q := by
        simpa [qDistribution] using hq
      have hrhs :
          M.distributionKLMax (profile.empiricalDistribution hN) +
              finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
              equalPriorAverageLogPenalty (N - 1) = ⊤ := by
        simp [distributionKLMax, relativeEntropy, pDistribution, qDistribution,
          hp', hq', finiteAlphabetMethodOfTypesPolynomialPenalty,
          equalPriorAverageLogPenalty]
      rw [hrhs]
      exact le_top
  · have hp' : ¬(profile.empiricalDistribution hN).SupportedBy M.p := by
      simpa [pDistribution] using hp
    have hrhs :
        M.distributionKLMax (profile.empiricalDistribution hN) +
            finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
            equalPriorAverageLogPenalty (N - 1) = ⊤ := by
      simp [distributionKLMax, relativeEntropy, pDistribution, qDistribution,
        hp', finiteAlphabetMethodOfTypesPolynomialPenalty,
        equalPriorAverageLogPenalty]
    rw [hrhs]
    exact le_top

/-- Finite-type KL minimax value over empirical distributions of `N`-profiles.
For `N = 0` this is set to `⊤`; all method-of-types applications use
positive copy number `N = n + 1`. -/
noncomputable def finiteTypeKLDualValue
    (M : ClassicalBinaryModel α) [DecidableEq α] (N : Nat) : EReal :=
  if hN : 0 < N then
    ⨅ profile : TensorPowerProfile α N,
      M.distributionKLMax (profile.empiricalDistribution hN)
  else
    ⊤

omit [DecidableEq α] in
theorem finiteTypeKLDualValue_eq_iInf_of_pos
    (M : ClassicalBinaryModel α) [DecidableEq α] {N : Nat} (hN : 0 < N) :
    M.finiteTypeKLDualValue N =
      ⨅ profile : TensorPowerProfile α N,
        M.distributionKLMax (profile.empiricalDistribution hN) := by
  simp [finiteTypeKLDualValue, hN]

omit [DecidableEq α] in
theorem finiteTypeKLDualValue_zero
    (M : ClassicalBinaryModel α) [DecidableEq α] :
    M.finiteTypeKLDualValue 0 = ⊤ := by
  simp [finiteTypeKLDualValue]

/-- The finite-type KL dual value is bounded by every empirical profile
candidate. -/
theorem finiteTypeKLDualValue_le_distributionKLMax
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    M.finiteTypeKLDualValue N ≤
      M.distributionKLMax (profile.empiricalDistribution hN) := by
  classical
  rw [finiteTypeKLDualValue_eq_iInf_of_pos (M := M) hN]
  exact iInf_le _ profile

/-- Rounded empirical profiles are admissible candidates for the finite-type
KL dual value. -/
theorem finiteTypeKLDualValue_le_roundedDistributionKLMax
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    {N : Nat} (hN : 0 < N) :
    M.finiteTypeKLDualValue N ≤
      M.distributionKLMax ((r.roundedProfile N).empiricalDistribution hN) := by
  exact finiteTypeKLDualValue_le_distributionKLMax
    (M := M) hN (r.roundedProfile N)

/-- The KL minimax objective is continuous along rounded empirical profiles
whose limiting distribution is supported on both model distributions. -/
theorem distributionKLMax_roundedProfile_tendsto
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    (hp : r.SupportedBy M.p) (hq : r.SupportedBy M.q) :
    Tendsto
      (fun n : Nat =>
        M.distributionKLMax
          ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)))
      atTop (𝓝 (M.distributionKLMax r)) := by
  classical
  have hp' : r.SupportedBy M.pDistribution.prob := by
    simpa [pDistribution] using hp
  have hq' : r.SupportedBy M.qDistribution.prob := by
    simpa [qDistribution] using hq
  have hptend :
      Tendsto
        (fun n : Nat =>
          relativeEntropyReal
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
            M.pDistribution)
        atTop (𝓝 (relativeEntropyReal r M.pDistribution)) :=
    ClassicalDistribution.relativeEntropyReal_roundedProfile_tendsto
      (r := r) (p := M.pDistribution) hp'
  have hqtend :
      Tendsto
        (fun n : Nat =>
          relativeEntropyReal
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
            M.qDistribution)
        atTop (𝓝 (relativeEntropyReal r M.qDistribution)) :=
    ClassicalDistribution.relativeEntropyReal_roundedProfile_tendsto
      (r := r) (p := M.qDistribution) hq'
  have hmaxtend :
      Tendsto
        (fun n : Nat =>
          max
            (relativeEntropyReal
              ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
              M.pDistribution)
            (relativeEntropyReal
              ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
              M.qDistribution))
        atTop
        (𝓝 (max (relativeEntropyReal r M.pDistribution)
          (relativeEntropyReal r M.qDistribution))) :=
    hptend.max hqtend
  have htarget :
      M.distributionKLMax r =
        ((max (relativeEntropyReal r M.pDistribution)
            (relativeEntropyReal r M.qDistribution) : ℝ) : EReal) :=
    distributionKLMax_eq_coe_real_of_supported (M := M) (r := r) hp hq
  rw [htarget]
  refine (EReal.tendsto_coe.mpr hmaxtend).congr' ?_
  filter_upwards [] with n
  let rn :=
    (r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)
  have hrn : rn.SupportedBy r.prob := by
    exact ClassicalDistribution.roundedProfile_empiricalDistribution_supportedBy
      (r := r) (N := n + 1) (Nat.succ_pos n)
  have hp_rn : rn.SupportedBy M.p := hrn.trans hp
  have hq_rn : rn.SupportedBy M.q := hrn.trans hq
  exact (distributionKLMax_eq_coe_real_of_supported
    (M := M) (r := rn) hp_rn hq_rn).symm

/-- The finite-type KL dual limsup is bounded by the KL minimax objective of
any common-support distribution, via rounded empirical approximants. -/
theorem limsup_finiteTypeKLDualValue_le_distributionKLMax
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    (hp : r.SupportedBy M.p) (hq : r.SupportedBy M.q) :
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.distributionKLMax r := by
  classical
  have hpoint :
      (fun n : Nat => M.finiteTypeKLDualValue (n + 1)) ≤ᶠ[atTop]
        fun n : Nat =>
          M.distributionKLMax
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)) := by
    exact Filter.Eventually.of_forall fun n =>
      finiteTypeKLDualValue_le_roundedDistributionKLMax
        (M := M) (r := r) (N := n + 1) (Nat.succ_pos n)
  have htend :=
    distributionKLMax_roundedProfile_tendsto (M := M) (r := r) hp hq
  calc
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop
        ≤
      Filter.limsup
        (fun n : Nat =>
          M.distributionKLMax
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)))
        atTop :=
          Filter.limsup_le_limsup hpoint (β := EReal)
    _ = M.distributionKLMax r := htend.limsup_eq

/-- Finite-copy method-of-types bound through the finite-type KL dual value,
including the polynomial type-counting penalty and the equal-prior `log 2`
penalty. -/
theorem finiteTypeChernoffValue_le_finiteTypeKLDualValue_add_penalties
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N) :
    M.finiteTypeChernoffValue N ≤
      M.finiteTypeKLDualValue N +
        finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
        equalPriorAverageLogPenalty (N - 1) := by
  classical
  by_cases hprofiles : Nonempty (TensorPowerProfile α N)
  · let g : TensorPowerProfile α N → EReal := fun profile =>
      M.distributionKLMax (profile.empiricalDistribution hN)
    haveI : Nonempty (TensorPowerProfile α N) := hprofiles
    obtain ⟨profile, hprofile⟩ := exists_eq_ciInf_of_finite (f := g)
    have hdual :
        M.distributionKLMax (profile.empiricalDistribution hN) =
          M.finiteTypeKLDualValue N := by
      rw [finiteTypeKLDualValue_eq_iInf_of_pos (M := M) hN]
      exact hprofile
    have hchernoff :
        M.finiteTypeChernoffValue N ≤
          normalizedNegLog (N - 1)
            (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) := by
      unfold finiteTypeChernoffValue
      exact iInf_le _ profile
    calc
      M.finiteTypeChernoffValue N
          ≤ normalizedNegLog (N - 1)
              (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) := hchernoff
      _ ≤ M.distributionKLMax (profile.empiricalDistribution hN) +
            finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
            equalPriorAverageLogPenalty (N - 1) :=
          normalizedNegLog_profileProductErrorLowerBound_le_distributionKLMax
            (M := M) hN profile
      _ = M.finiteTypeKLDualValue N +
            finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
            equalPriorAverageLogPenalty (N - 1) := by
          rw [hdual]
  · haveI : IsEmpty (TensorPowerProfile α N) := not_nonempty_iff.mp hprofiles
    unfold finiteTypeKLDualValue finiteTypeChernoffValue
    simp [hN]
    rw [iInf_of_empty, iInf_of_empty]
    simp [finiteAlphabetMethodOfTypesPolynomialPenalty, equalPriorAverageLogPenalty]

/-- The finite-copy profile bridge reduces the classical converse to the
finite-type KL dual limsup.  The two explicit method-of-types penalties vanish:
the alphabet polynomial prefactor contributes `|α| * log(N+1) / N`, and the
equal-prior average contributes `log 2 / N`. -/
theorem finiteTypeChernoffValue_limsup_le_of_finiteTypeKLDualValue_limsup_le
    (M : ClassicalBinaryModel α)
    (hkl :
      Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance) :
    Filter.limsup
        (fun n : Nat => M.finiteTypeChernoffValue (n + 1))
        atTop ≤ M.chernoffDistance := by
  classical
  let polynomialPenalty : Nat → EReal := fun n =>
    finiteAlphabetMethodOfTypesPolynomialPenalty α n
  let priorPenalty : Nat → EReal := fun n =>
    equalPriorAverageLogPenalty n
  have hpoint :
      (fun n : Nat => M.finiteTypeChernoffValue (n + 1)) ≤ᶠ[atTop]
        fun n : Nat =>
          M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n := by
    exact Filter.Eventually.of_forall fun n => by
      simpa [polynomialPenalty, priorPenalty, Nat.add_sub_cancel] using
        finiteTypeChernoffValue_le_finiteTypeKLDualValue_add_penalties
          (M := M) (N := n + 1) (Nat.succ_pos n)
  have hpolynomial_limsup :
      Filter.limsup polynomialPenalty atTop = (0 : EReal) := by
    exact (finiteAlphabetMethodOfTypesPolynomialPenalty_tendsto_zero
      (α := α)).limsup_eq
  have hprior_limsup :
      Filter.limsup priorPenalty atTop = (0 : EReal) := by
    exact equalPriorAverageLogPenalty_tendsto_zero.limsup_eq
  have hsum1 :
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
          atTop ≤
        Filter.limsup
            (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
            atTop +
          Filter.limsup polynomialPenalty atTop := by
    simpa only [Pi.add_apply] using
      EReal.limsup_add_le
        (u := fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        (v := polynomialPenalty)
        (f := atTop)
        (Or.inr (by rw [hpolynomial_limsup]; simp))
        (Or.inr (by rw [hpolynomial_limsup]; simp))
  have hsum2 :
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n)
          atTop ≤
        Filter.limsup
            (fun n : Nat =>
              M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
            atTop +
          Filter.limsup priorPenalty atTop := by
    simpa only [Pi.add_apply] using
      EReal.limsup_add_le
        (u := fun n : Nat =>
          M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
        (v := priorPenalty)
        (f := atTop)
        (Or.inr (by rw [hprior_limsup]; simp))
        (Or.inr (by rw [hprior_limsup]; simp))
  have hbridge :=
    Filter.limsup_le_limsup hpoint (β := EReal)
      (u := fun n : Nat => M.finiteTypeChernoffValue (n + 1))
      (v := fun n : Nat =>
        M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n)
  calc
    Filter.limsup
        (fun n : Nat => M.finiteTypeChernoffValue (n + 1))
        atTop
        ≤
      Filter.limsup
        (fun n : Nat =>
          M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n)
        atTop := hbridge
    _ ≤
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
          atTop +
        Filter.limsup priorPenalty atTop := hsum2
    _ =
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
          atTop := by
        rw [hprior_limsup]
        simp
    _ ≤
      Filter.limsup
          (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
          atTop +
        Filter.limsup polynomialPenalty atTop := hsum1
    _ =
      Filter.limsup
          (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
          atTop := by
        rw [hpolynomial_limsup]
        simp
    _ ≤ M.chernoffDistance := hkl

/-- The generic method-of-types converse reduces to the finite-type KL dual
limsup bound.  This packages the pointwise type-class lower bound, the
finite-type bridge, and the vanishing polynomial/equal-prior penalties. -/
theorem methodOfTypesChernoffConverse_of_finiteTypeKLDualValue_limsup_le
    (M : ClassicalBinaryModel α)
    (hkl :
      Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance) :
    Filter.limsup
        (fun n : Nat =>
          normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal))
        atTop ≤ M.chernoffDistance := by
  classical
  have hpoint :
      (fun n : Nat =>
          normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal)) ≤ᶠ[atTop]
        fun n : Nat => M.finiteTypeChernoffValue (n + 1) := by
    exact Filter.Eventually.of_forall fun n => by
      simpa using
        normalizedNegLog_le_finiteTypeChernoffValue
          (M := M) (N := n + 1) (Nat.succ_pos n)
  have hlimsup :=
    Filter.limsup_le_limsup hpoint (β := EReal)
      (u := fun n : Nat =>
        normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal))
      (v := fun n : Nat => M.finiteTypeChernoffValue (n + 1))
  exact hlimsup.trans
    (finiteTypeChernoffValue_limsup_le_of_finiteTypeKLDualValue_limsup_le
      (M := M) hkl)

/-- Infinite Chernoff distance is the immediate support-boundary case for the
finite-type KL dual limsup. -/
theorem limsup_finiteTypeKLDualValue_le_chernoffDistance_of_eq_top
    (M : ClassicalBinaryModel α)
    (htop : M.chernoffDistance = ⊤) :
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance := by
  rw [htop]
  exact le_top

/-- The finite-type KL dual limsup is bounded by the classical Chernoff
distance.  Infinite Chernoff distance is immediate; otherwise the direct
tilted-distribution witness supplies a common-support distribution whose KL
maximum is at most the Chernoff distance. -/
theorem limsup_finiteTypeKLDualValue_le_chernoffDistance
    (M : ClassicalBinaryModel α) [DecidableEq α] :
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance := by
  classical
  by_cases htop : M.chernoffDistance = ⊤
  · exact limsup_finiteTypeKLDualValue_le_chernoffDistance_of_eq_top
      (M := M) htop
  · obtain ⟨r, hp, hq, hkl⟩ :=
      exists_distribution_klMax_le_chernoffDistance (M := M) htop
    exact
      (limsup_finiteTypeKLDualValue_le_distributionKLMax
        (M := M) (r := r) hp hq).trans hkl

/-- Generic finite-alphabet classical method-of-types Chernoff converse. -/
theorem methodOfTypesChernoffConverse
    (M : ClassicalBinaryModel α) [DecidableEq α] :
    Filter.limsup
        (fun n : Nat =>
          normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal))
        atTop ≤ M.chernoffDistance :=
  methodOfTypesChernoffConverse_of_finiteTypeKLDualValue_limsup_le
    (M := M) (limsup_finiteTypeKLDualValue_le_chernoffDistance (M := M))

end ClassicalBinaryModel

/-- Spectral probability weight of a state eigenvector. -/
def stateSpectralWeight (rho : State a) (x : a) : ℝ≥0 :=
  ⟨rho.pos.isHermitian.eigenvalues x, rho.pos.eigenvalues_nonneg x⟩

/-- Spectral weights of a density state sum to one. -/
theorem stateSpectralWeight_sum (rho : State a) :
    ∑ x : a, stateSpectralWeight rho x = 1 := by
  apply NNReal.eq
  apply Complex.ofReal_injective
  have htrace :
      (∑ x : a, ((rho.pos.isHermitian.eigenvalues x : ℝ) : ℂ)) = 1 := by
    exact rho.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans rho.trace_eq_one
  simpa [stateSpectralWeight] using htrace

/-- Transition unitary from the eigenbasis of `rho` to the eigenbasis of `sigma`. -/
def nussbaumSzkolaTransitionUnitary (rho sigma : State a) : Matrix.unitaryGroup a ℂ :=
  rho.pos.isHermitian.eigenvectorUnitary⁻¹ * sigma.pos.isHermitian.eigenvectorUnitary

/-- Nussbaum--Szkola overlap weight `|<psi_x|phi_y>|^2`. -/
def nussbaumSzkolaOverlap (rho sigma : State a) (x y : a) : ℝ≥0 :=
  ⟨Complex.normSq ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) x y),
    Complex.normSq_nonneg _⟩

/-- Nussbaum--Szkola overlap weights sum to one along each `rho` eigenvector. -/
theorem nussbaumSzkolaOverlap_row_sum (rho sigma : State a) (x : a) :
    ∑ y : a, nussbaumSzkolaOverlap rho sigma x y = 1 := by
  apply NNReal.eq
  simpa [nussbaumSzkolaOverlap] using
    unitary_row_normSq_sum_local (nussbaumSzkolaTransitionUnitary rho sigma) x

/-- Nussbaum--Szkola overlap weights sum to one along each `sigma` eigenvector. -/
theorem nussbaumSzkolaOverlap_col_sum (rho sigma : State a) (y : a) :
    ∑ x : a, nussbaumSzkolaOverlap rho sigma x y = 1 := by
  apply NNReal.eq
  simpa [nussbaumSzkolaOverlap] using
    unitary_col_normSq_sum_local (nussbaumSzkolaTransitionUnitary rho sigma) y

/-- Tensor product of a fixed one-copy unitary under the repository's
left-associated `TensorPower` convention. -/
def tensorPowerUnitary (U : Matrix.unitaryGroup a ℂ) :
    (n : Nat) → Matrix.unitaryGroup (TensorPower a n) ℂ
  | 0 => 1
  | n + 1 =>
      let Un := tensorPowerUnitary U n
      ⟨Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)),
        Matrix.kronecker_mem_unitary U.2 Un.2⟩

/-- Product spectral weight of a tensor-power eigenbasis word. -/
def tensorPowerSpectralWeight (rho : State a) :
    (n : Nat) → TensorPower a n → ℝ≥0
  | 0, _ => 1
  | n + 1, x => stateSpectralWeight rho x.1 * tensorPowerSpectralWeight rho n x.2

/-- Product Nussbaum--Szkola overlap of two tensor-power eigenbasis words. -/
def tensorPowerNussbaumSzkolaOverlap (rho sigma : State a) :
    (n : Nat) → TensorPower a n → TensorPower a n → ℝ≥0
  | 0, _, _ => 1
  | n + 1, x, y =>
      nussbaumSzkolaOverlap rho sigma x.1 y.1 *
        tensorPowerNussbaumSzkolaOverlap rho sigma n x.2 y.2

/-- Tensor powers are diagonalized by the tensor product of the one-copy
eigenbasis unitary. -/
theorem tensorPower_matrix_eq_tensorPowerUnitary_diagonal
    (rho : State a) (n : Nat) :
    (rho.tensorPower n).matrix =
      (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
          CMatrix (TensorPower a n)) *
        Matrix.diagonal
          (fun x : TensorPower a n => (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)) *
          star
            (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
              CMatrix (TensorPower a n)) := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [State.tensorPower, State.unit, tensorPowerUnitary,
        tensorPowerSpectralWeight, Matrix.diagonal, Matrix.mul_apply,
        Matrix.one_apply]
  | succ n ih =>
      let U : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
      let Un : Matrix.unitaryGroup (TensorPower a n) ℂ := tensorPowerUnitary U n
      let D : CMatrix a :=
        Matrix.diagonal fun x : a => (((stateSpectralWeight rho x : ℝ≥0) : ℝ) : ℂ)
      let Dn : CMatrix (TensorPower a n) :=
        Matrix.diagonal fun x : TensorPower a n =>
          (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)
      have hrho :
          rho.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
        simpa [U, D, stateSpectralWeight, Unitary.conjStarAlgAut_apply]
          using rho.pos.isHermitian.spectral_theorem
      change Matrix.kronecker rho.matrix (rho.tensorPower n).matrix =
        (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))) *
          Matrix.diagonal
            (fun x : Prod a (TensorPower a n) =>
              ((((stateSpectralWeight rho x.1 *
                tensorPowerSpectralWeight rho n x.2 : ℝ≥0) : ℝ)) : ℂ)) *
            star (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)))
      rw [hrho, ih]
      simp [U, Un, D,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
        Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]

/-- Product Nussbaum--Szkola overlaps are squared transition amplitudes between
the tensor-product eigenbases. -/
theorem tensorPowerNussbaumSzkolaOverlap_eq_normSq
    (rho sigma : State a) (n : Nat) (x y : TensorPower a n) :
    (tensorPowerNussbaumSzkolaOverlap rho sigma n x y : ℝ) =
      Complex.normSq
        ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
            CMatrix (TensorPower a n)) *
          (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
            CMatrix (TensorPower a n))) x y) := by
  induction n with
  | zero =>
      cases x
      cases y
      simp [tensorPowerUnitary, tensorPowerNussbaumSzkolaOverlap, Matrix.mul_apply,
        Matrix.one_apply]
      change (1 : ℝ) = Complex.normSq (1 : ℂ)
      norm_num [Complex.normSq]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rcases y with ⟨y0, ys⟩
      let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
      let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
      let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ := tensorPowerUnitary Urho n
      let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ := tensorPowerUnitary Usigma n
      have hentry :
          ((star (Matrix.kronecker (Urho : CMatrix a) (UrhoN : CMatrix (TensorPower a n))) *
              Matrix.kronecker (Usigma : CMatrix a) (UsigmaN : CMatrix (TensorPower a n)))
              (x0, xs) (y0, ys)) =
            ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) *
              ((star (UrhoN : CMatrix (TensorPower a n)) *
                (UsigmaN : CMatrix (TensorPower a n))) xs ys) := by
        have hstar :
            star (Matrix.kronecker (Urho : CMatrix a)
                (UrhoN : CMatrix (TensorPower a n))) =
              Matrix.kronecker (star (Urho : CMatrix a))
                (star (UrhoN : CMatrix (TensorPower a n))) := by
          ext i j
          simp [Matrix.star_apply]
        rw [hstar]
        have hmul :
            Matrix.kronecker (star (Urho : CMatrix a))
                (star (UrhoN : CMatrix (TensorPower a n))) *
              Matrix.kronecker (Usigma : CMatrix a)
                (UsigmaN : CMatrix (TensorPower a n)) =
            Matrix.kronecker (star (Urho : CMatrix a) * (Usigma : CMatrix a))
              (star (UrhoN : CMatrix (TensorPower a n)) *
                (UsigmaN : CMatrix (TensorPower a n))) := by
          simpa [Matrix.kronecker] using
            (Matrix.mul_kronecker_mul
              (star (Urho : CMatrix a)) (Usigma : CMatrix a)
              (star (UrhoN : CMatrix (TensorPower a n)))
              (UsigmaN : CMatrix (TensorPower a n))).symm
        rw [hmul]
        simp
      change
        ((nussbaumSzkolaOverlap rho sigma x0 y0 *
            tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ≥0) : ℝ) =
          Complex.normSq
            ((star (Matrix.kronecker (Urho : CMatrix a)
                (UrhoN : CMatrix (TensorPower a n))) *
              Matrix.kronecker (Usigma : CMatrix a)
                (UsigmaN : CMatrix (TensorPower a n))) (x0, xs) (y0, ys))
      rw [hentry, Complex.normSq_mul]
      have hoverlap :
          (nussbaumSzkolaOverlap rho sigma x0 y0 : ℝ) =
            Complex.normSq ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) := by
        simp only [nussbaumSzkolaOverlap, nussbaumSzkolaTransitionUnitary, Urho, Usigma,
          Matrix.star_eq_conjTranspose]
        rfl
      calc
        ((nussbaumSzkolaOverlap rho sigma x0 y0 *
            tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ≥0) : ℝ) =
            (nussbaumSzkolaOverlap rho sigma x0 y0 : ℝ) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ) := by
              simp
        _ =
            Complex.normSq ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ) := by
              rw [hoverlap]
        _ =
            Complex.normSq ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) *
              Complex.normSq
                ((star (UrhoN : CMatrix (TensorPower a n)) *
                  (UsigmaN : CMatrix (TensorPower a n))) xs ys) := by
              rw [ih xs ys]

omit [Fintype a] in
private theorem projection_complement_isHermitian {P : CMatrix a}
    (hPherm : P.IsHermitian) :
    (1 - P).IsHermitian :=
  Matrix.isHermitian_one.sub hPherm

private theorem projection_complement_idempotent {P : CMatrix a}
    (hPidem : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  calc
    (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by rw [hPidem]; abel

private theorem hermitian_projection_bridge_normSq_symm {P : CMatrix a}
    (hPherm : P.IsHermitian)
    (U V : Matrix.unitaryGroup a ℂ) (x y : a) :
    Complex.normSq ((star (V : CMatrix a) * P * (U : CMatrix a)) y x) =
      Complex.normSq ((star (U : CMatrix a) * P * (V : CMatrix a)) x y) := by
  have hmatrix :
      star (star (U : CMatrix a) * P * (V : CMatrix a)) =
        star (V : CMatrix a) * P * (U : CMatrix a) := by
    simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [hPherm]
  have hentry := congrFun (congrFun hmatrix y) x
  rw [← hentry]
  simp [Complex.normSq]

private theorem state_trace_one_sub_projection_re_eq_nussbaumSzkola_source_sum
    (rho sigma : State a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    ((rho.matrix * (1 - P)).trace).re =
      ∑ x : a, (stateSpectralWeight rho x : ℝ) *
        ∑ y : a,
          Complex.normSq
            ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                (1 - P) * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  have htrace :=
    posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
      (M := rho.matrix) (B := 1 - P) rho.pos
  calc
    ((rho.matrix * (1 - P)).trace).re =
        ∑ x : a, (stateSpectralWeight rho x : ℝ) *
          ((star (Urho : CMatrix a) * (1 - P) * (Urho : CMatrix a)) x x).re := by
          simpa [Urho, stateSpectralWeight] using htrace
    _ = ∑ x : a, (stateSpectralWeight rho x : ℝ) *
          ∑ y : a,
            Complex.normSq
              ((star (Urho : CMatrix a) * (1 - P) * (Usigma : CMatrix a)) x y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := 1 - P)
            (projection_complement_isHermitian hPherm)
            (projection_complement_idempotent hPidem)
            Urho Usigma x]
    _ = ∑ x : a, (stateSpectralWeight rho x : ℝ) *
          ∑ y : a,
            Complex.normSq
              ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                  (1 - P) * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
          rfl

private theorem state_trace_projection_re_eq_nussbaumSzkola_source_sum
    (rho sigma : State a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    ((sigma.matrix * P).trace).re =
      ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
        ∑ x : a,
          Complex.normSq
            ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                P * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  have htrace :=
    posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
      (M := sigma.matrix) (B := P) sigma.pos
  calc
    ((sigma.matrix * P).trace).re =
        ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ((star (Usigma : CMatrix a) * P * (Usigma : CMatrix a)) y y).re := by
          simpa [Usigma, stateSpectralWeight] using htrace
    _ = ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ∑ x : a,
            Complex.normSq
              ((star (Usigma : CMatrix a) * P * (Urho : CMatrix a)) y x) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := P) hPherm hPidem Usigma Urho y]
    _ = ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ∑ x : a,
            Complex.normSq
              ((star (Urho : CMatrix a) * P * (Usigma : CMatrix a)) x y) := by
          apply Finset.sum_congr rfl
          intro y _
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [hermitian_projection_bridge_normSq_symm hPherm Urho Usigma x y]
    _ = ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ∑ x : a,
            Complex.normSq
              ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                  P * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
          rfl

/-- The Nussbaum--Szkola finite classical model
`p_xy = p_x |<psi_x|phi_y>|^2`,
`q_xy = q_y |<psi_x|phi_y>|^2`. -/
def nussbaumSzkolaModel (rho sigma : State a) : ClassicalBinaryModel (a × a) where
  p xy := stateSpectralWeight rho xy.1 * nussbaumSzkolaOverlap rho sigma xy.1 xy.2
  q xy := stateSpectralWeight sigma xy.2 * nussbaumSzkolaOverlap rho sigma xy.1 xy.2
  p_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : a, ∑ y : a,
          stateSpectralWeight rho x * nussbaumSzkolaOverlap rho sigma x y)
          = ∑ x : a, stateSpectralWeight rho x *
              (∑ y : a, nussbaumSzkolaOverlap rho sigma x y) := by
            simp [Finset.mul_sum]
      _ = ∑ x : a, stateSpectralWeight rho x := by
            simp [nussbaumSzkolaOverlap_row_sum]
      _ = 1 := stateSpectralWeight_sum rho
  q_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : a, ∑ y : a,
          stateSpectralWeight sigma y * nussbaumSzkolaOverlap rho sigma x y)
          = ∑ y : a, ∑ x : a,
              stateSpectralWeight sigma y * nussbaumSzkolaOverlap rho sigma x y := by
            rw [Finset.sum_comm]
      _ = ∑ y : a, stateSpectralWeight sigma y *
              (∑ x : a, nussbaumSzkolaOverlap rho sigma x y) := by
            simp [Finset.mul_sum]
      _ = ∑ y : a, stateSpectralWeight sigma y := by
            simp [nussbaumSzkolaOverlap_col_sum]
      _ = 1 := stateSpectralWeight_sum sigma

private theorem nussbaumSzkolaModel_petzChernoffCoefficient_term
    (p q r : ℝ≥0) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (p * r) ^ s * (q * r) ^ (1 - s) =
      p ^ s * q ^ (1 - s) * r := by
  have hs1' : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  calc
    (p * r) ^ s * (q * r) ^ (1 - s) =
        (p ^ s * r ^ s) * (q ^ (1 - s) * r ^ (1 - s)) := by
          rw [NNReal.mul_rpow, NNReal.mul_rpow]
    _ = p ^ s * q ^ (1 - s) * (r ^ s * r ^ (1 - s)) := by
          ac_rfl
    _ = p ^ s * q ^ (1 - s) * r ^ (s + (1 - s)) := by
          rw [NNReal.rpow_add_of_nonneg r hs0 hs1']
    _ = p ^ s * q ^ (1 - s) * r := by
          have hsum : s + (1 - s) = 1 := by ring
          rw [hsum, NNReal.rpow_one]

/-- Nussbaum--Szkola classical Chernoff coefficient equals the quantum Petz
Chernoff coefficient.  The exponent convention matches
`State.petzRenyiCoefficient`, namely `Tr(ρ^s σ^(1-s))`
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
theorem nussbaumSzkolaModel_petzChernoffCoefficient_eq
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (nussbaumSzkolaModel rho sigma).petzChernoffCoefficient s =
      rho.petzRenyiCoefficient sigma s := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  have hrho :
      CFC.rpow rho.matrix s =
        (Urho : CMatrix a) *
          Matrix.diagonal (fun x => (((stateSpectralWeight rho x : ℝ) ^ s : ℝ) : ℂ)) *
            star (Urho : CMatrix a) := by
    simpa [Urho, stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal rho.pos s
  have hsigma :
      CFC.rpow sigma.matrix (1 - s) =
        (Usigma : CMatrix a) *
          Matrix.diagonal
            (fun y => (((stateSpectralWeight sigma y : ℝ) ^ (1 - s) : ℝ) : ℂ)) *
            star (Usigma : CMatrix a) := by
    simpa [Usigma, stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal sigma.pos (1 - s)
  have htrace :
      (rho.petzRenyiCoefficient sigma s : ℝ) =
        ∑ x : a, ∑ y : a,
          ((stateSpectralWeight rho x : ℝ) ^ s) *
            ((stateSpectralWeight sigma y : ℝ) ^ (1 - s)) *
              (nussbaumSzkolaOverlap rho sigma x y : ℝ) := by
    change ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re = _
    rw [hrho, hsigma]
    simpa [Urho, Usigma, nussbaumSzkolaOverlap, nussbaumSzkolaTransitionUnitary,
      Matrix.star_eq_conjTranspose, mul_assoc, mul_left_comm, mul_comm] using
      trace_mul_two_unitary_conj_diagonal_ofReal_re
        Urho Usigma
        (fun x : a => (stateSpectralWeight rho x : ℝ) ^ s)
        (fun y : a => (stateSpectralWeight sigma y : ℝ) ^ (1 - s))
  apply NNReal.eq
  calc
    ((nussbaumSzkolaModel rho sigma).petzChernoffCoefficient s : ℝ) =
        ∑ xy : a × a,
          (((stateSpectralWeight rho xy.1) ^ s *
            (stateSpectralWeight sigma xy.2) ^ (1 - s) *
              nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ≥0) : ℝ) := by
          simp [ClassicalBinaryModel.petzChernoffCoefficient, nussbaumSzkolaModel,
            nussbaumSzkolaModel_petzChernoffCoefficient_term _ _ _ hs0 hs1,
            mul_assoc]
    _ = ∑ x : a, ∑ y : a,
          ((stateSpectralWeight rho x : ℝ) ^ s) *
            ((stateSpectralWeight sigma y : ℝ) ^ (1 - s)) *
              (nussbaumSzkolaOverlap rho sigma x y : ℝ) := by
          rw [Fintype.sum_prod_type]
          simp [NNReal.coe_rpow, mul_assoc]
    _ = (rho.petzRenyiCoefficient sigma s : ℝ) := htrace.symm

/-- The one-copy Nussbaum--Szkola classical Chernoff distance matches the
quantum Chernoff distance. -/
theorem nussbaumSzkolaModel_chernoffDistance_eq
    (rho sigma : State a) :
    (nussbaumSzkolaModel rho sigma).chernoffDistance =
      rho.chernoffDistance sigma := by
  unfold ClassicalBinaryModel.chernoffDistance State.chernoffDistance
  apply iSup_congr
  intro s
  simp [ClassicalBinaryModel.chernoffExponent, State.petzChernoffExponent,
    nussbaumSzkolaModel_petzChernoffCoefficient_eq rho sigma s.2.1 s.2.2]

/-- Genuine product Nussbaum--Szkola classical model over the `n`-fold product
alphabet `(a × a)^n`. -/
def nussbaumSzkolaProductModel (rho sigma : State a) (n : Nat) :
    ClassicalBinaryModel (TensorPower (a × a) n) :=
  (nussbaumSzkolaModel rho sigma).tensorPower n

/-- Equal-prior Bayesian error of the genuine product Nussbaum--Szkola
classical model. -/
def nussbaumSzkolaProductClassicalError (rho sigma : State a) (n : Nat) : ℝ≥0∞ :=
  (nussbaumSzkolaProductModel rho sigma n).equalPriorErrorENNReal

/-- The canonical product Nussbaum--Szkola `p` distribution is the product
spectral weight times the product transition overlap. -/
theorem nussbaumSzkolaProductModel_p_eq
    (rho sigma : State a) (n : Nat) (x y : TensorPower a n) :
    (nussbaumSzkolaProductModel rho sigma n).p
        ((tensorPowerProdEquiv a a n).symm (x, y)) =
      tensorPowerSpectralWeight rho n x *
        tensorPowerNussbaumSzkolaOverlap rho sigma n x y := by
  induction n with
  | zero =>
      cases x
      cases y
      simp [nussbaumSzkolaProductModel, ClassicalBinaryModel.tensorPower,
        tensorPowerProdEquiv, tensorPowerSpectralWeight,
        tensorPowerNussbaumSzkolaOverlap]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rcases y with ⟨y0, ys⟩
      change
        (stateSpectralWeight rho x0 * nussbaumSzkolaOverlap rho sigma x0 y0) *
            (nussbaumSzkolaProductModel rho sigma n).p
              ((tensorPowerProdEquiv a a n).symm (xs, ys)) =
          (stateSpectralWeight rho x0 * tensorPowerSpectralWeight rho n xs) *
            (nussbaumSzkolaOverlap rho sigma x0 y0 *
              tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys)
      rw [ih xs ys]
      ac_rfl

/-- The canonical product Nussbaum--Szkola `q` distribution is the product
sigma spectral weight times the product transition overlap. -/
theorem nussbaumSzkolaProductModel_q_eq
    (rho sigma : State a) (n : Nat) (x y : TensorPower a n) :
    (nussbaumSzkolaProductModel rho sigma n).q
        ((tensorPowerProdEquiv a a n).symm (x, y)) =
      tensorPowerSpectralWeight sigma n y *
        tensorPowerNussbaumSzkolaOverlap rho sigma n x y := by
  induction n with
  | zero =>
      cases x
      cases y
      simp [nussbaumSzkolaProductModel, ClassicalBinaryModel.tensorPower,
        tensorPowerProdEquiv, tensorPowerSpectralWeight,
        tensorPowerNussbaumSzkolaOverlap]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rcases y with ⟨y0, ys⟩
      change
        (stateSpectralWeight sigma y0 * nussbaumSzkolaOverlap rho sigma x0 y0) *
            (nussbaumSzkolaProductModel rho sigma n).q
              ((tensorPowerProdEquiv a a n).symm (xs, ys)) =
          (stateSpectralWeight sigma y0 * tensorPowerSpectralWeight sigma n ys) *
            (nussbaumSzkolaOverlap rho sigma x0 y0 *
              tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys)
      rw [ih xs ys]
      ac_rfl

/-- Source-shaped finite comparison obligation for the genuine product
Nussbaum--Szkola classical sequence.

Unlike `HasNussbaumSzkolaFiniteComparison`, this predicate does not force the
classical sequence to be the spectral Nussbaum--Szkola model of tensor-power
states.  It pins the sequence to the canonical product model over
`(a × a)^n`, avoiding noncanonical choices in degenerate tensor-power
eigenspaces [Gour2024Resources, BookQRT.tex:15911-15949]. -/
def HasNussbaumSzkolaProductFiniteComparison
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  classicalError = nussbaumSzkolaProductClassicalError rho sigma ∧
    ∀ n : Nat,
      quantumChernoffConverseComparisonConstant * classicalError n ≤
        optimalEqualPriorTensorPowerError rho sigma n

/-- Product Nussbaum--Szkola models have multiplicative classical Petz/Chernoff
coefficient. -/
theorem nussbaumSzkolaProductModel_petzChernoffCoefficient_eq_pow
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    (nussbaumSzkolaProductModel rho sigma n).petzChernoffCoefficient s =
      rho.petzRenyiCoefficient sigma s ^ n := by
  calc
    (nussbaumSzkolaProductModel rho sigma n).petzChernoffCoefficient s =
        (nussbaumSzkolaModel rho sigma).petzChernoffCoefficient s ^ n := by
          exact ClassicalBinaryModel.tensorPower_petzChernoffCoefficient
            (nussbaumSzkolaModel rho sigma) s n
    _ = rho.petzRenyiCoefficient sigma s ^ n := by
          rw [nussbaumSzkolaModel_petzChernoffCoefficient_eq rho sigma hs0 hs1]

theorem tensorPower_trace_one_sub_projection_re_eq_nussbaumSzkolaProduct_source_sum
    (rho sigma : State a) (n : Nat) {P : CMatrix (TensorPower a n)}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (((rho.tensorPower n).matrix * (1 - P)).trace).re =
      ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
        ∑ y : TensorPower a n,
          Complex.normSq
            ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n)) *
                (1 - P) *
              (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n))) x y) := by
  classical
  let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n
  let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n
  have hdiag := tensorPower_matrix_eq_tensorPowerUnitary_diagonal rho n
  have htrace :=
    trace_mul_unitary_conj_diagonal_ofReal_arbitrary_re
      UrhoN (fun x : TensorPower a n => (tensorPowerSpectralWeight rho n x : ℝ))
      (1 - P)
  calc
    (((rho.tensorPower n).matrix * (1 - P)).trace).re =
        ((((UrhoN : CMatrix (TensorPower a n)) *
            (Matrix.diagonal
              fun x : TensorPower a n =>
                (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)) *
              star (UrhoN : CMatrix (TensorPower a n))) *
            (1 - P)).trace).re := by
          rw [hdiag]
    _ = ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
          ((star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
            (UrhoN : CMatrix (TensorPower a n))) x x).re := by
          simpa [UrhoN] using htrace
    _ = ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
          ∑ y : TensorPower a n,
            Complex.normSq
              ((star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
                (UsigmaN : CMatrix (TensorPower a n))) x y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := 1 - P)
            (projection_complement_isHermitian hPherm)
            (projection_complement_idempotent hPidem)
            UrhoN UsigmaN x]
    _ = ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
          ∑ y : TensorPower a n,
            Complex.normSq
              ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n)) *
                  (1 - P) *
                (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n))) x y) := by
          rfl

theorem tensorPower_trace_projection_re_eq_nussbaumSzkolaProduct_source_sum
    (rho sigma : State a) (n : Nat) {P : CMatrix (TensorPower a n)}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (((sigma.tensorPower n).matrix * P).trace).re =
      ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
        ∑ x : TensorPower a n,
          Complex.normSq
            ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n)) *
                P *
              (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n))) x y) := by
  classical
  let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n
  let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n
  have hdiag := tensorPower_matrix_eq_tensorPowerUnitary_diagonal sigma n
  have htrace :=
    trace_mul_unitary_conj_diagonal_ofReal_arbitrary_re
      UsigmaN (fun y : TensorPower a n => (tensorPowerSpectralWeight sigma n y : ℝ))
      P
  calc
    (((sigma.tensorPower n).matrix * P).trace).re =
        ((((UsigmaN : CMatrix (TensorPower a n)) *
            (Matrix.diagonal
              fun y : TensorPower a n =>
                (((tensorPowerSpectralWeight sigma n y : ℝ≥0) : ℝ) : ℂ)) *
              star (UsigmaN : CMatrix (TensorPower a n))) *
            P).trace).re := by
          rw [hdiag]
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ((star (UsigmaN : CMatrix (TensorPower a n)) * P *
            (UsigmaN : CMatrix (TensorPower a n))) y y).re := by
          simpa [UsigmaN] using htrace
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ∑ x : TensorPower a n,
            Complex.normSq
              ((star (UsigmaN : CMatrix (TensorPower a n)) * P *
                (UrhoN : CMatrix (TensorPower a n))) y x) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := P) hPherm hPidem UsigmaN UrhoN y]
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ∑ x : TensorPower a n,
            Complex.normSq
              ((star (UrhoN : CMatrix (TensorPower a n)) * P *
                (UsigmaN : CMatrix (TensorPower a n))) x y) := by
          apply Finset.sum_congr rfl
          intro y _
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [hermitian_projection_bridge_normSq_symm hPherm UrhoN UsigmaN x y]
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ∑ x : TensorPower a n,
            Complex.normSq
              ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n)) *
                  P *
                (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n))) x y) := by
          rfl

/-- Finite projection comparison for the canonical product Nussbaum--Szkola
sequence, with Gour's exact `1 / 2` constant. -/
theorem half_nussbaumSzkolaProductModel_equalPriorError_le_projection_error
    (rho sigma : State a) (n : Nat) {P : CMatrix (TensorPower a n)}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
      (1 / 2 : ℝ) *
        ((((rho.tensorPower n).matrix * (1 - P)).trace).re +
          (((sigma.tensorPower n).matrix * P).trace).re) := by
  classical
  let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n
  let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n
  let rejectAmp : TensorPower a n × TensorPower a n → ℂ := fun xy =>
    (star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
      (UsigmaN : CMatrix (TensorPower a n))) xy.1 xy.2
  let acceptAmp : TensorPower a n × TensorPower a n → ℂ := fun xy =>
    (star (UrhoN : CMatrix (TensorPower a n)) * P *
      (UsigmaN : CMatrix (TensorPower a n))) xy.1 xy.2
  let rhsDouble : ℝ :=
    ∑ xy : TensorPower a n × TensorPower a n,
      (((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
          Complex.normSq (rejectAmp xy) +
        ((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
          Complex.normSq (acceptAmp xy))
  have hentry_sum (xy : TensorPower a n × TensorPower a n) :
      rejectAmp xy + acceptAmp xy =
        ((star (UrhoN : CMatrix (TensorPower a n)) *
          (UsigmaN : CMatrix (TensorPower a n))) xy.1 xy.2) := by
    have hmat :
        star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
            (UsigmaN : CMatrix (TensorPower a n)) +
          star (UrhoN : CMatrix (TensorPower a n)) * P *
            (UsigmaN : CMatrix (TensorPower a n)) =
          star (UrhoN : CMatrix (TensorPower a n)) *
            (UsigmaN : CMatrix (TensorPower a n)) := by
      noncomm_ring
    have hentry := congrFun (congrFun hmat xy.1) xy.2
    simpa [rejectAmp, acceptAmp] using hentry
  have hterm (xy : TensorPower a n × TensorPower a n) :
      (1 / 2 : ℝ) *
          min
            (((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ))
            (((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ)) ≤
        ((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
            Complex.normSq (rejectAmp xy) +
          ((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
            Complex.normSq (acceptAmp xy) := by
    have hnorm :
        (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ) ≤
          2 * (Complex.normSq (rejectAmp xy) + Complex.normSq (acceptAmp xy)) := by
      have h := complex_normSq_add_le_two_sum (rejectAmp xy) (acceptAmp xy)
      rw [hentry_sum xy] at h
      simpa [UrhoN, UsigmaN, tensorPowerNussbaumSzkolaOverlap_eq_normSq]
        using h
    exact half_min_weight_normSq_add_le_weighted_normSq
      (by positivity) (by positivity)
      (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      (by positivity) hnorm
  have hlhs_le_rhsDouble :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        rhsDouble := by
    let e := tensorPowerProdEquiv a a n
    calc
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) =
          ∑ z : TensorPower (a × a) n,
            (1 / 2 : ℝ) *
              min
                (((1 / 2 : ℝ) *
                  ((nussbaumSzkolaProductModel rho sigma n).p z : ℝ)))
                (((1 / 2 : ℝ) *
                  ((nussbaumSzkolaProductModel rho sigma n).q z : ℝ))) := by
            simp [ClassicalBinaryModel.equalPriorError, Finset.mul_sum]
      _ = ∑ xy : TensorPower a n × TensorPower a n,
            (1 / 2 : ℝ) *
              min
                (((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
                  (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ))
                (((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
                  (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ)) := by
            refine Fintype.sum_equiv e _ _ ?_
            intro z
            have hp :=
              nussbaumSzkolaProductModel_p_eq rho sigma n (e z).1 (e z).2
            have hq :=
              nussbaumSzkolaProductModel_q_eq rho sigma n (e z).1 (e z).2
            have hz :
                (tensorPowerProdEquiv a a n).symm ((e z).1, (e z).2) = z := by
              exact e.left_inv z
            conv_lhs => rw [← hz]
            rw [hp, hq]
            apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
            apply congrArg₂ min <;> simp [NNReal.coe_mul, mul_assoc]
      _ ≤ rhsDouble := by
            unfold rhsDouble
            exact Finset.sum_le_sum fun xy _ => hterm xy
  have htrace_rho :=
    tensorPower_trace_one_sub_projection_re_eq_nussbaumSzkolaProduct_source_sum
      rho sigma n hPherm hPidem
  have htrace_sigma :=
    tensorPower_trace_projection_re_eq_nussbaumSzkolaProduct_source_sum
      rho sigma n hPherm hPidem
  have hrhsDouble :
      rhsDouble =
        (1 / 2 : ℝ) *
          ((((rho.tensorPower n).matrix * (1 - P)).trace).re +
            (((sigma.tensorPower n).matrix * P).trace).re) := by
    let rhoPart : ℝ := ∑ xy : TensorPower a n × TensorPower a n,
      ((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
        Complex.normSq (rejectAmp xy)
    let sigmaPart : ℝ := ∑ xy : TensorPower a n × TensorPower a n,
      ((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
        Complex.normSq (acceptAmp xy)
    have hrhs_split : rhsDouble = rhoPart + sigmaPart := by
      unfold rhsDouble rhoPart sigmaPart
      rw [Finset.sum_add_distrib]
    have hrhoPart :
        rhoPart = (1 / 2 : ℝ) *
          (((rho.tensorPower n).matrix * (1 - P)).trace).re := by
      calc
        rhoPart =
            (1 / 2 : ℝ) *
              (∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
                ∑ y : TensorPower a n, Complex.normSq (rejectAmp (x, y))) := by
              unfold rhoPart
              rw [Fintype.sum_prod_type]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) *
              (((rho.tensorPower n).matrix * (1 - P)).trace).re := by
              rw [htrace_rho]
    have hsigmaPart :
        sigmaPart = (1 / 2 : ℝ) *
          (((sigma.tensorPower n).matrix * P).trace).re := by
      calc
        sigmaPart =
            (1 / 2 : ℝ) *
              (∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
                ∑ x : TensorPower a n, Complex.normSq (acceptAmp (x, y))) := by
              unfold sigmaPart
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) *
              (((sigma.tensorPower n).matrix * P).trace).re := by
              rw [htrace_sigma]
    rw [hrhs_split, hrhoPart, hsigmaPart]
    ring
  exact hlhs_le_rhsDouble.trans_eq hrhsDouble

private theorem half_nussbaumSzkolaModel_equalPriorError_le_projection_error
    (rho sigma : State a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (1 / 2 : ℝ) * ((nussbaumSzkolaModel rho sigma).equalPriorError : ℝ) ≤
      (1 / 2 : ℝ) *
        (((rho.matrix * (1 - P)).trace).re + ((sigma.matrix * P).trace).re) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  let rejectAmp : a × a → ℂ := fun xy =>
    (star (Urho : CMatrix a) * (1 - P) * (Usigma : CMatrix a)) xy.1 xy.2
  let acceptAmp : a × a → ℂ := fun xy =>
    (star (Urho : CMatrix a) * P * (Usigma : CMatrix a)) xy.1 xy.2
  let rhsDouble : ℝ :=
    ∑ xy : a × a,
      (((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
          Complex.normSq (rejectAmp xy) +
        ((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
          Complex.normSq (acceptAmp xy))
  have hentry_sum (xy : a × a) :
      rejectAmp xy + acceptAmp xy =
        ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) xy.1 xy.2) := by
    have hmat :
        star (Urho : CMatrix a) * (1 - P) * (Usigma : CMatrix a) +
            star (Urho : CMatrix a) * P * (Usigma : CMatrix a) =
          star (Urho : CMatrix a) * (Usigma : CMatrix a) := by
      noncomm_ring
    have hentry := congrFun (congrFun hmat xy.1) xy.2
    simpa [rejectAmp, acceptAmp, Urho, Usigma, nussbaumSzkolaTransitionUnitary,
      Matrix.star_eq_conjTranspose] using hentry
  have hterm (xy : a × a) :
      (1 / 2 : ℝ) *
          min
            (((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
              (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ))
            (((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
              (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ)) ≤
        ((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
            Complex.normSq (rejectAmp xy) +
          ((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
            Complex.normSq (acceptAmp xy) := by
    have hnorm :
        (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ) ≤
          2 * (Complex.normSq (rejectAmp xy) + Complex.normSq (acceptAmp xy)) := by
      have h := complex_normSq_add_le_two_sum (rejectAmp xy) (acceptAmp xy)
      rw [hentry_sum xy] at h
      simpa [nussbaumSzkolaOverlap] using h
    exact half_min_weight_normSq_add_le_weighted_normSq
      (by positivity) (by positivity)
      (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      (by positivity) hnorm
  have hlhs_le_rhsDouble :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rho sigma).equalPriorError : ℝ) ≤
        rhsDouble := by
    calc
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rho sigma).equalPriorError : ℝ) =
          ∑ xy : a × a,
            (1 / 2 : ℝ) *
              min
                (((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
                  (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ))
                (((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
                  (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ)) := by
            simp [ClassicalBinaryModel.equalPriorError, nussbaumSzkolaModel,
              Finset.mul_sum, mul_left_comm, mul_comm]
      _ ≤ rhsDouble := by
            unfold rhsDouble
            exact Finset.sum_le_sum fun xy _ => hterm xy
  have htrace_rho :=
    state_trace_one_sub_projection_re_eq_nussbaumSzkola_source_sum
      rho sigma hPherm hPidem
  have htrace_sigma :=
    state_trace_projection_re_eq_nussbaumSzkola_source_sum
      rho sigma hPherm hPidem
  have hrhsDouble :
      rhsDouble =
        (1 / 2 : ℝ) *
          (((rho.matrix * (1 - P)).trace).re + ((sigma.matrix * P).trace).re) := by
    let rhoPart : ℝ := ∑ xy : a × a,
      ((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
        Complex.normSq (rejectAmp xy)
    let sigmaPart : ℝ := ∑ xy : a × a,
      ((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
        Complex.normSq (acceptAmp xy)
    have hrhs_split : rhsDouble = rhoPart + sigmaPart := by
      unfold rhsDouble rhoPart sigmaPart
      rw [Finset.sum_add_distrib]
    have hrhoPart :
        rhoPart = (1 / 2 : ℝ) * ((rho.matrix * (1 - P)).trace).re := by
      calc
        rhoPart =
            (1 / 2 : ℝ) *
              (∑ x : a, (stateSpectralWeight rho x : ℝ) *
                ∑ y : a, Complex.normSq (rejectAmp (x, y))) := by
              unfold rhoPart
              rw [Fintype.sum_prod_type]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) * ((rho.matrix * (1 - P)).trace).re := by
              rw [htrace_rho]
    have hsigmaPart :
        sigmaPart = (1 / 2 : ℝ) * ((sigma.matrix * P).trace).re := by
      calc
        sigmaPart =
            (1 / 2 : ℝ) *
              (∑ y : a, (stateSpectralWeight sigma y : ℝ) *
                ∑ x : a, Complex.normSq (acceptAmp (x, y))) := by
              unfold sigmaPart
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) * ((sigma.matrix * P).trace).re := by
              rw [htrace_sigma]
    rw [hrhs_split, hrhoPart, hsigmaPart]
    ring
  exact hlhs_le_rhsDouble.trans_eq hrhsDouble

private theorem half_trace_accept_effect_error_eq_equalPriorError
    (T : BinaryHypothesisTest a) (rho sigma : State a) :
    (1 / 2 : ℝ) *
        (((rho.matrix * (1 - T.acceptRhoEffect)).trace).re +
          ((sigma.matrix * T.acceptRhoEffect).trace).re) =
      (T.equalPriorError rho sigma : ℝ) := by
  have hreject_trace :
      ((rho.matrix * (1 - T.acceptRhoEffect)).trace).re =
        (T.rejectProb rho : ℝ) := by
    rw [← T.rejectRhoEffect_eq_one_sub_acceptRhoEffect]
    exact (T.rejectProb_eq_trace_re rho).symm
  have haccept_trace :
      ((sigma.matrix * T.acceptRhoEffect).trace).re =
        (T.acceptProb sigma : ℝ) :=
    (T.acceptProb_eq_trace_re sigma).symm
  rw [hreject_trace, haccept_trace]
  unfold BinaryHypothesisTest.equalPriorError BinaryHypothesisTest.typeIError
    BinaryHypothesisTest.typeIIError
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat]
  ring

/-- The Nussbaum--Szkola classical error sequence for tensor powers.

At copy number `n`, this uses the spectral Nussbaum--Szkola model associated to
`rho^⊗n` and `sigma^⊗n`. -/
def nussbaumSzkolaClassicalError (rho sigma : State a) (n : Nat) : ℝ≥0∞ :=
  (nussbaumSzkolaModel (rho.tensorPower n) (sigma.tensorPower n)).equalPriorErrorENNReal

/-- The classical error sequence is the tensor-power Nussbaum--Szkola sequence. -/
def HasNussbaumSzkolaTensorPowerCompatibility
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  classicalError = nussbaumSzkolaClassicalError rho sigma

/-- The canonical Nussbaum--Szkola classical error sequence satisfies the
tensor-power compatibility convention by definition. -/
theorem nussbaumSzkolaClassicalError_tensorPowerCompatible (rho sigma : State a) :
    HasNussbaumSzkolaTensorPowerCompatibility
      rho sigma (nussbaumSzkolaClassicalError rho sigma) :=
  rfl

/-- Source-shaped finite Nussbaum--Szkola comparison obligation.

The first field pins the sequence to the tensor-power Nussbaum--Szkola
construction.  The second field is the finite quantum-to-classical comparison
with the source's `1 / 2` constant. -/
def HasNussbaumSzkolaFiniteComparison
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  HasNussbaumSzkolaTensorPowerCompatibility rho sigma classicalError ∧
    ∀ n : Nat,
      quantumChernoffConverseComparisonConstant * classicalError n ≤
        optimalEqualPriorTensorPowerError rho sigma n

/-- Source-shaped finite-copy quantum-to-classical comparison for the QCB converse.

The predicate states the reusable finite-`n` estimate supplied by the
Nussbaum--Szkola construction: the quantum optimal equal-prior tensor-power
error dominates one half of a corresponding classical error sequence
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
def HasQuantumToClassicalChernoffComparison
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  ∀ n : Nat,
    quantumChernoffConverseComparisonConstant * classicalError n ≤
      optimalEqualPriorTensorPowerError rho sigma n

/-- The source-shaped Nussbaum--Szkola finite comparison instantiates the
generic quantum-to-classical Chernoff comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_of_nussbaumSzkola
    (rho sigma : State a)
    {classicalError : Nat → ℝ≥0∞}
    (hfinite : HasNussbaumSzkolaFiniteComparison rho sigma classicalError) :
    HasQuantumToClassicalChernoffComparison rho sigma classicalError :=
  hfinite.2

/-- Product Nussbaum--Szkola finite comparison instantiates the generic
quantum-to-classical Chernoff comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_of_nussbaumSzkolaProduct
    (rho sigma : State a)
    {classicalError : Nat → ℝ≥0∞}
    (hfinite : HasNussbaumSzkolaProductFiniteComparison rho sigma classicalError) :
    HasQuantumToClassicalChernoffComparison rho sigma classicalError :=
  hfinite.2

/-- The canonical Nussbaum--Szkola sequence satisfies the finite quantum-to-classical
comparison with Gour's `1 / 2` constant. -/
theorem hasNussbaumSzkolaFiniteComparison
    (rho sigma : State a) :
    HasNussbaumSzkolaFiniteComparison
      rho sigma (nussbaumSzkolaClassicalError rho sigma) := by
  refine ⟨nussbaumSzkolaClassicalError_tensorPowerCompatible rho sigma, ?_⟩
  intro n
  classical
  let rhoN : State (TensorPower a n) := rho.tensorPower n
  let sigmaN : State (TensorPower a n) := sigma.tensorPower n
  let T0 : BinaryHypothesisTest (TensorPower a n) := rhoN.helstromTest sigmaN
  have hPherm : T0.acceptRhoEffect.IsHermitian :=
    T0.acceptRhoEffect_pos.isHermitian
  have hPidem : T0.acceptRhoEffect * T0.acceptRhoEffect = T0.acceptRhoEffect := by
    let H : CMatrix (TensorPower a n) := rhoN.matrix - sigmaN.matrix
    let hH : H.IsHermitian := rhoN.pos.isHermitian.sub sigmaN.pos.isHermitian
    simpa [T0, State.helstromTest, BinaryHypothesisTest.acceptRhoEffect, H, hH]
      using positiveSpectralProjector_idempotent H hH
  have hsource :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ) ≤
        (T0.equalPriorError rhoN sigmaN : ℝ) := by
    have hprojection :=
      half_nussbaumSzkolaModel_equalPriorError_le_projection_error
        rhoN sigmaN hPherm hPidem
    exact hprojection.trans_eq
      (half_trace_accept_effect_error_eq_equalPriorError T0 rhoN sigmaN)
  have hsource_formula :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ) ≤
        (1 / 2 : ℝ) * (1 - rhoN.normalizedTraceDistance sigmaN) := by
    exact hsource.trans_eq (State.helstromTest_equalPriorError_eq rhoN sigmaN)
  rw [optimalEqualPriorTensorPowerError]
  refine le_iInf ?_
  intro T
  have hTreal :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ) := by
    have hopt := (State.helstrom_equalPriorError_optimal rhoN sigmaN).2 T
    exact hsource_formula.trans (by
      simpa [BinaryHypothesisTest.equalPriorTensorPowerError, rhoN, sigmaN] using hopt)
  have hTnn :
      ((1 / 2 : ℝ≥0) * (nussbaumSzkolaModel rhoN sigmaN).equalPriorError) ≤
        T.equalPriorTensorPowerError rho sigma := by
    apply NNReal.coe_le_coe.mp
    simpa using hTreal
  have hTenn :
      (((1 / 2 : ℝ≥0) * (nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ≥0) :
          ℝ≥0∞) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hTnn
  unfold quantumChernoffConverseComparisonConstant nussbaumSzkolaClassicalError
  simpa [ClassicalBinaryModel.equalPriorErrorENNReal, rhoN, sigmaN] using hTenn

/-- The canonical product Nussbaum--Szkola sequence satisfies the finite
quantum-to-classical comparison with Gour's `1 / 2` constant. -/
theorem hasNussbaumSzkolaProductFiniteComparison
    (rho sigma : State a) :
    HasNussbaumSzkolaProductFiniteComparison
      rho sigma (nussbaumSzkolaProductClassicalError rho sigma) := by
  refine ⟨rfl, ?_⟩
  intro n
  classical
  let rhoN : State (TensorPower a n) := rho.tensorPower n
  let sigmaN : State (TensorPower a n) := sigma.tensorPower n
  let T0 : BinaryHypothesisTest (TensorPower a n) := rhoN.helstromTest sigmaN
  have hPherm : T0.acceptRhoEffect.IsHermitian :=
    T0.acceptRhoEffect_pos.isHermitian
  have hPidem : T0.acceptRhoEffect * T0.acceptRhoEffect = T0.acceptRhoEffect := by
    let H : CMatrix (TensorPower a n) := rhoN.matrix - sigmaN.matrix
    let hH : H.IsHermitian := rhoN.pos.isHermitian.sub sigmaN.pos.isHermitian
    simpa [T0, State.helstromTest, BinaryHypothesisTest.acceptRhoEffect, H, hH]
      using positiveSpectralProjector_idempotent H hH
  have hsource :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        (T0.equalPriorError rhoN sigmaN : ℝ) := by
    have hprojection :=
      half_nussbaumSzkolaProductModel_equalPriorError_le_projection_error
        rho sigma n hPherm hPidem
    exact hprojection.trans_eq
      (half_trace_accept_effect_error_eq_equalPriorError T0 rhoN sigmaN)
  have hsource_formula :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        (1 / 2 : ℝ) * (1 - rhoN.normalizedTraceDistance sigmaN) := by
    exact hsource.trans_eq (State.helstromTest_equalPriorError_eq rhoN sigmaN)
  rw [optimalEqualPriorTensorPowerError]
  refine le_iInf ?_
  intro T
  have hTreal :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ) := by
    have hopt := (State.helstrom_equalPriorError_optimal rhoN sigmaN).2 T
    exact hsource_formula.trans (by
      simpa [BinaryHypothesisTest.equalPriorTensorPowerError, rhoN, sigmaN] using hopt)
  have hTnn :
      ((1 / 2 : ℝ≥0) * (nussbaumSzkolaProductModel rho sigma n).equalPriorError) ≤
        T.equalPriorTensorPowerError rho sigma := by
    apply NNReal.coe_le_coe.mp
    simpa using hTreal
  have hTenn :
      (((1 / 2 : ℝ≥0) * (nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ≥0) :
          ℝ≥0∞) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hTnn
  unfold quantumChernoffConverseComparisonConstant nussbaumSzkolaProductClassicalError
  simpa [ClassicalBinaryModel.equalPriorErrorENNReal] using hTenn

/-- The canonical Nussbaum--Szkola sequence satisfies the generic
quantum-to-classical comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_nussbaumSzkolaClassicalError
    (rho sigma : State a) :
    HasQuantumToClassicalChernoffComparison
      rho sigma (nussbaumSzkolaClassicalError rho sigma) :=
  hasQuantumToClassicalChernoffComparison_of_nussbaumSzkola
    rho sigma (hasNussbaumSzkolaFiniteComparison rho sigma)

/-- The canonical product Nussbaum--Szkola sequence satisfies the generic
quantum-to-classical comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_nussbaumSzkolaProductClassicalError
    (rho sigma : State a) :
    HasQuantumToClassicalChernoffComparison
      rho sigma (nussbaumSzkolaProductClassicalError rho sigma) :=
  hasQuantumToClassicalChernoffComparison_of_nussbaumSzkolaProduct
    rho sigma (hasNussbaumSzkolaProductFiniteComparison rho sigma)

/-- Source-shaped classical method-of-types converse estimate.

The source proof lower-bounds classical errors using `(n+1)^(-m)` type-class
prefactors and then obtains the limsup orientation for the normalized negative
log error exponent [Gour2024Resources, BookQRT.tex:15414-15469]. -/
def HasClassicalMethodOfTypesChernoffConverse
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  Filter.limsup (fun n : Nat => normalizedNegLog n (classicalError (n + 1)))
    atTop ≤ rho.chernoffDistance sigma

/-- Finite-copy exponent form of the classical method-of-types Chernoff converse.

This predicate records the source-backed finite-`n` conclusion after applying
the type-class lower bounds with the polynomial prefactor `(n+1)^(-m)`: the
normalized negative log of the classical error is eventually bounded by the
Chernoff distance plus the finite-alphabet polynomial penalty. -/
def HasClassicalMethodOfTypesFiniteExponentBound
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  ∀ᶠ n in atTop,
    normalizedNegLog n (classicalError (n + 1)) ≤
      rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n

/-- The finite method-of-types exponent bound implies the limsup converse
orientation required by `HasClassicalMethodOfTypesChernoffConverse`. -/
theorem classicalMethodOfTypes_limsup_le_of_finiteExponentBound
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞)
    (hfinite :
      ∀ᶠ n in atTop,
        normalizedNegLog n (classicalError (n + 1)) ≤
          rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n) :
    Filter.limsup (fun n : Nat => normalizedNegLog n (classicalError (n + 1)))
        atTop ≤ rho.chernoffDistance sigma := by
  have hpenalty :
      Tendsto (fun n : Nat => methodOfTypesPolynomialPenalty (a := a) n)
        atTop (𝓝 (0 : EReal)) :=
    methodOfTypesPolynomialPenalty_tendsto_zero (a := a)
  have hsum :
      Tendsto
        (fun n : Nat => rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n)
        atTop (𝓝 (rho.chernoffDistance sigma)) := by
    have hpair :
        Tendsto
          (fun n : Nat => (rho.chernoffDistance sigma, methodOfTypesPolynomialPenalty (a := a) n))
          atTop (𝓝 (rho.chernoffDistance sigma, (0 : EReal))) :=
      tendsto_const_nhds.prodMk_nhds hpenalty
    have hadd :
        ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
          (rho.chernoffDistance sigma, (0 : EReal)) :=
      EReal.continuousAt_add (p := (rho.chernoffDistance sigma, (0 : EReal)))
        (Or.inr (by simp)) (Or.inr (by simp))
    simpa using hadd.tendsto.comp hpair
  have hlimsup_le :=
    Filter.limsup_le_limsup hfinite (β := EReal)
      (u := fun n : Nat => normalizedNegLog n (classicalError (n + 1)))
      (v := fun n : Nat => rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n)
  exact hlimsup_le.trans (le_of_eq hsum.limsup_eq)

/-- Source-shaped classical method-of-types route packaged as the existing
converse predicate. -/
theorem hasClassicalMethodOfTypesChernoffConverse_of_finiteExponentBound
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞)
    (hfinite : HasClassicalMethodOfTypesFiniteExponentBound rho sigma classicalError) :
    HasClassicalMethodOfTypesChernoffConverse rho sigma classicalError :=
  classicalMethodOfTypes_limsup_le_of_finiteExponentBound rho sigma classicalError hfinite

/-- The generic finite-alphabet method-of-types converse instantiated for the
canonical product Nussbaum--Szkola classical error sequence. -/
theorem hasClassicalMethodOfTypesChernoffConverse_nussbaumSzkolaProductClassicalError
    (rho sigma : State a) :
    HasClassicalMethodOfTypesChernoffConverse
      rho sigma (nussbaumSzkolaProductClassicalError rho sigma) := by
  classical
  have h :=
    ClassicalBinaryModel.methodOfTypesChernoffConverse
      (M := nussbaumSzkolaModel rho sigma)
  simpa [HasClassicalMethodOfTypesChernoffConverse,
    nussbaumSzkolaProductClassicalError, nussbaumSzkolaProductModel,
    nussbaumSzkolaModel_chernoffDistance_eq] using h

/-- The finite quantum-to-classical comparison turns the product
Nussbaum--Szkola classical exponent into a pointwise upper bound on the quantum
optimal-error exponent, with the explicit `log 2 / (n+1)` penalty from the
source's `1 / 2` comparison constant. -/
theorem optimalErrorExponent_le_nussbaumSzkolaProductClassicalExponent_add_penalty
    (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n ≤
      normalizedNegLog n
        (nussbaumSzkolaProductClassicalError rho sigma (n + 1)) +
        equalPriorAverageLogPenalty n := by
  have hcomparison :
      quantumChernoffConverseComparisonConstant *
          nussbaumSzkolaProductClassicalError rho sigma (n + 1) ≤
        optimalEqualPriorTensorPowerError rho sigma (n + 1) :=
    hasQuantumToClassicalChernoffComparison_nussbaumSzkolaProductClassicalError
      rho sigma (n + 1)
  have hquantum :
      optimalEqualPriorTensorPowerErrorExponent rho sigma n ≤
        normalizedNegLog n
          (quantumChernoffConverseComparisonConstant *
            nussbaumSzkolaProductClassicalError rho sigma (n + 1)) := by
    simpa [optimalEqualPriorTensorPowerErrorExponent] using
      normalizedNegLog_antitone n hcomparison
  have hpenalty :=
    normalizedNegLog_half_mul_coe_le_add_equalPriorAverageLogPenalty
      n ((nussbaumSzkolaProductModel rho sigma (n + 1)).equalPriorError)
  exact hquantum.trans (by
    simpa [quantumChernoffConverseComparisonConstant,
      nussbaumSzkolaProductClassicalError,
      ClassicalBinaryModel.equalPriorErrorENNReal] using hpenalty)

/-- Limsup-side quantum Chernoff converse obtained from the product
Nussbaum--Szkola comparison and the generic classical method-of-types
converse. -/
theorem limsup_errorExponent_le_chernoffDistance_nussbaumSzkolaProduct
    (rho sigma : State a) :
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma := by
  let classicalSeq : Nat → EReal := fun n =>
    normalizedNegLog n (nussbaumSzkolaProductClassicalError rho sigma (n + 1))
  let priorPenalty : Nat → EReal := fun n => equalPriorAverageLogPenalty n
  have hpoint :
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n) ≤ᶠ[atTop]
        fun n : Nat => classicalSeq n + priorPenalty n := by
    exact Filter.Eventually.of_forall fun n => by
      simpa [classicalSeq, priorPenalty] using
        optimalErrorExponent_le_nussbaumSzkolaProductClassicalExponent_add_penalty
          rho sigma n
  have hprior_limsup :
      Filter.limsup priorPenalty atTop = (0 : EReal) :=
    equalPriorAverageLogPenalty_tendsto_zero.limsup_eq
  have hsum :
      Filter.limsup (fun n : Nat => classicalSeq n + priorPenalty n) atTop ≤
        Filter.limsup classicalSeq atTop + Filter.limsup priorPenalty atTop := by
    simpa only [Pi.add_apply] using
      EReal.limsup_add_le
        (u := classicalSeq) (v := priorPenalty) (f := atTop)
        (Or.inr (by rw [hprior_limsup]; simp))
        (Or.inr (by rw [hprior_limsup]; simp))
  have hclassical :
      Filter.limsup classicalSeq atTop ≤ rho.chernoffDistance sigma := by
    simpa [classicalSeq] using
      hasClassicalMethodOfTypesChernoffConverse_nussbaumSzkolaProductClassicalError
        rho sigma
  have hbridge :=
    Filter.limsup_le_limsup hpoint (β := EReal)
      (u := fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      (v := fun n : Nat => classicalSeq n + priorPenalty n)
  calc
    Filter.limsup
        (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
        atTop
        ≤ Filter.limsup (fun n : Nat => classicalSeq n + priorPenalty n) atTop :=
          hbridge
    _ ≤ Filter.limsup classicalSeq atTop + Filter.limsup priorPenalty atTop := hsum
    _ = Filter.limsup classicalSeq atTop := by
          rw [hprior_limsup]
          simp
    _ ≤ rho.chernoffDistance sigma := hclassical

/-- Source-backed QCB lower/converse route required before the final squeeze.

This is deliberately a route predicate, not the final unconditional QCB theorem:
the Nussbaum--Szkola comparison and classical method-of-types machinery are
explicit upstream obligations.  The last field records the required limsup
shape `limsup_errorExponent_le_chernoffDistance`, including arbitrary-state
and zero-overlap boundary cases, before the final squeeze theorem consumes it
[Gour2024Resources, BookQRT.tex:15373-15949]. -/
def QuantumChernoffConverseRoute (rho sigma : State a) : Prop :=
  ∃ classicalError : Nat → ℝ≥0∞,
    HasQuantumToClassicalChernoffComparison rho sigma classicalError ∧
    HasClassicalMethodOfTypesChernoffConverse rho sigma classicalError ∧
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma

/-- Unconditional product Nussbaum--Szkola converse route for the QCB squeeze. -/
theorem quantumChernoffConverseRoute (rho sigma : State a) :
    QuantumChernoffConverseRoute rho sigma := by
  refine ⟨nussbaumSzkolaProductClassicalError rho sigma,
    hasQuantumToClassicalChernoffComparison_nussbaumSzkolaProductClassicalError
      rho sigma,
    hasClassicalMethodOfTypesChernoffConverse_nussbaumSzkolaProductClassicalError
      rho sigma,
    limsup_errorExponent_le_chernoffDistance_nussbaumSzkolaProduct
      rho sigma⟩

/-- Limsup-side QCB bound extracted from a source-backed converse route.

This is the reusable lower/converse route API; it does not claim the final
asymptotic quantum Chernoff bound statement. -/
theorem limsup_errorExponent_le_chernoffDistance_of_converseRoute
    (rho sigma : State a)
    (h : QuantumChernoffConverseRoute rho sigma) :
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma := by
  rcases h with ⟨_classicalError, _hComparison, _hClassical, hlimsup⟩
  exact hlimsup

/-- Upper-side assembly of the QCB squeeze from pointwise Chernoff exponent
lower bounds.

If every Petz/Chernoff exponent indexed by `0 ≤ s ≤ 1` is eventually below the
optimal tensor-power error exponent, then the Chernoff distance, defined as the
supremum over those exponents, is below the `liminf` of the optimal exponent
sequence.  This is the reusable bridge from the finite-copy direct bound and
exponent calculus to the asymptotic squeeze
[Gour2024Resources, BookQRT.tex:15887-15909]. -/
theorem chernoffDistance_le_liminf_errorExponent_of_eventually_petzChernoffExponent_le
    (rho sigma : State a)
    (hupper :
      ∀ s : Set.Icc (0 : ℝ) 1,
        ∀ᶠ n in atTop,
          rho.petzChernoffExponent sigma s.1 ≤
            optimalEqualPriorTensorPowerErrorExponent rho sigma n) :
    rho.chernoffDistance sigma ≤
      Filter.liminf
        (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
        atTop := by
  rw [State.chernoffDistance]
  refine iSup_le ?_
  intro s
  exact le_liminf_of_le (by isBoundedDefault) (hupper s)

/-- Liminf/limsup squeeze bridge for the optimal-error exponent.

This theorem deliberately consumes the two squeeze sides as hypotheses, instead
of proving the asymptotic QCB statement by name.  A downstream statement can
instantiate this bridge after supplying the direct `liminf` side and the
converse `limsup` side. -/
theorem errorExponent_tendsto_chernoffDistance_of_liminf_limsup
    (rho sigma : State a)
    (hliminf :
      rho.chernoffDistance sigma ≤
        Filter.liminf
          (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
          atTop)
    (hlimsup :
      Filter.limsup
          (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
          atTop ≤ rho.chernoffDistance sigma) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (rho.chernoffDistance sigma)) := by
  exact tendsto_of_le_liminf_of_limsup_le hliminf hlimsup

/-- QCB squeeze bridge using the registered converse route.

The direct side is stated as the eventual pointwise Petz/Chernoff exponent
bound produced by the finite-copy upper-bound and exponent-calculus route; the
converse side is supplied by `QuantumChernoffConverseRoute`.  This is a bridge
for downstream use, not the public asymptotic QCB theorem entrypoint
[Gour2024Resources, BookQRT.tex:15373-15949]. -/
theorem errorExponent_tendsto_chernoffDistance_of_eventually_petzChernoffExponent_le_of_converseRoute
    (rho sigma : State a)
    (hupper :
      ∀ s : Set.Icc (0 : ℝ) 1,
        ∀ᶠ n in atTop,
          rho.petzChernoffExponent sigma s.1 ≤
            optimalEqualPriorTensorPowerErrorExponent rho sigma n)
    (hroute : QuantumChernoffConverseRoute rho sigma) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (rho.chernoffDistance sigma)) :=
  errorExponent_tendsto_chernoffDistance_of_liminf_limsup rho sigma
    (chernoffDistance_le_liminf_errorExponent_of_eventually_petzChernoffExponent_le
      rho sigma hupper)
    (limsup_errorExponent_le_chernoffDistance_of_converseRoute rho sigma hroute)

/-- Unconditional limsup-side QCB converse bound. -/
theorem limsup_errorExponent_le_chernoffDistance
    (rho sigma : State a) :
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma :=
  limsup_errorExponent_le_chernoffDistance_of_converseRoute
    rho sigma (quantumChernoffConverseRoute rho sigma)

/-- Unconditional direct-side lower bound for the liminf of optimal-error
exponents. -/
theorem chernoffDistance_le_liminf_errorExponent
    (rho sigma : State a) :
    rho.chernoffDistance sigma ≤
      Filter.liminf
        (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
        atTop :=
  chernoffDistance_le_liminf_errorExponent_of_eventually_petzChernoffExponent_le
    rho sigma
    (eventually_petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
      rho sigma)

/-- Unconditional convergence of the optimal tensor-power error exponent to
the quantum Chernoff distance.  This is the squeeze API consumed by the
separate public QCB theorem. -/
theorem errorExponent_tendsto_chernoffDistance
    (rho sigma : State a) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (rho.chernoffDistance sigma)) :=
  errorExponent_tendsto_chernoffDistance_of_liminf_limsup rho sigma
    (chernoffDistance_le_liminf_errorExponent rho sigma)
    (limsup_errorExponent_le_chernoffDistance rho sigma)

/-- Zero optimal error gives infinite extended exponent. -/
theorem optimalEqualPriorTensorPowerErrorExponent_eq_top_of_optimalEqualPriorTensorPowerError_eq_zero
    (rho sigma : State a) (n : Nat)
    (h : optimalEqualPriorTensorPowerError rho sigma (n + 1) = 0) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n = ⊤ :=
  normalizedNegLog_eq_top_of_eq_zero n
    (optimalEqualPriorTensorPowerError rho sigma (n + 1)) h

/-- Positive optimal error gives the finite real-log exponent; finiteness follows from `≤ 1`. -/
theorem optimalEqualPriorTensorPowerErrorExponent_eq_coe_real_of_ne_zero
    (rho sigma : State a) (n : Nat)
    (h0 : optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ 0) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n =
      ((normalizedNegLogReal n
        (optimalEqualPriorTensorPowerError rho sigma (n + 1)) : ℝ) : EReal) :=
  normalizedNegLog_eq_coe_real_of_ne_zero_ne_top n
    (optimalEqualPriorTensorPowerError rho sigma (n + 1))
    h0
    (optimalEqualPriorTensorPowerError_ne_top rho sigma (n + 1))

/-- Finite real convergence of optimal-error exponents lifts to `EReal`.

This is the finite-limit bridge signature: the only boundary
assumption is eventual nonzero optimal error; finiteness is derived from the
probability bound. -/
theorem optimalEqualPriorTensorPowerErrorExponent_tendsto_of_eventually_finite_real_tendsto
    (rho sigma : State a) {L : ℝ}
    (h_nonzero : ∀ᶠ n in atTop,
      optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ 0)
    (hlim : Tendsto
      (fun n : Nat =>
        normalizedNegLogReal n
          (optimalEqualPriorTensorPowerError rho sigma (n + 1)))
      atTop (𝓝 L)) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (L : EReal)) := by
  have hfinite : ∀ᶠ n in atTop,
      optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ 0 ∧
        optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ ⊤ :=
    h_nonzero.and (Filter.Eventually.of_forall fun n =>
      optimalEqualPriorTensorPowerError_ne_top rho sigma (n + 1))
  exact normalizedNegLog_tendsto_coe_of_eventually_ne_zero_ne_top_real_tendsto
    hfinite hlim

/-- Real convergence to `+∞` of optimal-error exponents lifts to the `EReal` top limit. -/
theorem optimalEqualPriorTensorPowerErrorExponent_tendsto_top_of_real_tendsto_atTop
    (rho sigma : State a)
    (hlim : Tendsto
      (fun n : Nat =>
        normalizedNegLogReal n
          (optimalEqualPriorTensorPowerError rho sigma (n + 1)))
      atTop atTop) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (⊤ : EReal)) := by
  exact normalizedNegLog_tendsto_top_of_eventually_ne_top_real_tendsto_atTop
    (Filter.Eventually.of_forall fun n =>
      optimalEqualPriorTensorPowerError_ne_top rho sigma (n + 1))
    hlim

/-- Eventually zero optimal error forces the optimal-error exponent to tend to `⊤`. -/
theorem optimalEqualPriorTensorPowerErrorExponent_tendsto_top_of_eventually_zero
    (rho sigma : State a)
    (hzero : ∀ᶠ n in atTop,
      optimalEqualPriorTensorPowerError rho sigma (n + 1) = 0) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (⊤ : EReal)) :=
  normalizedNegLog_tendsto_top_of_eventually_eq_zero hzero

/-- Statement shape of the asymptotic quantum Chernoff bound, without proving it. -/
def asymptoticQuantumChernoffBoundStatement (rho sigma : State a) : Prop :=
  Tendsto (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
    atTop (𝓝 (rho.chernoffDistance sigma))

/-- Asymptotic quantum Chernoff bound for finite-dimensional states.

This packages Tomamichel's asymptotic QCB statement using the Audenaert/Gour
finite-copy proof route already assembled in the convergence theorem. -/
theorem asymptoticQuantumChernoffBound
    (rho sigma : State a) :
    asymptoticQuantumChernoffBoundStatement rho sigma :=
  errorExponent_tendsto_chernoffDistance rho sigma

end BinaryHypothesisTest

end

end QIT
