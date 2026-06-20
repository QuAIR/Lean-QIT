/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.HypothesisTesting
public import QIT.Core.Information.Renyi
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Asymptotic binary hypothesis-testing notation

This module provides the statement-level asymptotic API needed for binary
discrimination over IID tensor powers.  It reuses the binary-test convention
from `QIT.Core.HypothesisTesting` and the tensor-power state API.

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

private theorem spectrum_real_diagonal_ofReal {n : Type u} [Fintype n] [DecidableEq n]
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

private theorem aeval_diagonal_ofReal {n : Type u} [Fintype n] [DecidableEq n]
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

private theorem cfc_diagonal_ofReal {n : Type u} [Fintype n] [DecidableEq n]
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
      rw [spectrum_real_diagonal_ofReal d] at hx
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
      rw [aeval_diagonal_ofReal d p]
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
  exact cfc_diagonal_ofReal d (fun x => x ^ s)

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
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) := by
  let UA := hA.isHermitian.eigenvectorUnitary
  let UB := hB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let da : a -> ℝ := hA.isHermitian.eigenvalues
  let db : b -> ℝ := hB.isHermitian.eigenvalues
  let dprod : Prod a b -> ℝ := fun i => da i.1 * db i.2
  have hda : ∀ i, 0 ≤ da i := by
    intro i
    exact hA.eigenvalues_nonneg i
  have hdb : ∀ i, 0 ≤ db i := by
    intro i
    exact hB.eigenvalues_nonneg i
  have hdprod : ∀ i, 0 ≤ dprod i := by
    intro i
    exact mul_nonneg (hda i.1) (hdb i.2)
  have hA_spec :
      A = Unitary.conjStarAlgAut ℂ _ UA
        (Matrix.diagonal (fun i => (da i : ℂ))) := by
    simpa [UA, da, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hB_spec :
      B = Unitary.conjStarAlgAut ℂ _ UB
        (Matrix.diagonal (fun i => (db i : ℂ))) := by
    simpa [UB, db, Function.comp_def] using hB.isHermitian.spectral_theorem
  have hAB_spec :
      Matrix.kronecker A B =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => (dprod i : ℂ))) := by
    rw [hA_spec, hB_spec]
    simp [U, dprod, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  have hDprod_psd :
      (Matrix.diagonal (fun i => (dprod i : ℂ)) : CMatrix (Prod a b)).PosSemidef :=
    Matrix.PosSemidef.diagonal (d := fun i => (dprod i : ℂ)) (by
      intro i
      change (0 : ℂ) ≤ (dprod i : ℂ)
      exact_mod_cast hdprod i)
  have hA_rpow :
      CFC.rpow A s =
        Unitary.conjStarAlgAut ℂ _ UA
          (Matrix.diagonal (fun i => ((da i ^ s : ℝ) : ℂ))) := by
    rw [hA_spec]
    rw [rpow_conjStarAlgAut UA
      (Matrix.PosSemidef.diagonal (d := fun i => (da i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (da i : ℂ)
        exact_mod_cast hda i)) hs0]
    rw [rpow_diagonal_ofReal da hda s]
  have hB_rpow :
      CFC.rpow B s =
        Unitary.conjStarAlgAut ℂ _ UB
          (Matrix.diagonal (fun i => ((db i ^ s : ℝ) : ℂ))) := by
    rw [hB_spec]
    rw [rpow_conjStarAlgAut UB
      (Matrix.PosSemidef.diagonal (d := fun i => (db i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (db i : ℂ)
        exact_mod_cast hdb i)) hs0]
    rw [rpow_diagonal_ofReal db hdb s]
  have hleft :
      CFC.rpow (Matrix.kronecker A B) s =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => ((dprod i ^ s : ℝ) : ℂ))) := by
    rw [hAB_spec]
    rw [rpow_conjStarAlgAut U hDprod_psd hs0]
    rw [rpow_diagonal_ofReal dprod hdprod s]
  have hdiag :
      Matrix.diagonal (fun i : Prod a b => ((dprod i ^ s : ℝ) : ℂ)) =
        Matrix.diagonal (fun i : Prod a b => (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [dprod, Real.mul_rpow (hda i.1) (hdb i.2)]
    · simp [Matrix.diagonal, hij]
  have hright :
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal
            (fun i : Prod a b => (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ))) := by
    rw [hA_rpow, hB_rpow]
    simp [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  rw [hleft, hdiag, hright]

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The trace of the product of two positive semidefinite matrices is real. -/
theorem trace_mul_posSemidef_im_eq_zero {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((A * B).trace).im = 0 := by
  let S := psdSqrt A
  have hpsd : (S * B * S).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    dsimp [S] at h
    rw [psdSqrt_isHermitian A] at h
    exact h
  have htrace : 0 ≤ (S * B * S).trace :=
    Matrix.PosSemidef.trace_nonneg hpsd
  have hEq : (A * B).trace = (S * B * S).trace := by
    have hsqrt : S * S = A := by
      simpa [S] using psdSqrt_mul_self_of_posSemidef hA
    rw [← hsqrt]
    calc
      ((S * S) * B).trace = (S * (S * B)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((S * B) * S).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (S * B * S).trace := by
        rw [Matrix.mul_assoc]
  rw [hEq]
  exact htrace.2.symm

/-- The trace of the product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_posSemidef_re_nonneg {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B).trace).re := by
  let S := psdSqrt A
  have hpsd : (S * B * S).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    dsimp [S] at h
    rw [psdSqrt_isHermitian A] at h
    exact h
  have htrace : 0 ≤ (S * B * S).trace :=
    Matrix.PosSemidef.trace_nonneg hpsd
  have hEq : (A * B).trace = (S * B * S).trace := by
    have hsqrt : S * S = A := by
      simpa [S] using psdSqrt_mul_self_of_posSemidef hA
    rw [← hsqrt]
    calc
      ((S * S) * B).trace = (S * (S * B)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((S * B) * S).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (S * B * S).trace := by
        rw [Matrix.mul_assoc]
  rw [hEq]
  exact htrace.1

/-- The trace of the product of two positive definite matrices is positive. -/
theorem trace_mul_posDef_re_pos {A B : CMatrix a} [Nonempty a]
    (hA : A.PosDef) (hB : B.PosDef) :
    0 < ((A * B).trace).re := by
  let S := psdSqrt A
  have hS_hm : S.IsHermitian := psdSqrt_isHermitian A
  have hS_posdef : S.PosDef := by
    rw [show S = CFC.rpow A (1 / 2 : ℝ) by
      simp [S, psdSqrt, CFC.sqrt_eq_rpow]]
    change (A ^ (1 / 2 : ℝ)).PosDef
    rw [CFC.rpow_eq_cfc_real (a := A) (y := (1 / 2 : ℝ))
      (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)]
    rw [hA.isHermitian.cfc_eq]
    rw [Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe :
      IsUnit (hA.isHermitian.eigenvectorUnitary : CMatrix a))]
    rw [Matrix.posDef_diagonal_iff]
    intro i
    have hr : 0 < hA.isHermitian.eigenvalues i ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (hA.eigenvalues_pos i) (1 / 2 : ℝ)
    show 0 < ((hA.isHermitian.eigenvalues i ^ (1 / 2 : ℝ) : ℝ) : ℂ)
    exact_mod_cast hr
  have hpsd : (S * B * S).PosDef := by
    have h := hB.mul_mul_conjTranspose_same (B := S) ?_
    · rwa [hS_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hS_posdef.isUnit
  have hEq : (A * B).trace = (S * B * S).trace := by
    have hsqrt : S * S = A := by
      simpa [S] using psdSqrt_mul_self_of_posSemidef hA.posSemidef
    rw [← hsqrt]
    calc
      ((S * S) * B).trace = (S * (S * B)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((S * B) * S).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (S * B * S).trace := by
        rw [Matrix.mul_assoc]
  rw [hEq]
  exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpsd)).1

namespace State

/-- Real powers of density matrices are positive semidefinite. -/
theorem rpowMatrix_posSemidef (rho : State a) (s : ℝ) :
    (CFC.rpow rho.matrix s).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := rho.matrix) (y := s))

/-- A normalized finite-dimensional state has a nonempty index type. -/
theorem nonempty (rho : State a) : Nonempty a := by
  classical
  by_contra h
  haveI : IsEmpty a := not_nonempty_iff.mp h
  have htrace := rho.trace_eq_one
  simp [Matrix.trace] at htrace

/-- Real powers of positive-definite density matrices are positive definite. -/
theorem rpowMatrix_posDef_of_posDef (rho : State a) (hρ : rho.matrix.PosDef) (s : ℝ) :
    (CFC.rpow rho.matrix s).PosDef := by
  change (rho.matrix ^ s).PosDef
  rw [CFC.rpow_eq_cfc_real (a := rho.matrix) (y := s)
    (Matrix.nonneg_iff_posSemidef.mpr hρ.posSemidef)]
  rw [hρ.isHermitian.cfc_eq]
  rw [Matrix.IsHermitian.cfc]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hρ.isHermitian.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  have hr : 0 < hρ.isHermitian.eigenvalues i ^ s :=
    Real.rpow_pos_of_pos (hρ.eigenvalues_pos i) s
  show 0 < ((hρ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)
  exact_mod_cast hr

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

theorem prod_matrix_kronecker {b : Type v} [Fintype b] [DecidableEq b]
    (rho : State a) (sigma : State b) :
    (rho.prod sigma).matrix = Matrix.kronecker rho.matrix sigma.matrix := by
  rfl

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

/-- Exact exponent sequence `n ↦ -(1/(n+1)) log P*_{e,n+1}`. -/
def optimalEqualPriorTensorPowerErrorExponent (rho sigma : State a) (n : Nat) : EReal :=
  normalizedNegLog n (optimalEqualPriorTensorPowerError rho sigma (n + 1))

/-- The optimal-error exponent is the normalized extended negative log at index `n + 1`. -/
theorem optimalEqualPriorTensorPowerErrorExponent_eq_normalizedNegLog
    (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n =
      normalizedNegLog n (optimalEqualPriorTensorPowerError rho sigma (n + 1)) := rfl

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

end BinaryHypothesisTest

end

end QIT
