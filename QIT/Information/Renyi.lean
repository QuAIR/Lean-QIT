/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Quantum Renyi divergences

Petz and sandwiched Renyi divergences defined via `CFC.rpow`, plus their
tensor-power additivity under `State.prod` (Kronecker product). This is the
FQAEP engine layer — the Renyi family is the workhorse of the finite-N AEP
and one-shot decoupling bounds.

The definitions expose positive-definite input witnesses and order-domain
witnesses `0 < α`, `α ≠ 1` as API preconditions. The witnesses are not
computationally used by `CFC.rpow`, but they keep downstream theorem
statements aligned with the mathematical domain.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix Polynomial

namespace QIT

universe u v

noncomputable section

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

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

private theorem rpow_conjStarAlgAut_nonneg
    {n : Type u} [Fintype n] [DecidableEq n]
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

private theorem rpow_conjStarAlgAut_posDef
    {n : Type u} [Fintype n] [DecidableEq n]
    (u : Matrix.unitaryGroup n ℂ) {A : CMatrix n} (hA : A.PosDef)
    (s : ℝ) :
    CFC.rpow (Unitary.conjStarAlgAut ℂ _ u A) s =
      Unitary.conjStarAlgAut ℂ _ u (CFC.rpow A s) := by
  change (Unitary.conjStarAlgAut ℂ _ u A) ^ s =
    Unitary.conjStarAlgAut ℂ _ u (A ^ s)
  have hmap_nonneg : 0 ≤ Unitary.conjStarAlgAut ℂ (CMatrix n) u A := by
    rw [Unitary.conjStarAlgAut_apply]
    exact Matrix.nonneg_iff_posSemidef.mpr
      (hA.posSemidef.mul_mul_conjTranspose_same (u : CMatrix n))
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := Unitary.conjStarAlgAut ℂ (CMatrix n) u A) (y := s)
    hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa using
    (StarAlgHomClass.map_cfc
      (Unitary.conjStarAlgAut ℂ (CMatrix n) u)
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (.inl (ne_of_gt ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix n => (u : CMatrix n) * A * star (u : CMatrix n)
        fun_prop)).symm

private theorem cMatrix_rpow_kronecker_nonneg_core
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
    rw [rpow_conjStarAlgAut_nonneg UA
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
    rw [rpow_conjStarAlgAut_nonneg UB
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
    rw [rpow_conjStarAlgAut_nonneg U hDprod_psd hs0]
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

/-- Kronecker products commute with `CFC.rpow` for positive semidefinite matrices
and nonnegative exponents. This is the domain needed by the Chernoff/Petz
coefficient lemmas. -/
theorem cMatrix_rpow_kronecker_nonneg
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {s : ℝ} (_hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) :=
  cMatrix_rpow_kronecker_nonneg_core hA hB _hs0

/-- Kronecker products commute with `CFC.rpow` for positive definite matrices
and arbitrary real exponents. This is the full-rank domain needed for Renyi
divergence additivity when the exponent can be negative. -/
theorem cMatrix_rpow_kronecker_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosDef) (hB : B.PosDef)
    (s : ℝ) :
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
    exact le_of_lt (hA.eigenvalues_pos i)
  have hdb : ∀ i, 0 ≤ db i := by
    intro i
    exact le_of_lt (hB.eigenvalues_pos i)
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
  have hDprod_pd :
      (Matrix.diagonal (fun i => (dprod i : ℂ)) : CMatrix (Prod a b)).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    have hpos : 0 < dprod i := mul_pos (hA.eigenvalues_pos i.1) (hB.eigenvalues_pos i.2)
    change 0 < ((dprod i : ℝ) : ℂ)
    exact_mod_cast hpos
  have hA_rpow :
      CFC.rpow A s =
        Unitary.conjStarAlgAut ℂ _ UA
          (Matrix.diagonal (fun i => ((da i ^ s : ℝ) : ℂ))) := by
    rw [hA_spec]
    rw [rpow_conjStarAlgAut_posDef UA
      (by
        rw [Matrix.posDef_diagonal_iff]
        intro i
        change 0 < ((da i : ℝ) : ℂ)
        exact_mod_cast hA.eigenvalues_pos i) s]
    rw [rpow_diagonal_ofReal da hda s]
  have hB_rpow :
      CFC.rpow B s =
        Unitary.conjStarAlgAut ℂ _ UB
          (Matrix.diagonal (fun i => ((db i ^ s : ℝ) : ℂ))) := by
    rw [hB_spec]
    rw [rpow_conjStarAlgAut_posDef UB
      (by
        rw [Matrix.posDef_diagonal_iff]
        intro i
        change 0 < ((db i : ℝ) : ℂ)
        exact_mod_cast hB.eigenvalues_pos i) s]
    rw [rpow_diagonal_ofReal db hdb s]
  have hleft :
      CFC.rpow (Matrix.kronecker A B) s =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => ((dprod i ^ s : ℝ) : ℂ))) := by
    rw [hAB_spec]
    rw [rpow_conjStarAlgAut_posDef U hDprod_pd s]
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

theorem log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2
  rw [Real.log_mul hx hy]
  ring

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

private theorem renyi_cMatrix_rpow_posSemidef (A : CMatrix a) (s : ℝ) :
    (CFC.rpow A s).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := s))

theorem cMatrix_rpow_posDef_of_posDef {A : CMatrix a} (hA : A.PosDef) (s : ℝ) :
    (CFC.rpow A s).PosDef := by
  change (A ^ s).PosDef
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s)
    (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)]
  rw [hA.isHermitian.cfc_eq]
  rw [Matrix.IsHermitian.cfc]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hA.isHermitian.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  have hr : 0 < hA.isHermitian.eigenvalues i ^ s :=
    Real.rpow_pos_of_pos (hA.eigenvalues_pos i) s
  show 0 < ((hA.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)
  exact_mod_cast hr

namespace State

/-- Petz quantum Renyi divergence D_α(ρ‖σ) = 1/(α-1) · log2 Tr(ρ^α · σ^(1-α)).

Requires α > 0, α ≠ 1 and both states positive-definite (invertible). -/
def petzRenyi (ρ σ : State a) (_hρ : ρ.matrix.PosDef) (_hσ : σ.matrix.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let A := CFC.rpow ρ.matrix α
  let B := CFC.rpow σ.matrix (1 - α)
  r * log2 ((A * B).trace.re)

/-- Petz quantum Renyi divergence in the PSD branch used for `0 < α < 1`.

For this order range no inverse power of the second state is needed.  This
definition is the source-faithful kernel for Khatri--Wilde's
`D_α(ρ ‖ σ)` comparison with a merely positive semidefinite `σ`. -/
def petzRenyiPSD (ρ σ : State a)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let A := CFC.rpow ρ.matrix α
  let B := CFC.rpow σ.matrix (1 - α)
  r * log2 ((A * B).trace.re)

theorem petzRenyiPSD_eq_petzRenyi
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.petzRenyiPSD σ α hα_pos hα_ne_one =
      ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one := rfl

/-- Sandwiched quantum Renyi divergence D̃_α(ρ‖σ).

D̃_α(ρ‖σ) = 1/(α-1) · log2 Tr((σ^((1-α)/2α) · ρ · σ^((1-α)/2α))^α). -/
def sandwichedRenyi (ρ σ : State a) (_hρ : ρ.matrix.PosDef) (_hσ : σ.matrix.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ.matrix s
  let M := CFC.rpow (C * ρ.matrix * C) α
  r * log2 (M.trace.re)

/-- Real powers of density matrices are positive semidefinite. -/
theorem rpowMatrix_posSemidef (ρ : State a) (s : ℝ) :
    (CFC.rpow ρ.matrix s).PosSemidef :=
  renyi_cMatrix_rpow_posSemidef ρ.matrix s

/-- Real powers of positive-definite density matrices are positive definite. -/
theorem rpowMatrix_posDef_of_posDef (ρ : State a) (hρ : ρ.matrix.PosDef) (s : ℝ) :
    (CFC.rpow ρ.matrix s).PosDef :=
  cMatrix_rpow_posDef_of_posDef hρ s

theorem prod_matrix_kronecker {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) (σ : State b) :
    (ρ.prod σ).matrix = Matrix.kronecker ρ.matrix σ.matrix := rfl

theorem prod_posDef {b : Type v} [Fintype b] [DecidableEq b]
    {ρ : State a} {σ : State b}
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) :
    (ρ.prod σ).matrix.PosDef := by
  rw [prod_matrix_kronecker]
  exact hρ.kronecker hσ

theorem tensorPower_posDef {ρ : State a}
    (hρ : ρ.matrix.PosDef) (n : Nat) :
    (ρ.tensorPower n).matrix.PosDef := by
  induction n with
  | zero =>
      rw [State.tensorPower_zero]
      change (1 : CMatrix PUnit).PosDef
      exact Matrix.PosDef.one
  | succ n ih =>
      rw [State.tensorPower_succ]
      exact State.prod_posDef hρ ih

private theorem petzRenyi_trace_re_pos (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) (α : ℝ) :
    0 < ((CFC.rpow ρ.matrix α * CFC.rpow σ.matrix (1 - α)).trace).re := by
  haveI : Nonempty a := ρ.nonempty
  exact trace_mul_posDef_re_pos
    (ρ.rpowMatrix_posDef_of_posDef hρ α)
    (σ.rpowMatrix_posDef_of_posDef hσ (1 - α))

theorem petzRenyi_prod {b : Type v} [Fintype b] [DecidableEq b]
    (ρ₁ σ₁ : State a) (ρ₂ σ₂ : State b)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ₁.prod ρ₂).petzRenyi (σ₁.prod σ₂)
        (State.prod_posDef hρ₁ hρ₂) (State.prod_posDef hσ₁ hσ₂)
        α hα_pos hα_ne_one =
      ρ₁.petzRenyi σ₁ hρ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.petzRenyi σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
  unfold petzRenyi
  have htrace :
      ((CFC.rpow (ρ₁.prod ρ₂).matrix α *
          CFC.rpow (σ₁.prod σ₂).matrix (1 - α)).trace).re =
        ((CFC.rpow ρ₁.matrix α * CFC.rpow σ₁.matrix (1 - α)).trace).re *
          ((CFC.rpow ρ₂.matrix α * CFC.rpow σ₂.matrix (1 - α)).trace).re := by
    have htraceC :
        (CFC.rpow (ρ₁.prod ρ₂).matrix α *
            CFC.rpow (σ₁.prod σ₂).matrix (1 - α)).trace =
          (CFC.rpow ρ₁.matrix α * CFC.rpow σ₁.matrix (1 - α)).trace *
            (CFC.rpow ρ₂.matrix α * CFC.rpow σ₂.matrix (1 - α)).trace := by
      rw [prod_matrix_kronecker ρ₁ ρ₂, prod_matrix_kronecker σ₁ σ₂]
      rw [cMatrix_rpow_kronecker_posDef hρ₁ hρ₂ α]
      rw [cMatrix_rpow_kronecker_posDef hσ₁ hσ₂ (1 - α)]
      change
        (Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow ρ₁.matrix α) (CFC.rpow ρ₂.matrix α) *
        Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow σ₁.matrix (1 - α)) (CFC.rpow σ₂.matrix (1 - α))).trace =
        (CFC.rpow ρ₁.matrix α * CFC.rpow σ₁.matrix (1 - α)).trace *
          (CFC.rpow ρ₂.matrix α * CFC.rpow σ₂.matrix (1 - α)).trace
      rw [← Matrix.mul_kronecker_mul]
      rw [Matrix.trace_kronecker]
    have h_im1 :
        ((CFC.rpow ρ₁.matrix α * CFC.rpow σ₁.matrix (1 - α)).trace).im = 0 :=
      trace_mul_posSemidef_im_eq_zero (ρ₁.rpowMatrix_posSemidef α)
        (σ₁.rpowMatrix_posSemidef (1 - α))
    have h_im2 :
        ((CFC.rpow ρ₂.matrix α * CFC.rpow σ₂.matrix (1 - α)).trace).im = 0 :=
      trace_mul_posSemidef_im_eq_zero (ρ₂.rpowMatrix_posSemidef α)
        (σ₂.rpowMatrix_posSemidef (1 - α))
    rw [htraceC, Complex.mul_re, h_im1, h_im2]
    ring
  have hxpos : 0 < ((CFC.rpow ρ₁.matrix α *
      CFC.rpow σ₁.matrix (1 - α)).trace).re :=
    petzRenyi_trace_re_pos ρ₁ σ₁ hρ₁ hσ₁ α
  have hypos : 0 < ((CFC.rpow ρ₂.matrix α *
      CFC.rpow σ₂.matrix (1 - α)).trace).re :=
    petzRenyi_trace_re_pos ρ₂ σ₂ hρ₂ hσ₂ α
  change (1 / (α - 1)) *
      log2 ((CFC.rpow (ρ₁.prod ρ₂).matrix α *
          CFC.rpow (σ₁.prod σ₂).matrix (1 - α)).trace).re =
    (1 / (α - 1)) *
      log2 ((CFC.rpow ρ₁.matrix α *
          CFC.rpow σ₁.matrix (1 - α)).trace).re +
    (1 / (α - 1)) *
      log2 ((CFC.rpow ρ₂.matrix α *
          CFC.rpow σ₂.matrix (1 - α)).trace).re
  rw [htrace]
  rw [log2_mul (ne_of_gt hxpos) (ne_of_gt hypos)]
  ring

theorem petzRenyi_tensorPower (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : Nat) :
    (ρ.tensorPower n).petzRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
      (n : ℝ) * ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      unfold petzRenyi
      rw [State.tensorPower_zero, State.tensorPower_zero]
      dsimp [State.unit]
      rw [Nat.cast_zero, zero_mul]
      change 1 / (α - 1) *
          log2 (((1 : CMatrix PUnit) ^ α * (1 : CMatrix PUnit) ^ (1 - α)).trace).re =
        0
      rw [show ((1 : CMatrix PUnit) ^ α) = 1 by exact CFC.one_rpow,
        show ((1 : CMatrix PUnit) ^ (1 - α)) = 1 by exact CFC.one_rpow,
        one_mul, Matrix.trace_one]
      simp [log2]
  | succ n ih =>
      change (ρ.prod (ρ.tensorPower n)).petzRenyi (σ.prod (σ.tensorPower n))
          _ _ α hα_pos hα_ne_one =
        ↑(n + 1) * ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one
      rw [State.petzRenyi_prod ρ σ (ρ.tensorPower n) (σ.tensorPower n)
        hρ hσ (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring_nf

theorem sandwichedRenyi_prod {b : Type v} [Fintype b] [DecidableEq b]
    (ρ₁ σ₁ : State a) (ρ₂ σ₂ : State b)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ₁.prod ρ₂).sandwichedRenyi (σ₁.prod σ₂)
        (State.prod_posDef hρ₁ hρ₂) (State.prod_posDef hσ₁ hσ₂)
        α hα_pos hα_ne_one =
      ρ₁.sandwichedRenyi σ₁ hρ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.sandwichedRenyi σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
  unfold sandwichedRenyi
  let s := (1 - α) / (2 * α)
  have hC :
      CFC.rpow (σ₁.prod σ₂).matrix s =
        Matrix.kronecker (CFC.rpow σ₁.matrix s) (CFC.rpow σ₂.matrix s) := by
    rw [prod_matrix_kronecker σ₁ σ₂]
    exact cMatrix_rpow_kronecker_posDef hσ₁ hσ₂ s
  have hinner :
      CFC.rpow (σ₁.prod σ₂).matrix s * (ρ₁.prod ρ₂).matrix *
          CFC.rpow (σ₁.prod σ₂).matrix s =
        Matrix.kronecker
          (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s)
          (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) := by
    rw [hC, prod_matrix_kronecker ρ₁ ρ₂]
    simp [Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  have hinner₁_pos :
      (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s).PosDef := by
    have hC₁ : (CFC.rpow σ₁.matrix s).PosDef :=
      σ₁.rpowMatrix_posDef_of_posDef hσ₁ s
    have hC₁_hm : (CFC.rpow σ₁.matrix s).IsHermitian :=
      (renyi_cMatrix_rpow_posSemidef σ₁.matrix s).isHermitian
    have h := hρ₁.mul_mul_conjTranspose_same (B := CFC.rpow σ₁.matrix s) ?_
    · rwa [hC₁_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hC₁.isUnit
  have hinner₂_pos :
      (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s).PosDef := by
    have hC₂ : (CFC.rpow σ₂.matrix s).PosDef :=
      σ₂.rpowMatrix_posDef_of_posDef hσ₂ s
    have hC₂_hm : (CFC.rpow σ₂.matrix s).IsHermitian :=
      (renyi_cMatrix_rpow_posSemidef σ₂.matrix s).isHermitian
    have h := hρ₂.mul_mul_conjTranspose_same (B := CFC.rpow σ₂.matrix s) ?_
    · rwa [hC₂_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hC₂.isUnit
  have htrace :
      ((CFC.rpow
        (CFC.rpow (σ₁.prod σ₂).matrix s * (ρ₁.prod ρ₂).matrix *
          CFC.rpow (σ₁.prod σ₂).matrix s) α).trace).re =
        ((CFC.rpow
          (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s) α).trace).re *
          ((CFC.rpow
            (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) α).trace).re := by
    have htraceC :
        (CFC.rpow
          (CFC.rpow (σ₁.prod σ₂).matrix s * (ρ₁.prod ρ₂).matrix *
            CFC.rpow (σ₁.prod σ₂).matrix s) α).trace =
          (CFC.rpow
            (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s) α).trace *
            (CFC.rpow
              (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) α).trace := by
      rw [hinner]
      rw [cMatrix_rpow_kronecker_posDef hinner₁_pos hinner₂_pos α]
      change
        (Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow
            (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s) α)
          (CFC.rpow
            (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) α)).trace =
          (CFC.rpow
            (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s) α).trace *
            (CFC.rpow
              (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) α).trace
      rw [Matrix.trace_kronecker]
    have h_im1 :
        ((CFC.rpow
          (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s) α).trace).im = 0 := by
      have hpsd := hinner₁_pos.posSemidef
      have htrace_nonneg : 0 ≤
          (CFC.rpow (CFC.rpow σ₁.matrix s * ρ₁.matrix *
            CFC.rpow σ₁.matrix s) α).trace :=
        Matrix.PosSemidef.trace_nonneg
          (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg
            (a := CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s)
            (y := α)))
      exact htrace_nonneg.2.symm
    have h_im2 :
        ((CFC.rpow
          (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) α).trace).im = 0 := by
      have htrace_nonneg : 0 ≤
          (CFC.rpow (CFC.rpow σ₂.matrix s * ρ₂.matrix *
            CFC.rpow σ₂.matrix s) α).trace :=
        Matrix.PosSemidef.trace_nonneg
          (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg
            (a := CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s)
            (y := α)))
      exact htrace_nonneg.2.symm
    rw [htraceC, Complex.mul_re, h_im1, h_im2]
    ring
  have hxpos : 0 < ((CFC.rpow
      (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s) α).trace).re := by
    haveI : Nonempty a := ρ₁.nonempty
    exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (cMatrix_rpow_posDef_of_posDef hinner₁_pos α))).1
  have hypos : 0 < ((CFC.rpow
      (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) α).trace).re := by
    haveI : Nonempty b := ρ₂.nonempty
    exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (cMatrix_rpow_posDef_of_posDef hinner₂_pos α))).1
  change (1 / (α - 1)) *
      log2 ((CFC.rpow
        (CFC.rpow (σ₁.prod σ₂).matrix s * (ρ₁.prod ρ₂).matrix *
          CFC.rpow (σ₁.prod σ₂).matrix s) α).trace).re =
    (1 / (α - 1)) *
      log2 ((CFC.rpow
        (CFC.rpow σ₁.matrix s * ρ₁.matrix * CFC.rpow σ₁.matrix s) α).trace).re +
    (1 / (α - 1)) *
      log2 ((CFC.rpow
        (CFC.rpow σ₂.matrix s * ρ₂.matrix * CFC.rpow σ₂.matrix s) α).trace).re
  rw [htrace]
  rw [log2_mul (ne_of_gt hxpos) (ne_of_gt hypos)]
  ring

theorem sandwichedRenyi_tensorPower (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : Nat) :
    (ρ.tensorPower n).sandwichedRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
      (n : ℝ) * ρ.sandwichedRenyi σ hρ hσ α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      unfold sandwichedRenyi
      rw [State.tensorPower_zero, State.tensorPower_zero]
      dsimp [State.unit]
      rw [Nat.cast_zero, zero_mul]
      change 1 / (α - 1) *
          log2 ((((1 : CMatrix PUnit) ^ ((1 - α) / (2 * α)) *
              1 * (1 : CMatrix PUnit) ^ ((1 - α) / (2 * α))) ^ α).trace).re =
        0
      rw [show ((1 : CMatrix PUnit) ^ ((1 - α) / (2 * α))) = 1 by exact CFC.one_rpow,
        one_mul, mul_one,
        show ((1 : CMatrix PUnit) ^ α) = 1 by exact CFC.one_rpow,
        Matrix.trace_one]
      simp [log2]
  | succ n ih =>
      change (ρ.prod (ρ.tensorPower n)).sandwichedRenyi (σ.prod (σ.tensorPower n))
          _ _ α hα_pos hα_ne_one =
        ↑(n + 1) * ρ.sandwichedRenyi σ hρ hσ α hα_pos hα_ne_one
      rw [State.sandwichedRenyi_prod ρ σ (ρ.tensorPower n) (σ.tensorPower n)
        hρ hσ (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring_nf

/-- Tensor-power additivity of the Petz and sandwiched Renyi divergences. -/
theorem renyi_tensorPower_additivity (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : Nat) :
    (ρ.tensorPower n).petzRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
          (n : ℝ) * ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one ∧
    (ρ.tensorPower n).sandwichedRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
          (n : ℝ) * ρ.sandwichedRenyi σ hρ hσ α hα_pos hα_ne_one := by
  exact ⟨State.petzRenyi_tensorPower ρ σ hρ hσ α hα_pos hα_ne_one n,
    State.sandwichedRenyi_tensorPower ρ σ hρ hσ α hα_pos hα_ne_one n⟩

end State

end

end QIT
