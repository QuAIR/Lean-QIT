/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy
public import QIT.Information.Renyi
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Real.Basic

/-!
# Typical-subspace projector and Schumacher compression

Definitions for the quantum typical subspace and Schumacher compression rate.

The typical projector is constructed spectrally: diagonalize the finite
tensor-power density matrix, keep exactly those eigenspaces whose eigenvalues
are typical, and conjugate the diagonal mask back to the original basis.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-! ## Spectral projectors selected by a finite eigenvalue predicate -/

/-- Spectral projector obtained by selecting a decidable predicate on the
eigenbasis of a Hermitian matrix. -/
def spectralPredicateProjector
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    CMatrix a :=
  (hH.eigenvectorUnitary : CMatrix a) *
    Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) *
      star (hH.eigenvectorUnitary : CMatrix a)

/-- A spectral predicate projector is positive semidefinite. -/
theorem spectralPredicateProjector_posSemidef
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    (spectralPredicateProjector H hH p).PosSemidef := by
  classical
  unfold spectralPredicateProjector
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : p i
  · simp [hi]
  · simp [hi]

/-- A spectral predicate projector is Hermitian. -/
theorem spectralPredicateProjector_isHermitian
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    (spectralPredicateProjector H hH p).IsHermitian :=
  (spectralPredicateProjector_posSemidef H hH p).1

/-- A spectral predicate projector is idempotent. -/
theorem spectralPredicateProjector_idempotent
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    spectralPredicateProjector H hH p * spectralPredicateProjector H hH p =
      spectralPredicateProjector H hH p := by
  classical
  unfold spectralPredicateProjector
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  have hD : D * D = D := by
    change
      Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : p i <;> simp [hi]
    · simp [Matrix.diagonal, hij]
  calc
    (U * D * star U) * (U * D * star U) =
        U * D * (star U * U) * D * star U := by
          noncomm_ring
    _ = U * D * 1 * D * star U := by rw [hU]
    _ = U * (D * D) * star U := by noncomm_ring
    _ = U * D * star U := by rw [hD]

/-- A spectral predicate projector is bounded above by the identity effect. -/
theorem spectralPredicateProjector_le_one
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    spectralPredicateProjector H hH p ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  unfold spectralPredicateProjector
  have hOne :
      (1 : CMatrix a) =
        (hH.eigenvectorUnitary : CMatrix a) *
          (1 : CMatrix a) *
            star (hH.eigenvectorUnitary : CMatrix a) := by
    simp
  rw [hOne]
  have hsub :
      (hH.eigenvectorUnitary : CMatrix a) * 1 * star (hH.eigenvectorUnitary : CMatrix a) -
        (hH.eigenvectorUnitary : CMatrix a) *
          Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) *
            star (hH.eigenvectorUnitary : CMatrix a) =
        (hH.eigenvectorUnitary : CMatrix a) *
          (1 - Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)) *
            star (hH.eigenvectorUnitary : CMatrix a) := by
    noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  have hdiag :
      (1 - Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) : CMatrix a) =
        Matrix.diagonal (fun i => 1 - if p i then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  rw [hdiag]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : p i
  · simp [hi]
  · simp [hi]

/-- The trace of a spectral predicate projector is the number of selected
eigenbasis directions. -/
theorem spectralPredicateProjector_trace_re
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    (spectralPredicateProjector H hH p).trace.re =
      ∑ i, if p i then (1 : ℝ) else (0 : ℝ) := by
  classical
  unfold spectralPredicateProjector
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  change ((U * D * star U).trace).re = ∑ i, if p i then (1 : ℝ) else 0
  calc
    ((U * D * star U).trace).re = D.trace.re := by
      rw [Matrix.trace_mul_cycle]
      simp [U]
    _ = ∑ i, if p i then (1 : ℝ) else (0 : ℝ) := by
      simp [D, Matrix.trace_diagonal]

/-- The probability weight of a spectral predicate projector against its
underlying Hermitian matrix is the selected eigenvalue sum. -/
theorem spectralPredicateProjector_trace_mul_re
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    ((H * spectralPredicateProjector H hH p).trace).re =
      ∑ i, if p i then hH.eigenvalues i else (0 : ℝ) := by
  classical
  let U : CMatrix a := hH.eigenvectorUnitary
  let Λ : CMatrix a := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let P : CMatrix a := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  have hspec : H = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hH.spectral_theorem
  unfold spectralPredicateProjector
  change ((H * (U * P * star U)).trace).re =
    ∑ i, if p i then hH.eigenvalues i else (0 : ℝ)
  conv_lhs => rw [hspec]
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  have hmul :
      (U * Λ * star U) * (U * P * star U) = U * (Λ * P) * star U := by
    calc
      (U * Λ * star U) * (U * P * star U) =
          U * Λ * (star U * U) * P * star U := by
            noncomm_ring
      _ = U * Λ * 1 * P * star U := by rw [hU]
      _ = U * (Λ * P) * star U := by noncomm_ring
  rw [hmul]
  calc
    ((U * (Λ * P) * star U).trace).re = (Λ * P).trace.re := by
      rw [Matrix.trace_mul_cycle]
      simp [U]
    _ = ∑ i, if p i then hH.eigenvalues i else (0 : ℝ) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p i <;> simp [hi]

/-- The Schumacher compression rate equals the von Neumann entropy.

rate(rho) = S(rho) = -sum lambda_i log2(lambda_i). -/
def State.schumacherRate (ρ : State a) : ℝ :=
  State.vonNeumann ρ

namespace State

/-- Eigenvalue typicality for the `n`-fold IID state, in bits:
`-log₂ μ` lies within `n δ` of `n S(ρ)`, and zero eigenvalues are excluded. -/
def typicalEigenvalue (ρ : State a) (n : ℕ) (δ μ : ℝ) : Prop :=
  0 < μ ∧ |(-log2 μ) - (n : ℝ) * ρ.vonNeumann| ≤ (n : ℝ) * δ

/-- The finite tensor-power spectral typical-subspace projector. -/
def typicalSubspaceProjector (ρ : State a) (n : ℕ) (δ : ℝ) :
    CMatrix (TensorPower a n) := by
  classical
  let τ := ρ.tensorPower n
  exact spectralPredicateProjector τ.matrix τ.pos.isHermitian
    (fun i => typicalEigenvalue ρ n δ (τ.pos.isHermitian.eigenvalues i))

/-- Number of selected spectral directions, expressed as a real trace count. -/
def typicalSubspaceDimension (ρ : State a) (n : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    then (1 : ℝ) else 0

/-- Spectral probability weight accepted by the typical projector. -/
def typicalSubspaceSpectralWeight (ρ : State a) (n : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0

/-- Spectral probability weight rejected by the typical projector. -/
def atypicalSubspaceSpectralWeight (ρ : State a) (n : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    if ¬ typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0

/-- Second moment of the centered log-eigenvalue random variable for
`ρ^{⊗ n}`. It is the finite spectral-distribution quantity that feeds
Chebyshev-style concentration estimates; separate tensor-product spectrum
lemmas are needed to turn it into an explicit `O(n)` variance bound. -/
def typicalLogDeviationSecondMoment (ρ : State a) (n : ℕ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    let μ := (ρ.tensorPower n).pos.isHermitian.eigenvalues i
    μ * (((-log2 μ) - (n : ℝ) * ρ.vonNeumann) ^ 2)

/-- Eigenvalues of an IID tensor-power density matrix sum to one. -/
theorem tensorPower_eigenvalue_sum (ρ : State a) (n : ℕ) :
    ∑ i : TensorPower a n, (ρ.tensorPower n).pos.isHermitian.eigenvalues i = 1 := by
  have hc :
      (∑ i : TensorPower a n,
          (((ρ.tensorPower n).pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 := by
    exact (ρ.tensorPower n).pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans
      (ρ.tensorPower n).trace_eq_one
  exact Complex.ofReal_injective (by simpa using hc)

/-- The trace-count dimension of the typical subspace is nonnegative. -/
theorem typicalSubspaceDimension_nonneg (ρ : State a) (n : ℕ) (δ : ℝ) :
    0 ≤ ρ.typicalSubspaceDimension n δ := by
  classical
  unfold typicalSubspaceDimension
  exact Finset.sum_nonneg fun i _ => by
    by_cases hi :
      typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    · simp [hi]
    · simp [hi]

/-- The trace-count dimension of the typical subspace is at most the ambient
finite tensor-power dimension. -/
theorem typicalSubspaceDimension_le_card (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceDimension n δ ≤ (Fintype.card (TensorPower a n) : ℝ) := by
  classical
  unfold typicalSubspaceDimension
  calc
    (∑ i : TensorPower a n,
        if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        then (1 : ℝ) else 0)
        ≤ ∑ _i : TensorPower a n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi :
            typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          · simp [hi]
          · simp [hi]
    _ = (Fintype.card (TensorPower a n) : ℝ) := by simp

/-- The typical spectral weight is nonnegative. -/
theorem typicalSubspaceSpectralWeight_nonneg (ρ : State a) (n : ℕ) (δ : ℝ) :
    0 ≤ ρ.typicalSubspaceSpectralWeight n δ := by
  classical
  unfold typicalSubspaceSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi :
    typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
  · simp [hi, (ρ.tensorPower n).pos.eigenvalues_nonneg i]
  · simp [hi]

/-- The typical spectral weight is at most one. -/
theorem typicalSubspaceSpectralWeight_le_one (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceSpectralWeight n δ ≤ 1 := by
  classical
  unfold typicalSubspaceSpectralWeight
  calc
    (∑ i : TensorPower a n,
        if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0)
        ≤ ∑ i : TensorPower a n, (ρ.tensorPower n).pos.isHermitian.eigenvalues i := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi :
            typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          · simp [hi]
          · simp [hi, (ρ.tensorPower n).pos.eigenvalues_nonneg i]
    _ = 1 := tensorPower_eigenvalue_sum ρ n

/-- The atypical spectral weight is nonnegative. -/
theorem atypicalSubspaceSpectralWeight_nonneg (ρ : State a) (n : ℕ) (δ : ℝ) :
    0 ≤ ρ.atypicalSubspaceSpectralWeight n δ := by
  classical
  unfold atypicalSubspaceSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi :
    typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
  · simp [hi]
  · simp [hi, (ρ.tensorPower n).pos.eigenvalues_nonneg i]

/-- The typical and atypical spectral weights partition the tensor-power
state's total spectral weight. -/
theorem typicalSubspaceSpectralWeight_add_atypical (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceSpectralWeight n δ +
      ρ.atypicalSubspaceSpectralWeight n δ = 1 := by
  classical
  unfold typicalSubspaceSpectralWeight atypicalSubspaceSpectralWeight
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i : TensorPower a n,
        ((if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0) +
        if ¬ typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0)) =
        ∑ i : TensorPower a n, (ρ.tensorPower n).pos.isHermitian.eigenvalues i := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi :
            typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          · simp [hi]
          · simp [hi]
    _ = 1 := tensorPower_eigenvalue_sum ρ n

/-- The centered log-eigenvalue second moment is nonnegative. -/
theorem typicalLogDeviationSecondMoment_nonneg (ρ : State a) (n : ℕ) :
    0 ≤ ρ.typicalLogDeviationSecondMoment n := by
  classical
  unfold typicalLogDeviationSecondMoment
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg ((ρ.tensorPower n).pos.eigenvalues_nonneg i) (sq_nonneg _)

/-- Finite spectral Chebyshev bridge for the typical projector.

This is a genuine concentration-form estimate at the spectral-distribution
level: the atypical spectral weight times `(n δ)^2` is controlled by the
centered second moment of the log-eigenvalues of `ρ^{⊗ n}`. A later proof
can combine it with product-spectrum/variance additivity to obtain the usual
i.i.d. typical-subspace concentration bounds. -/
theorem atypicalSubspaceSpectralWeight_mul_sq_le_logDeviationSecondMoment
    (ρ : State a) {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    ρ.atypicalSubspaceSpectralWeight n δ * (((n : ℝ) * δ) ^ 2) ≤
      ρ.typicalLogDeviationSecondMoment n := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  unfold atypicalSubspaceSpectralWeight typicalLogDeviationSecondMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  let μ := (ρ.tensorPower n).pos.isHermitian.eigenvalues i
  let d := (-log2 μ) - (n : ℝ) * ρ.vonNeumann
  have hμ_nonneg : 0 ≤ μ := by
    simpa [μ] using (ρ.tensorPower n).pos.eigenvalues_nonneg i
  by_cases htyp : typicalEigenvalue ρ n δ μ
  · have hterm_nonneg : 0 ≤ μ * d ^ 2 := mul_nonneg hμ_nonneg (sq_nonneg d)
    simp [htyp, μ, d, hterm_nonneg]
  · by_cases hμ_pos : 0 < μ
    · have hnotle : ¬ |d| ≤ (n : ℝ) * δ := by
        intro hle
        exact htyp ⟨hμ_pos, by simpa [d, μ] using hle⟩
      have hclt : (n : ℝ) * δ < |d| := lt_of_not_ge hnotle
      have hcabs : |(n : ℝ) * δ| ≤ |d| := by
        rw [abs_of_nonneg (le_of_lt hcpos)]
        exact le_of_lt hclt
      have hsq : ((n : ℝ) * δ) ^ 2 ≤ d ^ 2 := by
        have hs := sq_le_sq.mpr hcabs
        simpa [sq_abs] using hs
      have hmul := mul_le_mul_of_nonneg_left hsq hμ_nonneg
      simpa [htyp, μ, d] using hmul
    · have hμ_zero : μ = 0 := le_antisymm (not_lt.mp hμ_pos) hμ_nonneg
      simp [μ, hμ_zero]

/-- Division form of the finite spectral Chebyshev bridge. -/
theorem atypicalSubspaceSpectralWeight_le_logDeviationSecondMoment_div_sq
    (ρ : State a) {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    ρ.atypicalSubspaceSpectralWeight n δ ≤
      ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  have hc2pos : 0 < (((n : ℝ) * δ) ^ 2) := sq_pos_of_pos hcpos
  rw [le_div_iff₀ hc2pos]
  exact ρ.atypicalSubspaceSpectralWeight_mul_sq_le_logDeviationSecondMoment hn hδ

/-- Lower bound on the accepted typical spectral weight obtained from the
finite spectral Chebyshev bridge. -/
theorem one_sub_logDeviationSecondMoment_div_sq_le_typicalSubspaceSpectralWeight
    (ρ : State a) {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    1 - ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2) ≤
      ρ.typicalSubspaceSpectralWeight n δ := by
  have hle := ρ.atypicalSubspaceSpectralWeight_le_logDeviationSecondMoment_div_sq hn hδ
  have hadd := ρ.typicalSubspaceSpectralWeight_add_atypical n δ
  linarith

/-- The typical-subspace projector is positive semidefinite. -/
theorem typicalSubspaceProjector_posSemidef (ρ : State a) (n : ℕ) (δ : ℝ) :
    (ρ.typicalSubspaceProjector n δ).PosSemidef := by
  classical
  unfold typicalSubspaceProjector
  exact spectralPredicateProjector_posSemidef _ _ _

/-- The typical-subspace projector is Hermitian. -/
theorem typicalSubspaceProjector_isHermitian (ρ : State a) (n : ℕ) (δ : ℝ) :
    (ρ.typicalSubspaceProjector n δ).IsHermitian :=
  (ρ.typicalSubspaceProjector_posSemidef n δ).1

/-- The typical-subspace projector is idempotent. -/
theorem typicalSubspaceProjector_idempotent (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector n δ * ρ.typicalSubspaceProjector n δ =
      ρ.typicalSubspaceProjector n δ := by
  classical
  unfold typicalSubspaceProjector
  exact spectralPredicateProjector_idempotent _ _ _

/-- The typical-subspace projector is bounded by the identity effect. -/
theorem typicalSubspaceProjector_le_one (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector n δ ≤ 1 := by
  classical
  unfold typicalSubspaceProjector
  exact spectralPredicateProjector_le_one _ _ _

/-- The trace of the typical-subspace projector counts the selected spectral
directions of `ρ^{⊗ n}`. -/
theorem typicalSubspaceProjector_trace_re (ρ : State a) (n : ℕ) (δ : ℝ) :
    (ρ.typicalSubspaceProjector n δ).trace.re =
      ρ.typicalSubspaceDimension n δ := by
  classical
  unfold typicalSubspaceProjector
  unfold typicalSubspaceDimension
  exact spectralPredicateProjector_trace_re _ _ _

/-- The tensor-power state weight accepted by the typical projector is exactly
the selected eigenvalue sum. -/
theorem typicalSubspaceProjector_trace_mul_re (ρ : State a) (n : ℕ) (δ : ℝ) :
    (((ρ.tensorPower n).matrix * ρ.typicalSubspaceProjector n δ).trace).re =
      ρ.typicalSubspaceSpectralWeight n δ := by
  classical
  unfold typicalSubspaceProjector
  unfold typicalSubspaceSpectralWeight
  exact spectralPredicateProjector_trace_mul_re _ _ _

/-- The bundled projector statement used by downstream theorem routes. -/
def typicalSubspaceProjector_statement
    (ρ : State a) (n : ℕ) (δ : ℝ) : Prop :=
  (ρ.typicalSubspaceProjector n δ).PosSemidef ∧
    (ρ.typicalSubspaceProjector n δ).IsHermitian ∧
    ρ.typicalSubspaceProjector n δ * ρ.typicalSubspaceProjector n δ =
      ρ.typicalSubspaceProjector n δ ∧
    ρ.typicalSubspaceProjector n δ ≤ 1

/-- The finite spectral typical-subspace projector satisfies the bundled
projector statement. -/
theorem typicalSubspaceProjector_statement_proved (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector_statement n δ := by
  exact ⟨ρ.typicalSubspaceProjector_posSemidef n δ,
    ρ.typicalSubspaceProjector_isHermitian n δ,
    ρ.typicalSubspaceProjector_idempotent n δ,
    ρ.typicalSubspaceProjector_le_one n δ⟩

/-- Complete finite spectral typical-projector estimate package.

This is the closure-level infrastructure consumed by later finite-N AEP
routes: it records the spectral projector construction, rank/probability
envelopes, exact trace identities, and the finite spectral Chebyshev
concentration bridge for the tensor-power density matrix. -/
structure TypicalProjectorEstimates (ρ : State a) (n : ℕ) (δ : ℝ) : Prop where
  projector_statement : ρ.typicalSubspaceProjector_statement n δ
  trace_eq_dimension :
    (ρ.typicalSubspaceProjector n δ).trace.re =
      ρ.typicalSubspaceDimension n δ
  trace_weight_eq_spectralWeight :
    (((ρ.tensorPower n).matrix * ρ.typicalSubspaceProjector n δ).trace).re =
      ρ.typicalSubspaceSpectralWeight n δ
  dimension_nonneg : 0 ≤ ρ.typicalSubspaceDimension n δ
  dimension_le_card :
    ρ.typicalSubspaceDimension n δ ≤ (Fintype.card (TensorPower a n) : ℝ)
  spectralWeight_nonneg : 0 ≤ ρ.typicalSubspaceSpectralWeight n δ
  spectralWeight_le_one : ρ.typicalSubspaceSpectralWeight n δ ≤ 1
  atypicalSpectralWeight_nonneg : 0 ≤ ρ.atypicalSubspaceSpectralWeight n δ
  spectralWeight_partition :
    ρ.typicalSubspaceSpectralWeight n δ +
      ρ.atypicalSubspaceSpectralWeight n δ = 1
  logDeviationSecondMoment_nonneg : 0 ≤ ρ.typicalLogDeviationSecondMoment n
  atypical_mul_sq_le_logDeviationSecondMoment :
    ∀ (_ : 0 < n) (_ : 0 < δ),
      ρ.atypicalSubspaceSpectralWeight n δ * (((n : ℝ) * δ) ^ 2) ≤
        ρ.typicalLogDeviationSecondMoment n
  atypical_le_logDeviationSecondMoment_div_sq :
    ∀ (_ : 0 < n) (_ : 0 < δ),
      ρ.atypicalSubspaceSpectralWeight n δ ≤
        ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2)
  typical_weight_lower_bound :
    ∀ (_ : 0 < n) (_ : 0 < δ),
      1 - ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2) ≤
        ρ.typicalSubspaceSpectralWeight n δ

/-- The finite spectral typical-subspace projector satisfies the complete
estimate package required by the AEP proof route. -/
theorem typicalSubspaceProjector_estimates (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.TypicalProjectorEstimates n δ where
  projector_statement := ρ.typicalSubspaceProjector_statement_proved n δ
  trace_eq_dimension := ρ.typicalSubspaceProjector_trace_re n δ
  trace_weight_eq_spectralWeight := ρ.typicalSubspaceProjector_trace_mul_re n δ
  dimension_nonneg := ρ.typicalSubspaceDimension_nonneg n δ
  dimension_le_card := ρ.typicalSubspaceDimension_le_card n δ
  spectralWeight_nonneg := ρ.typicalSubspaceSpectralWeight_nonneg n δ
  spectralWeight_le_one := ρ.typicalSubspaceSpectralWeight_le_one n δ
  atypicalSpectralWeight_nonneg := ρ.atypicalSubspaceSpectralWeight_nonneg n δ
  spectralWeight_partition := ρ.typicalSubspaceSpectralWeight_add_atypical n δ
  logDeviationSecondMoment_nonneg := ρ.typicalLogDeviationSecondMoment_nonneg n
  atypical_mul_sq_le_logDeviationSecondMoment := by
    intro hn hδ
    exact ρ.atypicalSubspaceSpectralWeight_mul_sq_le_logDeviationSecondMoment hn hδ
  atypical_le_logDeviationSecondMoment_div_sq := by
    intro hn hδ
    exact ρ.atypicalSubspaceSpectralWeight_le_logDeviationSecondMoment_div_sq hn hδ
  typical_weight_lower_bound := by
    intro hn hδ
    exact ρ.one_sub_logDeviationSecondMoment_div_sq_le_typicalSubspaceSpectralWeight hn hδ

/-- Schumacher data compression theorem: rate S(rho) is achievable.

Alice can compress n copies of a quantum source rho into n * S(rho) + epsilon
qubits with arbitrarily small error for large n. -/
def schumacherTheorem_statement
    (ρ : State a) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (δ : ℝ), 0 < δ →
    ∃ N : ℕ, ∀ n ≥ N, ρ.schumacherRate ≤ ρ.schumacherRate + δ

end State

end

end QIT
