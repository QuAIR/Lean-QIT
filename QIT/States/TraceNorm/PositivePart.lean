/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.Spectral

/-!
# Positive part and spectral projector API

Finite-dimensional positive-part support projectors for Hermitian complex
matrices.  This module exposes the trace-max bridge needed by the Audenaert
positive-operator trace inequality route:

* `positiveSpectralProjector H hH`: the spectral projector onto the strictly
  positive eigenspaces of a Hermitian matrix `H`;
* `positiveSpectralProjector_score_eq_posPart_trace`: that projector attains
  `Tr(H⁺)`;
* `hermitian_trace_mul_effect_le_posPart_trace`: every effect `0 ≤ E ≤ 1`
  has `Re Tr(H E) ≤ Re Tr(H⁺)`.

The source route uses the projector onto the range of the positive part and the
maximization of `Tr(QH)` over self-adjoint projectors
[Audenaert2006QuantumChernoff, audenaert-2006-quantum-chernoff.tex:324-331]
and [Audenaert2006QuantumChernoff,
audenaert-2006-quantum-chernoff.tex:345-350].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u

noncomputable section

/-- The spectral projector onto the strictly positive eigenspaces of a Hermitian matrix. -/
def positiveSpectralProjector {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) : CMatrix a :=
  (hH.eigenvectorUnitary : CMatrix a) *
    Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
      star (hH.eigenvectorUnitary : CMatrix a)

private def eigenbasisConjugate {a : Type u} [Fintype a] [DecidableEq a]
    {H : CMatrix a} (hH : H.IsHermitian) (E : CMatrix a) : CMatrix a :=
  star (hH.eigenvectorUnitary : CMatrix a) * E * (hH.eigenvectorUnitary : CMatrix a)

private theorem trace_diagonal_mul_eq_sum {a : Type u} [Fintype a] [DecidableEq a]
    (d : a → ℂ) (E : CMatrix a) :
    (Matrix.diagonal d * E).trace = ∑ i, d i * E i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

private theorem real_posPart_eq_if (x : ℝ) : x⁺ = if 0 < x then x else 0 := by
  rw [_root_.posPart_def]
  split_ifs with hx
  · exact max_eq_left hx.le
  · exact max_eq_right (le_of_not_gt hx)

/-- The positive spectral projector is positive semidefinite. -/
theorem positiveSpectralProjector_posSemidef {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    (positiveSpectralProjector H hH).PosSemidef := by
  classical
  unfold positiveSpectralProjector
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < hH.eigenvalues i
  · simp [hi]
  · simp [hi]

/-- The positive spectral projector is Hermitian. -/
theorem positiveSpectralProjector_isHermitian {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    (positiveSpectralProjector H hH).IsHermitian :=
  (positiveSpectralProjector_posSemidef H hH).1

/-- The positive spectral projector is idempotent. -/
theorem positiveSpectralProjector_idempotent {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH * positiveSpectralProjector H hH =
      positiveSpectralProjector H hH := by
  classical
  unfold positiveSpectralProjector
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a :=
    Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0)
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  have hD : D * D = D := by
    change
      Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i <;> simp [hi]
    · simp [Matrix.diagonal, hij]
  calc
    (U * D * star U) * (U * D * star U) =
        U * D * (star U * U) * D * star U := by
          noncomm_ring
    _ = U * D * 1 * D * star U := by rw [hU]
    _ = U * (D * D) * star U := by noncomm_ring
    _ = U * D * star U := by rw [hD]

/-- The positive spectral projector is bounded by the identity effect. -/
theorem positiveSpectralProjector_le_one {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  unfold positiveSpectralProjector
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
          Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
            star (hH.eigenvectorUnitary : CMatrix a) =
        (hH.eigenvectorUnitary : CMatrix a) *
          (1 - Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0)) *
            star (hH.eigenvectorUnitary : CMatrix a) := by
    noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  have hdiag :
      (1 - Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) :
        CMatrix a) =
        Matrix.diagonal (fun i => 1 - if 0 < hH.eigenvalues i then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal, hij]
  rw [hdiag]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < hH.eigenvalues i
  · simp [hi]
  · simp [hi]

/-- The trace of the positive part is the sum of positive eigenvalues. -/
theorem posPart_trace_re_eq_positive_eigenvalue_sum {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) :
    (H⁺).trace.re = ∑ i, if 0 < hH.eigenvalues i then hH.eigenvalues i else 0 := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  rw [hH.cfc_eq]
  rw [Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  simp [Matrix.trace, real_posPart_eq_if]

/-- For a trace-zero Hermitian matrix, the trace norm is twice the trace of
the positive part. -/
theorem traceNorm_eq_two_posPart_trace_re_of_trace_zero {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) (htr : H.trace = 0) :
    traceNorm H = 2 * (H⁺).trace.re := by
  have hAbs : H⁺ + H⁻ = CFC.abs H :=
    CFC.posPart_add_negPart H hH.isSelfAdjoint
  have hSub : H⁺ - H⁻ = H :=
    CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have htrace_sub : (H⁺).trace.re - (H⁻).trace.re = 0 := by
    have h := congrArg Complex.re (congrArg Matrix.trace hSub)
    rw [htr] at h
    simpa [Matrix.trace_sub] using h
  have htrace_abs : (CFC.abs H).trace.re = (H⁺).trace.re + (H⁻).trace.re := by
    have h := congrArg Complex.re (congrArg Matrix.trace hAbs)
    simpa [Matrix.trace_add] using h.symm
  rw [show traceNorm H = (CFC.abs H).trace.re by rfl, htrace_abs]
  linarith

private theorem hermitian_trace_mul_eq_sum_eigenbasis_diag {a : Type u}
    [Fintype a] [DecidableEq a] (H E : CMatrix a) (hH : H.IsHermitian) :
    ((H * E).trace).re =
      ∑ i, hH.eigenvalues i * ((eigenbasisConjugate hH E) i i).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))
  have hHdiag : H = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hH.spectral_theorem
  have htrace :
      (H * E).trace = (D * eigenbasisConjugate hH E).trace := by
    calc
      (H * E).trace =
          (((U : CMatrix a) * D * star (U : CMatrix a)) * E).trace := by
            simp [hHdiag]
      _ = ((U : CMatrix a) * D * (star (U : CMatrix a) * E)).trace := by
            simp [Matrix.mul_assoc]
      _ = ((star (U : CMatrix a) * E) * (U : CMatrix a) * D).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (D * eigenbasisConjugate hH E).trace := by
            rw [Matrix.trace_mul_comm]
            simp [eigenbasisConjugate, U, Matrix.mul_assoc]
  rw [htrace]
  rw [trace_diagonal_mul_eq_sum]
  simp [Complex.re_sum, mul_comm]

private theorem eigenbasisConjugate_posSemidef {a : Type u} [Fintype a] [DecidableEq a]
    {H E : CMatrix a} (hH : H.IsHermitian) (hE : E.PosSemidef) :
    (eigenbasisConjugate hH E).PosSemidef := by
  unfold eigenbasisConjugate
  rw [Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  exact hE

private theorem eigenbasisConjugate_le_one {a : Type u} [Fintype a] [DecidableEq a]
    {H E : CMatrix a} (hH : H.IsHermitian) (hE : E ≤ 1) :
    eigenbasisConjugate hH E ≤ 1 := by
  rw [Matrix.le_iff] at hE ⊢
  unfold eigenbasisConjugate
  have hOne :
      (1 : CMatrix a) =
        star (hH.eigenvectorUnitary : CMatrix a) * 1 *
          (hH.eigenvectorUnitary : CMatrix a) := by
    simp
  rw [hOne]
  have hsub :
      star (hH.eigenvectorUnitary : CMatrix a) * 1 * (hH.eigenvectorUnitary : CMatrix a) -
        star (hH.eigenvectorUnitary : CMatrix a) * E *
          (hH.eigenvectorUnitary : CMatrix a) =
        star (hH.eigenvectorUnitary : CMatrix a) * (1 - E) *
          (hH.eigenvectorUnitary : CMatrix a) := by
    noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  exact hE

private theorem effect_diag_re_nonneg {a : Type u} {E : CMatrix a} (hE : E.PosSemidef)
    (i : a) :
    0 ≤ (E i i).re :=
  (Complex.nonneg_iff.mp (hE.diag_nonneg (i := i))).1

private theorem effect_diag_re_le_one {a : Type u} [DecidableEq a] {E : CMatrix a}
    (hE : E ≤ 1) (i : a) :
    (E i i).re ≤ 1 := by
  rw [Matrix.le_iff] at hE
  have h := (Complex.nonneg_iff.mp (hE.diag_nonneg (i := i))).1
  have hdiag : ((1 - E) i i).re = 1 - (E i i).re := by
    simp
  linarith

/-- Trace-max upper bound for Hermitian positive parts.  This is stated for
all effects `0 ≤ E ≤ 1`, hence it applies in particular to self-adjoint
projectors. -/
theorem hermitian_trace_mul_effect_le_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (H E : CMatrix a)
    (hH : H.IsHermitian) (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    ((H * E).trace).re ≤ (H⁺).trace.re := by
  classical
  rw [hermitian_trace_mul_eq_sum_eigenbasis_diag H E hH,
    posPart_trace_re_eq_positive_eigenvalue_sum H hH]
  apply Finset.sum_le_sum
  intro i _
  let E' := eigenbasisConjugate hH E
  have hE'pos : E'.PosSemidef := eigenbasisConjugate_posSemidef hH hEpos
  have hE'le : E' ≤ 1 := eigenbasisConjugate_le_one hH hEle
  have hdiag_nonneg : 0 ≤ (E' i i).re := effect_diag_re_nonneg hE'pos i
  have hdiag_le : (E' i i).re ≤ 1 := effect_diag_re_le_one hE'le i
  change hH.eigenvalues i * (E' i i).re ≤
    if 0 < hH.eigenvalues i then hH.eigenvalues i else 0
  by_cases hlam : 0 < hH.eigenvalues i
  · simp [hlam]
    nlinarith
  · have hlam_le : hH.eigenvalues i ≤ 0 := le_of_not_gt hlam
    simp [hlam]
    exact mul_nonpos_of_nonpos_of_nonneg hlam_le hdiag_nonneg

/-- The positive spectral projector attains the positive-part trace. -/
theorem positiveSpectralProjector_score_eq_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) :
    ((H * positiveSpectralProjector H hH).trace).re = (H⁺).trace.re := by
  classical
  rw [hermitian_trace_mul_eq_sum_eigenbasis_diag H (positiveSpectralProjector H hH) hH,
    posPart_trace_re_eq_positive_eigenvalue_sum H hH]
  apply Finset.sum_congr rfl
  intro i _
  have hdiag :
      (eigenbasisConjugate hH (positiveSpectralProjector H hH)) i i =
        (if 0 < hH.eigenvalues i then (1 : ℂ) else 0) := by
    unfold eigenbasisConjugate positiveSpectralProjector
    have hassoc :
        star (hH.eigenvectorUnitary : CMatrix a) *
              (((hH.eigenvectorUnitary : CMatrix a) *
                  Matrix.diagonal (fun j => if 0 < hH.eigenvalues j then (1 : ℂ) else 0)) *
                star (hH.eigenvectorUnitary : CMatrix a)) *
            (hH.eigenvectorUnitary : CMatrix a) =
          (star (hH.eigenvectorUnitary : CMatrix a) * (hH.eigenvectorUnitary : CMatrix a)) *
              Matrix.diagonal (fun j => if 0 < hH.eigenvalues j then (1 : ℂ) else 0) *
            (star (hH.eigenvectorUnitary : CMatrix a) * (hH.eigenvectorUnitary : CMatrix a)) := by
      noncomm_ring
    rw [hassoc]
    rw [Unitary.coe_star_mul_self]
    simp
  rw [hdiag]
  by_cases hlam : 0 < hH.eigenvalues i
  · simp [hlam]
  · simp [hlam]

/-- Positive-part trace-max package: the positive spectral projector attains
`Tr(H⁺)`, and every effect is bounded above by that value. -/
theorem positiveSpectralProjector_trace_max_effect {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) :
    ((H * positiveSpectralProjector H hH).trace).re = (H⁺).trace.re ∧
      ∀ E : CMatrix a, E.PosSemidef → E ≤ 1 →
        ((H * E).trace).re ≤ (H⁺).trace.re :=
  ⟨positiveSpectralProjector_score_eq_posPart_trace H hH,
    fun E hEpos hEle => hermitian_trace_mul_effect_le_posPart_trace H E hH hEpos hEle⟩

/-- Difference of density matrices has trace zero. -/
theorem state_sub_trace_zero {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) :
    (rho.matrix - sigma.matrix).trace = 0 := by
  rw [Matrix.trace_sub, rho.trace_eq_one, sigma.trace_eq_one]
  norm_num

/-- Normalized trace distance between states is the trace of the positive part
of their Hermitian difference. -/
theorem State.normalizedTraceDistance_eq_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    rho.normalizedTraceDistance sigma = ((rho.matrix - sigma.matrix)⁺).trace.re := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  have hH : H.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  have htr : H.trace = 0 := by
    simpa [H] using state_sub_trace_zero rho sigma
  have hnorm := traceNorm_eq_two_posPart_trace_re_of_trace_zero H hH htr
  calc
    rho.normalizedTraceDistance sigma = (1 / 2 : ℝ) * traceNorm H := by rfl
    _ = (1 / 2 : ℝ) * (2 * (H⁺).trace.re) := by rw [hnorm]
    _ = (H⁺).trace.re := by ring

/-- Backward-compatible unqualified spelling of the state positive-part trace
formula. -/
theorem normalizedTraceDistance_eq_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    rho.normalizedTraceDistance sigma = ((rho.matrix - sigma.matrix)⁺).trace.re :=
  State.normalizedTraceDistance_eq_posPart_trace rho sigma

end

end QIT
