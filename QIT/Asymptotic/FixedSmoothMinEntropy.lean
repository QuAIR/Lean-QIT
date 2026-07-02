/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.Smooth
public import QIT.OneShot.SmoothEndpoint
public import QIT.Information.Renyi.AlphaEntropyContinuity
public import QIT.Information.Renyi.ConditionalPetzRenyi
public import QIT.Asymptotic.AEP
public import QIT.Information.Renyi.RpowOperatorConvex
public import QIT.States.Geometry.FuchsVdG
public import QIT.OneShot.GentleMeasurement
public import QIT.HypothesisTesting.Audenaert
public import QIT.States.PosSqrtOrder
public import QIT.Util.BlockMatrix
public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Fixed-side smooth conditional min-entropy

This module adds the fixed-reference side of the conditional min-entropy API.
The existing `State.conditionalMinEntropy` and `State.smoothConditionalMinEntropy`
optimize over the conditioning state.  For the finite fully quantum AEP route,
we also need the candidate where the same reference state `σ_B` is kept fixed
through the purified-distance smoothing ball, plus the order bridge into the
optimized quantity.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Filter

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The Petz trace functional `Tr(A^α B^(1-α))`, kept as a real scalar.

The positive-definite hypotheses needed by most analytic uses stay on the
lemmas that consume the definition. -/
def cMatrixPetzTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) : ℝ :=
  ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re

/-- Vectorized form of the complex Petz trace kernel.

This is the Hilbert-Schmidt-space entry point for the Petz perspective route:
left multiplication by `A^α` and right multiplication by `B^(1-α)` are encoded
as a Kronecker matrix acting on `Matrix.vec 1`. -/
theorem cMatrixPetzTrace_trace_eq_vec_one_kronecker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    (CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace =
      dotProduct (star (Matrix.vec (1 : CMatrix ι)))
        (Matrix.mulVec
          (Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
            (CFC.rpow A alpha))
          (Matrix.vec (1 : CMatrix ι))) := by
  have hmulvec :
      Matrix.mulVec
          (Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
            (CFC.rpow A alpha))
          (Matrix.vec (1 : CMatrix ι)) =
        Matrix.vec (CFC.rpow A alpha * (1 : CMatrix ι) *
          (Matrix.transpose (Matrix.transpose (CFC.rpow B (1 - alpha))))) := by
    simpa using
      (Matrix.kronecker_mulVec_vec
        (A := CFC.rpow A alpha) (X := (1 : CMatrix ι))
        (B := Matrix.transpose (CFC.rpow B (1 - alpha))))
  rw [hmulvec]
  rw [Matrix.mul_one]
  rw [Matrix.transpose_transpose]
  rw [Matrix.star_vec_dotProduct_vec]
  rw [Matrix.conjTranspose_one]
  rw [Matrix.one_mul]

/-- Real-valued vectorized form of `cMatrixPetzTrace`. -/
theorem cMatrixPetzTrace_eq_vec_one_kronecker_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTrace A B alpha =
      (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
        (Matrix.mulVec
          (Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
            (CFC.rpow A alpha))
          (Matrix.vec (1 : CMatrix ι)))).re := by
  rw [cMatrixPetzTrace]
  exact congrArg Complex.re (cMatrixPetzTrace_trace_eq_vec_one_kronecker A B alpha)

private theorem cMatrix_rpow_unitary_conj_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) (s : ℝ) :
    CFC.rpow (star (U : CMatrix ι) * A * (U : CMatrix ι)) s =
      star (U : CMatrix ι) * CFC.rpow A s * (U : CMatrix ι) := by
  change (star (U : CMatrix ι) * A * (U : CMatrix ι)) ^ s =
    star (U : CMatrix ι) * (A ^ s) * (U : CMatrix ι)
  have hmap_nonneg : 0 ≤ star (U : CMatrix ι) * A * (U : CMatrix ι) :=
    Matrix.nonneg_iff_posSemidef.mpr (by
      simpa [Matrix.mul_assoc] using
        hA.posSemidef.conjTranspose_mul_mul_same (U : CMatrix ι))
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := star (U : CMatrix ι) * A * (U : CMatrix ι))
    (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [Unitary.conjStarAlgAut_symm_apply] using
    (StarAlgHomClass.map_cfc
      ((Unitary.conjStarAlgAut ℂ (CMatrix ι) U).symm)
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact
          (Real.continuousAt_rpow_const x s
            (.inl (ne_of_gt
              ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix ι => star (U : CMatrix ι) * A * (U : CMatrix ι)
        fun_prop)).symm

/-- Petz trace is invariant under simultaneous unitary conjugation, for
positive-definite inputs and every real exponent. -/
theorem cMatrixPetzTrace_unitary_conj_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosDef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) :
    cMatrixPetzTrace (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha =
      cMatrixPetzTrace A B alpha := by
  unfold cMatrixPetzTrace
  rw [cMatrix_rpow_unitary_conj_posDef hA U alpha,
    cMatrix_rpow_unitary_conj_posDef hB U (1 - alpha)]
  let Apow : CMatrix ι := CFC.rpow A alpha
  let Bpow : CMatrix ι := CFC.rpow B (1 - alpha)
  change (((star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
      (star (U : CMatrix ι) * Bpow * (U : CMatrix ι))).trace).re =
    (Apow * Bpow).trace.re
  have hU : (U : CMatrix ι) * star (U : CMatrix ι) = 1 :=
    Unitary.coe_mul_star_self U
  have hprod :
      (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
          (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
        star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι) := by
    rw [show
        (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
            (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
          star (U : CMatrix ι) * Apow *
            ((U : CMatrix ι) * star (U : CMatrix ι)) *
              Bpow * (U : CMatrix ι) by noncomm_ring]
    rw [hU]
    noncomm_ring
  have htrace :
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
        (Apow * Bpow).trace := by
    calc
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
          ((U : CMatrix ι) * (star (U : CMatrix ι) * (Apow * Bpow))).trace := by
            exact Matrix.trace_mul_comm
              (star (U : CMatrix ι) * (Apow * Bpow)) (U : CMatrix ι)
      _ = (((U : CMatrix ι) * star (U : CMatrix ι)) * (Apow * Bpow)).trace := by
            congr 1
            rw [Matrix.mul_assoc]
      _ = (Apow * Bpow).trace := by
            rw [hU, Matrix.one_mul]
  rw [hprod]
  exact congrArg Complex.re htrace

/-- Petz trace is invariant under simultaneous unitary conjugation when the
left input is PSD and the left exponent is nonnegative. -/
theorem cMatrixPetzTrace_unitary_conj_eq_posSemidef_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha) :
    cMatrixPetzTrace (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha =
      cMatrixPetzTrace A B alpha := by
  unfold cMatrixPetzTrace
  rw [cMatrix_rpow_unitary_conj hA U halpha_nonneg,
    cMatrix_rpow_unitary_conj_posDef hB U (1 - alpha)]
  let Apow : CMatrix ι := CFC.rpow A alpha
  let Bpow : CMatrix ι := CFC.rpow B (1 - alpha)
  change (((star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
      (star (U : CMatrix ι) * Bpow * (U : CMatrix ι))).trace).re =
    (Apow * Bpow).trace.re
  have hU : (U : CMatrix ι) * star (U : CMatrix ι) = 1 :=
    Unitary.coe_mul_star_self U
  have hprod :
      (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
          (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
        star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι) := by
    rw [show
        (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
            (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
          star (U : CMatrix ι) * Apow *
            ((U : CMatrix ι) * star (U : CMatrix ι)) *
              Bpow * (U : CMatrix ι) by noncomm_ring]
    rw [hU]
    noncomm_ring
  have htrace :
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
        (Apow * Bpow).trace := by
    calc
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
          ((U : CMatrix ι) * (star (U : CMatrix ι) * (Apow * Bpow))).trace := by
            exact Matrix.trace_mul_comm
              (star (U : CMatrix ι) * (Apow * Bpow)) (U : CMatrix ι)
      _ = (((U : CMatrix ι) * star (U : CMatrix ι)) * (Apow * Bpow)).trace := by
            congr 1
            rw [Matrix.mul_assoc]
      _ = (Apow * Bpow).trace := by
            rw [hU, Matrix.one_mul]
  rw [hprod]
  exact congrArg Complex.re htrace

/-- The Petz trace effect-variational inequality needed to turn a spectral
threshold into a positive-part bound.

This is the remaining noncommutative input in the TCR smooth-min route: it
should follow from the operator-convex/perspective form of `x ↦ x^α` for
`1 < α ≤ 2` (or an equivalent Petz-Hölder/Young inequality). Instantiating this
at the positive spectral projector of `A - λB` gives
`Tr((A - λB)⁺) ≤ λ^(1-α) Tr(A^α B^(1-α))`. -/
def cMatrixPetzTraceEffectVariational
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (lambda alpha : ℝ) : Prop :=
  ∀ E : CMatrix ι, E.PosSemidef → E ≤ 1 →
    (((E * A).trace).re - lambda * ((E * B).trace).re) ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re

/-- Dephasing/pinching in the orthonormal basis encoded by a unitary `U`.

This is the finite matrix form of
`X ↦ ∑ᵢ |ψᵢ⟩⟨ψᵢ| X |ψᵢ⟩⟨ψᵢ|`, written by moving `X` into the `U` basis,
discarding off-diagonal entries, and conjugating back. The diagonal values are
taken as real parts, which is the source-facing form used for Hermitian
positive inputs. -/
def cMatrixUnitaryDephase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : CMatrix ι) : CMatrix ι :=
  (U : CMatrix ι) *
    (Matrix.diagonal fun i =>
      ((((star (U : CMatrix ι) * X * (U : CMatrix ι)) i i).re : ℝ) : ℂ) :
        CMatrix ι) *
      star (U : CMatrix ι)

/-- The coordinate sign attached to a Boolean sign choice. -/
def cMatrixSignScalar
    {ι : Type*} (s : ι → Bool) (i : ι) : ℂ :=
  if s i then -1 else 1

@[simp]
theorem cMatrixSignScalar_star
    {ι : Type*} (s : ι → Bool) (i : ι) :
    star (cMatrixSignScalar s i) = cMatrixSignScalar s i := by
  by_cases h : s i <;> simp [cMatrixSignScalar, h]

@[simp]
theorem cMatrixSignScalar_mul_self
    {ι : Type*} (s : ι → Bool) (i : ι) :
    cMatrixSignScalar s i * cMatrixSignScalar s i = 1 := by
  by_cases h : s i <;> simp [cMatrixSignScalar, h]

/-- Diagonal sign unitary for a Boolean sign choice on coordinates. -/
def cMatrixSignUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Bool) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal fun i => cMatrixSignScalar s i, by
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar :
        star (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) =
          (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.star_apply, Matrix.diagonal]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [Matrix.star_apply, Matrix.diagonal, hij, hji]
    rw [hstar, Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]⟩

@[simp]
theorem cMatrixSignUnitary_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Bool) (i j : ι) :
    (cMatrixSignUnitary s : CMatrix ι) i j =
      if i = j then cMatrixSignScalar s i else 0 := by
  simp [cMatrixSignUnitary, Matrix.diagonal]

/-- Conjugating by a coordinate sign unitary multiplies an entry by the two
endpoint signs. -/
theorem cMatrixSignUnitary_conj_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Bool) (X : CMatrix ι) (i j : ι) :
    (star (cMatrixSignUnitary s : CMatrix ι) * X *
        (cMatrixSignUnitary s : CMatrix ι)) i j =
      cMatrixSignScalar s i * X i j * cMatrixSignScalar s j := by
  change (star (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) * X *
      (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι)) i j =
    cMatrixSignScalar s i * X i j * cMatrixSignScalar s j
  have hstar :
      star (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) =
        (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.star_apply, Matrix.diagonal]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Matrix.star_apply, Matrix.diagonal, hij, hji]
  rw [hstar, Matrix.mul_diagonal, Matrix.diagonal_mul]

private def cMatrixSignToggle
    {ι : Type*} [DecidableEq ι] (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun s := Function.update s i (!(s i))
  invFun s := Function.update s i (!(s i))
  left_inv := by
    intro s
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Function.update, hk]
  right_inv := by
    intro s
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Function.update, hk]

private theorem cMatrixSignScalar_toggle_self
    {ι : Type*} [DecidableEq ι] (s : ι → Bool) (i : ι) :
    cMatrixSignScalar (cMatrixSignToggle i s) i = -cMatrixSignScalar s i := by
  by_cases h : s i <;> simp [cMatrixSignScalar, cMatrixSignToggle, Function.update, h]

private theorem cMatrixSignScalar_toggle_of_ne
    {ι : Type*} [DecidableEq ι] (s : ι → Bool) {i j : ι} (hij : i ≠ j) :
    cMatrixSignScalar (cMatrixSignToggle i s) j = cMatrixSignScalar s j := by
  have hji : j ≠ i := fun h => hij h.symm
  simp [cMatrixSignScalar, cMatrixSignToggle, Function.update, hji]

private theorem cMatrixSign_sum_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) {i j : ι} (hij : i ≠ j) :
    ∑ s : ι → Bool, cMatrixSignScalar s i * X i j * cMatrixSignScalar s j = 0 := by
  classical
  let f : (ι → Bool) → ℂ := fun s =>
    cMatrixSignScalar s i * X i j * cMatrixSignScalar s j
  let S : ℂ := ∑ s : ι → Bool, f s
  have htoggle : S = ∑ s : ι → Bool, f (cMatrixSignToggle i s) := by
    simpa [S] using ((cMatrixSignToggle i).sum_comp f).symm
  have hneg_terms : ∀ s : ι → Bool, f (cMatrixSignToggle i s) = -f s := by
    intro s
    simp [f, cMatrixSignScalar_toggle_self, cMatrixSignScalar_toggle_of_ne s hij,
      neg_mul]
  have hS_neg : S = -S := by
    calc
      S = ∑ s : ι → Bool, f (cMatrixSignToggle i s) := htoggle
      _ = ∑ s : ι → Bool, -f s := by
          exact Finset.sum_congr rfl fun s _ => hneg_terms s
      _ = -S := by simp [S]
  have hdouble : S + S = 0 := by
    nth_rw 1 [hS_neg]
    abel
  have htwo : (2 : ℂ) * S = 0 := by
    simpa [two_mul] using hdouble
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne

/-- Entrywise form of the sign-unitary average: it keeps diagonal entries and
cancels off-diagonal entries. -/
theorem cMatrixSignAverage_conj_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) (i j : ι) :
    (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i j =
      if i = j then X i j else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    have hsum :
        (∑ s : ι → Bool,
          (star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i i) =
          Fintype.card (ι → Bool) • X i i := by
      calc
        (∑ s : ι → Bool,
          (star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i i)
            = ∑ _s : ι → Bool, X i i := by
                apply Finset.sum_congr rfl
                intro s _
                rw [cMatrixSignUnitary_conj_apply]
                calc
                  cMatrixSignScalar s i * X i i * cMatrixSignScalar s i =
                      (cMatrixSignScalar s i * cMatrixSignScalar s i) * X i i := by ring
                  _ = X i i := by simp
        _ = Fintype.card (ι → Bool) • X i i := by
              simp [Finset.sum_const]
    rw [Matrix.smul_apply, Matrix.sum_apply, hsum, nsmul_eq_mul]
    simp
  · have hsum :
        (∑ s : ι → Bool,
          (star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i j) = 0 := by
      simpa [cMatrixSignUnitary_conj_apply] using
        cMatrixSign_sum_offDiag X (i := i) (j := j) hij
    simp [Matrix.smul_apply, Matrix.sum_apply, hsum, hij]

/-- Off-diagonal cancellation under the coordinate sign average. -/
theorem cMatrixSignAverage_conj_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) {i j : ι} (hij : i ≠ j) :
    (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i j = 0 := by
  simpa [hij] using cMatrixSignAverage_conj_apply X i j

/-- Diagonal entries are fixed by the coordinate sign average. -/
theorem cMatrixSignAverage_conj_diag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) (i : ι) :
    (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i i = X i i := by
  simpa using cMatrixSignAverage_conj_apply X i i

/-- For Hermitian inputs, coordinate dephasing in the standard basis is the
uniform average over coordinate sign-unitary conjugates. -/
theorem cMatrixUnitaryDephase_one_eq_signAverage_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CMatrix ι} (hX : X.IsHermitian) :
    cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) X =
      ((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    have hdiag_star : star (X i i) = X i i := by
      simpa [Matrix.star_apply] using congr_fun (congr_fun hX.eq i) i
    have hdiag_im : (X i i).im = 0 := by
      have h := congrArg Complex.im hdiag_star
      simp at h
      linarith
    have hdiag : (((X i i).re : ℝ) : ℂ) = X i i := by
      apply Complex.ext <;> simp [hdiag_im]
    rw [cMatrixSignAverage_conj_diag X i]
    unfold cMatrixUnitaryDephase
    simp [Matrix.diagonal, hdiag]
  · rw [cMatrixSignAverage_conj_offDiag X hij]
    unfold cMatrixUnitaryDephase
    simp [Matrix.diagonal, hij]

theorem cMatrixUnitaryDephase_trace_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : CMatrix ι) :
    (cMatrixUnitaryDephase U X).trace.re = X.trace.re := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  let D : CMatrix ι := Matrix.diagonal fun i => (((X' i i).re : ℝ) : ℂ)
  have hdephase : cMatrixUnitaryDephase U X =
      (U : CMatrix ι) * D * star (U : CMatrix ι) := by
    simp [cMatrixUnitaryDephase, X', D]
  have htrace_conj :
      ((U : CMatrix ι) * D * star (U : CMatrix ι)).trace = D.trace := by
    calc
      ((U : CMatrix ι) * D * star (U : CMatrix ι)).trace =
          (star (U : CMatrix ι) * ((U : CMatrix ι) * D)).trace := by
            exact Matrix.trace_mul_comm ((U : CMatrix ι) * D) (star (U : CMatrix ι))
      _ = ((star (U : CMatrix ι) * (U : CMatrix ι)) * D).trace := by
            congr 1
            rw [Matrix.mul_assoc]
      _ = D.trace := by
            rw [Unitary.coe_star_mul_self U, Matrix.one_mul]
  have htrace_basis : X'.trace = X.trace := by
    calc
      X'.trace = (((star (U : CMatrix ι) * X) * (U : CMatrix ι)).trace) := by
          simp [X', Matrix.mul_assoc]
      _ = ((U : CMatrix ι) * (star (U : CMatrix ι) * X)).trace := by
          exact Matrix.trace_mul_comm (star (U : CMatrix ι) * X) (U : CMatrix ι)
      _ = (((U : CMatrix ι) * star (U : CMatrix ι)) * X).trace := by
          congr 1
          rw [Matrix.mul_assoc]
      _ = X.trace := by
          have hU : (U : CMatrix ι) * star (U : CMatrix ι) = 1 := by
            exact Unitary.coe_mul_star_self U
          rw [hU, Matrix.one_mul]
  have hD_trace_re : D.trace.re = X'.trace.re := by
    simp [D, X', Matrix.trace]
  rw [hdephase, htrace_conj]
  exact hD_trace_re.trans (congrArg Complex.re htrace_basis)

private theorem trace_mul_diagonal_ofReal_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CMatrix ι) (d : ι → ℝ) :
    ((M * (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix ι)).trace).re =
      ∑ i, (M i i).re * d i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Complex.mul_re]

private theorem trace_mul_unitary_diagonal_conj_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ) :
    ((E * ((U : CMatrix ι) *
        (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix ι) *
          star (U : CMatrix ι))).trace).re =
      (((star (U : CMatrix ι) * E * (U : CMatrix ι)) *
        (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix ι)).trace).re := by
  let D : CMatrix ι := Matrix.diagonal fun i => ((d i : ℝ) : ℂ)
  have htrace :
      (E * ((U : CMatrix ι) * D * star (U : CMatrix ι))).trace =
        (((star (U : CMatrix ι) * E * (U : CMatrix ι)) * D).trace) := by
    calc
      (E * ((U : CMatrix ι) * D * star (U : CMatrix ι))).trace =
          (((E * (U : CMatrix ι)) * D) * star (U : CMatrix ι)).trace := by
            congr 1
            noncomm_ring
      _ = (star (U : CMatrix ι) * ((E * (U : CMatrix ι)) * D)).trace := by
            exact Matrix.trace_mul_comm (((E * (U : CMatrix ι)) * D))
              (star (U : CMatrix ι))
      _ = (((star (U : CMatrix ι) * E * (U : CMatrix ι)) * D).trace) := by
            congr 1
            noncomm_ring
  simpa [D] using congrArg Complex.re htrace

private theorem scalar_effect_threshold_le_scaled_petz
    {e a b lambda alpha : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (ha : 0 ≤ a) (hb : 0 < b) (hlambda : 0 < lambda)
    (halpha : 1 ≤ alpha) :
    e * (a - lambda * b) ≤ lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
  have hrhs_nonneg :
      0 ≤ lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
    positivity
  by_cases hgap : a - lambda * b ≤ 0
  · have hleft_nonpos : e * (a - lambda * b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he0 hgap
    exact hleft_nonpos.trans hrhs_nonneg
  · have hgap_nonneg : 0 ≤ a - lambda * b := le_of_lt (lt_of_not_ge hgap)
    have hleft_le_gap : e * (a - lambda * b) ≤ 1 * (a - lambda * b) :=
      mul_le_mul_of_nonneg_right he1 hgap_nonneg
    have hratio_ge_one : 1 ≤ a / (lambda * b) := by
      rw [one_le_div (mul_pos hlambda hb)]
      linarith
    have ha_pos : 0 < a := by
      nlinarith [mul_pos hlambda hb]
    have hratio_le_rpow : a / (lambda * b) ≤ (a / (lambda * b)) ^ alpha :=
      Real.self_le_rpow_of_one_le hratio_ge_one halpha
    have hscalar :
        a - lambda * b ≤
          lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
      have hden_pos : 0 < lambda * b := mul_pos hlambda hb
      have hden_nonneg : 0 ≤ lambda * b := le_of_lt hden_pos
      have hmul :
          (lambda * b) * (a / (lambda * b)) ≤
            (lambda * b) * ((a / (lambda * b)) ^ alpha) :=
        mul_le_mul_of_nonneg_left hratio_le_rpow hden_nonneg
      have hleft_eq : (lambda * b) * (a / (lambda * b)) = a := by
        field_simp [ne_of_gt hden_pos]
      have hright_eq :
          (lambda * b) * ((a / (lambda * b)) ^ alpha) =
            lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
        calc
          (lambda * b) * ((a / (lambda * b)) ^ alpha)
              = (lambda * b) * (a ^ alpha / (lambda * b) ^ alpha) := by
                  rw [Real.div_rpow (le_of_lt ha_pos) hden_nonneg]
          _ = a ^ alpha * ((lambda * b) / (lambda * b) ^ alpha) := by ring
          _ = a ^ alpha * ((lambda * b) ^ (1 : ℝ) / (lambda * b) ^ alpha) := by
                rw [Real.rpow_one]
          _ = a ^ alpha * ((lambda * b) ^ (1 - alpha)) := by
                rw [Real.rpow_sub hden_pos 1 alpha]
          _ = a ^ alpha * (lambda ^ (1 - alpha) * b ^ (1 - alpha)) := by
                rw [Real.mul_rpow (le_of_lt hlambda) (le_of_lt hb)]
          _ = lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by ring
      rw [hleft_eq, hright_eq] at hmul
      linarith
    exact hleft_le_gap.trans (by simpa using hscalar)

private theorem posDef_unitary_conj_diag_re_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    0 < ((star (U : CMatrix ι) * A * (U : CMatrix ι)) i i).re := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  have hA' : A'.PosDef := by
    dsimp [A']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff (Unitary.isUnit_coe :
      IsUnit (U : CMatrix ι))]
    exact hA
  exact (Complex.pos_iff.mp (hA'.diag_pos (i := i))).1

private theorem posSemidef_unitary_conj_diag_re_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosSemidef) (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    0 ≤ ((star (U : CMatrix ι) * A * (U : CMatrix ι)) i i).re := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  simpa [A'] using posSemidef_diagonal_re_nonneg hA' i

theorem cMatrixUnitaryDephase_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CMatrix ι} (hX : X.PosSemidef) (U : Matrix.unitaryGroup ι ℂ) :
    (cMatrixUnitaryDephase U X).PosSemidef := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  let D : CMatrix ι := Matrix.diagonal fun i => (((X' i i).re : ℝ) : ℂ)
  have hX' : X'.PosSemidef := by
    simpa [X'] using posSemidef_unitary_conj hX U
  have hD : D.PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    change 0 ≤ (((X' i i).re : ℝ) : ℂ)
    exact_mod_cast posSemidef_diagonal_re_nonneg hX' i
  have hconj : ((U : CMatrix ι) * D * star (U : CMatrix ι)).PosSemidef := by
    rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hD
  simpa [cMatrixUnitaryDephase, X', D] using hconj

theorem cMatrixUnitaryDephase_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CMatrix ι} (hX : X.PosDef) (U : Matrix.unitaryGroup ι ℂ) :
    (cMatrixUnitaryDephase U X).PosDef := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  let D : CMatrix ι := Matrix.diagonal fun i => (((X' i i).re : ℝ) : ℂ)
  have hD : D.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < (((X' i i).re : ℝ) : ℂ)
    exact_mod_cast (by
      simpa [X'] using posDef_unitary_conj_diag_re_pos hX U i)
  have hconj : ((U : CMatrix ι) * D * star (U : CMatrix ι)).PosDef := by
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hD
  simpa [cMatrixUnitaryDephase, X', D] using hconj

theorem cMatrixUnitaryDephase_one_eq_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) :
    cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) X =
      (Matrix.diagonal fun i => (((X i i).re : ℝ) : ℂ) : CMatrix ι) := by
  unfold cMatrixUnitaryDephase
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hij]

theorem cMatrixUnitaryDephase_eq_unitary_conj_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : CMatrix ι) :
    cMatrixUnitaryDephase U X =
      (U : CMatrix ι) *
        cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ)
          (star (U : CMatrix ι) * X * (U : CMatrix ι)) *
        star (U : CMatrix ι) := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  rw [cMatrixUnitaryDephase_one_eq_diagonal X']
  simp [cMatrixUnitaryDephase, X', Matrix.mul_assoc]

theorem cMatrixPetzTrace_unitaryDephase_eq_coordinate_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha =
      cMatrixPetzTrace
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ)
          (star (U : CMatrix ι) * A * (U : CMatrix ι)))
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ)
          (star (U : CMatrix ι) * B * (U : CMatrix ι))) alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  have hdephA :
      cMatrixUnitaryDephase U A =
        (U : CMatrix ι) *
          cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' *
          star (U : CMatrix ι) := by
    simpa [A'] using cMatrixUnitaryDephase_eq_unitary_conj_coordinate U A
  have hdephB :
      cMatrixUnitaryDephase U B =
        (U : CMatrix ι) *
          cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' *
          star (U : CMatrix ι) := by
    simpa [B'] using cMatrixUnitaryDephase_eq_unitary_conj_coordinate U B
  have hA_coord :
      star (U : CMatrix ι) * cMatrixUnitaryDephase U A * (U : CMatrix ι) =
        cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' := by
    rw [hdephA]
    have hUU : star (U : CMatrix ι) * (U : CMatrix ι) = 1 :=
      Unitary.coe_star_mul_self U
    calc
      star (U : CMatrix ι) *
            ((U : CMatrix ι) *
              cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' *
              star (U : CMatrix ι)) *
            (U : CMatrix ι) =
          (star (U : CMatrix ι) * (U : CMatrix ι)) *
            cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' *
            (star (U : CMatrix ι) * (U : CMatrix ι)) := by
            noncomm_ring
      _ = cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' := by
            rw [hUU, Matrix.one_mul, Matrix.mul_one]
  have hB_coord :
      star (U : CMatrix ι) * cMatrixUnitaryDephase U B * (U : CMatrix ι) =
        cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' := by
    rw [hdephB]
    have hUU : star (U : CMatrix ι) * (U : CMatrix ι) = 1 :=
      Unitary.coe_star_mul_self U
    calc
      star (U : CMatrix ι) *
            ((U : CMatrix ι) *
              cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' *
              star (U : CMatrix ι)) *
            (U : CMatrix ι) =
          (star (U : CMatrix ι) * (U : CMatrix ι)) *
            cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' *
            (star (U : CMatrix ι) * (U : CMatrix ι)) := by
            noncomm_ring
      _ = cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' := by
            rw [hUU, Matrix.one_mul, Matrix.mul_one]
  have hconj :=
    (cMatrixPetzTrace_unitary_conj_eq_posSemidef_left
      (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B)
      (cMatrixUnitaryDephase_posSemidef hA U)
      (cMatrixUnitaryDephase_posDef hB U) U halpha_nonneg)
  rw [hA_coord, hB_coord] at hconj
  exact hconj.symm

/-- Finite uniform joint convexity for the Petz trace functional.

This is the smallest reusable Jensen shape needed by the sign-twirl proof
below: if the operator-convex perspective theorem for `x ↦ x^alpha` is
available, it should instantiate this statement for finite families with a
positive-semidefinite left input, positive-definite reference input, and
`1 < alpha ≤ 2`. -/
def cMatrixPetzTraceUniformJointConvex
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) (alpha : ℝ) : Prop :=
  (∀ k, (A k).PosSemidef) →
  (∀ k, (B k).PosDef) →
  1 < alpha → alpha ≤ 2 →
    cMatrixPetzTrace
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)
        alpha ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) * cMatrixPetzTrace (A k) (B k) alpha

/-- The linear-minus-resolvent integrand that appears in the operator-convex
perspective integral for `x ↦ x^α`, `1 < α ≤ 2`.

The coefficient is left explicit: in the Audenaert/Ando integral it will be a
positive scalar depending on the integration variable. -/
def cMatrixPetzPerspectiveResolventIntegrand
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (r coeff : ℝ) (A : CMatrix a) (B : CMatrix b) : CMatrix (a × b) :=
  Matrix.kronecker A (1 : CMatrix b) -
    coeff • Matrix.andoResolventIntegrand (a := a) (b := b) r A B

private theorem cMatrix_rpowIntegrand₁₂_eq_resolvent_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p r : ℝ} {A : CMatrix ι}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (hr : 0 < r) (hA : A.PosSemidef) :
    cfcₙ (Real.rpowIntegrand₁₂ p r) A =
      (r ^ (p - 1)) •
        (r⁻¹ • A + r • (A + r • (1 : CMatrix ι))⁻¹ -
          (1 : CMatrix ι)) := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hself : IsSelfAdjoint A := hA.isHermitian
  have hq_nonneg : quasispectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg A hA_nonneg x hx
  have hx_nonneg : ∀ x ∈ spectrum ℝ A, 0 ≤ x := by
    intro x hx
    exact hq_nonneg (spectrum_subset_quasispectrum ℝ A hx)
  have hden : ∀ x ∈ spectrum ℝ A, r + x ≠ 0 := by
    intro x hx hzero
    have hx0 := hx_nonneg x hx
    linarith
  have hfcont : ContinuousOn (Real.rpowIntegrand₁₂ p r) (quasispectrum ℝ A) := by
    exact (Real.continuousOn_rpowIntegrand₁₂_uncurry hp.1
      (quasispectrum ℝ A) hq_nonneg).uncurry_left r hr
  have halg : algebraMap ℝ (CMatrix ι) r = r • (1 : CMatrix ι) := by
    ext i j
    rw [Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  calc
    cfcₙ (Real.rpowIntegrand₁₂ p r) A =
        cfc (Real.rpowIntegrand₁₂ p r) A := by
      rw [cfcₙ_eq_cfc (a := A) (f := Real.rpowIntegrand₁₂ p r) (hf := hfcont)
        (hf0 := Real.rpowIntegrand₁₂_zero (p := p) hr)]
    _ = cfc (fun x : ℝ =>
          r ^ (p - 1) * (r⁻¹ * x + r * (r + x)⁻¹ - 1)) A := by
      rfl
    _ =
        r ^ (p - 1) •
          (r⁻¹ • A + r • Ring.inverse (algebraMap ℝ (CMatrix ι) r + A) -
            (1 : CMatrix ι)) := by
      rw [cfc_const_mul
        (r ^ (p - 1))
        (fun x : ℝ => r⁻¹ * x + r * (r + x)⁻¹ - 1) A
        (hf := by fun_prop (disch := grind -abstractProof))]
      rw [cfc_sub
        (f := fun x : ℝ => r⁻¹ * x + r * (r + x)⁻¹)
        (g := fun _ : ℝ => 1) (a := A)
        (hf := by fun_prop (disch := grind -abstractProof))
        (hg := by fun_prop)]
      rw [cfc_add
        (f := fun x : ℝ => r⁻¹ * x)
        (g := fun x : ℝ => r * (r + x)⁻¹) (a := A)
        (hf := by fun_prop)
        (hg := by fun_prop (disch := grind -abstractProof))]
      rw [cfc_const_mul_id (R := ℝ) r⁻¹ A (ha := hself)]
      rw [cfc_const_mul r (fun x : ℝ => (r + x)⁻¹) A
        (hf := by fun_prop (disch := grind -abstractProof))]
      rw [cfc_inv
        (fun x : ℝ => r + x) A hden
        (hf := by fun_prop)
        (ha := hself)]
      rw [cfc_const_add (R := ℝ) (r := r) (f := fun x : ℝ => x)
        (a := A) (ha := hself)]
      rw [cfc_id' (R := ℝ) (a := A) (ha := hself)]
      rw [cfc_const (R := ℝ) (A := CMatrix ι) 1 A (ha := hself)]
      simp
    _ =
        (r ^ (p - 1)) •
          (r⁻¹ • A + r • (A + r • (1 : CMatrix ι))⁻¹ -
            (1 : CMatrix ι)) := by
      rw [halg]
      congr 2
      congr 1
      congr 1
      rw [add_comm]
      rw [Matrix.nonsing_inv_eq_ringInverse]

private theorem cMatrixPetz_kronecker_inv_ref_mul_right
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hB : B.PosDef) :
    Matrix.kronecker A B⁻¹ * Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker A (1 : CMatrix b) := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  calc
    Matrix.kronecker A B⁻¹ * Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker (A * (1 : CMatrix a)) (B⁻¹ * B) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul A (1 : CMatrix a) B⁻¹ B).symm
    _ = Matrix.kronecker A (1 : CMatrix b) := by
        rw [Matrix.nonsing_inv_mul B hdet]
        simp

private theorem cMatrixPetz_andoDenom_mul_ref_inv_eq_shift
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hB : B.PosDef) {r : ℝ} :
    (Matrix.kronecker A (1 : CMatrix b) +
        r • Matrix.kronecker (1 : CMatrix a) B) *
      Matrix.kronecker (1 : CMatrix a) B⁻¹ =
    Matrix.kronecker A B⁻¹ + r • (1 : CMatrix (a × b)) := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  calc
    (Matrix.kronecker A (1 : CMatrix b) +
        r • Matrix.kronecker (1 : CMatrix a) B) *
      Matrix.kronecker (1 : CMatrix a) B⁻¹ =
      Matrix.kronecker A (1 : CMatrix b) *
          Matrix.kronecker (1 : CMatrix a) B⁻¹ +
        (r • Matrix.kronecker (1 : CMatrix a) B) *
          Matrix.kronecker (1 : CMatrix a) B⁻¹ := by
        rw [add_mul]
    _ = Matrix.kronecker A B⁻¹ + r • (1 : CMatrix (a × b)) := by
        have h₁ :
            Matrix.kronecker A (1 : CMatrix b) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              Matrix.kronecker A B⁻¹ := by
          calc
            Matrix.kronecker A (1 : CMatrix b) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              Matrix.kronecker (A * (1 : CMatrix a))
                ((1 : CMatrix b) * B⁻¹) := by
                simpa [Matrix.kronecker] using
                  (Matrix.mul_kronecker_mul
                    A (1 : CMatrix a) (1 : CMatrix b) B⁻¹).symm
            _ = Matrix.kronecker A B⁻¹ := by
                simp
        have h₂ :
            (r • Matrix.kronecker (1 : CMatrix a) B) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              r • (1 : CMatrix (a × b)) := by
          calc
            (r • Matrix.kronecker (1 : CMatrix a) B) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              r •
                (Matrix.kronecker (1 : CMatrix a) B *
                  Matrix.kronecker (1 : CMatrix a) B⁻¹) := by
                simp
            _ = r • (1 : CMatrix (a × b)) := by
                have hmul :
                    Matrix.kronecker (1 : CMatrix a) B *
                        Matrix.kronecker (1 : CMatrix a) B⁻¹ =
                      1 := by
                  calc
                    Matrix.kronecker (1 : CMatrix a) B *
                        Matrix.kronecker (1 : CMatrix a) B⁻¹ =
                      Matrix.kronecker
                        ((1 : CMatrix a) * (1 : CMatrix a)) (B * B⁻¹) := by
                        simpa [Matrix.kronecker] using
                          (Matrix.mul_kronecker_mul
                            (1 : CMatrix a) (1 : CMatrix a) B B⁻¹).symm
                    _ = 1 := by
                        rw [Matrix.mul_nonsing_inv B hdet]
                        simp
                rw [hmul]
        rw [h₁, h₂]

private theorem cMatrixPetz_shiftedKroneckerInv_inv_eq_ref_mul_andoDenom_inv
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {r : ℝ} {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosDef) (hr : 0 < r) :
    (Matrix.kronecker A B⁻¹ + r • (1 : CMatrix (a × b)))⁻¹ =
      Matrix.kronecker (1 : CMatrix a) B *
        (Matrix.kronecker A (1 : CMatrix b) +
          r • Matrix.kronecker (1 : CMatrix a) B)⁻¹ := by
  let X : CMatrix (a × b) := Matrix.kronecker A (1 : CMatrix b)
  let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
  let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
  let D : CMatrix (a × b) := X + r • Y
  have hYpd : Y.PosDef := by
    simpa [Y] using Matrix.PosDef.one.kronecker hB
  have hYdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hYpd.isUnit
  have hDpd : D.PosDef := by
    simpa [X, Y, D] using Matrix.andoDenom_posDef (a := a) (b := b) hA hB hr
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDpd.isUnit
  have hYinv : Y⁻¹ = Matrix.kronecker (1 : CMatrix a) B⁻¹ := by
    simpa [Y] using (Matrix.inv_kronecker (1 : CMatrix a) B)
  have hDYinv : D * Y⁻¹ = C + r • (1 : CMatrix (a × b)) := by
    rw [hYinv]
    simpa [X, Y, C, D] using
      cMatrixPetz_andoDenom_mul_ref_inv_eq_shift
        (a := a) (b := b) (A := A) (B := B) (r := r) hB
  apply Matrix.inv_eq_right_inv
  calc
    (C + r • (1 : CMatrix (a × b))) * (Y * D⁻¹) =
        (D * Y⁻¹) * (Y * D⁻¹) := by
      rw [hDYinv]
    _ = D * (Y⁻¹ * (Y * D⁻¹)) := by
      exact Matrix.mul_assoc D Y⁻¹ (Y * D⁻¹)
    _ = D * ((Y⁻¹ * Y) * D⁻¹) := by
      exact congrArg (fun Z : CMatrix (a × b) => D * Z)
        (Matrix.mul_assoc Y⁻¹ Y D⁻¹).symm
    _ = D * (1 * D⁻¹) := by
      rw [Matrix.nonsing_inv_mul Y hYdet]
    _ = 1 := by
      rw [Matrix.one_mul, Matrix.mul_nonsing_inv D hDdet]

theorem cMatrix_rpowIntegrand₁₂_kronecker_inv_mul_right_eq_petzPerspective
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {p r : ℝ} {A : CMatrix a} {B : CMatrix b}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (hr : 0 < r)
    (hA : A.PosSemidef) (hB : B.PosDef) :
    cfcₙ (Real.rpowIntegrand₁₂ p r) (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B := by
  let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
  let X : CMatrix (a × b) := Matrix.kronecker A (1 : CMatrix b)
  let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
  let D : CMatrix (a × b) := X + r • Y
  have hCpsd : C.PosSemidef := by
    simpa [C] using hA.kronecker hB.inv.posSemidef
  have hCmulY : C * Y = X := by
    simpa [C, Y, X] using
      cMatrixPetz_kronecker_inv_ref_mul_right
        (a := a) (b := b) (A := A) (B := B) hB
  have hinv : (C + r • (1 : CMatrix (a × b)))⁻¹ = Y * D⁻¹ := by
    simpa [C, X, Y, D] using
      cMatrixPetz_shiftedKroneckerInv_inv_eq_ref_mul_andoDenom_inv
        (a := a) (b := b) (A := A) (B := B) (r := r) hA hB hr
  have hDright : D * D⁻¹ = 1 := by
    have hDpd : D.PosDef := by
      simpa [X, Y, D] using Matrix.andoDenom_posDef (a := a) (b := b) hA hB hr
    have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDpd.isUnit
    exact Matrix.mul_nonsing_inv D hDdet
  have hresolvent_complement : Y - r • (Y * D⁻¹ * Y) = X * D⁻¹ * Y := by
    calc
      Y - r • (Y * D⁻¹ * Y) =
          (X + r • Y) * D⁻¹ * Y - r • (Y * D⁻¹ * Y) := by
        change Y - r • (Y * D⁻¹ * Y) = D * D⁻¹ * Y - r • (Y * D⁻¹ * Y)
        rw [hDright]
        simp [Matrix.mul_assoc]
      _ = X * D⁻¹ * Y := by
        simp [Matrix.add_mul, Matrix.mul_assoc, sub_eq_add_neg]
  have hpow : r ^ (p - 1) * r⁻¹ = r ^ (p - 2) := by
    calc
      r ^ (p - 1) * r⁻¹ = r ^ (p - 1) * r ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
      _ = r ^ ((p - 1) + (-1 : ℝ)) := by
        rw [← Real.rpow_add hr (p - 1) (-1 : ℝ)]
      _ = r ^ (p - 2) := by
        ring_nf
  have hpow_mul : r * r ^ (p - 2) = r ^ (p - 1) := by
    calc
      r * r ^ (p - 2) = r ^ (1 : ℝ) * r ^ (p - 2) := by
        rw [Real.rpow_one]
      _ = r ^ ((1 : ℝ) + (p - 2)) := by
        rw [← Real.rpow_add hr (1 : ℝ) (p - 2)]
      _ = r ^ (p - 1) := by
        ring_nf
  have hpowEntry :
      ((r ^ (p - 1) : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ) =
        ((r ^ (p - 2) : ℝ) : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hpow
  have hpowMulEntry :
      (r : ℂ) * ((r ^ (p - 2) : ℝ) : ℂ) =
        ((r ^ (p - 1) : ℝ) : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hpow_mul
  calc
    cfcₙ (Real.rpowIntegrand₁₂ p r) (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      ((r ^ (p - 1)) •
        (r⁻¹ • C + r • (C + r • (1 : CMatrix (a × b)))⁻¹ -
          (1 : CMatrix (a × b)))) * Y := by
        rw [cMatrix_rpowIntegrand₁₂_eq_resolvent_affine
          (p := p) (r := r) (A := C) hp hr hCpsd]
    _ =
      (r ^ (p - 1)) •
        ((r⁻¹ • C) * Y + (r • (C + r • (1 : CMatrix (a × b)))⁻¹) * Y -
          Y) := by
        simp [sub_eq_add_neg, add_mul]
    _ =
      (r ^ (p - 1)) •
        (r⁻¹ • X + r • (Y * D⁻¹ * Y) - Y) := by
        simp [hinv, hCmulY, Matrix.mul_assoc]
    _ =
      (r ^ (p - 1)) •
        (r⁻¹ • X - (Y - r • (Y * D⁻¹ * Y))) := by
        abel_nf
    _ =
      (r ^ (p - 1)) •
        (r⁻¹ • X - X * D⁻¹ * Y) := by
        rw [hresolvent_complement]
    _ =
      (r ^ (p - 2)) •
        (X - r • (X * D⁻¹ * Y)) := by
        ext i j
        simp only [Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
        let W : ℂ := (X * D⁻¹ * Y) i j
        change ((r ^ (p - 1) : ℝ) : ℂ) * (((r⁻¹ : ℝ) : ℂ) * X i j - W) =
          ((r ^ (p - 2) : ℝ) : ℂ) * (X i j - (r : ℂ) * W)
        calc
          ((r ^ (p - 1) : ℝ) : ℂ) * (((r⁻¹ : ℝ) : ℂ) * X i j - W) =
              (((r ^ (p - 1) : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ)) * X i j -
                ((r ^ (p - 1) : ℝ) : ℂ) * W := by ring
          _ =
              ((r ^ (p - 2) : ℝ) : ℂ) * X i j -
                ((r : ℂ) * ((r ^ (p - 2) : ℝ) : ℂ)) * W := by
            rw [hpowEntry, hpowMulEntry]
          _ =
              ((r ^ (p - 2) : ℝ) : ℂ) * (X i j - (r : ℂ) * W) := by
            ring
    _ =
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B := by
        simp [cMatrixPetzPerspectiveResolventIntegrand,
          Matrix.andoResolventIntegrand, X, Y, D]

private theorem cMatrixPetz_integrableOn_mul_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix ι}
    (hf : MeasureTheory.IntegrableOn f s μ) (R : CMatrix ι) :
    MeasureTheory.IntegrableOn (fun r => f r * R) s μ := by
  have hf' : MeasureTheory.Integrable f (μ.restrict s) := by
    simpa [MeasureTheory.IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix ι) (1 : CMatrix ι) R).integrable_comp hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply, MeasureTheory.IntegrableOn] using h

private theorem cMatrixPetz_setIntegral_mul_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix ι}
    (hf : MeasureTheory.IntegrableOn f s μ) (R : CMatrix ι) :
    (∫ r in s, f r ∂μ) * R = ∫ r in s, f r * R ∂μ := by
  have hf' : MeasureTheory.Integrable f (μ.restrict s) := by
    simpa [MeasureTheory.IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix ι) (1 : CMatrix ι) R).integral_comp_comm hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply] using h.symm

private noncomputable def cMatrixPetzConjTransposeCLM
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    CMatrix ι →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => Matrix.conjTranspose M
       map_add' := by intro M N; simp
       map_smul' := by intro c M; ext i j; simp } : CMatrix ι →ₗ[ℝ] CMatrix ι)

private theorem cMatrixPetz_integral_conjTranspose
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : MeasureTheory.Integrable f μ) :
    Matrix.conjTranspose (∫ x, f x ∂μ) =
      ∫ x, Matrix.conjTranspose (f x) ∂μ := by
  simpa [cMatrixPetzConjTransposeCLM] using
    ((cMatrixPetzConjTransposeCLM (ι := ι)).integral_comp_comm hf).symm

private noncomputable def cMatrixPetzEntryCLMComplex
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) : CMatrix ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => M i j
       map_add' := by intro M N; simp
       map_smul' := by intro c M; simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℂ] ℂ)

private noncomputable def cMatrixPetzQuadraticCLM
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℂ) : CMatrix ι →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (x i) * x j) •
    cMatrixPetzEntryCLMComplex (ι := ι) i j

private theorem cMatrixPetzQuadraticCLM_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (A : CMatrix ι) :
    cMatrixPetzQuadraticCLM x A = dotProduct (star x) (Matrix.mulVec A x) := by
  simp [cMatrixPetzQuadraticCLM, cMatrixPetzEntryCLMComplex, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

private theorem cMatrixPetz_integral_dotProduct_mulVec
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : MeasureTheory.Integrable f μ) (x : ι → ℂ) :
    dotProduct (star x) (Matrix.mulVec (∫ t, f t ∂μ) x) =
      ∫ t, dotProduct (star x) (Matrix.mulVec (f t) x) ∂μ := by
  simp_rw [← cMatrixPetzQuadraticCLM_apply x]
  exact
    ((cMatrixPetzQuadraticCLM x).integral_comp_comm hf).symm

private theorem cMatrixPetz_integral_posSemidef_of_ae
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : MeasureTheory.Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, cMatrixPetz_integral_conjTranspose (hf := hf)]
    apply MeasureTheory.integral_congr_ae
    exact hpos.mono fun _ ht => ht.isHermitian.eq
  · intro x
    rw [cMatrixPetz_integral_dotProduct_mulVec (hf := hf) x]
    exact MeasureTheory.integral_nonneg_of_ae
      (hpos.mono fun _ ht => ht.dotProduct_mulVec_nonneg x)

private theorem cMatrixPetz_setIntegral_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → CMatrix ι}
    (hf : MeasureTheory.IntegrableOn f s μ) (hg : MeasureTheory.IntegrableOn g s μ)
    (hle : ∀ r ∈ s, f r ≤ g r) :
    ∫ r in s, f r ∂μ ≤ ∫ r in s, g r ∂μ := by
  have hdiffInt : MeasureTheory.IntegrableOn (fun r : ℝ => g r - f r) s μ := hg.sub hf
  have hdiffPSD :
      (∫ r in s, (g r - f r) ∂μ).PosSemidef := by
    have hdiffInt' :
        MeasureTheory.Integrable (fun r : ℝ => g r - f r) (μ.restrict s) := by
      simpa [MeasureTheory.IntegrableOn] using hdiffInt
    exact
      cMatrixPetz_integral_posSemidef_of_ae (μ := μ.restrict s) hdiffInt'
        ((MeasureTheory.ae_restrict_iff' hs).mpr
          (MeasureTheory.ae_of_all μ fun r hr => Matrix.le_iff.mp (hle r hr)))
  have hsub :
      ∫ r in s, (g r - f r) ∂μ =
        (∫ r in s, g r ∂μ) - (∫ r in s, f r ∂μ) := by
    simpa [MeasureTheory.IntegrableOn] using
      MeasureTheory.integral_sub (μ := μ.restrict s)
        (by simpa [MeasureTheory.IntegrableOn] using hg)
        (by simpa [MeasureTheory.IntegrableOn] using hf)
  rw [hsub] at hdiffPSD
  exact Matrix.le_iff.mpr hdiffPSD

private theorem cMatrixPetz_setIntegral_finset_sum_smul
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} {f : κ → ℝ → CMatrix ι}
    (c : ℝ) (hf : ∀ k, MeasureTheory.IntegrableOn (f k) s μ) :
    ∫ r in s, (∑ k, c • f k r) ∂μ =
      ∑ k, c • ∫ r in s, f k r ∂μ := by
  have hf' :
      ∀ k, MeasureTheory.Integrable (f k) (μ.restrict s) := by
    intro k
    simpa [MeasureTheory.IntegrableOn] using hf k
  calc
    ∫ r in s, (∑ k, c • f k r) ∂μ =
        ∫ r, (∑ k, c • f k r) ∂(μ.restrict s) := rfl
    _ = ∑ k, ∫ r, c • f k r ∂(μ.restrict s) := by
        rw [MeasureTheory.integral_finsetSum]
        intro k _
        exact (hf' k).smul c
    _ = ∑ k, c • ∫ r, f k r ∂(μ.restrict s) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [MeasureTheory.integral_smul]
    _ = ∑ k, c • ∫ r in s, f k r ∂μ := rfl

private theorem cMatrixPetz_rpow_nonsing_inv_eq_rpow_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosDef) (p : ℝ) :
    CFC.rpow B⁻¹ p = CFC.rpow B (-p) := by
  obtain ⟨u, hu⟩ := hB.isUnit
  have hBnonneg : (0 : CMatrix ι) ≤ B :=
    Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef
  have hinv : B⁻¹ = (↑u⁻¹ : CMatrix ι) := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu]
    simp
  calc
    CFC.rpow B⁻¹ p = CFC.rpow (↑u⁻¹ : CMatrix ι) p := by
      rw [hinv]
    _ = CFC.rpow (↑u : CMatrix ι) (-p) := by
      exact (CFC.rpow_neg u p (ha' := by simpa [hu] using hBnonneg)).symm
    _ = CFC.rpow B (-p) := by
      rw [hu]

private theorem cMatrixPetz_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosDef)
    {p : ℝ} (hp0 : 0 ≤ p) :
    CFC.rpow (Matrix.kronecker A B⁻¹) p *
        Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) := by
  have hBinv_psd : B⁻¹.PosSemidef := hB.inv.posSemidef
  have hpowK :
      CFC.rpow (Matrix.kronecker A B⁻¹) p =
        Matrix.kronecker (CFC.rpow A p) (CFC.rpow B⁻¹ p) := by
    simpa using
      cMatrix_rpow_kronecker_nonneg
        (A := A) (B := B⁻¹) hA hBinv_psd hp0
  have hBpow : CFC.rpow B⁻¹ p * B = CFC.rpow B (1 - p) := by
    rw [cMatrixPetz_rpow_nonsing_inv_eq_rpow_neg hB p]
    have hBpowone : CFC.rpow B (1 : ℝ) = B :=
      CFC.rpow_one B (ha := Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef)
    calc
      CFC.rpow B (-p) * B =
          CFC.rpow B (-p) * CFC.rpow B (1 : ℝ) := by
        rw [hBpowone]
      _ = CFC.rpow B (-p + 1) := by
        exact (CFC.rpow_add (a := B) (x := -p) (y := 1) hB.isUnit).symm
      _ = CFC.rpow B (1 - p) := by
        ring_nf
  calc
    CFC.rpow (Matrix.kronecker A B⁻¹) p *
        Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker (CFC.rpow A p) (CFC.rpow B⁻¹ p) *
        Matrix.kronecker (1 : CMatrix a) B := by
        rw [hpowK]
    _ =
      Matrix.kronecker (CFC.rpow A p * (1 : CMatrix a))
        (CFC.rpow B⁻¹ p * B) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul
            (CFC.rpow A p) (1 : CMatrix a) (CFC.rpow B⁻¹ p) B).symm
    _ = Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) := by
        rw [hBpow]
        simp

/-- High-alpha integral representation for the Petz perspective resolvent
integrand. -/
theorem cMatrixPetzPerspectiveIntegralRepresentation_Ioo_one_two
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    ∃ μ : MeasureTheory.Measure ℝ,
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        MeasureTheory.IntegrableOn (fun r : ℝ => (r ^ (p - 2)) •
          cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B)
          (Set.Ioi 0) μ) ∧
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) =
          ∫ r in Set.Ioi 0, (r ^ (p - 2)) •
            cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B ∂μ) := by
  let pNN : ℝ≥0 := ⟨p, le_trans zero_le_one hp.1.le⟩
  have hpNN : pNN ∈ Set.Ioo (1 : ℝ≥0) 2 := by
    constructor
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂
      (CMatrix (a × b)) hpNN
  refine ⟨μ, ?_, ?_⟩
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hCnonneg : C ∈ Set.Ici (0 : CMatrix (a × b)) :=
      Matrix.nonneg_iff_posSemidef.mpr hCpsd
    have hCInt :
        MeasureTheory.IntegrableOn
          (fun r : ℝ => cfcₙ (Real.rpowIntegrand₁₂ p r) C)
          (Set.Ioi 0) μ := by
      simpa [pNN] using (hμ C hCnonneg).1
    have hRightInt :
        MeasureTheory.IntegrableOn
          (fun r : ℝ => cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y)
          (Set.Ioi 0) μ :=
      cMatrixPetz_integrableOn_mul_right hCInt Y
    let F : ℝ → CMatrix (a × b) := fun r =>
      cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        cMatrix_rpowIntegrand₁₂_kronecker_inv_mul_right_eq_petzPerspective
          (a := a) (b := b) (p := p) (r := r) (A := A) (B := B)
          hp hr hA hB
    have hGInt : MeasureTheory.IntegrableOn G (Set.Ioi 0) μ :=
      hRightInt.congr_fun hEqOn measurableSet_Ioi
    simpa [G] using hGInt
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hp0 : 0 ≤ p := le_trans zero_le_one hp.1.le
    have hpNN_pos : 0 < pNN := by
      exact lt_trans zero_lt_one hpNN.1
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hCnonneg : C ∈ Set.Ici (0 : CMatrix (a × b)) :=
      Matrix.nonneg_iff_posSemidef.mpr hCpsd
    have hCInt :
        MeasureTheory.IntegrableOn
          (fun r : ℝ => cfcₙ (Real.rpowIntegrand₁₂ p r) C)
          (Set.Ioi 0) μ := by
      simpa [pNN] using (hμ C hCnonneg).1
    let F : ℝ → CMatrix (a × b) := fun r =>
      cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        cMatrix_rpowIntegrand₁₂_kronecker_inv_mul_right_eq_petzPerspective
          (a := a) (b := b) (p := p) (r := r) (A := A) (B := B)
          hp hr hA hB
    have hCpow :
        CFC.rpow C p =
          ∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C ∂μ := by
      calc
        CFC.rpow C p = C ^ pNN := by
          exact (by
            simpa [pNN] using
              (CFC.nnrpow_eq_rpow (a := C) hpNN_pos).symm)
        _ = ∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C ∂μ := by
          simpa [pNN] using (hμ C hCnonneg).2
    have hLeft : CFC.rpow C p * Y = ∫ r in Set.Ioi 0, F r ∂μ := by
      calc
        CFC.rpow C p * Y =
            (∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C ∂μ) * Y := by
          rw [hCpow]
        _ = ∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y ∂μ := by
          rw [cMatrixPetz_setIntegral_mul_right hCInt Y]
        _ = ∫ r in Set.Ioi 0, F r ∂μ := by
          rfl
    have hFGint : ∫ r in Set.Ioi 0, F r ∂μ = ∫ r in Set.Ioi 0, G r ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hEqOn
    have hTensor :
        CFC.rpow C p * Y =
          Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) := by
      simpa [C, Y] using
        cMatrixPetz_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
          (a := a) (b := b) (A := A) (B := B) hA hB hp0
    calc
      Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) =
          CFC.rpow C p * Y := by
        exact hTensor.symm
      _ = ∫ r in Set.Ioi 0, F r ∂μ := hLeft
      _ = ∫ r in Set.Ioi 0, G r ∂μ := hFGint
      _ = ∫ r in Set.Ioi 0, (r ^ (p - 2)) •
          cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B ∂μ := by
        rfl

theorem cMatrixPetzPerspectiveResolventIntegrand_convex_posDef
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {r coeff t : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
        (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) ≤
      t • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff A₁ B₁ +
        (1 - t) • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
          r coeff A₂ B₂ := by
  let I₁ := Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let I₂ := Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ibar := Matrix.andoResolventIntegrand (a := a) (b := b) r
    (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂)
  let Xbar : CMatrix (a × b) :=
    Matrix.kronecker (t • A₁ + (1 - t) • A₂) (1 : CMatrix b)
  have hconc : t • I₁ + (1 - t) • I₂ ≤ Ibar := by
    simpa [I₁, I₂, Ibar] using
      Matrix.andoResolventIntegrand_concave_posDef
        (a := a) (b := b) hA₁ hA₂ hB₁ hB₂ hr ht0 ht1
  have hscaled : coeff • (t • I₁ + (1 - t) • I₂) ≤ coeff • Ibar :=
    smul_le_smul_of_nonneg_left hconc hcoeff
  have hsub : Xbar - coeff • Ibar ≤ Xbar - coeff • (t • I₁ + (1 - t) • I₂) :=
    sub_le_sub_left hscaled Xbar
  calc
    cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
        (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) =
      Xbar - coeff • Ibar := by rfl
    _ ≤ Xbar - coeff • (t • I₁ + (1 - t) • I₂) := hsub
    _ = t • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff A₁ B₁ +
        (1 - t) • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
          r coeff A₂ B₂ := by
      ext i j
      simp [cMatrixPetzPerspectiveResolventIntegrand, Xbar, I₁, I₂,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
        Matrix.sub_apply, add_mul]
      ring

theorem cMatrixPetzPerspectiveResolventIntegrand_convexOn_posDef
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {r coeff : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff) :
    ConvexOn ℝ ({P : CMatrix a × CMatrix b | P.1.PosSemidef ∧ P.2.PosDef})
      (fun P : CMatrix a × CMatrix b =>
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff P.1 P.2) := by
  refine ⟨?hconv, ?hineq⟩
  · intro x hx y hy s t hs ht hst
    have ht_eq : t = 1 - s := by linarith
    have hs_le_one : s ≤ 1 := by linarith
    constructor
    · simpa [Prod.smul_mk, ht_eq] using
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul hx.1 hs)
          (Matrix.PosSemidef.smul hy.1 (sub_nonneg.mpr hs_le_one))
    · simpa [Prod.smul_mk, ht_eq] using
        Matrix.PosDef.convexCombination hx.2 hy.2 hs hs_le_one
  · intro x hx y hy s t hs ht hst
    have ht_eq : t = 1 - s := by linarith
    have hs_le_one : s ≤ 1 := by linarith
    obtain ⟨A₁, B₁⟩ := x
    obtain ⟨A₂, B₂⟩ := y
    simpa [Prod.smul_mk, ht_eq] using
      cMatrixPetzPerspectiveResolventIntegrand_convex_posDef
        (a := a) (b := b) hx.1 hy.1 hx.2 hy.2 hr hcoeff hs hs_le_one

private theorem cMatrixPetz_fst_weighted_pair_sum
    {κ a b : Type*} [Fintype κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b) (w : ℝ) :
    (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i).1 =
      ∑ k, w • A k := by
  let fstLin : (CMatrix a × CMatrix b) →ₗ[ℝ] CMatrix a :=
    { toFun := Prod.fst
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  show fstLin (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i) =
    ∑ k, w • A k
  rw [map_sum]
  simp [fstLin]

private theorem cMatrixPetz_snd_weighted_pair_sum
    {κ a b : Type*} [Fintype κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b) (w : ℝ) :
    (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i).2 =
      ∑ k, w • B k := by
  let sndLin : (CMatrix a × CMatrix b) →ₗ[ℝ] CMatrix b :=
    { toFun := Prod.snd
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  show sndLin (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i) =
    ∑ k, w • B k
  rw [map_sum]
  simp [sndLin]

/-- Finite uniform Jensen for the resolvent integrand in the Petz perspective
route.

This is the finite-matrix Effros/Ando step before integrating the
Audenaert-resolvent representation of `x ↦ x^α`, `1 < α ≤ 2`. -/
theorem cMatrixPetzPerspectiveResolvent_uniform_average_le
    {κ a b : Type*} [Fintype κ] [Nonempty κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b)
    {r coeff : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff)
    (hA : ∀ k, (A k).PosSemidef) (hB : ∀ k, (B k).PosDef) :
    cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
        (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k)
        (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k) ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
          r coeff (A k) (B k) := by
  classical
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hweight_nonneg :
      ∀ k ∈ (Finset.univ : Finset κ), 0 ≤ w := by
    intro _ _
    exact inv_nonneg.mpr hcard_pos.le
  have hweight_sum :
      ∑ k ∈ (Finset.univ : Finset κ), w = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change (Fintype.card κ : ℝ) * w = 1
    dsimp [w]
    field_simp [ne_of_gt hcard_pos]
  have hmem :
      ∀ k ∈ (Finset.univ : Finset κ),
        (A k, B k) ∈
          ({P : CMatrix a × CMatrix b | P.1.PosSemidef ∧ P.2.PosDef}) := by
    intro k _
    exact ⟨hA k, hB k⟩
  have hjensen :=
    (cMatrixPetzPerspectiveResolventIntegrand_convexOn_posDef
      (a := a) (b := b) (r := r) (coeff := coeff) hr hcoeff).map_sum_le
      (t := (Finset.univ : Finset κ))
      (w := fun _ : κ => w)
      (p := fun k : κ => (A k, B k))
      hweight_nonneg hweight_sum hmem
  rw [cMatrixPetz_fst_weighted_pair_sum (A := A) (B := B) (w := w),
    cMatrixPetz_snd_weighted_pair_sum (A := A) (B := B) (w := w)] at hjensen
  simpa [w] using hjensen

/-- Loewner monotonicity after evaluating a complex matrix on a fixed
Hilbert-space vector. -/
theorem cMatrix_quadraticForm_re_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : CMatrix ι} (hMN : M ≤ N) (x : ι → ℂ) :
    (dotProduct (star x) (Matrix.mulVec M x)).re ≤
      (dotProduct (star x) (Matrix.mulVec N x)).re := by
  have hdiff : (N - M).PosSemidef := Matrix.le_iff.mp hMN
  have hnonneg : 0 ≤ dotProduct (star x) (Matrix.mulVec (N - M) x) :=
    hdiff.dotProduct_mulVec_nonneg x
  have hnonneg_re :
      0 ≤ (dotProduct (star x) (Matrix.mulVec (N - M) x)).re := by
    exact (Complex.le_def.mp hnonneg).1
  have hdiff_eval :
      dotProduct (star x) (Matrix.mulVec (N - M) x) =
        dotProduct (star x) (Matrix.mulVec N x) -
          dotProduct (star x) (Matrix.mulVec M x) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  rw [hdiff_eval, Complex.sub_re] at hnonneg_re
  linarith

/-- Quadratic forms are real-linear in a finite weighted sum of matrices. -/
theorem cMatrix_quadraticForm_re_sum_smul
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (K : κ → CMatrix ι) (w : ℝ) (x : ι → ℂ) :
    (dotProduct (star x) (Matrix.mulVec (∑ k, w • K k) x)).re =
      ∑ k, w * (dotProduct (star x) (Matrix.mulVec (K k) x)).re := by
  rw [Matrix.sum_mulVec]
  simp [dotProduct_sum, Matrix.smul_mulVec, Complex.real_smul]

/-- Hilbert-Schmidt quadratic-form version of the finite uniform Jensen step
for the Petz perspective resolvent integrand.

This is the concrete bridge from the existing matrix-valued resolvent layer to
the Petz kernel layer: any fixed Hilbert-Schmidt vector, in particular
`Matrix.vec 1`, can be evaluated against the Loewner-order Jensen inequality.
The remaining high-exponent Petz step is the explicit integral/functional
calculus identity identifying the rpow Petz kernel with the integral of these
resolvent kernels. -/
theorem cMatrixPetzPerspectiveResolvent_uniform_average_quadratic_le
    {κ a b : Type*} [Fintype κ] [Nonempty κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b)
    {r coeff : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff)
    (hA : ∀ k, (A k).PosSemidef) (hB : ∀ k, (B k).PosDef)
    (x : a × b → ℂ) :
    (dotProduct (star x)
      (Matrix.mulVec
        (cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k)
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k)) x)).re ≤
      (dotProduct (star x)
        (Matrix.mulVec
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) •
            cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
              r coeff (A k) (B k)) x)).re := by
  exact cMatrix_quadraticForm_re_mono
    (cMatrixPetzPerspectiveResolvent_uniform_average_le
      (a := a) (b := b) A B hr hcoeff hA hB) x

/-- Finite uniform Jensen packaging for the matrix power map.

The hypothesis is the matrix-specialized operator-convexity input supplied by
`CFC.convexOn_rpow_one_two` for `1 ≤ α ≤ 2`.  This lemma turns that input into
the finite-uniform averaging shape used by the Petz sign-orbit bridge.  The
remaining Petz blocker is the noncommutative perspective/relative-modular step
that turns this single-variable Jensen input into joint convexity of
`Tr(A^α B^(1-α))`. -/
theorem cMatrix_rpow_uniform_average_le_uniform_average_rpow_of_convexOn
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A : κ → CMatrix ι) {alpha : ℝ}
    (hconv :
      ConvexOn ℝ (Set.Ici (0 : CMatrix ι)) (fun X : CMatrix ι => X ^ alpha))
    (hA : ∀ k, 0 ≤ A k) :
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k) ^ alpha ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) • (A k) ^ alpha := by
  classical
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hweight_nonneg :
      ∀ k ∈ (Finset.univ : Finset κ), 0 ≤ ((Fintype.card κ : ℝ)⁻¹) := by
    intro _ _
    exact inv_nonneg.mpr hcard_pos.le
  have hweight_sum :
      ∑ k ∈ (Finset.univ : Finset κ), ((Fintype.card κ : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)⁻¹ = 1
    field_simp [ne_of_gt hcard_pos]
  have hmem :
      ∀ k ∈ (Finset.univ : Finset κ), A k ∈ Set.Ici (0 : CMatrix ι) := by
    intro k _
    exact hA k
  simpa using
    hconv.map_sum_le
      (t := (Finset.univ : Finset κ))
      (w := fun _ : κ => ((Fintype.card κ : ℝ)⁻¹))
      (p := A) hweight_nonneg hweight_sum hmem

/-- The finite Jensen/joint-convexity instance needed by the sign-unitary
averaging proof of coordinate pinching monotonicity for the Petz trace. -/
def cMatrixPetzTraceSignUnitaryJensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) : Prop :=
  cMatrixPetzTrace
      (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
      (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
      alpha ≤
    ∑ s : ι → Bool,
      ((Fintype.card (ι → Bool) : ℝ)⁻¹) *
        cMatrixPetzTrace
          (star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
          (star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
          alpha

/-- The sign-unitary Jensen component follows from finite uniform joint
convexity of the Petz trace, specialized to the sign orbit. -/
theorem cMatrixPetzTraceSignUnitaryJensen_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    cMatrixPetzTraceSignUnitaryJensen A B alpha := by
  classical
  have hAorbit :
      ∀ s : ι → Bool,
        (star (cMatrixSignUnitary s : CMatrix ι) * A *
          (cMatrixSignUnitary s : CMatrix ι)).PosSemidef := by
    intro s
    simpa using posSemidef_unitary_conj hA (cMatrixSignUnitary s)
  have hBorbit :
      ∀ s : ι → Bool,
        (star (cMatrixSignUnitary s : CMatrix ι) * B *
          (cMatrixSignUnitary s : CMatrix ι)).PosDef := by
    intro s
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (cMatrixSignUnitary s : CMatrix ι))]
    exact hB
  simpa [cMatrixPetzTraceUniformJointConvex, cMatrixPetzTraceSignUnitaryJensen]
    using hconv hAorbit hBorbit halpha_gt halpha_le_two

theorem cMatrixPetzTrace_dephase_one_le_of_signUnitary_jensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef) {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (hJ : cMatrixPetzTraceSignUnitaryJensen A B alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A)
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  classical
  have hAavg := cMatrixUnitaryDephase_one_eq_signAverage_of_isHermitian hA.isHermitian
  have hBavg := cMatrixUnitaryDephase_one_eq_signAverage_of_isHermitian hB.isHermitian
  have hJ' :
      cMatrixPetzTrace (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A)
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B) alpha ≤
        ∑ s : ι → Bool,
          ((Fintype.card (ι → Bool) : ℝ)⁻¹) *
            cMatrixPetzTrace
              (star (cMatrixSignUnitary s : CMatrix ι) * A *
                (cMatrixSignUnitary s : CMatrix ι))
              (star (cMatrixSignUnitary s : CMatrix ι) * B *
                (cMatrixSignUnitary s : CMatrix ι))
              alpha := by
    simpa [cMatrixPetzTraceSignUnitaryJensen, hAavg, hBavg] using hJ
  have hterm (s : ι → Bool) :
      cMatrixPetzTrace
          (star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
          (star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
          alpha =
        cMatrixPetzTrace A B alpha :=
    cMatrixPetzTrace_unitary_conj_eq_posSemidef_left
      A B hA hB (cMatrixSignUnitary s) halpha_nonneg
  have hweights :
      (∑ _s : ι → Bool, ((Fintype.card (ι → Bool) : ℝ)⁻¹)) = 1 := by
    have hcard_pos : 0 < (Fintype.card (ι → Bool) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩ :
        0 < Fintype.card (ι → Bool))
    rw [Finset.sum_const, nsmul_eq_mul]
    change (Fintype.card (ι → Bool) : ℝ) *
        (Fintype.card (ι → Bool) : ℝ)⁻¹ = 1
    field_simp [ne_of_gt hcard_pos]
  calc
    cMatrixPetzTrace (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A)
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B) alpha
        ≤ ∑ s : ι → Bool,
          ((Fintype.card (ι → Bool) : ℝ)⁻¹) *
            cMatrixPetzTrace
              (star (cMatrixSignUnitary s : CMatrix ι) * A *
                (cMatrixSignUnitary s : CMatrix ι))
              (star (cMatrixSignUnitary s : CMatrix ι) * B *
                (cMatrixSignUnitary s : CMatrix ι))
              alpha := hJ'
    _ = cMatrixPetzTrace A B alpha := by
      simp_rw [hterm]
      rw [← Finset.sum_mul, hweights, one_mul]

theorem cMatrixPetzTrace_unitaryDephase_le_of_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha)
    (hcoord :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTrace
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A')
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B') alpha ≤
        cMatrixPetzTrace A' B' alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  calc
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha =
        cMatrixPetzTrace
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A')
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B') alpha := by
          simpa [A', B'] using
            cMatrixPetzTrace_unitaryDephase_eq_coordinate_conj A B hA hB U
              (alpha := alpha)
              halpha_nonneg
    _ ≤ cMatrixPetzTrace A' B' alpha := hcoord
    _ = cMatrixPetzTrace A B alpha := by
          simpa [A', B'] using
            cMatrixPetzTrace_unitary_conj_eq_posSemidef_left A B hA hB U
              halpha_nonneg

theorem cMatrixPetzTrace_unitaryDephase_le_of_signUnitary_jensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hJ :
      cMatrixPetzTraceSignUnitaryJensen
        (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  exact cMatrixPetzTrace_unitaryDephase_le_of_coordinate A B hA hB U
    (alpha := alpha) (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) halpha_gt)) (by
      dsimp [A', B']
      exact cMatrixPetzTrace_dephase_one_le_of_signUnitary_jensen
        A' B' hA' hB' (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) halpha_gt)) hJ)

theorem cMatrixPetzTrace_unitaryDephase_le_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A' *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B' *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  exact cMatrixPetzTrace_unitaryDephase_le_of_signUnitary_jensen
    A B hA hB U halpha_gt halpha_le_two
    (cMatrixPetzTraceSignUnitaryJensen_of_uniformJointConvex
      A' B' hA' hB' halpha_gt halpha_le_two (by simpa [A', B'] using hconv))

/-- The source Petz monotonicity input for a single unitary dephasing map.

This is the narrow noncommutative bridge still needed after the scalar
threshold and diagonal-sum bookkeeping have been discharged. -/
def cMatrixPetzTraceUnitaryDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) : Prop :=
  cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
    cMatrixPetzTrace A B alpha

/-- Hilbert-Schmidt kernel for the Petz trace quadratic form.

Under `Matrix.vec`, this is left multiplication by `A^α` and right
multiplication by `B^(1-α)`. It is the finite-dimensional relative-modular
entry point for the Petz quasi-entropy route. -/
def cMatrixPetzTraceKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
    (CFC.rpow A alpha)

/-- Hilbert-Schmidt kernel for left multiplication by `A` under `Matrix.vec`. -/
def cMatrixLeftMulKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.kronecker (1 : CMatrix ι) A

/-- Hilbert-Schmidt kernel for right multiplication by `B` under `Matrix.vec`. -/
def cMatrixRightMulKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : CMatrix ι) : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.kronecker (Matrix.transpose B) (1 : CMatrix ι)

theorem cMatrixLeftMulKernel_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosSemidef) :
    (cMatrixLeftMulKernel A).PosSemidef := by
  simpa [cMatrixLeftMulKernel] using Matrix.PosSemidef.one.kronecker hA

theorem cMatrixRightMulKernel_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosSemidef) :
    (cMatrixRightMulKernel B).PosSemidef := by
  simpa [cMatrixRightMulKernel] using hB.transpose.kronecker Matrix.PosSemidef.one

theorem cMatrixLeftMulKernel_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) :
    (cMatrixLeftMulKernel A).PosDef := by
  simpa [cMatrixLeftMulKernel] using Matrix.PosDef.one.kronecker hA

theorem cMatrixRightMulKernel_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosDef) :
    (cMatrixRightMulKernel B).PosDef := by
  simpa [cMatrixRightMulKernel] using hB.transpose.kronecker Matrix.PosDef.one

theorem cMatrixLeftRightMulKernel_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) :
    cMatrixLeftMulKernel A * cMatrixRightMulKernel B =
      cMatrixRightMulKernel B * cMatrixLeftMulKernel A := by
  calc
    cMatrixLeftMulKernel A * cMatrixRightMulKernel B =
        Matrix.kronecker ((1 : CMatrix ι) * Matrix.transpose B)
          (A * (1 : CMatrix ι)) := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul (1 : CMatrix ι) (Matrix.transpose B)
                A (1 : CMatrix ι)).symm
    _ = Matrix.kronecker (Matrix.transpose B * (1 : CMatrix ι))
          ((1 : CMatrix ι) * A) := by
          rw [Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
    _ = cMatrixRightMulKernel B * cMatrixLeftMulKernel A := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul (Matrix.transpose B) (1 : CMatrix ι)
                (1 : CMatrix ι) A)

/-- The relative-modular Hilbert-Schmidt kernel `R(B⁻¹)L(A)` as a Kronecker
matrix. -/
theorem cMatrixRightInvMulLeftKernel_eq_kronecker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) :
    cMatrixRightMulKernel B⁻¹ * cMatrixLeftMulKernel A =
      Matrix.kronecker (Matrix.transpose B⁻¹) A := by
  calc
    cMatrixRightMulKernel B⁻¹ * cMatrixLeftMulKernel A =
        Matrix.kronecker (Matrix.transpose B⁻¹ * (1 : CMatrix ι))
          ((1 : CMatrix ι) * A) := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul (Matrix.transpose B⁻¹) (1 : CMatrix ι)
                (1 : CMatrix ι) A).symm
    _ = Matrix.kronecker (Matrix.transpose B⁻¹) A := by
          simp

/-- The Kronecker-shaped Petz kernel is the product of right- and
left-multiplication Hilbert-Schmidt kernels after applying the two scalar
functional-calculus powers.

This is the concrete finite-dimensional perspective identity
`R(B)^(1-α) L(A)^α = R(B^(1-α)) L(A^α)` at the kernel level; the remaining
Step-4 analytic input is the Jensen/Loewner inequality for this powered
perspective kernel. -/
theorem cMatrixPetzTraceKernel_eq_rightLeftPowerKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTraceKernel A B alpha =
      cMatrixRightMulKernel (CFC.rpow B (1 - alpha)) *
        cMatrixLeftMulKernel (CFC.rpow A alpha) := by
  calc
    cMatrixPetzTraceKernel A B alpha =
        Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
          (CFC.rpow A alpha) := by
          rfl
    _ = Matrix.kronecker
          (Matrix.transpose (CFC.rpow B (1 - alpha)) * (1 : CMatrix ι))
          ((1 : CMatrix ι) * CFC.rpow A alpha) := by
          simp
    _ = cMatrixRightMulKernel (CFC.rpow B (1 - alpha)) *
        cMatrixLeftMulKernel (CFC.rpow A alpha) := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul
                (Matrix.transpose (CFC.rpow B (1 - alpha))) (1 : CMatrix ι)
                (1 : CMatrix ι) (CFC.rpow A alpha))

/-- Equivalent left/right order for the Petz powered kernel.  The two
Hilbert-Schmidt multiplication kernels commute, so the perspective kernel can
be read as `L(A^α) R(B^(1-α))` as well as `R(B^(1-α)) L(A^α)`. -/
theorem cMatrixPetzTraceKernel_eq_leftRightPowerKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTraceKernel A B alpha =
      cMatrixLeftMulKernel (CFC.rpow A alpha) *
        cMatrixRightMulKernel (CFC.rpow B (1 - alpha)) := by
  rw [cMatrixPetzTraceKernel_eq_rightLeftPowerKernel]
  exact (cMatrixLeftRightMulKernel_commute
    (CFC.rpow A alpha) (CFC.rpow B (1 - alpha))).symm

/-- Petz trace as the quadratic form of `cMatrixPetzTraceKernel` at `vec 1`. -/
theorem cMatrixPetzTrace_eq_kernel_vec_one_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTrace A B alpha =
      (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
        (Matrix.mulVec (cMatrixPetzTraceKernel A B alpha)
          (Matrix.vec (1 : CMatrix ι)))).re := by
  simpa [cMatrixPetzTraceKernel] using
    cMatrixPetzTrace_eq_vec_one_kronecker_re A B alpha

private theorem cMatrixPetz_real_uniform_average_eq_complex_smul_sum
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (X : κ → CMatrix ι) :
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k) =
      (((Fintype.card κ : ℂ)⁻¹) • ∑ k, X k) := by
  ext i j
  have hcoeff : (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) =
      ((Fintype.card κ : ℂ)⁻¹) := by
    norm_num [Complex.ofReal_inv]
  calc
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k) i j =
        ∑ k, (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) * X k i j := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.smul_apply]
    _ = ∑ k, ((Fintype.card κ : ℂ)⁻¹) * X k i j := by
          simp [hcoeff]
    _ = ((Fintype.card κ : ℂ)⁻¹) * ∑ k, X k i j := by
          rw [Finset.mul_sum]
    _ = (((Fintype.card κ : ℂ)⁻¹) • ∑ k, X k) i j := by
          change ((Fintype.card κ : ℂ)⁻¹) * ∑ k, X k i j =
            ((Fintype.card κ : ℂ)⁻¹) * ((∑ k, X k) i j)
          rw [Matrix.sum_apply]

private theorem cMatrixPetz_real_uniform_average_transpose
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (X : κ → CMatrix ι) :
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • (X k).transpose) =
      (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k).transpose := by
  ext i j
  calc
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • (X k).transpose) i j =
        ∑ k, (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) * (X k j i) := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.smul_apply, Matrix.transpose_apply]
    _ = (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k) j i := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.smul_apply]

private theorem cMatrixPetz_reindex_le
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {M N : CMatrix α} (hMN : M ≤ N) :
    Matrix.reindex e e M ≤ Matrix.reindex e e N := by
  have hdiff : (N - M).PosSemidef := Matrix.le_iff.mp hMN
  have hdiff_reindex : (Matrix.reindex e e (N - M)).PosSemidef := by
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
      hdiff.submatrix e.symm
  have hsub :
      Matrix.reindex e e (N - M) =
        Matrix.reindex e e N - Matrix.reindex e e M := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.sub_apply]
  rw [hsub] at hdiff_reindex
  exact Matrix.le_iff.mpr hdiff_reindex

private theorem cMatrixPetz_reindex_prodComm_kronecker
    {a b : Type*} [Fintype a] [Fintype b]
    (M : CMatrix a) (N : CMatrix b) :
    Matrix.reindex (Equiv.prodComm a b) (Equiv.prodComm a b)
        (Matrix.kronecker M N) =
      Matrix.kronecker N M := by
  ext x y
  cases x
  cases y
  simp [Matrix.reindex_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_comm]

private theorem cMatrixPetz_reindex_finset_sum_smul
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (c : ℝ) (M : κ → CMatrix α) :
    Matrix.reindex e e (∑ k, c • M k) =
      ∑ k, c • Matrix.reindex e e (M k) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]

private theorem cMatrixPetz_submatrix_prodSwap_kronecker
    {a b : Type*} [Fintype a] [Fintype b]
    (M : CMatrix a) (N : CMatrix b) :
    (Matrix.kronecker M N).submatrix (Prod.swap : b × a → a × b) Prod.swap =
      Matrix.kronecker N M := by
  ext x y
  cases x
  cases y
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_comm]

private theorem cMatrixPetz_submatrix_prodSwap_kroneckerMap_mul
    {a b : Type*} [Fintype a] [Fintype b]
    (M : CMatrix a) (N : CMatrix b) :
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) M N).submatrix
        (Prod.swap : b × a → a × b) Prod.swap =
      Matrix.kroneckerMap (fun x y : ℂ => x * y) N M := by
  ext x y
  cases x
  cases y
  simp [Matrix.kroneckerMap_apply, mul_comm]

private theorem cMatrixPetz_submatrix_prodSwap_finset_sum_smul
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (c : ℝ) (M : κ → CMatrix (α × β)) :
    (∑ k, c • M k).submatrix (Prod.swap : β × α → α × β) Prod.swap =
      ∑ k, c • (M k).submatrix (Prod.swap : β × α → α × β) Prod.swap := by
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply]

private theorem cMatrixPetz_submatrix_prodSwap_smul_finset_sum
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (c : ℝ) (M : κ → CMatrix (α × β)) :
    (c • ∑ k, M k).submatrix (Prod.swap : β × α → α × β) Prod.swap =
      c • ∑ k, (M k).submatrix (Prod.swap : β × α → α × β) Prod.swap := by
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply]

private theorem cMatrixPetz_submatrix_prodSwap_complex_smul_finset_sum
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (c : ℂ) (M : κ → CMatrix (α × β)) :
    (c • ∑ k, M k).submatrix (Prod.swap : β × α → α × β) Prod.swap =
      c • ∑ k, (M k).submatrix (Prod.swap : β × α → α × β) Prod.swap := by
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply]

private def cMatrixPetzConjStarAlgEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] : CMatrix ι ≃⋆ₐ[ℝ] CMatrix ι :=
  StarAlgEquiv.ofAlgEquiv (AlgEquiv.mapMatrix (Complex.conjAe)) (by
    intro A
    ext i j
    simp)

private theorem cMatrixPetz_map_star_eq_transpose_of_posSemidef
    {ι : Type*} {A : CMatrix ι} (hA : A.PosSemidef) :
    A.map star = A.transpose := by
  ext i j
  simpa using hA.isHermitian.apply j i

private theorem cMatrixPetz_rpow_map_star_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) (s : ℝ) :
    CFC.rpow (A.map star) s = (CFC.rpow A s).map star := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hmap_eq : A.map star = A.transpose :=
    cMatrixPetz_map_star_eq_transpose_of_posSemidef hA.posSemidef
  have hmap_nonneg : 0 ≤ A.map star := by
    rw [hmap_eq]
    exact Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef.transpose
  change (A.map star) ^ s = (A ^ s).map star
  rw [CFC.rpow_eq_cfc_real (a := A.map star) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixPetzConjStarAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixPetzConjStarAlgEquiv (ι := ι))
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact
          (Real.continuousAt_rpow_const x s
            (.inl (ne_of_gt
              ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix ι => A.map star
        fun_prop)
      (hφa := by
        change IsSelfAdjoint (A.map star)
        rw [hmap_eq]
        exact hA.posSemidef.transpose.isHermitian)).symm

private theorem cMatrixPetz_rpow_transpose_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) (s : ℝ) :
    CFC.rpow A.transpose s = (CFC.rpow A s).transpose := by
  have hmapA : A.map star = A.transpose :=
    cMatrixPetz_map_star_eq_transpose_of_posSemidef hA.posSemidef
  have hpowmap :
      CFC.rpow (A.map star) s = (CFC.rpow A s).map star :=
    cMatrixPetz_rpow_map_star_posDef hA s
  have hpowPSD : (CFC.rpow A s).PosSemidef :=
    cMatrix_rpow_posSemidef (A := A) (s := s) hA.posSemidef
  have hpowmapTranspose :
      (CFC.rpow A s).map star = (CFC.rpow A s).transpose :=
    cMatrixPetz_map_star_eq_transpose_of_posSemidef hpowPSD
  rw [← hmapA, hpowmap, hpowmapTranspose]

set_option maxHeartbeats 800000 in
private theorem cMatrixPetz_rawTensorUniformJointConvex_Ioo_one_two
    {κ a b : Type*} [Fintype κ] [Nonempty κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b) {alpha : ℝ}
    (halpha : alpha ∈ Set.Ioo (1 : ℝ) 2)
    (hA : ∀ k, (A k).PosSemidef) (hB : ∀ k, (B k).PosDef) :
    Matrix.kronecker
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k) alpha)
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k) (1 - alpha)) ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        Matrix.kronecker (CFC.rpow (A k) alpha) (CFC.rpow (B k) (1 - alpha)) := by
  classical
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let Abar : CMatrix a := ∑ k, w • A k
  let Bbar : CMatrix b := ∑ k, w • B k
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hAbar : Abar.PosSemidef := by
    dsimp [Abar]
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.PosSemidef.smul (hA k) hw_nonneg
  have hBbar : Bbar.PosDef := by
    dsimp [Bbar]
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hB k) hw_pos
  obtain ⟨μ, hint, hrep⟩ :=
    cMatrixPetzPerspectiveIntegralRepresentation_Ioo_one_two
      (a := a) (b := b) (p := alpha) halpha
  let Fbar : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (alpha - 2)) •
      cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r Abar Bbar
  let Fk : κ → ℝ → CMatrix (a × b) := fun k r =>
    (r ^ (alpha - 2)) •
      cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r (A k) (B k)
  have hFbarInt : MeasureTheory.IntegrableOn Fbar (Set.Ioi 0) μ := by
    simpa [Fbar, Abar, Bbar] using hint hAbar hBbar
  have hFkInt : ∀ k, MeasureTheory.IntegrableOn (Fk k) (Set.Ioi 0) μ := by
    intro k
    simpa [Fk] using hint (hA k) (hB k)
  have hsumInt :
      MeasureTheory.IntegrableOn (fun r : ℝ => ∑ k, w • Fk k r) (Set.Ioi 0) μ := by
    have hsum :
        ∀ s : Finset κ,
          MeasureTheory.IntegrableOn (fun r : ℝ => ∑ k ∈ s, w • Fk k r)
            (Set.Ioi 0) μ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          have hz :
              MeasureTheory.Integrable (fun _r : ℝ => (0 : CMatrix (a × b)))
                (μ.restrict (Set.Ioi 0)) :=
            MeasureTheory.integrable_zero ℝ (CMatrix (a × b)) (μ.restrict (Set.Ioi 0))
          change MeasureTheory.Integrable (fun _r : ℝ => (0 : CMatrix (a × b)))
            (μ.restrict (Set.Ioi 0))
          exact hz
      | insert k s hks ih =>
          have hk : MeasureTheory.IntegrableOn (fun r : ℝ => w • Fk k r) (Set.Ioi 0) μ := by
            have hk' : MeasureTheory.Integrable (Fk k) (μ.restrict (Set.Ioi 0)) := by
              simpa [MeasureTheory.IntegrableOn] using hFkInt k
            have hksmul : MeasureTheory.Integrable (fun r : ℝ => w • Fk k r)
                (μ.restrict (Set.Ioi 0)) := hk'.smul w
            simpa [MeasureTheory.IntegrableOn] using hksmul
          have hadd := hk.add ih
          simpa [Finset.sum_insert hks, Pi.add_apply] using hadd
    simpa using hsum (Finset.univ : Finset κ)
  have hmono :
      ∀ r ∈ Set.Ioi (0 : ℝ), Fbar r ≤ ∑ k, w • Fk k r := by
    intro r hr
    have hr_pos : 0 < r := hr
    have hbase :=
      cMatrixPetzPerspectiveResolvent_uniform_average_le
        (a := a) (b := b) A B (r := r) (coeff := r)
        hr_pos hr_pos.le hA hB
    have hscaled :=
      smul_le_smul_of_nonneg_left hbase
        (Real.rpow_nonneg hr_pos.le (alpha - 2))
    simpa [Fbar, Fk, Abar, Bbar, w, Finset.smul_sum, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hintegral_le :
      ∫ r in Set.Ioi 0, Fbar r ∂μ ≤
        ∫ r in Set.Ioi 0, (∑ k, w • Fk k r) ∂μ :=
    cMatrixPetz_setIntegral_mono measurableSet_Ioi hFbarInt hsumInt hmono
  have hrepbar :
      Matrix.kronecker (CFC.rpow Abar alpha) (CFC.rpow Bbar (1 - alpha)) =
        ∫ r in Set.Ioi 0, Fbar r ∂μ := by
    simpa [Fbar, Abar, Bbar] using hrep hAbar hBbar
  have hrepks :
      ∀ k, Matrix.kronecker (CFC.rpow (A k) alpha) (CFC.rpow (B k) (1 - alpha)) =
        ∫ r in Set.Ioi 0, Fk k r ∂μ := by
    intro k
    simpa [Fk] using hrep (hA k) (hB k)
  have hsumIntegral :
      ∫ r in Set.Ioi 0, (∑ k, w • Fk k r) ∂μ =
        ∑ k, w • ∫ r in Set.Ioi 0, Fk k r ∂μ :=
    cMatrixPetz_setIntegral_finset_sum_smul (κ := κ) (ι := a × b)
      (μ := μ) (s := Set.Ioi 0) (f := Fk) w hFkInt
  calc
    Matrix.kronecker
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k) alpha)
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k) (1 - alpha)) =
        ∫ r in Set.Ioi 0, Fbar r ∂μ := by
          simpa [Abar, Bbar, w] using hrepbar
    _ ≤ ∫ r in Set.Ioi 0, (∑ k, w • Fk k r) ∂μ := hintegral_le
    _ = ∑ k, w • ∫ r in Set.Ioi 0, Fk k r ∂μ := hsumIntegral
    _ = ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        Matrix.kronecker (CFC.rpow (A k) alpha) (CFC.rpow (B k) (1 - alpha)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hrepks k]

/-- The finite-uniform rpow-perspective Jensen statement at the Hilbert-Schmidt
kernel level.

This is the exact remaining kernel inequality produced by the
Hansen-Pedersen/Effros perspective theorem for `x ↦ x^α`, `1 < α ≤ 2`.
It is intentionally matrix-valued: `cMatrixPetzTraceUniformJointConvex` is then
obtained by evaluating this Loewner inequality on `Matrix.vec 1`. -/
def cMatrixPetzTraceKernelUniformJointConvex
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) (alpha : ℝ) : Prop :=
  (∀ k, (A k).PosSemidef) →
  (∀ k, (B k).PosDef) →
  1 < alpha → alpha ≤ 2 →
    cMatrixPetzTraceKernel
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)
        alpha ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        cMatrixPetzTraceKernel (A k) (B k) alpha

theorem cMatrixPetzTraceKernelUniformJointConvex_Ioo_one_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ}
    (halpha : alpha ∈ Set.Ioo (1 : ℝ) 2) :
    cMatrixPetzTraceKernelUniformJointConvex A B alpha := by
  classical
  intro hA hB _halpha_gt _halpha_le_two
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let e : ι × ι ≃ ι × ι := Equiv.prodComm ι ι
  have hraw :=
    cMatrixPetz_rawTensorUniformJointConvex_Ioo_one_two
      (A := A) (B := fun k => (B k).transpose) (alpha := alpha) halpha
      hA (fun k => (hB k).transpose)
  have hreindex := cMatrixPetz_reindex_le (e := e) hraw
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hBbar : (∑ k, w • B k).PosDef := by
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hB k) hw_pos
  have hBavg_rpow :
      CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • (B k).transpose) (1 - alpha) =
        (CFC.rpow ((((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)) (1 - alpha)).transpose := by
    rw [cMatrixPetz_real_uniform_average_transpose]
    rw [cMatrixPetz_rpow_transpose_posDef hBbar]
    rw [cMatrixPetz_real_uniform_average_eq_complex_smul_sum]
  have hBavgC_rpow :
      CFC.rpow (((Fintype.card κ : ℂ)⁻¹) • ∑ k, (B k).transpose) (1 - alpha) =
        (CFC.rpow ((((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)) (1 - alpha)).transpose := by
    rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum
      (fun k => (B k).transpose)]
    exact hBavg_rpow
  have hBk_rpow :
      ∀ k, CFC.rpow (B k).transpose (1 - alpha) =
        (CFC.rpow (B k) (1 - alpha)).transpose := by
    intro k
    exact cMatrixPetz_rpow_transpose_posDef (hB k) (1 - alpha)
  rw [hBavg_rpow] at hreindex
  simp_rw [hBk_rpow] at hreindex
  simpa [cMatrixPetzTraceKernel, e, w,
    cMatrixPetz_reindex_prodComm_kronecker,
    cMatrixPetz_reindex_finset_sum_smul,
    cMatrixPetz_submatrix_prodSwap_kronecker,
    cMatrixPetz_submatrix_prodSwap_kroneckerMap_mul,
    cMatrixPetz_submatrix_prodSwap_finset_sum_smul,
    cMatrixPetz_submatrix_prodSwap_smul_finset_sum,
    cMatrixPetz_submatrix_prodSwap_complex_smul_finset_sum,
    cMatrixPetz_real_uniform_average_eq_complex_smul_sum,
    hBavg_rpow, hBavgC_rpow, hBk_rpow] using hreindex

private theorem cMatrixPetz_squarePerspective_uniform_average_le
    {κ n : Type*} [Fintype κ] [Nonempty κ] [Fintype n] [DecidableEq n]
    (X Y : κ → CMatrix n)
    (hX : ∀ k, (X k).IsHermitian)
    (hY : ∀ k, (Y k).PosDef) :
    let w : ℝ := (Fintype.card κ : ℝ)⁻¹
    let Xbar : CMatrix n := ∑ k, w • X k
    let Ybar : CMatrix n := ∑ k, w • Y k
    Xbar * Ybar⁻¹ * Xbar ≤ ∑ k, w • (X k * (Y k)⁻¹ * X k) := by
  classical
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let Xbar : CMatrix n := ∑ k, w • X k
  let Ybar : CMatrix n := ∑ k, w • Y k
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hYbar : Ybar.PosDef := by
    dsimp [Ybar]
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hY k) hw_pos
  have hw_self : IsSelfAdjoint w := by
    rw [isSelfAdjoint_iff]
    simp
  have hXbar : Xbar.IsHermitian := by
    dsimp [Xbar]
    induction (Finset.univ : Finset κ) using Finset.induction_on with
    | empty =>
        simp
    | insert k s hks ih =>
        rw [Finset.sum_insert hks]
        exact Matrix.IsHermitian.add (Matrix.IsHermitian.smul (hX k) hw_self) ih
  have hblock_k : ∀ k,
      (Matrix.fromBlocks (X k * (Y k)⁻¹ * X k) (X k) (X k) (Y k) :
        CMatrix (Sum n n)).PosSemidef := by
    intro k
    letI : Invertible (Y k) := (hY k).isUnit.invertible
    have hschur := Matrix.PosDef.fromBlocks₂₂
      (X k * (Y k)⁻¹ * X k) (X k) (D := Y k) (hY k)
    have hblock' := hschur.mpr (by
      simpa [hX k |>.eq] using (Matrix.PosSemidef.zero : (0 : CMatrix n).PosSemidef))
    simpa [hX k |>.eq] using hblock'
  have hsumBlock :
      (∑ k, w • (Matrix.fromBlocks (X k * (Y k)⁻¹ * X k) (X k) (X k) (Y k) :
        CMatrix (Sum n n))).PosSemidef := by
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.PosSemidef.smul (hblock_k k) hw_nonneg
  have hblockAvg :
      (Matrix.fromBlocks (∑ k, w • (X k * (Y k)⁻¹ * X k)) Xbar Xbar Ybar :
        CMatrix (Sum n n)).PosSemidef := by
    convert hsumBlock using 1
    ext (_ | _) (_ | _) <;>
      simp [Xbar, Ybar, Matrix.sum_apply, Matrix.smul_apply, Matrix.fromBlocks_smul]
  have hschurAvg :
      ((∑ k, w • (X k * (Y k)⁻¹ * X k)) - Xbar * Ybar⁻¹ * Xbar).PosSemidef := by
    letI : Invertible Ybar := hYbar.isUnit.invertible
    have hschur := Matrix.PosDef.fromBlocks₂₂
      (∑ k, w • (X k * (Y k)⁻¹ * X k)) Xbar (D := Ybar) hYbar
    have hschur' := hschur.mp (by simpa [hXbar.eq] using hblockAvg)
    simpa [hXbar.eq] using hschur'
  exact Matrix.le_iff.mpr hschurAvg

private theorem cMatrixLeftMulKernel_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : CMatrix ι) :
    cMatrixLeftMulKernel A * cMatrixLeftMulKernel C =
      cMatrixLeftMulKernel (A * C) := by
  calc
    cMatrixLeftMulKernel A * cMatrixLeftMulKernel C =
        Matrix.kronecker ((1 : CMatrix ι) * (1 : CMatrix ι)) (A * C) := by
          simpa [cMatrixLeftMulKernel, Matrix.kronecker] using
            (Matrix.mul_kronecker_mul (1 : CMatrix ι) (1 : CMatrix ι) A C).symm
    _ = cMatrixLeftMulKernel (A * C) := by
          simp [cMatrixLeftMulKernel]

private theorem cMatrixRightMulKernel_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosDef) :
    (cMatrixRightMulKernel B)⁻¹ = cMatrixRightMulKernel B⁻¹ := by
  apply Matrix.inv_eq_right_inv
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hBT : B.transpose * B⁻¹.transpose = (1 : CMatrix ι) := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul B hdet]
    ext i j
    simp [Matrix.one_apply, eq_comm]
  calc
    cMatrixRightMulKernel B * cMatrixRightMulKernel B⁻¹ =
        Matrix.kronecker (B.transpose * B⁻¹.transpose)
          ((1 : CMatrix ι) * (1 : CMatrix ι)) := by
          simpa [cMatrixRightMulKernel, Matrix.kronecker] using
            (Matrix.mul_kronecker_mul B.transpose B⁻¹.transpose
              (1 : CMatrix ι) (1 : CMatrix ι)).symm
    _ = 1 := by
          rw [hBT]
          ext x y
          rcases x with ⟨x₁, x₂⟩
          rcases y with ⟨y₁, y₂⟩
          by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
            Prod.ext_iff, h₁, h₂]

private theorem cMatrixLeftMulKernel_uniform_average
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → CMatrix ι) :
    cMatrixLeftMulKernel (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k) =
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) • cMatrixLeftMulKernel (A k) := by
  rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum A]
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  by_cases hxy : x₁ = y₁
  · subst y₁
    simp [cMatrixLeftMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
  · simp [cMatrixLeftMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply, hxy]

private theorem cMatrixRightMulKernel_uniform_average
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (B : κ → CMatrix ι) :
    cMatrixRightMulKernel (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k) =
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) • cMatrixRightMulKernel (B k) := by
  rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum B]
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  by_cases hxy : x₂ = y₂
  · subst y₂
    simp [cMatrixRightMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply]
  · simp [cMatrixRightMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply, hxy]

private theorem cMatrixPetzTraceKernel_two_eq_squarePerspective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CMatrix ι} (hA : A.PosSemidef) (hB : B.PosDef) :
    cMatrixPetzTraceKernel A B 2 =
      cMatrixLeftMulKernel A * (cMatrixRightMulKernel B)⁻¹ *
        cMatrixLeftMulKernel A := by
  have hA_two : CFC.rpow A (2 : ℝ) = A * A := by
    simpa [pow_two] using
      (CFC.rpow_natCast A 2 (Matrix.nonneg_iff_posSemidef.mpr hA))
  have hB_neg_one : CFC.rpow B (-1 : ℝ) = B⁻¹ := by
    have h := cMatrixPetz_rpow_nonsing_inv_eq_rpow_neg hB (1 : ℝ)
    have hBpow1 : CFC.rpow B⁻¹ (1 : ℝ) = B⁻¹ :=
      CFC.rpow_one B⁻¹ (ha := Matrix.nonneg_iff_posSemidef.mpr hB.inv.posSemidef)
    rw [hBpow1] at h
    exact h.symm
  have hB_one_sub_two : CFC.rpow B (1 - (2 : ℝ)) = B⁻¹ := by
    rw [show (1 - (2 : ℝ)) = -1 by norm_num]
    exact hB_neg_one
  calc
    cMatrixPetzTraceKernel A B 2 =
        cMatrixLeftMulKernel (A * A) * cMatrixRightMulKernel B⁻¹ := by
          rw [cMatrixPetzTraceKernel_eq_leftRightPowerKernel, hA_two, hB_one_sub_two]
    _ = cMatrixLeftMulKernel A * cMatrixRightMulKernel B⁻¹ *
        cMatrixLeftMulKernel A := by
          rw [← cMatrixLeftMulKernel_mul A A]
          calc
            (cMatrixLeftMulKernel A * cMatrixLeftMulKernel A) *
                cMatrixRightMulKernel B⁻¹ =
                cMatrixLeftMulKernel A *
                  (cMatrixLeftMulKernel A * cMatrixRightMulKernel B⁻¹) := by
                  rw [Matrix.mul_assoc]
            _ = cMatrixLeftMulKernel A *
                  (cMatrixRightMulKernel B⁻¹ * cMatrixLeftMulKernel A) := by
                  rw [cMatrixLeftRightMulKernel_commute]
            _ = cMatrixLeftMulKernel A * cMatrixRightMulKernel B⁻¹ *
                  cMatrixLeftMulKernel A := by
                  rw [Matrix.mul_assoc]
    _ = cMatrixLeftMulKernel A * (cMatrixRightMulKernel B)⁻¹ *
        cMatrixLeftMulKernel A := by
          rw [cMatrixRightMulKernel_inv hB]

theorem cMatrixPetzTraceKernelUniformJointConvex_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) :
    cMatrixPetzTraceKernelUniformJointConvex A B 2 := by
  classical
  intro hA hB _halpha_gt _halpha_le_two
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let X : κ → CMatrix (ι × ι) := fun k => cMatrixLeftMulKernel (A k)
  let Y : κ → CMatrix (ι × ι) := fun k => cMatrixRightMulKernel (B k)
  let Abar : CMatrix ι := ((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k
  let Bbar : CMatrix ι := ((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hAbar : Abar.PosSemidef := by
    dsimp [Abar]
    rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum A]
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.PosSemidef.smul (hA k) hw_nonneg
  have hBbar : Bbar.PosDef := by
    dsimp [Bbar]
    rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum B]
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hB k) hw_pos
  have hsq :=
    cMatrixPetz_squarePerspective_uniform_average_le X Y
      (fun k => (cMatrixLeftMulKernel_posSemidef (hA k)).isHermitian)
      (fun k => cMatrixRightMulKernel_posDef (hB k))
  have hsq' :
      cMatrixLeftMulKernel Abar * (cMatrixRightMulKernel Bbar)⁻¹ *
          cMatrixLeftMulKernel Abar ≤
        ∑ k, w •
          (cMatrixLeftMulKernel (A k) * (cMatrixRightMulKernel (B k))⁻¹ *
            cMatrixLeftMulKernel (A k)) := by
    simpa [X, Y, Abar, Bbar, w,
      cMatrixLeftMulKernel_uniform_average,
      cMatrixRightMulKernel_uniform_average] using hsq
  have hleft :
      cMatrixPetzTraceKernel Abar Bbar 2 =
        cMatrixLeftMulKernel Abar * (cMatrixRightMulKernel Bbar)⁻¹ *
          cMatrixLeftMulKernel Abar :=
    cMatrixPetzTraceKernel_two_eq_squarePerspective hAbar hBbar
  have hright :
      ∀ k, cMatrixPetzTraceKernel (A k) (B k) 2 =
        cMatrixLeftMulKernel (A k) * (cMatrixRightMulKernel (B k))⁻¹ *
          cMatrixLeftMulKernel (A k) := by
    intro k
    exact cMatrixPetzTraceKernel_two_eq_squarePerspective (hA k) (hB k)
  calc
    cMatrixPetzTraceKernel
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)
        2 =
        cMatrixLeftMulKernel Abar * (cMatrixRightMulKernel Bbar)⁻¹ *
          cMatrixLeftMulKernel Abar := by
          simpa [Abar, Bbar] using hleft
    _ ≤ ∑ k, w •
          (cMatrixLeftMulKernel (A k) * (cMatrixRightMulKernel (B k))⁻¹ *
            cMatrixLeftMulKernel (A k)) := hsq'
    _ = ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
          cMatrixPetzTraceKernel (A k) (B k) 2 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hright k]

theorem cMatrixPetzTraceKernelUniformJointConvex_of_rpow_perspective_one_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ} :
    cMatrixPetzTraceKernelUniformJointConvex A B alpha := by
  classical
  intro hA hB halpha_gt halpha_le_two
  by_cases halpha_lt_two : alpha < 2
  · exact
      cMatrixPetzTraceKernelUniformJointConvex_Ioo_one_two
        A B ⟨halpha_gt, halpha_lt_two⟩ hA hB halpha_gt halpha_le_two
  · have halpha_eq_two : alpha = 2 :=
      le_antisymm halpha_le_two (le_of_not_gt halpha_lt_two)
    subst alpha
    exact cMatrixPetzTraceKernelUniformJointConvex_two
      A B hA hB (by norm_num) (by norm_num)

/-- Kernel-level finite uniform Jensen implies the scalar Petz trace
finite-uniform joint convexity used by the dephasing bridge. -/
theorem cMatrixPetzTraceUniformJointConvex_of_kernel_uniformJointConvex
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ}
    (hkernel : cMatrixPetzTraceKernelUniformJointConvex A B alpha) :
    cMatrixPetzTraceUniformJointConvex A B alpha := by
  intro hA hB halpha_gt halpha_le_two
  let x : ι × ι → ℂ := Matrix.vec (1 : CMatrix ι)
  have hquad :=
    cMatrix_quadraticForm_re_mono
      (hkernel hA hB halpha_gt halpha_le_two) x
  have hsum :
      (dotProduct (star x)
        (Matrix.mulVec
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) •
            cMatrixPetzTraceKernel (A k) (B k) alpha) x)).re =
        ∑ k, ((Fintype.card κ : ℝ)⁻¹) *
          cMatrixPetzTrace (A k) (B k) alpha := by
    rw [cMatrix_quadraticForm_re_sum_smul]
    simp_rw [cMatrixPetzTrace_eq_kernel_vec_one_re]
    rfl
  rw [← cMatrixPetzTrace_eq_kernel_vec_one_re
      (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
      (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k) alpha] at hquad
  rw [hsum] at hquad
  exact hquad

/-- Uniform joint convexity of the Petz trace from the rpow perspective route.

The resolvent layer already supplies finite Jensen for each positive
Audenaert/Effros integrand.  After the remaining rpow-perspective integral
identity has produced the corresponding Hilbert-Schmidt kernel Loewner
Jensen statement, this theorem closes the exact scalar
`cMatrixPetzTraceUniformJointConvex` shape consumed by the finite-AEP
dephasing chain. -/
theorem cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ} :
    cMatrixPetzTraceUniformJointConvex A B alpha :=
  cMatrixPetzTraceUniformJointConvex_of_kernel_uniformJointConvex
    A B (cMatrixPetzTraceKernelUniformJointConvex_of_rpow_perspective_one_two A B)

/-- The remaining Petz Jensen/monotonicity input expressed directly on the
Hilbert-Schmidt quadratic kernels.

This is intentionally narrower than full Petz quasi-entropy monotonicity: it
only asks for the vector/kernel comparison needed by the unitary pinching map
used in the TCR finite-AEP proof. -/
def cMatrixPetzTraceKernelDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) : Prop :=
  (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
      (Matrix.mulVec
        (cMatrixPetzTraceKernel
          (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha)
        (Matrix.vec (1 : CMatrix ι)))).re ≤
    (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
      (Matrix.mulVec (cMatrixPetzTraceKernel A B alpha)
        (Matrix.vec (1 : CMatrix ι)))).re

theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ)
    (hkernel : cMatrixPetzTraceKernelDephaseMonotone A B U alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha := by
  unfold cMatrixPetzTraceUnitaryDephaseMonotone
  rw [cMatrixPetzTrace_eq_kernel_vec_one_re
      (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha,
    cMatrixPetzTrace_eq_kernel_vec_one_re A B alpha]
  exact hkernel

/-- Sign-coordinate Jensen supplies the narrow unitary-dephasing monotonicity
predicate. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_signUnitaryJensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hJ :
      cMatrixPetzTraceSignUnitaryJensen
        (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha := by
  unfold cMatrixPetzTraceUnitaryDephaseMonotone
  exact cMatrixPetzTrace_unitaryDephase_le_of_signUnitary_jensen
    A B hA hB U halpha_gt halpha_le_two hJ

/-- Finite uniform joint convexity on the sign orbit supplies the narrow
unitary-dephasing monotonicity predicate. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A' *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B' *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  exact cMatrixPetzTraceUnitaryDephaseMonotone_of_signUnitaryJensen
    A B hA hB U halpha_gt halpha_le_two
    (cMatrixPetzTraceSignUnitaryJensen_of_uniformJointConvex
      A' B' hA' hB' halpha_gt halpha_le_two (by simpa [A', B'] using hconv))

/-- A global finite-uniform Petz joint-convexity input supplies the narrow
unitary-dephasing monotonicity predicate for any finite matrix pair.

This wrapper is intentionally light: it composes the already-proved sign-orbit
pinching bridge with a reusable universal joint-convexity hypothesis.  The
remaining analytic theorem is the production of `hjoint` from the Petz
perspective/operator-convexity route for `1 < α ≤ 2`. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex_all
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hjoint :
      ∀ {κ : Type w} [Fintype κ] [Nonempty κ],
        (Aκ Bκ : κ → CMatrix ι) →
          cMatrixPetzTraceUniformJointConvex Aκ Bκ alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
  cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
    A B hA hB U halpha_gt halpha_le_two
    (by
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      simpa [A', B'] using
        hjoint (κ := ι → Bool)
          (fun s : ι → Bool =>
            star (cMatrixSignUnitary s : CMatrix ι) * A' *
              (cMatrixSignUnitary s : CMatrix ι))
          (fun s : ι → Bool =>
            star (cMatrixSignUnitary s : CMatrix ι) * B' *
              (cMatrixSignUnitary s : CMatrix ι)))

/-- Petz trace is monotone under unitary dephasing for `1 < α ≤ 2`, using the
finite-dimensional rpow perspective/Jensen theorem. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_rpow_perspective_one_two
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
  cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex_all
    A B hA hB U halpha_gt halpha_le_two
    (fun {κ} [Fintype κ] [Nonempty κ] (Aκ Bκ : κ → CMatrix ι) =>
      cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two Aκ Bκ)

/-- Petz trace of the dephased pair is exactly the source diagonal sum.

This discharges the unitary-basis, CFC-power, and trace bookkeeping around TCR
lines 664--670. The remaining mathematical input is the Petz quasi-entropy
monotonicity inequality comparing this dephased Petz trace with the original
noncommutative Petz trace. -/
theorem cMatrix_petzTrace_unitaryDephase_eq_diag_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) :
    ((CFC.rpow (cMatrixUnitaryDephase U A) alpha *
        CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha)).trace).re =
      ∑ i,
        ((star (U : CMatrix ι) * A * (U : CMatrix ι)) i i).re ^ alpha *
          ((star (U : CMatrix ι) * B * (U : CMatrix ι)) i i).re ^
            (1 - alpha) := by
  classical
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  let a : ι → ℝ := fun i => (A' i i).re
  let b : ι → ℝ := fun i => (B' i i).re
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    simpa [A', a] using posSemidef_unitary_conj_diag_re_nonneg hA U i
  have hb_nonneg : ∀ i, 0 ≤ b i := by
    intro i
    exact le_of_lt (by
      simpa [B', b] using posDef_unitary_conj_diag_re_pos hB U i)
  have hApow :
      CFC.rpow (cMatrixUnitaryDephase U A) alpha =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((a i) ^ alpha : ℝ) : ℂ) : CMatrix ι) *
            star (U : CMatrix ι) := by
    unfold cMatrixUnitaryDephase
    simpa [A', a] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U a ha_nonneg alpha
  have hBpow :
      CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha) =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((b i) ^ (1 - alpha) : ℝ) : ℂ) :
            CMatrix ι) *
            star (U : CMatrix ι) := by
    unfold cMatrixUnitaryDephase
    simpa [B', b] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U b hb_nonneg (1 - alpha)
  rw [hApow, hBpow]
  simpa [A', B', a, b] using
    trace_mul_unitary_conj_diagonal_ofReal_re U
      (fun i => (a i) ^ alpha) (fun i => (b i) ^ (1 - alpha))

/-- Source-facing dephasing/Petz comparison with the true monotonicity step as
an explicit hypothesis.

The hypothesis is exactly the Petz quasi-entropy monotonicity for the pinching
map in TCR lines 664--670, specialized to `g(t)=t^alpha` and the unitary basis
`U`. This theorem removes the scalar/unitary/reindex bookkeeping from callers:
from that monotonicity statement it returns the diagonal-sum comparison used by
the positive-part trace bound. -/
theorem cMatrix_dephased_eigenbasis_sum_le_petzTrace_of_dephasing_monotonicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (_halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hmono :
      ((CFC.rpow (cMatrixUnitaryDephase U A) alpha *
          CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha)).trace).re ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re) :
    let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
    let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
    ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) ≤
      ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  classical
  dsimp
  rw [← cMatrix_petzTrace_unitaryDephase_eq_diag_sum A B hA hB U alpha]
  exact hmono

/-- Source-shaped scalar/eigenbasis part of the TCR positive-part trace step.

For `H = A - λB`, diagonalize `H` and set
`r_i = ⟨ψ_i,Aψ_i⟩`, `s_i = ⟨ψ_i,Bψ_i⟩`.  This proves the threshold estimate up
to the dephasing/Petz monotonicity comparison
`∑ r_i^α s_i^(1-α) ≤ Tr(A^α B^(1-α))`. -/
theorem cMatrix_posPart_trace_re_le_scaled_dephased_eigenbasis_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha)
    (hH : (A - lambda • B).IsHermitian) :
    let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
    let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
    let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) := by
  classical
  let H : CMatrix ι := A - lambda • B
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  let p : ι → ℝ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    by_cases hi : 0 < hH.eigenvalues i <;> simp [p, hi]
  have hp_le_one : ∀ i, p i ≤ 1 := by
    intro i
    by_cases hi : 0 < hH.eigenvalues i <;> simp [p, hi]
  have hA_diag_nonneg : ∀ i, 0 ≤ (A' i i).re := by
    intro i
    simpa [A'] using posSemidef_unitary_conj_diag_re_nonneg hA U i
  have hB_diag_pos : ∀ i, 0 < (B' i i).re := by
    intro i
    simpa [B'] using posDef_unitary_conj_diag_re_pos hB U i
  have hHdiag (i : ι) :
      ((star (U : CMatrix ι) * H * (U : CMatrix ι)) i i).re =
        (A' i i).re - lambda * (B' i i).re := by
    have hmat :
        star (U : CMatrix ι) * H * (U : CMatrix ι) =
          A' - lambda • B' := by
      dsimp [H, A', B']
      noncomm_ring
    rw [hmat]
    simp [Complex.real_smul]
  have htrace_projector :
      ((H * positiveSpectralProjector H hH).trace).re =
        ∑ i, (((star (U : CMatrix ι) * H * (U : CMatrix ι)) i i).re * p i) := by
    unfold positiveSpectralProjector
    have hmask :
        (Matrix.diagonal (fun i =>
          if 0 < hH.eigenvalues i then (1 : ℂ) else 0) : CMatrix ι) =
            Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : 0 < hH.eigenvalues i <;> simp [p, hi]
      · simp [Matrix.diagonal, hij]
    rw [hmask]
    have htrace := trace_mul_unitary_diagonal_conj_re H U p
    have hdiag :=
      trace_mul_diagonal_ofReal_re
        (star (U : CMatrix ι) * H * (U : CMatrix ι)) p
    simpa [H, U] using htrace.trans hdiag
  have hpos_trace :
      ((A - lambda • B)⁺).trace.re =
        ∑ i, p i * ((A' i i).re - lambda * (B' i i).re) := by
    have hscore := positiveSpectralProjector_score_eq_posPart_trace H hH
    calc
      ((A - lambda • B)⁺).trace.re = (H⁺).trace.re := by rfl
      _ = ((H * positiveSpectralProjector H hH).trace).re := hscore.symm
      _ = ∑ i, (((star (U : CMatrix ι) * H * (U : CMatrix ι)) i i).re * p i) :=
          htrace_projector
      _ = ∑ i, p i * ((A' i i).re - lambda * (B' i i).re) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hHdiag i]
          ring
  calc
    ((A - lambda • B)⁺).trace.re =
        ∑ i, p i * ((A' i i).re - lambda * (B' i i).re) := hpos_trace
    _ ≤ ∑ i, lambda ^ (1 - alpha) *
        ((A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha)) :=
          Finset.sum_le_sum fun i _ =>
            scalar_effect_threshold_le_scaled_petz (hp_nonneg i) (hp_le_one i)
              (hA_diag_nonneg i) (hB_diag_pos i) hlambda (le_of_lt halpha_gt)
    _ = lambda ^ (1 - alpha) *
        ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) := by
          rw [Finset.mul_sum]

/-- Positive-part trace bound from the source scalar threshold plus the
remaining Petz monotonicity/dephasing comparison. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephased_eigenbasis_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hdephase :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  classical
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hscalar :
      ((A - lambda • B)⁺).trace.re ≤
        lambda ^ (1 - alpha) *
          ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) := by
    simpa [U, A', B'] using
      cMatrix_posPart_trace_re_le_scaled_dephased_eigenbasis_sum
        A B hA hB hlambda halpha_gt hH
  have hlambda_pow_nonneg : 0 ≤ lambda ^ (1 - alpha) := by
    positivity
  exact hscalar.trans (mul_le_mul_of_nonneg_left hdephase hlambda_pow_nonneg)

/-- Positive-part trace bound from the source scalar threshold plus Petz
quasi-entropy monotonicity for the dephasing/pinching map.

Compared with
`cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephased_eigenbasis_bound`,
this exposes the remaining source input in its Petz form: monotonicity says the
Petz trace cannot increase after dephasing in the eigenbasis of `A - λB`. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephasing_monotonicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hmono :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      ((CFC.rpow (cMatrixUnitaryDephase U A) alpha *
          CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha)).trace).re ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  classical
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  have hdephase :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
    exact cMatrix_dephased_eigenbasis_sum_le_petzTrace_of_dephasing_monotonicity
      A B hA hB U halpha_gt halpha_le_two (by simpa [U] using hmono)
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephased_eigenbasis_bound
    A B hA hB hlambda halpha_gt halpha_le_two hH (by simpa [U] using hdephase)

/-- Positive-part trace bound with the remaining dephasing monotonicity input
packaged through `cMatrixPetzTrace`. -/
theorem cMatrix_posPart_trace_re_le_scaled_cMatrixPetzTrace_of_dephasing_monotonicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hmono :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
        cMatrixPetzTrace A B alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephasing_monotonicity
    A B hA hB hlambda halpha_gt halpha_le_two hH (by
      simpa [cMatrixPetzTrace] using hmono)

/-- Positive-part trace bound from the narrow unitary-dephasing monotonicity
predicate. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hmono :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  exact cMatrix_posPart_trace_re_le_scaled_cMatrixPetzTrace_of_dephasing_monotonicity
    A B hA hB hlambda halpha_gt halpha_le_two hH (by
      simpa [cMatrixPetzTraceUnitaryDephaseMonotone] using hmono)

/-- Positive-part trace bound from the Hilbert-Schmidt kernel form of the
remaining Petz dephasing monotonicity input. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_kernelDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hkernel :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone A B U alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
      A B U alpha (by simpa [U] using hkernel)
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
    A B hA hB hlambda halpha_gt halpha_le_two hH (by simpa [U] using hmono)

/-- Positive-part trace bound with the remaining noncommutative input packaged
as finite uniform joint convexity on the sign orbit of the eigenbasis of
`A - λB`. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      let H : CMatrix ι := A - lambda • B
      let hH : H.IsHermitian :=
        hA.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A' *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B' *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  let H : CMatrix ι := A - lambda • B
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hA.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
      A B hA hB U halpha_gt halpha_le_two (by
        simpa [H, hH, U] using hconv)
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
    A B hA hB hlambda halpha_gt halpha_le_two hH (by
      simpa [U] using hmono)

/-- Checked commutative/simultaneously diagonal bridge for the Petz
effect-variational inequality.

This does not close the noncommutative `A,B` bridge, but it proves the exact
predicate when `A` and `B` are positive diagonal in one unitary basis. -/
theorem cMatrixPetzTraceEffectVariational_of_simultaneously_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha)
    (hA :
      A = (U : CMatrix ι) *
        (Matrix.diagonal fun i => ((a i : ℝ) : ℂ) : CMatrix ι) *
          star (U : CMatrix ι))
    (hB :
      B = (U : CMatrix ι) *
        (Matrix.diagonal fun i => ((b i : ℝ) : ℂ) : CMatrix ι) *
          star (U : CMatrix ι)) :
    cMatrixPetzTraceEffectVariational A B lambda alpha := by
  intro E hEpos hEle
  let E' : CMatrix ι := star (U : CMatrix ι) * E * (U : CMatrix ι)
  have hE'pos : E'.PosSemidef := by
    simpa [E'] using posSemidef_unitary_conj hEpos U
  have hE'le : E' ≤ 1 := by
    rw [Matrix.le_iff]
    have hdiff : ((1 : CMatrix ι) - E).PosSemidef := by
      simpa [Matrix.le_iff] using hEle
    have hconj : (star (U : CMatrix ι) * ((1 : CMatrix ι) - E) *
        (U : CMatrix ι)).PosSemidef := by
      simpa using posSemidef_unitary_conj hdiff U
    have hmatrix :
        star (U : CMatrix ι) * ((1 : CMatrix ι) - E) * (U : CMatrix ι) =
          (1 : CMatrix ι) - E' := by
      dsimp [E']
      have hU : star (U : CMatrix ι) * (U : CMatrix ι) = 1 := by
        exact Unitary.coe_star_mul_self U
      calc
        star (U : CMatrix ι) * ((1 : CMatrix ι) - E) * (U : CMatrix ι) =
            star (U : CMatrix ι) * (1 : CMatrix ι) * (U : CMatrix ι) -
              star (U : CMatrix ι) * E * (U : CMatrix ι) := by
              noncomm_ring
        _ = (1 : CMatrix ι) - star (U : CMatrix ι) * E * (U : CMatrix ι) := by
              rw [Matrix.mul_one, hU]
    simpa [hmatrix] using hconj
  have hdiag_nonneg : ∀ i, 0 ≤ (E' i i).re :=
    fun i => posSemidef_diagonal_re_nonneg hE'pos i
  have hdiag_le_one : ∀ i, (E' i i).re ≤ 1 := by
    intro i
    have hcompl : ((1 : CMatrix ι) - E').PosSemidef := by
      simpa [Matrix.le_iff] using hE'le
    have hnonneg := posSemidef_diagonal_re_nonneg hcompl i
    have hentry :
        (((1 : CMatrix ι) - E') i i).re = 1 - (E' i i).re := by
      simp
    linarith
  have hEA :
      ((E * A).trace).re = ∑ i, (E' i i).re * a i := by
    rw [hA]
    rw [trace_mul_unitary_diagonal_conj_re]
    exact trace_mul_diagonal_ofReal_re E' a
  have hEB :
      ((E * B).trace).re = ∑ i, (E' i i).re * b i := by
    rw [hB]
    rw [trace_mul_unitary_diagonal_conj_re]
    exact trace_mul_diagonal_ofReal_re E' b
  have hApow :
      CFC.rpow A alpha =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((a i) ^ alpha : ℝ) : ℂ) : CMatrix ι) *
            star (U : CMatrix ι) := by
    rw [hA]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U a (fun i => le_of_lt (ha i)) alpha
  have hBpow :
      CFC.rpow B (1 - alpha) =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((b i) ^ (1 - alpha) : ℝ) : ℂ) : CMatrix ι) *
            star (U : CMatrix ι) := by
    rw [hB]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U b (fun i => le_of_lt (hb i))
      (1 - alpha)
  have hpetz :
      ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re =
        ∑ i, (a i) ^ alpha * (b i) ^ (1 - alpha) := by
    rw [hApow, hBpow]
    simpa using trace_mul_unitary_conj_diagonal_ofReal_re U
      (fun i => (a i) ^ alpha) (fun i => (b i) ^ (1 - alpha))
  have hsum :
      (∑ i, (E' i i).re * a i) -
          lambda * (∑ i, (E' i i).re * b i) ≤
        lambda ^ (1 - alpha) *
          (∑ i, (a i) ^ alpha * (b i) ^ (1 - alpha)) := by
    calc
      (∑ i, (E' i i).re * a i) -
          lambda * (∑ i, (E' i i).re * b i)
          = ∑ i, (E' i i).re * (a i - lambda * b i) := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ ≤ ∑ i, lambda ^ (1 - alpha) * ((a i) ^ alpha * (b i) ^ (1 - alpha)) :=
          Finset.sum_le_sum fun i _ =>
            scalar_effect_threshold_le_scaled_petz (hdiag_nonneg i) (hdiag_le_one i)
              (le_of_lt (ha i)) (hb i) hlambda (le_of_lt halpha_gt)
      _ = lambda ^ (1 - alpha) *
          (∑ i, (a i) ^ alpha * (b i) ^ (1 - alpha)) := by
            rw [Finset.mul_sum]
  rw [hEA, hEB, hpetz]
  exact hsum

/-- Reduction from the Petz effect-variational inequality to the desired
positive-part trace threshold inequality. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_effect_variational
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (_halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hvar : cMatrixPetzTraceEffectVariational A B lambda alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  let H : CMatrix ι := A - lambda • B
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hA.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let P : CMatrix ι := positiveSpectralProjector H hH
  have hPpos : P.PosSemidef := by
    simpa [P] using positiveSpectralProjector_posSemidef H hH
  have hPle : P ≤ 1 := by
    simpa [P] using positiveSpectralProjector_le_one H hH
  have hvarP := hvar P hPpos hPle
  have htrace :
      (((P * A).trace).re - lambda * ((P * B).trace).re) =
        ((P * H).trace).re := by
    dsimp [H]
    simp [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul,
      Complex.real_smul]
  have hscore :
      ((P * H).trace).re = (H⁺).trace.re := by
    have h := positiveSpectralProjector_score_eq_posPart_trace H hH
    rw [Matrix.trace_mul_comm] at h
    simpa [P] using h
  simpa [H] using (hscore ▸ htrace ▸ hvarP)

namespace State

private theorem fixedSmooth_trace_re_le_of_le {ι : Type*} [Fintype ι] {X Y : CMatrix ι}
    (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have hnon : 0 ≤ (Y - X).trace.re := (Matrix.PosSemidef.trace_nonneg hXY).1
  have htrace : (Y - X).trace.re = Y.trace.re - X.trace.re := by
    simp [Matrix.trace_sub]
  linarith

private theorem fixedSmooth_identityTensorStateMatrix_trace_re (σ : State b) :
    (identityTensorStateMatrix (a := a) σ).trace.re = (Fintype.card a : ℝ) := by
  change (Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) σ.matrix).trace.re =
    (Fintype.card a : ℝ)
  rw [Matrix.trace_kronecker, σ.trace_eq_one, Matrix.trace_one]
  norm_num

private theorem neg_log2_rpow_two_neg (lam : ℝ) :
    -log2 (Real.rpow 2 (-lam)) = lam := by
  unfold log2
  change -(Real.log ((2 : ℝ) ^ (-lam)) / Real.log 2) = lam
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lam)]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  field_simp [hlog2]

private theorem rpow_two_log2_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  apply Real.log_injOn_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    hx
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  unfold log2
  field_simp [ne_of_gt (Real.log_pos one_lt_two)]

private theorem rpow_two_mul_log2_pos {x gamma : ℝ} (hx : 0 < x) :
    Real.rpow 2 (gamma * log2 x) = x ^ gamma := by
  apply Real.log_injOn_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    (Real.rpow_pos_of_pos hx gamma)
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow hx]
  unfold log2
  field_simp [ne_of_gt (Real.log_pos one_lt_two)]

private theorem rpow_two_neg_sub_mul_log2_pos {H gamma x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (-(H - gamma * log2 x)) =
      Real.rpow 2 (-H) * x ^ gamma := by
  calc
    Real.rpow 2 (-(H - gamma * log2 x)) =
        Real.rpow 2 (-H + gamma * log2 x) := by ring_nf
    _ = Real.rpow 2 (-H) * Real.rpow 2 (gamma * log2 x) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-H) (gamma * log2 x)
    _ = Real.rpow 2 (-H) * x ^ gamma := by
        rw [rpow_two_mul_log2_pos hx]

private theorem traceNorm_eq_trace_re_of_posSemidef
    (A : CMatrix (Prod a b)) (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  rw [traceNorm]
  have hherm : Matrix.conjTranspose A = A := hA.isHermitian.eq
  have hs : psdSqrt (Matrix.conjTranspose A * A) = A := by
    rw [hherm]
    simpa [psdSqrt, sq] using (CFC.sqrt_sq A hA.nonneg)
  rw [hs]

private theorem cMatrix_trace_mul_le_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D X Y : CMatrix ι} (hD : D.PosSemidef) (hXY : X ≤ Y) :
    ((D * X).trace).re ≤ ((D * Y).trace).re := by
  rw [Matrix.le_iff] at hXY
  have hnonneg : 0 ≤ ((D * (Y - X)).trace).re := by
    let S := psdSqrt D
    have hpsd : (S * (Y - X) * S).PosSemidef := by
      have h := hXY.mul_mul_conjTranspose_same S
      rw [psdSqrt_isHermitian D] at h
      exact h
    have htrace_re : 0 ≤ ((S * (Y - X) * S).trace).re :=
      (Matrix.PosSemidef.trace_nonneg hpsd).1
    have hEq : (D * (Y - X)).trace = (S * (Y - X) * S).trace := by
      have hSsq : S * S = D := by
        simpa [S] using psdSqrt_mul_self_of_posSemidef hD
      rw [← hSsq]
      calc
        ((S * S) * (Y - X)).trace = (S * (S * (Y - X))).trace := by
          rw [Matrix.mul_assoc]
        _ = ((S * (Y - X)) * S).trace := by rw [Matrix.trace_mul_comm]
        _ = (S * (Y - X) * S).trace := by rw [Matrix.mul_assoc]
    rwa [hEq]
  have hcalc :
      ((D * (Y - X)).trace).re =
        ((D * Y).trace).re - ((D * X).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  linarith

private theorem trace_conjTranspose_mul_hermitian_re_eq
    {ι : Type*} [Fintype ι] {G D : CMatrix ι} (hD : D.IsHermitian) :
    ((Matrix.conjTranspose G * D).trace).re = ((G * D).trace).re := by
  have htrace :
      (Matrix.conjTranspose G * D).trace = star ((G * D).trace) := by
    calc
      (Matrix.conjTranspose G * D).trace =
          (D * Matrix.conjTranspose G).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (Matrix.conjTranspose (G * D)).trace := by
        rw [Matrix.conjTranspose_mul, hD.eq]
      _ = star ((G * D).trace) := Matrix.trace_conjTranspose _
  rw [htrace]
  simp

private theorem cMatrix_real_smul_le_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CMatrix ι} {c : ℝ} (hc : 0 ≤ c) (hAB : A ≤ B) :
    ((c : ℂ) • A) ≤ ((c : ℂ) • B) := by
  rw [Matrix.le_iff] at hAB ⊢
  simpa [sub_eq_add_neg, smul_add, smul_neg] using hAB.smul hc

/-- Fuchs--van de Graaf lower bound gives a trace-distance control on
purified distance. -/
theorem purifiedDistance_le_sqrt_two_mul_normalizedTraceDistance
    (ρ σ : State (Prod a b)) :
    ρ.purifiedDistance σ ≤
      Real.sqrt (2 * ρ.normalizedTraceDistance σ) := by
  have hF_nonneg : 0 ≤ ρ.fidelity σ := ρ.fidelity_nonneg σ
  have hF_sq_le : ρ.fidelity σ ^ 2 ≤ 1 := by
    simpa [State.squaredFidelity_eq_fidelity_sq] using
      ρ.squaredFidelity_le_one_of_uhlmann σ
  have hF_le_one : ρ.fidelity σ ≤ 1 := by
    nlinarith [hF_nonneg, hF_sq_le]
  have hD_nonneg : 0 ≤ ρ.normalizedTraceDistance σ :=
    State.normalizedTraceDistance_nonneg ρ σ
  have hlow : 1 - ρ.fidelity σ ≤ ρ.normalizedTraceDistance σ :=
    ρ.fuchs_van_de_graaf_lower σ
  have hprod :
      (1 - ρ.fidelity σ) * (1 + ρ.fidelity σ) ≤
        ρ.normalizedTraceDistance σ * 2 := by
    refine mul_le_mul hlow ?_ ?_ hD_nonneg
    · nlinarith [hF_le_one]
    · nlinarith [hF_nonneg]
  have hsf_le_one : ρ.squaredFidelity σ ≤ 1 :=
    ρ.squaredFidelity_le_one_of_uhlmann σ
  have harg_nonneg : 0 ≤ 1 - ρ.squaredFidelity σ := by
    linarith
  rw [State.purifiedDistance_eq]
  refine Real.le_sqrt_of_sq_le ?_
  rw [Real.sq_sqrt harg_nonneg]
  rw [State.squaredFidelity_eq_fidelity_sq]
  nlinarith [hprod]

/-- The trace norm is continuous on finite-dimensional complex matrices.

This local copy keeps the finite-AEP regularization path from importing the heavier
trace-norm continuity dependencies into the basic trace-distance API. -/
private theorem finiteAEPTraceNorm_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (traceNorm : CMatrix ι → ℝ) := by
  have hgram : Continuous (fun M : CMatrix ι => star M * M) := by
    exact (Continuous.star continuous_id).matrix_mul continuous_id
  have hnonneg : ∀ M : CMatrix ι, (star M * M) ∈ {A : CMatrix ι | 0 ≤ A} := by
    intro M
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self M)
  have hsqrtOn :
      ContinuousOn (CFC.sqrt : CMatrix ι → CMatrix ι) {A : CMatrix ι | 0 ≤ A} := by
    exact CFC.continuousOn_sqrt
  have hsqrt : Continuous (fun M : CMatrix ι => CFC.sqrt (star M * M)) := by
    exact hsqrtOn.comp_continuous hgram hnonneg
  have htrace : Continuous (fun M : CMatrix ι => (CFC.sqrt (star M * M)).trace) :=
    Continuous.matrix_trace hsqrt
  simpa [traceNorm, psdSqrt] using Complex.continuous_re.comp htrace

/-- Normalized trace distance from a fixed state is continuous. -/
private theorem finiteAEP_normalizedTraceDistance_continuous_left
    (σ : State (Prod a b)) :
    Continuous fun ρ : State (Prod a b) => ρ.normalizedTraceDistance σ := by
  rw [show (fun ρ : State (Prod a b) => ρ.normalizedTraceDistance σ) =
      fun ρ : State (Prod a b) =>
        (1 / 2 : ℝ) * traceNorm (ρ.matrix - σ.matrix) by
    funext ρ
    rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq,
      QIT.traceDistance]]
  exact continuous_const.mul
    (finiteAEPTraceNorm_continuous.comp (by fun_prop))

private theorem log2_card_left_nonneg (ρ : State (Prod a b)) :
    0 ≤ log2 (Fintype.card a : ℝ) := by
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have hcard_one : 1 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr inferInstance))
  exact div_nonneg (Real.log_nonneg hcard_one)
    (le_of_lt (Real.log_pos one_lt_two))

private theorem ConditionalMinEntropyFeasible_scale_lower_bound
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (Fintype.card a : ℝ)⁻¹ ≤ Real.rpow 2 (-lam) := by
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have htrace := fixedSmooth_trace_re_le_of_le h
  have hleft : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hright :
      (((Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ).trace).re =
        Real.rpow 2 (-lam) * (Fintype.card a : ℝ) := by
    rw [Matrix.trace_smul]
    simp [fixedSmooth_identityTensorStateMatrix_trace_re (a := a) σ]
  rw [hleft, hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  rw [inv_le_iff_one_le_mul₀ hcard_pos]
  simpa [mul_comm] using htrace

private theorem ConditionalMinEntropyFeasible_le_log2_card_left
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ log2 (Fintype.card a : ℝ) := by
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have hscale := ConditionalMinEntropyFeasible_scale_lower_bound (a := a) h
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hlog := Real.log_le_log (inv_pos.mpr hcard_pos) hscale
  have hlog2_nonneg : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos one_lt_two)
  have hdiv := div_le_div_of_nonneg_right hlog hlog2_nonneg
  change log2 ((Fintype.card a : ℝ)⁻¹) ≤
    log2 (Real.rpow 2 (-lam)) at hdiv
  have hneg := neg_le_neg hdiv
  have hcard :
      -log2 ((Fintype.card a : ℝ)⁻¹) = log2 (Fintype.card a : ℝ) := by
    unfold log2
    rw [Real.log_inv]
    ring
  rw [neg_log2_rpow_two_neg lam, hcard] at hneg
  exact hneg

private theorem conditionalMinEntropyFeasibleSet_bddAbove
    (ρ : State (Prod a b)) :
    BddAbove {lam : ℝ | ∃ τ : State b,
      ConditionalMinEntropyFeasible (a := a) ρ τ lam} := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro lam hlam
  rcases hlam with ⟨τ, hτ⟩
  exact ConditionalMinEntropyFeasible_le_log2_card_left (a := a) hτ

/-! ## Fixed-reference conditional min-entropy -/

/-- Conditional min-entropy with the conditioning state `σ_B` fixed.

This is the fixed-reference candidate
`sup {λ | ρ_AB ≤ 2^{-λ} (I_A ⊗ σ_B)}`.  Optimizing this quantity over `σ_B`
recovers the candidate set used by `State.conditionalMinEntropy`. -/
def conditionalMinEntropyFixed (ρ : State (Prod a b)) (σ : State b) : ℝ :=
  sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropyFixed_eq (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMinEntropyFixed σ =
      sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- A fixed-reference feasible exponent is an optimized feasible exponent, so
the fixed-reference min-entropy is bounded by the optimized min-entropy.

The nonemptiness hypothesis is necessary for this real-valued `sSup` API:
if the fixed `σ_B` has no feasible exponent, the mathematical value should be
`-∞`, while Lean's real `sSup ∅` is `0`. -/
theorem conditionalMinEntropyFixed_le_conditionalMinEntropy
    (ρ : State (Prod a b)) (σ : State b)
    (hfixed : ({lam : ℝ |
      ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty) :
    ρ.conditionalMinEntropyFixed σ ≤ ρ.conditionalMinEntropy := by
  rw [conditionalMinEntropyFixed_eq, conditionalMinEntropy_eq]
  refine csSup_le hfixed ?_
  intro lam hlam
  exact le_csSup (conditionalMinEntropyFeasibleSet_bddAbove (a := a) ρ)
    (show ∃ τ : State b, ConditionalMinEntropyFeasible (a := a) ρ τ lam from
      ⟨σ, hlam⟩)

/-- Fixed-reference conditional min-entropy is bounded above by the left-system
dimension. -/
theorem conditionalMinEntropyFixed_le_log2_card_left
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMinEntropyFixed σ ≤ log2 (Fintype.card a : ℝ) := by
  rw [conditionalMinEntropyFixed_eq]
  by_cases hne :
      ({lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      ConditionalMinEntropyFeasible_le_log2_card_left (a := a) hlam
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact log2_card_left_nonneg (a := a) ρ

private theorem conditionalMinEntropy_le_log2_card_left_of_fixedSmooth
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) := by
  rw [conditionalMinEntropy_eq]
  by_cases hne :
      ({lam : ℝ | ∃ τ : State b,
        ConditionalMinEntropyFeasible (a := a) ρ τ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      let ⟨_, hτ⟩ := hlam
      ConditionalMinEntropyFeasible_le_log2_card_left (a := a) hτ
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact log2_card_left_nonneg (a := a) ρ

theorem ConditionalMinEntropyFeasible_le_conditionalEntropy_of_posDef_reference
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalEntropy :=
  conditionalMinEntropyFeasible_le_conditionalEntropy_of_supportTraceLog_nonneg
    (ρ := ρ) (σ := σ) hσ hfeas
    (conditionalMinEntropyFeasible_supportTraceLog_residual_nonneg
      (ρ := ρ) (σ := σ) hσ hfeas)

private theorem ConditionalMinEntropyFeasible.exists_posDef_reference_below
    {ρ : State (Prod a b)} {σ : State b} {lam μ : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam)
    (hμ : μ < lam) :
    ∃ σ' : State b, σ'.matrix.PosDef ∧
      ConditionalMinEntropyFeasible (a := a) ρ σ' μ := by
  classical
  letI : Nonempty b := σ.nonempty
  let q : ℝ := Real.rpow 2 (μ - lam)
  let p : ℝ := 1 - q
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    linarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    linarith
  have hp_pos : 0 < p := by
    dsimp [p]
    linarith
  let m : State b := State.maximallyMixed b
  let σ' : State b := State.regularizedWithState σ m p hp0 hp1
  have hσ'pos : σ'.matrix.PosDef := by
    simpa [σ'] using
      State.regularizedWithState_posDef_of_noise σ m
        (State.maximallyMixed_posDef_of_nonempty (a := b)) hp0 hp1 hp_pos
  refine ⟨σ', hσ'pos, ?_⟩
  rw [ConditionalMinEntropyFeasible] at hfeas ⊢
  let cμ : ℝ := Real.rpow 2 (-μ)
  let cLam : ℝ := Real.rpow 2 (-lam)
  let Tσ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let Tm : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) m
  have hcμ_nonneg : 0 ≤ cμ := by
    dsimp [cμ]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-μ)
  have hp_nonneg : 0 ≤ p := hp0
  have hcoef :
      cμ * (1 - p) = cLam := by
    have hq_def : 1 - p = q := by
      dsimp [p]
      ring
    calc
      cμ * (1 - p) = cμ * q := by rw [hq_def]
      _ = Real.rpow 2 (-μ) * Real.rpow 2 (μ - lam) := rfl
      _ = Real.rpow 2 ((-μ) + (μ - lam)) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-μ) (μ - lam)).symm
      _ = cLam := by
        dsimp [cLam]
        ring_nf
  have hσ'_tensor :
      identityTensorStateMatrix (a := a) σ' =
        ((1 - p : ℝ) : ℂ) • Tσ + ((p : ℝ) : ℂ) • Tm := by
    ext x y
    simp [σ', State.regularizedWithState_matrix, State.regularizedStateMatrix,
      Tσ, Tm, identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Complex.real_smul]
    ring
  have hside :
      ((cμ : ℂ) • identityTensorStateMatrix (a := a) σ') =
        ((cLam : ℂ) • Tσ) + (((cμ * p : ℝ) : ℂ) • Tm) := by
    rw [hσ'_tensor, smul_add, smul_smul, smul_smul]
    have hcoefC : (cμ : ℂ) * ((1 - p : ℝ) : ℂ) = (cLam : ℂ) := by
      exact_mod_cast hcoef
    have hcoefCp : (cμ : ℂ) * ((p : ℝ) : ℂ) = ((cμ * p : ℝ) : ℂ) := by
      norm_num
    rw [hcoefC, hcoefCp]
  refine le_trans hfeas ?_
  rw [hside]
  exact le_add_of_nonneg_right (by
    have hscaleC : (0 : ℂ) ≤ ((cμ * p : ℝ) : ℂ) := by
      exact_mod_cast mul_nonneg hcμ_nonneg hp_nonneg
    simpa [Matrix.le_iff, Tm] using
      Matrix.PosSemidef.smul (identityTensorStateMatrix_posSemidef_of_state (a := a) m)
        hscaleC)

theorem ConditionalMinEntropyFeasible_le_conditionalEntropy
    (ρ : State (Prod a b)) (σ : State b) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalEntropy := by
  by_contra hnot
  have hlt : ρ.conditionalEntropy < lam := lt_of_not_ge hnot
  let μ : ℝ := (ρ.conditionalEntropy + lam) / 2
  have hμ_lam : μ < lam := by
    change (ρ.conditionalEntropy + lam) / 2 < lam
    linarith
  have hH_μ : ρ.conditionalEntropy < μ := by
    change ρ.conditionalEntropy < (ρ.conditionalEntropy + lam) / 2
    linarith
  rcases ConditionalMinEntropyFeasible.exists_posDef_reference_below
      (a := a) hfeas hμ_lam with ⟨σ', hσ', hfeas'⟩
  have hμ_le_H :
      μ ≤ ρ.conditionalEntropy :=
    ConditionalMinEntropyFeasible_le_conditionalEntropy_of_posDef_reference
      (ρ := ρ) (σ := σ') hσ' hfeas'
  linarith

theorem conditionalMinEntropy_le_conditionalEntropy
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy ≤ ρ.conditionalEntropy := by
  classical
  letI : Nonempty b := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [conditionalMinEntropy_eq]
  change sSup (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) ≤
    ρ.conditionalEntropy
  refine csSup_le (ρ.conditionalMinEntropyFeasibleExponentValueSet_nonempty (a := a)) ?_
  intro lam hlam
  rcases hlam with ⟨σ, hfeas⟩
  exact ConditionalMinEntropyFeasible_le_conditionalEntropy
    (ρ := ρ) (σ := σ) hfeas

/-! ## Fixed-reference smooth conditional min-entropy -/

/-- Candidate values for the fixed-reference smooth conditional min-entropy.

The nearby state is smoothed in purified distance, while the side-information
reference `σ_B` is kept fixed in the unsmoothed min-entropy of each witness. -/
def SmoothConditionalMinEntropyFixedCandidate
    (ρ : State (Prod a b)) (σ : State b) (ε h : ℝ) : Prop :=
  ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
    h = ρ'.conditionalMinEntropyFixed σ

@[simp]
theorem SmoothConditionalMinEntropyFixedCandidate_eq
    (ρ : State (Prod a b)) (σ : State b) (ε h : ℝ) :
    SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h ↔
      ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
        h = ρ'.conditionalMinEntropyFixed σ :=
  Iff.rfl

/-- Fixed-reference smooth min-entropy candidates are monotone in the smoothing
radius. -/
theorem SmoothConditionalMinEntropyFixedCandidate_mono
    {ρ : State (Prod a b)} {σ : State b} {ε δ h : ℝ} (hεδ : ε ≤ δ) :
    SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h →
      SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Fixed-reference smooth conditional min-entropy as the supremum of
fixed-reference min-entropies over the purified-distance epsilon ball. -/
def smoothConditionalMinEntropyFixed
    (ρ : State (Prod a b)) (σ : State b) (ε : ℝ) : ℝ :=
  sSup {h : ℝ | SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h}

theorem smoothConditionalMinEntropyFixed_eq_sSup_candidates
    (ρ : State (Prod a b)) (σ : State b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixed σ ε =
      sSup {h : ℝ |
        SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMinEntropyFixed_eq
    (ρ : State (Prod a b)) (σ : State b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixed σ ε =
      sSup {h : ℝ |
        ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMinEntropyFixed σ} :=
  rfl

/-- Fixed-reference smooth min-entropy candidates are bounded above by the
left-system dimension. -/
theorem SmoothConditionalMinEntropyFixedCandidate_bddAbove
    (ρ : State (Prod a b)) (σ : State b) (ε : ℝ) :
    BddAbove {h : ℝ |
      SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h} := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro h hh
  rcases hh with ⟨ρ', _hball, rfl⟩
  exact conditionalMinEntropyFixed_le_log2_card_left (a := a) ρ' σ

private theorem SmoothConditionalMinEntropyCandidate_bddAbove
    (ρ : State (Prod a b)) (ε : ℝ) :
    BddAbove {h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h} := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro h hh
  rcases hh with ⟨ρ', _hball, rfl⟩
  exact conditionalMinEntropy_le_log2_card_left_of_fixedSmooth (a := a) ρ'

/-- Fixed-reference smooth conditional min-entropy is monotone in the smoothing
radius. -/
theorem smoothConditionalMinEntropyFixed_mono
    {ρ : State (Prod a b)} {σ : State b} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≤
      ρ.smoothConditionalMinEntropyFixed σ δ := by
  rw [smoothConditionalMinEntropyFixed_eq_sSup_candidates,
    smoothConditionalMinEntropyFixed_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨ρ.conditionalMinEntropyFixed σ, ρ, State.purifiedBall_self_of_nonneg ρ hε, rfl⟩
  intro h hh
  exact le_csSup
    (SmoothConditionalMinEntropyFixedCandidate_bddAbove (a := a) ρ σ δ)
    (SmoothConditionalMinEntropyFixedCandidate_mono (a := a) (ρ := ρ)
      (σ := σ) hεδ hh)

/-- Fixed-reference smooth min-entropy is bounded by the existing optimized
smooth min-entropy. -/
theorem smoothConditionalMinEntropyFixed_le_smoothConditionalMinEntropy
    (ρ : State (Prod a b)) (σ : State b) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hfixed : ∀ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' →
      ({lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ' σ lam}).Nonempty) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≤ ρ.smoothConditionalMinEntropy ε := by
  rw [smoothConditionalMinEntropyFixed_eq_sSup_candidates,
    smoothConditionalMinEntropy_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨ρ.conditionalMinEntropyFixed σ, ρ, State.purifiedBall_self_of_nonneg ρ hε, rfl⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  exact le_trans
    (conditionalMinEntropyFixed_le_conditionalMinEntropy ρ' σ (hfixed ρ' hball))
    (le_csSup
      (SmoothConditionalMinEntropyCandidate_bddAbove (a := a) ρ ε)
      (show SmoothConditionalMinEntropyCandidate (a := a) ρ ε
        ρ'.conditionalMinEntropy from ⟨ρ', hball, rfl⟩))

end State

namespace SubnormalizedState

private theorem neg_log2_rpow_two_neg (lam : ℝ) :
    -log2 (Real.rpow 2 (-lam)) = lam := by
  unfold log2
  change -(Real.log ((2 : ℝ) ^ (-lam)) / Real.log 2) = lam
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lam)]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  field_simp [hlog2]

private theorem rpow_two_log2_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  apply Real.log_injOn_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    hx
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  unfold log2
  field_simp [ne_of_gt (Real.log_pos one_lt_two)]

private theorem cMatrix_posSemidef_le_trace_re_smul_one_forFixedSmooth
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : CMatrix ι}
    (hA : A.PosSemidef) :
    A ≤ (((A.trace.re : ℝ) : ℂ) • (1 : CMatrix ι)) := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup ι ℂ := hA.1.eigenvectorUnitary
  let D : CMatrix ι := Matrix.diagonal fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : A = (U : CMatrix ι) * D * star (U : CMatrix ι) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hA.1.spectral_theorem
  have heig_sum : ∑ i, hA.1.eigenvalues i = A.trace.re := by
    have htrace := congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
    simpa using htrace.symm
  have heig_le_trace : ∀ i, hA.1.eigenvalues i ≤ A.trace.re := by
    intro i
    have hnonneg (j : ι) : 0 ≤ hA.1.eigenvalues j := hA.eigenvalues_nonneg j
    calc
      hA.1.eigenvalues i
          ≤ hA.1.eigenvalues i +
              ∑ j ∈ Finset.univ.erase i, hA.1.eigenvalues j :=
            le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, hA.1.eigenvalues j := by
            rw [add_comm]
            exact Finset.sum_erase_add (s := Finset.univ)
              (f := fun j => hA.1.eigenvalues j) (Finset.mem_univ i)
      _ = A.trace.re := heig_sum
  let c : ℂ := ((A.trace.re : ℝ) : ℂ)
  have hsub :
      c • (1 : CMatrix ι) - A =
        (U : CMatrix ι) * (c • (1 : CMatrix ι) - D) * star (U : CMatrix ι) := by
    have hunit_scalar :
        (U : CMatrix ι) * (c • (1 : CMatrix ι)) * star (U : CMatrix ι) =
          c • (1 : CMatrix ι) := by
      have hunit : (U : CMatrix ι) * star (U : CMatrix ι) = 1 := by
        simp
      calc
        (U : CMatrix ι) * (c • (1 : CMatrix ι)) * star (U : CMatrix ι) =
            c • ((U : CMatrix ι) * (1 : CMatrix ι) * star (U : CMatrix ι)) := by
              simp
        _ = c • (1 : CMatrix ι) := by
              simp [hunit]
    calc
      c • (1 : CMatrix ι) - A =
          c • (1 : CMatrix ι) - (U : CMatrix ι) * D * star (U : CMatrix ι) := by
            rw [hdiag]
      _ = (U : CMatrix ι) * (c • (1 : CMatrix ι)) * star (U : CMatrix ι) -
          (U : CMatrix ι) * D * star (U : CMatrix ι) := by
            rw [hunit_scalar]
      _ = (U : CMatrix ι) * (c • (1 : CMatrix ι) - D) * star (U : CMatrix ι) := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
  have hdiag_sub :
      c • (1 : CMatrix ι) - D =
        Matrix.diagonal fun i => (((A.trace.re - hA.1.eigenvalues i : ℝ) : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D, c]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix ι))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast sub_nonneg.mpr (heig_le_trace i)

private theorem trace_re_le_of_le {ι : Type*} [Fintype ι] {X Y : CMatrix ι}
    (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have hnon : 0 ≤ (Y - X).trace.re := (Matrix.PosSemidef.trace_nonneg hXY).1
  have htrace : (Y - X).trace.re = Y.trace.re - X.trace.re := by
    simp [Matrix.trace_sub]
  linarith

private theorem identityTensorStateMatrix_trace_re_le_card
    (σ : SubnormalizedState b) :
    (identityTensorStateMatrix (a := a) σ).trace.re ≤ (Fintype.card a : ℝ) := by
  change (Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) σ.matrix).trace.re ≤
    (Fintype.card a : ℝ)
  rw [Matrix.trace_kronecker, Matrix.trace_one]
  rw [Complex.mul_re, σ.trace_im_zero]
  simp
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by positivity
  exact mul_le_of_le_one_right hcard_nonneg σ.trace_le_one

private theorem ConditionalMinEntropyFeasible_scale_lower_bound_of_trace_lower
    [Nonempty a]
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b}
    {lam δ : ℝ}
    (_hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re)
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    δ / (Fintype.card a : ℝ) ≤ Real.rpow 2 (-lam) := by
  have htrace := trace_re_le_of_le h
  have hright_le :
      (((Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ).trace).re ≤
        Real.rpow 2 (-lam) * (Fintype.card a : ℝ) := by
    rw [Matrix.trace_smul]
    simp
    exact mul_le_mul_of_nonneg_left
      (identityTensorStateMatrix_trace_re_le_card (a := a) σ)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hδ_le : δ ≤ Real.rpow 2 (-lam) * (Fintype.card a : ℝ) :=
    le_trans hδρ (le_trans htrace hright_le)
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  exact (div_le_iff₀ hcard_pos).mpr hδ_le

/-- Every subnormalized finite-dimensional state is bounded above by the
identity operator. -/
theorem matrix_le_one_forFixedSmooth (ρ : SubnormalizedState a) :
    ρ.matrix ≤ 1 := by
  have htrace :
      ρ.matrix ≤ (((ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) :=
    cMatrix_posSemidef_le_trace_re_smul_one_forFixedSmooth ρ.pos
  have htrace_le_one :
      (((ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) ≤ 1 := by
    rw [Matrix.le_iff]
    have hdiff :
        (1 : CMatrix a) - (((ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) =
          (((1 - ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [hdiff]
    have hscalar : (0 : ℂ) ≤ (((1 - ρ.matrix.trace.re : ℝ) : ℝ) : ℂ) := by
      exact_mod_cast sub_nonneg.mpr ρ.trace_le_one
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one hscalar
  exact le_trans htrace htrace_le_one

private theorem exists_pos_scalar_smul_one_le_matrix_of_posDef_forFixedSmooth
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : CMatrix b) ≤ σ.matrix := by
  classical
  haveI : Nonempty b := σ.nonempty
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun i : b => hσ.1.eigenvalues i)
  have hc_pos : 0 < c := by
    dsimp [c]
    rw [Finset.lt_inf'_iff]
    intro i _hi
    exact hσ.eigenvalues_pos i
  have hc_le_eig : ∀ i : b, c ≤ hσ.1.eigenvalues i := by
    intro i
    exact Finset.inf'_le (f := fun i : b => hσ.1.eigenvalues i) (Finset.mem_univ i)
  refine ⟨c, hc_pos, ?_⟩
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup b ℂ := hσ.1.eigenvectorUnitary
  let D : CMatrix b := Matrix.diagonal fun i => ((hσ.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : σ.matrix = (U : CMatrix b) * D * star (U : CMatrix b) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hσ.1.spectral_theorem
  have hUstar : (U : CMatrix b) * star (U : CMatrix b) = 1 := by
    simp
  have hscalar :
      (U : CMatrix b) * (c • (1 : CMatrix b)) * star (U : CMatrix b) =
        c • (1 : CMatrix b) := by
    calc
      (U : CMatrix b) * (c • (1 : CMatrix b)) * star (U : CMatrix b) =
          c • ((U : CMatrix b) * (1 : CMatrix b) * star (U : CMatrix b)) := by
            simp
      _ = c • (1 : CMatrix b) := by
            rw [Matrix.mul_one, hUstar]
  have hsub :
      σ.matrix - c • (1 : CMatrix b) =
        (U : CMatrix b) * (D - c • (1 : CMatrix b)) * star (U : CMatrix b) := by
    calc
      σ.matrix - c • (1 : CMatrix b) =
          (U : CMatrix b) * D * star (U : CMatrix b) -
            (U : CMatrix b) * (c • (1 : CMatrix b)) * star (U : CMatrix b) := by
            rw [hdiag, hscalar]
      _ = (U : CMatrix b) * (D - c • (1 : CMatrix b)) * star (U : CMatrix b) := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
  have hdiag_sub :
      D - c • (1 : CMatrix b) =
        Matrix.diagonal fun i => (((hσ.1.eigenvalues i : ℝ) - c : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix b))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast sub_nonneg.mpr (hc_le_eig i)

private theorem one_le_inv_smul_identityTensorStateMatrix_toSubnormalized_of_posDef
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ∃ c : ℝ, 0 < c ∧
      (1 : CMatrix (Prod a b)) ≤
        ((c⁻¹ : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized := by
  rcases exists_pos_scalar_smul_one_le_matrix_of_posDef_forFixedSmooth σ hσ
    with ⟨c, hc_pos, hc_le⟩
  refine ⟨c, hc_pos, ?_⟩
  have hdiffB : (σ.matrix - c • (1 : CMatrix b)).PosSemidef := by
    simpa [Matrix.le_iff] using hc_le
  rw [Matrix.le_iff]
  have hdiff :
      ((c⁻¹ : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized -
          (1 : CMatrix (Prod a b)) =
        ((c⁻¹ : ℝ) : ℂ) •
          Matrix.kronecker (1 : CMatrix a) (σ.matrix - c • (1 : CMatrix b)) := by
    ext x y
    rcases x with ⟨xa, xb⟩
    rcases y with ⟨ya, yb⟩
    by_cases hA : xa = ya
    · subst ya
      by_cases hB : xb = yb
      · subst yb
        simp [SubnormalizedState.identityTensorStateMatrix, identityTensorStateMatrix,
          Matrix.kronecker, Matrix.kroneckerMap_apply]
        field_simp [ne_of_gt hc_pos]
      · simp [SubnormalizedState.identityTensorStateMatrix, identityTensorStateMatrix,
          Matrix.kronecker, Matrix.kroneckerMap_apply, hB]
    · simp [SubnormalizedState.identityTensorStateMatrix, identityTensorStateMatrix,
        Matrix.kronecker, Matrix.kroneckerMap_apply, hA]
  rw [hdiff]
  exact Matrix.PosSemidef.smul
    (Matrix.PosSemidef.one.kronecker hdiffB)
    (by exact_mod_cast inv_nonneg.mpr hc_pos.le)

/-- A positive-definite fixed normalized side reference makes every
subnormalized joint witness feasible for some fixed-reference min-entropy
exponent. -/
theorem conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
    (ρ : SubnormalizedState (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) :
    ({lam : ℝ |
      ConditionalMinEntropyFeasible (a := a) ρ σ.toSubnormalized lam}).Nonempty := by
  rcases one_le_inv_smul_identityTensorStateMatrix_toSubnormalized_of_posDef
      (a := a) σ hσ with ⟨c, hc_pos, hone_le⟩
  let lam : ℝ := -log2 c⁻¹
  refine ⟨lam, ?_⟩
  have hρ_le :
      ρ.matrix ≤
        ((c⁻¹ : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized :=
    le_trans ρ.matrix_le_one_forFixedSmooth hone_le
  have hrpow : Real.rpow 2 (-lam) = c⁻¹ := by
    dsimp [lam]
    rw [neg_neg]
    exact rpow_two_log2_pos (inv_pos.mpr hc_pos)
  change ρ.matrix ≤
    ((Real.rpow 2 (-lam) : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized
  rw [hrpow]
  exact hρ_le

private theorem ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
    [Nonempty a]
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b}
    {lam δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re)
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ log2 (Fintype.card a : ℝ) - log2 δ := by
  have hscale :=
    ConditionalMinEntropyFeasible_scale_lower_bound_of_trace_lower
      (a := a) hδ hδρ h
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hδ_div_pos : 0 < δ / (Fintype.card a : ℝ) :=
    div_pos hδ hcard_pos
  have hlog := Real.log_le_log hδ_div_pos hscale
  have hdiv := div_le_div_of_nonneg_right hlog
    (le_of_lt (Real.log_pos one_lt_two))
  change log2 (δ / (Fintype.card a : ℝ)) ≤
    log2 (Real.rpow 2 (-lam)) at hdiv
  have hneg := neg_le_neg hdiv
  have hleft :
      -log2 (δ / (Fintype.card a : ℝ)) =
        log2 (Fintype.card a : ℝ) - log2 δ := by
    unfold log2
    rw [Real.log_div hδ.ne' hcard_pos.ne']
    ring
  rw [neg_log2_rpow_two_neg lam, hleft] at hneg
  exact hneg

/-! ## Subnormalized fixed-reference conditional min-entropy -/

/-- Subnormalized conditional min-entropy with the conditioning state fixed.

Both the joint witness and the side reference are subnormalized, matching the
subnormalized `ConditionalMinEntropyFeasible` API in `Smooth.lean`. -/
def conditionalMinEntropyFixed
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) : ℝ :=
  sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropyFixed_eq
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    ρ.conditionalMinEntropyFixed σ =
      sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- Fixed-reference subnormalized min-entropy candidates are bounded above
when the joint state has a positive trace lower bound. -/
theorem conditionalMinEntropyFixed_feasibleSet_bddAbove_of_trace_lower
    [Nonempty a]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b)
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    BddAbove {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam} := by
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro lam hlam
  exact ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
    (a := a) hδ hδρ hlam

/-- Fixed-reference subnormalized min-entropy is bounded above when the joint
state has a positive trace lower bound. -/
theorem conditionalMinEntropyFixed_le_of_trace_lower_bound
    [Nonempty a]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b)
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re)
    (hδ_le_one : δ ≤ 1) :
    ρ.conditionalMinEntropyFixed σ ≤ log2 (Fintype.card a : ℝ) - log2 δ := by
  rw [conditionalMinEntropyFixed_eq]
  by_cases hne :
      ({lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
        (a := a) hδ hδρ hlam
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    have hcard_one : 1 ≤ (Fintype.card a : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr inferInstance))
    have hlog_card_nonneg : 0 ≤ log2 (Fintype.card a : ℝ) := by
      exact div_nonneg (Real.log_nonneg hcard_one)
        (le_of_lt (Real.log_pos one_lt_two))
    have hlogδ_nonpos : log2 δ ≤ 0 := by
      unfold log2
      have hlogδ : Real.log δ ≤ Real.log 1 := Real.log_le_log hδ hδ_le_one
      rw [Real.log_one] at hlogδ
      exact div_nonpos_of_nonpos_of_nonneg hlogδ
        (le_of_lt (Real.log_pos one_lt_two))
    linarith

/-- Optimized subnormalized min-entropy feasible exponents are bounded above
when the joint state has a positive trace lower bound. -/
theorem conditionalMinEntropy_feasibleSet_bddAbove_of_trace_lower
    [Nonempty a]
    (ρ : SubnormalizedState (Prod a b))
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    BddAbove {lam : ℝ | ∃ σ : SubnormalizedState b,
      ConditionalMinEntropyFeasible (a := a) ρ σ lam} := by
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
    (a := a) hδ hδρ hσ

/-- Fixed-reference subnormalized min-entropy is bounded by the optimized
subnormalized min-entropy, provided the fixed feasible set is nonempty.

The nonempty hypothesis mirrors the normalized fixed-reference API and avoids
assigning artificial finite content to zero-support corner cases. -/
theorem conditionalMinEntropyFixed_le_conditionalMinEntropy
    [Nonempty a]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b)
    (hfixed : ({lam : ℝ |
      ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty)
    (hρtr : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMinEntropyFixed σ ≤ ρ.conditionalMinEntropy := by
  rw [conditionalMinEntropyFixed_eq, conditionalMinEntropy_eq]
  refine csSup_le hfixed ?_
  intro lam hlam
  exact le_csSup
    (conditionalMinEntropy_feasibleSet_bddAbove_of_trace_lower
      (a := a) ρ hρtr le_rfl)
    (show ∃ τ : SubnormalizedState b,
      ConditionalMinEntropyFeasible (a := a) ρ τ lam from ⟨σ, hlam⟩)

/-- Any feasible fixed-reference exponent lower-bounds the subnormalized
fixed-reference conditional min-entropy, provided the witness has positive
trace.  The trace hypothesis is the real-valued `sSup` replacement for the
usual extended-real `-∞` zero-trace corner. -/
theorem le_conditionalMinEntropyFixed_of_feasible
    [Nonempty a]
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ}
    (hρtr : 0 < ρ.matrix.trace.re)
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalMinEntropyFixed σ := by
  rw [conditionalMinEntropyFixed_eq]
  exact le_csSup
    (conditionalMinEntropyFixed_feasibleSet_bddAbove_of_trace_lower
      (a := a) ρ σ hρtr le_rfl)
    hfeas

end SubnormalizedState

namespace State

/-! ## Fixed-reference smooth min-entropy with subnormalized witnesses -/

/-- Candidate values for fixed-reference smooth conditional min-entropy around
a normalized center, allowing subnormalized witnesses in the purified ball. -/
def SmoothConditionalMinEntropyFixedSubnormalizedCandidate
    (ρ : State (Prod a b)) (σ : SubnormalizedState b) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (Prod a b),
    ρ.toSubnormalized.purifiedBall ε ρ' ∧
      h = ρ'.conditionalMinEntropyFixed σ

@[simp]
theorem SmoothConditionalMinEntropyFixedSubnormalizedCandidate_eq
    (ρ : State (Prod a b)) (σ : SubnormalizedState b) (ε h : ℝ) :
    SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h ↔
      ∃ ρ' : SubnormalizedState (Prod a b),
        ρ.toSubnormalized.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMinEntropyFixed σ :=
  Iff.rfl

/-- Fixed-reference smooth conditional min-entropy with subnormalized witnesses
and a fixed subnormalized side reference. -/
def smoothConditionalMinEntropyFixedSubnormalized
    (ρ : State (Prod a b)) (σ : SubnormalizedState b) (ε : ℝ) : ℝ :=
  sSup {h : ℝ |
    SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h}

theorem smoothConditionalMinEntropyFixedSubnormalized_eq_sSup_candidates
    (ρ : State (Prod a b)) (σ : SubnormalizedState b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε =
      sSup {h : ℝ |
        SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMinEntropyFixedSubnormalized_eq
    (ρ : State (Prod a b)) (σ : SubnormalizedState b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε =
      sSup {h : ℝ |
        ∃ ρ' : SubnormalizedState (Prod a b),
          ρ.toSubnormalized.purifiedBall ε ρ' ∧
            h = ρ'.conditionalMinEntropyFixed σ} :=
  rfl

/-- Subnormalized fixed-reference smooth-min candidates around a normalized
center are bounded above for radii below one. -/
theorem SmoothConditionalMinEntropyFixedSubnormalizedCandidate_bddAbove
    (ρ : State (Prod a b)) (σ : SubnormalizedState b) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) :
    BddAbove {h : ℝ |
      SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h} := by
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  let δ : ℝ := (1 - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε_lt)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    nlinarith
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    have hcenter_trace : ρ.matrix.trace.re = 1 := by
      rw [ρ.trace_eq_one]
      norm_num
    simpa [δ, hcenter_trace] using
      ρ.toSubnormalized.purifiedBall_trace_lower_bound ρ' hε_sqrt hball
  exact SubnormalizedState.conditionalMinEntropyFixed_le_of_trace_lower_bound
    (a := a) ρ' σ hδ hδρ' hδ_le_one

/-- Subnormalized smooth min-entropy candidates around a normalized center are
bounded above for radii below one. -/
theorem SubnormalizedState.SmoothConditionalMinEntropyCandidate_bddAbove_of_state_center
    (ρ : State (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) :
    BddAbove {h : ℝ |
      SubnormalizedState.SmoothConditionalMinEntropyCandidate (a := a)
        ρ.toSubnormalized ε h} := by
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  let δ : ℝ := (1 - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε_lt)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    nlinarith
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    have hcenter_trace : ρ.matrix.trace.re = 1 := by
      rw [ρ.trace_eq_one]
      norm_num
    simpa [δ, hcenter_trace] using
      ρ.toSubnormalized.purifiedBall_trace_lower_bound ρ' hε_sqrt hball
  rw [SubnormalizedState.conditionalMinEntropy_eq]
  by_cases hne :
      ({lam : ℝ | ∃ σ : SubnormalizedState b,
        SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      SubnormalizedState.ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
        (a := a) hδ hδρ' hlam.choose_spec
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    have hcard_one : 1 ≤ (Fintype.card a : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr inferInstance))
    have hlog_card_nonneg : 0 ≤ log2 (Fintype.card a : ℝ) := by
      exact div_nonneg (Real.log_nonneg hcard_one)
        (le_of_lt (Real.log_pos one_lt_two))
    have hlogδ_nonpos : log2 δ ≤ 0 := by
      unfold log2
      have hlogδ : Real.log δ ≤ Real.log 1 := Real.log_le_log hδ hδ_le_one
      rw [Real.log_one] at hlogδ
      exact div_nonpos_of_nonpos_of_nonneg hlogδ
        (le_of_lt (Real.log_pos one_lt_two))
    linarith

/-- Moving a normalized center only increases the smoothing radius needed for
subnormalized smooth min-entropy.  This is the `sSup`-level form of
`SubnormalizedState.SmoothConditionalMinEntropyCandidate_center_migration`. -/
theorem subnormalizedSmoothConditionalMinEntropy_center_migration
    (ρ η : State (Prod a b)) {ε δ : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter : η.toSubnormalized.purifiedDistance ρ.toSubnormalized ≤ δ) :
    η.toSubnormalized.smoothConditionalMinEntropy ε ≤
      ρ.toSubnormalized.smoothConditionalMinEntropy (ε + δ) := by
  rw [SubnormalizedState.smoothConditionalMinEntropy_eq_sSup_candidates,
    SubnormalizedState.smoothConditionalMinEntropy_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨η.toSubnormalized.conditionalMinEntropy, η.toSubnormalized,
      SubnormalizedState.purifiedBall_self_of_nonneg η.toSubnormalized hε_nonneg, rfl⟩
  intro h hh
  exact le_csSup
    (SubnormalizedState.SmoothConditionalMinEntropyCandidate_bddAbove_of_state_center
      (a := a) ρ hεδ_nonneg hεδ_lt)
    (SubnormalizedState.SmoothConditionalMinEntropyCandidate_center_migration
      (a := a) hcenter hh)

/-- Tensor-power spelling of center migration for the public smooth-min
quantity used in the finite-AEP statement. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropy_center_migration
    (ρ η : State (Prod a b)) (n : ℕ) {ε δ : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter :
      (η.tensorPowerBipartite n).toSubnormalized.purifiedDistance
        (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ) :
    η.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n ≤
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy (ε + δ) n := by
  simpa [State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq] using
    subnormalizedSmoothConditionalMinEntropy_center_migration
      (a := TensorPower a n) (b := TensorPower b n)
      (ρ := ρ.tensorPowerBipartite n) (η := η.tensorPowerBipartite n)
      hε_nonneg hεδ_nonneg hεδ_lt hcenter

/-- Transfer a tensor-power smooth-min lower bound across nearby centers by
paying the purified-distance gap in the smoothing radius. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropy_lower_bound_of_center_migration
    (ρ η : State (Prod a b)) (n : ℕ) {ε δ L : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter :
      (η.tensorPowerBipartite n).toSubnormalized.purifiedDistance
        (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ)
    (hlower :
      L ≤ η.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n) :
    L ≤ ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy (ε + δ) n := by
  exact le_trans hlower
    (tensorPowerSubnormalizedSmoothConditionalMinEntropy_center_migration
      (ρ := ρ) (η := η) (n := n)
      hε_nonneg hεδ_nonneg hεδ_lt hcenter)

/-- Fixed-reference subnormalized smooth min-entropy is bounded by the
optimized subnormalized smooth min-entropy around the embedded normalized
center.

The fixed-reference nonempty hypothesis is local to each subnormalized witness,
matching the unsmoothed comparison. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
    (ρ : State (Prod a b)) (σ : SubnormalizedState b) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1)
    (hfixed : ∀ ρ' : SubnormalizedState (Prod a b),
      ρ.toSubnormalized.purifiedBall ε ρ' →
        ({lam : ℝ |
          SubnormalizedState.ConditionalMinEntropyFeasible (a := a)
            ρ' σ lam}).Nonempty) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε ≤
      ρ.toSubnormalized.smoothConditionalMinEntropy ε := by
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  rw [smoothConditionalMinEntropyFixedSubnormalized_eq_sSup_candidates,
    SubnormalizedState.smoothConditionalMinEntropy_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨ρ.toSubnormalized.conditionalMinEntropyFixed σ,
      ρ.toSubnormalized, SubnormalizedState.purifiedBall_self_of_nonneg
        ρ.toSubnormalized hε_nonneg, rfl⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hρ'tr : 0 < ρ'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ.toSubnormalized ρ' hε_sqrt hball
  exact le_trans
    (SubnormalizedState.conditionalMinEntropyFixed_le_conditionalMinEntropy
      (a := a) ρ' σ (hfixed ρ' hball) hρ'tr)
    (le_csSup
      (SubnormalizedState.SmoothConditionalMinEntropyCandidate_bddAbove_of_state_center
        (a := a) ρ hε_nonneg hε_lt)
      (show SubnormalizedState.SmoothConditionalMinEntropyCandidate (a := a)
          ρ.toSubnormalized ε ρ'.conditionalMinEntropy from
        ⟨ρ', hball, rfl⟩))

/-- A subnormalized purified-ball witness with a fixed-reference feasible
exponent gives a lower bound on normalized-center, subnormalized-witness smooth
min-entropy. -/
theorem le_smoothConditionalMinEntropyFixedSubnormalized_of_feasible_witness
    {ρ : State (Prod a b)} {ρ' : SubnormalizedState (Prod a b)}
    {σ : SubnormalizedState b} {ε lam lower : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1)
    (hball : ρ.toSubnormalized.purifiedBall ε ρ')
    (hfeas : SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ lam)
    (hlower : lower ≤ lam) :
    lower ≤ ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε := by
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hρ'tr : 0 < ρ'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ.toSubnormalized ρ' hε_sqrt hball
  have hmin : lam ≤ ρ'.conditionalMinEntropyFixed σ :=
    SubnormalizedState.le_conditionalMinEntropyFixed_of_feasible
      (a := a) hρ'tr hfeas
  have hsmooth :
      ρ'.conditionalMinEntropyFixed σ ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε := by
    rw [smoothConditionalMinEntropyFixedSubnormalized_eq_sSup_candidates]
    exact le_csSup
      (SmoothConditionalMinEntropyFixedSubnormalizedCandidate_bddAbove
        (a := a) ρ σ hε_nonneg hε_lt)
      (show SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε
        (ρ'.conditionalMinEntropyFixed σ) from ⟨ρ', hball, rfl⟩)
  exact le_trans hlower (le_trans hmin hsmooth)

/-! ## Fixed-reference feasible witnesses -/

/-- Fixed-reference Petz threshold exponent used in the TCR smooth-min lower
bound. -/
def petzSmoothMinThresholdExponent
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one -
    (1 / (α - 1)) * log2 (2 / ε ^ 2)

/-- Fixed-reference Petz threshold scale, i.e. the right-hand scalar
`2^{-λ}` for `petzSmoothMinThresholdExponent`. -/
def petzSmoothMinThresholdScale
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  Real.rpow 2
    (-(ρ.petzSmoothMinThresholdExponent hρ σ hσ ε α hα_pos hα_ne_one))

/-- Fixed-reference Petz threshold exponent for an arbitrary left state and a
full-rank reference side. This is the source-domain version of
`petzSmoothMinThresholdExponent`: only the reference matrix carries a
positive-definiteness witness. -/
def petzSmoothMinThresholdExponentFullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one -
    (1 / (α - 1)) * log2 (2 / ε ^ 2)

/-- Full-reference Petz threshold scale for arbitrary left states. -/
def petzSmoothMinThresholdScaleFullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  Real.rpow 2
    (-(ρ.petzSmoothMinThresholdExponentFullReference σ hσ ε α hα_pos hα_ne_one))

theorem petzSmoothMinThresholdScale_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    0 < ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one := by
  unfold petzSmoothMinThresholdScale
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

theorem petzSmoothMinThresholdScaleFullReference_pos
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    0 < ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one := by
  unfold petzSmoothMinThresholdScaleFullReference
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

theorem petzSmoothMinThresholdExponentFullReference_eq_neg_log2_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.petzSmoothMinThresholdExponentFullReference σ hσ ε α hα_pos hα_ne_one =
      -log2 (ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α
        hα_pos hα_ne_one) := by
  simpa [petzSmoothMinThresholdScaleFullReference] using
    (neg_log2_rpow_two_neg
      (ρ.petzSmoothMinThresholdExponentFullReference σ hσ ε α hα_pos hα_ne_one)).symm

theorem petzSmoothMinThresholdScale_eq_entropyPenalty
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one =
      Real.rpow 2
          (-(ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
            hα_pos hα_ne_one)) *
        (2 / ε ^ 2) ^ (1 / (α - 1)) := by
  have hx : 0 < 2 / ε ^ 2 := by
    exact div_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hε_pos)
  simpa [petzSmoothMinThresholdScale, petzSmoothMinThresholdExponent] using
    (rpow_two_neg_sub_mul_log2_pos
      (H := ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one)
      (gamma := 1 / (α - 1)) (x := 2 / ε ^ 2) hx)

theorem petzSmoothMinThresholdScale_rpow_one_sub_alpha_mul_traceTerm_eq
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε) (hα_gt : 1 < α) :
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ^ (1 - α) *
      ρ.conditionalPetzRenyiTraceTerm σ α =
        ε ^ 2 / 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let H : ℝ := ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one
  let T : ℝ := ρ.conditionalPetzRenyiTraceTerm σ α
  let x : ℝ := 2 / ε ^ 2
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hx_pos : 0 < x := by
    exact div_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hε_pos)
  have hT_pos : 0 < T := by
    simpa [T] using
      conditionalPetzRenyiTraceTerm_pos_of_posDef (ρ := ρ) hρ (σ := σ) hσ α
  have hT :
      Real.rpow 2 ((1 - α) * H) = T := by
    simpa [H, T, hα_pos, hα_ne_one] using
      rpow_two_one_sub_alpha_mul_conditionalPetzRenyiEntropyCandidate
        (ρ := ρ) hρ (σ := σ) hσ α hα_pos hα_ne_one
  have hlam_def :
      lam = Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x)) := by
    simp [lam, petzSmoothMinThresholdScale, petzSmoothMinThresholdExponent,
      H, x]
  have hpow_lam :
      lam ^ (1 - α) =
        Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x) * (1 - α)) := by
    rw [hlam_def]
    exact (Real.rpow_mul (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
      (-(H - (1 / (α - 1)) * log2 x)) (1 - α)).symm
  have hexp :
      -(H - (1 / (α - 1)) * log2 x) * (1 - α) =
        (α - 1) * H + -log2 x := by
    have hden : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne_one
    field_simp [hden]
    ring
  have hH_inv :
      Real.rpow 2 ((α - 1) * H) = T⁻¹ := by
    have hrewrite : (α - 1) * H = -((1 - α) * H) := by ring
    calc
      Real.rpow 2 ((α - 1) * H) =
          Real.rpow 2 (-((1 - α) * H)) := by rw [hrewrite]
      _ = (Real.rpow 2 ((1 - α) * H))⁻¹ := by
          exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((1 - α) * H)
      _ = T⁻¹ := by rw [hT]
  have hx_inv : Real.rpow 2 (-log2 x) = x⁻¹ := by
    calc
      Real.rpow 2 (-log2 x) =
          (Real.rpow 2 (log2 x))⁻¹ := by
        exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (log2 x)
      _ = x⁻¹ := by rw [rpow_two_log2_pos hx_pos]
  have hmain : lam ^ (1 - α) * T = x⁻¹ := by
    calc
      lam ^ (1 - α) * T =
          Real.rpow 2 ((α - 1) * H + -log2 x) * T := by
        rw [hpow_lam, hexp]
      _ =
          (Real.rpow 2 ((α - 1) * H) * Real.rpow 2 (-log2 x)) * T := by
        exact congrArg (fun y : ℝ => y * T)
          (Real.rpow_add (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
            ((α - 1) * H) (-log2 x))
      _ = (T⁻¹ * x⁻¹) * T := by rw [hH_inv, hx_inv]
      _ = x⁻¹ := by
        field_simp [ne_of_gt hT_pos]
  have hx_inv_eq : x⁻¹ = ε ^ 2 / 2 := by
    dsimp [x]
    field_simp [pow_ne_zero 2 (ne_of_gt hε_pos)]
  simpa [lam, T, hα_pos, hα_ne_one] using hmain.trans hx_inv_eq

theorem petzSmoothMinThresholdScaleFullReference_rpow_one_sub_alpha_mul_traceTerm_eq
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε) (hα_gt : 1 < α) :
    ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ^ (1 - α) *
      ρ.conditionalPetzRenyiTraceTerm σ α =
        ε ^ 2 / 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let H : ℝ :=
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one
  let T : ℝ := ρ.conditionalPetzRenyiTraceTerm σ α
  let x : ℝ := 2 / ε ^ 2
  let lam : ℝ := ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one
  have hx_pos : 0 < x := by
    exact div_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hε_pos)
  have hT_pos : 0 < T := by
    simpa [T] using
      conditionalPetzRenyiTraceTerm_pos_of_fullReference (ρ := ρ) (σ := σ) hσ α
  have hT :
      Real.rpow 2 ((1 - α) * H) = T := by
    dsimp [H, conditionalPetzRenyiEntropyCandidateFullReference]
    have hden : 1 - α ≠ 0 := sub_ne_zero.mpr hα_ne_one.symm
    rw [show (1 - α) * ((1 / (1 - α)) * log2 T) = log2 T by
      field_simp [hden]]
    exact rpow_two_log2_pos hT_pos
  have hlam_def :
      lam = Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x)) := by
    simp [lam, petzSmoothMinThresholdScaleFullReference,
      petzSmoothMinThresholdExponentFullReference, H, x]
  have hpow_lam :
      lam ^ (1 - α) =
        Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x) * (1 - α)) := by
    rw [hlam_def]
    exact (Real.rpow_mul (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
      (-(H - (1 / (α - 1)) * log2 x)) (1 - α)).symm
  have hexp :
      -(H - (1 / (α - 1)) * log2 x) * (1 - α) =
        (α - 1) * H + -log2 x := by
    have hden : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne_one
    field_simp [hden]
    ring
  have hH_inv :
      Real.rpow 2 ((α - 1) * H) = T⁻¹ := by
    have hrewrite : (α - 1) * H = -((1 - α) * H) := by ring
    calc
      Real.rpow 2 ((α - 1) * H) =
          Real.rpow 2 (-((1 - α) * H)) := by rw [hrewrite]
      _ = (Real.rpow 2 ((1 - α) * H))⁻¹ := by
          exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((1 - α) * H)
      _ = T⁻¹ := by rw [hT]
  have hx_inv : Real.rpow 2 (-log2 x) = x⁻¹ := by
    calc
      Real.rpow 2 (-log2 x) =
          (Real.rpow 2 (log2 x))⁻¹ := by
        exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (log2 x)
      _ = x⁻¹ := by rw [rpow_two_log2_pos hx_pos]
  have hmain : lam ^ (1 - α) * T = x⁻¹ := by
    calc
      lam ^ (1 - α) * T =
          Real.rpow 2 ((α - 1) * H + -log2 x) * T := by
        rw [hpow_lam, hexp]
      _ =
          (Real.rpow 2 ((α - 1) * H) * Real.rpow 2 (-log2 x)) * T := by
        exact congrArg (fun y : ℝ => y * T)
          (Real.rpow_add (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
            ((α - 1) * H) (-log2 x))
      _ = (T⁻¹ * x⁻¹) * T := by rw [hH_inv, hx_inv]
      _ = x⁻¹ := by
        field_simp [ne_of_gt hT_pos]
  have hx_inv_eq : x⁻¹ = ε ^ 2 / 2 := by
    dsimp [x]
    field_simp [pow_ne_zero 2 (ne_of_gt hε_pos)]
  simpa [lam, T, hα_pos, hα_ne_one] using hmain.trans hx_inv_eq

theorem SubnormalizedState.ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
    {ρ' : SubnormalizedState (Prod a b)}
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ.toSubnormalized
      (ρ.petzSmoothMinThresholdExponent hρ σ hσ ε α hα_pos hα_ne_one) := by
  simpa [SubnormalizedState.ConditionalMinEntropyFeasible,
    petzSmoothMinThresholdScale, State.toSubnormalized_identityTensorStateMatrix_eq] using hbound

theorem SubnormalizedState.ConditionalMinEntropyFeasible.of_le_positive_scale
    {ρ' : SubnormalizedState (Prod a b)}
    (σ : State b) {lambda : ℝ} (hlambda : 0 < lambda)
    (hbound :
      ρ'.matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ.toSubnormalized
      (-log2 lambda) := by
  have hscale : Real.rpow 2 (-(-log2 lambda)) = lambda := by
    simpa using rpow_two_log2_pos hlambda
  rw [SubnormalizedState.ConditionalMinEntropyFeasible,
    State.toSubnormalized_identityTensorStateMatrix_eq]
  rw [hscale]
  exact hbound

/-- Petz-shaped fixed-reference smooth-min lower bound from a subnormalized
smoothed witness and a direct fixed-reference operator bound.

This is the narrow bridge needed by threshold-compressed substates: the witness
is not normalized, and the smoothing ball is centered at `ρ.toSubnormalized`. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_petz_operator_bound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (ρ' : SubnormalizedState (Prod a b))
    (hball : ρ.toSubnormalized.purifiedBall ε ρ')
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact le_smoothConditionalMinEntropyFixedSubnormalized_of_feasible_witness
    (a := a) (ρ := ρ) (ρ' := ρ') (σ := σ.toSubnormalized)
    hε_pos.le hε_lt hball
    (SubnormalizedState.ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
      (a := a) (ρ' := ρ') ρ hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) hbound)
    le_rfl

/-- Fixed-reference smooth-min lower bound from an explicit positive threshold
scale, with no full-rank assumption on the left state. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_positive_operator_bound
    (ρ : State (Prod a b)) (σ : State b)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (ρ' : SubnormalizedState (Prod a b))
    (hball : ρ.toSubnormalized.purifiedBall ε ρ')
    (hbound :
      ρ'.matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact le_smoothConditionalMinEntropyFixedSubnormalized_of_feasible_witness
    (a := a) (ρ := ρ) (ρ' := ρ') (σ := σ.toSubnormalized)
    hε_pos.le hε_lt hball
    (SubnormalizedState.ConditionalMinEntropyFeasible.of_le_positive_scale
      (a := a) (ρ' := ρ') σ hlambda hbound)
    le_rfl

/-! ### Source-shaped smooth-min Petz witness bridge -/

/-- The positive part `Δ = {ρ_AB - λ(I_A ⊗ σ_B)}_+` used in the
source-shaped TCR smooth-min witness. -/
def fixedPetzThresholdPositivePart
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  (ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ)⁺

theorem fixedPetzThresholdPositivePart_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).PosSemidef := by
  unfold fixedPetzThresholdPositivePart
  exact Matrix.nonneg_iff_posSemidef.mp
    (CFC.posPart_nonneg (ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ))

/-- The source-shaped threshold matrix
`Λ = λ(I_A ⊗ σ_B)` for the fixed-reference smooth-min witness. -/
def fixedPetzSmoothMinLambdaMatrix
    (_ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  lambda • identityTensorStateMatrix (a := a) σ

/-- Positive-part decomposition gives the source majorization
`ρ_AB ≤ Λ + Δ`. -/
theorem fixedPetzSmoothMin_state_le_lambda_add_delta
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.matrix ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
        ρ.fixedPetzThresholdPositivePart σ lambda := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let H : CMatrix (Prod a b) := ρ.matrix - Λ
  have hH : H.IsHermitian := by
    dsimp [H, Λ, fixedPetzSmoothMinLambdaMatrix, identityTensorStateMatrix]
    exact ρ.pos.isHermitian.sub
      ((identityTensorStateMatrix_posSemidef_of_state (a := a) σ).isHermitian.smul
        (IsSelfAdjoint.all lambda))
  rw [Matrix.le_iff]
  have hsub : H⁺ - H = H⁻ := by
    have h := CFC.posPart_sub_negPart H hH.isSelfAdjoint
    calc
      H⁺ - H = H⁺ - (H⁺ - H⁻) := by rw [h]
      _ = H⁻ := by abel
  have hdiff :
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda - ρ.matrix =
        H⁺ - H := by
    simp [H, Λ, fixedPetzSmoothMinLambdaMatrix, fixedPetzThresholdPositivePart]
    abel
  rw [hdiff, hsub]
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)

/-- For a positive-definite finite matrix, the CFC inverse square-root is an
ordinary two-sided inverse square-root. -/
theorem cMatrix_rpow_neg_half_mul_self_mul_rpow_neg_half_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) :
    CFC.rpow A (-(1 / 2 : ℝ)) * A * CFC.rpow A (-(1 / 2 : ℝ)) = 1 := by
  classical
  let U : CMatrix ι := hA.isHermitian.eigenvectorUnitary
  let D : CMatrix ι :=
    Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i : ℝ) : ℂ))
  let R : CMatrix ι :=
    Matrix.diagonal
      (fun i => ((hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
  have hA_spec : A = U * D * star U := by
    simpa [U, D, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hA.isHermitian.spectral_theorem
  have hR :
      CFC.rpow A (-(1 / 2 : ℝ)) = U * R * star U := by
    simpa [U, R] using
      cMatrix_rpow_eq_eigenbasis_diagonal hA.posSemidef (-(1 / 2 : ℝ))
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary]
  have hRDR : R * D * R = 1 := by
    dsimp [R, D]
    simp only [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      have hi : 0 < hA.isHermitian.eigenvalues i := hA.eigenvalues_pos i
      have hreal :
          hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) *
              hA.isHermitian.eigenvalues i *
              hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) = 1 := by
        have hsum : (-(1 / 2 : ℝ)) + -(1 / 2 : ℝ) = -1 := by ring
        rw [mul_right_comm, ← Real.rpow_add hi, hsum,
          Real.rpow_neg hi.le, Real.rpow_one, inv_mul_cancel₀ (ne_of_gt hi)]
      simpa using (show
        (↑(hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) *
          hA.isHermitian.eigenvalues i *
          hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ))) : ℂ) = 1 by
        exact_mod_cast hreal)
    · simp only [Matrix.diagonal_apply_ne _ hij]
      simp [hij]
  calc
    CFC.rpow A (-(1 / 2 : ℝ)) * A * CFC.rpow A (-(1 / 2 : ℝ)) =
        (U * R * star U) * (U * D * star U) * (U * R * star U) := by
      rw [hR, hA_spec]
    _ = U * (R * D * R) * star U := by
      conv_lhs =>
        rw [show U * R * star U * (U * D * star U) * (U * R * star U) =
          U * R * (star U * U) * D * (star U * U) * R * star U by noncomm_ring]
      rw [hU]
      noncomm_ring
    _ = 1 := by
      rw [hRDR]
      simp [U]

theorem cMatrix_rpow_neg_half_mul_self_eq_psdSqrt_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) :
    CFC.rpow A (-(1 / 2 : ℝ)) * A = psdSqrt A := by
  calc
    CFC.rpow A (-(1 / 2 : ℝ)) * A =
        CFC.rpow A (-(1 / 2 : ℝ)) * CFC.rpow A 1 := by
      exact congrArg (fun X => CFC.rpow A (-(1 / 2 : ℝ)) * X)
        (CFC.rpow_one A
          (ha := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)).symm
    _ = CFC.rpow A (-(1 / 2 : ℝ) + 1) := by
      exact (CFC.rpow_add (a := A) (x := -(1 / 2 : ℝ)) (y := 1) hA.isUnit).symm
    _ = CFC.rpow A (1 / 2 : ℝ) := by norm_num
    _ = psdSqrt A := by
      simpa [psdSqrt] using (CFC.sqrt_eq_rpow (a := A)).symm

/-- The source-shaped positive-definite/core filter
`G = Λ^{1/2}(Λ + Δ)^{-1/2}`.

For now this is the ordinary CFC `rpow (-1/2)` version.  Downstream lemmas
keep the inverse/square-root order fact as an explicit hypothesis, so the
support-inverse generalization can replace this definition without changing the
smooth-min handoff. -/
def fixedPetzSmoothMinG
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  psdSqrt (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda) *
    CFC.rpow
      (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
        ρ.fixedPetzThresholdPositivePart σ lambda)
      (-(1 / 2 : ℝ))

/-- Matrix of the source-shaped witness `ρ~ = GρG†`. -/
def fixedPetzSmoothMinWitnessMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix *
    Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda)

theorem fixedPetzSmoothMinLambdaMatrix_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda).PosDef := by
  unfold fixedPetzSmoothMinLambdaMatrix
  exact (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ).smul hlambda

theorem fixedPetzSmoothMinLambda_add_delta_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
      ρ.fixedPetzThresholdPositivePart σ lambda).PosDef :=
  by
    rw [add_comm]
    exact Matrix.PosDef.posSemidef_add
      (ρ.fixedPetzThresholdPositivePart_posSemidef σ lambda)
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ)

theorem fixedPetzSmoothMinG_filter_conj_eq_lambda_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    ρ.fixedPetzSmoothMinG σ lambda *
        (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda) *
          Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) =
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let Δ : CMatrix (Prod a b) := ρ.fixedPetzThresholdPositivePart σ lambda
  let A : CMatrix (Prod a b) := Λ + Δ
  let R : CMatrix (Prod a b) := CFC.rpow A (-(1 / 2 : ℝ))
  let S : CMatrix (Prod a b) := psdSqrt Λ
  have hΛpsd : Λ.PosSemidef := by
    simpa [Λ] using
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ).posSemidef
  have hApos : A.PosDef := by
    simpa [A, Λ, Δ] using
      ρ.fixedPetzSmoothMinLambda_add_delta_posDef σ lambda hlambda hσ
  have hR_sandwich : R * A * R = 1 := by
    simpa [R, A] using
      cMatrix_rpow_neg_half_mul_self_mul_rpow_neg_half_of_posDef hApos
  have hS2 : S * S = Λ := by
    simpa [S, Λ] using psdSqrt_mul_self_of_posSemidef hΛpsd
  have hS_star : Matrix.conjTranspose S = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using (psdSqrt_isHermitian Λ).eq
  have hR_star : Matrix.conjTranspose R = R := by
    have hRpsd : R.PosSemidef := by
      simpa [R, A] using cMatrix_rpow_posSemidef (s := (-(1 / 2 : ℝ))) hApos.posSemidef
    simpa [R, Matrix.star_eq_conjTranspose] using hRpsd.isHermitian.eq
  calc
    ρ.fixedPetzSmoothMinG σ lambda *
        (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda) *
          Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) =
        (S * R) * A * Matrix.conjTranspose (S * R) := by
      simp [fixedPetzSmoothMinG, S, R, A, Λ, Δ]
    _ = S * (R * A * R) * S := by
      rw [Matrix.conjTranspose_mul, hS_star, hR_star]
      noncomm_ring
    _ = Λ := by
      rw [hR_sandwich]
      simp [hS2]

theorem fixedPetzSmoothMinG_filter_conj_le_lambda_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    ρ.fixedPetzSmoothMinG σ lambda *
        (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda) *
          Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda := by
  rw [ρ.fixedPetzSmoothMinG_filter_conj_eq_lambda_posDef σ lambda hlambda hσ]

theorem fixedPetzSmoothMinWitnessMatrix_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).PosSemidef := by
  unfold fixedPetzSmoothMinWitnessMatrix
  exact ρ.pos.mul_mul_conjTranspose_same (ρ.fixedPetzSmoothMinG σ lambda)

theorem fixedPetzSmoothMinWitnessMatrix_trace_re_le_one_of_contract
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).trace.re ≤ 1 := by
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  have htrace_le :
      ((ρ.matrix * (Matrix.conjTranspose G * G)).trace).re ≤
        ((ρ.matrix * 1).trace).re :=
    cMatrix_trace_mul_le_of_le ρ.pos hcontract
  have hcyc :
      (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).trace =
        (ρ.matrix * (Matrix.conjTranspose G * G)).trace := by
    calc
      (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).trace =
          (G * ρ.matrix * Matrix.conjTranspose G).trace := rfl
      _ = (ρ.matrix * (Matrix.conjTranspose G * G)).trace := by
          calc
            (G * ρ.matrix * Matrix.conjTranspose G).trace =
                ((G * ρ.matrix) * Matrix.conjTranspose G).trace := by
              rw [Matrix.mul_assoc]
            _ = (Matrix.conjTranspose G * (G * ρ.matrix)).trace := by
              rw [Matrix.trace_mul_comm]
            _ = ((Matrix.conjTranspose G * G) * ρ.matrix).trace := by
              rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (Matrix.conjTranspose G * G)).trace := by
              rw [Matrix.trace_mul_comm]
  rw [hcyc]
  rw [Matrix.mul_one, ρ.trace_eq_one] at htrace_le
  norm_num at htrace_le
  exact htrace_le

/-- The source-shaped witness as a subnormalized state, assuming the filter is
contractive in the `G†G ≤ I` sense. -/
def fixedPetzSmoothMinWitnessSubstate
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    SubnormalizedState (Prod a b) where
  matrix := ρ.fixedPetzSmoothMinWitnessMatrix σ lambda
  pos := ρ.fixedPetzSmoothMinWitnessMatrix_posSemidef σ lambda
  trace_le_one :=
    ρ.fixedPetzSmoothMinWitnessMatrix_trace_re_le_one_of_contract σ lambda hcontract

@[simp]
theorem fixedPetzSmoothMinWitnessSubstate_matrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).matrix =
      ρ.fixedPetzSmoothMinWitnessMatrix σ lambda :=
  rfl

/-- Conjugating an operator inequality by a fixed matrix preserves the order. -/
theorem cMatrix_conj_le_conj_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R X G : CMatrix ι} (hRX : R ≤ X) :
    G * R * Matrix.conjTranspose G ≤ G * X * Matrix.conjTranspose G := by
  rw [Matrix.le_iff] at hRX ⊢
  have hpsd := hRX.mul_mul_conjTranspose_same G
  have hdiff :
      G * X * Matrix.conjTranspose G - G * R * Matrix.conjTranspose G =
        G * (X - R) * Matrix.conjTranspose G := by
    noncomm_ring
  rwa [hdiff]

theorem fixedPetzSmoothMinG_contract_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
        ρ.fixedPetzSmoothMinG σ lambda ≤ 1 := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let Δ : CMatrix (Prod a b) := ρ.fixedPetzThresholdPositivePart σ lambda
  let A : CMatrix (Prod a b) := Λ + Δ
  let R : CMatrix (Prod a b) := CFC.rpow A (-(1 / 2 : ℝ))
  let S : CMatrix (Prod a b) := psdSqrt Λ
  have hΛpsd : Λ.PosSemidef := by
    simpa [Λ] using
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ).posSemidef
  have hΔpsd : Δ.PosSemidef := by
    simpa [Δ] using ρ.fixedPetzThresholdPositivePart_posSemidef σ lambda
  have hApos : A.PosDef := by
    simpa [A, Λ, Δ] using
      ρ.fixedPetzSmoothMinLambda_add_delta_posDef σ lambda hlambda hσ
  have hΛ_le_A : Λ ≤ A := by
    rw [Matrix.le_iff]
    simpa [A] using hΔpsd
  have hR_sandwich : R * A * R = 1 := by
    simpa [R, A] using
      cMatrix_rpow_neg_half_mul_self_mul_rpow_neg_half_of_posDef hApos
  have hS2 : S * S = Λ := by
    simpa [S, Λ] using psdSqrt_mul_self_of_posSemidef hΛpsd
  have hS_star : Matrix.conjTranspose S = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using (psdSqrt_isHermitian Λ).eq
  have hR_star : Matrix.conjTranspose R = R := by
    have hRpsd : R.PosSemidef := by
      simpa [R, A] using cMatrix_rpow_posSemidef (s := (-(1 / 2 : ℝ))) hApos.posSemidef
    simpa [R, Matrix.star_eq_conjTranspose] using hRpsd.isHermitian.eq
  have hconj : R * Λ * R ≤ R * A * R := by
    simpa [hR_star] using cMatrix_conj_le_conj_of_le (G := R) hΛ_le_A
  have hG_eq : ρ.fixedPetzSmoothMinG σ lambda = S * R := by
    simp [fixedPetzSmoothMinG, S, R, A, Λ, Δ]
  calc
    Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
        ρ.fixedPetzSmoothMinG σ lambda =
        R * Λ * R := by
      rw [hG_eq, Matrix.conjTranspose_mul, hS_star, hR_star]
      calc
        R * S * (S * R) = R * (S * S) * R := by noncomm_ring
        _ = R * Λ * R := by rw [hS2]
    _ ≤ R * A * R := hconj
    _ = 1 := hR_sandwich

private theorem contract_doubled_effect_posSemidef_of_contract
    {ι : Type*} [Fintype ι] [DecidableEq ι] {G : CMatrix ι}
    (hcontract : Matrix.conjTranspose G * G ≤ 1) :
    ((1 : CMatrix ι) + 1 - (G + Matrix.conjTranspose G)).PosSemidef := by
  have hdiff : ((1 : CMatrix ι) - Matrix.conjTranspose G * G).PosSemidef := by
    simpa [Matrix.le_iff] using hcontract
  have hsq :
      (((1 : CMatrix ι) - Matrix.conjTranspose G) *
          ((1 : CMatrix ι) - G)).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self ((1 : CMatrix ι) - G)
    simpa [Matrix.conjTranspose_sub] using h
  have hsum := Matrix.PosSemidef.add hsq hdiff
  convert hsum using 1
  noncomm_ring

/-- TCR source trace estimate for the `GρG†` smooth-min witness:
the trace loss of the source filter is controlled by the threshold positive
part `Δ = {ρ_AB - λ(I_A ⊗ σ_B)}_+`. -/
theorem fixedPetzSmoothMinG_trace_loss_le_positivePart_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let Δ : CMatrix (Prod a b) := ρ.fixedPetzThresholdPositivePart σ lambda
  let A : CMatrix (Prod a b) := Λ + Δ
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  let E : CMatrix (Prod a b) := (1 : CMatrix (Prod a b)) + 1 -
    (G + Matrix.conjTranspose G)
  let S : CMatrix (Prod a b) := psdSqrt Λ
  let R : CMatrix (Prod a b) := CFC.rpow A (-(1 / 2 : ℝ))
  have hcontract : Matrix.conjTranspose G * G ≤ 1 := by
    simpa [G] using ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ
  have hEpos : E.PosSemidef := by
    simpa [E, G] using
      contract_doubled_effect_posSemidef_of_contract (G := G) hcontract
  have hρ_le_A : ρ.matrix ≤ A := by
    simpa [A, Λ, Δ] using ρ.fixedPetzSmoothMin_state_le_lambda_add_delta σ lambda
  have htrace_le : ((E * ρ.matrix).trace).re ≤ ((E * A).trace).re :=
    cMatrix_trace_mul_le_of_le hEpos hρ_le_A
  have hGρ_conj :
      ((Matrix.conjTranspose G * ρ.matrix).trace).re =
        ((G * ρ.matrix).trace).re :=
    trace_conjTranspose_mul_hermitian_re_eq ρ.pos.isHermitian
  have hEρ :
      ((E * ρ.matrix).trace).re =
        2 * (1 - ((G * ρ.matrix).trace).re) := by
    simp [E, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
      hGρ_conj, ρ.trace_eq_one]
    ring
  have hΛpsd : Λ.PosSemidef := by
    simpa [Λ] using
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ).posSemidef
  have hΔpsd : Δ.PosSemidef := by
    simpa [Δ] using ρ.fixedPetzThresholdPositivePart_posSemidef σ lambda
  have hApos : A.PosDef := by
    simpa [A, Λ, Δ] using
      ρ.fixedPetzSmoothMinLambda_add_delta_posDef σ lambda hlambda hσ
  have hΛ_le_A : Λ ≤ A := by
    rw [Matrix.le_iff]
    simpa [A] using hΔpsd
  have hSpos : S.PosSemidef := by
    simpa [S] using psdSqrt_pos Λ
  have hS2 : S * S = Λ := by
    simpa [S, Λ] using psdSqrt_mul_self_of_posSemidef hΛpsd
  have hS_le_sqrtA : S ≤ psdSqrt A := by
    simpa [S] using psdSqrt_le_psdSqrt_of_le hΛ_le_A
  have htrace_S : Λ.trace.re ≤ ((S * psdSqrt A).trace).re := by
    have h := cMatrix_trace_mul_le_of_le hSpos hS_le_sqrtA
    simpa [hS2] using h
  have hG_eq : G = S * R := by
    simp [G, S, R, A, Λ, Δ, fixedPetzSmoothMinG]
  have hRA : R * A = psdSqrt A := by
    simpa [R, A] using cMatrix_rpow_neg_half_mul_self_eq_psdSqrt_of_posDef hApos
  have hGA : G * A = S * psdSqrt A := by
    rw [hG_eq]
    calc
      (S * R) * A = S * (R * A) := by noncomm_ring
      _ = S * psdSqrt A := by rw [hRA]
  have hGA_lower : Λ.trace.re ≤ ((G * A).trace).re := by
    rw [hGA]
    exact htrace_S
  have hGA_conj :
      ((Matrix.conjTranspose G * A).trace).re = ((G * A).trace).re :=
    trace_conjTranspose_mul_hermitian_re_eq hApos.isHermitian
  have hAtr : A.trace.re = Λ.trace.re + Δ.trace.re := by
    simp [A, Matrix.trace_add]
  have hEA :
      ((E * A).trace).re ≤ 2 * Δ.trace.re := by
    have hEAeq :
        ((E * A).trace).re =
          2 * A.trace.re - ((G * A).trace).re -
            ((Matrix.conjTranspose G * A).trace).re := by
      simp [E, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
        ]
      ring
    rw [hEAeq, hGA_conj, hAtr]
    linarith
  have htwice :
      2 * (1 - ((G * ρ.matrix).trace).re) ≤ 2 * Δ.trace.re := by
    rw [← hEρ]
    exact le_trans htrace_le hEA
  have hloss : 1 - ((G * ρ.matrix).trace).re ≤ Δ.trace.re := by
    linarith
  simpa [G, Δ] using hloss

/-- If `ρ ≤ Λ + Δ`, then the source filter reduces the witness bound to the
single CFC inverse/square-root inequality `G(Λ+Δ)G† ≤ Λ`. -/
theorem fixedPetzSmoothMinWitnessMatrix_le_lambda_of_le_add_delta
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hρ_le :
      ρ.matrix ≤
        ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda)
    (hconj :
      ρ.fixedPetzSmoothMinG σ lambda *
          (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
            ρ.fixedPetzThresholdPositivePart σ lambda) *
            Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) ≤
        ρ.fixedPetzSmoothMinLambdaMatrix σ lambda) :
    ρ.fixedPetzSmoothMinWitnessMatrix σ lambda ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda := by
  exact le_trans (cMatrix_conj_le_conj_of_le
    (G := ρ.fixedPetzSmoothMinG σ lambda) hρ_le) hconj

/-- Source-shaped witness bound reduced only to the CFC filter inequality
`G(Λ+Δ)G† ≤ Λ`; the positive-part majorization is discharged here. -/
theorem fixedPetzSmoothMinWitnessMatrix_le_lambda_of_filter_conj
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hconj :
      ρ.fixedPetzSmoothMinG σ lambda *
          (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
            ρ.fixedPetzThresholdPositivePart σ lambda) *
            Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) ≤
        ρ.fixedPetzSmoothMinLambdaMatrix σ lambda) :
    ρ.fixedPetzSmoothMinWitnessMatrix σ lambda ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda :=
  ρ.fixedPetzSmoothMinWitnessMatrix_le_lambda_of_le_add_delta σ lambda
    (ρ.fixedPetzSmoothMin_state_le_lambda_add_delta σ lambda) hconj

/-- Source-shaped `GρG†` handoff at an explicit positive threshold scale.
This is the PSD-left version of the threshold bridge: the center state is an
arbitrary finite state, while full-rankness is only required for the fixed
reference when the concrete TCR filter is used. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound_scale
    (ρ : State (Prod a b)) (σ : State b)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract))
    (hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_positive_operator_bound
    (ρ := ρ) (σ := σ) ε lambda hε_pos hε_lt hlambda
    (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) hball hbound

/-- Source-shaped `GρG†` handoff at an explicit positive threshold scale, with
the CFC filter order inequality discharged from a full-rank reference. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda
          (ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ))) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ
  have hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ := by
    have hmain :
        ρ.fixedPetzSmoothMinWitnessMatrix σ lambda ≤
          ρ.fixedPetzSmoothMinLambdaMatrix σ lambda :=
      ρ.fixedPetzSmoothMinWitnessMatrix_le_lambda_of_filter_conj σ lambda
        (ρ.fixedPetzSmoothMinG_filter_conj_le_lambda_posDef σ lambda hlambda hσ)
    simpa [fixedPetzSmoothMinWitnessSubstate_matrix,
      fixedPetzSmoothMinLambdaMatrix] using hmain
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound_scale
      σ ε lambda hε_pos hε_lt hlambda hcontract
      (by simpa [hcontract] using hball) hbound

/-- Source-shaped `GρG†` handoff into the existing subnormalized smooth-min
lower-bound theorem.  The two remaining source obligations are explicit:
the witness must lie in the purified ball, and the CFC filter must satisfy the
direct threshold operator bound. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hcontract :
      Matrix.conjTranspose
          (ρ.fixedPetzSmoothMinG σ
            (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))) *
          ρ.fixedPetzSmoothMinG σ
            (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) ≤ 1)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ
          (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
          hcontract))
    (hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ
        (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
        hcontract).matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_petz_operator_bound
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
    (ρ.fixedPetzSmoothMinWitnessSubstate σ
      (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
      hcontract)
    hball hbound

/-- Source-shaped `GρG†` smooth-min handoff with the contractivity and
operator-order parts discharged in the positive-definite core.  The only
remaining source obligation is the purified-ball estimate for the TCR witness. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ
          (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
          (ρ.fixedPetzSmoothMinG_contract_posDef σ
            (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
            (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
            hσ))) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let lam : ℝ :=
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hlam : 0 < lam :=
    ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lam) *
          ρ.fixedPetzSmoothMinG σ lam ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lam hlam hσ
  have hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lam hcontract).matrix ≤
        ((lam : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ := by
    have hmain :
        ρ.fixedPetzSmoothMinWitnessMatrix σ lam ≤
          ρ.fixedPetzSmoothMinLambdaMatrix σ lam :=
      ρ.fixedPetzSmoothMinWitnessMatrix_le_lambda_of_filter_conj σ lam
        (ρ.fixedPetzSmoothMinG_filter_conj_le_lambda_posDef σ lam hlam hσ)
    simpa [fixedPetzSmoothMinWitnessSubstate_matrix,
      fixedPetzSmoothMinLambdaMatrix] using hmain
  exact smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
    hcontract (by simpa [lam, hcontract] using hball) hbound

/-! ### Fixed-reference threshold projector bridge -/

/-- Hermitian fixed-reference threshold matrix
`ρ_AB - λ (I_A ⊗ σ_B)`.

This is the conditional analogue of the state-vs-state threshold matrix used
in the hypothesis-testing/Petz comparison file. -/
def fixedPetzThresholdMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ

theorem fixedPetzThresholdMatrix_isHermitian
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdMatrix σ lambda).IsHermitian := by
  unfold fixedPetzThresholdMatrix identityTensorStateMatrix
  exact ρ.pos.isHermitian.sub
    ((identityTensorStateMatrix_posSemidef_of_state (a := a) σ).isHermitian.smul
      (IsSelfAdjoint.all lambda))

/-- Positive spectral projector of
`ρ_AB - λ (I_A ⊗ σ_B)` for the fixed-reference threshold construction. -/
def fixedPetzThresholdProjector
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  positiveSpectralProjector
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

theorem fixedPetzThresholdProjector_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdProjector σ lambda).PosSemidef := by
  unfold fixedPetzThresholdProjector
  exact positiveSpectralProjector_posSemidef
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

theorem fixedPetzThresholdProjector_isHermitian
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdProjector σ lambda).IsHermitian :=
  (ρ.fixedPetzThresholdProjector_posSemidef σ lambda).isHermitian

theorem fixedPetzThresholdProjector_idempotent
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdProjector σ lambda *
        ρ.fixedPetzThresholdProjector σ lambda =
      ρ.fixedPetzThresholdProjector σ lambda := by
  unfold fixedPetzThresholdProjector
  exact positiveSpectralProjector_idempotent
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

theorem fixedPetzThresholdProjector_le_one
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdProjector σ lambda ≤ 1 := by
  unfold fixedPetzThresholdProjector
  exact positiveSpectralProjector_le_one
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

private theorem one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart_fixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : CMatrix ι) (hH : H.IsHermitian) :
    (1 - positiveSpectralProjector H hH) * (-H) = H⁻ := by
  let P := positiveSpectralProjector H hH
  have hPH : P * H = H⁺ := positiveSpectralProjector_mul_self_eq_posPart H hH
  have hsub : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have hQH : (1 - P) * H = -H⁻ := by
    calc
      (1 - P) * H = H - P * H := by simp [sub_mul]
      _ = H - H⁺ := by rw [hPH]
      _ = -H⁻ := by
        nth_rewrite 1 [← hsub]
        abel
  calc
    (1 - P) * (-H) = -((1 - P) * H) := by rw [mul_neg]
    _ = -(-H⁻) := by rw [hQH]
    _ = H⁻ := by simp

/-- On the complement of the fixed-reference positive threshold projector,
`λ(I_A ⊗ σ_B) - ρ_AB` is positive semidefinite after left selection.

This is the matrix-order core needed before a postselection/normalization
bridge can turn the threshold effect into a smoothed min-entropy witness. -/
theorem fixedPetzThresholdComplement_mul_gap_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ((1 - ρ.fixedPetzThresholdProjector σ lambda) *
        (lambda • identityTensorStateMatrix (a := a) σ - ρ.matrix)).PosSemidef := by
  let H : CMatrix (Prod a b) := ρ.fixedPetzThresholdMatrix σ lambda
  let hH : H.IsHermitian := ρ.fixedPetzThresholdMatrix_isHermitian σ lambda
  have hselect :
      (1 - positiveSpectralProjector H hH) * (-H) = H⁻ :=
    one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart_fixed H hH
  have hneg : (H⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hmatrix :
      (1 - ρ.fixedPetzThresholdProjector σ lambda) *
          (lambda • identityTensorStateMatrix (a := a) σ - ρ.matrix) =
        H⁻ := by
    simpa [H, hH, fixedPetzThresholdProjector, fixedPetzThresholdMatrix,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hselect
  rw [hmatrix]
  exact hneg

/-- Complement projection matrix for the fixed-reference Petz threshold. -/
def fixedPetzThresholdComplementProjector
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  1 - ρ.fixedPetzThresholdProjector σ lambda

@[simp]
theorem fixedPetzThresholdComplementProjector_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdComplementProjector σ lambda =
      1 - ρ.fixedPetzThresholdProjector σ lambda :=
  rfl

theorem fixedPetzThresholdComplementProjector_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdComplementProjector σ lambda).PosSemidef := by
  have hle := ρ.fixedPetzThresholdProjector_le_one σ lambda
  rw [Matrix.le_iff] at hle
  simpa [fixedPetzThresholdComplementProjector] using hle

theorem fixedPetzThresholdComplementProjector_isHermitian
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdComplementProjector σ lambda).IsHermitian :=
  (ρ.fixedPetzThresholdComplementProjector_posSemidef σ lambda).isHermitian

theorem fixedPetzThresholdComplementProjector_idempotent
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdComplementProjector σ lambda *
        ρ.fixedPetzThresholdComplementProjector σ lambda =
      ρ.fixedPetzThresholdComplementProjector σ lambda := by
  unfold fixedPetzThresholdComplementProjector
  have hP := ρ.fixedPetzThresholdProjector_idempotent σ lambda
  calc
    (1 - ρ.fixedPetzThresholdProjector σ lambda) *
        (1 - ρ.fixedPetzThresholdProjector σ lambda) =
      1 - ρ.fixedPetzThresholdProjector σ lambda -
        ρ.fixedPetzThresholdProjector σ lambda +
          ρ.fixedPetzThresholdProjector σ lambda *
            ρ.fixedPetzThresholdProjector σ lambda := by
        noncomm_ring
    _ = 1 - ρ.fixedPetzThresholdProjector σ lambda := by
        rw [hP]
        noncomm_ring

/-- The fixed-threshold postselected matrix `(1-P)ρ(1-P)`. -/
def fixedPetzThresholdCompressedMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  ρ.fixedPetzThresholdComplementProjector σ lambda *
    ρ.matrix * ρ.fixedPetzThresholdComplementProjector σ lambda

@[simp]
theorem fixedPetzThresholdCompressedMatrix_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdCompressedMatrix σ lambda =
      ρ.fixedPetzThresholdComplementProjector σ lambda *
        ρ.matrix * ρ.fixedPetzThresholdComplementProjector σ lambda :=
  rfl

theorem fixedPetzThresholdCompressedMatrix_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedMatrix σ lambda).PosSemidef := by
  let Q : CMatrix (Prod a b) := ρ.fixedPetzThresholdComplementProjector σ lambda
  have h := ρ.pos.conjTranspose_mul_mul_same Q
  have hQ : Matrix.conjTranspose Q = Q := by
    simpa [Q] using (ρ.fixedPetzThresholdComplementProjector_isHermitian σ lambda).eq
  rw [hQ] at h
  change (Q * ρ.matrix * Q).PosSemidef
  exact h

theorem fixedPetzThresholdCompressedMatrix_trace_re_le_one
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedMatrix σ lambda).trace.re ≤ 1 := by
  let Q : CMatrix (Prod a b) := ρ.fixedPetzThresholdComplementProjector σ lambda
  have htrace_le' :
      ((ρ.matrix * Q).trace).re ≤ ((ρ.matrix * 1).trace).re :=
    cMatrix_trace_mul_le_of_le ρ.pos
      (by
        rw [Matrix.le_iff]
        have hPpos := ρ.fixedPetzThresholdProjector_posSemidef σ lambda
        simpa [Q, fixedPetzThresholdComplementProjector, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc] using hPpos)
  have htrace_le : ((ρ.matrix * Q).trace).re ≤ ρ.matrix.trace.re := by
    simpa [Q, Matrix.mul_one] using htrace_le'
  have hcyc :
      (ρ.fixedPetzThresholdCompressedMatrix σ lambda).trace =
        (ρ.matrix * Q).trace := by
    calc
      (ρ.fixedPetzThresholdCompressedMatrix σ lambda).trace =
          (Q * ρ.matrix * Q).trace := rfl
      _ = (ρ.matrix * (Q * Q)).trace := by
          calc
            (Q * ρ.matrix * Q).trace = ((Q * ρ.matrix) * Q).trace := by
              rw [Matrix.mul_assoc]
            _ = (Q * (Q * ρ.matrix)).trace := by rw [Matrix.trace_mul_comm]
            _ = ((Q * Q) * ρ.matrix).trace := by rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (Q * Q)).trace := by rw [Matrix.trace_mul_comm]
      _ = (ρ.matrix * Q).trace := by
          rw [show Q * Q = Q by
            exact ρ.fixedPetzThresholdComplementProjector_idempotent σ lambda]
  rw [hcyc]
  rw [ρ.trace_eq_one] at htrace_le
  norm_num at htrace_le
  exact htrace_le

/-- The fixed-threshold postselected matrix as a subnormalized state. -/
def fixedPetzThresholdCompressedSubstate
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    SubnormalizedState (Prod a b) where
  matrix := ρ.fixedPetzThresholdCompressedMatrix σ lambda
  pos := ρ.fixedPetzThresholdCompressedMatrix_posSemidef σ lambda
  trace_le_one := ρ.fixedPetzThresholdCompressedMatrix_trace_re_le_one σ lambda

@[simp]
theorem fixedPetzThresholdCompressedSubstate_matrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix =
      ρ.fixedPetzThresholdCompressedMatrix σ lambda :=
  rfl

theorem fixedPetzThresholdComplement_trace_re_eq_one_sub_projector_trace_re
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re =
      1 - ((ρ.fixedPetzThresholdProjector σ lambda * ρ.matrix).trace).re := by
  rw [fixedPetzThresholdComplementProjector_eq]
  have htrace :
      (((1 - ρ.fixedPetzThresholdProjector σ lambda) * ρ.matrix).trace).re =
        ρ.matrix.trace.re -
          ((ρ.fixedPetzThresholdProjector σ lambda * ρ.matrix).trace).re := by
    simp [sub_mul, Matrix.trace_sub]
  rw [htrace, ρ.trace_eq_one]
  norm_num

/-- The complement fail probability is the positive-threshold projector
probability. -/
theorem fixedPetzThresholdComplement_fail_eq_projector_trace_re
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    1 - ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re =
      ((ρ.fixedPetzThresholdProjector σ lambda * ρ.matrix).trace).re := by
  rw [fixedPetzThresholdComplement_trace_re_eq_one_sub_projector_trace_re]
  ring

theorem fixedPetzThresholdCompressedSubstate_traceNorm_sub_le_of_complement_fail
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail :
      1 - (((ρ.fixedPetzThresholdComplementProjector σ lambda) * ρ.matrix).trace).re ≤
        ε ^ 2 / 2) :
    traceNorm ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix - ρ.matrix) ≤
      2 * ε := by
  let Q : CMatrix (Prod a b) := ρ.fixedPetzThresholdComplementProjector σ lambda
  have hgentle := gentle_projector Q
    (ρ.fixedPetzThresholdComplementProjector_posSemidef σ lambda)
    (ρ.fixedPetzThresholdComplementProjector_idempotent σ lambda) ρ
  have hsqrt_le : Real.sqrt (1 - ((Q * ρ.matrix).trace).re) ≤ ε := by
    refine (Real.sqrt_le_left hε).mpr ?_
    have hhalf : ε ^ 2 / 2 ≤ ε ^ 2 := by
      nlinarith [sq_nonneg ε]
    exact le_trans hfail hhalf
  calc
    traceNorm ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix - ρ.matrix)
        = traceNorm (Q * ρ.matrix * Q - ρ.matrix) := by
          rfl
    _ ≤ 2 * Real.sqrt (1 - ((Q * ρ.matrix).trace).re) := hgentle
    _ ≤ 2 * ε := by
          exact mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)

theorem fixedPetzThresholdCompressedSubstate_traceNorm_sub_le_of_projector_fail
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail :
      (((ρ.fixedPetzThresholdProjector σ lambda) * ρ.matrix).trace).re ≤ ε ^ 2 / 2) :
    traceNorm ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix - ρ.matrix) ≤
      2 * ε := by
  refine ρ.fixedPetzThresholdCompressedSubstate_traceNorm_sub_le_of_complement_fail
    σ lambda hε ?_
  rwa [fixedPetzThresholdComplement_fail_eq_projector_trace_re]

/-- If the compressed substate is known to have sufficiently large
generalized fidelity with the original state, it lies in the subnormalized
purified-distance ball. This is the remaining handoff needed after a
compression-specific fidelity lower bound is available. -/
theorem fixedPetzThresholdCompressedSubstate_purifiedBall_of_generalizedFidelity
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfid :
      1 - ρ.toSubnormalized.generalizedFidelity
          (ρ.fixedPetzThresholdCompressedSubstate σ lambda) ≤ ε ^ 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda) := by
  rw [SubnormalizedState.purifiedBall_eq, SubnormalizedState.purifiedDistance_eq]
  exact (Real.sqrt_le_left hε).mpr hfid

/-- Purification-overlap handoff for the fixed-Petz compressed substate.

This is the checked intermediate used by the purification/Uhlmann route: once
the concrete post-measurement purification of
`ρ.fixedPetzThresholdCompressedSubstate σ lambda` is constructed with overlap
at least `t` against a purification of `ρ.toSubnormalized`, generalized
fidelity is at least `t`. -/
theorem fixedPetzThresholdCompressedSubstate_le_generalizedFidelity_of_hatExtension_overlap
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ψ Φ : PureVector (Prod r (Sum PUnit (Prod a b)))}
    (hΨ : Ψ.Purifies ρ.toSubnormalized.hatExtension)
    (hΦ : Φ.Purifies (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension)
    {t : ℝ} (hoverlap : t ≤ Ψ.overlapSq Φ) :
    t ≤ ρ.toSubnormalized.generalizedFidelity
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda) :=
by
  rw [SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension]
  exact le_trans hoverlap
    (PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ)

/-- Exact-overlap handoff for the fixed-Petz compressed substate.

This is the concrete target left by the post-measurement purification
construction: if two hat-extension purifications have overlap exactly
`Tr(Qρ)`, where `Q` is the fixed-Petz complement projector, then generalized
fidelity is at least `(Re Tr(Qρ))²`. -/
theorem fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_overlap_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ψ Φ : PureVector (Prod r (Sum PUnit (Prod a b)))}
    (hΨ : Ψ.Purifies ρ.toSubnormalized.hatExtension)
    (hΦ : Φ.Purifies (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension)
    (hoverlap :
      Ψ.overlap Φ =
        ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace)) :
    (((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda) :=
by
  refine
    fixedPetzThresholdCompressedSubstate_le_generalizedFidelity_of_hatExtension_overlap
      (ρ := ρ) (σ := σ) (lambda := lambda) (Ψ := Ψ) (Φ := Φ)
      hΨ hΦ ?_
  rw [PureVector.overlapSq_eq_normSq, hoverlap]
  simpa [sq] using
    Complex.re_sq_le_normSq
      ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace)

/-- Amplitude-matrix version of the fixed-Petz compressed-substate
purification-overlap handoff.

This isolates the concrete post-measurement construction obligation to three
matrix equations: the two target-side Gram equations matching
`PureVector.Purifies`, and the trace pairing of the two amplitude matrices. -/
theorem fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_amplitudeMatrix_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ψ Φ : PureVector (Prod r (Sum PUnit (Prod a b)))}
    (hΨamp :
      Ψ.amplitudeMatrix * Matrix.conjTranspose Ψ.amplitudeMatrix =
        ρ.toSubnormalized.hatExtension.matrix)
    (hΦamp :
      Φ.amplitudeMatrix * Matrix.conjTranspose Φ.amplitudeMatrix =
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension.matrix)
    (hoverlapAmp :
      (Matrix.conjTranspose Ψ.amplitudeMatrix * Φ.amplitudeMatrix).trace =
        ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace)) :
    (((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda) :=
by
  have hΨ : Ψ.Purifies ρ.toSubnormalized.hatExtension := by
    rw [PureVector.purifies_iff, PureVector.state_matrix]
    rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
    exact hΨamp
  have hΦ : Φ.Purifies (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension := by
    rw [PureVector.purifies_iff, PureVector.state_matrix]
    rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
    exact hΦamp
  refine
    fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_overlap_eq
      (ρ := ρ) (σ := σ) (lambda := lambda) (Ψ := Ψ) (Φ := Φ)
      hΨ hΦ ?_
  rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
  exact hoverlapAmp

/-- Candidate amplitude matrix for the hat extension of the fixed-Petz
compressed substate.

The failure row carries the square root of the compressed state's failure mass.
The success block is the complement threshold projector applied to the
canonical square-root amplitude of `ρ`. -/
def fixedPetzThresholdHatCompressedAmplitudeMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    CMatrix (Sum PUnit (Prod a b)) :=
  Matrix.fromBlocks
    (fun _ _ : PUnit =>
      ((Real.sqrt
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatFailureMass : ℝ) : ℂ))
    0 0
    (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.sqrtMatrix)

theorem fixedPetzThresholdHatCompressedAmplitudeMatrix_gram
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda *
        Matrix.conjTranspose
          (ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda) =
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension.matrix := by
  classical
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzThresholdCompressedSubstate σ lambda
  let Q : CMatrix (Prod a b) :=
    ρ.fixedPetzThresholdComplementProjector σ lambda
  let S : CMatrix (Prod a b) := ρ.sqrtMatrix
  have hQ : Matrix.conjTranspose Q = Q := by
    simpa [Q] using (ρ.fixedPetzThresholdComplementProjector_isHermitian σ lambda).eq
  have hS : Matrix.conjTranspose S = S := by
    simpa [S] using ρ.sqrtMatrix_isHermitian.eq
  have hsuccess :
      (Q * S) * Matrix.conjTranspose (Q * S) = τ.matrix := by
    rw [Matrix.conjTranspose_mul, hQ, hS]
    calc
      (Q * S) * (S * Q) = Q * (S * S) * Q := by
        simp only [Matrix.mul_assoc]
      _ = Q * ρ.matrix * Q := by rw [ρ.sqrtMatrix_mul_self]
      _ = τ.matrix := by
        simp [τ, Q, fixedPetzThresholdCompressedSubstate_matrix,
          fixedPetzThresholdCompressedMatrix]
  unfold fixedPetzThresholdHatCompressedAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  ext x y
  cases x with
  | inl xi =>
      cases y with
      | inl yj =>
          cases xi
          cases yj
          simp [τ, Matrix.mul_apply, SubnormalizedState.hatExtension_matrix,
            ← Complex.ofReal_mul, Real.mul_self_sqrt τ.hatFailureMass_nonneg]
      | inr yj =>
          simp [SubnormalizedState.hatExtension_matrix]
  | inr xi =>
      cases y with
      | inl yj =>
          simp [SubnormalizedState.hatExtension_matrix]
      | inr yj =>
          simpa [τ, Q, S] using congrFun (congrFun hsuccess xi) yj

theorem toSubnormalized_hatExtension_sqrtMatrix
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.hatExtension.sqrtMatrix =
      Matrix.fromBlocks (0 : CMatrix PUnit) 0 0 ρ.sqrtMatrix := by
  classical
  have hfail : ρ.toSubnormalized.hatFailureMass = 0 := by
    simp [SubnormalizedState.hatFailureMass, ρ.trace_eq_one]
  rw [State.sqrtMatrix, SubnormalizedState.hatExtension_matrix,
    SubnormalizedState.hatExtensionMatrix]
  rw [Matrix.fromBlocks_diagonal_psdSqrt ρ.toSubnormalized.hatFailureBlock_pos
    ρ.toSubnormalized.pos]
  have hfailBlock :
      psdSqrt ρ.toSubnormalized.hatFailureBlock = (0 : CMatrix PUnit) := by
    rw [show ρ.toSubnormalized.hatFailureBlock = (0 : CMatrix PUnit) by
      ext i j
      cases i
      cases j
      simp [SubnormalizedState.hatFailureBlock, hfail]]
    simp
  rw [hfailBlock]
  rfl

theorem toSubnormalized_hatExtension_canonicalPurification_amplitudeMatrix
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.hatExtension.canonicalPurification.amplitudeMatrix =
      Matrix.fromBlocks (0 : CMatrix PUnit) 0 0 ρ.sqrtMatrix := by
  classical
  ext x i
  cases x with
  | inl xi =>
      cases xi
      cases i with
      | inl ij =>
          cases ij
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]
      | inr ij =>
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]
  | inr xi =>
      cases i with
      | inl ij =>
          cases ij
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]
      | inr ij =>
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]

/-- Candidate amplitude matrix for the hat extension of the source-shaped
`GρG†` witness.

The failure row carries the square root of the witness failure mass.  The
success block is the source filter `G` applied to the canonical square-root
amplitude of `ρ`. -/
def fixedPetzSmoothMinWitnessHatAmplitudeMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    CMatrix (Sum PUnit (Prod a b)) :=
  Matrix.fromBlocks
    (fun _ _ : PUnit =>
      ((Real.sqrt
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).hatFailureMass : ℝ) : ℂ))
    0 0 (ρ.fixedPetzSmoothMinG σ lambda * ρ.sqrtMatrix)

theorem fixedPetzSmoothMinWitnessHatAmplitudeMatrix_gram
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract *
        Matrix.conjTranspose
          (ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract) =
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).hatExtension.matrix := by
  classical
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  let S : CMatrix (Prod a b) := ρ.sqrtMatrix
  have hS : Matrix.conjTranspose S = S := by
    simpa [S] using ρ.sqrtMatrix_isHermitian.eq
  have hsuccess :
      (G * S) * Matrix.conjTranspose (G * S) = τ.matrix := by
    rw [Matrix.conjTranspose_mul, hS]
    calc
      (G * S) * (S * Matrix.conjTranspose G) =
          G * (S * S) * Matrix.conjTranspose G := by
        noncomm_ring
      _ = G * ρ.matrix * Matrix.conjTranspose G := by
        rw [show S * S = ρ.matrix by simp [S]]
      _ = τ.matrix := by
        simp [τ, G, fixedPetzSmoothMinWitnessSubstate_matrix,
          fixedPetzSmoothMinWitnessMatrix]
  unfold fixedPetzSmoothMinWitnessHatAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  ext x y
  cases x with
  | inl xi =>
      cases y with
      | inl yj =>
          cases xi
          cases yj
          simp [τ, Matrix.mul_apply, SubnormalizedState.hatExtension_matrix,
            ← Complex.ofReal_mul, Real.mul_self_sqrt τ.hatFailureMass_nonneg]
      | inr yj =>
          simp [SubnormalizedState.hatExtension_matrix]
  | inr xi =>
      cases y with
      | inl yj =>
          simp [SubnormalizedState.hatExtension_matrix]
      | inr yj =>
          simpa [τ, G, S] using congrFun (congrFun hsuccess xi) yj

theorem fixedPetzSmoothMinWitnessHatAmplitudeMatrix_overlap_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (Matrix.conjTranspose
          ρ.toSubnormalized.hatExtension.canonicalPurification.amplitudeMatrix *
        ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract).trace =
      (ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace := by
  classical
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  rw [toSubnormalized_hatExtension_canonicalPurification_amplitudeMatrix]
  unfold fixedPetzSmoothMinWitnessHatAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.trace_fromBlocks_diagonal]
  simp
  calc
    (Matrix.conjTranspose ρ.sqrtMatrix * (G * ρ.sqrtMatrix)).trace =
        (ρ.sqrtMatrix * (G * ρ.sqrtMatrix)).trace := by
      rw [ρ.sqrtMatrix_isHermitian.eq]
    _ = ((ρ.sqrtMatrix * G) * ρ.sqrtMatrix).trace := by rw [Matrix.mul_assoc]
    _ = (G * (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
      calc
        ((ρ.sqrtMatrix * G) * ρ.sqrtMatrix).trace =
            (ρ.sqrtMatrix * (ρ.sqrtMatrix * G)).trace := by
              rw [Matrix.trace_mul_comm]
        _ = ((ρ.sqrtMatrix * ρ.sqrtMatrix) * G).trace := by
              rw [← Matrix.mul_assoc]
        _ = (G * (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
              rw [Matrix.trace_mul_comm]
    _ = (G * ρ.matrix).trace := by
      rw [ρ.sqrtMatrix_mul_self]
    _ = (ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace := by
      simp [G]

theorem fixedPetzSmoothMinWitnessSubstate_sq_trace_re_le_generalizedFidelity
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) := by
  classical
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract
  let AΦ : CMatrix (Sum PUnit.{max u v + 1} (Prod a b)) :=
    ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract
  have htrace : (AΦ * Matrix.conjTranspose AΦ).trace = 1 := by
    rw [show AΦ * Matrix.conjTranspose AΦ = τ.hatExtension.matrix by
      simpa [AΦ, τ] using
        ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix_gram σ lambda hcontract]
    exact τ.hatExtension_trace_one
  let Φ := PureVector.ofAmplitudeMatrix AΦ htrace
  have hΨ :
      ρ.toSubnormalized.hatExtension.canonicalPurification.Purifies
        ρ.toSubnormalized.hatExtension :=
    ρ.toSubnormalized.hatExtension.canonicalPurification_purifies
  have hΦ : Φ.Purifies τ.hatExtension := by
    rw [PureVector.purifies_iff, PureVector.state_matrix]
    rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
    simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
      ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix_gram σ lambda hcontract
  have hoverlapSq :
      (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ^ 2 ≤
        ρ.toSubnormalized.hatExtension.canonicalPurification.overlapSq Φ := by
    rw [PureVector.overlapSq_eq_normSq]
    have hoverlap :
        ρ.toSubnormalized.hatExtension.canonicalPurification.overlap Φ =
          (ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace := by
      rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
      simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
        ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix_overlap_trace σ lambda hcontract
    rw [hoverlap]
    simpa [sq] using
      Complex.re_sq_le_normSq
        ((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace)
  rw [SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension]
  exact le_trans hoverlapSq
    (PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ)

theorem fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_trace_re
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1)
    (htrace :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤ ε ^ 2 / 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) := by
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract
  let q : ℝ := ((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re
  have hgf : q ^ 2 ≤ ρ.toSubnormalized.generalizedFidelity τ := by
    simpa [τ, q] using
      ρ.fixedPetzSmoothMinWitnessSubstate_sq_trace_re_le_generalizedFidelity
        σ lambda hcontract
  have hq_nonneg : 0 ≤ q := by
    have hhalf_lt_one : ε ^ 2 / 2 < 1 := by nlinarith [hε_pos, hε_lt]
    have hq_lt : 1 - q < 1 := lt_of_le_of_lt (by simpa [q] using htrace) hhalf_lt_one
    linarith
  have hone_sub_gf :
      1 - ρ.toSubnormalized.generalizedFidelity τ ≤ ε ^ 2 := by
    have hone_sub_qsq : 1 - q ^ 2 ≤ ε ^ 2 := by
      by_cases hq_le_one : q ≤ 1
      · have hfactor : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
        have htwo : 1 + q ≤ 2 := by linarith
        have hnon : 0 ≤ 1 - q := by linarith
        calc
          1 - q ^ 2 = (1 - q) * (1 + q) := hfactor
          _ ≤ (1 - q) * 2 := mul_le_mul_of_nonneg_left htwo hnon
          _ ≤ (ε ^ 2 / 2) * 2 := by
            exact mul_le_mul_of_nonneg_right (by simpa [q] using htrace) (by norm_num)
          _ = ε ^ 2 := by ring
      · have hq_ge_one : 1 ≤ q := le_of_not_ge hq_le_one
        have hnonpos : 1 - q ^ 2 ≤ 0 := by nlinarith
        have hεsq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
        exact le_trans hnonpos hεsq_nonneg
    linarith
  rw [SubnormalizedState.purifiedBall_eq, SubnormalizedState.purifiedDistance_eq]
  exact (Real.sqrt_le_left hε_pos.le).mpr hone_sub_gf

theorem fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_positivePart_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1)
    (htrace :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re)
    (hdelta :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤ ε ^ 2 / 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) :=
  ρ.fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_trace_re σ lambda
    hε_pos hε_lt hcontract (le_trans htrace hdelta)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (htrace :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re)
    (hdelta :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤ ε ^ 2 / 2) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ
  have hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) :=
    ρ.fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_positivePart_trace
      σ lambda hε_pos hε_lt hcontract htrace hdelta
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball_scale
      σ hσ ε lambda hε_pos hε_lt hlambda
      (by simpa [hcontract] using hball)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε lambda α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
        lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α)
    (hscale :
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α ≤ ε ^ 2 / 2) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  have htrace_lam :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re :=
    ρ.fixedPetzSmoothMinG_trace_loss_le_positivePart_trace σ lambda hlambda hσ
  have hdelta_lam :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤ ε ^ 2 / 2 :=
    le_trans hpetz hscale
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace_scale
      σ hσ ε lambda hε_pos hε_lt hlambda htrace_lam hdelta_lam

theorem fixedPetzThresholdPositivePart_trace_re_le_epsilon_sq_half_of_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε) (hα_gt : 1 < α)
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α) :
    let lam : ℝ :=
      ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
    (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hpetz_lam :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
    simpa [lam, hα_pos, hα_ne_one] using hpetz
  have hscale :
      lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α = ε ^ 2 / 2 := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_rpow_one_sub_alpha_mul_traceTerm_eq
        hρ σ hσ hε_pos hα_gt
  exact le_trans hpetz_lam (le_of_eq hscale)

/-- Fixed-reference specialization of the Petz effect-variational reduction.

This is the exact remaining one-shot source obligation in matrix form:
prove the Petz effect-variational inequality for
`A = ρ_AB` and `B = I_A ⊗ σ_B`, then the TCR positive-part trace bound follows. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hvar :
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lambda α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_effect_variational
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      ρ.pos hB hlambda hα_gt hα_le_two hvar

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hvar :
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lambda α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_effect_variational
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      hρ.posSemidef hB hlambda hα_gt hα_le_two hvar

/-- Fixed-reference positive-part trace bound from the narrow Petz
unitary-dephasing monotonicity predicate in the Petz-threshold eigenbasis. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hmono :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      ρ.pos hB hlambda hα_gt hα_le_two
      (ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian))
      (by simpa [hB] using hmono)

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hmono :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      hρ.posSemidef hB hlambda hα_gt hα_le_two
      (hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian))
      (by simpa [hB] using hmono)

/-- Fixed-reference positive-part trace bound from the Hilbert-Schmidt kernel
form of Petz dephasing monotonicity in the Petz-threshold eigenbasis. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_kernelDephaseMonotone_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hkernel :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
      ρ.matrix (identityTensorStateMatrix (a := a) σ) U α
      (by simpa [hB, H, hH, U] using hkernel)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone_posSemidef
    σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hkernel :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
      ρ.matrix (identityTensorStateMatrix (a := a) σ) U α
      (by simpa [hB, H, hH, U] using hkernel)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
    hρ σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

/-- Fixed-reference positive-part trace bound from finite uniform joint
convexity on the sign orbit of the Petz-threshold eigenbasis. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_uniformJointConvex_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
      ρ.matrix (identityTensorStateMatrix (a := a) σ) ρ.pos hB U
      hα_gt hα_le_two (by
        simpa [hB, H, hH, U] using hconv)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone_posSemidef
    σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_uniformJointConvex
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
      cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
      ρ.matrix (identityTensorStateMatrix (a := a) σ) hρ.posSemidef hB U
      hα_gt hα_le_two (by
        simpa [hB, H, hH, U] using hconv)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
    hρ σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

/-- Fixed-reference source one-shot smooth-min lower bound for arbitrary left
states and a full-rank reference, with Petz dephasing monotonicity supplied via
finite-uniform joint convexity.

This is the `σ_B` full-support branch of TCR 2008 `thm:entropy-ineq`: the left
state is only positive semidefinite, while the reference side is positive
definite. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference_of_uniformJointConvex
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScaleFullReference_pos σ hσ ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ :=
    ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScaleFullReference_pos σ hσ ε α hα_pos hα_ne_one
  have hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
    exact
      ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_uniformJointConvex_posSemidef
        σ hσ hlam hα_gt hα_le_two (by
          simpa [lam, hα_pos, hα_ne_one] using hconv)
  have hscale :
      lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α ≤ ε ^ 2 / 2 := by
    exact le_of_eq (by
      simpa [lam, hα_pos, hα_ne_one] using
        ρ.petzSmoothMinThresholdScaleFullReference_rpow_one_sub_alpha_mul_traceTerm_eq
          σ hσ hε_pos hα_gt)
  have hsmooth :
      -log2 lam ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε :=
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace_scale
      σ hσ ε lam α hε_pos hε_lt hlam hpetz hscale
  have hexponent :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one -
          (1 / (α - 1)) * log2 (2 / ε ^ 2) =
        -log2 lam := by
    simpa [lam, hα_pos, hα_ne_one, petzSmoothMinThresholdExponentFullReference] using
      ρ.petzSmoothMinThresholdExponentFullReference_eq_neg_log2_scale
        σ hσ ε α hα_pos hα_ne_one
  simpa [hα_pos, hα_ne_one] using hexponent.le.trans hsmooth

/-- Fixed-reference source one-shot smooth-min lower bound for arbitrary left
states and a full-rank reference, with Petz monotonicity discharged by the
finite-dimensional rpow-perspective theorem. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference_of_uniformJointConvex
      σ hσ ε α hε_pos hε_lt hα_gt hα_le_two (by
        exact cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two _ _)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (htrace :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      1 - (((ρ.fixedPetzSmoothMinG σ lam * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lam).trace.re)
    (hdelta :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let lam : ℝ :=
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hlam : 0 < lam :=
    ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lam) *
          ρ.fixedPetzSmoothMinG σ lam ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lam hlam hσ
  have htrace_lam :
      1 - (((ρ.fixedPetzSmoothMinG σ lam * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lam).trace.re := by
    simpa [lam] using htrace
  have hdelta_lam :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2 := by
    simpa [lam] using hdelta
  have hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lam hcontract) :=
    ρ.fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_positivePart_trace
      σ lam hε_pos hε_lt hcontract htrace_lam hdelta_lam
  exact
    smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball
      (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hcontract] using hball)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have htrace_lam :
      1 - (((ρ.fixedPetzSmoothMinG σ lam * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lam).trace.re :=
    ρ.fixedPetzSmoothMinG_trace_loss_le_positivePart_trace σ lam hlam hσ
  have hdelta_lam :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2 := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.fixedPetzThresholdPositivePart_trace_re_le_epsilon_sq_half_of_petzTrace
        hρ σ hσ hε_pos hα_gt hpetz
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one] using htrace_lam)
      (by simpa [lam, hα_pos, hα_ne_one] using hdelta_lam)

/-- Source-shaped `GρG†` smooth-min lower bound from the fixed-reference
Petz effect-variational inequality.

The noncommutative Petz-Hölder/operator-convex step is the explicit `hvar`
hypothesis; everything else in the TCR smooth-min bridge is discharged here. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hvar :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lam α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hvar_lam :
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lam α := by
    simpa [lam, hα_pos, hα_ne_one] using hvar
  have hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α :=
    ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational
      hρ σ hσ hlam hα_gt hα_le_two hvar_lam
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one] using hpetz)

/-- Source-shaped `GρG†` smooth-min lower bound from the narrow Petz
unitary-dephasing monotonicity predicate in the Petz-threshold eigenbasis. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hmono :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α := by
    simpa [lam, hα_pos, hα_ne_one, hlam] using hmono
  have hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α :=
    ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
      hρ σ hσ hlam hα_gt hα_le_two hmono_lam
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one] using hpetz)

/-- Source-shaped `GρG†` smooth-min lower bound from the Hilbert-Schmidt
kernel form of Petz dephasing monotonicity in the Petz-threshold eigenbasis. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hkernel :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α := by
    have hkernel_lam :
        cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
          (identityTensorStateMatrix (a := a) σ) U α := by
      simpa [lam, hα_pos, hα_ne_one, hlam, hB, H, hH, U] using hkernel
    have hmono :
        cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
          (identityTensorStateMatrix (a := a) σ) U α :=
      cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
        ρ.matrix (identityTensorStateMatrix (a := a) σ) U α hkernel_lam
    simpa [hB, H, hH, U] using hmono
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one, hlam] using hmono_lam)

/-- Source-shaped `GρG†` smooth-min lower bound from finite uniform joint
convexity on the sign orbit of the Petz-threshold eigenbasis. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_uniformJointConvex
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hconv_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α := by
    simpa [lam, hα_pos, hα_ne_one, hlam] using hconv
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α := by
    have hmono :
        cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
          (identityTensorStateMatrix (a := a) σ) U α :=
      cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
        ρ.matrix (identityTensorStateMatrix (a := a) σ) hρ.posSemidef hB U
        hα_gt hα_le_two (by
          simpa [hB, H, hH, U] using hconv_lam)
    simpa [hB, H, hH, U] using hmono
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one, hlam] using hmono_lam)

theorem fixedPetzThresholdHatCompressedAmplitudeMatrix_overlap_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
  (Matrix.conjTranspose
          ρ.toSubnormalized.hatExtension.canonicalPurification.amplitudeMatrix *
        ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda).trace =
      (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace := by
  classical
  rw [toSubnormalized_hatExtension_canonicalPurification_amplitudeMatrix]
  unfold fixedPetzThresholdHatCompressedAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.trace_fromBlocks_diagonal]
  simp
  calc
    (Matrix.conjTranspose ρ.sqrtMatrix *
        (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.sqrtMatrix)).trace =
        (ρ.sqrtMatrix *
          (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.sqrtMatrix)).trace := by
      rw [ρ.sqrtMatrix_isHermitian.eq]
    _ = ((ρ.sqrtMatrix * ρ.fixedPetzThresholdComplementProjector σ lambda) *
          ρ.sqrtMatrix).trace := by rw [Matrix.mul_assoc]
    _ = (ρ.fixedPetzThresholdComplementProjector σ lambda *
          (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
      calc
        ((ρ.sqrtMatrix * ρ.fixedPetzThresholdComplementProjector σ lambda) *
            ρ.sqrtMatrix).trace =
          (ρ.sqrtMatrix *
            (ρ.sqrtMatrix * ρ.fixedPetzThresholdComplementProjector σ lambda)).trace := by
            rw [Matrix.trace_mul_comm]
        _ = ((ρ.sqrtMatrix * ρ.sqrtMatrix) *
              ρ.fixedPetzThresholdComplementProjector σ lambda).trace := by
            rw [← Matrix.mul_assoc]
        _ = (ρ.fixedPetzThresholdComplementProjector σ lambda *
              (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
            rw [Matrix.trace_mul_comm]
    _ = (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace := by
      rw [ρ.sqrtMatrix_mul_self]
    _ = (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace := rfl

theorem fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda) := by
  classical
  let AΦ : CMatrix (Sum PUnit.{max u v + 1} (Prod a b)) :=
    ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda
  have htrace : (AΦ * Matrix.conjTranspose AΦ).trace = 1 := by
    rw [show AΦ * Matrix.conjTranspose AΦ =
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension.matrix by
      simpa [AΦ] using
        ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix_gram σ lambda]
    exact (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension_trace_one
  let Φ := PureVector.ofAmplitudeMatrix AΦ htrace
  refine
    fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_amplitudeMatrix_eq
      (ρ := ρ) (σ := σ) (lambda := lambda)
      (Ψ := ρ.toSubnormalized.hatExtension.canonicalPurification)
      (Φ := Φ) ?_ ?_ ?_
  · exact PureVector.purifies_amplitudeMatrix_mul_conjTranspose_eq
      ρ.toSubnormalized.hatExtension.canonicalPurification_purifies
  · simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
      ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix_gram σ lambda
  · simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
      ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix_overlap_trace σ lambda

theorem fixedPetzThresholdCompressedSubstate_purifiedBall_of_complement_fail
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail :
      1 - (((ρ.fixedPetzThresholdComplementProjector σ lambda) *
        ρ.matrix).trace).re ≤ ε ^ 2 / 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda) := by
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzThresholdCompressedSubstate σ lambda
  let Q : CMatrix (Prod a b) :=
    ρ.fixedPetzThresholdComplementProjector σ lambda
  let q : ℝ := ((Q * ρ.matrix).trace).re
  have hq_trace : τ.matrix.trace.re = q := by
    have hcyc : τ.matrix.trace = (ρ.matrix * Q).trace := by
      calc
        τ.matrix.trace = (Q * ρ.matrix * Q).trace := by
          simp [τ, Q, fixedPetzThresholdCompressedSubstate_matrix,
            fixedPetzThresholdCompressedMatrix]
        _ = (ρ.matrix * (Q * Q)).trace := by
          calc
            (Q * ρ.matrix * Q).trace = ((Q * ρ.matrix) * Q).trace := by
              rw [Matrix.mul_assoc]
            _ = (Q * (Q * ρ.matrix)).trace := by rw [Matrix.trace_mul_comm]
            _ = ((Q * Q) * ρ.matrix).trace := by rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (Q * Q)).trace := by rw [Matrix.trace_mul_comm]
        _ = (ρ.matrix * Q).trace := by
          rw [ρ.fixedPetzThresholdComplementProjector_idempotent σ lambda]
    rw [hcyc, Matrix.trace_mul_comm]
  have hgf :
      q ^ 2 ≤ ρ.toSubnormalized.generalizedFidelity τ := by
    simpa [τ, Q, q] using
      ρ.fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity σ lambda
  have hq_nonneg : 0 ≤ q := by
    simpa [hq_trace] using τ.trace_nonneg
  have hq_le_one : q ≤ 1 := by
    simpa [hq_trace] using τ.trace_le_one
  have hone_sub_gf :
      1 - ρ.toSubnormalized.generalizedFidelity τ ≤ ε ^ 2 := by
    have hone_sub_qsq : 1 - q ^ 2 ≤ ε ^ 2 := by
      have hfactor : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
      have htwo : 1 + q ≤ 2 := by linarith
      have hnon : 0 ≤ 1 - q := by linarith
      calc
        1 - q ^ 2 = (1 - q) * (1 + q) := hfactor
        _ ≤ (1 - q) * 2 := mul_le_mul_of_nonneg_left htwo hnon
        _ ≤ (ε ^ 2 / 2) * 2 := by
          exact mul_le_mul_of_nonneg_right (by simpa [Q, q] using hfail) (by norm_num)
        _ = ε ^ 2 := by ring
    linarith
  exact fixedPetzThresholdCompressedSubstate_purifiedBall_of_generalizedFidelity
    (ρ := ρ) (σ := σ) (lambda := lambda) hε (by simpa [τ] using hone_sub_gf)

/-- Two-sided compression by the complement of the fixed-reference threshold
projector satisfies the corresponding threshold operator inequality. -/
theorem fixedPetzThresholdComplement_compress_matrix_le
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (1 - ρ.fixedPetzThresholdProjector σ lambda) * ρ.matrix *
        (1 - ρ.fixedPetzThresholdProjector σ lambda) ≤
      (1 - ρ.fixedPetzThresholdProjector σ lambda) *
        (lambda • identityTensorStateMatrix (a := a) σ) *
          (1 - ρ.fixedPetzThresholdProjector σ lambda) := by
  let H : CMatrix (Prod a b) := ρ.fixedPetzThresholdMatrix σ lambda
  let hH : H.IsHermitian := ρ.fixedPetzThresholdMatrix_isHermitian σ lambda
  let P : CMatrix (Prod a b) := positiveSpectralProjector H hH
  let Q : CMatrix (Prod a b) := 1 - P
  let B : CMatrix (Prod a b) := lambda • identityTensorStateMatrix (a := a) σ
  change Q * ρ.matrix * Q ≤ Q * B * Q
  rw [Matrix.le_iff]
  have hselect : Q * (B - ρ.matrix) = H⁻ := by
    have h :=
      one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart_fixed H hH
    simpa [Q, P, B, H, hH, fixedPetzThresholdMatrix,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hnegQ : H⁻ * Q = H⁻ := by
    have hnegP : H⁻ * P = 0 := by
      simpa [P] using negPart_mul_positiveSpectralProjector H hH
    calc
      H⁻ * Q = H⁻ * (1 - P) := rfl
      _ = H⁻ - H⁻ * P := by rw [mul_sub, mul_one]
      _ = H⁻ := by rw [hnegP]; simp
  have hdiff :
      Q * B * Q - Q * ρ.matrix * Q = Q * (B - ρ.matrix) * Q := by
    noncomm_ring
  rw [hdiff, hselect, hnegQ]
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)

theorem fixedPetzThresholdCompressedMatrix_le_compressed_threshold
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdCompressedMatrix σ lambda ≤
      ρ.fixedPetzThresholdComplementProjector σ lambda *
        (lambda • identityTensorStateMatrix (a := a) σ) *
          ρ.fixedPetzThresholdComplementProjector σ lambda := by
  unfold fixedPetzThresholdCompressedMatrix fixedPetzThresholdComplementProjector
  exact ρ.fixedPetzThresholdComplement_compress_matrix_le σ lambda

theorem fixedPetzThresholdCompressedSubstate_le_compressed_threshold
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix ≤
      ρ.fixedPetzThresholdComplementProjector σ lambda *
        (lambda • identityTensorStateMatrix (a := a) σ) *
          ρ.fixedPetzThresholdComplementProjector σ lambda := by
  simpa using ρ.fixedPetzThresholdCompressedMatrix_le_compressed_threshold σ lambda

theorem fixedPetzThresholdCompressedSubstate_normalize_matrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (htr :
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re ≠ 0) :
    ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).normalize htr).matrix =
      ((((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re)⁻¹ : ℝ) : ℂ) •
        ρ.fixedPetzThresholdCompressedMatrix σ lambda := by
  rw [SubnormalizedState.normalize_matrix]
  rfl

theorem fixedPetzThresholdCompressedSubstate_normalize_le_scaled_compressed_threshold
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (htr :
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re ≠ 0) :
    ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).normalize htr).matrix ≤
      ((((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re)⁻¹ : ℝ) : ℂ) •
        (ρ.fixedPetzThresholdComplementProjector σ lambda *
          (lambda • identityTensorStateMatrix (a := a) σ) *
            ρ.fixedPetzThresholdComplementProjector σ lambda) := by
  rw [fixedPetzThresholdCompressedSubstate_normalize_matrix]
  exact cMatrix_real_smul_le_smul
    (inv_nonneg.mpr
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).trace_nonneg)
    (ρ.fixedPetzThresholdCompressedMatrix_le_compressed_threshold σ lambda)

/-- Any feasible fixed-reference exponent lower-bounds the fixed-reference
conditional min-entropy. -/
theorem le_conditionalMinEntropyFixed_of_feasible
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalMinEntropyFixed σ := by
  rw [conditionalMinEntropyFixed_eq]
  refine le_csSup ?_ hfeas
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro mu hmu
  exact ConditionalMinEntropyFeasible_le_log2_card_left (a := a) hmu

/-- A purified-ball state with a feasible fixed-reference min-entropy exponent
gives a lower bound on fixed-reference smooth min-entropy. -/
theorem le_smoothConditionalMinEntropyFixed_of_feasible_witness
    {ρ ρ' : State (Prod a b)} {σ : State b} {ε lam lower : ℝ}
    (hball : ρ.purifiedBall ε ρ')
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ' σ lam)
    (hlower : lower ≤ lam) :
    lower ≤ ρ.smoothConditionalMinEntropyFixed σ ε := by
  have hmin : lam ≤ ρ'.conditionalMinEntropyFixed σ :=
    le_conditionalMinEntropyFixed_of_feasible (a := a) hfeas
  have hsmooth :
      ρ'.conditionalMinEntropyFixed σ ≤
        ρ.smoothConditionalMinEntropyFixed σ ε := by
    rw [smoothConditionalMinEntropyFixed_eq_sSup_candidates]
    exact le_csSup
      (SmoothConditionalMinEntropyFixedCandidate_bddAbove (a := a) ρ σ ε)
      (show SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε
        (ρ'.conditionalMinEntropyFixed σ) from ⟨ρ', hball, rfl⟩)
  exact le_trans hlower (le_trans hmin hsmooth)

/-- Petz-shaped fixed-reference smooth-min lower bound from a concrete
order-feasible smoothed witness.

This isolates the remaining TCR construction: produce a nearby state `ρ'` whose
fixed-reference min-entropy order constraint is feasible at the displayed Petz
threshold. -/
theorem smoothConditionalMinEntropyFixed_lower_bound_of_petz_feasible_witness
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (_hε_pos : 0 < ε) (_hε_lt : ε < 1)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (ρ' : State (Prod a b))
    (hball : ρ.purifiedBall ε ρ')
    (hfeas :
      ConditionalMinEntropyFeasible (a := a) ρ' σ
        (ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
          (1 / (α - 1)) * log2 (2 / ε ^ 2))) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixed σ ε := by
  exact le_smoothConditionalMinEntropyFixed_of_feasible_witness
    (a := a) hball hfeas le_rfl

/-- An operator bound at the fixed-reference Petz threshold scale is exactly a
conditional-min-entropy feasible exponent at the Petz threshold. -/
theorem ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
    {ρ' : State (Prod a b)}
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ConditionalMinEntropyFeasible (a := a) ρ' σ
      (ρ.petzSmoothMinThresholdExponent hρ σ hσ ε α hα_pos hα_ne_one) := by
  simpa [ConditionalMinEntropyFeasible, petzSmoothMinThresholdScale] using hbound

/-- Petz-shaped fixed-reference smooth-min lower bound from a concrete
operator-order smoothed witness at the Petz threshold scale. -/
theorem smoothConditionalMinEntropyFixed_lower_bound_of_petz_operator_bound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (ρ' : State (Prod a b))
    (hball : ρ.purifiedBall ε ρ')
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixed σ ε := by
  exact smoothConditionalMinEntropyFixed_lower_bound_of_petz_feasible_witness
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
    ρ' hball
    (ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
      (a := a) (ρ' := ρ') ρ hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) hbound)

/-! ## Finite-AEP assembly core -/

/-! ### Full-rank regularization setup for arbitrary finite states -/

/-- Matrix path that regularizes an arbitrary finite bipartite state by adding
white noise on `AB`.

For `0 < η ≤ 1`, the associated state below is positive definite, and as
`η → 0+` this matrix tends back to `ρ.matrix`.  This is the reusable
regularization surface needed before taking the positive-definite finite-AEP
core to arbitrary states. -/
def finiteAEPFullRankRegularizationMatrix
    (ρ : State (Prod a b)) (η : ℝ) : CMatrix (Prod a b) :=
  (((1 - η : ℝ) : ℂ) • ρ.matrix) +
    ((((η / (Fintype.card (Prod a b) : ℝ) : ℝ)) : ℂ) •
      (1 : CMatrix (Prod a b)))

/-- The fixed direction from `ρ` toward the maximally mixed state used by the
white-noise regularization. -/
def finiteAEPFullRankRegularizationDirection
    (ρ : State (Prod a b)) : CMatrix (Prod a b) :=
  ((((1 / (Fintype.card (Prod a b) : ℝ) : ℝ) : ℂ) •
    (1 : CMatrix (Prod a b))) - ρ.matrix)

/-- The normalized state associated with
`finiteAEPFullRankRegularizationMatrix` when the regularization weight lies in
the probability interval. -/
def finiteAEPFullRankRegularization
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    State (Prod a b) where
  matrix := finiteAEPFullRankRegularizationMatrix ρ η
  pos := by
    unfold finiteAEPFullRankRegularizationMatrix
    have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
      exact_mod_cast sub_nonneg.mpr hη1
    have hright : (0 : ℂ) ≤ (((η / (Fintype.card (Prod a b) : ℝ) : ℝ) : ℂ)) := by
      exact_mod_cast div_nonneg hη0 (by positivity : (0 : ℝ) ≤ Fintype.card (Prod a b))
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul ρ.pos hleft)
      (Matrix.PosSemidef.smul Matrix.PosSemidef.one hright)
  trace_eq_one := by
    letI : Nonempty (Prod a b) := ρ.nonempty
    have hcardR : (Fintype.card (Prod a b) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card (Prod a b) ≠ 0))
    have hscalar :
        (1 - η) + (η / (Fintype.card (Prod a b) : ℝ)) *
            (Fintype.card (Prod a b) : ℝ) = 1 := by
      field_simp [hcardR]
      ring
    unfold finiteAEPFullRankRegularizationMatrix
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.trace_eq_one,
      Matrix.trace_one]
    simpa [smul_eq_mul] using congrArg (fun x : ℝ => (x : ℂ)) hscalar

@[simp]
theorem finiteAEPFullRankRegularization_matrix
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).matrix =
      finiteAEPFullRankRegularizationMatrix ρ η :=
  rfl

/-- The full-rank white-noise regularization differs from the original state
by `η` times a fixed matrix. -/
theorem finiteAEPFullRankRegularization_matrix_sub
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).matrix - ρ.matrix =
      ((η : ℂ) • ρ.finiteAEPFullRankRegularizationDirection) := by
  ext i j
  simp [finiteAEPFullRankRegularization_matrix,
    finiteAEPFullRankRegularizationMatrix, finiteAEPFullRankRegularizationDirection,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij]
    ring_nf
  · simp [hij]
    ring_nf

/-- The normalized trace distance from the white-noise regularization to the
original state is at most linear in the regularization weight. -/
theorem finiteAEPFullRankRegularization_normalizedTraceDistance_le
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).normalizedTraceDistance ρ ≤
      η * (1 / 2 : ℝ) *
        traceNorm ρ.finiteAEPFullRankRegularizationDirection := by
  rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq,
    QIT.traceDistance]
  rw [finiteAEPFullRankRegularization_matrix_sub ρ η hη0 hη1]
  have hnorm := traceNorm_real_smul_le (a := Prod a b) hη0
    ρ.finiteAEPFullRankRegularizationDirection
  nlinarith

/-- The purified distance from the white-noise regularization to the original
state is controlled by the square root of the regularization weight. -/
theorem finiteAEPFullRankRegularization_purifiedDistance_le
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).purifiedDistance ρ ≤
      Real.sqrt
        (η *
          traceNorm ρ.finiteAEPFullRankRegularizationDirection) := by
  have hP :=
    purifiedDistance_le_sqrt_two_mul_normalizedTraceDistance
      (ρ.finiteAEPFullRankRegularization η hη0 hη1) ρ
  have hD := ρ.finiteAEPFullRankRegularization_normalizedTraceDistance_le η hη0 hη1
  have htrace_nonneg :
      0 ≤ traceNorm ρ.finiteAEPFullRankRegularizationDirection :=
    traceNorm_nonneg _
  refine le_trans hP (Real.sqrt_le_sqrt ?_)
  nlinarith

private theorem cMatrix_real_smul_one_posDef_forFiniteAEP
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (hr : 0 < r) :
    (r • (1 : CMatrix ι)).PosDef := by
  rw [show r • (1 : CMatrix ι) = Matrix.diagonal (fun _ : ι => (r : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hr

/-- Positive regularization weight makes the white-noise regularization
positive definite, even when the original state is singular. -/
theorem finiteAEPFullRankRegularization_posDef
    (ρ : State (Prod a b)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηpos : 0 < η) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).matrix.PosDef := by
  letI : Nonempty (Prod a b) := ρ.nonempty
  unfold finiteAEPFullRankRegularization finiteAEPFullRankRegularizationMatrix
  have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
    exact_mod_cast sub_nonneg.mpr hη1
  have hright : 0 < η / (Fintype.card (Prod a b) : ℝ) := by
    exact div_pos hηpos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Prod a b)))
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.pos hleft)
    (cMatrix_real_smul_one_posDef_forFiniteAEP hright)

private theorem partialTraceA_one_forFiniteAEP
    (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :
    partialTraceA (a := a) (b := b) (1 : CMatrix (Prod a b)) =
      ((Fintype.card a : ℂ) • (1 : CMatrix b)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceA]
  · simp [partialTraceA, hij]

private theorem finiteAEPFullRankRegularization_whiteNoise_marginalB_scalar
    (ρ : State (Prod a b)) (η : ℝ) :
    ((η / (Fintype.card (Prod a b) : ℝ) : ℝ) *
        (Fintype.card a : ℝ)) =
      η / (Fintype.card b : ℝ) := by
  letI : Nonempty (Prod a b) := ρ.nonempty
  letI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have ha : (Fintype.card a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card a ≠ 0))
  have hb : (Fintype.card b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card b ≠ 0))
  have hprod :
      (Fintype.card (Prod a b) : ℝ) =
        (Fintype.card a : ℝ) * (Fintype.card b : ℝ) := by
    exact_mod_cast (Fintype.card_prod a b)
  rw [hprod]
  field_simp [ha, hb]

/-- The `B` marginal of the white-noise regularization is the matching
white-noise regularization of `ρ_B`. -/
theorem finiteAEPFullRankRegularization_marginalB_matrix
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).marginalB.matrix =
      (((1 - η : ℝ) : ℂ) • ρ.marginalB.matrix) +
        ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) := by
  unfold finiteAEPFullRankRegularization
  simp only [State.marginalB_matrix]
  unfold finiteAEPFullRankRegularizationMatrix
  rw [partialTraceA_add, partialTraceA_smul, partialTraceA_smul,
    partialTraceA_one_forFiniteAEP]
  rw [smul_smul]
  have hscalar :
      (((η / (Fintype.card (Prod a b) : ℝ) : ℝ) : ℂ) *
          (Fintype.card a : ℂ)) =
        (((η / (Fintype.card b : ℝ) : ℝ) : ℂ)) := by
    exact_mod_cast
      finiteAEPFullRankRegularization_whiteNoise_marginalB_scalar
        (a := a) (b := b) ρ η
  rw [hscalar]

/-- The `B` marginal of the regularized state is positive definite for every
positive regularization weight. -/
theorem finiteAEPFullRankRegularization_marginalB_posDef
    (ρ : State (Prod a b)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηpos : 0 < η) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).marginalB.matrix.PosDef := by
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  rw [finiteAEPFullRankRegularization_marginalB_matrix]
  have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
    exact_mod_cast sub_nonneg.mpr hη1
  have hright : 0 < η / (Fintype.card b : ℝ) := by
    exact div_pos hηpos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card b))
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.marginalB.pos hleft)
    (cMatrix_real_smul_one_posDef_forFiniteAEP hright)

/-- The full-rank regularization matrix tends back to the original state
matrix as the noise weight tends to zero through positive probabilities. -/
theorem finiteAEPFullRankRegularizationMatrix_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto (fun η : ℝ => finiteAEPFullRankRegularizationMatrix ρ η)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.matrix) := by
  have hcont : Continuous fun η : ℝ =>
      finiteAEPFullRankRegularizationMatrix ρ η := by
    unfold finiteAEPFullRankRegularizationMatrix
    fun_prop
  have h0 : finiteAEPFullRankRegularizationMatrix ρ 0 = ρ.matrix := by
    simp [finiteAEPFullRankRegularizationMatrix]
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- The expanded `B`-marginal white-noise regularization matrix tends back to
the original `B` marginal as the noise weight tends to zero through positive
probabilities. -/
theorem finiteAEPFullRankRegularization_marginalB_matrix_path_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        (((1 - η : ℝ) : ℂ) • ρ.marginalB.matrix) +
          ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.marginalB.matrix) := by
  have hcont : Continuous fun η : ℝ =>
      (((1 - η : ℝ) : ℂ) • ρ.marginalB.matrix) +
        ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) := by
    fun_prop
  have h0 :
      (((1 - (0 : ℝ) : ℝ) : ℂ) • ρ.marginalB.matrix) +
          ((((0 / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) =
        ρ.marginalB.matrix := by
    simp
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- The `B` marginal matrix of the full-rank regularized state tends back to
the original `B` marginal matrix as the noise weight tends to zero through
`η ∈ (0, 1)`.

Outside the interval the displayed path is filled in with the limiting matrix,
so it is a total function on `ℝ`; on the `nhdsWithin` filter it is eventually
equal to the actual regularized marginal. -/
theorem finiteAEPFullRankRegularization_marginalB_matrix_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          (ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le).marginalB.matrix
        else
          ρ.marginalB.matrix)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.marginalB.matrix) := by
  refine Filter.Tendsto.congr' ?_
    (finiteAEPFullRankRegularization_marginalB_matrix_path_tendsto_zero ρ)
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [dif_pos hη]
  exact
    (finiteAEPFullRankRegularization_marginalB_matrix
      (a := a) (b := b) ρ η hη.1.le hη.2.le).symm

/-- The full-rank regularized state tends back to the original state as the
noise weight tends to zero through `η ∈ (0, 1)`.

Outside the interval the displayed path is filled in with the limiting state,
so it is a total function on `ℝ`; on the `nhdsWithin` filter it is eventually
equal to the actual regularized state. -/
theorem finiteAEPFullRankRegularization_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  refine Filter.Tendsto.congr' ?_ (finiteAEPFullRankRegularizationMatrix_tendsto_zero ρ)
  filter_upwards [self_mem_nhdsWithin] with η hη
  change ρ.finiteAEPFullRankRegularizationMatrix η =
    (if hη' : η ∈ Set.Ioo (0 : ℝ) 1 then
      ρ.finiteAEPFullRankRegularization η hη'.1.le hη'.2.le
    else ρ).matrix
  rw [dif_pos hη]
  rfl

/-- Conditional entropy is continuous along the full-rank white-noise
regularization path. -/
theorem finiteAEPFullRankRegularization_conditionalEntropy_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        (if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).conditionalEntropy)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.conditionalEntropy) :=
  State.conditionalEntropy_continuous.tendsto ρ |>.comp
    (finiteAEPFullRankRegularization_tendsto_zero ρ)

/-- Fixed tensor powers are continuous as maps of the input density state. -/
theorem tensorPower_matrix_continuous (n : ℕ) :
    Continuous (fun ρ : State a => (ρ.tensorPower n).matrix) := by
  induction n with
  | zero =>
      change Continuous fun _ : State a => (1 : CMatrix PUnit)
      fun_prop
  | succ n ih =>
      change Continuous fun ρ : State a => (ρ.prod (ρ.tensorPower n)).matrix
      refine continuous_pi ?_
      intro i
      refine continuous_pi ?_
      intro j
      cases i with
      | mk i0 it =>
        cases j with
        | mk j0 jt =>
          simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
          exact ((continuous_apply j0).comp
              ((continuous_apply i0).comp State.continuous_matrix)).mul
            ((continuous_apply jt).comp ((continuous_apply it).comp ih))

/-- Fixed tensor powers are continuous at the state level. -/
theorem tensorPower_continuous (n : ℕ) :
    Continuous (fun ρ : State a => ρ.tensorPower n) := by
  rw [continuous_induced_rng]
  exact tensorPower_matrix_continuous (a := a) n

/-- Fixed bipartite tensor powers are continuous as matrix-valued maps of the
input density state. -/
theorem tensorPowerBipartite_matrix_continuous (n : ℕ) :
    Continuous (fun ρ : State (Prod a b) => (ρ.tensorPowerBipartite n).matrix) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp [State.tensorPowerBipartite]
  exact (continuous_apply ((tensorPowerProdEquiv a b n).symm j)).comp
    ((continuous_apply ((tensorPowerProdEquiv a b n).symm i)).comp
      (tensorPower_matrix_continuous (a := Prod a b) n))

/-- Fixed bipartite tensor powers are continuous at the state level. -/
theorem tensorPowerBipartite_continuous (n : ℕ) :
    Continuous (fun ρ : State (Prod a b) => ρ.tensorPowerBipartite n) := by
  rw [continuous_induced_rng]
  exact tensorPowerBipartite_matrix_continuous (a := a) (b := b) n

/-- Bipartite tensor powers of the full-rank white-noise regularization tend
back to the tensor power of the original state. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        (if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (ρ.tensorPowerBipartite n)) :=
  (tensorPowerBipartite_continuous (a := a) (b := b) n).tendsto ρ |>.comp
    (finiteAEPFullRankRegularization_tendsto_zero ρ)

/-- Bipartite tensor powers of the full-rank regularization approach the
original tensor power in normalized trace distance. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_normalizedTraceDistance_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).normalizedTraceDistance
            (ρ.tensorPowerBipartite n))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
  have hcont :=
    finiteAEP_normalizedTraceDistance_continuous_left
      (a := TensorPower a n) (b := TensorPower b n) (ρ.tensorPowerBipartite n)
  simpa using hcont.tendsto (ρ.tensorPowerBipartite n) |>.comp
    (finiteAEPFullRankRegularization_tensorPowerBipartite_tendsto_zero ρ n)

/-- Bipartite tensor powers of the full-rank regularization approach the
original tensor power in purified distance. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_purifiedDistance_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).purifiedDistance
            (ρ.tensorPowerBipartite n))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
  have hD :=
    finiteAEPFullRankRegularization_tensorPowerBipartite_normalizedTraceDistance_tendsto_zero
      (a := a) (b := b) ρ n
  refine squeeze_zero
    (f := fun η : ℝ =>
      ((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
        ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
      else
        ρ).tensorPowerBipartite n).purifiedDistance
          (ρ.tensorPowerBipartite n))
    (g := fun η : ℝ =>
      Real.sqrt
        (2 *
          (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
            ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
          else
            ρ).tensorPowerBipartite n).normalizedTraceDistance
              (ρ.tensorPowerBipartite n))))
    (fun η => ?_) (fun η => ?_) ?_
  · simp [State.purifiedDistance_eq]
  · exact purifiedDistance_le_sqrt_two_mul_normalizedTraceDistance
      (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
        ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
      else
        ρ).tensorPowerBipartite n))
      (ρ.tensorPowerBipartite n)
  · simpa using (hD.const_mul (2 : ℝ)).sqrt

/-- The same convergence after viewing normalized states as subnormalized
states, matching the smoothing-ball center-migration API. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_toSubnormalized_purifiedDistance_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).toSubnormalized).purifiedDistance
            (ρ.tensorPowerBipartite n).toSubnormalized)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
  refine Filter.Tendsto.congr' ?_
    (finiteAEPFullRankRegularization_tensorPowerBipartite_purifiedDistance_tendsto_zero
      (a := a) (b := b) ρ n)
  filter_upwards with η
  rw [State.toSubnormalized_purifiedDistance_eq]

/-- Eventually the regularized tensor power lies in any prescribed
subnormalized purified-distance ball around the original tensor power. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_toSubnormalized_purifiedDistance_eventually_le
    (ρ : State (Prod a b)) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
      (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
        ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
      else
        ρ).tensorPowerBipartite n).toSubnormalized).purifiedDistance
          (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ := by
  have h :=
    finiteAEPFullRankRegularization_tensorPowerBipartite_toSubnormalized_purifiedDistance_tendsto_zero
      (a := a) (b := b) ρ n
  have hlt :
      ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
        (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).toSubnormalized).purifiedDistance
            (ρ.tensorPowerBipartite n).toSubnormalized < δ :=
    h.eventually (Iio_mem_nhds hδ)
  filter_upwards [hlt] with η hη
  exact le_of_lt hη

/-- Transfer an unnormalized finite-AEP lower bound from a full-rank
regularized tensor-power center back to the original center.

The scalar comparison hypothesis isolates the remaining regularization
analysis: once the regularized conditional-entropy and eta penalty are shown
to dominate the target right-hand side, center migration supplies the smooth
min-entropy part. -/
theorem finiteAEPFullRankRegularization_tensorLowerBound_transfer
    (ρ : State (Prod a b)) (n : ℕ)
    {ξ ε δ targetL regL : ℝ} (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter :
      ((ρ.finiteAEPFullRankRegularization ξ hξ.1.le hξ.2.le).tensorPowerBipartite n).toSubnormalized.purifiedDistance
        (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ)
    (hreg :
      regL ≤
        (ρ.finiteAEPFullRankRegularization ξ hξ.1.le hξ.2.le).tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n)
    (hscalar : targetL ≤ regL) :
    targetL ≤ ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy (ε + δ) n := by
  exact le_trans hscalar
    (tensorPowerSubnormalizedSmoothConditionalMinEntropy_lower_bound_of_center_migration
      (ρ := ρ)
      (η := ρ.finiteAEPFullRankRegularization ξ hξ.1.le hξ.2.le)
      (n := n) hε_nonneg hεδ_nonneg hεδ_lt hcenter hreg)

/-- Package an unnormalized tensor-power lower bound into the public finite-N
AEP statement surface with an explicit source parameter `η`.

This is the arbitrary-state assembly shell: subsequent support/regularization
work only has to provide the displayed tensor lower bound for each admissible
positive smoothing parameter and blocklength. -/
theorem finiteNAEP_statement_of_explicitEta_tensorLowerBound
    (ρ : State (Prod a b)) (ε η : ℝ) (hε_lt : ε < 1) (n : ℕ)
    (hcore :
      ∀ (_hε_pos : 0 < ε)
        (_hn : 0 < n)
        (_hn_ge : (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ)),
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n ≥
          (n : ℝ) * ρ.conditionalEntropy -
            finiteAEPDelta ε η * Real.sqrt (n : ℝ)) :
    QIT.finiteNAEP_statement ρ ε η n := by
  intro hε_pos hn_ge
  have hM : 0 < log2 (2 / ε ^ 2) :=
    finiteAEP_log2_two_div_sq_pos hε_pos hε_lt
  have hnR : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 5) hM) hn_ge
  have hn : 0 < n := by exact_mod_cast hnR
  have hbound := hcore hε_pos hn hn_ge
  exact
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε η)
      (n := n) hn hbound

/-- Positive-definite fixed-reference finite-AEP core with subnormalized
smooth-min witnesses.

This is the assembly form that matches the source-shaped `GρG†` construction:
the one-shot smooth-min/Petz bridge produces a subnormalized nearby witness,
while the alpha-to-von-Neumann estimate is the positive-definite core from
`AlphaEntropyContinuity`. -/
theorem relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (_hε_pos : 0 < ε)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hsmoothMinPetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
          ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hpetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        ρ.conditionalEntropyRelative hρ σ hσ -
          4 * (α - 1) *
            (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 :=
    conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      (ρ := ρ) hρ (σ := σ) hσ α hα_gt hα_lt
  linarith

/-- Full-reference finite-AEP one-copy core for arbitrary left states and a
positive-definite reference.

This combines the source-aligned smooth-min lower bound (`thm:entropy-ineq`)
with the support-indexed alpha-to-von-Neumann bound (`lemma:alpha-bound`) in the
full-rank-reference branch. -/
theorem relativeFiniteAEP_core_fullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameterTrace σ))) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelativeFullReference σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameterTrace σ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hsmooth :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
          ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε :=
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference
      σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
  have hpetz :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        ρ.conditionalEntropyRelativeFullReference σ hσ -
          4 * (α - 1) *
            (log2 (ρ.conditionalAlphaConvergenceParameterTrace σ)) ^ 2 :=
    conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
      (ρ := ρ) (σ := σ) hσ α hα_gt hα_lt
  linarith

/-- Positive-definite fixed-reference finite-AEP core from the source-shaped
`GρG†` smooth-min construction, reducing the remaining one-shot estimate to
the single Petz positive-part trace bound. -/
theorem relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  exact
    ρ.relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
      hρ σ hσ ε α hε_pos hα_gt hα_le_two hα_lt
      (ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
        hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two hpetz)

/-- Positive-definite fixed-reference finite-AEP core from the source-shaped
`GρG†` smooth-min construction, exposing the remaining noncommutative source
step as the Petz effect-variational inequality. -/
theorem relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hvar :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lam α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  exact
    ρ.relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
      hρ σ hσ ε α hε_pos hα_gt hα_le_two hα_lt
      (ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_effectVariational
        hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two hvar)

/-- Positive-definite fixed-reference finite-AEP core from the source-shaped
`GρG†` smooth-min construction, exposing the remaining noncommutative source
step as the Hilbert-Schmidt kernel dephasing monotonicity inequality. -/
theorem relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hkernel :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  exact
    ρ.relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
      hρ σ hσ ε α hε_pos hα_gt hα_le_two hα_lt
      (ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_kernelDephaseMonotone
        hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two hkernel)

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, still exposing the Petz positive-part trace estimate.

This is only a specialization of the fixed-reference core above.  The
positive-definiteness of `ρ_B` and the Petz trace bound remain assumptions. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.marginalB hρB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart ρ.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm ρ.marginalB α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.marginalB.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
      hρ ρ.marginalB hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hpetz
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, with the remaining source step expressed as the Petz
effect-variational inequality. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hvar :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.marginalB hρB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) ρ.marginalB) lam α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.marginalB.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
      hρ ρ.marginalB hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hvar
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, with the remaining source step expressed as the Hilbert-Schmidt
kernel dephasing monotonicity inequality. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hkernel :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.marginalB hρB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρ.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρ.marginalB hρB
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) ρ.marginalB
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ ρ.marginalB hρB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) ρ.marginalB) U α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.marginalB.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
      hρ ρ.marginalB hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hkernel
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Optimized scalar-choice finite-AEP core with explicit tensor-power
bookkeeping assumptions.

The state `ρn` is intentionally arbitrary: downstream tensor-power work should
instantiate it with `ρ_AB^{⊗ n}` and prove the displayed entropy and eta-growth
hypotheses.  The Petz positive-part trace estimate is still explicit. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρn.finiteAEPEta hρn hρnB)))
    (hentropy_tensor : ρn.conditionalEntropy = (n : ℝ) * H)
    (heta_tensor :
      (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        (n : ℝ) * (log2 η) ^ 2)
    (hpetz :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρn.fixedPetzThresholdPositivePart ρn.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.marginalB α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hcore :
      ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.marginalB.toSubnormalized ε ≥
        ρn.conditionalEntropy -
          4 *
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1) *
              (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 -
            (1 /
                (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1)) *
              log2 (2 / ε ^ 2) := by
    exact
      ρn.finiteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
        hρn hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two hα_lt hpetz
  rw [hentropy_tensor] at hcore
  have hcoeff_nonneg :
      0 ≤
        4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) := by
    nlinarith
  have hquad :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          ((n : ℝ) * (log2 η) ^ 2) :=
    mul_le_mul_of_nonneg_left heta_tensor hcoeff_nonneg
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  have hpenalty :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) ≤
        QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    calc
      4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2) ≤
          4 *
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1) *
              ((n : ℝ) * (log2 η) ^ 2) +
            (1 /
                (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1)) *
              log2 (2 / ε ^ 2) := by
        linarith
      _ =
          4 *
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1) *
              (n : ℝ) *
              (log2 η) ^ 2 +
            (1 /
                (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1)) *
              log2 (2 / ε ^ 2) := by
        ring
      _ = QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := hscalar
  linarith

/-- Optimized scalar-choice finite-AEP core with the remaining source step
expressed as the Petz effect-variational inequality. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρn.finiteAEPEta hρn hρnB)))
    (hentropy_tensor : ρn.conditionalEntropy = (n : ℝ) * H)
    (heta_tensor :
      (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        (n : ℝ) * (log2 η) ^ 2)
    (hvar :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) lam α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  let lam : ℝ :=
    ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  have hlam : 0 < lam := by
    simpa [lam] using
      ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  have hvar_lam :
      cMatrixPetzTraceEffectVariational ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) lam α := by
    simpa [lam, hα_gt] using hvar
  have hpetz :
      (ρn.fixedPetzThresholdPositivePart ρn.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.marginalB α :=
    ρn.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational
      hρn ρn.marginalB hρnB hlam hα_gt hα_le_two hvar_lam
  exact
    ρn.finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
      hρn hρnB ε η α H hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      hentropy_tensor heta_tensor
      (by simpa [lam, hα_gt] using hpetz)

/-- Optimized scalar-choice finite-AEP core with the remaining source step
expressed as Petz monotonicity under the threshold-eigenbasis dephasing map.

This is the same assembly as
`finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational`, but
it isolates the noncommutative Appendix input as the source-shaped
`cMatrixPetzTraceUnitaryDephaseMonotone` predicate instead of the stronger
effect-variational package. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρn.finiteAEPEta hρn hρnB)))
    (hentropy_tensor : ρn.conditionalEntropy = (n : ℝ) * H)
    (heta_tensor :
      (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        (n : ℝ) * (log2 η) ^ 2)
    (hmono :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α hα_pos
          hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρn.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.marginalB hρnB
      let Hmat : CMatrix (Prod a b) :=
        ρn.matrix - lam • identityTensorStateMatrix (a := a) ρn.marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) U α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ :=
    ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
        hα_pos hα_ne_one
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) ρn.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.marginalB hρnB
      let Hmat : CMatrix (Prod a b) :=
        ρn.matrix - lam • identityTensorStateMatrix (a := a) ρn.marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) U α := by
    simpa [lam, hα_gt, hα_pos, hα_ne_one, hlam] using hmono
  have hpetz :
      (ρn.fixedPetzThresholdPositivePart ρn.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.marginalB α :=
    ρn.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
      hρn ρn.marginalB hρnB hlam hα_gt hα_le_two hmono_lam
  exact
    ρn.finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
      hρn hρnB ε η α H hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      hentropy_tensor heta_tensor
      (by simpa [lam, hα_gt, hα_pos, hα_ne_one] using hpetz)

theorem tensorPowerBipartite_posDef_forFiniteAEP
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).matrix.PosDef :=
  State.tensorPowerBipartite_posDef_forAEP ρ hρ n

theorem tensorPowerBipartite_marginalB_posDef_forFiniteAEP
    (ρ : State (Prod a b)) (_hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
  State.tensorPowerBipartite_marginalB_posDef_forAEP ρ _hρ hρB n

theorem tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef := by
  rw [State.tensorPowerBipartite_marginalB ρ n]
  exact State.tensorPower_posDef hρB n

theorem tensorPowerBipartite_succ_grouped
    (ρ : State (Prod a b)) (n : ℕ) :
    ρ.tensorPowerBipartite (n + 1) =
      (ρ.prod (ρ.tensorPowerBipartite n)).reindex
        (conditionalPetzRenyiProductGroupingEquiv
          a b (TensorPower a n) (TensorPower b n)) := by
  ext x y
  rcases x with ⟨⟨xA, xsA⟩, ⟨xB, xsB⟩⟩
  rcases y with ⟨⟨yA, ysA⟩, ⟨yB, ysB⟩⟩
  simp [State.tensorPowerBipartite, State.tensorPower_succ,
    conditionalPetzRenyiProductGroupingEquiv, tensorPowerProdEquiv,
    State.prod, State.reindex, Matrix.kronecker, Matrix.kroneckerMap_apply]

theorem tensorPowerBipartite_succ_grouped_marginalB
    (ρ : State (Prod a b)) (n : ℕ) :
    (((ρ.prod (ρ.tensorPowerBipartite n)).reindex
        (conditionalPetzRenyiProductGroupingEquiv
          a b (TensorPower a n) (TensorPower b n))).marginalB) =
      ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
  ext x y
  rcases x with ⟨xB, xsB⟩
  rcases y with ⟨yB, ysB⟩
  simp [State.marginalB, partialTraceA, State.prod, State.reindex,
    conditionalPetzRenyiProductGroupingEquiv, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Applying two right-reference isometries before taking a product state is
the same as applying their product isometry after the standard regrouping. -/
theorem conditioningIsometryApply_prod_reindex_grouped
    {a' : Type*} {c : Type*} {bPlus : Type*} {cPlus : Type*}
    [Fintype a'] [DecidableEq a'] [Fintype c] [DecidableEq c]
    [Fintype bPlus] [DecidableEq bPlus] [Fintype cPlus] [DecidableEq cPlus]
    (ρ : State (Prod a b)) (σ : State (Prod a' c))
    (V : ReferenceIsometry b bPlus) (W : ReferenceIsometry c cPlus) :
    ((ρ.conditioningIsometryApply V).prod (σ.conditioningIsometryApply W)).reindex
        (conditionalPetzRenyiProductGroupingEquiv a bPlus a' cPlus) =
      State.conditioningIsometryApply
        ((ρ.prod σ).reindex (conditionalPetzRenyiProductGroupingEquiv a b a' c))
        (V.prod W) := by
  apply State.ext
  ext x y
  rcases x with ⟨⟨xA, xA'⟩, ⟨xB, xC⟩⟩
  rcases y with ⟨⟨yA, yA'⟩, ⟨yB, yC⟩⟩
  simp [State.prod, State.reindex, State.conditioningIsometryApply_matrix,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.prod, conditionalPetzRenyiProductGroupingEquiv,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.mul_apply,
    Matrix.conjTranspose, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  conv_lhs =>
    enter [2, z]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, z, 2, w]
    rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset b)) rfl ?_
  intro z _
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset c)) rfl ?_
  intro zc _
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset b)) rfl ?_
  intro zb _
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset c)) rfl ?_
  intro zw _
  ring_nf

/-- Tensor powers commute with applying a right-reference isometry to the
conditioning register, using the tensor-power product isometry on `B^n`. -/
theorem conditioningIsometryApply_tensorPowerBipartite
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    ∀ n : ℕ,
      (ρ.conditioningIsometryApply V).tensorPowerBipartite n =
        (ρ.tensorPowerBipartite n).conditioningIsometryApply (V.tensorPower n)
  | 0 => by
      apply State.ext
      ext x y
      rcases x with ⟨xA, xB⟩
      rcases y with ⟨yA, yB⟩
      cases xA
      cases xB
      cases yA
      cases yB
      simp [State.tensorPowerBipartite, State.tensorPower, State.reindex,
        State.conditioningIsometryApply_matrix, ReferenceIsometry.applyMatrixRight,
        ReferenceIsometry.rightBlock, ReferenceIsometry.tensorPower,
        Matrix.mul_apply, Matrix.conjTranspose, TensorPower, tensorPowerProdEquiv]
      rfl
  | n + 1 => by
      have ih := conditioningIsometryApply_tensorPowerBipartite ρ V n
      rw [State.tensorPowerBipartite_succ_grouped]
      rw [ih]
      rw [conditioningIsometryApply_prod_reindex_grouped]
      rw [← State.tensorPowerBipartite_succ_grouped]
      rfl

/-- Embedding normalized states as subnormalized states commutes with applying
a right-reference isometry. -/
theorem toSubnormalized_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).toSubnormalized =
      ρ.toSubnormalized.conditioningIsometryApply V := by
  apply SubnormalizedState.ext
  rw [State.toSubnormalized_matrix]
  rw [SubnormalizedState.conditioningIsometryApply_matrix]
  rw [State.conditioningIsometryApply_matrix]
  rfl

private theorem tensorPower_nonempty_of_nonempty {α : Type*} [Nonempty α] :
    ∀ n : ℕ, Nonempty (TensorPower α n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 => ⟨(Classical.choice ‹Nonempty α›,
      Classical.choice (tensorPower_nonempty_of_nonempty n))⟩

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ_of_regroupedCandidate
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ)
    (hregroup :
      (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ (n + 1))
          (ρ.tensorPowerBipartite (n + 1)).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB (n + 1))
          α hα_pos hα_ne_one =
        (((ρ.prod (ρ.tensorPowerBipartite n)).reindex
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n))).conditionalPetzRenyiEntropyCandidate
            (State.reindex_posDef_of_posDef
              (ρ.prod (ρ.tensorPowerBipartite n))
              (State.prod_posDef hρ
                (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n))
              (conditionalPetzRenyiProductGroupingEquiv
                a b (TensorPower a n) (TensorPower b n)))
            (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB)
            (State.prod_posDef hρB
              (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))
            α hα_pos hα_ne_one)) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ (n + 1))
        (ρ.tensorPowerBipartite (n + 1)).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α hα_pos hα_ne_one := by
  have hprod :=
    conditionalPetzRenyiEntropyCandidate_prod_grouped_posDef
      (ρ₁ := ρ) (σ₁ := ρ.marginalB)
      (ρ₂ := ρ.tensorPowerBipartite n)
      (σ₂ := (ρ.tensorPowerBipartite n).marginalB)
      hρ hρB
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      α hα_pos hα_ne_one
  exact hregroup.trans hprod

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ (n + 1))
        (ρ.tensorPowerBipartite (n + 1)).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α hα_pos hα_ne_one := by
  refine
    tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ_of_regroupedCandidate
      ρ hρ hρB α hα_pos hα_ne_one n ?_
  let τ : State (Prod (Prod a (TensorPower a n)) (Prod b (TensorPower b n))) :=
    (ρ.prod (ρ.tensorPowerBipartite n)).reindex
      (conditionalPetzRenyiProductGroupingEquiv
        a b (TensorPower a n) (TensorPower b n))
  have hτ :
      ρ.tensorPowerBipartite (n + 1) = τ :=
    tensorPowerBipartite_succ_grouped ρ n
  have hτB :
      τ.marginalB = ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
    simpa [τ] using tensorPowerBipartite_succ_grouped_marginalB ρ n
  have hτ_matrix :
      (ρ.tensorPowerBipartite (n + 1)).matrix = τ.matrix :=
    congrArg State.matrix hτ
  have hτ_matrix' :
      Matrix.submatrix (ρ.tensorPower (n + 1)).matrix
          (tensorPowerProdEquiv a b (n + 1)).symm
          (tensorPowerProdEquiv a b (n + 1)).symm =
        Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
          (conditionalPetzRenyiProductGroupingEquiv
            a b (TensorPower a n) (TensorPower b n)).symm
          (conditionalPetzRenyiProductGroupingEquiv
            a b (TensorPower a n) (TensorPower b n)).symm := by
    simpa [State.tensorPowerBipartite_matrix, τ, State.reindex_matrix] using hτ_matrix
  have hτB_matrix :
      (ρ.tensorPowerBipartite (n + 1)).marginalB.matrix =
        (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB).matrix := by
    simpa [← hτ] using congrArg State.matrix hτB
  have hτB_ref :
      identityTensorStateMatrix (a := TensorPower a (n + 1))
          (ρ.tensorPowerBipartite (n + 1)).marginalB =
        identityTensorStateMatrix (a := Prod a (TensorPower a n))
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB) := by
    ext i j
    by_cases hij : i.1 = j.1
    · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, hij]
      exact congrFun (congrFun hτB_matrix i.2) j.2
    · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, hij]
      intro h
      exact False.elim (hij h)
  dsimp [conditionalPetzRenyiEntropyCandidate, conditionalPetzRenyiTraceTerm]
  rw [hτ_matrix', hτB_ref]
  rfl

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_succ
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite (n + 1)).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.marginalB hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
          α hα_pos hα_ne_one := by
  let τ : State (Prod (Prod a (TensorPower a n)) (Prod b (TensorPower b n))) :=
    (ρ.prod (ρ.tensorPowerBipartite n)).reindex
      (conditionalPetzRenyiProductGroupingEquiv
        a b (TensorPower a n) (TensorPower b n))
  have hτ :
      ρ.tensorPowerBipartite (n + 1) = τ :=
    tensorPowerBipartite_succ_grouped ρ n
  have hτB :
      τ.marginalB = ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
    simpa [τ] using tensorPowerBipartite_succ_grouped_marginalB ρ n
  have hregroup :
      (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite (n + 1)).marginalB
          (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB (n + 1))
          α hα_pos hα_ne_one =
        τ.conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB)
          (State.prod_posDef hρB
            (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n))
          α hα_pos hα_ne_one := by
    have hτ_matrix :
        (ρ.tensorPowerBipartite (n + 1)).matrix = τ.matrix :=
      congrArg State.matrix hτ
    have hτ_matrix' :
        Matrix.submatrix (ρ.tensorPower (n + 1)).matrix
            (tensorPowerProdEquiv a b (n + 1)).symm
            (tensorPowerProdEquiv a b (n + 1)).symm =
          Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm := by
      simpa [State.tensorPowerBipartite_matrix, τ, State.reindex_matrix] using hτ_matrix
    have hτ_matrix_def :
        τ.matrix =
          Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm := by
      simp [τ, State.reindex_matrix]
    have hτB_matrix :
        (ρ.tensorPowerBipartite (n + 1)).marginalB.matrix =
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB).matrix := by
      simpa [← hτ] using congrArg State.matrix hτB
    have hτB_ref :
        identityTensorStateMatrix (a := TensorPower a (n + 1))
            (ρ.tensorPowerBipartite (n + 1)).marginalB =
          identityTensorStateMatrix (a := Prod a (TensorPower a n))
            (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB) := by
      ext i j
      by_cases hij : i.1 = j.1
      · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply, hij]
        exact congrFun (congrFun hτB_matrix i.2) j.2
      · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply, hij]
        intro h
        exact False.elim (hij h)
    dsimp [conditionalPetzRenyiEntropyCandidateFullReference, conditionalPetzRenyiTraceTerm]
    rw [hτ_matrix', hτB_ref, hτ_matrix_def]
    rfl
  have hprod :=
    conditionalPetzRenyiEntropyCandidateFullReference_prod_grouped
      (ρ₁ := ρ) (σ₁ := ρ.marginalB)
      (ρ₂ := ρ.tensorPowerBipartite n)
      (σ₂ := (ρ.tensorPowerBipartite n).marginalB)
      hρB
      (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
      α hα_pos hα_ne_one
  exact hregroup.trans hprod

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_zero
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ.tensorPowerBipartite 0).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ 0)
        (ρ.tensorPowerBipartite 0).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB 0)
        α hα_pos hα_ne_one = 0 := by
  have hmat :
      (ρ.tensorPowerBipartite 0).matrix =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    simp [State.tensorPowerBipartite, State.tensorPower, State.reindex,
      State.unit, TensorPower, tensorPowerProdEquiv]
  have hBmat :
      (ρ.tensorPowerBipartite 0).marginalB.matrix =
        (1 : CMatrix (TensorPower b 0)) := by
    ext x y
    cases x
    cases y
    change partialTraceA (a := TensorPower a 0) (b := TensorPower b 0)
        (ρ.tensorPowerBipartite 0).matrix PUnit.unit PUnit.unit =
      (1 : CMatrix (TensorPower b 0)) PUnit.unit PUnit.unit
    rw [hmat]
    simp [partialTraceA, TensorPower]
    change (1 : ℂ) = 1
    norm_num
  have href :
      identityTensorStateMatrix (a := TensorPower a 0)
          (ρ.tensorPowerBipartite 0).marginalB =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    change
      (Matrix.kronecker (1 : CMatrix (TensorPower a 0))
          (ρ.tensorPowerBipartite 0).marginalB.matrix)
        (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0)))
          (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit)
    rw [hBmat]
    simp [TensorPower, Matrix.kronecker, Matrix.kroneckerMap_apply]
    change (1 : ℂ) * 1 = 1
    norm_num
  unfold conditionalPetzRenyiEntropyCandidate
  rw [hmat, href]
  dsimp only
  change 1 / (1 - α) *
      log2 ((((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) *
        ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α))).trace.re) =
    0
  rw [show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) = 1 by
      exact CFC.one_rpow,
    show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α)) = 1 by
      exact CFC.one_rpow,
    one_mul, Matrix.trace_one]
  have hcard : Fintype.card (Prod (TensorPower a 0) (TensorPower b 0)) = 1 := by
    change Fintype.card (PUnit × PUnit) = 1
    simp
  simp [hcard, log2]

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_zero
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ.tensorPowerBipartite 0).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite 0).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB 0)
        α hα_pos hα_ne_one = 0 := by
  have hmat :
      (ρ.tensorPowerBipartite 0).matrix =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    simp [State.tensorPowerBipartite, State.tensorPower, State.reindex,
      State.unit, TensorPower, tensorPowerProdEquiv]
  have hBmat :
      (ρ.tensorPowerBipartite 0).marginalB.matrix =
        (1 : CMatrix (TensorPower b 0)) := by
    ext x y
    cases x
    cases y
    change partialTraceA (a := TensorPower a 0) (b := TensorPower b 0)
        (ρ.tensorPowerBipartite 0).matrix PUnit.unit PUnit.unit =
      (1 : CMatrix (TensorPower b 0)) PUnit.unit PUnit.unit
    rw [hmat]
    simp [partialTraceA, TensorPower]
    change (1 : ℂ) = 1
    norm_num
  have href :
      identityTensorStateMatrix (a := TensorPower a 0)
          (ρ.tensorPowerBipartite 0).marginalB =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    change
      (Matrix.kronecker (1 : CMatrix (TensorPower a 0))
          (ρ.tensorPowerBipartite 0).marginalB.matrix)
        (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0)))
          (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit)
    rw [hBmat]
    simp [TensorPower, Matrix.kronecker, Matrix.kroneckerMap_apply]
    change (1 : ℂ) * 1 = 1
    norm_num
  unfold conditionalPetzRenyiEntropyCandidateFullReference conditionalPetzRenyiTraceTerm
  rw [hmat, href]
  change 1 / (1 - α) *
      log2 ((((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) *
        ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α))).trace.re) =
    0
  rw [show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) = 1 by
      exact CFC.one_rpow,
    show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α)) = 1 by
      exact CFC.one_rpow,
    one_mul, Matrix.trace_one]
  have hcard : Fintype.card (Prod (TensorPower a 0) (TensorPower b 0)) = 1 := by
    change Fintype.card (PUnit × PUnit) = 1
    simp
  simp [hcard, log2]

/-- Conditional Petz alpha-entropy candidate is additive on bipartite tensor
powers relative to the corresponding tensor-power marginal reference. -/
theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_additive
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
        α hα_pos hα_ne_one =
      (n : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_zero
        ρ hρ hρB α hα_pos hα_ne_one]
      simp
  | succ n ih =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ
        ρ hρ hρB α hα_pos hα_ne_one n]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- Full-reference conditional Petz alpha-entropy candidate is additive on
bipartite tensor powers relative to the corresponding tensor-power marginal
reference, without requiring the left state to be full-rank. -/
theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_additive
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
        α hα_pos hα_ne_one =
      (n : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.marginalB hρB α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_zero
        ρ hρB α hα_pos hα_ne_one]
      simp
  | succ n ih =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_succ
        ρ hρB α hα_pos hα_ne_one n]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- Tensor-power alpha-to-von-Neumann lower bound using single-copy eta and
conditional Petz alpha-entropy additivity.

This is the source-shaped route for TCR finite AEP: apply the one-copy
alpha-bound and then use additivity of the fixed-reference conditional Petz
candidate, instead of bounding the tensor-power convergence parameter. -/
theorem tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) {n : ℕ}
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB))) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
      (n : ℝ) * ρ.conditionalEntropy -
        4 * (α - 1) * (n : ℝ) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  have hsingle :
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one ≥
        ρ.conditionalEntropy -
          4 * (α - 1) * (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
    have h :=
      conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
        (ρ := ρ) hρ (σ := ρ.marginalB) hρB α hα_gt
        (by simpa [finiteAEPEta_eq] using hα_lt)
    rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at h
    simpa [finiteAEPEta_eq, hα_pos, hα_ne_one] using h
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hmul :
      (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2) ≤
        (n : ℝ) *
          ρ.conditionalPetzRenyiEntropyCandidate
            hρ ρ.marginalB hρB α hα_pos hα_ne_one :=
    mul_le_mul_of_nonneg_left hsingle hn_nonneg
  calc
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
        = (n : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidate
              hρ ρ.marginalB hρB α hα_pos hα_ne_one := by
          simpa [hα_pos, hα_ne_one] using
            tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_additive
              ρ hρ hρB α hα_pos hα_ne_one n
    _ ≥
        (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2) := hmul
    _ =
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
          ring

/-- Full-reference tensor-power alpha-to-von-Neumann lower bound using the
single-copy trace eta.

This is the arbitrary-left-state analogue of
`tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef`: the
joint tensor-power state is not assumed full-rank, while the canonical side
reference is propagated as a full-rank marginal reference. -/
theorem tensorPower_conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) {n : ℕ}
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace)) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
      (n : ℝ) * ρ.conditionalEntropy -
        4 * (α - 1) * (n : ℝ) *
          (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  have hsingle :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.marginalB hρB α hα_pos hα_ne_one ≥
        ρ.conditionalEntropy -
          4 * (α - 1) * (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
    have h :=
      conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
        (ρ := ρ) (σ := ρ.marginalB) hρB α hα_gt
        (by simpa [finiteAEPEtaTrace] using hα_lt)
    rw [ρ.conditionalEntropyRelativeFullReference_to_conditionalEntropy hρB] at h
    simpa [finiteAEPEtaTrace, hα_pos, hα_ne_one] using h
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hmul :
      (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 ρ.finiteAEPEtaTrace) ^ 2) ≤
        (n : ℝ) *
          ρ.conditionalPetzRenyiEntropyCandidateFullReference
            ρ.marginalB hρB α hα_pos hα_ne_one :=
    mul_le_mul_of_nonneg_left hsingle hn_nonneg
  calc
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
        = (n : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidateFullReference
              ρ.marginalB hρB α hα_pos hα_ne_one := by
          simpa [hα_pos, hα_ne_one] using
            tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_additive
              ρ hρB α hα_pos hα_ne_one n
    _ ≥
        (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 ρ.finiteAEPEtaTrace) ^ 2) := hmul
    _ =
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
          ring

/-- Optimized scalar-choice fixed-reference finite-AEP core from a
full-reference tensor/source-shaped Petz alpha lower bound.

The left state is arbitrary.  The only reference-side hypothesis is that the
fixed side reference is full-rank, which is enough for the full-reference
smooth-min/Petz lower bound. -/
theorem finiteAEP_core_fullReference_optimized_petzAlphaBound
    (ρn : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hpetz_alpha :
      ρn.conditionalPetzRenyiEntropyCandidateFullReference
          σ hσ α
          (by
            rw [hα_opt]
            have hden :
                0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
              exact mul_pos (mul_pos (by norm_num) hL)
                (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
            have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
              Real.sqrt_pos.mpr hM
            have hfrac :
                0 <
                  Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) :=
              div_pos hnum hden
            linarith)
          (by
            have hα_gt : 1 < α := by
              rw [hα_opt]
              have hden :
                  0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
                exact mul_pos (mul_pos (by norm_num) hL)
                  (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
              have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
                Real.sqrt_pos.mpr hM
              have hfrac :
                  0 <
                    Real.sqrt (log2 (2 / ε ^ 2)) /
                      (2 * log2 η * Real.sqrt (n : ℝ)) :=
                div_pos hnum hden
              linarith
            exact (ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H - 4 * (α - 1) * (n : ℝ) * (log2 η) ^ 2) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hsmooth :
      ρn.conditionalPetzRenyiEntropyCandidateFullReference σ hσ
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference
        σ hσ ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidateFullReference σ hσ
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H -
          4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1) *
            (n : ℝ) * (log2 η) ^ 2 := by
    simpa [hα_gt] using hpetz_alpha
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  calc
    ρn.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      (n : ℝ) * H -
        (4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (n : ℝ) *
            (log2 η) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2)) := by
        linarith
    _ = (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
        rw [hscalar]

/-- Tensor-power optimized finite-AEP core for arbitrary left state and
full-rank canonical marginal reference.

This is the full-reference source route: smooth-min is bounded by the
full-reference Petz candidate, while the Petz alpha term is tensorized by
additivity and the one-copy trace eta. -/
theorem tensorPowerFiniteAEP_core_fullReference_optimized_additivePetz
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace)) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
          Real.sqrt (n : ℝ) := by
  have hη3 : 3 ≤ ρ.finiteAEPEtaTrace := by
    simpa [finiteAEPEtaTrace] using
      conditionalAlphaConvergenceParameterTrace_ge_three
        (ρ := ρ) (σ := ρ.marginalB) hρB
  have hL : 0 < log2 ρ.finiteAEPEtaTrace := by
    unfold log2
    exact div_pos
      (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hη3))
      (Real.log_pos one_lt_two)
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  have hpetz_alpha :
      (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 ρ.finiteAEPEtaTrace) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
      hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_fullReference_optimized_petzAlphaBound
      (ρ.tensorPowerBipartite n).marginalB
      (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
      ε ρ.finiteAEPEtaTrace α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha

/-- Tensor-power optimized finite-AEP core for optimized subnormalized smooth
min-entropy, using only a full-rank canonical marginal reference. -/
theorem tensorPowerFiniteAEP_core_fullReference_optimized_subnormalizedSmooth_additivePetz
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace)) :
    (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
          Real.sqrt (n : ℝ) := by
  have hfixedCore :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_fullReference_optimized_additivePetz
      hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt
  have hbridge :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≤
        (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε :=
    (ρ.tensorPowerBipartite n)
      |>.smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε
        hε_pos.le hε_lt
        (fun ρ' _hball =>
          SubnormalizedState.conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
            (a := TensorPower a n) ρ' (ρ.tensorPowerBipartite n).marginalB
            (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n))
  exact le_trans hfixedCore hbridge

/-- Optimized scalar-choice finite-AEP core from a tensor/source-shaped Petz
alpha-bound.

Compared with
`finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational`, this
assembly lemma does not assume a tensor-power eta growth estimate.  It only
needs the already tensorized alpha-to-von-Neumann lower bound with the
single-copy eta parameter. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hpetz_alpha :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB α
          (by
            rw [hα_opt]
            have hden :
                0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
              exact mul_pos (mul_pos (by norm_num) hL)
                (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
            have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
              Real.sqrt_pos.mpr hM
            have hfrac :
                0 <
                  Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) :=
              div_pos hnum hden
            linarith)
          (by
            have hα_gt : 1 < α := by
              rw [hα_opt]
              have hden :
                  0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
                exact mul_pos (mul_pos (by norm_num) hL)
                  (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
              have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
                Real.sqrt_pos.mpr hM
              have hfrac :
                  0 <
                    Real.sqrt (log2 (2 / ε ^ 2)) /
                      (2 * log2 η * Real.sqrt (n : ℝ)) :=
                div_pos hnum hden
              linarith
            exact (ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H - 4 * (α - 1) * (n : ℝ) * (log2 η) ^ 2)
    (hvar :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) lam α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hsmooth :
      (ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.marginalB.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_effectVariational
        hρn ρn.marginalB hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
        (by simpa [hα_gt] using hvar)
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H -
          4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1) *
            (n : ℝ) * (log2 η) ^ 2 := by
    simpa [hα_gt] using hpetz_alpha
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  calc
    ρn.smoothConditionalMinEntropyFixedSubnormalized
        ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H -
        (4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (n : ℝ) *
            (log2 η) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2)) := by
        linarith
    _ = (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
        rw [hscalar]

/-- Optimized scalar-choice finite-AEP core from a tensor/source-shaped Petz
alpha lower bound, with the one-shot source step isolated as threshold-basis
Petz dephasing monotonicity.

This is the `cMatrixPetzTraceUnitaryDephaseMonotone` version of
`finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound`.
It keeps the remaining noncommutative Appendix input at the dephasing
monotonicity level, without asking callers to provide the stronger
effect-variational package. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_petzAlphaBound
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hpetz_alpha :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB α
          (by
            rw [hα_opt]
            have hden :
                0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
              exact mul_pos (mul_pos (by norm_num) hL)
                (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
            have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
              Real.sqrt_pos.mpr hM
            have hfrac :
                0 <
                  Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) :=
              div_pos hnum hden
            linarith)
          (by
            have hα_gt : 1 < α := by
              rw [hα_opt]
              have hden :
                  0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
                exact mul_pos (mul_pos (by norm_num) hL)
                  (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
              have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
                Real.sqrt_pos.mpr hM
              have hfrac :
                  0 <
                    Real.sqrt (log2 (2 / ε ^ 2)) /
                      (2 * log2 η * Real.sqrt (n : ℝ)) :=
                div_pos hnum hden
              linarith
            exact (ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H - 4 * (α - 1) * (n : ℝ) * (log2 η) ^ 2)
    (hmono :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α hα_pos
          hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρn.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.marginalB hρnB
      let Hmat : CMatrix (Prod a b) :=
        ρn.matrix - lam • identityTensorStateMatrix (a := a) ρn.marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) U α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hsmooth :
      (ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.marginalB.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
        hρn ρn.marginalB hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
        (by simpa [hα_gt] using hmono)
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H -
          4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1) *
            (n : ℝ) * (log2 η) ^ 2 := by
    simpa [hα_gt] using hpetz_alpha
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  calc
    ρn.smoothConditionalMinEntropyFixedSubnormalized
        ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H -
        (4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (n : ℝ) *
            (log2 η) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2)) := by
        linarith
    _ = (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
        rw [hscalar]

/-- Tensor-power optimized finite-AEP core using conditional Petz alpha-entropy
additivity and the single-copy eta parameter.

The remaining assumption is the one-shot Petz dephasing monotonicity in the
threshold eigenbasis for the tensor-power state.  This is the narrow
source-shaped replacement for the `hvar` assumption in
`tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_additivePetz`. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hmono :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
          ρ.log2_finiteAEPEta_pos hρ hρB
        have hden :
            0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB hρnB
      let Hmat : CMatrix (Prod (TensorPower a n) (TensorPower b n)) :=
        (ρ.tensorPowerBipartite n).matrix -
          lam • identityTensorStateMatrix (a := TensorPower a n)
            (ρ.tensorPowerBipartite n).marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
            hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod (TensorPower a n) (TensorPower b n)) ℂ :=
        hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) U α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
    ρ.log2_finiteAEPEta_pos hρ hρB
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  have hpetz_alpha :
      (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      hρ hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_petzAlphaBound
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      ε (ρ.finiteAEPEta hρ hρB) α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha hmono

/-- Tensor-power optimized finite-AEP core for the optimized subnormalized
smooth min-entropy around the embedded normalized tensor-power state.

This combines the fixed-reference tensor-power AEP core with the order bridge
from fixed-reference subnormalized smoothing to optimized subnormalized
smoothing.  The fixed-reference feasible-set nonemptiness is supplied by the
positive-definite tensor-power marginal, so the remaining source-shaped
assumption is Petz dephasing monotonicity in the threshold eigenbasis. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_unitaryDephaseMonotone_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hmono :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
          ρ.log2_finiteAEPEta_pos hρ hρB
        have hden :
            0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB hρnB
      let Hmat : CMatrix (Prod (TensorPower a n) (TensorPower b n)) :=
        (ρ.tensorPowerBipartite n).matrix -
          lam • identityTensorStateMatrix (a := TensorPower a n)
            (ρ.tensorPowerBipartite n).marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
            hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod (TensorPower a n) (TensorPower b n)) ℂ :=
        hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) U α) :
    (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  have hfixedCore :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt hmono
  have hbridge :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≤
        (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε :=
    (ρ.tensorPowerBipartite n)
      |>.smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε
        hε_pos.le hε_lt
        (fun ρ' _hball =>
          SubnormalizedState.conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
            (a := TensorPower a n) ρ' (ρ.tensorPowerBipartite n).marginalB
            (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))
  exact le_trans hfixedCore hbridge

/-- Tensor-power optimized finite-AEP core from a global finite-uniform Petz
joint-convexity input on the tensor-power matrix dimension.

The remaining hypothesis `hjoint` is the precise noncommutative
perspective/joint-convexity theorem still needed for the source proof route.
All tensor-power bookkeeping, alpha-continuity, scalar optimization, and
subnormalized smoothing bridges are discharged here. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hjoint :
      ∀ {κ : Type (max u v)} [Fintype κ] [Nonempty κ],
        (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) →
          cMatrixPetzTraceUniformJointConvex Aκ Bκ α) :
    (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  refine
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_unitaryDephaseMonotone_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt ?_
  dsimp
  let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
    tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
  let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
    tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
  let hα_gt : 1 < α := by
    rw [hα_opt]
    have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
      ρ.log2_finiteAEPEta_pos hρ hρB
    have hden :
        0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ :=
    (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
      hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one
  let hB : (identityTensorStateMatrix (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).marginalB).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).marginalB hρnB
  let Hmat : CMatrix (Prod (TensorPower a n) (TensorPower b n)) :=
    (ρ.tensorPowerBipartite n).matrix -
      lam • identityTensorStateMatrix (a := TensorPower a n)
        (ρ.tensorPowerBipartite n).marginalB
  let hH : Hmat.IsHermitian :=
    hρn.isHermitian.sub ((Matrix.PosDef.smul hB
      ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
        hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one)
    ).isHermitian)
  let U : Matrix.unitaryGroup (Prod (TensorPower a n) (TensorPower b n)) ℂ :=
    hH.eigenvectorUnitary
  exact cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex_all
    (ρ.tensorPowerBipartite n).matrix
    (identityTensorStateMatrix (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).marginalB)
    hρn.posSemidef hB U hα_gt hα_le_two hjoint

/-- Tensor-power optimized finite-AEP core with the Petz joint-convexity input
discharged by the finite-dimensional rpow perspective theorem. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_rpow_perspective_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB))) :
    (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  refine
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt ?_
  intro κ _ _ Aκ Bκ
  exact cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two Aκ Bκ

/-- Positive-definite finite-N AEP statement from the remaining universal Petz
joint-convexity input.

This theorem connects the source-aligned public statement surface to the
proved tensor-power core.  The only analytic input still left explicit is the
finite-uniform joint convexity of the Petz trace on the tensor-power matrix
dimension; the optimized alpha choice, source blocklength condition, and
normalization by `n` are all discharged here. -/
theorem finiteNAEP_statement_posDef_of_uniformJointConvex_all
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_lt : ε < 1) (n : ℕ)
    (hjoint :
      ∀ {κ : Type (max u v)} [Fintype κ] [Nonempty κ],
        (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) →
          cMatrixPetzTraceUniformJointConvex Aκ Bκ
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))) :
    QIT.finiteNAEP_statement ρ ε (ρ.finiteAEPEta hρ hρB) n := by
  intro hε_pos hn_ge
  let α : ℝ :=
    1 + Real.sqrt (log2 (2 / ε ^ 2)) /
      (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ))
  have hM : 0 < log2 (2 / ε ^ 2) :=
    finiteAEP_log2_two_div_sq_pos hε_pos hε_lt
  have hM_nonneg : 0 ≤ log2 (2 / ε ^ 2) := le_of_lt hM
  have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
    ρ.log2_finiteAEPEta_pos hρ hρB
  have hη3 : 3 ≤ ρ.finiteAEPEta hρ hρB :=
    ρ.three_le_finiteAEPEta hρ hρB
  have hnR : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 5) hM) hn_ge
  have hn : 0 < n := by exact_mod_cast hnR
  have hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) := rfl
  have hα_le_two : α ≤ 2 := by
    simpa [α] using
      finiteAEP_alpha_le_two_of_n_ge ε (ρ.finiteAEPEta hρ hρB)
        hM_nonneg hL hη3 hn hn_ge
  have hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)) := by
    simpa [α] using
      finiteAEP_alpha_window_of_n_ge ε (ρ.finiteAEPEta hρ hρB)
        hM_nonneg hL hn hn_ge
  have hcore :
      (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
            Real.sqrt (n : ℝ) :=
    have hjointAlpha :
        ∀ {κ : Type (max u v)} [Fintype κ] [Nonempty κ],
          (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) →
            cMatrixPetzTraceUniformJointConvex Aκ Bκ α := by
      intro κ _ _ Aκ Bκ
      simpa [α] using hjoint (κ := κ) Aκ Bκ
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt hjointAlpha
  simpa [State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq] using
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB))
      (n := n) hn hcore

/-- Finite-N AEP statement using only the full-rank marginal reference and the
trace-term eta parameter. -/
theorem finiteNAEP_statement_traceEta_of_marginal_posDef
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε ρ.finiteAEPEtaTrace n := by
  intro hε_pos hn_ge
  let α : ℝ :=
    1 + Real.sqrt (log2 (2 / ε ^ 2)) /
      (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ))
  have hM : 0 < log2 (2 / ε ^ 2) :=
    finiteAEP_log2_two_div_sq_pos hε_pos hε_lt
  have hM_nonneg : 0 ≤ log2 (2 / ε ^ 2) := le_of_lt hM
  have hη3 : 3 ≤ ρ.finiteAEPEtaTrace := by
    simpa [finiteAEPEtaTrace] using
      conditionalAlphaConvergenceParameterTrace_ge_three
        (ρ := ρ) (σ := ρ.marginalB) hρB
  have hL : 0 < log2 ρ.finiteAEPEtaTrace := by
    unfold log2
    exact div_pos
      (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hη3))
      (Real.log_pos one_lt_two)
  have hnR : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 5) hM) hn_ge
  have hn : 0 < n := by exact_mod_cast hnR
  have hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)) := rfl
  have hα_le_two : α ≤ 2 := by
    simpa [α] using
      finiteAEP_alpha_le_two_of_n_ge ε ρ.finiteAEPEtaTrace
        hM_nonneg hL hη3 hn hn_ge
  have hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace) := by
    simpa [α] using
      finiteAEP_alpha_window_of_n_ge ε ρ.finiteAEPEtaTrace
        hM_nonneg hL hn hn_ge
  have hcore :
      (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_fullReference_optimized_subnormalizedSmooth_additivePetz
      hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt
  simpa [State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq] using
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace)
      (n := n) hn hcore

/-- Tensor-power subnormalized smooth min-entropy is unchanged by compressing
the conditioning register to the support of the canonical marginal and applying
the tensor-power support isometry back, with the same smoothing radius. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropy_conditioningSupportCompressedState
    (ρ : State (Prod a b)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    ρ.conditioningSupportCompressedState.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n =
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n := by
  let ρc := ρ.conditioningSupportCompressedState
  let V : ReferenceIsometry (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) b :=
    psdSupportReferenceIsometry ρ.marginalB.matrix ρ.marginalB.pos
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  haveI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  haveI : Nonempty (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) :=
    ⟨(Classical.choice ρc.nonempty).2⟩
  haveI : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
  haveI : Nonempty (TensorPower b n) := tensorPower_nonempty_of_nonempty n
  haveI :
      Nonempty (TensorPower (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) n) :=
    tensorPower_nonempty_of_nonempty n
  have hε_sqrt :
      ε < Real.sqrt ((ρc.tensorPowerBipartite n).toSubnormalized.matrix.trace.re) := by
    rw [State.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hsmooth :=
    SubnormalizedState.smoothConditionalMinEntropy_conditioningIsometryApply
      (a := TensorPower a n)
      (ρ := (ρc.tensorPowerBipartite n).toSubnormalized)
      (V := V.tensorPower n) hε0 hε_sqrt
  have htensorState :
      (ρc.tensorPowerBipartite n).conditioningIsometryApply (V.tensorPower n) =
        ρ.tensorPowerBipartite n := by
    calc
      (ρc.tensorPowerBipartite n).conditioningIsometryApply (V.tensorPower n) =
          (ρc.conditioningIsometryApply V).tensorPowerBipartite n := by
            rw [State.conditioningIsometryApply_tensorPowerBipartite]
      _ = ρ.tensorPowerBipartite n := by
            rw [show ρc.conditioningIsometryApply V = ρ from by
              simpa [ρc, V] using
                State.conditioningSupportCompressedState_conditioningIsometryApply (ρ := ρ)]
  have hsubState :
      (ρc.tensorPowerBipartite n).toSubnormalized.conditioningIsometryApply
          (V.tensorPower n) =
        (ρ.tensorPowerBipartite n).toSubnormalized := by
    rw [← State.toSubnormalized_conditioningIsometryApply]
    rw [htensorState]
  rw [State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq,
    State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq]
  rw [← hsubState]
  exact hsmooth.symm

/-- Arbitrary-state finite-N AEP with the trace-term eta parameter, obtained
from the full-rank-marginal theorem by support compression of the conditioning
register. -/
theorem finiteNAEP_statement_traceEta
    (ρ : State (Prod a b)) (ε : ℝ) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε ρ.finiteAEPEtaTrace n := by
  let ρc := ρ.conditioningSupportCompressedState
  have hcompressed :
      QIT.finiteNAEP_statement ρc ε ρc.finiteAEPEtaTrace n :=
    finiteNAEP_statement_traceEta_of_marginal_posDef
      (ρ := ρc) (State.conditioningSupportCompressedState_marginalB_posDef ρ)
      ε hε_lt n
  intro hε_pos hn_ge
  have hε0 : 0 ≤ ε := le_of_lt hε_pos
  have hbound := hcompressed hε_pos hn_ge
  rw [← State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_conditioningSupportCompressedState
    ρ ε hε0 hε_lt n]
  rw [← State.conditionalEntropy_conditioningSupportCompressedState ρ]
  rw [← State.finiteAEPEtaTrace_conditioningSupportCompressedState ρ]
  exact hbound

/-- The finite-N AEP theorem supplies the lower half of the source proof of
the asymptotic fully quantum AEP.

This is the Lean version of the first step in TCR 2008, proof of
`thm:qaep`: after the final tolerance is fixed, for all sufficiently small
positive smoothing radii and sufficiently large blocklengths, the normalized
smooth-min rate is at least `H(A|B)_ρ` up to that tolerance. -/
theorem SmoothMinRateLowerFromFiniteNAEP_traceEta
    (ρ : State (Prod a b)) :
    ρ.SmoothMinRateLowerFromFiniteNAEP := by
  intro γ hγ
  have hε_pos :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε := by
    exact self_mem_nhdsWithin
  have hε_lt_one :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hε_pos, hε_lt_one] with ε hε_pos hε_lt_one
  have hdelta_tend :
      Tendsto
        (fun n : ℕ => QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace / Real.sqrt (n : ℝ))
        atTop (nhds 0) :=
    QIT.finiteAEPDelta_div_sqrt_tendsto_zero ε ρ.finiteAEPEtaTrace
  have hdelta_small :
      ∀ᶠ n : ℕ in atTop,
        QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace / Real.sqrt (n : ℝ) < γ := by
    exact hdelta_tend.eventually (Iio_mem_nhds hγ)
  have hn_ge :
      ∀ᶠ n : ℕ in atTop,
        (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ) := by
    refine eventually_atTop.2 ⟨Nat.ceil ((8 / 5 : ℝ) * log2 (2 / ε ^ 2)), ?_⟩
    intro n hn
    exact (Nat.le_ceil ((8 / 5 : ℝ) * log2 (2 / ε ^ 2))).trans
      (by exact_mod_cast hn)
  filter_upwards [hdelta_small, hn_ge] with n hdelta_small hn_ge
  have hfinite := finiteNAEP_statement_traceEta ρ ε hε_lt_one n hε_pos hn_ge
  change ρ.conditionalEntropy - γ ≤
    (1 / (n : ℝ)) * ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n
  linarith

/-- AFW continuity supplies the upper half of the source proof of TCR
`thm:qaep`.

The endpoint ordering `H_min ≤ H` is the only order input needed by
`AEP.lean`; the preceding support-log residual and padding lemmas prove it for
the optimized conditional min-entropy without a full-rank assumption. -/
theorem SmoothMinRateUpperFromContinuity.afw
    (ρ : State (Prod a b)) :
    ρ.SmoothMinRateUpperFromContinuity :=
  State.SmoothMinRateUpperFromContinuity.afw_of_tensorPower_ordering ρ
    (by
      intro n τ
      exact τ.conditionalMinEntropy_le_conditionalEntropy)

/-- Source-aligned min-entropy half of the asymptotic AEP, with the finite-N
lower bound discharged by the finite-AEP theorem and the AFW/Fannes upper
handoff left explicit. -/
theorem asymptoticAEPMin_statement_of_traceEta_and_continuity
    (ρ : State (Prod a b))
    (hupper : ρ.SmoothMinRateUpperFromContinuity) :
    SourceTwoStageLimitTo
      (fun ε n => ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate ε n)
      ρ.conditionalEntropy :=
  ρ.asymptoticAEPMin_statement_of_finiteNAEP_and_continuity
    (ρ.SmoothMinRateLowerFromFiniteNAEP_traceEta) hupper

/-- Smooth min/max duality supplies the source max-entropy half of TCR
`thm:qaep` once the min-entropy half is available on every finite complement. -/
theorem SmoothMaxRateFromMinDuality.smoothDuality
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.SmoothMaxRateFromMinDuality := by
  refine State.SmoothMaxRateFromMinDuality.of_all_min ρ ?_
  intro c _ _ _ σ
  exact σ.asymptoticAEPMin_statement_of_traceEta_and_continuity
    (State.SmoothMinRateUpperFromContinuity.afw σ)

/-- Source-aligned assembly theorem for the asymptotic fully quantum AEP.

The finite-N lower half is supplied by the finite-AEP theorem.  The remaining
two inputs are exactly the source proof's later ingredients: ordering plus
AFW/Fannes continuity for the min upper half, and smooth min/max plus von
Neumann duality for the max half. -/
theorem asymptoticAEP_statement_of_traceEta_continuity_and_duality
    (ρ : State (Prod a b))
    (hupper : ρ.SmoothMinRateUpperFromContinuity)
    (hmax : ρ.SmoothMaxRateFromMinDuality) :
    QIT.asymptoticAEP_statement ρ :=
  ρ.asymptoticAEP_statement_of_min_and_max_duality
    (ρ.asymptoticAEPMin_statement_of_traceEta_and_continuity hupper) hmax

/-- Fully quantum asymptotic equipartition property, TCR 2008 `thm:qaep`.

The proof follows the source route: finite-N AEP gives the smooth-min lower
limit, AFW continuity and `H_min ≤ H` give the smooth-min upper limit, and
smooth min/max duality plus conditional-entropy duality gives the max-entropy
limit. -/
theorem fullyQuantumAsymptoticEquipartitionProperty
    (ρ : State (Prod a b)) :
    QIT.asymptoticAEP_statement ρ := by
  letI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  letI : Nonempty b := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  exact ρ.asymptoticAEP_statement_of_traceEta_continuity_and_duality
    (State.SmoothMinRateUpperFromContinuity.afw ρ)
    (State.SmoothMaxRateFromMinDuality.smoothDuality ρ)

/-- Positive-definite finite-N AEP statement with Petz joint convexity
discharged by the finite-dimensional rpow perspective theorem. -/
theorem finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε (ρ.finiteAEPEta hρ hρB) n :=
  ρ.finiteNAEP_statement_posDef_of_uniformJointConvex_all
    hρ hρB ε hε_lt n
    (fun {κ} [Fintype κ] [Nonempty κ]
        (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) =>
      cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two Aκ Bκ)

/-- Explicit-`η` spelling of the positive-definite finite-N AEP theorem.

This keeps the public statement parameter separate from the current
positive-definite implementation of the source convergence parameter. -/
theorem finiteNAEP_statement_posDef_explicitEta_of_rpow_perspective_one_two
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (η ε : ℝ) (hη : η = ρ.finiteAEPEta hρ hρB)
    (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε η n := by
  subst η
  exact ρ.finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    hρ hρB ε hε_lt n

/-- Positive-definite finite-N AEP using the arbitrary-state trace-term eta
spelling of `Upsilon(A|B)_{rho|rho}`. -/
theorem finiteNAEP_statement_posDef_traceEta_of_rpow_perspective_one_two
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε ρ.finiteAEPEtaTrace n := by
  rw [← ρ.finiteAEPEta_eq_trace hρ hρB]
  exact ρ.finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    hρ hρB ε hε_lt n

/-- Tensor-power optimized finite-AEP core using conditional Petz alpha-entropy
additivity and the single-copy eta parameter.

The remaining assumptions are the single-copy alpha window and the one-shot
Petz effect-variational inequality.  No tensor-power eta square bound is
assumed. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hvar :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
          ρ.log2_finiteAEPEta_pos hρ hρB
        have hden :
            0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) lam α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
    ρ.log2_finiteAEPEta_pos hρ hρB
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  have hpetz_alpha :
      (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      hρ hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      ε (ρ.finiteAEPEta hρ hρB) α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha hvar

/-- Tensor-power instantiation of the optimized positive-definite finite-AEP
core.

This theorem discharges the tensor-power positive-definiteness bookkeeping for
`ρ_AB^{⊗ n}`, its `B^n` marginal, and conditional entropy additivity.  The eta
growth, alpha-window, and Petz effect-variational inputs remain explicit. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε η α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ((ρ.tensorPowerBipartite n).finiteAEPEta
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))))
    (heta_tensor :
      (log2 ((ρ.tensorPowerBipartite n).finiteAEPEta
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))) ^ 2 ≤
          (n : ℝ) * (log2 η) ^ 2)
    (hvar :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) lam α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      ε η α ρ.conditionalEntropy hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      (State.tensorPowerBipartite_conditionalEntropy ρ n) heta_tensor hvar

/-- Honest positive-definite fixed-reference finite-AEP core.

This combines the TCR alpha-to-von-Neumann estimate already proved in
`conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef` with an explicit
one-shot smooth-min/Petz lower-bound hypothesis.  That hypothesis is precisely
the missing fixed-reference analogue of TCR 2008 `thm:entropy-ineq`, lines
630--633; this theorem does not claim that bridge as proved. -/
theorem relativeFiniteAEP_core_posDef_of_smoothMinPetzBound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (_hε_pos : 0 < ε)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hsmoothMinPetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
          ρ.smoothConditionalMinEntropyFixed σ ε) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hpetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        ρ.conditionalEntropyRelative hρ σ hσ -
          4 * (α - 1) *
            (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 :=
    conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      (ρ := ρ) hρ (σ := σ) hσ α hα_gt hα_lt
  linarith

/-- Positive-definite fixed-reference finite-AEP core from a concrete
Petz-threshold operator-order smoothed witness.

Compared with `relativeFiniteAEP_core_posDef_of_smoothMinPetzBound`, this
removes the broad smooth-min/Petz lower-bound hypothesis and leaves the smaller
source construction: find `ρ'` in the purified ball below the fixed-reference
Petz threshold scale. -/
theorem relativeFiniteAEP_core_posDef_of_petz_feasible_witness
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε)
    (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hconstruct :
      ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
        ρ'.matrix ≤
          ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
            identityTensorStateMatrix (a := a) σ) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  rcases hconstruct with ⟨ρ', hball, hbound⟩
  exact relativeFiniteAEP_core_posDef_of_smoothMinPetzBound
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hα_gt hα_le_two hα_lt
    (smoothConditionalMinEntropyFixed_lower_bound_of_petz_operator_bound
      (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
      ρ' hball hbound)

end State

end

end QIT
