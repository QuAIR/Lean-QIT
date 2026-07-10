/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiDPI
public import QIT.HypothesisTesting.Audenaert
public import QIT.Util.BlockMatrix
public import Mathlib.Data.EReal.Basic

/-!
# Frank--Lieb low-alpha sandwiched Renyi Q support

Helpers for the Frank--Lieb/Lieb low-`alpha` theorem route for the
matrix-level sandwiched Renyi `Q` functional.  The source theorem is
Tomamichel2015FiniteResources, `renyi.tex:811-841`: for
`alpha in [1/2, 1)`, `(rho, sigma) |-> Qtilde_alpha(rho || sigma)` is
jointly concave.

This file deliberately stops at closed helper lemmas unless a non-circular
Frank--Lieb/Lieb concavity theorem is available locally.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology Matrix.Norms.L2Operator

universe u v w

namespace Matrix

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Tensoring on opposite sides commutes: `(A ⊗ I) (I ⊗ B) = (I ⊗ B) (A ⊗ I)`. -/
theorem kronecker_left_right_commute
    (A : QIT.CMatrix a) (B : QIT.CMatrix b) :
    Matrix.kronecker A (1 : QIT.CMatrix b) *
        Matrix.kronecker (1 : QIT.CMatrix a) B =
      Matrix.kronecker (1 : QIT.CMatrix a) B *
        Matrix.kronecker A (1 : QIT.CMatrix b) := by
  calc
    Matrix.kronecker A (1 : QIT.CMatrix b) *
        Matrix.kronecker (1 : QIT.CMatrix a) B =
      Matrix.kronecker (A * (1 : QIT.CMatrix a)) ((1 : QIT.CMatrix b) * B) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul A (1 : QIT.CMatrix a)
            (1 : QIT.CMatrix b) B).symm
    _ = Matrix.kronecker ((1 : QIT.CMatrix a) * A) (B * (1 : QIT.CMatrix b)) := by
        simp
    _ =
      Matrix.kronecker (1 : QIT.CMatrix a) B *
        Matrix.kronecker A (1 : QIT.CMatrix b) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul (1 : QIT.CMatrix a) A
            B (1 : QIT.CMatrix b))

/-- Trace form of the positive weighted Ando resolvent-integrand concavity.

The matrix inequality above is stronger; this trace form is the one that
matches the Frank--Lieb trace concavity statement after the Audenaert
fractional-power integral representation is inserted. -/
theorem andoResolventIntegrand_rpow_weighted_trace_concave_posDef
    {A₁ A₂ : QIT.CMatrix a} {B₁ B₂ : QIT.CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p r t : ℝ} (hr : 0 < r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (((r ^ (p - 1)) •
            andoResolventIntegrand (a := a) (b := b) r A₁ B₁).trace).re +
        (1 - t) * (((r ^ (p - 1)) •
            andoResolventIntegrand (a := a) (b := b) r A₂ B₂).trace).re ≤
      (((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r
        (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂)).trace).re := by
  let L : QIT.CMatrix (a × b) :=
    t • ((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
      (1 - t) •
        ((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂)
  let R : QIT.CMatrix (a × b) :=
    (r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hmat : L ≤ R := by
    simpa [L, R] using
      andoResolventIntegrand_rpow_weighted_concave_posDef
        hA₁ hA₂ hB₁ hB₂ hr ht0 ht1 (p := p)
  have hdiff : (R - L).PosSemidef := Matrix.le_iff.mp hmat
  have htrace_nonneg : 0 ≤ ((R - L).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hdiff).1
  have hle : L.trace.re ≤ R.trace.re := by
    simpa [Matrix.trace_sub] using htrace_nonneg
  simpa [L, R, Matrix.trace_add, Matrix.trace_smul, Complex.mul_re] using hle

end

end Matrix

namespace QIT

noncomputable section

open MeasureTheory

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- For a positive definite matrix, real powers of the nonsingular inverse
are the negative real powers of the original matrix. -/
public theorem cMatrix_rpow_nonsing_inv_eq_rpow_neg
    {B : CMatrix a} (hB : B.PosDef) (p : ℝ) :
    CFC.rpow B⁻¹ p = CFC.rpow B (-p) := by
  obtain ⟨u, hu⟩ := hB.isUnit
  have hBnonneg : (0 : CMatrix a) ≤ B :=
    Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef
  have hinv : B⁻¹ = (↑u⁻¹ : CMatrix a) := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu]
    simp
  calc
    CFC.rpow B⁻¹ p = CFC.rpow (↑u⁻¹ : CMatrix a) p := by
      rw [hinv]
    _ = CFC.rpow (↑u : CMatrix a) (-p) := by
      exact (CFC.rpow_neg u p (ha' := by simpa [hu] using hBnonneg)).symm
    _ = CFC.rpow B (-p) := by
      rw [hu]

/-- Multiplying the inverse-reference tensor power by `I ⊗ B` converts it
to the tensor power term in the Lieb--Ando trace concavity statement:
`(A ⊗ B⁻¹)^p (I ⊗ B) = A^p ⊗ B^(1-p)`. -/
public theorem cMatrix_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
    {b : Type v} [Fintype b] [DecidableEq b]
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
    rw [cMatrix_rpow_nonsing_inv_eq_rpow_neg hB p]
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

/-- Integrability is preserved by right-multiplication with a fixed complex
matrix. -/
public theorem cMatrix_integrableOn_mul_right
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (R : CMatrix a) :
    IntegrableOn (fun r => f r * R) s μ := by
  have hf' : Integrable f (μ.restrict s) := by
    simpa [IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix a) (1 : CMatrix a) R).integrable_comp hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply, IntegrableOn] using h

/-- Right-multiplication by a fixed matrix commutes with Bochner integration. -/
public theorem cMatrix_setIntegral_mul_right
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (R : CMatrix a) :
    (∫ r in s, f r ∂μ) * R = ∫ r in s, f r * R ∂μ := by
  have hf' : Integrable f (μ.restrict s) := by
    simpa [IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix a) (1 : CMatrix a) R).integral_comp_comm hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply] using h.symm

/-- Right-multiplying `A ⊗ B⁻¹` by `I ⊗ B` recovers `A ⊗ I`. -/
public theorem cMatrix_kronecker_inv_ref_mul_right
    {b : Type v} [Fintype b] [DecidableEq b]
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

/-- The shifted Audenaert denominator is the Ando denominator after
right-multiplication by `(I ⊗ B)⁻¹`. -/
public theorem cMatrix_andoDenom_mul_ref_inv_eq_shift
    {b : Type v} [Fintype b] [DecidableEq b]
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

/-- Inverse bridge between the shifted Audenaert resolvent denominator and
the Ando denominator. -/
public theorem cMatrix_shiftedKroneckerInv_inv_eq_ref_mul_andoDenom_inv
    {b : Type v} [Fintype b] [DecidableEq b]
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
      cMatrix_andoDenom_mul_ref_inv_eq_shift
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

/-- Pointwise bridge from Audenaert's fractional-power integrand applied to
`A ⊗ B⁻¹` to the weighted Ando resolvent integrand.

After right-multiplication by `I ⊗ B`, the resolvent form of
`audenaertRpowIntegrand` becomes exactly the integrand whose integral yields
the Lieb--Ando tensor trace-concavity term. -/
public theorem audenaertRpowIntegrand_kronecker_inv_mul_right_eq_ando
    {b : Type v} [Fintype b] [DecidableEq b]
    {p r : ℝ} {A : CMatrix a} {B : CMatrix b}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : 0 < r)
    (hA : A.PosSemidef) (hB : B.PosDef) :
    audenaertRpowIntegrand p r (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A B := by
  let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
  let X : CMatrix (a × b) := Matrix.kronecker A (1 : CMatrix b)
  let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
  let D : CMatrix (a × b) := X + r • Y
  have hCpsd : C.PosSemidef := by
    simpa [C] using hA.kronecker hB.inv.posSemidef
  have hCmulY : C * Y = X := by
    simpa [C, Y, X] using
      cMatrix_kronecker_inv_ref_mul_right
        (a := a) (b := b) (A := A) (B := B) hB
  have hinv : (C + r • (1 : CMatrix (a × b)))⁻¹ = Y * D⁻¹ := by
    simpa [C, X, Y, D] using
      cMatrix_shiftedKroneckerInv_inv_eq_ref_mul_andoDenom_inv
        (a := a) (b := b) (A := A) (B := B) (r := r) hA hB hr
  calc
    audenaertRpowIntegrand p r (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      (r ^ (p - 1) • (C * (C + r • (1 : CMatrix (a × b)))⁻¹)) * Y := by
        rw [audenaertRpowIntegrand_eq_resolvent hp hr hCpsd]
        simp [audenaertResolventIntegrand, C, Y]
    _ = r ^ (p - 1) • (C * (C + r • (1 : CMatrix (a × b)))⁻¹ * Y) := by
        simp
    _ = r ^ (p - 1) • (C * (Y * D⁻¹) * Y) := by
        rw [hinv]
    _ = r ^ (p - 1) • ((C * Y) * D⁻¹ * Y) := by
        congr 1
        rw [← Matrix.mul_assoc C Y D⁻¹, Matrix.mul_assoc]
    _ = r ^ (p - 1) • (X * D⁻¹ * Y) := by
        rw [hCmulY]
    _ = (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A B := by
        simp [Matrix.andoResolventIntegrand, X, Y, D]

/-- Audenaert's fractional-power representation gives the Ando integral
representation of the Lieb tensor power term, with one measure depending
only on `p` and the tensor dimension.

This is the analytic representation identity that closes the gap between
the pointwise Ando resolvent concavity and the finite-dimensional
Lieb--Ando trace concavity theorem for a positive definite reference
argument. -/
public theorem andoIntegralRepresentation_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1) :
    ∃ μ : Measure ℝ,
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        IntegrableOn (fun r : ℝ => (r ^ ((p : ℝ) - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A B)
          (Set.Ioi 0) μ) ∧
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        Matrix.kronecker (CFC.rpow A (p : ℝ)) (CFC.rpow B (1 - (p : ℝ))) =
          ∫ r in Set.Ioi 0, (r ^ ((p : ℝ) - 1)) •
            Matrix.andoResolventIntegrand (a := a) (b := b) r A B ∂μ) := by
  obtain ⟨μ, hint, hpow⟩ := audenaertRpowIntegralRepresentation (a := a × b) hp
  refine ⟨μ, ?_, ?_⟩
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hpReal : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hAudInt :
        IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r C)
          (Set.Ioi 0) μ :=
      hint hCpsd
    have hAudRightInt :
        IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r C * Y)
          (Set.Ioi 0) μ :=
      cMatrix_integrableOn_mul_right hAudInt Y
    let F : ℝ → CMatrix (a × b) := fun r =>
      audenaertRpowIntegrand (p : ℝ) r C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ ((p : ℝ) - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        audenaertRpowIntegrand_kronecker_inv_mul_right_eq_ando
          (a := a) (b := b) (p := (p : ℝ)) (r := r) (A := A) (B := B)
          hpReal hr hA hB
    have hGInt : IntegrableOn G (Set.Ioi 0) μ :=
      hAudRightInt.congr_fun hEqOn measurableSet_Ioi
    simpa [G] using hGInt
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hpReal : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩
    have hp0 : 0 ≤ (p : ℝ) := by
      exact_mod_cast (show (0 : ℝ≥0) ≤ p from zero_le)
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hAudInt :
        IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r C)
          (Set.Ioi 0) μ :=
      hint hCpsd
    let F : ℝ → CMatrix (a × b) := fun r =>
      audenaertRpowIntegrand (p : ℝ) r C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ ((p : ℝ) - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        audenaertRpowIntegrand_kronecker_inv_mul_right_eq_ando
          (a := a) (b := b) (p := (p : ℝ)) (r := r) (A := A) (B := B)
          hpReal hr hA hB
    have hCpow := hpow hCpsd
    have hLeft : CFC.rpow C (p : ℝ) * Y = ∫ r in Set.Ioi 0, F r ∂μ := by
      calc
        CFC.rpow C (p : ℝ) * Y =
            (∫ r in Set.Ioi 0, audenaertRpowIntegrand (p : ℝ) r C ∂μ) * Y := by
          rw [hCpow]
        _ = ∫ r in Set.Ioi 0, audenaertRpowIntegrand (p : ℝ) r C * Y ∂μ := by
          rw [cMatrix_setIntegral_mul_right hAudInt Y]
        _ = ∫ r in Set.Ioi 0, F r ∂μ := by
          rfl
    have hFGint : ∫ r in Set.Ioi 0, F r ∂μ = ∫ r in Set.Ioi 0, G r ∂μ := by
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem measurableSet_Ioi hEqOn
    have hTensor :
        CFC.rpow C (p : ℝ) * Y =
          Matrix.kronecker (CFC.rpow A (p : ℝ)) (CFC.rpow B (1 - (p : ℝ))) := by
      simpa [C, Y] using
        cMatrix_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
          (a := a) (b := b) (A := A) (B := B) hA hB hp0
    calc
      Matrix.kronecker (CFC.rpow A (p : ℝ)) (CFC.rpow B (1 - (p : ℝ))) =
          CFC.rpow C (p : ℝ) * Y := by
        exact hTensor.symm
      _ = ∫ r in Set.Ioi 0, F r ∂μ := hLeft
      _ = ∫ r in Set.Ioi 0, G r ∂μ := hFGint
      _ = ∫ r in Set.Ioi 0, (r ^ ((p : ℝ) - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A B ∂μ := by
        rfl

private noncomputable def cMatrixEntryCLMComplex {ι : Type v}
    [Fintype ι] [DecidableEq ι] (i j : ι) : CMatrix ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => M i j
       map_add' := by intro M N; simp
       map_smul' := by intro c M; simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℂ] ℂ)

private noncomputable def cMatrixConjTransposeCLM {ι : Type v}
    [Fintype ι] [DecidableEq ι] : CMatrix ι →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => Matrix.conjTranspose M
       map_add' := by intro M N; simp
       map_smul' := by intro c M; ext i j; simp } : CMatrix ι →ₗ[ℝ] CMatrix ι)

private theorem cMatrix_integral_conjTranspose {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) :
    Matrix.conjTranspose (∫ x, f x ∂μ) =
      ∫ x, Matrix.conjTranspose (f x) ∂μ := by
  simpa [cMatrixConjTransposeCLM] using
    ((cMatrixConjTransposeCLM (ι := ι)).integral_comp_comm hf).symm

private noncomputable def cMatrixQuadraticCLM {ι : Type v}
    [Fintype ι] [DecidableEq ι] (x : ι → ℂ) : CMatrix ι →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (x i) * x j) •
    cMatrixEntryCLMComplex (ι := ι) i j

private theorem cMatrixQuadraticCLM_apply {ι : Type v}
    [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (A : CMatrix ι) :
    cMatrixQuadraticCLM x A = dotProduct (star x) (Matrix.mulVec A x) := by
  simp [cMatrixQuadraticCLM, cMatrixEntryCLMComplex, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

private theorem cMatrix_integral_dotProduct_mulVec {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (x : ι → ℂ) :
    dotProduct (star x) (Matrix.mulVec (∫ t, f t ∂μ) x) =
      ∫ t, dotProduct (star x) (Matrix.mulVec (f t) x) ∂μ := by
  simp_rw [← cMatrixQuadraticCLM_apply x]
  exact
    ((cMatrixQuadraticCLM x).integral_comp_comm hf).symm

private theorem isClosed_setOf_zero_le_complex_frankLieb :
    IsClosed ({z : ℂ | 0 ≤ z} : Set ℂ) := by
  have h : ({z : ℂ | 0 ≤ z} : Set ℂ) = {z | 0 ≤ z.re} ∩ {z | z.im = 0} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hz
      simp [Complex.le_def] at hz ⊢
      tauto
    · rintro ⟨hre, him⟩
      simp [Complex.le_def]
      exact ⟨hre, him.symm⟩
  rw [h]
  exact (isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

private theorem continuous_cMatrix_quadraticForm {ι : Type v}
    [Fintype ι] [DecidableEq ι] (x : ι →₀ ℂ) :
    Continuous (fun A : CMatrix ι =>
      (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj)) := by
  classical
  simp only [Finsupp.sum, Finsupp.sum]
  exact continuous_finsetSum x.support fun i _ =>
    continuous_finsetSum x.support fun j _ =>
      Continuous.mul (Continuous.mul continuous_const
        (cMatrixEntryCLMComplex (ι := ι) i j).continuous) continuous_const

/-- The finite-dimensional cone of positive semidefinite complex matrices is
closed in the norm topology. -/
public theorem isClosed_cMatrix_posSemidef {ι : Type v}
    [Fintype ι] [DecidableEq ι] :
    IsClosed ({A : CMatrix ι | A.PosSemidef} : Set (CMatrix ι)) := by
  classical
  have h : ({A : CMatrix ι | A.PosSemidef} : Set (CMatrix ι)) =
      ({A | A.IsHermitian} ∩
        (⋂ x : ι →₀ ℂ,
          {A : CMatrix ι | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj})) := by
    ext A
    simp [Matrix.PosSemidef, Set.mem_iInter]
  rw [h]
  refine IsClosed.inter ?herm ?quad
  · have hH : ({A : CMatrix ι | A.IsHermitian} : Set (CMatrix ι)) =
        {A | Matrix.conjTranspose A = A} := by
      ext A
      simp [Matrix.IsHermitian]
    rw [hH]
    exact isClosed_eq (cMatrixConjTransposeCLM (ι := ι)).continuous continuous_id
  · exact isClosed_iInter fun x =>
      isClosed_setOf_zero_le_complex_frankLieb.preimage
        (continuous_cMatrix_quadraticForm (ι := ι) x)

/-- Positive semidefiniteness is preserved under limits of eventually PSD
matrix-valued filters. -/
public theorem cMatrix_posSemidef_of_tendsto {ι : Type v}
    [Fintype ι] [DecidableEq ι] {X : Type*} {l : Filter X} [l.NeBot]
    {F : X → CMatrix ι} {A : CMatrix ι}
    (hF : Filter.Tendsto F l (nhds A))
    (hpsd : ∀ᶠ x in l, (F x).PosSemidef) :
    A.PosSemidef :=
  (isClosed_cMatrix_posSemidef (ι := ι)).mem_of_tendsto hF hpsd

/-- Loewner inequalities are preserved under simultaneous limits. -/
public theorem cMatrix_le_of_tendsto {ι : Type v}
    [Fintype ι] [DecidableEq ι] {X : Type*} {l : Filter X} [l.NeBot]
    {F G : X → CMatrix ι} {A B : CMatrix ι}
    (hF : Filter.Tendsto F l (nhds A))
    (hG : Filter.Tendsto G l (nhds B))
    (hle : ∀ᶠ x in l, F x ≤ G x) :
    A ≤ B := by
  have hdiff :
      Filter.Tendsto (fun x : X => G x - F x) l (nhds (B - A)) :=
    hG.sub hF
  have hpsd : (B - A).PosSemidef :=
    cMatrix_posSemidef_of_tendsto hdiff
      (hle.mono fun _ hx => Matrix.le_iff.mp hx)
  exact Matrix.le_iff.mpr hpsd

/-- Bochner integration preserves positive semidefiniteness for matrix-valued
functions, up to almost-everywhere equality. -/
public theorem cMatrix_integral_posSemidef_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, cMatrix_integral_conjTranspose (hf := hf)]
    apply integral_congr_ae
    exact hpos.mono fun _ ht => ht.isHermitian.eq
  · intro x
    rw [cMatrix_integral_dotProduct_mulVec (hf := hf) x]
    exact integral_nonneg_of_ae (hpos.mono fun _ ht => ht.dotProduct_mulVec_nonneg x)

/-- Monotonicity of Bochner set integration for matrix-valued functions in
Loewner order.

Mathlib's scalar/order lemma needs a closed-order-topology instance which is
not available for `CMatrix`; this version proves the PSD difference directly
from quadratic forms. -/
public theorem cMatrix_setIntegral_mono
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hle : ∀ r ∈ s, f r ≤ g r) :
    ∫ r in s, f r ∂μ ≤ ∫ r in s, g r ∂μ := by
  have hdiffInt : IntegrableOn (fun r : ℝ => g r - f r) s μ := hg.sub hf
  have hdiffPSD :
      (∫ r in s, (g r - f r) ∂μ).PosSemidef := by
    have hdiffInt' : Integrable (fun r : ℝ => g r - f r) (μ.restrict s) := by
      simpa [IntegrableOn] using hdiffInt
    exact
      cMatrix_integral_posSemidef_of_ae (μ := μ.restrict s) hdiffInt'
        ((ae_restrict_iff' hs).mpr
          (ae_of_all μ fun r hr => Matrix.le_iff.mp (hle r hr)))
  have hsub :
      ∫ r in s, (g r - f r) ∂μ =
        (∫ r in s, g r ∂μ) - (∫ r in s, f r ∂μ) := by
    simpa [IntegrableOn] using
      integral_sub (μ := μ.restrict s)
        (by simpa [IntegrableOn] using hg)
        (by simpa [IntegrableOn] using hf)
  rw [hsub] at hdiffPSD
  exact Matrix.le_iff.mpr hdiffPSD

/-- Monotonicity of the real trace after Bochner integration of matrix-valued
functions.

This is the integration bridge needed by the Frank--Lieb/Ando route: once a
pointwise Loewner-order inequality is available for the resolvent integrand,
its trace inequality survives integration against the Audenaert measure. -/
theorem cMatrix_setIntegral_trace_re_mono
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hle : ∀ r ∈ s, f r ≤ g r) :
    ((∫ r in s, f r ∂μ).trace).re ≤
      ((∫ r in s, g r ∂μ).trace).re := by
  have hdiffInt : IntegrableOn (fun r : ℝ => g r - f r) s μ := hg.sub hf
  have htraceIntegral :
      (((∫ r in s, (g r - f r) ∂μ).trace).re) =
        ∫ r in s, ((g r - f r).trace).re ∂μ := by
    simpa [Matrix.mul_one, Matrix.one_mul] using
      audenaertTraceLeftRight_setIntegral (a := a) hdiffInt
        (1 : CMatrix a) (1 : CMatrix a)
  have htraceNonneg :
      0 ≤ ∫ r in s, ((g r - f r).trace).re ∂μ := by
    apply setIntegral_nonneg hs
    intro r hr
    have hdiff : (g r - f r).PosSemidef := Matrix.le_iff.mp (hle r hr)
    exact (Matrix.PosSemidef.trace_nonneg hdiff).1
  have hnonneg :
      0 ≤ (((∫ r in s, (g r - f r) ∂μ).trace).re) := by
    simpa [htraceIntegral] using htraceNonneg
  have hsub :
      ∫ r in s, (g r - f r) ∂μ =
        (∫ r in s, g r ∂μ) - (∫ r in s, f r ∂μ) := by
    simpa [IntegrableOn] using
      integral_sub (μ := μ.restrict s)
        (by simpa [IntegrableOn] using hg)
        (by simpa [IntegrableOn] using hf)
  rw [hsub, Matrix.trace_sub, Complex.sub_re] at hnonneg
  linarith

/-- Integrated trace concavity of the positive weighted Ando resolvent
integrand.

The hypotheses isolate the purely measure-theoretic side of the
Audenaert representation: once the three resolvent integrands are integrable,
the pointwise Ando Loewner inequality integrates to the corresponding trace
inequality. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    (((∫ r in s,
      (t • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
        (1 - t) • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂)) ∂μ).trace).re)
      ≤
    (((∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ).trace).re) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hLeftInt : IntegrableOn (fun r : ℝ => t • F₁ r + (1 - t) • F₂ r) s μ :=
    (hI₁.smul t).add (hI₂.smul (1 - t))
  have hmono :
      ∀ r ∈ s, t • F₁ r + (1 - t) • F₂ r ≤ Ft r := by
    intro r hrs
    simpa [F₁, F₂, Ft] using
      Matrix.andoResolventIntegrand_rpow_weighted_concave_posDef
        hA₁ hA₂ hB₁ hB₂ (hr_pos r hrs) ht0 ht1 (p := p)
  simpa [F₁, F₂, Ft] using
    cMatrix_setIntegral_trace_re_mono (a := a × b) hs hLeftInt hIt hmono

/-- Integrated Loewner concavity of the positive weighted Ando resolvent
integrand.

This is the matrix-order strengthening of
`andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef`.
It is the bridge needed to apply arbitrary positive trace functionals, rather
than only the ordinary trace. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    (∫ r in s,
      (t • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
        (1 - t) • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂)) ∂μ)
      ≤
    (∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hLeftInt : IntegrableOn (fun r : ℝ => t • F₁ r + (1 - t) • F₂ r) s μ :=
    (hI₁.smul t).add (hI₂.smul (1 - t))
  have hmono :
      ∀ r ∈ s, t • F₁ r + (1 - t) • F₂ r ≤ Ft r := by
    intro r hrs
    simpa [F₁, F₂, Ft] using
      Matrix.andoResolventIntegrand_rpow_weighted_concave_posDef
        hA₁ hA₂ hB₁ hB₂ (hr_pos r hrs) ht0 ht1 (p := p)
  simpa [F₁, F₂, Ft] using
    cMatrix_setIntegral_mono (a := a × b) hs hLeftInt hIt hmono

/-- Standard separated-left form of the integrated Ando trace concavity. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef'
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    t * (((∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ).trace).re) +
        (1 - t) * (((∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ).trace).re)
      ≤
    (((∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ).trace).re) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hbase :
      (((∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ).trace).re) ≤
        (((∫ r in s, Ft r ∂μ).trace).re) := by
    simpa [F₁, F₂, Ft] using
      andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef
        (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  have hI₁' : Integrable F₁ (μ.restrict s) := by
    simpa [IntegrableOn, F₁] using hI₁
  have hI₂' : Integrable F₂ (μ.restrict s) := by
    simpa [IntegrableOn, F₂] using hI₂
  have hleftIntegral :
      ∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ =
        t • (∫ r in s, F₁ r ∂μ) + (1 - t) • (∫ r in s, F₂ r ∂μ) := by
    have hadd :=
      integral_add (μ := μ.restrict s) (hI₁'.smul t) (hI₂'.smul (1 - t))
    have hsmul₁ :
        ∫ r in s, t • F₁ r ∂μ = t • (∫ r in s, F₁ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) t F₁)
    have hsmul₂ :
        ∫ r in s, (1 - t) • F₂ r ∂μ = (1 - t) • (∫ r in s, F₂ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) (1 - t) F₂)
    simpa [Pi.add_apply, hsmul₁, hsmul₂] using hadd
  have hleftTrace :
      (((∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ).trace).re) =
        t * (((∫ r in s, F₁ r ∂μ).trace).re) +
          (1 - t) * (((∫ r in s, F₂ r ∂μ).trace).re) := by
    rw [hleftIntegral]
    simp [Matrix.trace_add, Matrix.trace_smul, Complex.mul_re]
  rw [hleftTrace] at hbase
  simpa [F₁, F₂, Ft] using hbase

/-- Standard separated-left form of the integrated Ando Loewner concavity. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef'
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    t • (∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ) +
        (1 - t) • (∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ)
      ≤
    (∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hbase :
      (∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ) ≤
        (∫ r in s, Ft r ∂μ) := by
    simpa [F₁, F₂, Ft] using
      andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef
        (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  have hI₁' : Integrable F₁ (μ.restrict s) := by
    simpa [IntegrableOn, F₁] using hI₁
  have hI₂' : Integrable F₂ (μ.restrict s) := by
    simpa [IntegrableOn, F₂] using hI₂
  have hleftIntegral :
      ∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ =
        t • (∫ r in s, F₁ r ∂μ) + (1 - t) • (∫ r in s, F₂ r ∂μ) := by
    have hadd :=
      integral_add (μ := μ.restrict s) (hI₁'.smul t) (hI₂'.smul (1 - t))
    have hsmul₁ :
        ∫ r in s, t • F₁ r ∂μ = t • (∫ r in s, F₁ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) t F₁)
    have hsmul₂ :
        ∫ r in s, (1 - t) • F₂ r ∂μ = (1 - t) • (∫ r in s, F₂ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) (1 - t) F₂)
    simpa [Pi.add_apply, hsmul₁, hsmul₂] using hadd
  rw [hleftIntegral] at hbase
  simpa [F₁, F₂, Ft] using hbase

/-- Handoff from the Ando integral representation to the Lieb--Ando tensor
trace-concavity statement.

This theorem isolates the remaining analytic identity: once each tensor power
term is represented by the Audenaert/Ando resolvent integral, the already
proved integrated Ando trace concavity gives the desired Lieb trace
concavity. -/
theorem liebAndo_tensorTraceConcavity_of_andoIntegralRepresentation_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ)
    (hRep₁ :
      Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ)
    (hRep₂ :
      Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ)
    (hRept :
      Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
          (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r
            (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) ∂μ) :
    t * ((Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p))).trace).re +
        (1 - t) *
          ((Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p))).trace).re
      ≤
    ((Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p))).trace).re := by
  have hconc :=
    andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef'
      (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  rw [hRep₁, hRep₂, hRept]
  exact hconc

/-- Handoff from the Ando integral representation to the Lieb--Ando tensor
Loewner-concavity statement.

This matrix-order version is stronger than the trace form and is the right
input for Epstein/Frank--Lieb positive trace functionals. -/
theorem liebAndo_tensorConcavity_of_andoIntegralRepresentation_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ)
    (hRep₁ :
      Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ)
    (hRep₂ :
      Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ)
    (hRept :
      Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
          (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r
            (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) ∂μ) :
    t • Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p)) +
        (1 - t) •
          Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p))
      ≤
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p)) := by
  have hconc :=
    andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef'
      (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  rw [hRep₁, hRep₂, hRept]
  exact hconc

/-- Lieb--Ando tensor trace concavity with a positive definite right
argument.

This is the completed Frank--Lieb/Epstein core for the nonsingular reference
case: Audenaert's CFC integral representation supplies the tensor power term,
and Ando's resolvent concavity supplies the integrated trace inequality. -/
public theorem liebAndo_tensorTraceConcavity_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))).trace).re +
        (1 - t) *
          ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))).trace).re
      ≤
    ((Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))).trace).re := by
  obtain ⟨μ, hint, hrep⟩ := andoIntegralRepresentation_posDef (a := a) (b := b) hp
  have hAbar : (t • A₁ + (1 - t) • A₂).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hA₁ ht0)
      (Matrix.PosSemidef.smul hA₂ (sub_nonneg.mpr ht1))
  have hBbar : (t • B₁ + (1 - t) • B₂).PosDef :=
    Matrix.PosDef.convexCombination hB₁ hB₂ ht0 ht1
  exact
    liebAndo_tensorTraceConcavity_of_andoIntegralRepresentation_posDef
      (a := a) (b := b) (μ := μ) (s := Set.Ioi 0) measurableSet_Ioi
      hA₁ hA₂ hB₁ hB₂ ht0 ht1
      (by intro r hr; exact hr)
      (hint hA₁ hB₁)
      (hint hA₂ hB₂)
      (hint hAbar hBbar)
      (hrep hA₁ hB₁)
      (hrep hA₂ hB₂)
      (hrep hAbar hBbar)

/-- Lieb--Ando tensor Loewner concavity with a positive definite right
argument.

This strengthens `liebAndo_tensorTraceConcavity_posDef` from ordinary trace
to Loewner order, so any positive trace functional can be applied downstream. -/
public theorem liebAndo_tensorConcavity_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ))) +
        (1 - t) •
          Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))
      ≤
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ))) := by
  obtain ⟨μ, hint, hrep⟩ := andoIntegralRepresentation_posDef (a := a) (b := b) hp
  have hAbar : (t • A₁ + (1 - t) • A₂).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hA₁ ht0)
      (Matrix.PosSemidef.smul hA₂ (sub_nonneg.mpr ht1))
  have hBbar : (t • B₁ + (1 - t) • B₂).PosDef :=
    Matrix.PosDef.convexCombination hB₁ hB₂ ht0 ht1
  exact
    liebAndo_tensorConcavity_of_andoIntegralRepresentation_posDef
      (a := a) (b := b) (μ := μ) (s := Set.Ioi 0) measurableSet_Ioi
      hA₁ hA₂ hB₁ hB₂ ht0 ht1
      (by intro r hr; exact hr)
      (hint hA₁ hB₁)
      (hint hA₂ hB₂)
      (hint hAbar hBbar)
      (hrep hA₁ hB₁)
      (hrep hA₂ hB₂)
      (hrep hAbar hBbar)

omit [DecidableEq a] in
/-- The real trace of `K ⊗ F x` is continuous in the right tensor factor. -/
public theorem cMatrix_kronecker_trace_re_tendsto_right
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (K : CMatrix a) (hF : Filter.Tendsto F l (nhds B)) :
    Filter.Tendsto
      (fun x : X => ((Matrix.kronecker K (F x)).trace).re)
      l
      (nhds ((Matrix.kronecker K B).trace.re)) := by
  have hcont :
      Continuous fun M : CMatrix b =>
        ((Matrix.kronecker K M).trace).re := by
    rw [continuous_iff_continuousAt]
    intro M
    have htrace : ContinuousAt (fun M : CMatrix b =>
        (Matrix.kronecker K M).trace) M := by
      simpa [Matrix.trace_kronecker] using
        ((continuous_const.mul
          (Continuous.matrix_trace continuous_id)).continuousAt : ContinuousAt
          (fun M : CMatrix b => K.trace * M.trace) M)
    exact Complex.continuous_re.continuousAt.comp htrace
  exact (hcont.tendsto B).comp hF

/-- Tensor-power trace continuity in the right tensor factor along
PSD-constrained filters. -/
public theorem cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (A : CMatrix a) (p : ℝ)
    (hF : Filter.Tendsto F l (nhds B))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q) :
    Filter.Tendsto
      (fun x : X =>
        ((Matrix.kronecker (CFC.rpow A p) (CFC.rpow (F x) q)).trace).re)
      l
      (nhds ((Matrix.kronecker (CFC.rpow A p) (CFC.rpow B q)).trace.re)) := by
  have hpow :
      Filter.Tendsto (fun x : X => CFC.rpow (F x) q) l
        (nhds (CFC.rpow B q)) :=
    cMatrix_rpow_tendsto_of_tendsto_posSemidef hq hF hFpsd hB
  exact
    cMatrix_kronecker_trace_re_tendsto_right
      (a := a) (b := b) (K := CFC.rpow A p) hpow

omit [Fintype a] [DecidableEq a] in
/-- Tensoring on the right by a convergent matrix family is continuous. -/
public theorem cMatrix_kronecker_tendsto_right
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (K : CMatrix a) (hF : Filter.Tendsto F l (nhds B)) :
    Filter.Tendsto (fun x : X => Matrix.kronecker K (F x)) l
      (nhds (Matrix.kronecker K B)) := by
  have hcont : Continuous fun M : CMatrix b => Matrix.kronecker K M := by
    apply continuous_matrix
    intro i j
    rcases i with ⟨ia, ib⟩
    rcases j with ⟨ja, jb⟩
    simpa [Matrix.kronecker, Matrix.kroneckerMap_apply] using
      (continuous_const.mul (continuous_apply_apply ib jb) :
        Continuous fun M : CMatrix b => K ia ja * M ib jb)
  exact (hcont.tendsto B).comp hF

/-- Tensor-power continuity in the right tensor factor along PSD-constrained
filters. -/
public theorem cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (A : CMatrix a) (p : ℝ)
    (hF : Filter.Tendsto F l (nhds B))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q) :
    Filter.Tendsto
      (fun x : X =>
        Matrix.kronecker (CFC.rpow A p) (CFC.rpow (F x) q))
      l
      (nhds (Matrix.kronecker (CFC.rpow A p) (CFC.rpow B q))) := by
  have hpow :
      Filter.Tendsto (fun x : X => CFC.rpow (F x) q) l
        (nhds (CFC.rpow B q)) :=
    cMatrix_rpow_tendsto_of_tendsto_posSemidef hq hF hFpsd hB
  exact
    cMatrix_kronecker_tendsto_right
      (a := a) (b := b) (K := CFC.rpow A p) hpow

/-- Lieb--Ando tensor trace concavity with unrestricted PSD right arguments.

This is the PSD closure of `liebAndo_tensorTraceConcavity_posDef`, obtained by
regularizing the right tensor factors by `ε I` and passing to the limit from the
positive side. -/
public theorem liebAndo_tensorTraceConcavity_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))).trace).re +
        (1 - t) *
          ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))).trace).re
      ≤
    ((Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))).trace).re := by
  let q : ℝ := 1 - (p : ℝ)
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let B₁ε : ℝ → CMatrix b := fun ε => B₁ + ε • (1 : CMatrix b)
  let B₂ε : ℝ → CMatrix b := fun ε => B₂ + ε • (1 : CMatrix b)
  let Bbar : CMatrix b := t • B₁ + (1 - t) • B₂
  let Bbarε : ℝ → CMatrix b := fun ε => t • B₁ε ε + (1 - t) • B₂ε ε
  have hq_pos : 0 < q := by
    have hp_lt_one : (p : ℝ) < 1 := by exact_mod_cast hp.2
    dsimp [q]
    linarith
  have hBbar : Bbar.PosSemidef := by
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hB₁ ht0)
      (Matrix.PosSemidef.smul hB₂ (sub_nonneg.mpr ht1))
  have hB₁ε_tend : Filter.Tendsto B₁ε l (nhds B₁) := by
    simpa [B₁ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₁)
  have hB₂ε_tend : Filter.Tendsto B₂ε l (nhds B₂) := by
    simpa [B₂ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₂)
  have hBbarε_tend : Filter.Tendsto Bbarε l (nhds Bbar) := by
    have htend :
        Filter.Tendsto
          (fun ε : ℝ => t • B₁ε ε + (1 - t) • B₂ε ε)
          l (nhds (t • B₁ + (1 - t) • B₂)) :=
      (hB₁ε_tend.const_smul t).add (hB₂ε_tend.const_smul (1 - t))
    simpa [Bbarε, Bbar] using htend
  have hB₁ε_psd : ∀ᶠ ε in l, (B₁ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₁ hε.le
  have hB₂ε_psd : ∀ᶠ ε in l, (B₂ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₂ hε.le
  have hBbarε_psd : ∀ᶠ ε in l, (Bbarε ε).PosSemidef := by
    filter_upwards [hB₁ε_psd, hB₂ε_psd] with ε h₁ h₂
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul h₁ ht0)
      (Matrix.PosSemidef.smul h₂ (sub_nonneg.mpr ht1))
  have hleft₁ :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q)).trace).re)
        l
        (nhds ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q)).trace.re)) :=
    cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₁) (p := (p : ℝ))
      hB₁ε_tend hB₁ε_psd hB₁ hq_pos
  have hleft₂ :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q)).trace).re)
        l
        (nhds ((Matrix.kronecker
          (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q)).trace.re)) :=
    cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₂) (p := (p : ℝ))
      hB₂ε_tend hB₂ε_psd hB₂ hq_pos
  have hright :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((Matrix.kronecker
            (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
            (CFC.rpow (Bbarε ε) q)).trace).re)
        l
        (nhds ((Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow Bbar q)).trace.re)) :=
    cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := t • A₁ + (1 - t) • A₂) (p := (p : ℝ))
      hBbarε_tend hBbarε_psd hBbar hq_pos
  have hleft :
      Filter.Tendsto
        (fun ε : ℝ =>
          t * ((Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q)).trace).re +
            (1 - t) * ((Matrix.kronecker
              (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q)).trace).re)
        l
        (nhds
          (t * ((Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q)).trace).re +
            (1 - t) * ((Matrix.kronecker
              (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q)).trace).re)) :=
    (hleft₁.const_mul t).add (hleft₂.const_mul (1 - t))
  have hineq_eventual :
      (fun ε : ℝ =>
        t * ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q)).trace).re +
          (1 - t) * ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q)).trace).re)
        ≤ᶠ[l]
      (fun ε : ℝ =>
        ((Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow (Bbarε ε) q)).trace).re) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    have hB₁ε_pos : (B₁ε ε).PosDef := by
      simpa [B₁ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₁ hε
    have hB₂ε_pos : (B₂ε ε).PosDef := by
      simpa [B₂ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₂ hε
    have hpos :=
      liebAndo_tensorTraceConcavity_posDef
        (a := a) (b := b) (p := p) hp
        (A₁ := A₁) (A₂ := A₂)
        (B₁ := B₁ε ε) (B₂ := B₂ε ε)
        hA₁ hA₂ hB₁ε_pos hB₂ε_pos ht0 ht1
    simpa [Bbarε, q] using hpos
  have hlimit :=
    le_of_tendsto_of_tendsto hleft hright hineq_eventual
  simpa [q, Bbar] using hlimit

/-- Lieb--Ando tensor Loewner concavity with unrestricted PSD right arguments.

This is the matrix-order PSD closure of `liebAndo_tensorConcavity_posDef`.
It is stronger than `liebAndo_tensorTraceConcavity_posSemidef` and is the
Frank--Lieb core needed before applying positive trace functionals in the
low-alpha Q-functional route. -/
public theorem liebAndo_tensorConcavity_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ))) +
        (1 - t) •
          Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))
      ≤
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ))) := by
  let q : ℝ := 1 - (p : ℝ)
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let B₁ε : ℝ → CMatrix b := fun ε => B₁ + ε • (1 : CMatrix b)
  let B₂ε : ℝ → CMatrix b := fun ε => B₂ + ε • (1 : CMatrix b)
  let Bbar : CMatrix b := t • B₁ + (1 - t) • B₂
  let Bbarε : ℝ → CMatrix b := fun ε => t • B₁ε ε + (1 - t) • B₂ε ε
  have hq_pos : 0 < q := by
    have hp_lt_one : (p : ℝ) < 1 := by exact_mod_cast hp.2
    dsimp [q]
    linarith
  have hBbar : Bbar.PosSemidef := by
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hB₁ ht0)
      (Matrix.PosSemidef.smul hB₂ (sub_nonneg.mpr ht1))
  have hB₁ε_tend : Filter.Tendsto B₁ε l (nhds B₁) := by
    simpa [B₁ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₁)
  have hB₂ε_tend : Filter.Tendsto B₂ε l (nhds B₂) := by
    simpa [B₂ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₂)
  have hBbarε_tend : Filter.Tendsto Bbarε l (nhds Bbar) := by
    have htend :
        Filter.Tendsto
          (fun ε : ℝ => t • B₁ε ε + (1 - t) • B₂ε ε)
          l (nhds (t • B₁ + (1 - t) • B₂)) :=
      (hB₁ε_tend.const_smul t).add (hB₂ε_tend.const_smul (1 - t))
    simpa [Bbarε, Bbar] using htend
  have hB₁ε_psd : ∀ᶠ ε in l, (B₁ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₁ hε.le
  have hB₂ε_psd : ∀ᶠ ε in l, (B₂ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₂ hε.le
  have hBbarε_psd : ∀ᶠ ε in l, (Bbarε ε).PosSemidef := by
    filter_upwards [hB₁ε_psd, hB₂ε_psd] with ε h₁ h₂
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul h₁ ht0)
      (Matrix.PosSemidef.smul h₂ (sub_nonneg.mpr ht1))
  have hleft₁ :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q))
        l
        (nhds (Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q))) :=
    cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₁) (p := (p : ℝ))
      hB₁ε_tend hB₁ε_psd hB₁ hq_pos
  have hleft₂ :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q))
        l
        (nhds (Matrix.kronecker
          (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q))) :=
    cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₂) (p := (p : ℝ))
      hB₂ε_tend hB₂ε_psd hB₂ hq_pos
  have hright :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.kronecker
            (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
            (CFC.rpow (Bbarε ε) q))
        l
        (nhds (Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow Bbar q))) :=
    cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := t • A₁ + (1 - t) • A₂) (p := (p : ℝ))
      hBbarε_tend hBbarε_psd hBbar hq_pos
  have hleft :
      Filter.Tendsto
        (fun ε : ℝ =>
          t • Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q) +
          (1 - t) • Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q))
        l
        (nhds
          (t • Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q) +
          (1 - t) • Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q))) :=
    (hleft₁.const_smul t).add (hleft₂.const_smul (1 - t))
  have hineq_eventual :
      (fun ε : ℝ =>
        t • Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q) +
        (1 - t) • Matrix.kronecker
          (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q))
        ≤ᶠ[l]
      (fun ε : ℝ =>
        Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow (Bbarε ε) q)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    have hB₁ε_pos : (B₁ε ε).PosDef := by
      simpa [B₁ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₁ hε
    have hB₂ε_pos : (B₂ε ε).PosDef := by
      simpa [B₂ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₂ hε
    have hpos :=
      liebAndo_tensorConcavity_posDef
        (a := a) (b := b) (p := p) hp
        (A₁ := A₁) (A₂ := A₂)
        (B₁ := B₁ε ε) (B₂ := B₂ε ε)
        hA₁ hA₂ hB₁ε_pos hB₂ε_pos ht0 ht1
    simpa [Bbarε, q] using hpos
  have hlimit :=
    cMatrix_le_of_tendsto hleft hright hineq_eventual
  simpa [q, Bbar] using hlimit

/-- Lieb--Ando tensor concavity after applying an arbitrary positive trace
functional.

This is the positive-functional form needed for the Epstein/Frank--Lieb
handoff: after vectorizing the fixed Kraus/weight matrix into a PSD tensor
weight `W`, the remaining concavity is exactly this theorem. -/
public theorem liebAndo_tensorWeightedTraceConcavity_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b} {W : CMatrix (a × b)}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (hW : W.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((W * Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))).trace).re +
        (1 - t) *
          ((W * Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))).trace).re
      ≤
    ((W * Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))).trace).re := by
  let M₁ : CMatrix (a × b) :=
    Matrix.kronecker (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))
  let M₂ : CMatrix (a × b) :=
    Matrix.kronecker (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))
  let Mt : CMatrix (a × b) :=
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))
  have hmat : t • M₁ + (1 - t) • M₂ ≤ Mt := by
    simpa [M₁, M₂, Mt] using
      liebAndo_tensorConcavity_posSemidef
        (a := a) (b := b) (p := p) hp
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
        hA₁ hA₂ hB₁ hB₂ ht0 ht1
  have htrace :=
    cMatrix_trace_mul_le_of_le_posSemidef_left hW hmat
  have hleft :
      ((W * (t • M₁ + (1 - t) • M₂)).trace).re =
        t * ((W * M₁).trace).re + (1 - t) * ((W * M₂).trace).re := by
    rw [mul_add, Matrix.trace_add, Complex.add_re]
    simp [Matrix.trace_smul, Complex.mul_re]
  rw [hleft] at htrace
  simpa [M₁, M₂, Mt] using htrace

/-- Rank-one PSD tensor weight obtained by vectorizing the fixed matrix in an
Epstein trace term. -/
def cMatrixVecWeight (K : CMatrix a) : CMatrix (a × a) :=
  rankOneMatrix (fun p : a × a => K p.1 p.2)

omit [DecidableEq a] in
/-- The vectorized Epstein weight is positive semidefinite. -/
theorem cMatrixVecWeight_posSemidef (K : CMatrix a) :
    (cMatrixVecWeight K).PosSemidef := by
  simpa [cMatrixVecWeight] using rankOneMatrix_pos (fun p : a × a => K p.1 p.2)

omit [DecidableEq a] in
/-- Vectorized trace identity for the Epstein trace term.

The transpose on the second tensor factor is the finite-dimensional
vectorization convention:
`Tr((K† A K) B) = Tr(|K⟩⟨K| (A ⊗ Bᵀ))`. -/
theorem epstein_traceTerm_tensor_trace_transpose (K A B : CMatrix a) :
    (((star K * A * K) * B).trace) =
      ((cMatrixVecWeight K * Matrix.kronecker A B.transpose).trace) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    cMatrixVecWeight, rankOneMatrix_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  let e : (((a × a) × a) × a) ≃ (a × a) × (a × a) := {
    toFun x := ((x.1.2, x.1.1.2), (x.2, x.1.1.1))
    invFun y := (((y.2.2, y.1.2), y.1.1), y.2.1)
    left_inv := by
      intro x
      rcases x with ⟨⟨⟨x, x_1⟩, x_2⟩, x_3⟩
      rfl
    right_inv := by
      intro y
      rcases y with ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩
      rfl
  }
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  simp [e, mul_assoc, mul_left_comm, mul_comm]

omit [DecidableEq a] in
/-- Real-part version of `epstein_traceTerm_tensor_trace_transpose`. -/
theorem epstein_traceTerm_tensor_trace_transpose_re (K A B : CMatrix a) :
    ((((star K * A * K) * B).trace).re) =
      (((cMatrixVecWeight K * Matrix.kronecker A B.transpose).trace).re) := by
  exact congrArg Complex.re (epstein_traceTerm_tensor_trace_transpose K A B)

/-- Entrywise complex conjugation as a real star-algebra equivalence on
complex matrices. -/
def cMatrixConjStarAlgEquiv : CMatrix a ≃⋆ₐ[ℝ] CMatrix a :=
  StarAlgEquiv.ofAlgEquiv (AlgEquiv.mapMatrix (Complex.conjAe)) (by
    intro A
    ext i j
    simp)

omit [Fintype a] [DecidableEq a] in
/-- For Hermitian/PSD matrices, entrywise conjugation is the ordinary
transpose. -/
theorem cMatrix_map_star_eq_transpose_of_posSemidef
    {A : CMatrix a} (hA : A.PosSemidef) :
    A.map star = A.transpose := by
  ext i j
  simpa using hA.isHermitian.apply j i

/-- Nonnegative real powers commute with entrywise conjugation on PSD matrices. -/
theorem cMatrix_rpow_map_star_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.rpow (A.map star) s = (CFC.rpow A s).map star := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hmap_nonneg : 0 ≤ A.map star := by
    rw [cMatrix_map_star_eq_transpose_of_posSemidef hA]
    exact Matrix.nonneg_iff_posSemidef.mpr hA.transpose
  change (A.map star) ^ s = (A ^ s).map star
  rw [CFC.rpow_eq_cfc_real (a := A.map star) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixConjStarAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixConjStarAlgEquiv (a := a))
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix a => A.map star
        fun_prop)).symm

/-- Nonnegative real powers commute with transpose on PSD matrices. -/
theorem cMatrix_rpow_transpose_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.rpow A.transpose s = (CFC.rpow A s).transpose := by
  have hmapA : A.map star = A.transpose :=
    cMatrix_map_star_eq_transpose_of_posSemidef hA
  have hpowmap :
      CFC.rpow (A.map star) s = (CFC.rpow A s).map star :=
    cMatrix_rpow_map_star_nonneg hA hs
  have hpowPSD : (CFC.rpow A s).PosSemidef :=
    cMatrix_rpow_posSemidef (A := A) (s := s) hA
  have hpowmapTranspose :
      (CFC.rpow A s).map star = (CFC.rpow A s).transpose :=
    cMatrix_map_star_eq_transpose_of_posSemidef hpowPSD
  rw [← hmapA, hpowmap, hpowmapTranspose]


/-- Binary convex combination of complex matrices, with real weights coerced
to complex scalars. -/
def cMatrixConvexCombination (t : ℝ) (A B : CMatrix a) : CMatrix a :=
  ((t : ℂ) • A) + (((1 - t : ℝ) : ℂ) • B)

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem cMatrixConvexCombination_apply
    (t : ℝ) (A B : CMatrix a) (i j : a) :
    cMatrixConvexCombination t A B i j =
      (t : ℂ) * A i j + ((1 - t : ℝ) : ℂ) * B i j := by
  simp [cMatrixConvexCombination]

omit [Fintype a] [DecidableEq a] in
/-- The local complex-scalar matrix convex-combination notation agrees with
the ambient real vector-space convex combination. -/
theorem cMatrixConvexCombination_eq_real_smul
    (t : ℝ) (A B : CMatrix a) :
    cMatrixConvexCombination t A B = t • A + (1 - t) • B := by
  ext i j
  simp [cMatrixConvexCombination]

omit [Fintype a] [DecidableEq a] in
/-- Positive semidefiniteness is preserved by complex scalar multiplication
by a nonnegative real scalar. -/
theorem posSemidef_complex_smul_of_real_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (((t : ℂ) • A) : CMatrix a).PosSemidef := by
  have htC : (0 : ℂ) ≤ (t : ℂ) := by
    exact_mod_cast ht
  exact Matrix.PosSemidef.smul hA htC

omit [Fintype a] [DecidableEq a] in
/-- PSD matrices are closed under binary convex combinations written with
complex scalar multiplication by real weights. -/
theorem cMatrixConvexCombination_posSemidef
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t A B).PosSemidef := by
  unfold cMatrixConvexCombination
  exact Matrix.PosSemidef.add
    (posSemidef_complex_smul_of_real_nonneg hA ht0)
    (posSemidef_complex_smul_of_real_nonneg hB (sub_nonneg.mpr ht1))

omit [DecidableEq a] in
/-- Positive definite matrices are closed under binary convex combinations. -/
theorem cMatrixConvexCombination_posDef
    {A B : CMatrix a} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t A B).PosDef := by
  have hconv : (t • A + (1 - t) • B).PosDef :=
    Matrix.PosDef.convexCombination hA hB ht0 ht1
  simpa [cMatrixConvexCombination_eq_real_smul] using hconv

/-- PSD identity regularization by the positive part of a real parameter. -/
def cMatrixPSDRegularization (A : CMatrix a) (ε : ℝ) : CMatrix a :=
  A + max ε 0 • (1 : CMatrix a)

omit [Fintype a] in
/-- PSD identity regularization is PSD for every real parameter. -/
theorem cMatrixPSDRegularization_posSemidef
    {A : CMatrix a} (hA : A.PosSemidef) (ε : ℝ) :
    (cMatrixPSDRegularization A ε).PosSemidef := by
  exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hA
    (show 0 ≤ max ε 0 from le_max_right ε 0)

omit [Fintype a] in
/-- PSD identity regularization is positive definite for positive parameter. -/
theorem cMatrixPSDRegularization_posDef_of_pos
    {A : CMatrix a} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (cMatrixPSDRegularization A ε).PosDef := by
  have hmax : max ε 0 = ε := max_eq_left hε.le
  simpa [cMatrixPSDRegularization, hmax] using
    State.cMatrix_posSemidef_add_pos_smul_one_posDef hA hε

omit [Fintype a] in
/-- PSD identity regularization tends back to the original matrix as
`ε → 0+`. -/
theorem cMatrixPSDRegularization_tendsto_zero (A : CMatrix a) :
    Filter.Tendsto (fun ε : ℝ => cMatrixPSDRegularization A ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds A) := by
  have hcont : Continuous fun ε : ℝ => cMatrixPSDRegularization A ε := by
    unfold cMatrixPSDRegularization
    fun_prop
  simpa [cMatrixPSDRegularization] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))).tendsto

omit [DecidableEq a] in
/-- The real trace of a binary complex-matrix convex combination is the same
binary convex combination of the real traces. -/
theorem cMatrixConvexCombination_trace_re
    (t : ℝ) (A B : CMatrix a) :
    ((cMatrixConvexCombination t A B).trace).re =
      t * A.trace.re + (1 - t) * B.trace.re := by
  simp [cMatrixConvexCombination, Matrix.trace_add, Matrix.trace_smul,
    Complex.mul_re]

/-- Power-of-power cancellation for PSD matrices and a positive real exponent. -/
theorem cMatrix_rpow_rpow_inv_of_pos
    {A : CMatrix a} (hA : A.PosSemidef) {c : ℝ} (hc_pos : 0 < c) :
    CFC.rpow (CFC.rpow A c) (1 / c) = A := by
  have hinv_nonneg : 0 ≤ (1 / c : ℝ) :=
    div_nonneg zero_le_one hc_pos.le
  have hmul : c * (1 / c) = (1 : ℝ) := by
    field_simp [hc_pos.ne']
  calc
    CFC.rpow (CFC.rpow A c) (1 / c) = CFC.rpow A (1 : ℝ) :=
      cMatrix_rpow_rpow_of_nonneg hA hc_pos.le hinv_nonneg hmul
    _ = A := by
      exact CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)

/-- Power-of-power reduction for positive-definite matrices and arbitrary
real exponents.

This is the positive-definite counterpart of
`cMatrix_rpow_rpow_of_nonneg`; it is needed for the Gour/Frank--Lieb
low-`α` Young optimizer, where the relevant exponent is negative. -/
theorem cMatrix_rpow_rpow_of_posDef
    {A : CMatrix a} (hA : A.PosDef)
    {r t s : ℝ} (hr_ne : r ≠ 0) (hrt : r * t = s) :
    CFC.rpow (CFC.rpow A r) t = CFC.rpow A s := by
  calc
    CFC.rpow (CFC.rpow A r) t = CFC.rpow A (r * t) := by
      exact CFC.rpow_rpow A r t hr_ne
        (ha := Matrix.PosDef.isStrictlyPositive hA)
    _ = CFC.rpow A s := by
      rw [hrt]

/-- Nonnegative real powers of the same PSD matrix multiply by adding
exponents. -/
theorem cMatrix_rpow_mul_rpow_of_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    CFC.rpow A r * CFC.rpow A s = CFC.rpow A (r + s) := by
  let rNN : ℝ≥0 := ⟨r, hr⟩
  let sNN : ℝ≥0 := ⟨s, hs⟩
  by_cases hr_zero : rNN = 0
  · have hr' : r = 0 := by
      have hcoe := congrArg (fun x : ℝ≥0 => x.val) hr_zero
      simpa [rNN] using hcoe
    have hzero : CFC.rpow A (0 : ℝ) = 1 := by
      simp only [CFC.rpow]
      simpa using cfc_const_one (R := ℝ≥0) A
    rw [hr', zero_add, hzero, Matrix.one_mul]
  · by_cases hs_zero : sNN = 0
    · have hs' : s = 0 := by
        have hcoe := congrArg (fun x : ℝ≥0 => x.val) hs_zero
        simpa [sNN] using hcoe
      have hzero : CFC.rpow A (0 : ℝ) = 1 := by
        simp only [CFC.rpow]
        simpa using cfc_const_one (R := ℝ≥0) A
      rw [hs', add_zero, hzero, Matrix.mul_one]
    · have hsum : ((rNN + sNN : ℝ≥0) : ℝ) = r + s := by rfl
      have hrNN_pos : 0 < rNN := pos_iff_ne_zero.mpr hr_zero
      have hsNN_pos : 0 < sNN := pos_iff_ne_zero.mpr hs_zero
      have hadd : A ^ (rNN + sNN) = A ^ rNN * A ^ sNN :=
        CFC.nnrpow_add (a := A) hrNN_pos hsNN_pos
      have hrpow : A ^ rNN = CFC.rpow A r := by
        simpa [rNN] using (CFC.nnrpow_eq_rpow (a := A) hrNN_pos)
      have hspow : A ^ sNN = CFC.rpow A s := by
        simpa [sNN] using (CFC.nnrpow_eq_rpow (a := A) hsNN_pos)
      have hsumpow : A ^ (rNN + sNN) = CFC.rpow A (r + s) := by
        simpa [rNN, sNN, hsum] using (CFC.nnrpow_eq_rpow (a := A)
          (add_pos hrNN_pos hsNN_pos))
      rw [← hrpow, ← hspow, ← hsumpow, hadd]

/-- Epstein's trace functional primitive
`Tr[(K† σ^c K)^(1/c)]`, written as a real trace.

This is the matrix term appearing in the Frank--Lieb low-`α` proof after
the reverse-Holder reduction.  The unrestricted concavity theorem is the
remaining source theorem; this definition only fixes the local expression
used by its closed helper lemmas. -/
def epsteinTraceTerm (K σ : CMatrix a) (c : ℝ) : ℝ :=
  ((CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)).trace).re

/-- Epstein--Young dual objective for the trace functional
`Tr[(K† σ^c K)^(1/c)]`.

For `0 < c < 1`, the missing unrestricted Frank--Lieb theorem can be routed
through the variational formula saying that the supremum of this objective
over PSD `X` is `epsteinTraceTerm K σ c`; the remaining hard input is Lieb
trace concavity for the first trace term. -/
def epsteinDualObjective (K σ X : CMatrix a) (c : ℝ) : ℝ :=
  (1 / c) * (((star K * CFC.rpow σ c * K) *
    CFC.rpow X (1 - c)).trace).re - ((1 - c) / c) * X.trace.re

/-- Epstein--Young dual objective values over PSD side matrices. -/
def epsteinDualObjectiveValueSet
    (K σ : CMatrix a) (c : ℝ) : Set ℝ :=
  {y | ∃ X : CMatrix a, X.PosSemidef ∧
    y = epsteinDualObjective K σ X c}

/-- The inner Epstein matrix `K† σ^c K` is PSD for PSD `σ`. -/
theorem epsteinTraceTerm_inner_posSemidef
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef) (c : ℝ) :
    (star K * CFC.rpow σ c * K).PosSemidef := by
  have hσc : (CFC.rpow σ c).PosSemidef :=
    cMatrix_rpow_posSemidef (A := σ) (s := c) hσ
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same hσc K

/-- Epstein's trace functional is nonnegative on PSD inputs. -/
theorem epsteinTraceTerm_nonneg
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef) (c : ℝ) :
    0 ≤ epsteinTraceTerm K σ c := by
  have hinner : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  have hpow :
      (CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)).PosSemidef :=
    cMatrix_rpow_posSemidef
      (A := star K * CFC.rpow σ c * K) (s := 1 / c) hinner
  simpa [epsteinTraceTerm] using (Matrix.PosSemidef.trace_nonneg hpow).1

/-- The first trace term in the Epstein--Young objective is nonnegative on
PSD inputs. -/
theorem epsteinDualObjective_traceTerm_nonneg
    (K : CMatrix a) {σ X : CMatrix a}
    (hσ : σ.PosSemidef) (hX : X.PosSemidef) {c : ℝ} (_hc_le_one : c ≤ 1) :
    0 ≤ (((star K * CFC.rpow σ c * K) *
      CFC.rpow X (1 - c)).trace).re := by
  have hM : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  have hXpow : (CFC.rpow X (1 - c)).PosSemidef :=
    cMatrix_rpow_posSemidef (A := X) (s := 1 - c) hX
  exact cMatrix_trace_mul_posSemidef_re_nonneg hM hXpow

omit [Fintype a] [DecidableEq a] in
private theorem epstein_young_scalar_bound
    {A S c : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S ≤ A := by
  have hc_le : 0 ≤ c := le_of_lt hc_pos
  have hone_sub_nonneg : 0 ≤ 1 - c := sub_nonneg.mpr hc_lt_one.le
  have hweights : c + (1 - c) = (1 : ℝ) := by ring
  have hgeom :
      A ^ c * S ^ (1 - c) ≤ c * A + (1 - c) * S :=
    Real.geom_mean_le_arith_mean2_weighted hc_le hone_sub_nonneg hA hS hweights
  have hinv_nonneg : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  calc
    (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S
        ≤ (1 / c) * (c * A + (1 - c) * S) - ((1 - c) / c) * S :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left hgeom hinv_nonneg) _
    _ = A := by
          field_simp [hc_pos.ne']
          ring

/-- Unnormalized PSD Holder handoff used by the Epstein--Young variational
upper bound.

This is the positive-power side of the Schatten variational formula after
normalizing the PSD side variable by its trace. -/
theorem posSemidef_trace_mul_rpow_le_psdSchattenPNorm_mul_trace_rpow
    {M X : CMatrix a} (hM : M.PosSemidef) (hX : X.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    ((M * CFC.rpow X (1 - c)).trace).re ≤
      psdSchattenPNorm M hM (1 / c) * X.trace.re ^ (1 - c) := by
  let S : ℝ := X.trace.re
  let T : ℝ := ((M * CFC.rpow X (1 - c)).trace).re
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using (Matrix.PosSemidef.trace_nonneg hX).1
  have hr_pos : 0 < 1 - c := sub_pos.mpr hc_lt_one
  by_cases hS_zero : S = 0
  · have hX_trace_im : X.trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg hX).2.symm
    have hX_trace_zero : X.trace = 0 := by
      exact Complex.ext (by simpa [S] using hS_zero) hX_trace_im
    have hX_zero : X = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hX).mp hX_trace_zero
    have hXpow_zero : CFC.rpow X (1 - c) = 0 := by
      rw [hX_zero]
      simpa using (CFC.zero_rpow (A := CMatrix a) (x := 1 - c) (ne_of_gt hr_pos))
    rw [hXpow_zero]
    simp [S, hS_zero, Real.zero_rpow (ne_of_gt hr_pos)]
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_zero)
    let N : CMatrix a := (S⁻¹ : ℝ) • X
    have hscale_nonneg : 0 ≤ S⁻¹ := inv_nonneg.mpr hS_nonneg
    have hN : N.PosSemidef := by
      simpa [N] using Matrix.PosSemidef.smul hX hscale_nonneg
    have hNtr : N.trace.re = 1 := by
      have hX_trace_im : X.trace.im = 0 :=
        (Matrix.PosSemidef.trace_nonneg hX).2.symm
      simp [N, S, Matrix.trace_smul, Complex.mul_re, hX_trace_im,
        inv_mul_cancel₀ hS_zero]
    have hpq : (1 / c).HolderConjugate (1 / (1 - c)) := by
      simpa [one_div] using Real.HolderConjugate.inv_one_sub_inv hc_pos hc_lt_one
    have hr : 1 - c = 1 / (1 / (1 - c)) := by
      field_simp [ne_of_gt hr_pos]
    have hholder :
        ((M * CFC.rpow N (1 - c)).trace).re ≤
          psdSchattenPNorm M hM (1 / c) :=
      psd_trace_rpow_holder_variational_upper
        (M := M) (N := N) hM hN hNtr hpq hr
    have hNpow :
        CFC.rpow N (1 - c) =
          (S⁻¹ ^ (1 - c) : ℝ) • CFC.rpow X (1 - c) := by
      simpa [N] using
        cMatrix_rpow_real_smul_posSemidef_schatten
          (A := X) (s := 1 - c) hX hscale_nonneg
    have hholder' :
        ((M * ((S⁻¹ ^ (1 - c) : ℝ) • CFC.rpow X (1 - c))).trace).re ≤
          psdSchattenPNorm M hM (1 / c) := by
      have hholder' := hholder
      rw [hNpow] at hholder'
      exact hholder'
    have htrace_smul :
        ((M * ((S⁻¹ ^ (1 - c) : ℝ) • CFC.rpow X (1 - c))).trace).re =
          S⁻¹ ^ (1 - c) * T := by
      simp [T, Matrix.trace_smul, Complex.mul_re]
    have hscaled :
        S⁻¹ ^ (1 - c) * T ≤ psdSchattenPNorm M hM (1 / c) := by
      simpa [htrace_smul] using hholder'
    have hSr_nonneg : 0 ≤ S ^ (1 - c) := Real.rpow_nonneg hS_nonneg _
    have hSr_pos : 0 < S ^ (1 - c) := Real.rpow_pos_of_pos hS_pos _
    have hscale_mul : S⁻¹ ^ (1 - c) * S ^ (1 - c) = 1 := by
      rw [Real.inv_rpow hS_nonneg]
      exact inv_mul_cancel₀ (ne_of_gt hSr_pos)
    have hmul :
        (S⁻¹ ^ (1 - c) * T) * S ^ (1 - c) ≤
          psdSchattenPNorm M hM (1 / c) * S ^ (1 - c) :=
      mul_le_mul_of_nonneg_right hscaled hSr_nonneg
    calc
      T = (S⁻¹ ^ (1 - c) * T) * S ^ (1 - c) := by
            exact
              (calc
                (S⁻¹ ^ (1 - c) * T) * S ^ (1 - c) =
                    T * (S⁻¹ ^ (1 - c) * S ^ (1 - c)) := by ring
                _ = T := by rw [hscale_mul, mul_one]).symm
      _ ≤ psdSchattenPNorm M hM (1 / c) * S ^ (1 - c) := hmul

/-- Upper-bound side of the finite-dimensional Epstein--Young variational
formula for the Epstein trace primitive. -/
theorem epsteinDualObjective_le_epsteinTraceTerm
    (K : CMatrix a) {σ X : CMatrix a}
    (hσ : σ.PosSemidef) (hX : X.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    epsteinDualObjective K σ X c ≤ epsteinTraceTerm K σ c := by
  let M : CMatrix a := star K * CFC.rpow σ c * K
  let A : ℝ := epsteinTraceTerm K σ c
  let S : ℝ := X.trace.re
  let T : ℝ := ((M * CFC.rpow X (1 - c)).trace).re
  have hM : M.PosSemidef := by
    simpa [M] using epsteinTraceTerm_inner_posSemidef K hσ c
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using epsteinTraceTerm_nonneg K hσ c
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using (Matrix.PosSemidef.trace_nonneg hX).1
  have htrace_holder :
      T ≤ psdSchattenPNorm M hM (1 / c) * S ^ (1 - c) := by
    simpa [T, S] using
      posSemidef_trace_mul_rpow_le_psdSchattenPNorm_mul_trace_rpow
        (M := M) (X := X) hM hX hc_pos hc_lt_one
  have hnorm :
      psdSchattenPNorm M hM (1 / c) = A ^ c := by
    have hpower_eq : psdTracePower M hM (1 / c) = A := by
      change (CFC.rpow M (1 / c)).trace.re = A
      rfl
    have hinv : 1 / (1 / c) = c := by
      field_simp [hc_pos.ne']
    rw [psdSchattenPNorm, hpower_eq, hinv]
    rfl
  have htrace_bound : T ≤ A ^ c * S ^ (1 - c) := by
    rw [hnorm] at htrace_holder
    exact htrace_holder
  have hinv_nonneg : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  have hscaled :
      (1 / c) * T - ((1 - c) / c) * S ≤
        (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left htrace_bound hinv_nonneg) _
  have hyoung :
      (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S ≤ A :=
    epstein_young_scalar_bound hA_nonneg hS_nonneg hc_pos hc_lt_one
  have hmain :
      (1 / c) * T - ((1 - c) / c) * S ≤ A := hscaled.trans hyoung
  simpa [epsteinDualObjective, A, S, T, M] using hmain

omit [DecidableEq a] in
/-- The linear penalty term in the Epstein--Young objective is affine in the
side variable. -/
theorem epsteinDualObjective_penalty_convexCombination
    (X₁ X₂ : CMatrix a) (c t : ℝ) :
    ((1 - c) / c) * (cMatrixConvexCombination t X₁ X₂).trace.re =
      t * (((1 - c) / c) * X₁.trace.re) +
        (1 - t) * (((1 - c) / c) * X₂.trace.re) := by
  rw [cMatrixConvexCombination_trace_re]
  ring

/-- Lieb--Ando supplies the Epstein--Young first trace-term concavity.

This is the concrete Frank--Lieb bridge for the dual objective: vectorize the
fixed matrix `K` into the PSD tensor weight `|K⟩⟨K|`, apply the tensor
positive-functional Lieb--Ando concavity theorem to
`σ ↦ σ^c` and `X ↦ X^(1-c)`, then convert back with the vectorized trace
identity. -/
theorem epsteinDualObjective_traceTerm_concave
    (K σ₁ σ₂ X₁ X₂ : CMatrix a)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    (hX₁ : X₁.PosSemidef) (hX₂ : X₂.PosSemidef)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((((star K * CFC.rpow σ₁ c * K) *
              CFC.rpow X₁ (1 - c)).trace).re) +
          (1 - t) * ((((star K * CFC.rpow σ₂ c * K) *
              CFC.rpow X₂ (1 - c)).trace).re) ≤
        ((((star K * CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c * K) *
            CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).trace).re) := by
  let p : ℝ≥0 := ⟨c, hc_pos.le⟩
  have hp : p ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    constructor
    · exact_mod_cast hc_pos
    · exact_mod_cast hc_lt_one
  have hX₁T : X₁.transpose.PosSemidef := hX₁.transpose
  have hX₂T : X₂.transpose.PosSemidef := hX₂.transpose
  have hW : (cMatrixVecWeight K).PosSemidef := cMatrixVecWeight_posSemidef K
  have htensor :=
    liebAndo_tensorWeightedTraceConcavity_posSemidef
      (a := a) (b := a) (p := p) hp
      (A₁ := σ₁) (A₂ := σ₂)
      (B₁ := X₁.transpose) (B₂ := X₂.transpose)
      (W := cMatrixVecWeight K)
      hσ₁ hσ₂ hX₁T hX₂T hW ht0 ht1
  have h1c_nonneg : 0 ≤ 1 - c := sub_nonneg.mpr hc_lt_one.le
  have hX₁powT :
      CFC.rpow X₁.transpose (1 - (p : ℝ)) =
        (CFC.rpow X₁ (1 - c)).transpose := by
    simpa [p] using cMatrix_rpow_transpose_nonneg (A := X₁) hX₁ h1c_nonneg
  have hX₂powT :
      CFC.rpow X₂.transpose (1 - (p : ℝ)) =
        (CFC.rpow X₂ (1 - c)).transpose := by
    simpa [p] using cMatrix_rpow_transpose_nonneg (A := X₂) hX₂ h1c_nonneg
  have hXmix : (cMatrixConvexCombination t X₁ X₂).PosSemidef :=
    cMatrixConvexCombination_posSemidef hX₁ hX₂ ht0 ht1
  have hXmixT :
      t • X₁.transpose + (1 - t) • X₂.transpose =
        (cMatrixConvexCombination t X₁ X₂).transpose := by
    ext i j
    simp [cMatrixConvexCombination]
  have hXmixpowT :
      CFC.rpow (t • X₁.transpose + (1 - t) • X₂.transpose) (1 - (p : ℝ)) =
        (CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).transpose := by
    rw [hXmixT]
    simpa [p] using
      cMatrix_rpow_transpose_nonneg
        (A := cMatrixConvexCombination t X₁ X₂) hXmix h1c_nonneg
  have hσmix :
      t • σ₁ + (1 - t) • σ₂ = cMatrixConvexCombination t σ₁ σ₂ :=
    (cMatrixConvexCombination_eq_real_smul t σ₁ σ₂).symm
  have htrace₁ :=
    epstein_traceTerm_tensor_trace_transpose_re K
      (CFC.rpow σ₁ c) (CFC.rpow X₁ (1 - c))
  have htrace₂ :=
    epstein_traceTerm_tensor_trace_transpose_re K
      (CFC.rpow σ₂ c) (CFC.rpow X₂ (1 - c))
  have htracet :=
    epstein_traceTerm_tensor_trace_transpose_re K
      (CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c)
      (CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c))
  have htensor' := htensor
  rw [hX₁powT, hX₂powT, hXmixpowT, hσmix] at htensor'
  have hpcoe : (p : ℝ) = c := rfl
  rw [hpcoe] at htensor'
  rw [htrace₁, htrace₂, htracet]
  simpa using htensor'

/-- Algebraic handoff from Lieb trace concavity to concavity of the
Epstein--Young dual objective.

The hard theorem is the hypothesis `htrace`, i.e. Lieb trace concavity for
the first term. This lemma only transports that theorem through the affine
penalty in `X`. -/
theorem epsteinDualObjective_concave_of_traceTerm
    (K σ₁ σ₂ X₁ X₂ : CMatrix a)
    {c t : ℝ} (hc_pos : 0 < c)
    (htrace :
      t * ((((star K * CFC.rpow σ₁ c * K) *
              CFC.rpow X₁ (1 - c)).trace).re) +
          (1 - t) * ((((star K * CFC.rpow σ₂ c * K) *
              CFC.rpow X₂ (1 - c)).trace).re) ≤
        ((((star K * CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c * K) *
            CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).trace).re)) :
    t * epsteinDualObjective K σ₁ X₁ c +
        (1 - t) * epsteinDualObjective K σ₂ X₂ c ≤
      epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂)
        (cMatrixConvexCombination t X₁ X₂) c := by
  let T₁ : ℝ :=
    ((((star K * CFC.rpow σ₁ c * K) *
      CFC.rpow X₁ (1 - c)).trace).re)
  let T₂ : ℝ :=
    ((((star K * CFC.rpow σ₂ c * K) *
      CFC.rpow X₂ (1 - c)).trace).re)
  let Tt : ℝ :=
    ((((star K * CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c * K) *
      CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).trace).re)
  have htrace' : t * T₁ + (1 - t) * T₂ ≤ Tt := by
    simpa [T₁, T₂, Tt] using htrace
  have hinv_nonneg : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  have hscaled :
      (1 / c) * (t * T₁ + (1 - t) * T₂) ≤ (1 / c) * Tt :=
    mul_le_mul_of_nonneg_left htrace' hinv_nonneg
  have hpenalty :
      ((1 - c) / c) * (cMatrixConvexCombination t X₁ X₂).trace.re =
        t * (((1 - c) / c) * X₁.trace.re) +
          (1 - t) * (((1 - c) / c) * X₂.trace.re) :=
    epsteinDualObjective_penalty_convexCombination X₁ X₂ c t
  unfold epsteinDualObjective
  dsimp [T₁, T₂, Tt] at hscaled
  rw [hpenalty]
  nlinarith

/-- Concavity of the Epstein--Young dual objective in the two PSD inputs.

This is the first complete Frank--Lieb handoff: the hard first trace term is
provided by `epsteinDualObjective_traceTerm_concave`; the remaining penalty is
affine. -/
theorem epsteinDualObjective_concave
    (K σ₁ σ₂ X₁ X₂ : CMatrix a)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    (hX₁ : X₁.PosSemidef) (hX₂ : X₂.PosSemidef)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * epsteinDualObjective K σ₁ X₁ c +
        (1 - t) * epsteinDualObjective K σ₂ X₂ c ≤
      epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂)
        (cMatrixConvexCombination t X₁ X₂) c := by
  exact
    epsteinDualObjective_concave_of_traceTerm K σ₁ σ₂ X₁ X₂ hc_pos
      (epsteinDualObjective_traceTerm_concave K σ₁ σ₂ X₁ X₂
        hc_pos hc_lt_one hσ₁ hσ₂ hX₁ hX₂ ht0 ht1)

/-- The Epstein--Young objective attains the Epstein trace term at the
natural optimizer `X = (K† σ^c K)^(1/c)`.

This is the equality side of the finite-dimensional Young variational formula.
The complementary upper-bound direction remains the hard analytic ingredient. -/
theorem epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    epsteinDualObjective K σ
      (CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)) c =
        epsteinTraceTerm K σ c := by
  let M : CMatrix a := star K * CFC.rpow σ c * K
  have hM : M.PosSemidef := by
    simpa [M] using epsteinTraceTerm_inner_posSemidef K hσ c
  have hinv_nonneg : 0 ≤ (1 / c : ℝ) := div_nonneg zero_le_one hc_pos.le
  have hsub_nonneg : 0 ≤ (1 - c : ℝ) := sub_nonneg.mpr hc_lt_one.le
  have hpowX :
      CFC.rpow (CFC.rpow M (1 / c)) (1 - c) =
        CFC.rpow M ((1 / c) * (1 - c)) :=
    cMatrix_rpow_rpow_of_nonneg hM hinv_nonneg hsub_nonneg rfl
  have hMone : CFC.rpow M (1 : ℝ) = M :=
    CFC.rpow_one M (ha := Matrix.nonneg_iff_posSemidef.mpr hM)
  have hadd :
      (1 : ℝ) + (1 / c) * (1 - c) = 1 / c := by
    field_simp [hc_pos.ne']
    ring
  have hmul :
      M * CFC.rpow M ((1 / c) * (1 - c)) =
        CFC.rpow M (1 / c) := by
    calc
      M * CFC.rpow M ((1 / c) * (1 - c))
          = CFC.rpow M (1 : ℝ) *
              CFC.rpow M ((1 / c) * (1 - c)) := by rw [hMone]
      _ = CFC.rpow M ((1 : ℝ) + (1 / c) * (1 - c)) :=
          cMatrix_rpow_mul_rpow_of_nonneg hM zero_le_one
            (mul_nonneg hinv_nonneg hsub_nonneg)
      _ = CFC.rpow M (1 / c) := by rw [hadd]
  have hfirst :
      (((star K * CFC.rpow σ c * K) *
          CFC.rpow (CFC.rpow (star K * CFC.rpow σ c * K) (1 / c))
            (1 - c)).trace).re =
        epsteinTraceTerm K σ c := by
    change ((M * CFC.rpow (CFC.rpow M (1 / c)) (1 - c)).trace).re =
      epsteinTraceTerm K σ c
    rw [hpowX, hmul]
    rfl
  have hoptimizerTrace :
      ((CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σ c := by
    rfl
  unfold epsteinDualObjective
  rw [hfirst, hoptimizerTrace]
  field_simp [hc_pos.ne']
  ring

theorem epsteinDualObjectiveValueSet_mem
    {K σ X : CMatrix a} (hX : X.PosSemidef) (c : ℝ) :
    epsteinDualObjective K σ X c ∈
      epsteinDualObjectiveValueSet K σ c :=
  ⟨X, hX, rfl⟩

/-- Finite-dimensional Epstein--Young variational formula as a greatest-value
statement.

This packages the already proved Young upper bound and optimizer equality:
for `0 < c < 1`, the trace primitive
`Tr[(K† σ^c K)^(1/c)]` is the supremal value of the Epstein--Young dual
objective over PSD side matrices. -/
theorem epsteinDualObjectiveValueSet_isGreatest
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    IsGreatest (epsteinDualObjectiveValueSet K σ c)
      (epsteinTraceTerm K σ c) := by
  let X : CMatrix a :=
    CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)
  have hinner : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  have hX : X.PosSemidef := by
    simpa [X] using
      cMatrix_rpow_posSemidef
        (A := star K * CFC.rpow σ c * K) (s := 1 / c) hinner
  constructor
  · refine ⟨X, hX, ?_⟩
    simpa [X] using
      (epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
        (a := a) K hσ hc_pos hc_lt_one).symm
  · intro y hy
    rcases hy with ⟨Y, hY, rfl⟩
    exact epsteinDualObjective_le_epsteinTraceTerm
      (a := a) K hσ hY hc_pos hc_lt_one

/-- `sSup` form of the finite-dimensional Epstein--Young variational
formula. -/
theorem epsteinDualObjectiveValueSet_sSup_eq
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    sSup (epsteinDualObjectiveValueSet K σ c) =
      epsteinTraceTerm K σ c :=
  (epsteinDualObjectiveValueSet_isGreatest
    (a := a) K hσ hc_pos hc_lt_one).csSup_eq

/-- Unrestricted finite-dimensional Epstein trace concavity.

For `0 < c < 1`, the map
`σ ↦ Tr[(K† σ^c K)^(1/c)]` is concave on PSD matrices.  This is the
minimum Epstein/Frank--Lieb theorem needed before converting the low-alpha
sandwiched `Q` functional to partial-trace monotonicity. -/
theorem epsteinTraceTerm_concave
    (K : CMatrix a) {σ₁ σ₂ : CMatrix a}
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * epsteinTraceTerm K σ₁ c +
        (1 - t) * epsteinTraceTerm K σ₂ c ≤
      epsteinTraceTerm K (cMatrixConvexCombination t σ₁ σ₂) c := by
  let X₁ : CMatrix a := CFC.rpow (star K * CFC.rpow σ₁ c * K) (1 / c)
  let X₂ : CMatrix a := CFC.rpow (star K * CFC.rpow σ₂ c * K) (1 / c)
  let Xt : CMatrix a := cMatrixConvexCombination t X₁ X₂
  have hM₁ : (star K * CFC.rpow σ₁ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ₁ c
  have hM₂ : (star K * CFC.rpow σ₂ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ₂ c
  have hX₁ : X₁.PosSemidef := by
    simpa [X₁] using
      cMatrix_rpow_posSemidef
        (A := star K * CFC.rpow σ₁ c * K) (s := 1 / c) hM₁
  have hX₂ : X₂.PosSemidef := by
    simpa [X₂] using
      cMatrix_rpow_posSemidef
        (A := star K * CFC.rpow σ₂ c * K) (s := 1 / c) hM₂
  have hσt : (cMatrixConvexCombination t σ₁ σ₂).PosSemidef :=
    cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1
  have hXt : Xt.PosSemidef := by
    simpa [Xt] using cMatrixConvexCombination_posSemidef hX₁ hX₂ ht0 ht1
  have hconc :
      t * epsteinDualObjective K σ₁ X₁ c +
          (1 - t) * epsteinDualObjective K σ₂ X₂ c ≤
        epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂) Xt c := by
    simpa [Xt] using
      epsteinDualObjective_concave K σ₁ σ₂ X₁ X₂
        hc_pos hc_lt_one hσ₁ hσ₂ hX₁ hX₂ ht0 ht1
  have heq₁ :
      epsteinDualObjective K σ₁ X₁ c = epsteinTraceTerm K σ₁ c := by
    simpa [X₁] using
      epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
        K hσ₁ hc_pos hc_lt_one
  have heq₂ :
      epsteinDualObjective K σ₂ X₂ c = epsteinTraceTerm K σ₂ c := by
    simpa [X₂] using
      epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
        K hσ₂ hc_pos hc_lt_one
  have hupper :
      epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂) Xt c ≤
        epsteinTraceTerm K (cMatrixConvexCombination t σ₁ σ₂) c :=
    epsteinDualObjective_le_epsteinTraceTerm K hσt hXt hc_pos hc_lt_one
  rw [heq₁, heq₂] at hconc
  exact hconc.trans hupper

namespace State

open RenyiDPI.Statement

/-- In the low-`alpha` Frank--Lieb range, the sandwiched reference exponent
`(1 - alpha) / (2 * alpha)` is nonnegative. -/
theorem sandwichedRenyiQ_sandwichExponent_nonneg
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    0 ≤ (1 - α) / (2 * α) := by
  have hα_pos : 0 < α := by
    linarith
  exact div_nonneg
    (sub_nonneg.mpr (le_of_lt hα_lt_one))
    (mul_nonneg (by norm_num) (le_of_lt hα_pos))

/-- In the low-`alpha` Frank--Lieb range, the trace-power exponent itself is
nonnegative. -/
theorem sandwichedRenyiQ_alpha_nonneg_of_lowAlpha
    {α : ℝ} (hα_half : 1 / 2 ≤ α) :
    0 ≤ α := by
  linarith

/-- In the strict low-`alpha` Frank--Lieb range, the Epstein exponent
`c = (1 - alpha) / alpha` is positive. -/
theorem sandwichedRenyiQ_frankLiebExponent_pos
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    0 < (1 - α) / α := by
  have hα_pos : 0 < α := by linarith
  exact div_pos (sub_pos.mpr hα_lt_one) hα_pos

/-- In the strict low-`alpha` Frank--Lieb range, the Epstein exponent
`c = (1 - alpha) / alpha` is less than one. -/
theorem sandwichedRenyiQ_frankLiebExponent_lt_one
    {α : ℝ} (hα_half : 1 / 2 < α) (_hα_lt_one : α < 1) :
    (1 - α) / α < 1 := by
  have hα_pos : 0 < α := by linarith
  rw [div_lt_one hα_pos]
  linarith

/-- Matrix-level sandwiched Renyi inner operator
`σ^((1 - α) / (2 * α)) ρ σ^((1 - α) / (2 * α))`.

This is the PSD input used in the Frank--Lieb low-`α` reverse-Holder
variational step before applying Lieb concavity. -/
def sandwichedRenyiQInner (ρ σ : CMatrix a) (α : ℝ) : CMatrix a :=
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ s
  C * ρ * C

/-- The matrix-level sandwiched Renyi `Q` inner operator is PSD for PSD inputs. -/
theorem sandwichedRenyiQInner_posSemidef
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) :
    (sandwichedRenyiQInner ρ σ α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hC : C.PosSemidef := by
    simpa [C] using cMatrix_rpow_posSemidef (A := σ) (s := s) hσ
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hρ C
  rw [hCstar] at hinner
  simpa [sandwichedRenyiQInner, s, C] using hinner

/-- The matrix-level sandwiched Renyi `Q` inner operator is positive definite
for positive-definite inputs. -/
theorem sandwichedRenyiQInner_posDef
    {ρ σ : CMatrix a} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (α : ℝ) :
    (sandwichedRenyiQInner ρ σ α).PosDef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hC : C.PosDef := by
    simpa [C] using cMatrix_rpow_posDef_of_posDef hσ s
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ * C).PosDef := by
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff hC.isUnit]
    exact hρ
  rw [hCstar] at hinner
  simpa [sandwichedRenyiQInner, s, C] using hinner

/-- With a positive-definite reference, the sandwiched `Q` inner operator
vanishes exactly when the left input vanishes. -/
theorem sandwichedRenyiQInner_eq_zero_iff_left_eq_zero_of_sigma_posDef
    {ρ σ : CMatrix a} (hσ : σ.PosDef) (α : ℝ) :
    sandwichedRenyiQInner ρ σ α = 0 ↔ ρ = 0 := by
  constructor
  · intro hinner
    let s : ℝ := (1 - α) / (2 * α)
    let C : CMatrix a := CFC.rpow σ s
    have hC : C.PosDef := by
      simpa [C] using cMatrix_rpow_posDef_of_posDef hσ s
    have hdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
    have hleft : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hdet
    have hright : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hdet
    have hinnerC : C * ρ * C = 0 := by
      simpa [sandwichedRenyiQInner, s, C] using hinner
    have hrho :
        ρ = C⁻¹ * (C * ρ * C) * C⁻¹ := by
      calc
        ρ = (1 : CMatrix a) * ρ * (1 : CMatrix a) := by simp
        _ = (C⁻¹ * C) * ρ * (C * C⁻¹) := by rw [hleft, hright]
        _ = C⁻¹ * (C * ρ * C) * C⁻¹ := by simp [Matrix.mul_assoc]
    rw [hinnerC] at hrho
    simpa using hrho
  · intro hρ
    simp [sandwichedRenyiQInner, hρ]

/-- Definition bridge from matrix-level `sandwichedRenyiQ` to the PSD trace
power used by the Schatten variational API. -/
theorem sandwichedRenyiQ_eq_psdTracePower_QInner
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) :
    sandwichedRenyiQ ρ σ hρ hσ α =
      psdTracePower (sandwichedRenyiQInner ρ σ α)
        (sandwichedRenyiQInner_posSemidef hρ hσ α) α := by
  unfold sandwichedRenyiQ sandwichedRenyiQInner psdTracePower
  rfl

/-- The PSD-friendly low-`α` `Q` functional is continuous along
PSD-constrained matrix paths when the reference sandwich exponent is
positive. -/
theorem sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X}
    {ρF σF : X → CMatrix a} {ρ σ : CMatrix a}
    {α : ℝ} (hα_pos : 0 < α)
    (hs_pos : 0 < (1 - α) / (2 * α))
    (hρF : Filter.Tendsto ρF l (nhds ρ))
    (hσF : Filter.Tendsto σF l (nhds σ))
    (hρFpsd : ∀ x, (ρF x).PosSemidef)
    (hσFpsd : ∀ x, (σF x).PosSemidef)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    Filter.Tendsto
      (fun x => sandwichedRenyiQ (ρF x) (σF x)
        (hρFpsd x) (hσFpsd x) α)
      l
      (nhds (sandwichedRenyiQ ρ σ hρ hσ α)) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hσpow :
      Filter.Tendsto (fun x => CFC.rpow (σF x) s) l
        (nhds (CFC.rpow σ s)) := by
    exact cMatrix_rpow_tendsto_of_tendsto_posSemidef
      (a := a) (p := s) (by simpa [s] using hs_pos)
      hσF (Filter.Eventually.of_forall hσFpsd) hσ
  have hinner :
      Filter.Tendsto
        (fun x => sandwichedRenyiQInner (ρF x) (σF x) α)
        l
        (nhds (sandwichedRenyiQInner ρ σ α)) := by
    have hmul :
        Filter.Tendsto
          (fun x => CFC.rpow (σF x) s * ρF x * CFC.rpow (σF x) s)
          l
          (nhds (CFC.rpow σ s * ρ * CFC.rpow σ s)) :=
      (hσpow.mul hρF).mul hσpow
    simpa [sandwichedRenyiQInner, s] using hmul
  have hinner_psd :
      ∀ x, (sandwichedRenyiQInner (ρF x) (σF x) α).PosSemidef :=
    fun x => sandwichedRenyiQInner_posSemidef (hρFpsd x) (hσFpsd x) α
  have htrace :=
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      (a := a) (p := α) hα_pos hinner
      (Filter.Eventually.of_forall hinner_psd)
      (sandwichedRenyiQInner_posSemidef hρ hσ α)
  simpa [sandwichedRenyiQ, sandwichedRenyiQInner, s] using htrace

/-- The PSD-friendly low-`α` `Q` functional vanishes when the left input is
zero. -/
theorem sandwichedRenyiQ_zero_left
    (σ : CMatrix a) (hσ : σ.PosSemidef) {α : ℝ} (hα_pos : 0 < α) :
    sandwichedRenyiQ (0 : CMatrix a) σ Matrix.PosSemidef.zero hσ α = 0 := by
  let s : ℝ := (1 - α) / (2 * α)
  have hpow :
      CFC.rpow (0 : CMatrix a) α = 0 := by
    simpa using (CFC.zero_rpow (A := CMatrix a) (x := α) (ne_of_gt hα_pos))
  unfold sandwichedRenyiQ
  change (CFC.rpow (CFC.rpow σ s * (0 : CMatrix a) * CFC.rpow σ s) α).trace.re = 0
  simp only [mul_zero, zero_mul]
  rw [hpow]
  simp

/-- The PSD-friendly low-`α` `Q` functional is nonnegative on PSD inputs. -/
theorem sandwichedRenyiQ_nonneg
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) :
    0 ≤ sandwichedRenyiQ ρ σ hρ hσ α := by
  rw [sandwichedRenyiQ_eq_psdTracePower_QInner hρ hσ α]
  exact psdTracePower_nonneg
    (sandwichedRenyiQInner ρ σ α)
    (sandwichedRenyiQInner_posSemidef hρ hσ α) α

/-- A normalized state has strictly positive low-`α` `Q` value against a
positive-definite matrix reference.

This is the positivity side condition needed when the source regularizes a PSD
reference to `σ + εI`: the regularized reference is positive definite, so the
finite real logarithmic branch is available without an additional support
hypothesis. -/
theorem sandwichedRenyiQ_pos_of_state_posDef_reference
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosDef)
    (α : ℝ) :
    0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ.posSemidef α := by
  have hρ_ne : ρ.matrix ≠ 0 := by
    intro hρ_zero
    have htrace_zero : ρ.matrix.trace = 0 := by
      rw [hρ_zero]
      simp
    have hone_zero : (1 : ℂ) = 0 := by
      rw [ρ.trace_eq_one] at htrace_zero
      exact htrace_zero
    exact one_ne_zero hone_zero
  have hinner_ne : sandwichedRenyiQInner ρ.matrix σ α ≠ 0 := by
    intro hinner_zero
    have hρ_zero :
        ρ.matrix = 0 :=
      (sandwichedRenyiQInner_eq_zero_iff_left_eq_zero_of_sigma_posDef
        (ρ := ρ.matrix) (σ := σ) hσ α).mp hinner_zero
    exact hρ_ne hρ_zero
  rw [sandwichedRenyiQ_eq_psdTracePower_QInner ρ.pos hσ.posSemidef α]
  exact psdTracePower_pos_of_ne_zero
    (sandwichedRenyiQInner ρ.matrix σ α)
    (sandwichedRenyiQInner_posSemidef ρ.pos hσ.posSemidef α) hinner_ne

/-- Reverse-Holder side-state objective values for the sandwiched Renyi `Q`
inner operator.

This is the matrix-level version of the Tomamichel 2015
`renyi.tex:817-824` variational step: for `0 < α < 1`, normalized PSD
side-states `N` supporting the sandwiched inner operator give the
reverse-Holder trace objective with exponent `1 - 1 / α`. -/
def sandwichedRenyiQReverseHolderValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  psdTraceReverseHolderStateValueSet (sandwichedRenyiQInner ρ σ α) α

/-- Reverse-Holder variational lower bound for the low-`α` sandwiched Renyi
`Q` primitive.

This is a non-circular Frank--Lieb-route primitive: it only unfolds
`Q_α(ρ, σ)` to the sandwiched inner PSD trace power and applies the
reverse-Holder variational inequality. It does not assume joint concavity. -/
theorem sandwichedRenyiQ_reverseHolder_norm_le_trace
    {ρ σ N : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hN : N.PosSemidef) (hNtr : N.trace.re = 1)
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hSupport : Matrix.Supports (sandwichedRenyiQInner ρ σ α) N) :
    (sandwichedRenyiQ ρ σ hρ hσ α) ^ (1 / α) ≤
      ((sandwichedRenyiQInner ρ σ α *
        CFC.rpow N (1 - 1 / α)).trace).re := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiQInner_posSemidef hρ hσ α
  have hvar :
      psdSchattenPNorm M hM α ≤
        ((M * CFC.rpow N (1 - 1 / α)).trace).re :=
    psd_trace_rpow_reverse_holder_variational
      hM hN hNtr (by simpa [M] using hSupport) hα_pos hα_lt_one rfl
  simpa [M, psdSchattenPNorm, psdTracePower,
    sandwichedRenyiQ, sandwichedRenyiQInner] using hvar

/-- Exact reverse-Holder minimizer statement for the sandwiched Renyi `Q`
inner operator when the inner operator is nonzero.

This formalizes the source-shaped minimization primitive before the Lieb
concavity step: the minimum normalized reverse-Holder side-state value is
`Q_α(ρ, σ)^(1 / α)`. -/
theorem sandwichedRenyiQ_reverseHolder_isLeast_of_inner_ne_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hinner_ne_zero : sandwichedRenyiQInner ρ σ α ≠ 0) :
    IsLeast (sandwichedRenyiQReverseHolderValueSet ρ σ α)
      ((sandwichedRenyiQ ρ σ hρ hσ α) ^ (1 / α)) := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiQInner_posSemidef hρ hσ α
  have hleast :
      IsLeast (psdTraceReverseHolderStateValueSet M α)
        (psdSchattenPNorm M hM α) :=
    psdTraceReverseHolderStateValueSet_isLeast_of_ne_zero
      hM hα_pos hα_lt_one (by simpa [M] using hinner_ne_zero)
  simpa [sandwichedRenyiQReverseHolderValueSet, M, psdSchattenPNorm,
    psdTracePower, sandwichedRenyiQ, sandwichedRenyiQInner] using hleast

/-- Exact `sInf` form of the reverse-Holder variational formula for the
sandwiched Renyi `Q` inner operator, in the nonzero case. -/
theorem sandwichedRenyiQ_reverseHolder_sInf_eq_of_inner_ne_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hinner_ne_zero : sandwichedRenyiQInner ρ σ α ≠ 0) :
    sInf (sandwichedRenyiQReverseHolderValueSet ρ σ α) =
      (sandwichedRenyiQ ρ σ hρ hσ α) ^ (1 / α) :=
  (sandwichedRenyiQ_reverseHolder_isLeast_of_inner_ne_zero
    hρ hσ hα_half hα_lt_one hinner_ne_zero).csInf_eq

omit [Fintype a] [DecidableEq a] in
/-- The mixed `rho` input in the binary joint-concavity statement is PSD. -/
theorem sandwichedRenyiQ_rho_mix_posSemidef
    {ρ₁ ρ₂ : CMatrix a} (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t ρ₁ ρ₂).PosSemidef :=
  cMatrixConvexCombination_posSemidef hρ₁ hρ₂ ht0 ht1

omit [Fintype a] [DecidableEq a] in
/-- The mixed `sigma` input in the binary joint-concavity statement is PSD. -/
theorem sandwichedRenyiQ_sigma_mix_posSemidef
    {σ₁ σ₂ : CMatrix a} (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t σ₁ σ₂).PosSemidef :=
  cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1

/-- The fixed Frank--Lieb weight `H^(-1/2)` is Hermitian. -/
theorem frankLieb_weight_isHermitian
    {H : CMatrix a} (hH : H.PosDef) :
    (CFC.rpow H (-(1 / 2 : ℝ))).IsHermitian :=
  (cMatrix_rpow_posSemidef
    (A := H) (s := -(1 / 2 : ℝ)) hH.posSemidef).isHermitian

/-- The fixed-weight Frank--Lieb inner term
`H^(-1/2) σ^c H^(-1/2)` is PSD. -/
theorem frankLieb_sigmaTerm_inner_posSemidef
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    (K * CFC.rpow σ c * K).PosSemidef := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hKstar : star K = K := by
    simpa [K] using (frankLieb_weight_isHermitian (a := a) hH).eq
  have hinner : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  rw [hKstar] at hinner
  simpa [K] using hinner

/-- The fixed-weight Frank--Lieb trace term is nonnegative. -/
theorem frankLieb_sigmaTerm_nonneg
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    0 ≤ ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hinner : (K * CFC.rpow σ c * K).PosSemidef := by
    simpa [K] using frankLieb_sigmaTerm_inner_posSemidef
      (a := a) (H := H) (σ := σ) hH hσ c
  have hpow : (CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).PosSemidef :=
    cMatrix_rpow_posSemidef
      (A := K * CFC.rpow σ c * K) (s := 1 / c) hinner
  simpa [K] using (Matrix.PosSemidef.trace_nonneg hpow).1

/-- Scaling the positive-definite Frank--Lieb weight rescales the fixed
`sigma` term with the source-predicted homogeneity. -/
theorem frankLieb_sigmaTerm_real_smul_weight
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef)
    {lambda c : ℝ} (hlambda_pos : 0 < lambda) (_hc_pos : 0 < c) :
    let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
      lambda ^ (-(1 / c)) *
        ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let S : CMatrix a := CFC.rpow σ c
  let mu : ℝ := lambda ^ (-(1 / 2 : ℝ))
  have hKlam : Klam = mu • K := by
    simpa [Klam, K, mu] using
      cMatrix_rpow_real_smul_posSemidef_schatten
        (A := H) (s := -(1 / 2 : ℝ)) hH.posSemidef (le_of_lt hlambda_pos)
  have hmu_mul : mu * mu = lambda ^ (-1 : ℝ) := by
    dsimp [mu]
    rw [← Real.rpow_add hlambda_pos]
    ring_nf
  have hinner :
      Klam * S * Klam = (lambda ^ (-1 : ℝ)) • (K * S * K) := by
    rw [hKlam]
    calc
      (mu • K) * S * (mu • K) =
          (mu * mu) • (K * S * K) := by
            simp [smul_smul, mul_assoc]
      _ = (lambda ^ (-1 : ℝ)) • (K * S * K) := by
            rw [hmu_mul]
  have hbase : (K * S * K).PosSemidef := by
    simpa [K, S] using
      frankLieb_sigmaTerm_inner_posSemidef
        (a := a) (H := H) (σ := σ) hH hσ c
  have hscale_nonneg : 0 ≤ lambda ^ (-1 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hlambda_pos) (-1 : ℝ)
  have hpow :
      CFC.rpow (Klam * S * Klam) (1 / c) =
        (((lambda ^ (-1 : ℝ)) ^ (1 / c) : ℝ) •
          CFC.rpow (K * S * K) (1 / c)) := by
    rw [hinner]
    simpa using cMatrix_rpow_real_smul_posSemidef_schatten
      (A := K * S * K) (s := 1 / c) hbase hscale_nonneg
  have hscale :
      (lambda ^ (-1 : ℝ)) ^ (1 / c) = lambda ^ (-(1 / c)) := by
    calc
      (lambda ^ (-1 : ℝ)) ^ (1 / c) =
          lambda ^ ((-1 : ℝ) * (1 / c)) := by
            rw [← Real.rpow_mul (le_of_lt hlambda_pos)]
      _ = lambda ^ (-(1 / c)) := by
            ring_nf
  dsimp only
  change
    ((CFC.rpow (Klam * S * Klam) (1 / c)).trace).re =
      lambda ^ (-(1 / c)) *
        ((CFC.rpow (K * S * K) (1 / c)).trace).re
  calc
    ((CFC.rpow (Klam * S * Klam) (1 / c)).trace).re =
        ((((lambda ^ (-1 : ℝ)) ^ (1 / c) : ℝ) •
          CFC.rpow (K * S * K) (1 / c)).trace).re := by
          rw [hpow]
    _ = (lambda ^ (-1 : ℝ)) ^ (1 / c) *
          ((CFC.rpow (K * S * K) (1 / c)).trace).re := by
          simp [Matrix.trace_smul, Complex.mul_re]
    _ = lambda ^ (-(1 / c)) *
          ((CFC.rpow (K * S * K) (1 / c)).trace).re := by
          rw [hscale]

theorem frankLieb_sigmaTerm_inner_posDef
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosDef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    (K * CFC.rpow σ c * K).PosDef := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hK : K.PosDef := by
    simpa [K] using cMatrix_rpow_posDef_of_posDef hH (-(1 / 2 : ℝ))
  have hKstar : star K = K := hK.isHermitian.eq
  have hσc : (CFC.rpow σ c).PosDef := cMatrix_rpow_posDef_of_posDef hσ c
  have hconj : (K * CFC.rpow σ c * star K).PosDef := by
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff hK.isUnit]
    exact hσc
  rwa [hKstar] at hconj

theorem frankLieb_sigmaTerm_pos
    [Nonempty a] {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosDef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    0 < ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hinner : (K * CFC.rpow σ c * K).PosDef := by
    simpa [K] using frankLieb_sigmaTerm_inner_posDef
      (a := a) (H := H) (σ := σ) hH hσ c
  have hpow :
      (CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).PosDef :=
    cMatrix_rpow_posDef_of_posDef hinner (1 / c)
  exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpow)).1

/-- Gour's source-shaped low-`α` sigma term.

For `c = (1 - α) / α`, this is the second trace term in the
Young variational formula from `BookQRT.tex`, lines 12066--12070:
`Tr[(σ^(-c/2) H σ^(-c/2))^(-1/c)]`. -/
def frankLiebSourceSigmaTerm (σ H : CMatrix a) (c : ℝ) : ℝ :=
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  ((CFC.rpow (D * H * D) (-(1 / c))).trace).re

/-- Gour's source-shaped fixed-weight low-`α` objective before rewriting the
second term by the `LL*`/`L*L` spectral identity. -/
def frankLiebSourceFixedWeightObjective
    (ρ σ H : CMatrix a) (α c : ℝ) : ℝ :=
  (((ρ * H).trace).re ^ α) *
    (frankLiebSourceSigmaTerm σ H c ^ (1 - α))

/-- The inner matrix in Gour's source-shaped sigma term is positive
definite for positive-definite `σ` and `H`. -/
theorem frankLiebSourceSigmaTerm_inner_posDef
    {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef) (c : ℝ) :
    let D : CMatrix a := CFC.rpow σ (-(c / 2))
    (D * H * D).PosDef := by
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  have hD : D.PosDef := by
    simpa [D] using cMatrix_rpow_posDef_of_posDef hσ (-(c / 2))
  have hDstar : star D = D := hD.isHermitian.eq
  have hconj : (D * H * star D).PosDef := by
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff hD.isUnit]
    exact hH
  rwa [hDstar] at hconj

/-- Gour's source-shaped sigma term is positive on positive-definite inputs. -/
theorem frankLiebSourceSigmaTerm_pos
    [Nonempty a] {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef) (c : ℝ) :
    0 < frankLiebSourceSigmaTerm σ H c := by
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  have hinner : (D * H * D).PosDef := by
    simpa [D] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hpow : (CFC.rpow (D * H * D) (-(1 / c))).PosDef :=
    cMatrix_rpow_posDef_of_posDef hinner (-(1 / c))
  exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpow)).1

/-- The source-shaped weight cancels the two reference powers in the
sandwiched low-`α` inner matrix under the trace.

This is the algebraic part of Gour's Young lower bound before applying
reverse Holder: the test weight `σ^(-c/2) H σ^(-c/2)` pairs with
`σ^(c/2) ρ σ^(c/2)` as `Tr[ρH]`. -/
theorem sandwichedRenyiQInner_mul_sourceWeight_trace_re_eq
    {ρ σ H : CMatrix a} (hσ : σ.PosDef) {α c : ℝ}
    (hc : c = (1 - α) / α) :
    let D : CMatrix a := CFC.rpow σ (-(c / 2))
    (((sandwichedRenyiQInner ρ σ α) * (D * H * D)).trace).re =
      ((ρ * H).trace).re := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  let D : CMatrix a := CFC.rpow σ (-s)
  have hc_half : c / 2 = s := by
    rw [hc]
    ring
  have hD_def : CFC.rpow σ (-(c / 2)) = D := by
    simp [D, s, hc_half]
  have hCD : C * D = 1 := by
    simpa [C, D] using
      (CFC.rpow_mul_rpow_neg (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDC : D * C = 1 := by
    simpa [C, D] using
      (CFC.rpow_neg_mul_rpow (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  dsimp only
  rw [hD_def]
  change ((((C * ρ * C) * (D * H * D)).trace).re = ((ρ * H).trace).re)
  calc
    (((C * ρ * C) * (D * H * D)).trace).re =
        (((D * H * D) * (C * ρ * C)).trace).re := by
          exact congrArg Complex.re (Matrix.trace_mul_comm (C * ρ * C) (D * H * D))
    _ = (((D * H * ρ) * C).trace).re := by
          have hmat :
              (D * H * D) * (C * ρ * C) = (D * H * ρ) * C := by
            calc
            (D * H * D) * (C * ρ * C) =
                (D * H) * (D * (C * (ρ * C))) := by
                  simp [Matrix.mul_assoc]
            _ = (D * H) * ((D * C) * (ρ * C)) := by
                  rw [← Matrix.mul_assoc D C (ρ * C)]
            _ = (D * H) * (ρ * C) := by
                  rw [hDC, Matrix.one_mul]
            _ = (D * H * ρ) * C := by
                  simp [Matrix.mul_assoc]
          exact congrArg (fun X : CMatrix a => X.trace.re) hmat
    _ = ((C * (D * H * ρ)).trace).re := by
          exact congrArg Complex.re (Matrix.trace_mul_comm (D * H * ρ) C)
    _ = ((H * ρ).trace).re := by
          have hmat : C * (D * H * ρ) = H * ρ := by
            calc
            C * (D * H * ρ) = C * (D * (H * ρ)) := by
              simp [Matrix.mul_assoc]
            _ = (C * D) * (H * ρ) := by
              rw [Matrix.mul_assoc C D (H * ρ)]
            _ = H * ρ := by
              rw [hCD, Matrix.one_mul]
          exact congrArg (fun X : CMatrix a => X.trace.re) hmat
    _ = ((ρ * H).trace).re := by
          exact congrArg Complex.re (Matrix.trace_mul_comm H ρ)

omit [Fintype a] [DecidableEq a] in
private theorem lowAlpha_rpow_bound_to_fixedWeight
    {Q x y α c : ℝ} (hQ : 0 ≤ Q) (hx : 0 ≤ x) (hy : 0 < y)
    (hα_pos : 0 < α) (hc : c = (1 - α) / α)
    (hbound : Q ^ (1 / α) ≤ x * y ^ c) :
    Q ≤ x ^ α * y ^ (1 - α) := by
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hQ_pow : (Q ^ (1 / α)) ^ α = Q := by
    simpa [one_div] using Real.rpow_inv_rpow hQ hα_ne
  have hleft_nonneg : 0 ≤ Q ^ (1 / α) :=
    Real.rpow_nonneg hQ (1 / α)
  have hraise :
      (Q ^ (1 / α)) ^ α ≤ (x * y ^ c) ^ α :=
    Real.rpow_le_rpow hleft_nonneg hbound hα_pos.le
  have hyc_nonneg : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
  have hmul_pow :
      (x * y ^ c) ^ α = x ^ α * (y ^ c) ^ α := by
    rw [Real.mul_rpow hx hyc_nonneg]
  have hy_pow :
      (y ^ c) ^ α = y ^ (1 - α) := by
    calc
      (y ^ c) ^ α = y ^ (c * α) := by
        rw [← Real.rpow_mul hy.le c α]
      _ = y ^ (1 - α) := by
        rw [hc]
        field_simp [hα_ne]
  calc
    Q = (Q ^ (1 / α)) ^ α := hQ_pow.symm
    _ ≤ (x * y ^ c) ^ α := hraise
    _ = x ^ α * y ^ (1 - α) := by
      rw [hmul_pow, hy_pow]

/-- The normalized Gour source witness has the expected reverse-Holder
power.

This is the matrix-power core of the low-`α` Young lower bound.  For
`c = (1 - α) / α` and
`W = σ^(-c/2) H σ^(-c/2)`, the normalized witness
`N = Tr[W^(-1/c)]⁻¹ W^(-1/c)` satisfies
`N^(1 - 1/α) = Tr[W^(-1/c)]^c W`. -/
theorem frankLiebSourceWitness_rpow_eq
    [Nonempty a] {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef)
    {α c : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hc : c = (1 - α) / α) :
    let D : CMatrix a := CFC.rpow σ (-(c / 2))
    let W : CMatrix a := D * H * D
    let y : ℝ := frankLiebSourceSigmaTerm σ H c
    let Y : CMatrix a := CFC.rpow W (-(1 / c))
    CFC.rpow ((y⁻¹ : ℝ) • Y : CMatrix a) (1 - 1 / α) =
      (y ^ c : ℝ) • W := by
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  let W : CMatrix a := D * H * D
  let y : ℝ := frankLiebSourceSigmaTerm σ H c
  let Y : CMatrix a := CFC.rpow W (-(1 / c))
  have hα_pos : 0 < α := by linarith
  have hc_pos : 0 < c := by
    rw [hc]
    exact sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hy_pos : 0 < y := by
    simpa [y] using frankLiebSourceSigmaTerm_pos
      (a := a) (σ := σ) (H := H) hσ hH c
  have hW : W.PosDef := by
    simpa [W, D] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hY : Y.PosSemidef := by
    simpa [Y] using cMatrix_rpow_posSemidef (A := W) (s := -(1 / c)) hW.posSemidef
  have hscale_nonneg : 0 ≤ y⁻¹ := inv_nonneg.mpr hy_pos.le
  have hexp : 1 - 1 / α = -c := by
    rw [hc]
    field_simp [ne_of_gt hα_pos]
    ring
  have hYpow : CFC.rpow Y (1 - 1 / α) = W := by
    have hr_ne : (-(1 / c) : ℝ) ≠ 0 := by
      exact neg_ne_zero.mpr (one_div_ne_zero hc_ne)
    have hrt : (-(1 / c) : ℝ) * (1 - 1 / α) = (1 : ℝ) := by
      rw [hexp]
      field_simp [hc_ne]
    calc
      CFC.rpow Y (1 - 1 / α) =
          CFC.rpow W (1 : ℝ) := by
            simpa [Y] using
              cMatrix_rpow_rpow_of_posDef (A := W) hW hr_ne hrt
      _ = W := by
            exact CFC.rpow_one W
              (ha := Matrix.nonneg_iff_posSemidef.mpr hW.posSemidef)
  have hscale :
      y⁻¹ ^ (1 - 1 / α) = y ^ c := by
    rw [hexp]
    rw [Real.inv_rpow hy_pos.le]
    rw [Real.rpow_neg hy_pos.le]
    simp
  calc
    CFC.rpow ((y⁻¹ : ℝ) • Y : CMatrix a) (1 - 1 / α) =
        (y⁻¹ ^ (1 - 1 / α) : ℝ) • CFC.rpow Y (1 - 1 / α) := by
          exact cMatrix_rpow_real_smul_posSemidef_schatten hY hscale_nonneg
    _ = (y ^ c : ℝ) • W := by
          rw [hscale, hYpow]

/-- Gour source-shaped reverse-Holder/Young lower bound for positive
definite inputs.

This proves the noncommutative analogue of the scalar Young lower bound in
`BookQRT.tex`, lines 12066--12070, but still in the source sigma-term form
`Tr[(σ^(-c/2) H σ^(-c/2))^(-1/c)]`.  The remaining source-alignment step is
the `LL*`/`L*L` spectral identity rewriting this sigma term to the existing
Frank--Lieb/Epstein term. -/
theorem sandwichedRenyiQ_le_frankLiebSourceFixedWeightObjective_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      frankLiebSourceFixedWeightObjective ρ σ H α ((1 - α) / α) := by
  let c : ℝ := (1 - α) / α
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  let W : CMatrix a := D * H * D
  let y : ℝ := frankLiebSourceSigmaTerm σ H c
  let Y : CMatrix a := CFC.rpow W (-(1 / c))
  let N : CMatrix a := (y⁻¹ : ℝ) • Y
  let Q : ℝ := sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α
  let x : ℝ := ((ρ * H).trace).re
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  have hα_pos : 0 < α := by linarith
  have hα_half_le : 1 / 2 ≤ α := le_of_lt hα_half
  have hQ_nonneg : 0 ≤ Q := by
    have hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiQInner_posSemidef hρ.posSemidef hσ.posSemidef α
    have hpow_nonneg : 0 ≤ psdTracePower M hM α :=
      psdTracePower_nonneg M hM α
    simpa [Q, M, sandwichedRenyiQ_eq_psdTracePower_QInner] using hpow_nonneg
  have hx_nonneg : 0 ≤ x := by
    exact le_of_lt (by
      simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH)
  have hW : W.PosDef := by
    simpa [W, D] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hy_pos : 0 < y := by
    simpa [y] using frankLiebSourceSigmaTerm_pos
      (a := a) (σ := σ) (H := H) hσ hH c
  have hY : Y.PosDef := by
    simpa [Y] using cMatrix_rpow_posDef_of_posDef hW (-(1 / c))
  have hNdef : N.PosDef := by
    simpa [N] using Matrix.PosDef.smul hY (inv_pos.mpr hy_pos)
  have hN : N.PosSemidef := hNdef.posSemidef
  have hNtr : N.trace.re = 1 := by
    have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    have hYtr : Y.trace.re = y := by
      simp [Y, y, frankLiebSourceSigmaTerm, W, D]
    calc
      N.trace.re = (((y⁻¹ : ℝ) • Y : CMatrix a).trace).re := by
        rfl
      _ = y⁻¹ * Y.trace.re := by
        simp [Matrix.trace_smul, Complex.mul_re]
      _ = y⁻¹ * y := by rw [hYtr]
      _ = 1 := inv_mul_cancel₀ hy_ne
  have hSupport : Matrix.Supports M N :=
    Matrix.Supports.of_right_posDef M N hNdef
  have hvar :
      Q ^ (1 / α) ≤ ((M * CFC.rpow N (1 - 1 / α)).trace).re := by
    simpa [Q, M] using
      sandwichedRenyiQ_reverseHolder_norm_le_trace
        (ρ := ρ) (σ := σ) (N := N)
        hρ.posSemidef hσ.posSemidef hN hNtr hα_half_le hα_lt_one hSupport
  have hNrpow :
      CFC.rpow N (1 - 1 / α) = (y ^ c : ℝ) • W := by
    simpa [N, Y, W, D, y, c] using
      frankLiebSourceWitness_rpow_eq
        (a := a) (σ := σ) (H := H) hσ hH hα_half hα_lt_one (rfl : c = (1 - α) / α)
  have htraceW : ((M * W).trace).re = x := by
    simpa [M, W, D, x, c] using
      sandwichedRenyiQInner_mul_sourceWeight_trace_re_eq
        (a := a) (ρ := ρ) (σ := σ) (H := H) hσ
        (α := α) (c := c) (rfl : c = (1 - α) / α)
  have htrace :
      ((M * CFC.rpow N (1 - 1 / α)).trace).re = x * y ^ c := by
    rw [hNrpow]
    calc
      ((M * ((y ^ c : ℝ) • W : CMatrix a)).trace).re =
          y ^ c * ((M * W).trace).re := by
            simp [Matrix.trace_smul, Complex.mul_re]
      _ = x * y ^ c := by
            rw [htraceW]
            ring
  have hbound : Q ^ (1 / α) ≤ x * y ^ c := by
    rw [htrace] at hvar
    exact hvar
  have hscalar :
      Q ≤ x ^ α * y ^ (1 - α) :=
    lowAlpha_rpow_bound_to_fixedWeight
      (Q := Q) (x := x) (y := y) (α := α) (c := c)
      hQ_nonneg hx_nonneg hy_pos hα_pos (rfl : c = (1 - α) / α) hbound
  simpa [frankLiebSourceFixedWeightObjective, Q, x, y, c] using hscalar

/-- Positive-definite matrices with the same characteristic polynomial have
the same real trace of every real power.

This packages the finite-dimensional spectral bookkeeping needed for Gour's
`LL*`/`L*L` step. -/
theorem psdTracePower_eq_of_posDef_charpoly_eq
    {A B : CMatrix a} (hA : A.PosDef) (hB : B.PosDef) (p : ℝ)
    (hchar : A.charpoly = B.charpoly) :
    psdTracePower A hA.posSemidef p =
      psdTracePower B hB.posSemidef p := by
  have heigs :
      hA.posSemidef.isHermitian.eigenvalues =
        hB.posSemidef.isHermitian.eigenvalues := by
    exact
      ((hA.posSemidef.isHermitian).eigenvalues_eq_eigenvalues_iff
        hB.posSemidef.isHermitian).mpr hchar
  rw [psdTracePower_eq_sum_eigenvalues_rpow,
    psdTracePower_eq_sum_eigenvalues_rpow]
  rw [heigs]

/-- Gour's source sigma term equals the Frank--Lieb/Epstein sigma term.

This is the finite-dimensional `LL*`/`L*L` spectral identity cited in
`BookQRT.tex`, line 12058.  It rewrites
`Tr[(σ^(-c/2) H σ^(-c/2))^(-1/c)]` as
`Tr[(H^(-1/2) σ^c H^(-1/2))^(1/c)]`. -/
theorem frankLiebSourceSigmaTerm_eq_frankLieb_sigmaTerm
    {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef) {c : ℝ} :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    frankLiebSourceSigmaTerm σ H c =
      ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let s : ℝ := c / 2
  let D : CMatrix a := CFC.rpow σ (-s)
  let S : CMatrix a := CFC.rpow σ s
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let L : CMatrix a := D * H * D
  let R : CMatrix a := K * CFC.rpow σ c * K
  let X : CMatrix a := S * K
  have hL : L.PosDef := by
    simpa [L, D, s] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hR : R.PosDef := by
    simpa [R, K] using frankLieb_sigmaTerm_inner_posDef
      (a := a) (H := H) (σ := σ) hH hσ c
  have hSstar : star S = S := by
    exact (cMatrix_rpow_posDef_of_posDef hσ s).isHermitian.eq
  have hKstar : star K = K := by
    exact (cMatrix_rpow_posDef_of_posDef hH (-(1 / 2 : ℝ))).isHermitian.eq
  have hDS : D * S = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_neg_mul_rpow (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hSD : S * D = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_mul_rpow_neg (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hK2 : K * K = H⁻¹ := by
    have hpow : K * K = CFC.rpow H (-1 : ℝ) := by
      calc
        K * K = CFC.rpow H (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) := by
          simpa [K] using
            (CFC.rpow_add (a := H) (x := -(1 / 2 : ℝ))
              (y := -(1 / 2 : ℝ)) hH.isUnit).symm
        _ = CFC.rpow H (-1 : ℝ) := by ring_nf
    have hinv : CFC.rpow H (-1 : ℝ) = H⁻¹ := by
      calc
        CFC.rpow H (-1 : ℝ) = CFC.rpow H⁻¹ (1 : ℝ) :=
          (cMatrix_rpow_nonsing_inv_eq_rpow_neg
            (a := a) (B := H) hH (1 : ℝ)).symm
        _ = H⁻¹ := by
          exact CFC.rpow_one H⁻¹
            (ha := Matrix.nonneg_iff_posSemidef.mpr hH.inv.posSemidef)
    rw [hpow, hinv]
  have hS2 : S * S = CFC.rpow σ c := by
    calc
      S * S = CFC.rpow σ (s + s) := by
        simpa [S] using
          (CFC.rpow_add (a := σ) (x := s) (y := s) hσ.isUnit).symm
      _ = CFC.rpow σ c := by
        congr 1
        simp [s]
  let V : CMatrix a := S * H⁻¹ * S
  have hLV : L * V = 1 := by
    calc
      L * V = (D * H * D) * (S * H⁻¹ * S) := rfl
      _ = (D * H) * ((D * S) * (H⁻¹ * S)) := by
        simp [Matrix.mul_assoc]
      _ = (D * H) * (H⁻¹ * S) := by
        rw [hDS, Matrix.one_mul]
      _ = D * (H * H⁻¹) * S := by
        simp [Matrix.mul_assoc]
      _ = D * (1 : CMatrix a) * S := by
        rw [Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)]
      _ = 1 := by
        simpa [Matrix.mul_assoc] using hDS
  have hLinv : L⁻¹ = V := by
    have hdet : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit
    calc
      L⁻¹ = L⁻¹ * 1 := by simp
      _ = L⁻¹ * (L * V) := by rw [hLV]
      _ = (L⁻¹ * L) * V := by simp [Matrix.mul_assoc]
      _ = V := by
        rw [Matrix.nonsing_inv_mul L hdet, Matrix.one_mul]
  have hXstar : star X = K * S := by
    simp [X, hSstar, hKstar]
  have hX_left : X * star X = L⁻¹ := by
    calc
      X * star X = (S * K) * (K * S) := by
        rw [hXstar]
      _ = S * (K * K) * S := by
        simp [Matrix.mul_assoc]
      _ = S * H⁻¹ * S := by
        rw [hK2]
      _ = L⁻¹ := hLinv.symm
  have hX_right : star X * X = R := by
    calc
      star X * X = (K * S) * (S * K) := by
        rw [hXstar]
      _ = K * (S * S) * K := by
        simp [Matrix.mul_assoc]
      _ = K * CFC.rpow σ c * K := by
        rw [hS2]
      _ = R := rfl
  have hchar : (L⁻¹).charpoly = R.charpoly := by
    calc
      (L⁻¹).charpoly = (X * star X).charpoly := by rw [hX_left]
      _ = (star X * X).charpoly := Matrix.charpoly_mul_comm X (star X)
      _ = R.charpoly := by rw [hX_right]
  have htrace :
      psdTracePower L⁻¹ hL.inv.posSemidef (1 / c) =
        psdTracePower R hR.posSemidef (1 / c) :=
    psdTracePower_eq_of_posDef_charpoly_eq hL.inv hR (1 / c) hchar
  calc
    frankLiebSourceSigmaTerm σ H c =
        psdTracePower L⁻¹ hL.inv.posSemidef (1 / c) := by
          change ((CFC.rpow L (-(1 / c))).trace).re =
            ((CFC.rpow L⁻¹ (1 / c)).trace).re
          rw [← cMatrix_rpow_nonsing_inv_eq_rpow_neg
            (a := a) (B := L) hL (1 / c)]
    _ = psdTracePower R hR.posSemidef (1 / c) := htrace
    _ = ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
          rfl

/-- The fixed-weight Frank--Lieb trace term is the Epstein trace primitive
with `K = H^(-1/2)`.

This is the source-notation alignment from
`Tr[(H^(-1/2) σ^c H^(-1/2))^(1/c)]` to the reusable Epstein expression
`Tr[(K† σ^c K)^(1/c)]`. -/
theorem frankLieb_sigmaTerm_eq_epsteinTraceTerm
    {H σ : CMatrix a} (hH : H.PosDef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re =
      epsteinTraceTerm K σ c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hKstar : star K = K := by
    simpa [K] using (frankLieb_weight_isHermitian (a := a) hH).eq
  have hKstar' : star (CFC.rpow H (-(1 / 2 : ℝ))) =
      CFC.rpow H (-(1 / 2 : ℝ)) := by
    simpa [K] using hKstar
  dsimp only [epsteinTraceTerm]
  rw [hKstar']

/-- Unrestricted fixed-weight Frank--Lieb sigma-term concavity.

For a fixed positive-definite weight `H` and `0 < c < 1`, the map
`σ ↦ Tr[(H^{-1/2} σ^c H^{-1/2})^{1/c}]` is concave on PSD matrices. -/
theorem frankLieb_sigmaTerm_concave
    {H σ₁ σ₂ : CMatrix a} (hH : H.PosDef)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re ≤
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hEpstein :
      t * epsteinTraceTerm K σ₁ c + (1 - t) * epsteinTraceTerm K σ₂ c ≤
        epsteinTraceTerm K σt c := by
    simpa [σt] using
      epsteinTraceTerm_concave (a := a) K hσ₁ hσ₂ hc_pos hc_lt_one ht0 ht1
  have h₁ :
      ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σ₁ c := by
    simpa [K] using
      frankLieb_sigmaTerm_eq_epsteinTraceTerm
        (a := a) (H := H) (σ := σ₁) hH c
  have h₂ :
      ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σ₂ c := by
    simpa [K] using
      frankLieb_sigmaTerm_eq_epsteinTraceTerm
        (a := a) (H := H) (σ := σ₂) hH c
  have ht :
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σt c := by
    simpa [K] using
      frankLieb_sigmaTerm_eq_epsteinTraceTerm
        (a := a) (H := H) (σ := σt) hH c
  dsimp only
  rw [h₁, h₂, ht]
  exact hEpstein

/-- Fixed-weight Frank--Lieb variational objective.

For a fixed positive-definite weight `H`, this is the source-shaped term
`(Tr ρH)^α * Tr[(H^{-1/2} σ^c H^{-1/2})^{1/c}]^{1-α}` appearing in the
low-`α` reverse-Holder bridge after setting `c = (1 - α) / α`. -/
def frankLiebFixedWeightObjective
    (ρ σ H : CMatrix a) (α c : ℝ) : ℝ :=
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  (((ρ * H).trace).re ^ α) *
    (((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re ^ (1 - α))

/-- Gour/Frank--Lieb fixed-weight lower bound in the local
Frank--Lieb/Epstein notation.

This is the source-shaped Young lower bound after applying the `LL*`/`L*L`
spectral rewrite, so it is directly compatible with
`sandwichedRenyiQFixedWeightValueSet`. -/
theorem sandwichedRenyiQ_le_frankLiebFixedWeightObjective_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) := by
  let c : ℝ := (1 - α) / α
  have hsource :
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
        frankLiebSourceFixedWeightObjective ρ σ H α c := by
    simpa [c] using
      sandwichedRenyiQ_le_frankLiebSourceFixedWeightObjective_posDef
        (a := a) (ρ := ρ) (σ := σ) (H := H)
        hρ hσ hH hα_half hα_lt_one
  have hsigma :
      frankLiebSourceSigmaTerm σ H c =
        (let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
        ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re) := by
    simpa [c] using frankLiebSourceSigmaTerm_eq_frankLieb_sigmaTerm
      (a := a) (σ := σ) (H := H) hσ hH (c := c)
  have hobj :
      frankLiebSourceFixedWeightObjective ρ σ H α c =
        frankLiebFixedWeightObjective ρ σ H α c := by
    unfold frankLiebSourceFixedWeightObjective frankLiebFixedWeightObjective
    rw [hsigma]
  exact hsource.trans_eq hobj

/-- Source-shaped additive Frank--Lieb/Young variational objective.

This is the finite-dimensional low-`α` objective in Gour's presentation
(`BookQRT.tex`, lines 12066--12070) after writing
`c = (1 - α) / α` and the positive weight as `H`.

The existing `frankLiebFixedWeightObjective` is the weighted geometric mean of
the two nonnegative summands in this additive objective. -/
def frankLiebAdditiveObjective
    (ρ σ H : CMatrix a) (α c : ℝ) : ℝ :=
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  α * ((ρ * H).trace).re +
    (1 - α) *
      ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re

/-- The fixed-weight multiplicative objective is bounded by the source-shaped
additive Frank--Lieb/Young objective.

This is exactly the scalar weighted AM--GM/Young step in Gour's low-`α`
variational spine; the two matrix inputs are only used to establish
nonnegativity of the scalar trace terms. -/
theorem frankLiebFixedWeightObjective_le_additiveObjective
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    frankLiebFixedWeightObjective ρ σ H α c ≤
      frankLiebAdditiveObjective ρ σ H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  have hx : 0 ≤ x := by
    simpa [x] using cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy : 0 ≤ y := by
    simpa [y, K] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hweights : α + (1 - α) = (1 : ℝ) := by ring
  have hyoung : x ^ α * y ^ (1 - α) ≤ α * x + (1 - α) * y :=
    Real.geom_mean_le_arith_mean2_weighted hα0 h1α hx hy hweights
  simpa [frankLiebFixedWeightObjective, frankLiebAdditiveObjective, K, x, y]
    using hyoung

/-- Positive scalar rescaling of the Frank--Lieb weight in the additive
Gour/Young objective.

This is the unrestricted-weight bookkeeping needed before optimizing the
source additive objective over the scale of `H`. -/
theorem frankLiebAdditiveObjective_real_smul_weight
    {ρ σ H : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef)
    {lambda α c : ℝ} (hlambda_pos : 0 < lambda) (hc_pos : 0 < c) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
      α * (lambda * ((ρ * H).trace).re) +
        (1 - α) *
          (lambda ^ (-(1 / c)) *
            ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re) := by
  let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hleft_trace :
      (((ρ * (lambda • H : CMatrix a)).trace).re) =
        lambda * ((ρ * H).trace).re := by
    calc
      ((ρ * (lambda • H : CMatrix a)).trace).re =
          (((lambda : ℂ) • (ρ * H : CMatrix a)).trace).re := by
            simp
      _ = lambda * ((ρ * H).trace).re := by
            simp [Matrix.trace_smul, Complex.mul_re]
  have hsigma :
      ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
        lambda ^ (-(1 / c)) *
          ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
    simpa [Klam, K] using
      frankLieb_sigmaTerm_real_smul_weight
        (a := a) (H := H) (σ := σ) hH hσ hlambda_pos hc_pos
  dsimp only
  unfold frankLiebAdditiveObjective
  change
    α * (((ρ * (lambda • H : CMatrix a)).trace).re) +
        (1 - α) *
          ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
      α * (lambda * ((ρ * H).trace).re) +
        (1 - α) *
          (lambda ^ (-(1 / c)) *
            ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re)
  rw [hleft_trace, hsigma]

/-- Concavity of the source-shaped additive Gour/Frank--Lieb objective for a
fixed positive weight.

This is the direct formal counterpart of the fixed-`H` part of Gour's
low-`α` variational proof: the `ρ` contribution is affine and the `σ`
contribution is Epstein/Frank--Lieb concave. -/
theorem frankLiebAdditiveObjective_concave
    {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {α c t : ℝ} (hα1 : α ≤ 1)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * frankLiebAdditiveObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α c ≤
      frankLiebAdditiveObjective
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let x₁ : ℝ := ((ρ₁ * H).trace).re
  let x₂ : ℝ := ((ρ₂ * H).trace).re
  let xt : ℝ := ((ρt * H).trace).re
  let y₁ : ℝ := ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re
  let y₂ : ℝ := ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re
  let yt : ℝ := ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re
  have hxt : xt = t * x₁ + (1 - t) * x₂ := by
    have hmul :
        ρt * H = cMatrixConvexCombination t (ρ₁ * H) (ρ₂ * H) := by
      dsimp [ρt]
      rw [cMatrixConvexCombination_eq_real_smul]
      rw [cMatrixConvexCombination_eq_real_smul]
      simp [Matrix.add_mul]
    change ((ρt * H).trace).re = t * x₁ + (1 - t) * x₂
    rw [hmul]
    simpa [x₁, x₂] using cMatrixConvexCombination_trace_re t (ρ₁ * H) (ρ₂ * H)
  have hy_conc : t * y₁ + (1 - t) * y₂ ≤ yt := by
    simpa [y₁, y₂, yt, K, σt] using
      frankLieb_sigmaTerm_concave
        (a := a) (H := H) (σ₁ := σ₁) (σ₂ := σ₂)
        hH hσ₁ hσ₂ hc_pos hc_lt_one ht0 ht1
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hscaled_y :
      (1 - α) * (t * y₁ + (1 - t) * y₂) ≤ (1 - α) * yt :=
    mul_le_mul_of_nonneg_left hy_conc h1α
  calc
    t * frankLiebAdditiveObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α c =
        α * (t * x₁ + (1 - t) * x₂) +
          (1 - α) * (t * y₁ + (1 - t) * y₂) := by
          simp [frankLiebAdditiveObjective, x₁, x₂, y₁, y₂, K]
          ring
    _ ≤ α * (t * x₁ + (1 - t) * x₂) + (1 - α) * yt :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hscaled_y (α * (t * x₁ + (1 - t) * x₂))
    _ = frankLiebAdditiveObjective ρt σt H α c := by
          simp [frankLiebAdditiveObjective, xt, yt, K, hxt]

private theorem frankLieb_additive_optimalScale_eq_weightedGeom
    {x y α : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    let lambda : ℝ := (y / x) ^ (1 - α)
    α * (lambda * x) +
        (1 - α) * (lambda ^ (-(α / (1 - α))) * y) =
      x ^ α * y ^ (1 - α) := by
  let lambda : ℝ := (y / x) ^ (1 - α)
  have hratio_pos : 0 < y / x := div_pos hy hx
  have hden_pos : 0 < 1 - α := sub_pos.mpr hα_lt_one
  have hlambda_x : lambda * x = x ^ α * y ^ (1 - α) := by
    calc
      lambda * x = (y / x) ^ (1 - α) * x := rfl
      _ = (y ^ (1 - α) / x ^ (1 - α)) * x := by
            rw [Real.div_rpow hy.le hx.le]
      _ = y ^ (1 - α) * (x / x ^ (1 - α)) := by
            field_simp [Real.rpow_pos_of_pos hx (1 - α)]
      _ = y ^ (1 - α) * x ^ α := by
            have hxpow : x / x ^ (1 - α) = x ^ α := by
              calc
                x / x ^ (1 - α) = x ^ (1 : ℝ) / x ^ (1 - α) := by
                  rw [Real.rpow_one]
                _ = x ^ (1 - (1 - α)) := by
                  rw [← Real.rpow_sub hx 1 (1 - α)]
                _ = x ^ α := by ring_nf
            rw [hxpow]
      _ = x ^ α * y ^ (1 - α) := by ring
  have hlambda_y :
      lambda ^ (-(α / (1 - α))) * y =
        x ^ α * y ^ (1 - α) := by
    have hexp : (1 - α) * (-(α / (1 - α))) = -α := by
      field_simp [ne_of_gt hden_pos]
    calc
      lambda ^ (-(α / (1 - α))) * y =
          ((y / x) ^ (1 - α)) ^ (-(α / (1 - α))) * y := rfl
      _ = (y / x) ^ ((1 - α) * (-(α / (1 - α)))) * y := by
            rw [Real.rpow_mul hratio_pos.le]
      _ = (y / x) ^ (-α) * y := by rw [hexp]
      _ = ((y / x) ^ α)⁻¹ * y := by
            rw [Real.rpow_neg hratio_pos.le]
      _ = (y ^ α / x ^ α)⁻¹ * y := by
            rw [Real.div_rpow hy.le hx.le]
      _ = (x ^ α / y ^ α) * y := by
            field_simp [Real.rpow_pos_of_pos hx α, Real.rpow_pos_of_pos hy α]
      _ = x ^ α * (y / y ^ α) := by
            field_simp [Real.rpow_pos_of_pos hy α]
      _ = x ^ α * y ^ (1 - α) := by
            have hypow : y / y ^ α = y ^ (1 - α) := by
              calc
                y / y ^ α = y ^ (1 : ℝ) / y ^ α := by
                  rw [Real.rpow_one]
                _ = y ^ (1 - α) := by
                  rw [← Real.rpow_sub hy 1 α]
            rw [hypow]
  dsimp only
  rw [hlambda_x, hlambda_y]
  ring

/-- At the source Young-optimizer scale, the additive Gour/Frank--Lieb
objective agrees with the fixed-weight multiplicative objective.

This is the source-faithful bridge from Gour's additive variational formula to
the fixed-weight objective used by the existing concavity/sInf handoff.  The
statement is intentionally full-rank on both matrix inputs; singular PSD
closure is a later step. -/
theorem frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    let c : ℝ := (1 - α) / α
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let x : ℝ := ((ρ * H).trace).re
    let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
    let lambda : ℝ := (y / x) ^ (1 - α)
    frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
      frankLiebFixedWeightObjective ρ σ H α c := by
  let c : ℝ := (1 - α) / α
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  let lambda : ℝ := (y / x) ^ (1 - α)
  have hα_pos : 0 < α := by linarith
  have hc_pos : 0 < c := by
    simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hx : 0 < x := by
    simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH
  have hy : 0 < y := by
    simpa [y, K, c] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ) hH hσ c
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    exact Real.rpow_pos_of_pos (div_pos hy hx) (1 - α)
  have hc_inv : 1 / c = α / (1 - α) := by
    dsimp [c]
    field_simp [ne_of_gt hα_pos, ne_of_gt (sub_pos.mpr hα_lt_one)]
  have hscale :
      frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
        α * (lambda * x) +
          (1 - α) * (lambda ^ (-(1 / c)) * y) := by
    simpa [K, x, y, c, lambda] using
      frankLiebAdditiveObjective_real_smul_weight
        (a := a) (ρ := ρ) (σ := σ) (H := H)
        hH hσ.posSemidef hlambda_pos hc_pos
  have hopt :
      α * (lambda * x) +
          (1 - α) * (lambda ^ (-(α / (1 - α))) * y) =
        x ^ α * y ^ (1 - α) := by
    simpa [lambda] using
      frankLieb_additive_optimalScale_eq_weightedGeom
        (x := x) (y := y) (α := α) hx hy hα_pos hα_lt_one
  calc
    frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
        α * (lambda * x) + (1 - α) * (lambda ^ (-(1 / c)) * y) := hscale
    _ = α * (lambda * x) + (1 - α) * (lambda ^ (-(α / (1 - α))) * y) := by
          rw [hc_inv]
    _ = x ^ α * y ^ (1 - α) := hopt
    _ = frankLiebFixedWeightObjective ρ σ H α c := by
          simp [frankLiebFixedWeightObjective, K, x, y, c]

/-- The fixed-weight Frank--Lieb objective vanishes when the left input is
zero. -/
theorem frankLiebFixedWeightObjective_zero_left
    (σ H : CMatrix a) {α c : ℝ} (hα_pos : 0 < α) :
    frankLiebFixedWeightObjective (0 : CMatrix a) σ H α c = 0 := by
  unfold frankLiebFixedWeightObjective
  simp [Real.zero_rpow (ne_of_gt hα_pos)]

/-- The fixed-weight Frank--Lieb objective is invariant under positive real
rescaling of the weight at the low-alpha source exponent
`c = (1 - alpha) / alpha`.

This is the homogeneity needed to move between normalized reverse-Holder
side-states and unrestricted positive Frank--Lieb weights. -/
theorem frankLiebFixedWeightObjective_real_smul_weight_strictLowAlpha
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) {lambda α : ℝ}
    (hlambda_pos : 0 < lambda)
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    frankLiebFixedWeightObjective ρ σ (lambda • H : CMatrix a) α ((1 - α) / α) =
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) := by
  let c : ℝ := (1 - α) / α
  let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda_pos
  have hx_nonneg : 0 ≤ x := by
    simpa [x] using cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy_nonneg : 0 ≤ y := by
    simpa [y, K, c] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  have hleft_trace :
      (((ρ * (lambda • H : CMatrix a)).trace).re) = lambda * x := by
    calc
      ((ρ * (lambda • H : CMatrix a)).trace).re =
          (((lambda : ℂ) • (ρ * H : CMatrix a)).trace).re := by
            simp
      _ = lambda * x := by
            simp [x, Matrix.trace_smul, Complex.mul_re]
  have hsigma :
      ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
        lambda ^ (-(1 / c)) * y := by
    simpa [Klam, K, c, y] using
      frankLieb_sigmaTerm_real_smul_weight
        (a := a) (H := H) (σ := σ) hH hσ hlambda_pos
        (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
  have hpow_x :
      (lambda * x) ^ α = lambda ^ α * x ^ α :=
    Real.mul_rpow hlambda_nonneg hx_nonneg
  have hpow_y :
      (lambda ^ (-(1 / c)) * y) ^ (1 - α) =
        (lambda ^ (-(1 / c))) ^ (1 - α) * y ^ (1 - α) :=
    Real.mul_rpow (Real.rpow_nonneg hlambda_nonneg (-(1 / c))) hy_nonneg
  have hscale :
      lambda ^ α * (lambda ^ (-(1 / c))) ^ (1 - α) = 1 := by
    have hc_pos : 0 < c := by
      simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
    have hα_pos : 0 < α := by linarith
    have hexp :
        α + (-(1 / c)) * (1 - α) = 0 := by
      dsimp [c]
      have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
      field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
      ring_nf
    calc
      lambda ^ α * (lambda ^ (-(1 / c))) ^ (1 - α) =
          lambda ^ α * lambda ^ ((-(1 / c)) * (1 - α)) := by
            rw [← Real.rpow_mul hlambda_nonneg]
      _ = lambda ^ (α + (-(1 / c)) * (1 - α)) := by
            rw [← Real.rpow_add hlambda_pos]
      _ = 1 := by
            rw [hexp, Real.rpow_zero]
  unfold frankLiebFixedWeightObjective
  change
    (((ρ * (lambda • H : CMatrix a)).trace).re ^ α) *
        (((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re ^
          (1 - α)) =
      x ^ α * y ^ (1 - α)
  rw [hleft_trace, hsigma, hpow_x, hpow_y]
  calc
    lambda ^ α * x ^ α *
        ((lambda ^ (-(1 / c))) ^ (1 - α) * y ^ (1 - α)) =
        (lambda ^ α * (lambda ^ (-(1 / c))) ^ (1 - α)) *
          (x ^ α * y ^ (1 - α)) := by ring
    _ = x ^ α * y ^ (1 - α) := by rw [hscale, one_mul]

/-- Identity-`H` special case of the Frank--Lieb `sigma` term concavity.

With `H = I`, the source term reduces by the PSD power-of-power law to
`Tr(σ)`, so the claimed concavity is trace linearity of the matrix convex
combination. -/
theorem frankLieb_sigmaTerm_concave_identity
    {σ₁ σ₂ : CMatrix a} (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {c t : ℝ} (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (CFC.rpow σ₁ c) (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow (CFC.rpow σ₂ c) (1 / c)).trace).re ≤
      ((CFC.rpow (CFC.rpow σt c) (1 / c)).trace).re := by
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hσt : σt.PosSemidef := by
    simpa [σt] using cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1
  have hpow₁ : CFC.rpow (CFC.rpow σ₁ c) (1 / c) = σ₁ :=
    cMatrix_rpow_rpow_inv_of_pos hσ₁ hc_pos
  have hpow₂ : CFC.rpow (CFC.rpow σ₂ c) (1 / c) = σ₂ :=
    cMatrix_rpow_rpow_inv_of_pos hσ₂ hc_pos
  have hpowt : CFC.rpow (CFC.rpow σt c) (1 / c) = σt :=
    cMatrix_rpow_rpow_inv_of_pos hσt hc_pos
  have htrace :
      σt.trace.re = t * σ₁.trace.re + (1 - t) * σ₂.trace.re := by
    simpa [σt] using cMatrixConvexCombination_trace_re t σ₁ σ₂
  dsimp only
  rw [hpow₁, hpow₂, hpowt, htrace]

/-- Positive-scalar weighted special case of the Frank--Lieb `sigma` term
concavity.

This is the source `H = λ⁻¹ I` sanity case: the weighted source term
`Tr[(λ σ^c)^(1/c)]` reduces to the fixed scalar `λ^(1/c)` times `Tr σ`,
so the binary concavity claim is again trace linearity.  It is still a
non-circular Frank--Lieb-route check because it verifies the weighted exponent
placement used by the general `H` theorem without assuming joint concavity. -/
theorem frankLieb_sigmaTerm_concave_real_smul
    {σ₁ σ₂ : CMatrix a} (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {lambda c t : ℝ} (hlambda : 0 ≤ lambda)
    (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (lambda • CFC.rpow σ₁ c : CMatrix a) (1 / c)).trace).re +
        (1 - t) *
          ((CFC.rpow (lambda • CFC.rpow σ₂ c : CMatrix a) (1 / c)).trace).re ≤
      ((CFC.rpow (lambda • CFC.rpow σt c : CMatrix a) (1 / c)).trace).re := by
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let w : ℝ := lambda ^ (1 / c)
  have hσt : σt.PosSemidef := by
    simpa [σt] using cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1
  have hpow₁ :
      CFC.rpow (lambda • CFC.rpow σ₁ c : CMatrix a) (1 / c) =
        w • σ₁ := by
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (cMatrix_rpow_posSemidef (A := σ₁) (s := c) hσ₁) hlambda]
    rw [cMatrix_rpow_rpow_inv_of_pos hσ₁ hc_pos]
  have hpow₂ :
      CFC.rpow (lambda • CFC.rpow σ₂ c : CMatrix a) (1 / c) =
        w • σ₂ := by
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (cMatrix_rpow_posSemidef (A := σ₂) (s := c) hσ₂) hlambda]
    rw [cMatrix_rpow_rpow_inv_of_pos hσ₂ hc_pos]
  have hpowt :
      CFC.rpow (lambda • CFC.rpow σt c : CMatrix a) (1 / c) =
        w • σt := by
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (cMatrix_rpow_posSemidef (A := σt) (s := c) hσt) hlambda]
    rw [cMatrix_rpow_rpow_inv_of_pos hσt hc_pos]
  have htrace :
      σt.trace.re = t * σ₁.trace.re + (1 - t) * σ₂.trace.re := by
    simpa [σt] using cMatrixConvexCombination_trace_re t σ₁ σ₂
  have htrace₁ :
      ((w • σ₁ : CMatrix a).trace).re = w * σ₁.trace.re := by
    simp [Matrix.trace_smul, Complex.mul_re]
  have htrace₂ :
      ((w • σ₂ : CMatrix a).trace).re = w * σ₂.trace.re := by
    simp [Matrix.trace_smul, Complex.mul_re]
  have htracet :
      ((w • σt : CMatrix a).trace).re = w * σt.trace.re := by
    simp [Matrix.trace_smul, Complex.mul_re]
  dsimp only
  rw [hpow₁, hpow₂, hpowt, htrace₁, htrace₂, htracet, htrace]
  ring_nf
  exact le_rfl

/-- Diagonal fixed-weight special case of the Frank--Lieb `sigma` term
concavity.

This is the common-eigenbasis sanity case for the source term
`Tr[(H^{-1/2} σ^c H^{-1/2})^(1/c)]`: a fixed nonnegative diagonal weight
`w` plays the role of the diagonal entries of `H^{-1}`, and the theorem
reduces the matrix statement to the scalar identity
`(wᵢ dᵢ^c)^(1/c) = wᵢ^(1/c) dᵢ`.  It is still not the full Frank--Lieb
theorem, but it verifies the nonconstant weighted exponent placement used by
that theorem. -/
theorem frankLieb_sigmaTerm_concave_diagonalWeight
    (w d₁ d₂ : a → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hd₁ : ∀ i, 0 ≤ d₁ i) (hd₂ : ∀ i, 0 ≤ d₂ i)
    {c t : ℝ} (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₁ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₂ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c)).trace).re ≤
      ((CFC.rpow
        (Matrix.diagonal
          (fun i => ((w i * (t * d₁ i + (1 - t) * d₂ i) ^ c : ℝ) : ℂ)) :
          CMatrix a)
        (1 / c)).trace).re := by
  let dt : a → ℝ := fun i => t * d₁ i + (1 - t) * d₂ i
  have hdt : ∀ i, 0 ≤ dt i := by
    intro i
    exact add_nonneg (mul_nonneg ht0 (hd₁ i))
      (mul_nonneg (sub_nonneg.mpr ht1) (hd₂ i))
  have hD₁ : ∀ i, 0 ≤ w i * d₁ i ^ c := fun i =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hd₁ i) c)
  have hD₂ : ∀ i, 0 ≤ w i * d₂ i ^ c := fun i =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hd₂ i) c)
  have hDt : ∀ i, 0 ≤ w i * dt i ^ c := fun i =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hdt i) c)
  have hpow₁ :
      CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₁ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * d₁ i : ℝ) : ℂ)) := by
    rw [cMatrix_rpow_diagonal_ofReal (fun i => w i * d₁ i ^ c) hD₁ (1 / c)]
    ext i j
    by_cases hij : i = j
    · subst j
      have hmul :
          (w i * d₁ i ^ c) ^ (1 / c) = w i ^ (1 / c) * d₁ i := by
        rw [Real.mul_rpow (hw i) (Real.rpow_nonneg (hd₁ i) c)]
        rw [← Real.rpow_mul (hd₁ i)]
        have hc_mul : c * (1 / c) = (1 : ℝ) := by
          field_simp [hc_pos.ne']
        rw [hc_mul, Real.rpow_one]
      simp only [Matrix.diagonal_apply, ↓reduceIte]
      exact congrArg (fun x : ℝ => (x : ℂ)) (by simpa [one_div] using hmul)
    · simp [Matrix.diagonal, hij]
  have hpow₂ :
      CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₂ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * d₂ i : ℝ) : ℂ)) := by
    rw [cMatrix_rpow_diagonal_ofReal (fun i => w i * d₂ i ^ c) hD₂ (1 / c)]
    ext i j
    by_cases hij : i = j
    · subst j
      have hmul :
          (w i * d₂ i ^ c) ^ (1 / c) = w i ^ (1 / c) * d₂ i := by
        rw [Real.mul_rpow (hw i) (Real.rpow_nonneg (hd₂ i) c)]
        rw [← Real.rpow_mul (hd₂ i)]
        have hc_mul : c * (1 / c) = (1 : ℝ) := by
          field_simp [hc_pos.ne']
        rw [hc_mul, Real.rpow_one]
      simp only [Matrix.diagonal_apply, ↓reduceIte]
      exact congrArg (fun x : ℝ => (x : ℂ)) (by simpa [one_div] using hmul)
    · simp [Matrix.diagonal, hij]
  have hpowt :
      CFC.rpow
          (Matrix.diagonal (fun i => ((w i * dt i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * dt i : ℝ) : ℂ)) := by
    rw [cMatrix_rpow_diagonal_ofReal (fun i => w i * dt i ^ c) hDt (1 / c)]
    ext i j
    by_cases hij : i = j
    · subst j
      have hmul :
          (w i * dt i ^ c) ^ (1 / c) = w i ^ (1 / c) * dt i := by
        rw [Real.mul_rpow (hw i) (Real.rpow_nonneg (hdt i) c)]
        rw [← Real.rpow_mul (hdt i)]
        have hc_mul : c * (1 / c) = (1 : ℝ) := by
          field_simp [hc_pos.ne']
        rw [hc_mul, Real.rpow_one]
      simp only [Matrix.diagonal_apply, ↓reduceIte]
      exact congrArg (fun x : ℝ => (x : ℂ)) (by simpa [one_div] using hmul)
    · simp [Matrix.diagonal, hij]
  rw [hpow₁, hpow₂]
  simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
  have hpowt' :
      CFC.rpow
          (Matrix.diagonal
            (fun i => ((w i * (t * d₁ i + (1 - t) * d₂ i) ^ c : ℝ) : ℂ)) :
              CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * (t * d₁ i + (1 - t) * d₂ i) : ℝ) : ℂ)) := by
    simpa [dt] using hpowt
  rw [hpowt']
  simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype a] in
omit [Fintype a] in
/-- Convex combinations of real diagonal complex matrices stay diagonal, with
the pointwise real convex-combination entries. -/
theorem cMatrixConvexCombination_diagonal_ofReal
    (t : ℝ) (s₁ s₂ : a → ℝ) :
    cMatrixConvexCombination t
        (Matrix.diagonal fun i => (s₁ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (s₂ i : ℂ) : CMatrix a) =
      Matrix.diagonal
        (fun i => ((t * s₁ i + (1 - t) * s₂ i : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cMatrixConvexCombination, Matrix.diagonal]
  · simp [cMatrixConvexCombination, Matrix.diagonal, hij]

omit [Fintype a] in
/-- A real diagonal complex matrix is PSD when its diagonal entries are
nonnegative. -/
theorem cMatrix_diagonal_ofReal_posSemidef
    (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a).PosSemidef :=
  Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
    intro i
    change (0 : ℂ) ≤ (d i : ℂ)
    exact_mod_cast hd i)

/-- Scalar power simplification for one diagonal entry of the Frank--Lieb
`sigma` term. -/
theorem frankLieb_sigmaTerm_diagonal_entry
    {h s c : ℝ} (hh : 0 < h) (hs : 0 ≤ s) (hc_pos : 0 < c) :
    (h ^ (-(1 / 2 : ℝ)) * s ^ c * h ^ (-(1 / 2 : ℝ))) ^ (1 / c) =
      h ^ (-(1 / c)) * s := by
  have hhalf :
      h ^ (-(1 / 2 : ℝ)) * h ^ (-(1 / 2 : ℝ)) =
        h ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hh]
    ring_nf
  have hbase_nonneg : 0 ≤ h ^ (-1 : ℝ) :=
    Real.rpow_nonneg hh.le (-1 : ℝ)
  have hspow_nonneg : 0 ≤ s ^ c :=
    Real.rpow_nonneg hs c
  have hhpow :
      (h ^ (-1 : ℝ)) ^ (1 / c) = h ^ (-(1 / c)) := by
    rw [← Real.rpow_mul hh.le]
    ring_nf
  have hspow : (s ^ c) ^ (1 / c) = s := by
    simpa [one_div] using Real.rpow_rpow_inv hs hc_pos.ne'
  calc
    (h ^ (-(1 / 2 : ℝ)) * s ^ c * h ^ (-(1 / 2 : ℝ))) ^ (1 / c)
        = ((h ^ (-(1 / 2 : ℝ)) * h ^ (-(1 / 2 : ℝ))) * s ^ c) ^ (1 / c) := by
            ring_nf
    _ = (h ^ (-1 : ℝ) * s ^ c) ^ (1 / c) := by
            rw [hhalf]
    _ = (h ^ (-1 : ℝ)) ^ (1 / c) * (s ^ c) ^ (1 / c) := by
            rw [Real.mul_rpow hbase_nonneg hspow_nonneg]
    _ = h ^ (-(1 / c)) * s := by
            rw [hhpow, hspow]

/-- Evaluation of the Frank--Lieb `sigma` term on a common real diagonal
basis.  The weighted term collapses to a fixed weighted trace. -/
theorem frankLieb_sigmaTerm_diagonal_eval
    (h s : a → ℝ) (hh : ∀ i, 0 < h i) (hs : ∀ i, 0 ≤ s i)
    {c : ℝ} (hc_pos : 0 < c) :
    let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let σ : CMatrix a := Matrix.diagonal fun i => (s i : ℂ)
    ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re =
      ∑ i, h i ^ (-(1 / c)) * s i := by
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let σ : CMatrix a := Matrix.diagonal fun i => (s i : ℂ)
  have hh_nonneg : ∀ i, 0 ≤ h i := fun i => (hh i).le
  have hK :
      K =
        Matrix.diagonal (fun i => ((h i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    simpa [K, H] using
      cMatrix_rpow_diagonal_ofReal (a := a) h hh_nonneg (-(1 / 2 : ℝ))
  have hσpow :
      CFC.rpow σ c =
        Matrix.diagonal (fun i => ((s i ^ c : ℝ) : ℂ)) := by
    simpa [σ] using cMatrix_rpow_diagonal_ofReal (a := a) s hs c
  have hinner_nonneg :
      ∀ i, 0 ≤ h i ^ (-(1 / 2 : ℝ)) * s i ^ c * h i ^ (-(1 / 2 : ℝ)) := by
    intro i
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (hh i).le (-(1 / 2 : ℝ)))
        (Real.rpow_nonneg (hs i) c))
      (Real.rpow_nonneg (hh i).le (-(1 / 2 : ℝ)))
  have hinner :
      K * CFC.rpow σ c * K =
        Matrix.diagonal
          (fun i =>
            ((h i ^ (-(1 / 2 : ℝ)) * s i ^ c *
                h i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    rw [hK, hσpow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  dsimp only
  rw [hinner]
  rw [cMatrix_rpow_diagonal_ofReal (a := a)
    (fun i => h i ^ (-(1 / 2 : ℝ)) * s i ^ c *
      h i ^ (-(1 / 2 : ℝ))) hinner_nonneg (1 / c)]
  rw [Matrix.trace_diagonal]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i _
  exact frankLieb_sigmaTerm_diagonal_entry (hh i) (hs i) hc_pos

/-- Evaluation of the full fixed-weight Frank--Lieb objective on a common
real diagonal basis.  This is the commuting/classical form of the
fixed-weight variational family:
`(∑ᵢ rhoᵢ hᵢ)^α * (∑ᵢ hᵢ^(-1/c) sigmaᵢ)^(1-α)`. -/
theorem frankLiebFixedWeightObjective_diagonal_eval
    (rho sigma h : a → ℝ) (_hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 ≤ sigma i) (hh : ∀ i, 0 < h i)
    (α : ℝ) {c : ℝ} (hc_pos : 0 < c) :
    let ρD : CMatrix a := Matrix.diagonal fun i => (rho i : ℂ)
    let σD : CMatrix a := Matrix.diagonal fun i => (sigma i : ℂ)
    let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
    frankLiebFixedWeightObjective ρD σD H α c =
      (∑ i, rho i * h i) ^ α *
        (∑ i, h i ^ (-(1 / c)) * sigma i) ^ (1 - α) := by
  let ρD : CMatrix a := Matrix.diagonal fun i => (rho i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (sigma i : ℂ)
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have htrace :
      ((ρD * H).trace).re = ∑ i, rho i * h i := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [Matrix.trace_diagonal, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hsigmaTerm :
      ((CFC.rpow (K * CFC.rpow σD c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * sigma i := by
    simpa [H, K, σD] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h sigma hh hsigma hc_pos
  unfold frankLiebFixedWeightObjective
  change
    ((ρD * H).trace).re ^ α *
        ((CFC.rpow (K * CFC.rpow σD c * K) (1 / c)).trace).re ^ (1 - α) =
      (∑ i, rho i * h i) ^ α *
        (∑ i, h i ^ (-(1 / c)) * sigma i) ^ (1 - α)
  rw [htrace, hsigmaTerm]

/-- Common-diagonal-basis special case of the Frank--Lieb `sigma` term
concavity.

When `H`, `σ₁`, and `σ₂` are diagonal in the same basis, the source term is
the linear functional `σ ↦ ∑ i hᵢ^(-1/c) σᵢ`.  This is a genuine
non-circular special case of the general theorem: it proves the full weighted
`H` expression for a shared eigenbasis, without assuming Frank--Lieb
concavity. -/
theorem frankLieb_sigmaTerm_concave_diagonal
    (h s₁ s₂ : a → ℝ) (hh : ∀ i, 0 < h i)
    (hs₁ : ∀ i, 0 ≤ s₁ i) (hs₂ : ∀ i, 0 ≤ s₂ i)
    {c t : ℝ} (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let σ₁ : CMatrix a := Matrix.diagonal fun i => (s₁ i : ℂ)
    let σ₂ : CMatrix a := Matrix.diagonal fun i => (s₂ i : ℂ)
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re ≤
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re := by
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let σ₁ : CMatrix a := Matrix.diagonal fun i => (s₁ i : ℂ)
  let σ₂ : CMatrix a := Matrix.diagonal fun i => (s₂ i : ℂ)
  let st : a → ℝ := fun i => t * s₁ i + (1 - t) * s₂ i
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hst : ∀ i, 0 ≤ st i := by
    intro i
    exact add_nonneg (mul_nonneg ht0 (hs₁ i))
      (mul_nonneg (sub_nonneg.mpr ht1) (hs₂ i))
  have hσt_diag :
      σt = Matrix.diagonal fun i => (st i : ℂ) := by
    simpa [σt, σ₁, σ₂, st] using
      cMatrixConvexCombination_diagonal_ofReal (a := a) t s₁ s₂
  have heval₁ :
      ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * s₁ i := by
    simpa [H, K, σ₁] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h s₁ hh hs₁ hc_pos
  have heval₂ :
      ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * s₂ i := by
    simpa [H, K, σ₂] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h s₂ hh hs₂ hc_pos
  have hevalt :
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * st i := by
    rw [hσt_diag]
    simpa [H, K, st] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h st hh hst hc_pos
  have hsum :
      t * (∑ i, h i ^ (-(1 / c)) * s₁ i) +
          (1 - t) * (∑ i, h i ^ (-(1 / c)) * s₂ i) =
        ∑ i, h i ^ (-(1 / c)) * st i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [st]
    ring
  dsimp only
  rw [heval₁, heval₂, hevalt]
  exact le_of_eq hsum

/-- Entrywise simplification of the common-diagonal sandwiched `Q` power
term.  This is the matrix-level analogue of the scalar identity behind the
classical sandwiched Renyi power sum. -/
theorem sandwichedRenyiQ_diagonal_entry
    {p q α : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hα : 0 < α) :
    (q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α =
      p ^ α * q ^ (1 - α) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hqs_nonneg : 0 ≤ q ^ s := Real.rpow_nonneg hq_nonneg s
  have hsα : (s + s) * α = 1 - α := by
    dsimp [s]
    field_simp [ne_of_gt hα]
    ring
  calc
    (q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α =
        (p * (q ^ s * q ^ s)) ^ α := by
          dsimp [s]
          ring_nf
    _ = p ^ α * (q ^ s * q ^ s) ^ α := by
          rw [Real.mul_rpow hp (mul_nonneg hqs_nonneg hqs_nonneg)]
    _ = p ^ α * (q ^ (s + s)) ^ α := by
          rw [Real.rpow_add hq s s]
    _ = p ^ α * q ^ ((s + s) * α) := by
          rw [← Real.rpow_mul hq_nonneg (s + s) α]
    _ = p ^ α * q ^ (1 - α) := by
          rw [hsα]

/-- Matrix-level sandwiched `Q` on a common positive real diagonal reference
is the classical power sum `∑ᵢ ρᵢ^α σᵢ^(1-α)`.

The reference diagonal is assumed entrywise positive so the low-alpha
sandwich exponent never has to interpret a negative power at zero. -/
theorem sandwichedRenyiQ_diagonal_eval
    (ρ σ : a → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α =
      ∑ i, ρ i ^ α * σ i ^ (1 - α) := by
  let s : ℝ := (1 - α) / (2 * α)
  let ρD : CMatrix a := Matrix.diagonal fun i => (ρ i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (σ i : ℂ)
  have hσ_nonneg : ∀ i, 0 ≤ σ i := fun i => (hσ i).le
  have hC :
      CFC.rpow σD s =
        Matrix.diagonal (fun i => ((σ i ^ s : ℝ) : ℂ)) := by
    simpa [σD] using cMatrix_rpow_diagonal_ofReal (a := a) σ hσ_nonneg s
  have hinner_nonneg :
      ∀ i, 0 ≤ σ i ^ s * ρ i * σ i ^ s := by
    intro i
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (hσ_nonneg i) s) (hρ i))
      (Real.rpow_nonneg (hσ_nonneg i) s)
  have hinner :
      CFC.rpow σD s * ρD * CFC.rpow σD s =
        Matrix.diagonal
          (fun i => ((σ i ^ s * ρ i * σ i ^ s : ℝ) : ℂ)) := by
    rw [hC, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hM :
      CFC.rpow (CFC.rpow σD s * ρD * CFC.rpow σD s) α =
        Matrix.diagonal
          (fun i => (((σ i ^ s * ρ i * σ i ^ s) ^ α : ℝ) : ℂ)) := by
    rw [hinner]
    exact cMatrix_rpow_diagonal_ofReal
      (a := a) (fun i => σ i ^ s * ρ i * σ i ^ s) hinner_nonneg α
  unfold sandwichedRenyiQ
  change
    (CFC.rpow (CFC.rpow σD s * ρD * CFC.rpow σD s) α).trace.re =
      ∑ i, ρ i ^ α * σ i ^ (1 - α)
  rw [hM, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i _
  simpa [s, mul_assoc] using
    sandwichedRenyiQ_diagonal_entry (p := ρ i) (q := σ i) (α := α)
      (hρ i) (hσ i) hα_pos

/-- Classical/commuting lower-bound direction of the fixed-weight
Frank--Lieb variational formula.

For every positive diagonal weight `h`, the fixed-weight objective dominates
the diagonal sandwiched `Q` value. This is the scalar core behind the
noncommutative fixed-weight `sInf` bridge. -/
theorem sandwichedRenyiQ_diagonal_le_frankLiebFixedWeightObjective
    [Nonempty a] (ρ σ h : a → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hh : ∀ i, 0 < h i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ≤
      frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) := by
  classical
  let c : ℝ := (1 - α) / α
  let p : a → ℝ := fun i => ρ i * h i
  let q : a → ℝ := fun i => σ i * h i ^ (-(1 / c))
  let w : a → ℝ := fun _ => 1
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (sub_pos.mpr hα_lt_one) hα_pos
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    exact mul_nonneg (hρ i) (le_of_lt (hh i))
  have hq_pos : ∀ i, 0 < q i := by
    intro i
    exact mul_pos (hσ i) (Real.rpow_pos_of_pos (hh i) (-(1 / c)))
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    simp [w]
  have hQ_pos : 0 < ∑ i, q i * w i := by
    have hterm : ∀ i ∈ (Finset.univ : Finset a), 0 < q i * w i := by
      intro i _
      simpa [w] using hq_pos i
    exact Finset.sum_pos hterm Finset.univ_nonempty
  have hweighted :=
    real_classical_renyi_weighted_power_term_ge
      (ι := a) (p := p) (q := q) (t := w)
      (le_of_lt hα_pos) (le_of_lt hα_lt_one)
      hp_nonneg hq_pos hw_nonneg hQ_pos
  have hleft :
      ∑ i, w i * p i ^ α * q i ^ (1 - α) =
        ∑ i, ρ i ^ α * σ i ^ (1 - α) := by
    apply Finset.sum_congr rfl
    intro i _
    have hh_nonneg : 0 ≤ h i := le_of_lt (hh i)
    have hsigma_nonneg : 0 ≤ σ i := le_of_lt (hσ i)
    have hpowa : (ρ i * h i) ^ α = ρ i ^ α * h i ^ α :=
      Real.mul_rpow (hρ i) hh_nonneg
    have hpowq :
        (σ i * h i ^ (-(1 / c))) ^ (1 - α) =
          σ i ^ (1 - α) * (h i ^ (-(1 / c))) ^ (1 - α) :=
      Real.mul_rpow hsigma_nonneg
        (Real.rpow_nonneg hh_nonneg (-(1 / c)))
    have hscale :
        h i ^ α * (h i ^ (-(1 / c))) ^ (1 - α) = 1 := by
      have hexp : α + (-(1 / c)) * (1 - α) = 0 := by
        dsimp [c]
        have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
        field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
        ring_nf
      calc
        h i ^ α * (h i ^ (-(1 / c))) ^ (1 - α) =
            h i ^ α * h i ^ ((-(1 / c)) * (1 - α)) := by
              rw [← Real.rpow_mul (le_of_lt (hh i))]
        _ = h i ^ (α + (-(1 / c)) * (1 - α)) := by
              rw [← Real.rpow_add (hh i)]
        _ = 1 := by
              rw [hexp, Real.rpow_zero]
    calc
      w i * p i ^ α * q i ^ (1 - α)
          = (ρ i * h i) ^ α *
              (σ i * h i ^ (-(1 / c))) ^ (1 - α) := by
              simp [p, q, w]
      _ = (ρ i ^ α * h i ^ α) *
            (σ i ^ (1 - α) * (h i ^ (-(1 / c))) ^ (1 - α)) := by
              rw [hpowa, hpowq]
      _ = ρ i ^ α * σ i ^ (1 - α) *
            (h i ^ α * (h i ^ (-(1 / c))) ^ (1 - α)) := by
              ring
      _ = ρ i ^ α * σ i ^ (1 - α) := by
              rw [hscale, mul_one]
  have hright :
      (∑ i, p i * w i) ^ α * (∑ i, q i * w i) ^ (1 - α) =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) := by
    simp [p, q, w, mul_comm, mul_left_comm]
  have hdiagQ :
      sandwichedRenyiQ
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
          (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
          α =
        ∑ i, ρ i ^ α * σ i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρ σ hρ hσ hα_pos
  have hobj :
      frankLiebFixedWeightObjective
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
          α c =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) :=
    frankLiebFixedWeightObjective_diagonal_eval ρ σ h hρ
      (fun i => (hσ i).le) hh α hc_pos
  calc
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α =
        ∑ i, ρ i ^ α * σ i ^ (1 - α) := hdiagQ
    _ = ∑ i, w i * p i ^ α * q i ^ (1 - α) := hleft.symm
    _ ≤ (∑ i, p i * w i) ^ α *
        (∑ i, q i * w i) ^ (1 - α) := hweighted
    _ = (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) := hright
    _ = frankLiebFixedWeightObjective
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
          α ((1 - α) / α) := by
            simpa [c] using hobj.symm

/-- Positive diagonal optimizer for the fixed-weight Frank--Lieb objective.

In the common diagonal full-rank case, the weight
`hᵢ = ρᵢ^(α-1) σᵢ^(1-α)` attains the scalar sandwiched `Q` value. Together
with `sandwichedRenyiQ_diagonal_le_frankLiebFixedWeightObjective`, this gives
the classical fixed-weight variational equality before the noncommutative
Frank--Lieb `sInf` bridge. -/
theorem frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
    frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) =
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := by
  classical
  let c : ℝ := (1 - α) / α
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  let S : ℝ := ∑ i, ρ i ^ α * σ i ^ (1 - α)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (sub_pos.mpr hα_lt_one) hα_pos
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  have hS_pos : 0 < S := by
    have hterm : ∀ i ∈ (Finset.univ : Finset a), 0 < ρ i ^ α * σ i ^ (1 - α) := by
      intro i _
      exact mul_pos (Real.rpow_pos_of_pos (hρ i) α)
        (Real.rpow_pos_of_pos (hσ i) (1 - α))
    exact Finset.sum_pos hterm Finset.univ_nonempty
  have hsumρ :
      ∑ i, ρ i * h i = S := by
    apply Finset.sum_congr rfl
    intro i _
    have hρpow : ρ i * ρ i ^ (α - 1) = ρ i ^ α := by
      calc
        ρ i * ρ i ^ (α - 1) = ρ i ^ (1 : ℝ) * ρ i ^ (α - 1) := by
          rw [Real.rpow_one]
        _ = ρ i ^ ((1 : ℝ) + (α - 1)) := by
          rw [← Real.rpow_add (hρ i)]
        _ = ρ i ^ α := by
          ring_nf
    calc
      ρ i * h i = (ρ i * ρ i ^ (α - 1)) * σ i ^ (1 - α) := by
        simp [h, mul_assoc]
      _ = ρ i ^ α * σ i ^ (1 - α) := by
        rw [hρpow]
  have hsumσ :
      ∑ i, h i ^ (-(1 / c)) * σ i = S := by
    apply Finset.sum_congr rfl
    intro i _
    have hbase :
        h i ^ (-(1 / c)) =
          ρ i ^ α * σ i ^ (-α) := by
      have hρ_nonneg : 0 ≤ ρ i ^ (α - 1) := le_of_lt
        (Real.rpow_pos_of_pos (hρ i) (α - 1))
      have hσ_nonneg : 0 ≤ σ i ^ (1 - α) := le_of_lt
        (Real.rpow_pos_of_pos (hσ i) (1 - α))
      have hρexp : (α - 1) * (-(1 / c)) = α := by
        dsimp [c]
        have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
        field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
        ring_nf
      have hσexp : (1 - α) * (-(1 / c)) = -α := by
        dsimp [c]
        have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
        field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
      calc
        h i ^ (-(1 / c)) =
            (ρ i ^ (α - 1) * σ i ^ (1 - α)) ^ (-(1 / c)) := by
              rfl
        _ = (ρ i ^ (α - 1)) ^ (-(1 / c)) *
            (σ i ^ (1 - α)) ^ (-(1 / c)) := by
              rw [Real.mul_rpow hρ_nonneg hσ_nonneg]
        _ = ρ i ^ ((α - 1) * (-(1 / c))) *
            σ i ^ ((1 - α) * (-(1 / c))) := by
              rw [← Real.rpow_mul (hρ i).le, ← Real.rpow_mul (hσ i).le]
        _ = ρ i ^ α * σ i ^ (-α) := by
              rw [hρexp, hσexp]
    have hσpow : σ i ^ (-α) * σ i = σ i ^ (1 - α) := by
      calc
        σ i ^ (-α) * σ i = σ i ^ (-α) * σ i ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = σ i ^ ((-α) + (1 : ℝ)) := by
          rw [← Real.rpow_add (hσ i)]
        _ = σ i ^ (1 - α) := by
          ring_nf
    calc
      h i ^ (-(1 / c)) * σ i =
          (ρ i ^ α * σ i ^ (-α)) * σ i := by
            rw [hbase]
      _ = ρ i ^ α * (σ i ^ (-α) * σ i) := by
            ring
      _ = ρ i ^ α * σ i ^ (1 - α) := by
            rw [hσpow]
  have hobj :
      frankLiebFixedWeightObjective
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
          α c =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) :=
    frankLiebFixedWeightObjective_diagonal_eval ρ σ h
      (fun i => (hρ i).le) (fun i => (hσ i).le) hh α hc_pos
  have hdiagQ :
      sandwichedRenyiQ
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
          (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
          α = S := by
    simpa [S] using
      sandwichedRenyiQ_diagonal_eval ρ σ
        (fun i => (hρ i).le) hσ hα_pos
  have hpowS : S ^ α * S ^ (1 - α) = S := by
    calc
      S ^ α * S ^ (1 - α) = S ^ (α + (1 - α)) := by
        rw [← Real.rpow_add hS_pos]
      _ = S := by
        rw [show α + (1 - α) = (1 : ℝ) by ring, Real.rpow_one]
  dsimp only
  calc
    frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) := by
          simpa [c] using hobj
    _ = S ^ α * S ^ (1 - α) := by
          rw [hsumρ, hsumσ]
    _ = S := hpowS
    _ = sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := hdiagQ.symm

omit [Fintype a] [DecidableEq a] in
/-- Binary scalar low-alpha concavity of the classical sandwiched Renyi power
term `p^α q^(1-α)`. -/
theorem sandwichedRenyiQ_scalarTerm_concave_lowAlpha
    {p₁ p₂ q₁ q₂ α t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (p₁ ^ α * q₁ ^ (1 - α)) +
        (1 - t) * (p₂ ^ α * q₂ ^ (1 - α)) ≤
      (t * p₁ + (1 - t) * p₂) ^ α *
        (t * q₁ + (1 - t) * q₂) ^ (1 - α) := by
  let p : Bool → ℝ := fun b => cond b p₁ p₂
  let q : Bool → ℝ := fun b => cond b q₁ q₂
  let w : Bool → ℝ := fun b => cond b t (1 - t)
  have hp : ∀ b, 0 ≤ p b := by
    intro b
    cases b <;> simp [p, hp₁, hp₂]
  have hq : ∀ b, 0 < q b := by
    intro b
    cases b <;> simp [q, hq₁, hq₂]
  have hw : ∀ b, 0 ≤ w b := by
    intro b
    cases b
    · simpa [w] using sub_nonneg.mpr ht1
    · simpa [w] using ht0
  have hQ_pos : 0 < ∑ b, q b * w b := by
    have hterm_true : 0 < q true * w true + q false * w false := by
      have hsumw : w true + w false = 1 := by simp [w]
      have hqmin : 0 < min q₁ q₂ := lt_min hq₁ hq₂
      have hge :
          min q₁ q₂ * (w true + w false) ≤ q true * w true + q false * w false := by
        have hle_true : min q₁ q₂ * w true ≤ q true * w true :=
          mul_le_mul_of_nonneg_right (min_le_left q₁ q₂) (hw true)
        have hle_false : min q₁ q₂ * w false ≤ q false * w false :=
          mul_le_mul_of_nonneg_right (min_le_right q₁ q₂) (hw false)
        calc
          min q₁ q₂ * (w true + w false) =
              min q₁ q₂ * w true + min q₁ q₂ * w false := by ring
          _ ≤ q true * w true + q false * w false := add_le_add hle_true hle_false
      have hpos : 0 < min q₁ q₂ * (w true + w false) := by
        rw [hsumw, mul_one]
        exact hqmin
      exact lt_of_lt_of_le hpos hge
    simpa [Fintype.sum_bool, q, w, add_comm, add_left_comm, add_assoc] using hterm_true
  have hraw :=
    real_classical_renyi_weighted_power_term_ge
      (ι := Bool) (p := p) (q := q) (t := w)
      hα_nonneg hα_le_one hp hq hw hQ_pos
  simpa [p, q, w, Fintype.sum_bool, mul_comm, mul_left_comm, mul_assoc,
    add_comm, add_left_comm, add_assoc] using hraw

/-- Fixed-weight Frank--Lieb objective is concave in the positive reference
case.

This combines the linearity of `ρ ↦ Tr(ρH)`, unrestricted Frank--Lieb
concavity of the fixed `σ` term, and scalar weighted-product concavity.  It is
the non-circular source-aligned step immediately before the reverse-Holder
fixed-weight variational bridge for `sandwichedRenyiQ`. -/
theorem frankLiebFixedWeightObjective_concave_posDef
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α c t : ℝ} (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * frankLiebFixedWeightObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α c ≤
      frankLiebFixedWeightObjective
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let x₁ : ℝ := ((ρ₁ * H).trace).re
  let x₂ : ℝ := ((ρ₂ * H).trace).re
  let xt : ℝ := ((ρt * H).trace).re
  let y₁ : ℝ := ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re
  let y₂ : ℝ := ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re
  let yt : ℝ := ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re
  have hx₁ : 0 ≤ x₁ := by
    simpa [x₁] using cMatrix_trace_mul_posSemidef_re_nonneg hρ₁ hH.posSemidef
  have hx₂ : 0 ≤ x₂ := by
    simpa [x₂] using cMatrix_trace_mul_posSemidef_re_nonneg hρ₂ hH.posSemidef
  have hy₁ : 0 < y₁ := by
    simpa [y₁, K] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ₁) hH hσ₁ c
  have hy₂ : 0 < y₂ := by
    simpa [y₂, K] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ₂) hH hσ₂ c
  have hσt_pos : σt.PosDef := by
    have hconv : (t • σ₁ + (1 - t) • σ₂).PosDef :=
      Matrix.PosDef.convexCombination hσ₁ hσ₂ ht0 ht1
    simpa [σt, cMatrixConvexCombination_eq_real_smul] using hconv
  have hyt_pos : 0 < yt := by
    simpa [yt, K, σt] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σt) hH hσt_pos c
  have hxt :
      xt = t * x₁ + (1 - t) * x₂ := by
    have hmul :
        ρt * H = cMatrixConvexCombination t (ρ₁ * H) (ρ₂ * H) := by
      calc
        ρt * H = (cMatrixConvexCombination t ρ₁ ρ₂) * H := rfl
        _ = (t • ρ₁ + (1 - t) • ρ₂) * H := by
          rw [cMatrixConvexCombination_eq_real_smul]
        _ = t • (ρ₁ * H) + (1 - t) • (ρ₂ * H) := by
          simp [Matrix.add_mul]
        _ = cMatrixConvexCombination t (ρ₁ * H) (ρ₂ * H) := by
          rw [cMatrixConvexCombination_eq_real_smul]
    change ((ρt * H).trace).re = t * x₁ + (1 - t) * x₂
    rw [hmul]
    simpa [x₁, x₂] using cMatrixConvexCombination_trace_re t (ρ₁ * H) (ρ₂ * H)
  have hy_conc :
      t * y₁ + (1 - t) * y₂ ≤ yt := by
    simpa [y₁, y₂, yt, K, σt] using
      frankLieb_sigmaTerm_concave
        (a := a) (H := H) (σ₁ := σ₁) (σ₂ := σ₂)
        hH hσ₁.posSemidef hσ₂.posSemidef hc_pos hc_lt_one ht0 ht1
  have hybar_pos : 0 < t * y₁ + (1 - t) * y₂ := by
    have hymin : 0 < min y₁ y₂ := lt_min hy₁ hy₂
    have hle :
        min y₁ y₂ * (t + (1 - t)) ≤ t * y₁ + (1 - t) * y₂ := by
      have hle₁ :
          min y₁ y₂ * t ≤ t * y₁ := by
        calc
          min y₁ y₂ * t = t * min y₁ y₂ := by ring
          _ ≤ t * y₁ := mul_le_mul_of_nonneg_left (min_le_left y₁ y₂) ht0
      have hle₂ :
          min y₁ y₂ * (1 - t) ≤ (1 - t) * y₂ := by
        calc
          min y₁ y₂ * (1 - t) = (1 - t) * min y₁ y₂ := by ring
          _ ≤ (1 - t) * y₂ :=
              mul_le_mul_of_nonneg_left (min_le_right y₁ y₂) (sub_nonneg.mpr ht1)
      calc
        min y₁ y₂ * (t + (1 - t)) =
            min y₁ y₂ * t + min y₁ y₂ * (1 - t) := by ring
        _ ≤ t * y₁ + (1 - t) * y₂ := add_le_add hle₁ hle₂
    have hpos : 0 < min y₁ y₂ * (t + (1 - t)) := by
      rw [show t + (1 - t) = (1 : ℝ) by ring, mul_one]
      exact hymin
    exact lt_of_lt_of_le hpos hle
  have hscalar :
      t * (x₁ ^ α * y₁ ^ (1 - α)) +
          (1 - t) * (x₂ ^ α * y₂ ^ (1 - α)) ≤
        (t * x₁ + (1 - t) * x₂) ^ α *
          (t * y₁ + (1 - t) * y₂) ^ (1 - α) :=
    sandwichedRenyiQ_scalarTerm_concave_lowAlpha
      hx₁ hx₂ hy₁ hy₂ hα_nonneg hα_le_one ht0 ht1
  have hxbar_nonneg : 0 ≤ t * x₁ + (1 - t) * x₂ :=
    add_nonneg (mul_nonneg ht0 hx₁) (mul_nonneg (sub_nonneg.mpr ht1) hx₂)
  have hyleft_nonneg : 0 ≤ t * y₁ + (1 - t) * y₂ := le_of_lt hybar_pos
  have hpow_y :
      (t * y₁ + (1 - t) * y₂) ^ (1 - α) ≤ yt ^ (1 - α) :=
    Real.rpow_le_rpow hyleft_nonneg hy_conc (sub_nonneg.mpr hα_le_one)
  have hxpow_nonneg : 0 ≤ (t * x₁ + (1 - t) * x₂) ^ α :=
    Real.rpow_nonneg hxbar_nonneg α
  have hmono :
      (t * x₁ + (1 - t) * x₂) ^ α *
          (t * y₁ + (1 - t) * y₂) ^ (1 - α) ≤
        (t * x₁ + (1 - t) * x₂) ^ α * yt ^ (1 - α) :=
    mul_le_mul_of_nonneg_left hpow_y hxpow_nonneg
  calc
    t * frankLiebFixedWeightObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α c =
        t * (x₁ ^ α * y₁ ^ (1 - α)) +
          (1 - t) * (x₂ ^ α * y₂ ^ (1 - α)) := by
          simp [frankLiebFixedWeightObjective, x₁, x₂, y₁, y₂, K]
    _ ≤ (t * x₁ + (1 - t) * x₂) ^ α *
          (t * y₁ + (1 - t) * y₂) ^ (1 - α) := hscalar
    _ ≤ (t * x₁ + (1 - t) * x₂) ^ α * yt ^ (1 - α) := hmono
    _ = xt ^ α * yt ^ (1 - α) := by
          rw [hxt]
    _ = frankLiebFixedWeightObjective ρt σt H α c := by
          simp [frankLiebFixedWeightObjective, xt, yt, K]

/-- Strict low-`alpha` specialization of the fixed-weight Frank--Lieb
objective concavity with `c = (1 - alpha) / alpha`. -/
theorem frankLiebFixedWeightObjective_concave_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
        (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤
      frankLiebFixedWeightObjective
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α) := by
  exact frankLiebFixedWeightObjective_concave_posDef
    (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
    hH hρ₁ hρ₂ hσ₁ hσ₂
    (by linarith) (le_of_lt hα_lt_one)
    (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
    (sandwichedRenyiQ_frankLiebExponent_lt_one hα_half hα_lt_one)
    ht0 ht1

/-- Fixed-weight Frank--Lieb variational values for the low-`alpha`
sandwiched `Q` functional.

The intended bridge is that `sandwichedRenyiQ` is the infimum over these
positive-definite weights.  Keeping this value set explicit lets the
Frank--Lieb concavity theorem feed the later `sInf` step without assuming
joint concavity of `Q` itself. -/
def sandwichedRenyiQFixedWeightValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  {y | ∃ H : CMatrix a, H.PosDef ∧
    y = frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α)}

/-- Trace-one positive-definite fixed-weight values.  This normalized variant
matches the normalized reverse-Holder side-state domain; the strict low-alpha
homogeneity theorem identifies it with the unrestricted fixed-weight set. -/
def sandwichedRenyiQFixedWeightStateValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  {y | ∃ H : CMatrix a, H.PosDef ∧ H.trace.re = 1 ∧
    y = frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α)}

/-- Additive Gour/Frank--Lieb Young objective values for the low-`alpha`
sandwiched `Q` functional.

This source-shaped family is equivalent, after optimizing over positive scalar
rescalings of the weight, to the multiplicative fixed-weight family above. -/
def sandwichedRenyiQAdditiveValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  {y | ∃ H : CMatrix a, H.PosDef ∧
    y = frankLiebAdditiveObjective ρ σ H α ((1 - α) / α)}

theorem sandwichedRenyiQFixedWeightValueSet_mem
    {ρ σ H : CMatrix a} (hH : H.PosDef) (α : ℝ) :
    frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) ∈
      sandwichedRenyiQFixedWeightValueSet ρ σ α :=
  ⟨H, hH, rfl⟩

theorem sandwichedRenyiQFixedWeightStateValueSet_mem
    {ρ σ H : CMatrix a} (hH : H.PosDef) (hHtr : H.trace.re = 1) (α : ℝ) :
    frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) ∈
      sandwichedRenyiQFixedWeightStateValueSet ρ σ α :=
  ⟨H, hH, hHtr, rfl⟩

theorem sandwichedRenyiQAdditiveValueSet_mem
    {ρ σ H : CMatrix a} (hH : H.PosDef) (α : ℝ) :
    frankLiebAdditiveObjective ρ σ H α ((1 - α) / α) ∈
      sandwichedRenyiQAdditiveValueSet ρ σ α :=
  ⟨H, hH, rfl⟩

/-- Fixed-weight Frank--Lieb objective values are nonnegative on PSD inputs. -/
theorem frankLiebFixedWeightObjective_nonneg
    {ρ σ H : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hH : H.PosDef)
    (α c : ℝ) :
    0 ≤ frankLiebFixedWeightObjective ρ σ H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hx : 0 ≤ ((ρ * H).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy :
      0 ≤ ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
    simpa [K] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  exact mul_nonneg (Real.rpow_nonneg hx α) (Real.rpow_nonneg hy (1 - α))

/-- Additive Gour/Frank--Lieb objective values are nonnegative in the
low-`alpha` weight range. -/
theorem frankLiebAdditiveObjective_nonneg
    {ρ σ H : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hH : H.PosDef)
    {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ frankLiebAdditiveObjective ρ σ H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hx : 0 ≤ ((ρ * H).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy :
      0 ≤ ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
    simpa [K] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  unfold frankLiebAdditiveObjective
  exact add_nonneg (mul_nonneg hα0 hx) (mul_nonneg h1α hy)

/-- Zero is a lower bound for the fixed-weight value set on PSD inputs. -/
theorem sandwichedRenyiQFixedWeightValueSet_lowerBound_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    0 ∈ lowerBounds (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  exact frankLiebFixedWeightObjective_nonneg hρ hσ hH α ((1 - α) / α)

/-- Gour/Frank--Lieb lower-bound direction: for positive-definite inputs,
`Q_α(ρ, σ)` is a lower bound for every positive-definite fixed-weight
objective.

This is the noncommutative source-shaped Young lower bound after the
`LL*`/`L*L` rewrite, and replaces the earlier diagonal-only lower-bound
sanity check. -/
theorem sandwichedRenyiQFixedWeightValueSet_lowerBound_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      lowerBounds (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  exact sandwichedRenyiQ_le_frankLiebFixedWeightObjective_posDef
    hρ hσ hH hα_half hα_lt_one

/-- Infimum lower-bound direction of Gour's fixed-weight variational formula:
the fixed-weight infimum is at least the sandwiched `Q` value. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_ge_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  have hnonempty : (sandwichedRenyiQFixedWeightValueSet ρ σ α).Nonempty := by
    refine ⟨frankLiebFixedWeightObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
    exact sandwichedRenyiQFixedWeightValueSet_mem
      (ρ := ρ) (σ := σ) (H := (1 : CMatrix a)) Matrix.PosDef.one α
  exact le_csInf
    hnonempty
    (sandwichedRenyiQFixedWeightValueSet_lowerBound_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- The positive-definite reverse-Holder optimizer induces an actual
fixed-weight Frank--Lieb value equal to `Q_α(ρ, σ)`.

This is the optimizer half of Gour's Young variational formula. It constructs
`H = σ^(c/2) N^(-c) σ^(c/2)` from the normalized reverse-Holder optimizer
`N` of the sandwiched inner operator. -/
theorem sandwichedRenyiQ_mem_fixedWeightValueSet_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      sandwichedRenyiQFixedWeightValueSet ρ σ α := by
  let c : ℝ := (1 - α) / α
  let s : ℝ := c / 2
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiQInner_posSemidef hρ.posSemidef hσ.posSemidef α
  let Q : ℝ := sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α
  let N : CMatrix a := psdTraceReverseHolderOptimizer M hM α
  let S : CMatrix a := CFC.rpow σ s
  let D : CMatrix a := CFC.rpow σ (-s)
  let W : CMatrix a := CFC.rpow N (-c)
  let H : CMatrix a := S * W * S
  have hα_pos : 0 < α := by linarith
  have hc_pos : 0 < c := by
    simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hMdef : M.PosDef := by
    simpa [M] using sandwichedRenyiQInner_posDef hρ hσ α
  have hMne : M ≠ 0 := by
    intro hzero
    have htr : (0 : ℂ) < M.trace := Matrix.PosDef.trace_pos hMdef
    rw [hzero] at htr
    simp at htr
  have hQ_power_pos : 0 < psdTracePower M hM α :=
    psdTracePower_pos_of_ne_zero M hM hMne
  have hNdef : N.PosDef :=
    psdTraceReverseHolderOptimizer_posDef_of_posDef hM hMdef hQ_power_pos
  have hNpsd : N.PosSemidef := hNdef.posSemidef
  rcases psdTraceReverseHolderOptimizer_props hM hα_pos hQ_power_pos with
    ⟨_hN, hNtr, _hSupport, hattain⟩
  have hQ_eq_power : Q = psdTracePower M hM α := by
    simpa [Q, M] using
      sandwichedRenyiQ_eq_psdTracePower_QInner hρ.posSemidef hσ.posSemidef α
  have hQ_pos : 0 < Q := by
    simpa [hQ_eq_power] using hQ_power_pos
  have hschatten :
      ((M * CFC.rpow N (1 - 1 / α)).trace).re =
        Real.rpow Q (1 / α) := by
    have hnorm :
        psdSchattenPNorm M hM α = Real.rpow Q (1 / α) := by
      rw [psdSchattenPNorm, ← hQ_eq_power]
    exact hattain.symm.trans hnorm
  have hexp : -c = 1 - 1 / α := by
    dsimp [c]
    field_simp [ne_of_gt hα_pos]
    ring
  have hW_eq : W = CFC.rpow N (1 - 1 / α) := by
    simp [W, hexp]
  have hSdef : S.PosDef := by
    simpa [S] using cMatrix_rpow_posDef_of_posDef hσ s
  have hSstar : star S = S := hSdef.isHermitian.eq
  have hWdef : W.PosDef := by
    simpa [W] using cMatrix_rpow_posDef_of_posDef hNdef (-c)
  have hH : H.PosDef := by
    have hconj : (star S * W * S).PosDef := by
      rw [Matrix.IsUnit.posDef_star_left_conjugate_iff hSdef.isUnit]
      exact hWdef
    rwa [hSstar] at hconj
  have hDS : D * S = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_neg_mul_rpow (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hSD : S * D = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_mul_rpow_neg (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDHD : D * H * D = W := by
    calc
      D * H * D = D * (S * W * S) * D := rfl
      _ = (D * S) * W * (S * D) := by
        simp [Matrix.mul_assoc]
      _ = W := by
        rw [hDS, hSD]
        simp
  have hx :
      ((ρ * H).trace).re = Real.rpow Q (1 / α) := by
    have htrace :=
      sandwichedRenyiQInner_mul_sourceWeight_trace_re_eq
        (a := a) (ρ := ρ) (σ := σ) (H := H) hσ
        (α := α) (c := c) (rfl : c = (1 - α) / α)
    have htraceD : ((M * (D * H * D)).trace).re = ((ρ * H).trace).re := by
      simpa [M, D, c] using htrace
    calc
      ((ρ * H).trace).re = ((M * (D * H * D)).trace).re := htraceD.symm
      _ = ((M * W).trace).re := by rw [hDHD]
      _ = ((M * CFC.rpow N (1 - 1 / α)).trace).re := by
        rw [hW_eq]
      _ = Real.rpow Q (1 / α) := hschatten
  have hy :
      frankLiebSourceSigmaTerm σ H c = 1 := by
    have hinner : (CFC.rpow σ (-(c / 2)) * H *
        CFC.rpow σ (-(c / 2))) = W := by
      simpa [D, s] using hDHD
    have hpowW : CFC.rpow W (-(1 / c)) = N := by
      have hr_ne : (-c : ℝ) ≠ 0 := neg_ne_zero.mpr hc_ne
      have hrt : (-c : ℝ) * (-(1 / c)) = (1 : ℝ) := by
        field_simp [hc_ne]
      calc
        CFC.rpow W (-(1 / c)) =
            CFC.rpow N (1 : ℝ) := by
              simpa [W] using
                cMatrix_rpow_rpow_of_posDef (A := N) hNdef hr_ne hrt
        _ = N := by
              exact CFC.rpow_one N
                (ha := Matrix.nonneg_iff_posSemidef.mpr hNdef.posSemidef)
    calc
      frankLiebSourceSigmaTerm σ H c =
          ((CFC.rpow (CFC.rpow σ (-(c / 2)) * H *
            CFC.rpow σ (-(c / 2))) (-(1 / c))).trace).re := rfl
      _ = ((CFC.rpow W (-(1 / c))).trace).re := by rw [hinner]
      _ = N.trace.re := by rw [hpowW]
      _ = 1 := hNtr
  have hfixed :
      frankLiebFixedWeightObjective ρ σ H α c = Q := by
    have hsource :
        frankLiebSourceFixedWeightObjective ρ σ H α c = Q := by
      unfold frankLiebSourceFixedWeightObjective
      calc
        ((ρ * H).trace).re ^ α * frankLiebSourceSigmaTerm σ H c ^ (1 - α) =
            (Real.rpow Q (1 / α)) ^ α * (1 : ℝ) ^ (1 - α) := by
              rw [hx, hy]
        _ = Q := by
              rw [show (Real.rpow Q (1 / α)) ^ α = Q by
                simpa [one_div] using
                  (Real.rpow_inv_rpow (le_of_lt hQ_pos) (ne_of_gt hα_pos))]
              simp
    have hsigma :
        frankLiebSourceSigmaTerm σ H c =
          (let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
          ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re) :=
      frankLiebSourceSigmaTerm_eq_frankLieb_sigmaTerm
        (a := a) (σ := σ) (H := H) hσ hH (c := c)
    have hobj :
        frankLiebSourceFixedWeightObjective ρ σ H α c =
          frankLiebFixedWeightObjective ρ σ H α c := by
      unfold frankLiebSourceFixedWeightObjective frankLiebFixedWeightObjective
      rw [hsigma]
    exact hobj.symm.trans hsource
  refine ⟨H, hH, ?_⟩
  simpa [c] using hfixed.symm

/-- Infimum upper-bound direction of Gour's fixed-weight variational formula:
the fixed-weight infimum is at most the sandwiched `Q` value. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_le_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α := by
  have hbdd : BddBelow (sandwichedRenyiQFixedWeightValueSet ρ σ α) :=
    ⟨0, sandwichedRenyiQFixedWeightValueSet_lowerBound_zero
      hρ.posSemidef hσ.posSemidef α⟩
  exact csInf_le hbdd
    (sandwichedRenyiQ_mem_fixedWeightValueSet_posDef
      hρ hσ hα_half hα_lt_one)

/-- Positive-definite fixed-weight Frank--Lieb variational formula for the
PSD-friendly low-`α` `Q` functional. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α :=
  le_antisymm
    (sandwichedRenyiQFixedWeightValueSet_sInf_le_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)
    (sandwichedRenyiQFixedWeightValueSet_sInf_ge_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- Zero is a lower bound for the additive Gour/Frank--Lieb value set on PSD
inputs in the low-`alpha` weight range. -/
theorem sandwichedRenyiQAdditiveValueSet_lowerBound_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ∈ lowerBounds (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  exact frankLiebAdditiveObjective_nonneg hρ hσ hH hα0 hα1

/-- Gour additive value-set lower-bound direction: for positive-definite
inputs, `Q_α(ρ, σ)` is a lower bound for every additive Young objective. -/
theorem sandwichedRenyiQAdditiveValueSet_lowerBound_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      lowerBounds (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  have hQ_le_fixed :
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
        frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) :=
    sandwichedRenyiQ_le_frankLiebFixedWeightObjective_posDef
      hρ hσ hH hα_half hα_lt_one
  have hfixed_le_add :
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) ≤
        frankLiebAdditiveObjective ρ σ H α ((1 - α) / α) :=
    frankLiebFixedWeightObjective_le_additiveObjective
      hρ.posSemidef hσ.posSemidef hH hα_nonneg hα_le_one
  exact hQ_le_fixed.trans hfixed_le_add

/-- Infimum lower-bound direction of Gour's additive variational formula. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_ge_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
  have hnonempty : (sandwichedRenyiQAdditiveValueSet ρ σ α).Nonempty := by
    refine ⟨frankLiebAdditiveObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
    exact sandwichedRenyiQAdditiveValueSet_mem
      (ρ := ρ) (σ := σ) (H := (1 : CMatrix a)) Matrix.PosDef.one α
  exact le_csInf
    hnonempty
    (sandwichedRenyiQAdditiveValueSet_lowerBound_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- For zero left input, zero is the least fixed-weight Frank--Lieb value. -/
theorem sandwichedRenyiQFixedWeightValueSet_zero_left_isLeast
    (σ : CMatrix a) (hσ : σ.PosSemidef) {α : ℝ} (hα_pos : 0 < α) :
    IsLeast (sandwichedRenyiQFixedWeightValueSet (0 : CMatrix a) σ α) 0 := by
  constructor
  · refine ⟨(1 : CMatrix a), Matrix.PosDef.one, ?_⟩
    simpa using
      (frankLiebFixedWeightObjective_zero_left
        (a := a) σ (1 : CMatrix a) (α := α) (c := (1 - α) / α) hα_pos).symm
  · exact sandwichedRenyiQFixedWeightValueSet_lowerBound_zero
      (ρ := (0 : CMatrix a)) (σ := σ) Matrix.PosSemidef.zero hσ α

/-- For zero left input, the fixed-weight Frank--Lieb infimum equals the
PSD-friendly `Q` value. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_zero_left
    (σ : CMatrix a) (hσ : σ.PosSemidef) {α : ℝ} (hα_pos : 0 < α) :
    sInf (sandwichedRenyiQFixedWeightValueSet (0 : CMatrix a) σ α) =
      sandwichedRenyiQ (0 : CMatrix a) σ Matrix.PosSemidef.zero hσ α := by
  calc
    sInf (sandwichedRenyiQFixedWeightValueSet (0 : CMatrix a) σ α) = 0 :=
      (sandwichedRenyiQFixedWeightValueSet_zero_left_isLeast
        (a := a) σ hσ hα_pos).csInf_eq
    _ = sandwichedRenyiQ (0 : CMatrix a) σ Matrix.PosSemidef.zero hσ α :=
      (sandwichedRenyiQ_zero_left σ hσ hα_pos).symm

/-- Positive-definite-reference zero-inner branch of the fixed-weight
Frank--Lieb variational formula. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_of_inner_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    {α : ℝ} (hα_pos : 0 < α)
    (hinner : sandwichedRenyiQInner ρ σ α = 0) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ hσ.posSemidef α := by
  have hρzero :
      ρ = 0 :=
    (sandwichedRenyiQInner_eq_zero_iff_left_eq_zero_of_sigma_posDef
      (a := a) (ρ := ρ) (σ := σ) hσ α).mp hinner
  subst hρzero
  exact sandwichedRenyiQFixedWeightValueSet_sInf_eq_zero_left
    (a := a) σ hσ.posSemidef hα_pos

/-- The fixed-weight value set is bounded below on PSD inputs. -/
theorem sandwichedRenyiQFixedWeightValueSet_bddBelow
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    BddBelow (sandwichedRenyiQFixedWeightValueSet ρ σ α) :=
  ⟨0, sandwichedRenyiQFixedWeightValueSet_lowerBound_zero hρ hσ α⟩

theorem sandwichedRenyiQAdditiveValueSet_bddBelow
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    BddBelow (sandwichedRenyiQAdditiveValueSet ρ σ α) :=
  ⟨0, sandwichedRenyiQAdditiveValueSet_lowerBound_zero hρ hσ hα0 hα1⟩

/-- Any fixed-weight value bounds the infimum of the fixed-weight family from
above. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) (α : ℝ) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) :=
  csInf_le (sandwichedRenyiQFixedWeightValueSet_bddBelow hρ hσ α)
    (sandwichedRenyiQFixedWeightValueSet_mem hH α)

/-- In the positive diagonal case, the sandwiched `Q` value is attained by an
explicit member of the fixed-weight Frank--Lieb value family. -/
theorem sandwichedRenyiQ_diagonal_mem_fixedWeightValueSet_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      sandwichedRenyiQFixedWeightValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α := by
  classical
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  have hH : H.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((h i : ℝ) : ℂ)
    exact_mod_cast hh i
  refine ⟨H, hH, ?_⟩
  exact (frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
    (a := a) ρ σ hρ hσ hα_pos hα_lt_one).symm

/-- Infimum upper bound supplied by the explicit positive diagonal
Frank--Lieb optimizer. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_le_diagonal_sandwichedRenyiQ_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α) ≤
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := by
  exact csInf_le
    (sandwichedRenyiQFixedWeightValueSet_bddBelow
      (ρ := (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a))
      (σ := (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a))
      (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
      (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
      α)
    (sandwichedRenyiQ_diagonal_mem_fixedWeightValueSet_posDef
      (a := a) ρ σ hρ hσ hα_pos hα_lt_one)

/-- Diagonal-only fixed-weight Frank--Lieb values.

This auxiliary family isolates the commuting/classical fixed-weight
variational formula from the still-missing noncommutative minimization over
all positive-definite weights. -/
def sandwichedRenyiQDiagonalFixedWeightValueSet
    (ρ σ : a → ℝ) (α : ℝ) : Set ℝ :=
  {y | ∃ h : a → ℝ, (∀ i, 0 < h i) ∧
    y = frankLiebFixedWeightObjective
      (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
      (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
      (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
      α ((1 - α) / α)}

theorem sandwichedRenyiQDiagonalFixedWeightValueSet_mem
    (ρ σ h : a → ℝ) (hh : ∀ i, 0 < h i) (α : ℝ) :
    frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) ∈
      sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α :=
  ⟨h, hh, rfl⟩

/-- The diagonal sandwiched `Q` value is a lower bound for every positive
diagonal fixed-weight objective. -/
theorem sandwichedRenyiQDiagonalFixedWeightValueSet_lowerBound_sandwichedRenyiQ
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      lowerBounds (sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨h, hh, rfl⟩
  exact sandwichedRenyiQ_diagonal_le_frankLiebFixedWeightObjective
    (a := a) ρ σ h hρ hσ hh hα_pos hα_lt_one

/-- In the positive diagonal case, the diagonal fixed-weight family attains
the sandwiched `Q` value. -/
theorem sandwichedRenyiQ_diagonal_mem_diagonalFixedWeightValueSet_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α := by
  classical
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  refine ⟨h, hh, ?_⟩
  exact (frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
    (a := a) ρ σ hρ hσ hα_pos hα_lt_one).symm

/-- Positive diagonal fixed-weight variational formula for the sandwiched
`Q` functional as an `IsLeast` statement. -/
theorem sandwichedRenyiQDiagonalFixedWeightValueSet_isLeast_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    IsLeast (sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α)
      (sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α) := by
  constructor
  · exact sandwichedRenyiQ_diagonal_mem_diagonalFixedWeightValueSet_posDef
      (a := a) ρ σ hρ hσ hα_pos hα_lt_one
  · exact sandwichedRenyiQDiagonalFixedWeightValueSet_lowerBound_sandwichedRenyiQ
      (a := a) ρ σ (fun i => (hρ i).le) hσ hα_pos hα_lt_one

/-- Positive diagonal fixed-weight variational formula in `sInf` form. -/
theorem sandwichedRenyiQDiagonalFixedWeightValueSet_sInf_eq_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α :=
  (sandwichedRenyiQDiagonalFixedWeightValueSet_isLeast_posDef
    (a := a) ρ σ hρ hσ hα_pos hα_lt_one).csInf_eq

/-- Zero is a lower bound for the trace-one fixed-weight value set on PSD
inputs. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_lowerBound_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    0 ∈ lowerBounds (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, _hHtr, rfl⟩
  exact frankLiebFixedWeightObjective_nonneg hρ hσ hH α ((1 - α) / α)

/-- The trace-one fixed-weight value set is bounded below on PSD inputs. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_bddBelow
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    BddBelow (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) :=
  ⟨0, sandwichedRenyiQFixedWeightStateValueSet_lowerBound_zero hρ hσ α⟩

/-- Any trace-one fixed-weight value bounds the infimum of the trace-one
family from above. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_sInf_le_fixedWeight
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) (hHtr : H.trace.re = 1) (α : ℝ) :
    sInf (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) ≤
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) :=
  csInf_le (sandwichedRenyiQFixedWeightStateValueSet_bddBelow hρ hσ α)
    (sandwichedRenyiQFixedWeightStateValueSet_mem hH hHtr α)

/-- The fixed-weight value family is nonempty, using the identity weight. -/
theorem sandwichedRenyiQFixedWeightValueSet_nonempty
    [Nonempty a] (ρ σ : CMatrix a) (α : ℝ) :
    (sandwichedRenyiQFixedWeightValueSet ρ σ α).Nonempty := by
  refine ⟨frankLiebFixedWeightObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
  exact sandwichedRenyiQFixedWeightValueSet_mem (ρ := ρ) (σ := σ)
    (H := (1 : CMatrix a)) Matrix.PosDef.one α

/-- The additive Gour/Frank--Lieb value family is nonempty, using the
identity weight. -/
theorem sandwichedRenyiQAdditiveValueSet_nonempty
    [Nonempty a] (ρ σ : CMatrix a) (α : ℝ) :
    (sandwichedRenyiQAdditiveValueSet ρ σ α).Nonempty := by
  refine ⟨frankLiebAdditiveObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
  exact sandwichedRenyiQAdditiveValueSet_mem (ρ := ρ) (σ := σ)
    (H := (1 : CMatrix a)) Matrix.PosDef.one α

/-- On full-rank inputs, optimizing Gour's additive Young objective over
unrestricted positive weights gives the same infimum as the multiplicative
fixed-weight objective family.

The two inequalities are the source AM--GM bound and the reverse optimized
rescaling supplied by
`frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef`. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_eq_fixedWeightValueSet_sInf_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  let c : ℝ := (1 - α) / α
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hc_pos : 0 < c := by
    simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hA_bdd :
      BddBelow (sandwichedRenyiQAdditiveValueSet ρ σ α) :=
    sandwichedRenyiQAdditiveValueSet_bddBelow
      hρ.posSemidef hσ.posSemidef hα_nonneg hα_le_one
  have hF_bdd :
      BddBelow (sandwichedRenyiQFixedWeightValueSet ρ σ α) :=
    sandwichedRenyiQFixedWeightValueSet_bddBelow
      hρ.posSemidef hσ.posSemidef α
  have hA_nonempty :
      (sandwichedRenyiQAdditiveValueSet ρ σ α).Nonempty :=
    sandwichedRenyiQAdditiveValueSet_nonempty ρ σ α
  have hF_nonempty :
      (sandwichedRenyiQFixedWeightValueSet ρ σ α).Nonempty :=
    sandwichedRenyiQFixedWeightValueSet_nonempty ρ σ α
  have hA_le_F :
      sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) ≤
        sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
    refine le_csInf hF_nonempty ?_
    intro z hz
    rcases hz with ⟨H, hH, rfl⟩
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let x : ℝ := ((ρ * H).trace).re
    let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
    let lambda : ℝ := (y / x) ^ (1 - α)
    have hx : 0 < x := by
      simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH
    have hy : 0 < y := by
      simpa [y, K, c] using frankLieb_sigmaTerm_pos
        (a := a) (H := H) (σ := σ) hH hσ c
    have hlambda_pos : 0 < lambda := by
      dsimp [lambda]
      exact Real.rpow_pos_of_pos (div_pos hy hx) (1 - α)
    have hHscaled : (lambda • H : CMatrix a).PosDef := by
      simpa using Matrix.PosDef.smul hH hlambda_pos
    have hscaled :
        frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
          frankLiebFixedWeightObjective ρ σ H α c := by
      simpa [c, K, x, y, lambda] using
        frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef
          (a := a) (ρ := ρ) (σ := σ) (H := H)
          hρ hσ hH hα_half hα_lt_one
    have hmem :
        frankLiebFixedWeightObjective ρ σ H α c ∈
          sandwichedRenyiQAdditiveValueSet ρ σ α := by
      refine ⟨lambda • H, hHscaled, ?_⟩
      simpa [c] using hscaled.symm
    simpa [c] using csInf_le hA_bdd hmem
  have hF_le_A :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
        sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
    refine le_csInf hA_nonempty ?_
    intro z hz
    rcases hz with ⟨H, hH, rfl⟩
    have hfixed_le_add :
        frankLiebFixedWeightObjective ρ σ H α c ≤
          frankLiebAdditiveObjective ρ σ H α c :=
      frankLiebFixedWeightObjective_le_additiveObjective
        hρ.posSemidef hσ.posSemidef hH hα_nonneg hα_le_one
    have hsInf_le_fixed :
        sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
          frankLiebFixedWeightObjective ρ σ H α c := by
      simpa [c] using sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
        hρ.posSemidef hσ.posSemidef hH α
    exact hsInf_le_fixed.trans hfixed_le_add
  exact le_antisymm hA_le_F hF_le_A

/-- A fixed-weight optimizer for the multiplicative Frank--Lieb family gives
an actual member of Gour's additive Young value family.

This is the source-shaped optimizer direction in Gour's variational formula:
the additive objective may first optimize over positive scalar rescalings of a
weight, and at the Young-optimal scale it agrees with the multiplicative
fixed-weight objective. -/
theorem sandwichedRenyiQ_mem_additiveValueSet_of_fixedWeight_eq_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hfixed :
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) =
        sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      sandwichedRenyiQAdditiveValueSet ρ σ α := by
  let c : ℝ := (1 - α) / α
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  let lambda : ℝ := (y / x) ^ (1 - α)
  have hx : 0 < x := by
    simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH
  have hy : 0 < y := by
    simpa [y, K, c] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ) hH hσ c
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    exact Real.rpow_pos_of_pos (div_pos hy hx) (1 - α)
  have hHscaled : (lambda • H : CMatrix a).PosDef := by
    simpa using Matrix.PosDef.smul hH hlambda_pos
  have hscaled :
      frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
        frankLiebFixedWeightObjective ρ σ H α c := by
    simpa [c, K, x, y, lambda] using
      frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef
        (a := a) (ρ := ρ) (σ := σ) (H := H)
        hρ hσ hH hα_half hα_lt_one
  refine ⟨lambda • H, hHscaled, ?_⟩
  calc
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α =
        frankLiebFixedWeightObjective ρ σ H α c := by
          simpa [c] using hfixed.symm
    _ = frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c :=
          hscaled.symm

/-- In the positive diagonal case, Gour's additive Young value family contains
the sandwiched `Q` value.

This is the commuting source sanity check for the additive variational route:
the diagonal fixed-weight optimizer is transported to the additive family by
the Young-optimal scalar rescaling. -/
theorem sandwichedRenyiQ_diagonal_mem_additiveValueSet_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hα_half : 1 / 2 < α) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      sandwichedRenyiQAdditiveValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α := by
  classical
  let ρD : CMatrix a := Matrix.diagonal fun i => (ρ i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (σ i : ℂ)
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  have hρD : ρD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((ρ i : ℝ) : ℂ)
    exact_mod_cast hρ i
  have hσD : σD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((σ i : ℝ) : ℂ)
    exact_mod_cast hσ i
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  have hH : H.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((h i : ℝ) : ℂ)
    exact_mod_cast hh i
  have hfixed :
      frankLiebFixedWeightObjective ρD σD H α ((1 - α) / α) =
        sandwichedRenyiQ ρD σD hρD.posSemidef hσD.posSemidef α := by
    simpa [ρD, σD, H, h] using
      frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
        (a := a) ρ σ hρ hσ hα_pos hα_lt_one
  have hmem :
      sandwichedRenyiQ ρD σD hρD.posSemidef hσD.posSemidef α ∈
        sandwichedRenyiQAdditiveValueSet ρD σD α :=
    sandwichedRenyiQ_mem_additiveValueSet_of_fixedWeight_eq_posDef
      (a := a) hρD hσD hH hα_half hα_lt_one hfixed
  simpa [ρD, σD] using hmem

/-- Infimum upper-bound direction of Gour's additive variational formula in
the positive diagonal case. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_le_diagonal_sandwichedRenyiQ_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQAdditiveValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α) ≤
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := by
  let ρD : CMatrix a := Matrix.diagonal fun i => (ρ i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (σ i : ℂ)
  have hρD : ρD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((ρ i : ℝ) : ℂ)
    exact_mod_cast hρ i
  have hσD : σD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((σ i : ℝ) : ℂ)
    exact_mod_cast hσ i
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hmem :
      sandwichedRenyiQ ρD σD hρD.posSemidef hσD.posSemidef α ∈
        sandwichedRenyiQAdditiveValueSet ρD σD α := by
    simpa [ρD, σD] using
      sandwichedRenyiQ_diagonal_mem_additiveValueSet_posDef
        (a := a) ρ σ hρ hσ (by linarith) hα_lt_one hα_half
  have hbdd :
      BddBelow (sandwichedRenyiQAdditiveValueSet ρD σD α) :=
    sandwichedRenyiQAdditiveValueSet_bddBelow
      hρD.posSemidef hσD.posSemidef hα_nonneg hα_le_one
  simpa [ρD, σD] using csInf_le hbdd hmem

/-- Transport a completed fixed-weight variational formula to the
source-shaped additive Gour/Frank--Lieb value family. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_eq_of_fixedWeight_sInf_eq_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hfixed :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
        sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α) :
    sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α := by
  rw [sandwichedRenyiQAdditiveValueSet_sInf_eq_fixedWeightValueSet_sInf_posDef
    hρ hσ hα_half hα_lt_one, hfixed]

/-- Positive-definite additive Gour/Frank--Lieb variational formula for the
PSD-friendly low-`α` `Q` functional. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_eq_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α :=
  sandwichedRenyiQAdditiveValueSet_sInf_eq_of_fixedWeight_sInf_eq_posDef
    hρ hσ hα_half hα_lt_one
    (sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- Transport a completed additive Gour/Frank--Lieb variational formula back
to the multiplicative fixed-weight family used by existing concavity
infrastructure. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_of_additive_sInf_eq_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hadd :
      sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
        sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α := by
  have heq :=
    sandwichedRenyiQAdditiveValueSet_sInf_eq_fixedWeightValueSet_sInf_posDef
      hρ hσ hα_half hα_lt_one
  rw [← heq, hadd]

/-- Trace-one fixed-weight values are nonempty, using the identity normalized
by the dimension trace. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_nonempty
    [Nonempty a] (ρ σ : CMatrix a) (α : ℝ) :
    (sandwichedRenyiQFixedWeightStateValueSet ρ σ α).Nonempty := by
  let trI : ℝ := ((1 : CMatrix a).trace).re
  have htrI_pos : 0 < trI := by
    exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (Matrix.PosDef.one : (1 : CMatrix a).PosDef))).1
  let H : CMatrix a := (trI⁻¹ : ℝ) • (1 : CMatrix a)
  have hH : H.PosDef := by
    simpa [H] using Matrix.PosDef.smul
      (Matrix.PosDef.one : (1 : CMatrix a).PosDef) (inv_pos.mpr htrI_pos)
  have htrI_im : ((1 : CMatrix a).trace).im = 0 :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (Matrix.PosDef.one : (1 : CMatrix a).PosDef))).2.symm
  have hHtr : H.trace.re = 1 := by
    simp [H, trI, Matrix.trace_smul]
  refine ⟨frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α), ?_⟩
  exact sandwichedRenyiQFixedWeightStateValueSet_mem hH hHtr α

/-- In the strict low-alpha range, the unrestricted fixed-weight values equal
the trace-one fixed-weight values.  This removes the normalization mismatch
between Frank--Lieb weights and reverse-Holder side-states. -/
theorem sandwichedRenyiQFixedWeightValueSet_eq_stateValueSet_strictLowAlpha
    [Nonempty a] {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQFixedWeightValueSet ρ σ α =
      sandwichedRenyiQFixedWeightStateValueSet ρ σ α := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨H, hH, rfl⟩
    let trH : ℝ := H.trace.re
    have htrH_pos : 0 < trH :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hH)).1
    let Hn : CMatrix a := (trH⁻¹ : ℝ) • H
    have hHn : Hn.PosDef := by
      simpa [Hn] using Matrix.PosDef.smul hH (inv_pos.mpr htrH_pos)
    have htrH_im : H.trace.im = 0 :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hH)).2.symm
    have hHntr : Hn.trace.re = 1 := by
      simp [Hn, trH, Matrix.trace_smul, Complex.mul_re, htrH_im,
        inv_mul_cancel₀ (ne_of_gt htrH_pos)]
    have hinv_pos : 0 < trH⁻¹ := inv_pos.mpr htrH_pos
    have hobj :
        frankLiebFixedWeightObjective ρ σ Hn α ((1 - α) / α) =
          frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) := by
      simpa [Hn, trH] using
        frankLiebFixedWeightObjective_real_smul_weight_strictLowAlpha
          (a := a) (ρ := ρ) (σ := σ) (H := H)
          hρ hσ hH hinv_pos hα_half hα_lt_one
    exact ⟨Hn, hHn, hHntr, hobj.symm⟩
  · intro hy
    rcases hy with ⟨H, hH, _hHtr, rfl⟩
    exact sandwichedRenyiQFixedWeightValueSet_mem hH α

/-- `sInf` form of the normalization bridge for fixed Frank--Lieb weights. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_stateValueSet_strictLowAlpha
    [Nonempty a] {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sInf (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) := by
  rw [sandwichedRenyiQFixedWeightValueSet_eq_stateValueSet_strictLowAlpha
    hρ hσ hα_half hα_lt_one]

/-- Common normalized-weight convex upper value for the fixed-weight
Frank--Lieb variational family. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_commonWeight_convexUpper_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef) (hHtr : H.trace.re = 1)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ y ∈ sandwichedRenyiQFixedWeightStateValueSet
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) α,
      t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
          (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤ y := by
  refine ⟨frankLiebFixedWeightObjective
      (cMatrixConvexCombination t ρ₁ ρ₂)
      (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α), ?_, ?_⟩
  · exact sandwichedRenyiQFixedWeightStateValueSet_mem
      (ρ := cMatrixConvexCombination t ρ₁ ρ₂)
      (σ := cMatrixConvexCombination t σ₁ σ₂)
      (H := H) hH hHtr α
  · exact frankLiebFixedWeightObjective_concave_strictLowAlpha
      (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hH hρ₁ hρ₂ hσ₁ hσ₂ hα_half hα_lt_one ht0 ht1

/-- Common-weight convex upper value for the fixed-weight Frank--Lieb
variational family.

For the same positive-definite weight `H`, the convex combination of the two
fixed-weight objective values is bounded by an actual member of the mixed
input value set.  This is the exact local form needed before passing from
fixed weights to the `sInf` variational formula for `sandwichedRenyiQ`. -/
theorem sandwichedRenyiQFixedWeightValueSet_commonWeight_convexUpper_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ y ∈ sandwichedRenyiQFixedWeightValueSet
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) α,
      t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
          (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤ y := by
  refine ⟨frankLiebFixedWeightObjective
      (cMatrixConvexCombination t ρ₁ ρ₂)
      (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α), ?_, ?_⟩
  · exact sandwichedRenyiQFixedWeightValueSet_mem
      (ρ := cMatrixConvexCombination t ρ₁ ρ₂)
      (σ := cMatrixConvexCombination t σ₁ σ₂)
      (H := H) hH α
  · exact frankLiebFixedWeightObjective_concave_strictLowAlpha
      (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hH hρ₁ hρ₂ hσ₁ hσ₂ hα_half hα_lt_one ht0 ht1

/-- Common-weight convex upper value for the source-shaped additive
Gour/Frank--Lieb variational family.

This is the direct Gour-route analogue of
`sandwichedRenyiQFixedWeightValueSet_commonWeight_convexUpper_strictLowAlpha`.
It uses the additive objective concavity rather than passing through the
multiplicative fixed-weight objective. -/
theorem sandwichedRenyiQAdditiveValueSet_commonWeight_convexUpper_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ y ∈ sandwichedRenyiQAdditiveValueSet
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) α,
      t * frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) +
          (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) ≤ y := by
  refine ⟨frankLiebAdditiveObjective
      (cMatrixConvexCombination t ρ₁ ρ₂)
      (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α), ?_, ?_⟩
  · exact sandwichedRenyiQAdditiveValueSet_mem
      (ρ := cMatrixConvexCombination t ρ₁ ρ₂)
      (σ := cMatrixConvexCombination t σ₁ σ₂)
      (H := H) hH α
  · exact frankLiebAdditiveObjective_concave
      (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hH hσ₁.posSemidef hσ₂.posSemidef
      (le_of_lt hα_lt_one)
      (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
      (sandwichedRenyiQ_frankLiebExponent_lt_one hα_half hα_lt_one)
      ht0 ht1

/-- Handoff from Gour's additive `sInf` variational formula to joint
concavity of the sandwiched `Q` functional.

This is the source-shaped version of the Frank--Lieb gap isolation: once the
additive Gour variational family is identified with `Q`, the already proved
additive fixed-weight concavity gives joint concavity of `Q`. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha_of_additive_sInf_eq
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQ₁ :
      sInf (sandwichedRenyiQAdditiveValueSet ρ₁ σ₁ α) =
        sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α)
    (hQ₂ :
      sInf (sandwichedRenyiQAdditiveValueSet ρ₂ σ₂ α) =
        sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α)
    (hQt :
      sInf (sandwichedRenyiQAdditiveValueSet
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂) α) =
        sandwichedRenyiQ
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂)
          (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
          (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
            ht0 ht1)
          α) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let Q₁ : ℝ := sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α
  let Q₂ : ℝ := sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α
  have hρt : ρt.PosSemidef := by
    simpa [ρt] using sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1
  have hσt_psd : σt.PosSemidef := by
    simpa [σt] using
      sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
        ht0 ht1
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hlower :
      t * Q₁ + (1 - t) * Q₂ ∈
        lowerBounds (sandwichedRenyiQAdditiveValueSet ρt σt α) := by
    intro y hy
    rcases hy with ⟨H, hH, rfl⟩
    have hQ₁_le :
        Q₁ ≤ frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) := by
      have hsInf_le :
          sInf (sandwichedRenyiQAdditiveValueSet ρ₁ σ₁ α) ≤
            frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) :=
        csInf_le
          (sandwichedRenyiQAdditiveValueSet_bddBelow
            hρ₁ hσ₁.posSemidef hα_nonneg hα_le_one)
          (sandwichedRenyiQAdditiveValueSet_mem hH α)
      simpa [Q₁, hQ₁] using hsInf_le
    have hQ₂_le :
        Q₂ ≤ frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) := by
      have hsInf_le :
          sInf (sandwichedRenyiQAdditiveValueSet ρ₂ σ₂ α) ≤
            frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) :=
        csInf_le
          (sandwichedRenyiQAdditiveValueSet_bddBelow
            hρ₂ hσ₂.posSemidef hα_nonneg hα_le_one)
          (sandwichedRenyiQAdditiveValueSet_mem hH α)
      simpa [Q₂, hQ₂] using hsInf_le
    have hlinear :
        t * Q₁ + (1 - t) * Q₂ ≤
          t * frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hQ₁_le ht0)
        (mul_le_mul_of_nonneg_left hQ₂_le (sub_nonneg.mpr ht1))
    have hconc :
        t * frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) ≤
          frankLiebAdditiveObjective ρt σt H α ((1 - α) / α) := by
      simpa [ρt, σt] using
        frankLiebAdditiveObjective_concave
          (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
          hH hσ₁.posSemidef hσ₂.posSemidef
          (le_of_lt hα_lt_one)
          (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
          (sandwichedRenyiQ_frankLiebExponent_lt_one hα_half hα_lt_one)
          ht0 ht1
    exact hlinear.trans hconc
  have hle_sInf :
      t * Q₁ + (1 - t) * Q₂ ≤
        sInf (sandwichedRenyiQAdditiveValueSet ρt σt α) :=
    le_csInf (sandwichedRenyiQAdditiveValueSet_nonempty ρt σt α) hlower
  have hQt' :
      sInf (sandwichedRenyiQAdditiveValueSet ρt σt α) =
        sandwichedRenyiQ ρt σt hρt hσt_psd α := by
    simpa [ρt, σt, hρt, hσt_psd] using hQt
  calc
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α =
        t * Q₁ + (1 - t) * Q₂ := rfl
    _ ≤ sInf (sandwichedRenyiQAdditiveValueSet ρt σt α) := hle_sInf
    _ = sandwichedRenyiQ ρt σt hρt hσt_psd α := hQt'
    _ = sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
          simp [ρt, σt]

/-- Handoff from the fixed-weight `sInf` variational formula to joint
concavity of the sandwiched `Q` functional.

This theorem isolates the remaining noncommutative Frank--Lieb variational
gap: once each `sandwichedRenyiQ` value is identified with the infimum over
fixed positive-definite weights, the already proved fixed-weight objective
concavity gives joint concavity of `Q`. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha_of_fixedWeight_sInf_eq
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQ₁ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₁ σ₁ α) =
        sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α)
    (hQ₂ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₂ σ₂ α) =
        sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α)
    (hQt :
      sInf (sandwichedRenyiQFixedWeightValueSet
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂) α) =
        sandwichedRenyiQ
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂)
          (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
          (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
            ht0 ht1)
          α) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let Q₁ : ℝ := sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α
  let Q₂ : ℝ := sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α
  have hρt : ρt.PosSemidef := by
    simpa [ρt] using sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1
  have hσt_psd : σt.PosSemidef := by
    simpa [σt] using
      sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
        ht0 ht1
  have hlower :
      t * Q₁ + (1 - t) * Q₂ ∈
        lowerBounds (sandwichedRenyiQFixedWeightValueSet ρt σt α) := by
    intro y hy
    rcases hy with ⟨H, hH, rfl⟩
    have hQ₁_le :
        Q₁ ≤ frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) := by
      simpa [Q₁, hQ₁] using
        sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
          hρ₁ hσ₁.posSemidef hH α
    have hQ₂_le :
        Q₂ ≤ frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) := by
      simpa [Q₂, hQ₂] using
        sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
          hρ₂ hσ₂.posSemidef hH α
    have hlinear :
        t * Q₁ + (1 - t) * Q₂ ≤
          t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hQ₁_le ht0)
        (mul_le_mul_of_nonneg_left hQ₂_le (sub_nonneg.mpr ht1))
    have hconc :
        t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤
          frankLiebFixedWeightObjective ρt σt H α ((1 - α) / α) := by
      simpa [ρt, σt] using
        frankLiebFixedWeightObjective_concave_strictLowAlpha
          (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
          hH hρ₁ hρ₂ hσ₁ hσ₂ hα_half hα_lt_one ht0 ht1
    exact hlinear.trans hconc
  have hle_sInf :
      t * Q₁ + (1 - t) * Q₂ ≤
        sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) :=
    le_csInf (sandwichedRenyiQFixedWeightValueSet_nonempty ρt σt α) hlower
  have hQt' :
      sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) =
        sandwichedRenyiQ ρt σt hρt hσt_psd α := by
    simpa [ρt, σt, hρt, hσt_psd] using hQt
  calc
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α =
        t * Q₁ + (1 - t) * Q₂ := rfl
    _ ≤ sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) := hle_sInf
    _ = sandwichedRenyiQ ρt σt hρt hσt_psd α := hQt'
    _ = sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
          simp [ρt, σt]

/-- Positive-definite Frank--Lieb low-`α` joint concavity for the
PSD-friendly sandwiched Rényi `Q` functional.

This is the full-rank specialization of Frank--Lieb Proposition 3 needed for
the `α < 1` branch: it combines the Gour/Young variational formula with the
already proved fixed-weight Frank--Lieb objective concavity. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha_posDef
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosDef) (hρ₂ : ρ₂.PosDef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁.posSemidef hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂.posSemidef hσ₂.posSemidef α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁.posSemidef hρ₂.posSemidef
          ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hρt : ρt.PosDef := by
    simpa [ρt] using cMatrixConvexCombination_posDef hρ₁ hρ₂ ht0 ht1
  have hσt : σt.PosDef := by
    simpa [σt] using cMatrixConvexCombination_posDef hσ₁ hσ₂ ht0 ht1
  have hQ₁ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₁ σ₁ α) =
        sandwichedRenyiQ ρ₁ σ₁ hρ₁.posSemidef hσ₁.posSemidef α :=
    sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρ₁ hσ₁ hα_half hα_lt_one
  have hQ₂ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₂ σ₂ α) =
        sandwichedRenyiQ ρ₂ σ₂ hρ₂.posSemidef hσ₂.posSemidef α :=
    sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρ₂ hσ₂ hα_half hα_lt_one
  have hQt :
      sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) =
        sandwichedRenyiQ ρt σt hρt.posSemidef hσt.posSemidef α :=
    sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρt hσt hα_half hα_lt_one
  simpa [ρt, σt] using
    sandwichedRenyiQ_jointConcave_lowAlpha_of_fixedWeight_sInf_eq
      (a := a) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hρ₁.posSemidef hρ₂.posSemidef hσ₁ hσ₂
      hα_half hα_lt_one ht0 ht1 hQ₁ hQ₂ hQt

/-- Frank--Lieb low-`α` joint concavity for the PSD-friendly sandwiched Rényi
`Q` functional on unrestricted PSD inputs.

This is the PSD closure of `sandwichedRenyiQ_jointConcave_lowAlpha_posDef`,
obtained by identity regularization and continuity of the positive matrix
powers appearing in Gour's `Q_α` expression. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁ α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂ α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁ hσ₂ ht0 ht1)
        α := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let ρ₁ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization ρ₁ ε
  let ρ₂ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization ρ₂ ε
  let σ₁ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization σ₁ ε
  let σ₂ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization σ₂ ε
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let ρtε : ℝ → CMatrix a :=
    fun ε => cMatrixConvexCombination t (ρ₁ε ε) (ρ₂ε ε)
  let σtε : ℝ → CMatrix a :=
    fun ε => cMatrixConvexCombination t (σ₁ε ε) (σ₂ε ε)
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos (by norm_num) hα_pos)
  have hρ₁ε_psd : ∀ ε, (ρ₁ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hρ₁ ε
  have hρ₂ε_psd : ∀ ε, (ρ₂ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hρ₂ ε
  have hσ₁ε_psd : ∀ ε, (σ₁ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hσ₁ ε
  have hσ₂ε_psd : ∀ ε, (σ₂ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hσ₂ ε
  have hρt_psd : ρt.PosSemidef := by
    simpa [ρt] using sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1
  have hσt_psd : σt.PosSemidef := by
    simpa [σt] using sandwichedRenyiQ_sigma_mix_posSemidef hσ₁ hσ₂ ht0 ht1
  have hρtε_psd : ∀ ε, (ρtε ε).PosSemidef := by
    intro ε
    exact cMatrixConvexCombination_posSemidef
      (hρ₁ε_psd ε) (hρ₂ε_psd ε) ht0 ht1
  have hσtε_psd : ∀ ε, (σtε ε).PosSemidef := by
    intro ε
    exact cMatrixConvexCombination_posSemidef
      (hσ₁ε_psd ε) (hσ₂ε_psd ε) ht0 ht1
  have hρ₁ε_tend : Filter.Tendsto ρ₁ε l (nhds ρ₁) := by
    simpa [ρ₁ε, l] using cMatrixPSDRegularization_tendsto_zero ρ₁
  have hρ₂ε_tend : Filter.Tendsto ρ₂ε l (nhds ρ₂) := by
    simpa [ρ₂ε, l] using cMatrixPSDRegularization_tendsto_zero ρ₂
  have hσ₁ε_tend : Filter.Tendsto σ₁ε l (nhds σ₁) := by
    simpa [σ₁ε, l] using cMatrixPSDRegularization_tendsto_zero σ₁
  have hσ₂ε_tend : Filter.Tendsto σ₂ε l (nhds σ₂) := by
    simpa [σ₂ε, l] using cMatrixPSDRegularization_tendsto_zero σ₂
  have hρtε_tend : Filter.Tendsto ρtε l (nhds ρt) := by
    have htend :
        Filter.Tendsto
          (fun ε => ((t : ℂ) • ρ₁ε ε) +
            (((1 - t : ℝ) : ℂ) • ρ₂ε ε))
          l
          (nhds (((t : ℂ) • ρ₁) + (((1 - t : ℝ) : ℂ) • ρ₂))) :=
      (hρ₁ε_tend.const_smul (t : ℂ)).add
        (hρ₂ε_tend.const_smul (((1 - t : ℝ) : ℂ)))
    simpa [ρtε, ρt, cMatrixConvexCombination] using htend
  have hσtε_tend : Filter.Tendsto σtε l (nhds σt) := by
    have htend :
        Filter.Tendsto
          (fun ε => ((t : ℂ) • σ₁ε ε) +
            (((1 - t : ℝ) : ℂ) • σ₂ε ε))
          l
          (nhds (((t : ℂ) • σ₁) + (((1 - t : ℝ) : ℂ) • σ₂))) :=
      (hσ₁ε_tend.const_smul (t : ℂ)).add
        (hσ₂ε_tend.const_smul (((1 - t : ℝ) : ℂ)))
    simpa [σtε, σt, cMatrixConvexCombination] using htend
  have hQ₁_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (ρ₁ε ε) (σ₁ε ε)
          (hρ₁ε_psd ε) (hσ₁ε_psd ε) α)
        l (nhds (sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁ α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos hρ₁ε_tend hσ₁ε_tend
      hρ₁ε_psd hσ₁ε_psd hρ₁ hσ₁
  have hQ₂_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (ρ₂ε ε) (σ₂ε ε)
          (hρ₂ε_psd ε) (hσ₂ε_psd ε) α)
        l (nhds (sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂ α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos hρ₂ε_tend hσ₂ε_tend
      hρ₂ε_psd hσ₂ε_psd hρ₂ hσ₂
  have hQt_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (ρtε ε) (σtε ε)
          (hρtε_psd ε) (hσtε_psd ε) α)
        l (nhds (sandwichedRenyiQ ρt σt hρt_psd hσt_psd α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos hρtε_tend hσtε_tend
      hρtε_psd hσtε_psd hρt_psd hσt_psd
  have hleft :
      Filter.Tendsto
        (fun ε =>
          t * sandwichedRenyiQ (ρ₁ε ε) (σ₁ε ε)
              (hρ₁ε_psd ε) (hσ₁ε_psd ε) α +
            (1 - t) * sandwichedRenyiQ (ρ₂ε ε) (σ₂ε ε)
              (hρ₂ε_psd ε) (hσ₂ε_psd ε) α)
        l
        (nhds
          (t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁ α +
            (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂ α)) :=
    (hQ₁_tend.const_mul t).add (hQ₂_tend.const_mul (1 - t))
  have hineq_eventual :
      (fun ε =>
          t * sandwichedRenyiQ (ρ₁ε ε) (σ₁ε ε)
              (hρ₁ε_psd ε) (hσ₁ε_psd ε) α +
            (1 - t) * sandwichedRenyiQ (ρ₂ε ε) (σ₂ε ε)
              (hρ₂ε_psd ε) (hσ₂ε_psd ε) α)
        ≤ᶠ[l]
      (fun ε => sandwichedRenyiQ (ρtε ε) (σtε ε)
          (hρtε_psd ε) (hσtε_psd ε) α) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hρ₁ε_pd : (ρ₁ε ε).PosDef := by
      simpa [ρ₁ε] using cMatrixPSDRegularization_posDef_of_pos hρ₁ hε
    have hρ₂ε_pd : (ρ₂ε ε).PosDef := by
      simpa [ρ₂ε] using cMatrixPSDRegularization_posDef_of_pos hρ₂ hε
    have hσ₁ε_pd : (σ₁ε ε).PosDef := by
      simpa [σ₁ε] using cMatrixPSDRegularization_posDef_of_pos hσ₁ hε
    have hσ₂ε_pd : (σ₂ε ε).PosDef := by
      simpa [σ₂ε] using cMatrixPSDRegularization_posDef_of_pos hσ₂ hε
    simpa [ρtε, σtε] using
      sandwichedRenyiQ_jointConcave_lowAlpha_posDef
        (a := a) (ρ₁ := ρ₁ε ε) (ρ₂ := ρ₂ε ε)
        (σ₁ := σ₁ε ε) (σ₂ := σ₂ε ε)
        hρ₁ε_pd hρ₂ε_pd hσ₁ε_pd hσ₂ε_pd
        hα_half hα_lt_one ht0 ht1
  have hlimit := le_of_tendsto_of_tendsto hleft hQt_tend hineq_eventual
  simpa [ρt, σt] using hlimit

/-- Package the PSD witnesses for `sandwichedRenyiQ` into a pair-valued
function.  The `if` keeps the function total on the ambient matrix product
space so that Mathlib's `ConcaveOn.le_map_sum` can be reused for finite
twirling averages. -/
noncomputable def sandwichedRenyiQPair (α : ℝ)
    (p : CMatrix a × CMatrix a) : ℝ := by
  classical
  exact
    if hp : p.1.PosSemidef ∧ p.2.PosSemidef then
      sandwichedRenyiQ p.1 p.2 hp.1 hp.2 α
    else
      0

theorem sandwichedRenyiQPair_eq {ρ σ : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    sandwichedRenyiQPair (a := a) α (ρ, σ) =
      sandwichedRenyiQ ρ σ hρ hσ α := by
  classical
  simp [sandwichedRenyiQPair, hρ, hσ]

/-- Congruence for the PSD-friendly `Q` functional under equality of its two
matrix arguments.  This small helper keeps dependent PSD witnesses out of
larger rewrites such as finite twirling identities. -/
theorem sandwichedRenyiQ_congr
    {ρ ρ' σ σ' : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρ' : ρ'.PosSemidef) (hσ' : σ'.PosSemidef)
    (hρeq : ρ = ρ') (hσeq : σ = σ') (α : ℝ) :
    sandwichedRenyiQ ρ σ hρ hσ α =
      sandwichedRenyiQ ρ' σ' hρ' hσ' α := by
  subst ρ'
  subst σ'
  rfl

/-- The PSD domain for the pair-valued `Q` functional. -/
def sandwichedRenyiQPSDDomain : Set (CMatrix a × CMatrix a) :=
  {p | p.1.PosSemidef ∧ p.2.PosSemidef}

omit [Fintype a] [DecidableEq a] in
theorem sandwichedRenyiQPSDDomain_convex :
    Convex ℝ (sandwichedRenyiQPSDDomain (a := a)) := by
  intro x hx y hy s t hs ht hst
  constructor
  · have hρ :
        (s • x.1 + t • y.1 : CMatrix a).PosSemidef :=
      Matrix.PosSemidef.add
        (Matrix.PosSemidef.smul hx.1 hs)
        (Matrix.PosSemidef.smul hy.1 ht)
    simpa [sandwichedRenyiQPSDDomain] using hρ
  · have hσ :
        (s • x.2 + t • y.2 : CMatrix a).PosSemidef :=
      Matrix.PosSemidef.add
        (Matrix.PosSemidef.smul hx.2 hs)
        (Matrix.PosSemidef.smul hy.2 ht)
    simpa [sandwichedRenyiQPSDDomain] using hσ

/-- Frank--Lieb joint concavity as a `ConcaveOn` theorem on the PSD pair cone.

This is a Mathlib-facing wrapper around the source-shaped binary theorem
`sandwichedRenyiQ_jointConcave_lowAlpha`; it is used only to derive finite
average Jensen inequalities for local-unitary twirling. -/
theorem sandwichedRenyiQPair_concaveOn_lowAlpha
    [Nonempty a] {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    ConcaveOn ℝ (sandwichedRenyiQPSDDomain (a := a))
      (sandwichedRenyiQPair (a := a) α) := by
  refine ⟨sandwichedRenyiQPSDDomain_convex (a := a), ?_⟩
  intro x hx y hy s t hs ht hst
  have ht_eq : t = 1 - s := by linarith
  subst t
  have hs_le : s ≤ 1 := by linarith
  have hmixρ :
      (s • x.1 + (1 - s) • y.1 : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx.1 hs)
      (Matrix.PosSemidef.smul hy.1 (sub_nonneg.mpr hs_le))
  have hmixσ :
      (s • x.2 + (1 - s) • y.2 : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx.2 hs)
      (Matrix.PosSemidef.smul hy.2 (sub_nonneg.mpr hs_le))
  have hconc :=
    sandwichedRenyiQ_jointConcave_lowAlpha
      (a := a) (ρ₁ := x.1) (ρ₂ := y.1) (σ₁ := x.2) (σ₂ := y.2)
      hx.1 hy.1 hx.2 hy.2 hα_half hα_lt_one hs hs_le
  simpa [sandwichedRenyiQPair, sandwichedRenyiQPSDDomain, hx.1, hx.2,
    hy.1, hy.2, hmixρ, hmixσ, cMatrixConvexCombination_eq_real_smul,
    smul_eq_mul, Complex.real_smul, add_comm, add_left_comm, add_assoc] using hconc

omit [Fintype a] [DecidableEq a] in
theorem cMatrix_finset_weightedSum_posSemidef
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (A : ι → CMatrix a)
    (hA : ∀ i ∈ s, (A i).PosSemidef)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, (w i : ℂ) • A i).PosSemidef := by
  classical
  revert hA hw_nonneg
  refine Finset.induction_on s ?_ ?_
  · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix a).PosSemidef)
  · intro i s his hsind hA hw_nonneg
    rw [Finset.sum_insert his]
    have hwi : (0 : ℂ) ≤ (w i : ℂ) := by
      exact_mod_cast hw_nonneg i (Finset.mem_insert_self i s)
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul (hA i (Finset.mem_insert_self i s))
        hwi)
      (hsind
        (fun j hj => hA j (Finset.mem_insert_of_mem hj))
        (fun j hj => hw_nonneg j (Finset.mem_insert_of_mem hj)))

omit [Fintype a] [DecidableEq a] in
theorem finset_weightedPair_sum_fst
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρ σ : ι → CMatrix a) :
    (∑ i ∈ s, w i • ((ρ i, σ i) : CMatrix a × CMatrix a)).1 =
      ∑ i ∈ s, (w i : ℂ) • ρ i := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      rw [Prod.fst_add, Prod.smul_fst, ih]
      change w i • ρ i + (∑ x ∈ s, (w x : ℂ) • ρ x) =
        (w i : ℂ) • ρ i + ∑ x ∈ s, (w x : ℂ) • ρ x
      simp

omit [Fintype a] [DecidableEq a] in
theorem finset_weightedPair_sum_snd
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρ σ : ι → CMatrix a) :
    (∑ i ∈ s, w i • ((ρ i, σ i) : CMatrix a × CMatrix a)).2 =
      ∑ i ∈ s, (w i : ℂ) • σ i := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      rw [Prod.snd_add, Prod.smul_snd, ih]
      change w i • σ i + (∑ x ∈ s, (w x : ℂ) • σ x) =
        (w i : ℂ) • σ i + ∑ x ∈ s, (w x : ℂ) • σ x
      simp

/-- Finite Jensen inequality for the low-`α` `Q` functional on PSD matrix
pairs.  This is the exact finite-average bridge needed before applying local
unitary twirling; the proof is just `ConcaveOn.le_map_sum` applied to the
Gour/Frank--Lieb joint concavity theorem. -/
theorem sandwichedRenyiQ_finset_weightedAverage_ge_average_lowAlpha
    [Nonempty a] {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρ σ : ι → CMatrix a)
    (hρ : ∀ i ∈ s, (ρ i).PosSemidef)
    (hσ : ∀ i ∈ s, (σ i).PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i *
        sandwichedRenyiQPair (a := a) α (ρ i, σ i) ≤
      sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) • ρ i)
        (∑ i ∈ s, (w i : ℂ) • σ i)
        (cMatrix_finset_weightedSum_posSemidef s w ρ hρ hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w σ hσ hw_nonneg)
        α := by
  classical
  let p : ι → CMatrix a × CMatrix a := fun i => (ρ i, σ i)
  have hmem : ∀ i ∈ s, p i ∈ sandwichedRenyiQPSDDomain (a := a) := by
    intro i hi
    exact ⟨hρ i hi, hσ i hi⟩
  have hjensen :=
    (sandwichedRenyiQPair_concaveOn_lowAlpha
      (a := a) hα_half hα_lt_one).le_map_sum
      (t := s) (w := w) (p := p) hw_nonneg hw_sum hmem
  have hsum_fst :
      (∑ i ∈ s, w i • p i).1 = ∑ i ∈ s, (w i : ℂ) • ρ i := by
    simpa [p] using finset_weightedPair_sum_fst (a := a) s w ρ σ
  have hsum_snd :
      (∑ i ∈ s, w i • p i).2 = ∑ i ∈ s, (w i : ℂ) • σ i := by
    simpa [p] using finset_weightedPair_sum_snd (a := a) s w ρ σ
  have hsum_mem :
      (∑ i ∈ s, w i • p i) ∈ sandwichedRenyiQPSDDomain (a := a) := by
    constructor
    · rw [hsum_fst]
      exact
        cMatrix_finset_weightedSum_posSemidef s w ρ hρ hw_nonneg
    · rw [hsum_snd]
      exact
        cMatrix_finset_weightedSum_posSemidef s w σ hσ hw_nonneg
  have hright :
      sandwichedRenyiQPair (a := a) α (∑ i ∈ s, w i • p i) =
        sandwichedRenyiQ
          (∑ i ∈ s, (w i : ℂ) • ρ i)
          (∑ i ∈ s, (w i : ℂ) • σ i)
          (cMatrix_finset_weightedSum_posSemidef s w ρ hρ hw_nonneg)
          (cMatrix_finset_weightedSum_posSemidef s w σ hσ hw_nonneg)
          α := by
    rw [sandwichedRenyiQPair_eq hsum_mem.1 hsum_mem.2]
    unfold sandwichedRenyiQ
    rw [hsum_fst, hsum_snd]
  simpa [p, hright, smul_eq_mul]
    using (by simpa [hright, smul_eq_mul] using hjensen)

/-- Finite local-right-unitary averaging lower bound for the low-`α`
`Q` functional.

This is the Frank--Lieb/Jensen part of the local twirling route.  It does not
use partial trace monotonicity: after applying finite Jensen, every summand is
identified with the original `Q(ρ,σ)` by local-right-unitary invariance. -/
theorem sandwichedRenyiQ_localRightUnitary_weightedAverage_ge
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a] [Nonempty b]
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (U : ι → Matrix.unitaryGroup b ℂ)
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    sandwichedRenyiQ ρ σ hρ hσ α ≤
      sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i _
            simpa using
              posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i _
            simpa using
              posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        α := by
  classical
  let ρU : ι → CMatrix (Prod a b) := fun i =>
    (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
      star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))
  let σU : ι → CMatrix (Prod a b) := fun i =>
    (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
      star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))
  have hρU : ∀ i ∈ s, (ρU i).PosSemidef := by
    intro i hi
    simpa [ρU] using
      posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹
  have hσU : ∀ i ∈ s, (σU i).PosSemidef := by
    intro i hi
    simpa [σU] using
      posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹
  have hα_pos : 0 < α := by linarith
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hs_nonneg : 0 ≤ (1 - α) / (2 * α) := by
    have hnum : 0 ≤ 1 - α := le_of_lt (sub_pos.mpr hα_lt_one)
    have hden : 0 ≤ 2 * α := by positivity
    exact div_nonneg hnum hden
  have hterm :
      ∀ i ∈ s,
        sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
          sandwichedRenyiQ ρ σ hρ hσ α := by
    intro i hi
    calc
      sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
          sandwichedRenyiQ (ρU i) (σU i) (hρU i hi) (hσU i hi) α := by
            rw [sandwichedRenyiQPair_eq]
      _ = sandwichedRenyiQ ρ σ hρ hσ α := by
            simpa [ρU, σU] using
              sandwichedRenyiQ_localRightUnitary_conj hρ hσ (U i) α
                hs_nonneg hα_nonneg
  have havg :
      ∑ i ∈ s, w i * sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
        sandwichedRenyiQ ρ σ hρ hσ α := by
    calc
      ∑ i ∈ s, w i * sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
          (∑ i ∈ s, w i) * sandwichedRenyiQ ρ σ hρ hσ α := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (by
              intro i hi
              rw [hterm i hi])
      _ = sandwichedRenyiQ ρ σ hρ hσ α := by
            rw [hw_sum, one_mul]
  have hjensen :=
    sandwichedRenyiQ_finset_weightedAverage_ge_average_lowAlpha
      (a := Prod a b) s w ρU σU hρU hσU hα_half hα_lt_one
      hw_nonneg hw_sum
  calc
    sandwichedRenyiQ ρ σ hρ hσ α =
        ∑ i ∈ s, w i * sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) := havg.symm
    _ ≤ sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) • ρU i)
        (∑ i ∈ s, (w i : ℂ) • σU i)
        (cMatrix_finset_weightedSum_posSemidef s w ρU hρU hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w σU hσU hw_nonneg)
        α := hjensen
    _ = sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        α := by
          simp [ρU, σU]

/-- If a finite local-right-unitary ensemble realizes the partial-trace
depolarizing twirl, then Frank--Lieb joint concavity gives the low-`α`
partial-trace monotonicity for the PSD-friendly `Q` functional.

This theorem isolates the remaining finite-design input in the Gour/Frank--Lieb
route.  The hypotheses `hTwirlρ` and `hTwirlσ` are exactly the local twirling
identity
`Twirl_B(X) = Tr_B(X) ⊗ π_B`; no DPI or partial-trace monotonicity is assumed. -/
theorem sandwichedRenyiQ_marginalA_ge_of_localRightUnitary_twirling
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a] [Nonempty b]
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (U : ι → Matrix.unitaryGroup b ℂ)
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hTwirlρ :
      (∑ i ∈ s, (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix)
    (hTwirlσ :
      (∑ i ∈ s, (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix) :
    sandwichedRenyiQ ρ σ hρ hσ α ≤
      sandwichedRenyiQ
        (partialTraceB ρ) (partialTraceB σ)
        (partialTraceB_posSemidef hρ)
        (partialTraceB_posSemidef hσ)
        α := by
  classical
  have htwirl :=
    sandwichedRenyiQ_localRightUnitary_weightedAverage_ge
      (a := a) (b := b) s w U hρ hσ hα_half hα_lt_one
      hw_nonneg hw_sum
  have hsum_tensor :
      sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        α =
      sandwichedRenyiQ
        (Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix)
        (Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix)
        ((partialTraceB_posSemidef hρ).kronecker (maximallyMixed b).pos)
        ((partialTraceB_posSemidef hσ).kronecker (maximallyMixed b).pos)
        α :=
    sandwichedRenyiQ_congr
      (cMatrix_finset_weightedSum_posSemidef s w
        (fun i =>
          (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
        (by
          intro i hi
          simpa using
            posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
        hw_nonneg)
      (cMatrix_finset_weightedSum_posSemidef s w
        (fun i =>
          (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
        (by
          intro i hi
          simpa using
            posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
        hw_nonneg)
      ((partialTraceB_posSemidef hρ).kronecker (maximallyMixed b).pos)
      ((partialTraceB_posSemidef hσ).kronecker (maximallyMixed b).pos)
      hTwirlρ hTwirlσ α
  have htensor :
      sandwichedRenyiQ
        (Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix)
        (Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix)
        ((partialTraceB_posSemidef hρ).kronecker (maximallyMixed b).pos)
        ((partialTraceB_posSemidef hσ).kronecker (maximallyMixed b).pos)
        α =
      sandwichedRenyiQ
        (partialTraceB ρ) (partialTraceB σ)
        (partialTraceB_posSemidef hρ)
        (partialTraceB_posSemidef hσ)
        α :=
    sandwichedRenyiQ_kronecker_maximallyMixed_right
      (partialTraceB_posSemidef hρ) (partialTraceB_posSemidef hσ)
      α hα_half hα_lt_one
  exact htwirl.trans_eq (hsum_tensor.trans htensor)

/-- The real signs used for the finite diagonal-sign twirl. -/
def boolSignComplex (x : Bool) : ℂ :=
  if x then -1 else 1

@[simp] theorem boolSignComplex_false : boolSignComplex false = 1 := rfl

@[simp] theorem boolSignComplex_true : boolSignComplex true = -1 := rfl

@[simp] theorem boolSignComplex_not (x : Bool) :
    boolSignComplex (!x) = - boolSignComplex x := by
  cases x <;> simp [boolSignComplex]

@[simp] theorem boolSignComplex_star (x : Bool) :
    star (boolSignComplex x) = boolSignComplex x := by
  cases x <;> simp [boolSignComplex]

@[simp] theorem boolSignComplex_sq (x : Bool) :
    boolSignComplex x * boolSignComplex x = 1 := by
  cases x <;> simp [boolSignComplex]

/-- Diagonal `±1` unitary used to dephase the right tensor factor. -/
def diagonalSignUnitary {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) : Matrix.unitaryGroup b ℂ :=
  ⟨Matrix.diagonal fun j => boolSignComplex (ε j), by
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      ext j j'
      by_cases h : j = j'
      · subst j'
        simp
      · simp [h]
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      ext j j'
      by_cases h : j = j'
      · subst j'
        simp
      · simp [h]⟩

@[simp] theorem diagonalSignUnitary_coe {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) :
    (diagonalSignUnitary ε : CMatrix b) =
      Matrix.diagonal fun j => boolSignComplex (ε j) := rfl

theorem diagonalSignUnitary_conj_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    (((localRightUnitary (a := a) (diagonalSignUnitary ε) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
      boolSignComplex (ε j) * X (i, j) (i', j') * boolSignComplex (ε j') := by
  simp only [localRightUnitary_coe, diagonalSignUnitary_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal,
    Matrix.of_apply, Matrix.conjTranspose_apply]
  have hinner : ∀ x : Prod a b,
      (∑ y : Prod a b,
        (((if i = y.1 then 1 else 0) *
            if j = y.2 then boolSignComplex (ε j) else 0) * X y x)) =
        boolSignComplex (ε j) * X (i, j) x := by
    intro x
    refine (Finset.sum_eq_single (i, j) ?_ ?_).trans ?_
    · intro y _ hy
      rcases y with ⟨y₁, y₂⟩
      by_cases hjy : j = y₂
      · by_cases hiy : i = y₁
        · exfalso
          apply hy
          exact Prod.ext hiy.symm hjy.symm
        · simp [hjy, hiy]
      · simp [hjy]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
    · simp
  simp_rw [hinner]
  refine (Finset.sum_eq_single (i', j') ?_ ?_).trans ?_
  · intro x _ hx
    rcases x with ⟨x₁, x₂⟩
    by_cases hjx : j' = x₂
    · by_cases hix : i' = x₁
      · exfalso
        apply hx
        exact Prod.ext hix.symm hjx.symm
      · have hix' : x₁ ≠ i' := fun h => hix h.symm
        simp [hjx, hix']
    · simp [hjx]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
  · simp [mul_assoc]

/-- Flipping one Boolean coordinate negates the corresponding sign. -/
def flipBoolCoordinate {b : Type v} [DecidableEq b] (j : b) :
    (b → Bool) ≃ (b → Bool) where
  toFun ε := Function.update ε j (!(ε j))
  invFun ε := Function.update ε j (!(ε j))
  left_inv ε := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Function.update, hk]
  right_inv ε := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Function.update, hk]

@[simp] theorem flipBoolCoordinate_self {b : Type v} [DecidableEq b]
    (j : b) (ε : b → Bool) :
    flipBoolCoordinate j ε j = !(ε j) := by
  simp [flipBoolCoordinate]

@[simp] theorem flipBoolCoordinate_ne {b : Type v} [DecidableEq b]
    {j k : b} (hjk : k ≠ j) (ε : b → Bool) :
    flipBoolCoordinate j ε k = ε k := by
  simp [flipBoolCoordinate, Function.update, hjk]

theorem boolSignComplex_sum_mul_eq_zero_of_ne
    {b : Type v} [Fintype b] [DecidableEq b] {j j' : b} (hjj' : j ≠ j') :
    (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j')) = 0 := by
  classical
  let S : ℂ := ∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j')
  have hsum :
      S = -S := by
    calc
      S = ∑ ε : b → Bool,
          boolSignComplex ((flipBoolCoordinate j) ε j) *
            boolSignComplex ((flipBoolCoordinate j) ε j') := by
        dsimp [S]
        exact (Equiv.sum_comp (flipBoolCoordinate j)
          (fun ε : b → Bool => boolSignComplex (ε j) * boolSignComplex (ε j'))).symm
      _ = ∑ ε : b → Bool,
          -(boolSignComplex (ε j) * boolSignComplex (ε j')) := by
        refine Finset.sum_congr rfl ?_
        intro ε _
        have hj' : j' ≠ j := fun h => hjj' h.symm
        simp [hj']
      _ = -S := by
        simp [S, Finset.sum_neg_distrib]
  have htwo : (2 : ℂ) * S = 0 := by
    have hSS : S + S = 0 := by
      exact add_eq_zero_iff_eq_neg.mpr hsum
    calc
      (2 : ℂ) * S = S + S := by ring
      _ = 0 := hSS
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_eq_zero.mp htwo |>.resolve_left htwo_ne

theorem boolSignComplex_sum_mul_eq_card
    {b : Type v} [Fintype b] [DecidableEq b] (j : b) :
    (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j)) =
      (Fintype.card (b → Bool) : ℂ) := by
  simp

/-- The finite diagonal-sign twirl on the right tensor factor.  It removes the
off-diagonal blocks in the right subsystem. -/
def localRightSignTwirl {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) : CMatrix (Prod a b) :=
  ((Fintype.card (b → Bool) : ℂ)⁻¹) •
    ∑ ε : b → Bool,
      (localRightUnitary (a := a) (diagonalSignUnitary ε) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod a b))

theorem localRightSignTwirl_apply {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    localRightSignTwirl X (i, j) (i', j') =
      if j = j' then X (i, j) (i', j') else 0 := by
  classical
  have hcard : ((Fintype.card (b → Bool) : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (b → Bool) ≠ 0)
  by_cases hjj' : j = j'
  · subst j'
    unfold localRightSignTwirl
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    simp_rw [diagonalSignUnitary_conj_apply]
    have hsumdiag :
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j) * boolSignComplex (ε j)) =
            (Fintype.card (b → Bool) : ℂ) * X (i, j) (i', j) := by
      calc
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j) * boolSignComplex (ε j)) =
            (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j)) *
              X (i, j) (i', j) := by
          simp [mul_left_comm, mul_comm]
        _ = (Fintype.card (b → Bool) : ℂ) * X (i, j) (i', j) := by
          rw [boolSignComplex_sum_mul_eq_card]
    rw [hsumdiag]
    change ((Fintype.card (b → Bool) : ℂ)⁻¹ *
        ((Fintype.card (b → Bool) : ℂ) * X (i, j) (i', j))) =
      X (i, j) (i', j)
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  · have hzero :
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j') * boolSignComplex (ε j')) = 0 := by
      calc
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j') * boolSignComplex (ε j')) =
            X (i, j) (i', j') *
              (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j')) := by
          simp [Finset.mul_sum, mul_assoc, mul_comm]
        _ = 0 := by
          rw [boolSignComplex_sum_mul_eq_zero_of_ne hjj', mul_zero]
    unfold localRightSignTwirl
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    simp_rw [diagonalSignUnitary_conj_apply]
    simp [hjj', hzero]

/-- Permutation unitary for a finite basis permutation.  The convention is
`U e_k = e_{π k}`. -/
def permutationUnitary {b : Type v} [Fintype b] [DecidableEq b]
    (π : Equiv.Perm b) : Matrix.unitaryGroup b ℂ :=
  ⟨fun j k => if π j = k then 1 else 0, by
    constructor
    · ext j j'
      simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply]
      by_cases hjj' : j = j'
      · subst j'
        refine (Finset.sum_eq_single (π.symm j) ?_ ?_).trans ?_
        · intro k _ hk
          by_cases hkj : k = π.symm j
          · exact False.elim (hk hkj)
          · have hne : π k ≠ j := by
              intro h
              apply hkj
              simpa using congrArg π.symm h
            simp [hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
        · simp
      · rw [if_neg hjj']
        refine Finset.sum_eq_zero ?_
        intro k _
        by_cases hkj : k = π.symm j
        · subst k
          simp [hjj']
        · have hne : π k ≠ j := by
            intro h
            apply hkj
            simpa using congrArg π.symm h
          simp [hne]
    · ext j j'
      simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply]
      by_cases hjj' : j = j'
      · subst j'
        refine (Finset.sum_eq_single (π j) ?_ ?_).trans ?_
        · intro k _ hk
          by_cases hkj : k = π j
          · exact False.elim (hk hkj)
          · have hne : π j ≠ k := fun h => hkj h.symm
            simp [hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
        · simp
      · rw [if_neg hjj']
        refine Finset.sum_eq_zero ?_
        intro k _
        by_cases hkj : k = π j
        · subst k
          have hne : ¬π j' = π j := fun h => hjj' (π.injective h.symm)
          simp [hne]
        · have hne : π j ≠ k := fun h => hkj h.symm
          simp [hne]⟩

@[simp] theorem permutationUnitary_coe {b : Type v} [Fintype b] [DecidableEq b]
    (π : Equiv.Perm b) :
    (permutationUnitary π : CMatrix b) = fun j k => if π j = k then 1 else 0 := rfl

theorem permutationUnitary_conj_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (π : Equiv.Perm b) (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    (((localRightUnitary (a := a) (permutationUnitary π) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
      X (i, π j) (i', π j') := by
  simp only [localRightUnitary_coe, permutationUnitary_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply]
  have hinner : ∀ x : Prod a b,
      (∑ y : Prod a b,
        (((if i = y.1 then 1 else 0) * if π j = y.2 then 1 else 0) * X y x)) =
        X (i, π j) x := by
    intro x
    refine (Finset.sum_eq_single (i, π j) ?_ ?_).trans ?_
    · intro y _ hy
      rcases y with ⟨y₁, y₂⟩
      by_cases hiy : i = y₁
      · by_cases hjy : π j = y₂
        · exfalso
          apply hy
          exact Prod.ext hiy.symm hjy.symm
        · simp [hiy, hjy]
      · simp [hiy]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
    · simp
  simp_rw [hinner]
  refine (Finset.sum_eq_single (i', π j') ?_ ?_).trans ?_
  · intro x _ hx
    rcases x with ⟨x₁, x₂⟩
    by_cases hix : i' = x₁
    · by_cases hjx : π j' = x₂
      · exfalso
        apply hx
        exact Prod.ext hix.symm hjx.symm
      · simp [hix, hjx]
    · have hix' : x₁ ≠ i' := fun h => hix h.symm
      simp [hix']
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
  · simp

/-- The permutation group acts transitively on finite-basis labels, so the
orbit sum of a scalar function is independent of the starting label. -/
theorem perm_orbit_sum_eq {b : Type v} [Fintype b] [DecidableEq b]
    (f : b → ℂ) (j k : b) :
    (∑ π : Equiv.Perm b, f (π j)) =
      ∑ π : Equiv.Perm b, f (π k) := by
  classical
  let τ : Equiv.Perm b := Equiv.swap j k
  have h :
      (∑ π : Equiv.Perm b, f ((π * τ) j)) =
        ∑ π : Equiv.Perm b, f (π j) := by
    exact Fintype.sum_equiv
      { toFun := fun π : Equiv.Perm b => π * τ
        invFun := fun π => π * τ⁻¹
        left_inv := by intro π; simp
        right_inv := by intro π; simp }
      (fun π : Equiv.Perm b => f ((π * τ) j))
      (fun π : Equiv.Perm b => f (π j))
      (by intro π; rfl)
  calc
    (∑ π : Equiv.Perm b, f (π j)) =
        ∑ π : Equiv.Perm b, f ((π * τ) j) := h.symm
    _ = ∑ π : Equiv.Perm b, f (π k) := by
      simp [τ]

theorem perm_orbit_sum_card_mul {b : Type v} [Fintype b] [DecidableEq b]
    (f : b → ℂ) (j : b) :
    (Fintype.card b : ℂ) * (∑ π : Equiv.Perm b, f (π j)) =
      (Fintype.card (Equiv.Perm b) : ℂ) * ∑ k : b, f k := by
  classical
  have hconst : ∀ k : b,
      (∑ π : Equiv.Perm b, f (π k)) =
        ∑ π : Equiv.Perm b, f (π j) := by
    intro k
    exact perm_orbit_sum_eq f k j
  calc
    (Fintype.card b : ℂ) * (∑ π : Equiv.Perm b, f (π j)) =
        ∑ k : b, (∑ π : Equiv.Perm b, f (π j)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ k : b, ∑ π : Equiv.Perm b, f (π k) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hconst k]
    _ = ∑ π : Equiv.Perm b, ∑ k : b, f (π k) := by
      rw [Finset.sum_comm]
    _ = ∑ π : Equiv.Perm b, ∑ k : b, f k := by
      refine Finset.sum_congr rfl ?_
      intro π _
      exact (Equiv.sum_comp π f)
    _ = (Fintype.card (Equiv.Perm b) : ℂ) * ∑ k : b, f k := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem perm_orbit_average_eq_uniform {b : Type v} [Fintype b] [DecidableEq b]
    (f : b → ℂ) (j : b) :
    (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ *
        (∑ π : Equiv.Perm b, f (π j)) =
      (Fintype.card b : ℂ)⁻¹ * ∑ k : b, f k := by
  classical
  haveI : Nonempty b := ⟨j⟩
  let cB : ℂ := Fintype.card b
  let cP : ℂ := Fintype.card (Equiv.Perm b)
  let A : ℂ := ∑ π : Equiv.Perm b, f (π j)
  let S : ℂ := ∑ k : b, f k
  have hB : cB ≠ 0 := by
    dsimp [cB]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card b ≠ 0)
  have hP : cP ≠ 0 := by
    dsimp [cP]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm b) ≠ 0)
  have hmain : cB * A = cP * S := by
    dsimp [cB, cP, A, S]
    exact perm_orbit_sum_card_mul f j
  have hA : A = cB⁻¹ * (cP * S) := by
    calc
      A = (cB⁻¹ * cB) * A := by rw [inv_mul_cancel₀ hB, one_mul]
      _ = cB⁻¹ * (cB * A) := by rw [mul_assoc]
      _ = cB⁻¹ * (cP * S) := by rw [hmain]
  calc
    cP⁻¹ * A = cP⁻¹ * (cB⁻¹ * (cP * S)) := by rw [hA]
    _ = cB⁻¹ * S := by
      field_simp [hP]

/-- Average over right-subsystem basis permutations. -/
def localRightPermutationTwirl {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) : CMatrix (Prod a b) :=
  ((Fintype.card (Equiv.Perm b) : ℂ)⁻¹) •
    ∑ π : Equiv.Perm b,
      (localRightUnitary (a := a) (permutationUnitary π) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod a b))

theorem localRightPermutationTwirl_apply {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    localRightPermutationTwirl X (i, j) (i', j') =
      (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ *
        ∑ π : Equiv.Perm b, X (i, π j) (i', π j') := by
  unfold localRightPermutationTwirl
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [permutationUnitary_conj_apply]
  rfl

theorem localRightPermutationTwirl_signTwirl_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    localRightPermutationTwirl (localRightSignTwirl X) (i, j) (i', j') =
      if j = j' then
        (Fintype.card b : ℂ)⁻¹ * ∑ k : b, X (i, k) (i', k)
      else 0 := by
  classical
  rw [localRightPermutationTwirl_apply]
  by_cases hjj' : j = j'
  · subst j'
    have hsum :
        (∑ π : Equiv.Perm b,
          localRightSignTwirl X (i, π j) (i', π j)) =
          ∑ π : Equiv.Perm b, X (i, π j) (i', π j) := by
      refine Finset.sum_congr rfl ?_
      intro π _
      simp [localRightSignTwirl_apply]
    rw [hsum]
    rw [perm_orbit_average_eq_uniform (fun k : b => X (i, k) (i', k)) j]
    simp
  · have hsum :
        (∑ π : Equiv.Perm b,
          localRightSignTwirl X (i, π j) (i', π j')) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro π _
      have hne : π j ≠ π j' := fun h => hjj' (π.injective h)
      simp [localRightSignTwirl_apply, hne]
    rw [hsum, mul_zero]
    simp [hjj']

theorem localRightPermutationTwirl_signTwirl_eq_marginalA_kronecker_maximallyMixed
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty b]
    (X : CMatrix (Prod a b)) :
    localRightPermutationTwirl (localRightSignTwirl X) =
      Matrix.kronecker (partialTraceB X) (maximallyMixed b).matrix := by
  classical
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  rw [localRightPermutationTwirl_signTwirl_apply]
  have hcast :
      ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ)) =
        (Fintype.card b : ℂ)⁻¹ := by
    have hcardR : (Fintype.card b : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card b ≠ 0)
    norm_num [hcardR]
  by_cases hjj' : j = j'
  · subst j'
    simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hcast, mul_comm]
  · simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hjj']

/-- Local-right unitaries respect multiplication. -/
theorem localRightUnitary_mul {b : Type v} [Fintype b] [DecidableEq b]
    (U V : Matrix.unitaryGroup b ℂ) :
    (localRightUnitary (a := a) (U * V) : CMatrix (Prod a b)) =
      (localRightUnitary (a := a) U : CMatrix (Prod a b)) *
        (localRightUnitary (a := a) V : CMatrix (Prod a b)) := by
  rw [localRightUnitary_coe, localRightUnitary_coe, localRightUnitary_coe]
  change Matrix.kronecker (1 : CMatrix a) ((U * V : Matrix.unitaryGroup b ℂ) : CMatrix b) =
    Matrix.kronecker (1 : CMatrix a) (U : CMatrix b) *
      Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)
  simpa using
    (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
      (U : CMatrix b) (V : CMatrix b))

/-- Entrywise formula for the finite right-unitary family obtained by first
dephasing with a diagonal sign and then permuting the right tensor factor. -/
theorem localRightSignPermutationUnitary_conj_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) (π : Equiv.Perm b) (X : CMatrix (Prod a b))
    (i i' : a) (j j' : b) :
    (((localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b)) *
        X *
        star (localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
      boolSignComplex (ε (π j)) * X (i, π j) (i', π j') *
        boolSignComplex (ε (π j')) := by
  classical
  let P : CMatrix (Prod a b) := localRightUnitary (a := a) (permutationUnitary π)
  let D : CMatrix (Prod a b) := localRightUnitary (a := a) (diagonalSignUnitary ε)
  have hmul :
      (localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b)) = P * D := by
    simpa [P, D] using
      localRightUnitary_mul (a := a) (U := permutationUnitary π)
        (V := diagonalSignUnitary ε)
  calc
    (((localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b)) *
        X *
        star (localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
        (P * (D * X * star D) * star P) (i, j) (i', j') := by
          rw [hmul, star_mul]
          simp [P, D, mul_assoc]
    _ = (D * X * star D) (i, π j) (i', π j') := by
          simpa [P] using
            permutationUnitary_conj_apply (a := a) π (D * X * star D) i i' j j'
    _ = boolSignComplex (ε (π j)) * X (i, π j) (i', π j') *
          boolSignComplex (ε (π j')) := by
          simpa [D] using
            diagonalSignUnitary_conj_apply (a := a) ε X i i' (π j) (π j')

/-- The concrete finite local-right-unitary ensemble used in the low-`α`
Gour/Frank--Lieb route realizes the right-subsystem depolarizing twirl.  The
ensemble first applies all diagonal sign flips and then all basis
permutations; its average is `Tr_B(X) ⊗ π_B`. -/
theorem localRightSignPermutationTwirl_eq_marginalA_kronecker_maximallyMixed
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty b]
    (X : CMatrix (Prod a b)) :
    (∑ idx : (b → Bool) × Equiv.Perm b,
      ((Fintype.card ((b → Bool) × Equiv.Perm b) : ℂ)⁻¹) •
        ((localRightUnitary (a := a)
            (permutationUnitary idx.2 * diagonalSignUnitary idx.1) :
              CMatrix (Prod a b)) *
          X *
          star (localRightUnitary (a := a)
            (permutationUnitary idx.2 * diagonalSignUnitary idx.1) :
              CMatrix (Prod a b)))) =
      Matrix.kronecker (partialTraceB X) (maximallyMixed b).matrix := by
  classical
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp_rw [localRightSignPermutationUnitary_conj_apply]
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum]
  have hS : (Fintype.card (b → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (b → Bool) ≠ 0)
  have hP : (Fintype.card (Equiv.Perm b) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm b) ≠ 0)
  have hcard :
      ((Fintype.card ((b → Bool) × Equiv.Perm b) : ℂ)⁻¹) =
        (Fintype.card (b → Bool) : ℂ)⁻¹ *
          (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ := by
    rw [Fintype.card_prod]
    rw [Nat.cast_mul]
    field_simp [hS, hP]
  have hcastB :
      ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ)) =
        (Fintype.card b : ℂ)⁻¹ := by
    have hcardR : (Fintype.card b : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card b ≠ 0)
    norm_num [hcardR]
  by_cases hjj' : j = j'
  · subst j'
    have hsum :
        (∑ idx : (b → Bool) × Equiv.Perm b,
          boolSignComplex (idx.1 (idx.2 j)) *
              X (i, idx.2 j) (i', idx.2 j) *
            boolSignComplex (idx.1 (idx.2 j))) =
          (Fintype.card (b → Bool) : ℂ) *
            ∑ π : Equiv.Perm b, X (i, π j) (i', π j) := by
      rw [Fintype.sum_prod_type]
      simp [Finset.mul_sum, mul_left_comm, mul_comm]
    rw [hsum, hcard]
    calc
      ((Fintype.card (b → Bool) : ℂ)⁻¹ *
          (Fintype.card (Equiv.Perm b) : ℂ)⁻¹) *
          ((Fintype.card (b → Bool) : ℂ) *
            ∑ π : Equiv.Perm b, X (i, π j) (i', π j)) =
          (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ *
            ∑ π : Equiv.Perm b, X (i, π j) (i', π j) := by
        field_simp [hS, hP]
      _ = (Fintype.card b : ℂ)⁻¹ * ∑ k : b, X (i, k) (i', k) := by
        exact perm_orbit_average_eq_uniform (fun k : b => X (i, k) (i', k)) j
      _ = (Matrix.kronecker (partialTraceB X) (maximallyMixed b).matrix)
          (i, j) (i', j) := by
        simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker,
          Matrix.kroneckerMap_apply, hcastB, mul_comm]
  · have hsum :
        (∑ idx : (b → Bool) × Equiv.Perm b,
          boolSignComplex (idx.1 (idx.2 j)) *
              X (i, idx.2 j) (i', idx.2 j') *
            boolSignComplex (idx.1 (idx.2 j'))) = 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_eq_zero ?_
      intro π _
      have hne : π j ≠ π j' := fun h => hjj' (π.injective h)
      calc
        (∑ ε : b → Bool,
          boolSignComplex (ε (π j)) *
              X (i, π j) (i', π j') *
            boolSignComplex (ε (π j'))) =
            X (i, π j) (i', π j') *
              (∑ ε : b → Bool,
                boolSignComplex (ε (π j)) * boolSignComplex (ε (π j'))) := by
          simp [Finset.mul_sum, mul_assoc, mul_comm]
        _ = 0 := by
          rw [boolSignComplex_sum_mul_eq_zero_of_ne hne, mul_zero]
    rw [hsum, mul_zero]
    simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hjj']

/-- Low-`α` partial-trace monotonicity for the PSD-friendly sandwiched Renyi
`Q` functional.

This is the finite-dimensional Gour/Frank--Lieb proof spine: use Frank--Lieb
joint concavity of `Q`, average over a finite local-right-unitary design
(diagonal signs and basis permutations), then identify the twirled state with
`Tr_B(X) ⊗ π_B` and cancel the maximally mixed tensor factor. -/
theorem sandwichedRenyiQ_marginalA_ge_of_half_lt_lt_one
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a] [Nonempty b]
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ hσ α ≤
      sandwichedRenyiQ
        (partialTraceB ρ) (partialTraceB σ)
        (partialTraceB_posSemidef hρ)
        (partialTraceB_posSemidef hσ)
        α := by
  classical
  let ι : Type v := (b → Bool) × Equiv.Perm b
  let w : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
  let U : ι → Matrix.unitaryGroup b ℂ :=
    fun idx => permutationUnitary idx.2 * diagonalSignUnitary idx.1
  have hcardR : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hw_sum : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
    dsimp [w]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcardR]
  have hcast : (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) =
      (Fintype.card ι : ℂ)⁻¹ := by
    norm_num [hcardR]
  have hTwirlρ :
      (∑ i ∈ (Finset.univ : Finset ι), (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix := by
    simpa [ι, w, U, hcast] using
      localRightSignPermutationTwirl_eq_marginalA_kronecker_maximallyMixed
        (a := a) (b := b) ρ
  have hTwirlσ :
      (∑ i ∈ (Finset.univ : Finset ι), (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix := by
    simpa [ι, w, U, hcast] using
      localRightSignPermutationTwirl_eq_marginalA_kronecker_maximallyMixed
        (a := a) (b := b) σ
  exact
    sandwichedRenyiQ_marginalA_ge_of_localRightUnitary_twirling
      (a := a) (b := b) (s := Finset.univ) (w := w) (U := U)
      hρ hσ hα_half hα_lt_one hw_nonneg hw_sum hTwirlρ hTwirlσ

/-- Stinespring isometry invariance of the PSD-friendly low-`α` `Q`
functional.

The lifted states may be singular on `B × κ`; this theorem is exactly why the
strict low-`α` route uses the PSD-level `Q` functional before converting back
to the full-rank sandwiched Renyi divergence at the input and output endpoints. -/
theorem sandwichedRenyiQ_stinespringLiftState
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ σ : State a) {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (stinespringLiftState K hTP ρ).matrix
        (stinespringLiftState K hTP σ).matrix
        (stinespringLiftState K hTP ρ).pos
        (stinespringLiftState K hTP σ).pos α =
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α := by
  let V := MatrixMap.krausStinespringIsometry K hTP
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  simpa [stinespringLiftState, V] using
    sandwichedRenyiQ_isometry_conj
      (V := V.matrix) V.isometry ρ.pos σ.pos α hs_pos hα_pos

/-- Matrix-level Stinespring lift associated to a trace-preserving Kraus
family.

This is the same Stinespring isometry used by `stinespringLiftState`, but it is
stated for an arbitrary matrix input.  It lets the low-`α` `Q` route handle a
PSD reference operator without first normalizing it into a state. -/
def stinespringLiftMatrix {b : Type v} {κ : Type w}
    [Fintype b] [DecidableEq b] [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (X : CMatrix a) : CMatrix (Prod b κ) :=
  (MatrixMap.krausStinespringIsometry K hTP).matrix * X *
    Matrix.conjTranspose (MatrixMap.krausStinespringIsometry K hTP).matrix

/-- The matrix-level Stinespring lift preserves positive semidefiniteness. -/
theorem stinespringLiftMatrix_posSemidef
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {X : CMatrix a} (hX : X.PosSemidef) :
    (stinespringLiftMatrix K hTP X).PosSemidef := by
  simpa [stinespringLiftMatrix] using
    hX.mul_mul_conjTranspose_same
      (MatrixMap.krausStinespringIsometry K hTP).matrix

/-- Tracing the environment of the matrix-level Stinespring lift recovers the
Kraus map. -/
theorem partialTraceB_stinespringLiftMatrix
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (X : CMatrix a) :
    partialTraceB (stinespringLiftMatrix K hTP X) = MatrixMap.ofKraus K X := by
  simpa [stinespringLiftMatrix] using
    MatrixMap.partialTraceB_krausStinespringIsometry K hTP X

/-- Stinespring isometry invariance of the PSD-friendly low-`α` `Q`
functional for a normalized state and an arbitrary PSD matrix reference.

This is the matrix-reference version of `sandwichedRenyiQ_stinespringLiftState`
and is the source-facing handoff needed before a full PSD-reference divergence
interface is introduced. -/
theorem sandwichedRenyiQ_stinespringLiftMatrix_reference
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (stinespringLiftState K hTP ρ).matrix
        (stinespringLiftMatrix K hTP σ)
        (stinespringLiftState K hTP ρ).pos
        (stinespringLiftMatrix_posSemidef K hTP hσ) α =
      sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α := by
  let V := MatrixMap.krausStinespringIsometry K hTP
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  simpa [stinespringLiftState, stinespringLiftMatrix, V] using
    sandwichedRenyiQ_isometry_conj
      (V := V.matrix) V.isometry ρ.pos hσ α hs_pos hα_pos

/-- Strict low-`α` `Q`-functional data processing for a channel acting on a
state and a PSD matrix reference.

This theorem is the PSD-reference core of the Gour/Frank--Lieb route: it proves
the monotonicity of the positive-power `Q_α` expression without requiring the
reference to be normalized or positive definite.  It is later packaged as a
singular PSD-reference divergence via the regularization/limit convention. -/
theorem sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α ≤
      sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  let ρL := stinespringLiftState K hTP ρ
  let σL : CMatrix (Prod b (a × b)) := stinespringLiftMatrix K hTP σ
  letI : Nonempty a := ρ.nonempty
  letI : Nonempty b := (Φ.applyState ρ).nonempty
  have hσL : σL.PosSemidef := by
    simpa [σL] using stinespringLiftMatrix_posSemidef K hTP hσ
  have hPT :
      sandwichedRenyiQ ρL.matrix σL ρL.pos hσL α ≤
        sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL)
          (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef hσL) α := by
    exact sandwichedRenyiQ_marginalA_ge_of_half_lt_lt_one
      (a := b) (b := a × b) (hρ := ρL.pos) (hσ := hσL)
      hα_half hα_lt_one
  have hIso :
      sandwichedRenyiQ ρL.matrix σL ρL.pos hσL α =
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α := by
    simpa [ρL, σL] using
      sandwichedRenyiQ_stinespringLiftMatrix_reference
        K hTP ρ hσ hα_half hα_lt_one
  have hρout : partialTraceB ρL.matrix = (Φ.applyState ρ).matrix := by
    have hstate := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP ρ
    have hm := congrArg State.matrix hstate
    simpa [ρL, State.marginalA] using hm
  have hσout : partialTraceB σL = Φ.map σ := by
    simpa [σL, hK] using partialTraceB_stinespringLiftMatrix K hTP σ
  calc
    sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α =
        sandwichedRenyiQ ρL.matrix σL ρL.pos hσL α := hIso.symm
    _ ≤ sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL)
        (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef hσL) α := hPT
    _ = sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α := by
      simp [sandwichedRenyiQ, hρout, hσout]

/-! ### Source regularization surface for singular PSD references -/

/-- Quadratic-form expansion for a Kraus map.

This is the reusable support-domain calculation: testing `Φ(N)` on an output
vector is the sum of the input quadratic forms of `N` on the Kraus-pulled
vectors. -/
theorem matrixMap_ofKraus_quadraticForm_sum
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b] [Fintype κ]
    (K : κ → Matrix b a ℂ) (N : CMatrix a) (y : b → ℂ) :
    dotProduct (star y) (Matrix.mulVec ((MatrixMap.ofKraus K) N) y) =
      ∑ k : κ, dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
        (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) := by
  simp [MatrixMap.ofKraus, Matrix.sum_mulVec, dotProduct_sum, Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Kraus maps preserve finite-dimensional support domination.

If `M` is supported by a PSD reference `N`, then applying the same completely
positive Kraus map to both matrices preserves that support relation.  This is
the matrix-level domain bridge needed for the source `ρ ≪ σ` branch of the
high-`α` sandwiched Renyi theorem. -/
theorem matrixMap_ofKraus_supports
    {b : Type v} {κ : Type w} [Fintype b] [DecidableEq b] [Fintype κ]
    (K : κ → Matrix b a ℂ)
    {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    Matrix.Supports ((MatrixMap.ofKraus K) M) ((MatrixMap.ofKraus K) N) := by
  intro y hy
  have hqsum_zero :
      (∑ k : κ, dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
        (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y))) = 0 := by
    have hqform :
        dotProduct (star y) (Matrix.mulVec ((MatrixMap.ofKraus K) N) y) = 0 := by
      rw [hy]
      simp
    simpa [matrixMap_ofKraus_quadraticForm_sum K N y] using hqform
  have hq_nonneg :
      ∀ k ∈ (Finset.univ : Finset κ),
        0 ≤ dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
          (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) := by
    intro k _hk
    exact hN.dotProduct_mulVec_nonneg _
  have hq_zero :
      ∀ k : κ, dotProduct (star (Matrix.mulVec (Matrix.conjTranspose (K k)) y))
          (Matrix.mulVec N (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) = 0 := by
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg hq_nonneg).mp hqsum_zero
      k (Finset.mem_univ k)
  have hpull :
      ∀ k : κ, Matrix.mulVec M (Matrix.mulVec (Matrix.conjTranspose (K k)) y) = 0 := by
    intro k
    exact hSupport (Matrix.mulVec (Matrix.conjTranspose (K k)) y)
      ((hN.dotProduct_mulVec_zero_iff
        (Matrix.mulVec (Matrix.conjTranspose (K k)) y)).mp (hq_zero k))
  have hterm :
      ∀ k : κ, Matrix.mulVec (K k * M * Matrix.conjTranspose (K k)) y = 0 := by
    intro k
    calc
      Matrix.mulVec (K k * M * Matrix.conjTranspose (K k)) y =
          Matrix.mulVec (K k) (Matrix.mulVec M
            (Matrix.mulVec (Matrix.conjTranspose (K k)) y)) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by simp [hpull k]
  calc
    Matrix.mulVec ((MatrixMap.ofKraus K) M) y =
        ∑ k : κ, Matrix.mulVec (K k * M * Matrix.conjTranspose (K k)) y := by
          simp [MatrixMap.ofKraus, Matrix.sum_mulVec]
    _ = 0 := by simp [hterm]

/-- Channels preserve finite-dimensional support domination of PSD references.

This is the Schrödinger-picture support-domain counterpart of source
monotonicity: if the input state/operator is supported on the input reference,
then the channel output is supported on the output reference. -/
theorem channel_map_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    Matrix.Supports (Φ.map M) (Φ.map N) := by
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  simpa [← hK] using matrixMap_ofKraus_supports K hN hSupport

/-- State/reference support domination is preserved by applying a channel.

This is the source-domain statement `ρ ≪ σ ⇒ Φ(ρ) ≪ Φ(σ)` for PSD matrix
references. -/
theorem channel_applyState_supports_of_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) := by
  exact channel_map_supports Φ hσ hSupport

/-- Khatri--Wilde/Gour reference regularization `σ_ε = σ + ε I`.

The singular-reference part of the public sandwiched-Renyi DPI is obtained in
the source by applying the positive-definite theorem to this path and then
taking `ε → 0+`.  This definition keeps that source path explicit and avoids
silently replacing a Schrödinger-picture channel by a unital map. -/
def sandwichedRenyiReferenceRegularization (σ : CMatrix a) (ε : ℝ) : CMatrix a :=
  σ + ε • (1 : CMatrix a)

omit [Fintype a] in
@[simp] theorem sandwichedRenyiReferenceRegularization_zero (σ : CMatrix a) :
    sandwichedRenyiReferenceRegularization σ 0 = σ := by
  simp [sandwichedRenyiReferenceRegularization]

omit [Fintype a] in
/-- The source regularization of a PSD reference is positive definite for
strictly positive regularization parameter. -/
theorem sandwichedRenyiReferenceRegularization_posDef
    {σ : CMatrix a} (hσ : σ.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (sandwichedRenyiReferenceRegularization σ ε).PosDef := by
  simpa [sandwichedRenyiReferenceRegularization] using
    cMatrix_posSemidef_add_pos_smul_one_posDef hσ hε

omit [Fintype a] in
/-- The source regularization of a PSD reference is PSD for nonnegative
regularization parameter. -/
theorem sandwichedRenyiReferenceRegularization_posSemidef
    {σ : CMatrix a} (hσ : σ.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) :
    (sandwichedRenyiReferenceRegularization σ ε).PosSemidef := by
  simpa [sandwichedRenyiReferenceRegularization] using
    cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hσ hε

/-- Positive source regularization supports every input matrix. -/
theorem supports_sandwichedRenyiReferenceRegularization_of_pos
    (M : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports M (sandwichedRenyiReferenceRegularization σ ε) :=
  Matrix.Supports.of_right_posDef M
    (sandwichedRenyiReferenceRegularization σ ε)
    (sandwichedRenyiReferenceRegularization_posDef hσ hε)

/-- Channel outputs obey the support condition for the channel-compatible
source regularization `Φ(σ + εI)`.

For high-`α` singular references, this is the exact source-domain bridge used
before taking `ε → 0+`: even if `Φ(σ + εI)` is singular, the output state is
supported on it. -/
theorem channel_applyState_supports_regularized_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports (Φ.applyState ρ).matrix
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) := by
  exact channel_applyState_supports_of_supports ρ
    (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε)) Φ
    (supports_sandwichedRenyiReferenceRegularization_of_pos ρ.matrix hσ hε)

omit [Fintype a] in
/-- The regularization path `σ + εI` converges to `σ` as `ε → 0+`. -/
theorem sandwichedRenyiReferenceRegularization_tendsto
    (σ : CMatrix a) :
    Filter.Tendsto (fun ε : ℝ => sandwichedRenyiReferenceRegularization σ ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds σ) := by
  simpa [sandwichedRenyiReferenceRegularization] using
    cMatrix_tendsto_add_pos_smul_one (A := σ)

/-- The matrix-reference sandwiched Renyi inner operator in the spectral basis
of the PSD reference.  This is the non-regularized support-compression form:
after conjugating by the reference eigenbasis, the inner operator is a diagonal
weight sandwich of the conjugated input state. -/
theorem sandwichedRenyiReferenceInner_conj_eigenbasis
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    let D : CMatrix a := Matrix.diagonal
      (fun i => ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
    star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ σ α * (U : CMatrix a) =
      D * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
  have hpow :
      CFC.rpow σ s = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, s] using cMatrix_rpow_eq_eigenbasis_diagonal hσ s
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp
  change star (U : CMatrix a) *
      ((CFC.rpow σ s) * ρ.matrix * (CFC.rpow σ s)) * (U : CMatrix a) =
    D * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D
  rw [hpow]
  calc
    star (U : CMatrix a) *
        (((U : CMatrix a) * D * star (U : CMatrix a)) * ρ.matrix *
          ((U : CMatrix a) * D * star (U : CMatrix a))) * (U : CMatrix a)
        = D * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D := by
          simp [Matrix.mul_assoc, hUstarU]
          rw [← Matrix.mul_assoc, hUstarU, Matrix.one_mul]

/-- The source-regularized matrix-reference sandwiched Renyi inner operator in
the original PSD reference eigenbasis.  For `ε ≥ 0`, `σ + εI` has the same
eigenvectors as `σ`, with eigenvalues shifted by `ε`. -/
theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    let Dε : CMatrix a := Matrix.diagonal
      (fun i => (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ))
    star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α * (U : CMatrix a) =
      Dε * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * Dε := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let Dε : CMatrix a := Matrix.diagonal
    (fun i => (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ))
  have hpow :
      CFC.rpow (sandwichedRenyiReferenceRegularization σ ε) s =
        (U : CMatrix a) * Dε * star (U : CMatrix a) := by
    simpa [sandwichedRenyiReferenceRegularization, U, Dε, s] using
      cMatrix_rpow_add_nonneg_smul_one_eigenbasis_diagonal hσ hε s
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp
  change star (U : CMatrix a) *
      ((CFC.rpow (sandwichedRenyiReferenceRegularization σ ε) s) * ρ.matrix *
        (CFC.rpow (sandwichedRenyiReferenceRegularization σ ε) s)) * (U : CMatrix a) =
    Dε * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * Dε
  rw [hpow]
  calc
    star (U : CMatrix a) *
        (((U : CMatrix a) * Dε * star (U : CMatrix a)) * ρ.matrix *
          ((U : CMatrix a) * Dε * star (U : CMatrix a))) * (U : CMatrix a)
        = Dε * (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * Dε := by
          simp [Matrix.mul_assoc, hUstarU]
          rw [← Matrix.mul_assoc, hUstarU, Matrix.one_mul]

/-- Under the support condition `ρ ≪ σ`, the spectral-basis entries of the
source-regularized high-`α` inner operator vanish whenever either side lies in
the zero eigenspace of `σ`.

This is the cancellation step needed before taking `ε → 0+` with the negative
reference exponent: the shifted factors `(λᵢ + ε)^s` may diverge when
`λᵢ = 0`, but the supported conjugated input matrix has zero row and column in
those directions. -/
theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_eq_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    {ε : ℝ} (hε : 0 ≤ ε) (α : ℝ) {i j : a}
    (hzero : hσ.isHermitian.eigenvalues i = 0 ∨
      hσ.isHermitian.eigenvalues j = 0) :
    (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α *
        (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j = 0 := by
  classical
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let Dε : CMatrix a := Matrix.diagonal
    (fun k => (((hσ.isHermitian.eigenvalues k + ε) ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hMzero : M' i j = 0 := by
    simpa [M', U] using
      supports_conjugate_entry_eq_zero_of_left_or_right_zero
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport (i := i) (j := j) hzero
  have hform :=
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis
      ρ hσ hε α
  rw [hform]
  change (Dε * M' * Dε) i j = 0
  simp [Dε, Matrix.mul_apply, Matrix.diagonal, hMzero]

/-- Non-regularized version of the same support cancellation: the high-`α`
inner operator has no spectral-basis entries touching the zero eigenspace of a
supporting singular reference. -/
theorem sandwichedRenyiReferenceInner_conj_eigenbasis_entry_eq_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) {i j : a}
    (hzero : hσ.isHermitian.eigenvalues i = 0 ∨
      hσ.isHermitian.eigenvalues j = 0) :
    (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
        sandwichedRenyiReferenceInner ρ σ α *
        (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j = 0 := by
  classical
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun k => ((hσ.isHermitian.eigenvalues k ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hMzero : M' i j = 0 := by
    simpa [M', U] using
      supports_conjugate_entry_eq_zero_of_left_or_right_zero
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport (i := i) (j := j) hzero
  have hform :=
    sandwichedRenyiReferenceInner_conj_eigenbasis
      ρ hσ α
  rw [hform]
  change (D * M' * D) i j = 0
  simp [D, Matrix.mul_apply, Matrix.diagonal, hMzero]

/-- Entrywise form of the source-regularized high-`α` inner operator in the
original PSD reference eigenbasis. -/
theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) (α : ℝ) (i j : a) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    (star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α *
        (U : CMatrix a)) i j =
      (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ) *
        (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) i j *
          (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ) := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let Dε : CMatrix a := Matrix.diagonal
    (fun k => (((hσ.isHermitian.eigenvalues k + ε) ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hform :=
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis
      ρ hσ hε α
  rw [hform]
  change (Dε * M' * Dε) i j =
    (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ) *
      M' i j * (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ)
  simp [Dε, M', Matrix.mul_apply, Matrix.diagonal]

/-- Entrywise form of the high-`α` inner operator in the PSD reference
eigenbasis.  Together with the regularized entry formula, this is the local
calculation needed for the supported `ε → 0+` limit. -/
theorem sandwichedRenyiReferenceInner_conj_eigenbasis_entry
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (i j : a) :
    let s : ℝ := (1 - α) / (2 * α)
    let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
    (star (U : CMatrix a) *
        sandwichedRenyiReferenceInner ρ σ α *
        (U : CMatrix a)) i j =
      ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
        (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) i j *
          ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) := by
  classical
  dsimp
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun k => ((hσ.isHermitian.eigenvalues k ^ s : ℝ) : ℂ))
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hform :=
    sandwichedRenyiReferenceInner_conj_eigenbasis
      ρ hσ α
  rw [hform]
  change (D * M' * D) i j =
    ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
      M' i j * ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ)
  simp [D, M', Matrix.mul_apply, Matrix.diagonal]

/-- Supported source regularization converges entrywise in the reference
eigenbasis.  This is the pointwise Gour/source support-compression step for
the high-`α` finite branch: zero spectral directions are killed by the support
condition, while positive directions use ordinary scalar power continuity. -/
theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_tendsto
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (i j : a) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j)) := by
  classical
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  by_cases hi0 : hσ.isHermitian.eigenvalues i = 0
  · have htarget :
        (star (U : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j = 0 := by
      simpa [U] using
        sandwichedRenyiReferenceInner_conj_eigenbasis_entry_eq_zero
          ρ hσ hSupport α (i := i) (j := j) (Or.inl hi0)
    rw [htarget]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    symm
    simpa [U] using
      sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_eq_zero
        ρ hσ hSupport (le_of_lt hε) α (i := i) (j := j) (Or.inl hi0)
  by_cases hj0 : hσ.isHermitian.eigenvalues j = 0
  · have htarget :
        (star (U : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j = 0 := by
      simpa [U] using
        sandwichedRenyiReferenceInner_conj_eigenbasis_entry_eq_zero
          ρ hσ hSupport α (i := i) (j := j) (Or.inr hj0)
    rw [htarget]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    symm
    simpa [U] using
      sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_eq_zero
        ρ hσ hSupport (le_of_lt hε) α (i := i) (j := j) (Or.inr hj0)
  have hi_pos : 0 < hσ.isHermitian.eigenvalues i := by
    exact lt_of_le_of_ne (hσ.eigenvalues_nonneg i) (by
      intro h
      exact hi0 h.symm)
  have hj_pos : 0 < hσ.isHermitian.eigenvalues j := by
    exact lt_of_le_of_ne (hσ.eigenvalues_nonneg j) (by
      intro h
      exact hj0 h.symm)
  have hlin_i :
      Filter.Tendsto (fun ε : ℝ => hσ.isHermitian.eigenvalues i + ε)
        l (nhds (hσ.isHermitian.eigenvalues i)) := by
    have hcont : Continuous fun ε : ℝ => hσ.isHermitian.eigenvalues i + ε := by
      fun_prop
    simpa [l] using
      (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))).tendsto
  have hlin_j :
      Filter.Tendsto (fun ε : ℝ => hσ.isHermitian.eigenvalues j + ε)
        l (nhds (hσ.isHermitian.eigenvalues j)) := by
    have hcont : Continuous fun ε : ℝ => hσ.isHermitian.eigenvalues j + ε := by
      fun_prop
    simpa [l] using
      (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))).tendsto
  have hpow_i :
      Filter.Tendsto
        (fun ε : ℝ => ((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ))
        l (nhds (hσ.isHermitian.eigenvalues i ^ s)) := by
    exact
      (Real.continuousAt_rpow_const (hσ.isHermitian.eigenvalues i) s
        (Or.inl (ne_of_gt hi_pos))).tendsto.comp hlin_i
  have hpow_j :
      Filter.Tendsto
        (fun ε : ℝ => ((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ))
        l (nhds (hσ.isHermitian.eigenvalues j ^ s)) := by
    exact
      (Real.continuousAt_rpow_const (hσ.isHermitian.eigenvalues j) s
        (Or.inl (ne_of_gt hj_pos))).tendsto.comp hlin_j
  have hcpow_i :
      Filter.Tendsto
        (fun ε : ℝ => (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ))
        l (nhds (((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.tendsto _ |>.comp hpow_i
  have hcpow_j :
      Filter.Tendsto
        (fun ε : ℝ => (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ))
        l (nhds (((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.tendsto _ |>.comp hpow_j
  have hexplicit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (((hσ.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ) *
            M' i j *
              (((hσ.isHermitian.eigenvalues j + ε) ^ s : ℝ) : ℂ))
        l
        (nhds
          (((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
            M' i j *
              (((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ)))) := by
    exact (hcpow_i.mul tendsto_const_nhds).mul hcpow_j
  have htarget :
      (star (U : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j =
        ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
          M' i j * ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) := by
    simpa [s, U, M'] using
      sandwichedRenyiReferenceInner_conj_eigenbasis_entry
        ρ hσ α i j
  rw [htarget]
  refine hexplicit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  symm
  simpa [s, U, M'] using
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry
      ρ hσ (le_of_lt hε) α i j

/-- Matrix form of the supported source-regularization convergence in the
reference eigenbasis. -/
theorem sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_tendsto
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ σ α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a))) := by
  change Filter.Tendsto
      (fun ε : ℝ => fun i => fun j =>
        (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
          sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α *
          (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (fun i => fun j =>
          (star (hσ.isHermitian.eigenvectorUnitary : CMatrix a) *
            sandwichedRenyiReferenceInner ρ σ α *
            (hσ.isHermitian.eigenvectorUnitary : CMatrix a)) i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_entry_tendsto
      ρ hσ hSupport α i j

/-- Supported source regularization converges for the high-`α` inner operator.

This is the first coordinate-free continuity statement in the Gour/source
support-domain route.  The proof conjugates to the PSD reference eigenbasis,
uses entrywise support cancellation there, then conjugates back by the fixed
unitary. -/
theorem sandwichedRenyiReferenceInner_regularization_tendsto_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sandwichedRenyiReferenceInner ρ σ α)) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  have hconj :=
    sandwichedRenyiReferenceInner_regularized_conj_eigenbasis_tendsto
      ρ hσ hSupport α
  have hcont : Continuous fun X : CMatrix a => (U : CMatrix a) * X * star (U : CMatrix a) := by
    fun_prop
  have hback :=
    (hcont.tendsto
      (star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α *
        (U : CMatrix a))).comp hconj
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp
  change Filter.Tendsto
      (fun ε : ℝ =>
        (U : CMatrix a) *
          (star (U : CMatrix a) *
            sandwichedRenyiReferenceInner ρ
              (sandwichedRenyiReferenceRegularization σ ε) α *
            (U : CMatrix a)) *
          star (U : CMatrix a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((U : CMatrix a) *
          (star (U : CMatrix a) *
            sandwichedRenyiReferenceInner ρ σ α *
            (U : CMatrix a)) *
          star (U : CMatrix a))) at hback
  have hback' :
      Filter.Tendsto
        (fun ε : ℝ =>
          (U : CMatrix a) *
            (star (U : CMatrix a) *
              sandwichedRenyiReferenceInner ρ
                (sandwichedRenyiReferenceRegularization σ ε) α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((U : CMatrix a) *
            (star (U : CMatrix a) *
              sandwichedRenyiReferenceInner ρ σ α))) := by
    simpa [Matrix.mul_assoc, hUstarU] using hback
  have htarget :
      (U : CMatrix a) *
          (star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α) =
        sandwichedRenyiReferenceInner ρ σ α := by
    rw [← Matrix.mul_assoc, hUUstar, Matrix.one_mul]
  rw [htarget] at hback'
  refine hback'.congr' ?_
  filter_upwards with ε
  symm
  rw [← Matrix.mul_assoc, hUUstar, Matrix.one_mul]

/-- Under the finite high-`α` support condition, the singular-reference inner
operator is nonzero.  In the reference eigenbasis, the supported state has no
entries touching the zero eigenspace; on the positive eigenspace the reference
power factors are nonzero scalars. -/
theorem sandwichedRenyiReferenceInner_ne_zero_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    sandwichedRenyiReferenceInner ρ σ α ≠ 0 := by
  classical
  let s : ℝ := (1 - α) / (2 * α)
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  intro hinner_zero
  have hconj_zero :
      star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a) = 0 := by
    rw [hinner_zero]
    simp
  have hM'_zero : M' = 0 := by
    ext i j
    by_cases hi0 : hσ.isHermitian.eigenvalues i = 0
    · simpa [M', U] using
        supports_conjugate_entry_eq_zero_of_left_or_right_zero
          (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
          (i := i) (j := j) (Or.inl hi0)
    by_cases hj0 : hσ.isHermitian.eigenvalues j = 0
    · simpa [M', U] using
        supports_conjugate_entry_eq_zero_of_left_or_right_zero
          (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
          (i := i) (j := j) (Or.inr hj0)
    have hi_pos : 0 < hσ.isHermitian.eigenvalues i := by
      exact lt_of_le_of_ne (hσ.eigenvalues_nonneg i) (by
        intro h
        exact hi0 h.symm)
    have hj_pos : 0 < hσ.isHermitian.eigenvalues j := by
      exact lt_of_le_of_ne (hσ.eigenvalues_nonneg j) (by
        intro h
        exact hj0 h.symm)
    have hentry_zero :
        (star (U : CMatrix a) * sandwichedRenyiReferenceInner ρ σ α *
          (U : CMatrix a)) i j = 0 := by
      simpa using congrArg (fun M : CMatrix a => M i j) hconj_zero
    have hentry_formula :
        (star (U : CMatrix a) *
            sandwichedRenyiReferenceInner ρ σ α *
            (U : CMatrix a)) i j =
          ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) *
            M' i j * ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) := by
      simpa [s, U, M'] using
        sandwichedRenyiReferenceInner_conj_eigenbasis_entry
          ρ hσ α i j
    rw [hentry_formula] at hentry_zero
    have hi_ne :
        ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast
        (ne_of_gt (Real.rpow_pos_of_pos hi_pos s))
    have hj_ne :
        ((hσ.isHermitian.eigenvalues j ^ s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast
        (ne_of_gt (Real.rpow_pos_of_pos hj_pos s))
    have hleft :
        ((hσ.isHermitian.eigenvalues i ^ s : ℝ) : ℂ) * M' i j = 0 :=
      (mul_eq_zero.mp hentry_zero).resolve_right hj_ne
    exact (mul_eq_zero.mp hleft).resolve_left hi_ne
  have hρ_zero : ρ.matrix = 0 := by
    have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simp
    have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      ρ.matrix = (U : CMatrix a) * M' * star (U : CMatrix a) := by
        symm
        calc
          (U : CMatrix a) * M' * star (U : CMatrix a) =
              (U : CMatrix a) *
                (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) *
                  star (U : CMatrix a) := by
                rfl
          _ = ((U : CMatrix a) * star (U : CMatrix a)) * ρ.matrix *
                ((U : CMatrix a) * star (U : CMatrix a)) := by
                noncomm_ring
          _ = ρ.matrix := by
                rw [hUUstar]
                simp
      _ = 0 := by
        rw [hM'_zero]
        simp
  exact ρ.matrix_ne_zero hρ_zero

/-- The supported singular-reference high-`α` inner operator has strictly
positive power trace. -/
theorem sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) :
    0 <
      psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
        (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) α :=
  psdTracePower_pos_of_ne_zero
    (sandwichedRenyiReferenceInner ρ σ α)
    (sandwichedRenyiReferenceInner_posSemidef ρ hσ α)
    (sandwichedRenyiReferenceInner_ne_zero_of_supports ρ hσ hSupport α)

/-- The high-`α` raw power trace of the supported source-regularized inner
operator converges to the supported singular finite branch.

The statement is written without a dependent PSD witness for the regularized
reference because the source filter supplies `ε > 0` only eventually.  Callers
can unfold `psdTracePower` on that eventual positive branch. -/
theorem sandwichedRenyiReferenceInner_tracePower_regularization_tendsto_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα_pos : 0 < α) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ((CFC.rpow
          (sandwichedRenyiReferenceInner ρ
            (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re) := by
  have hinner :=
    sandwichedRenyiReferenceInner_regularization_tendsto_of_supports
      ρ hσ hSupport α
  have hinner_psd_event :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (sandwichedRenyiReferenceInner ρ
          (sandwichedRenyiReferenceRegularization σ ε) α).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact
      sandwichedRenyiReferenceInner_posSemidef ρ
        (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε)) α
  exact
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      hα_pos hinner hinner_psd_event
      (sandwichedRenyiReferenceInner_posSemidef ρ hσ α)

/-- Real-valued finite branch of the sandwiched Renyi divergence against a
PSD reference in the strict low-`α` range.

For `1 / 2 < α < 1`, the source expression uses only the positive-power
functional `Q_α(ρ, σ)`.  The caller must supply positivity of this `Q` value
when using logarithmic order lemmas; this keeps the finite real-valued branch
separate from the extended-real singular case where `Q_α = 0`. -/
def sandwichedRenyiPSDReferenceLowAlpha
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α)

/-- On positive-definite references, the PSD low-`α` finite branch agrees with
the existing positive-definite reference divergence surface. -/
theorem sandwichedRenyiPSDReferenceLowAlpha_eq_reference_posDef
    (ρ : State a) {σ : CMatrix a}
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ.posSemidef α =
      sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one := by
  rfl

/-- Strict low-`α` DPI for the finite real-valued PSD-reference branch.

This is the source-facing PSD-reference continuation of the Gour/Frank--Lieb
route: it uses `Q_α(ρ, σ) ≤ Q_α(Φρ, Φσ)` and the negative logarithmic
prefactor for `α < 1`.  The hypothesis `hQpos` selects the finite branch
`Q_α(ρ, σ) > 0`; the channel inequality then implies positivity of the output
`Q` value. -/
theorem sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α := by
  have hQ :=
    sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
      ρ hσ Φ α hα_half hα_lt_one
  have hlog :
      log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) ≤
        log2 (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hQpos hQ)
      (le_of_lt (Real.log_pos one_lt_two))
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  simpa [sandwichedRenyiPSDReferenceLowAlpha] using
    mul_le_mul_of_nonpos_left hlog hcoef_nonpos

/-- Input-side source regularization curve for the finite PSD-reference
strict low-`α` branch.

The branch is total on `ℝ`; along the source filter `ε → 0+`, it unfolds to
`D̃_α(ρ || σ + εI)` expressed through the PSD-friendly `Q` functional. -/
def sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (ε : ℝ) : ℝ :=
  if hε : 0 ≤ ε then
    sandwichedRenyiPSDReferenceLowAlpha ρ
      (sandwichedRenyiReferenceRegularization σ ε)
      (sandwichedRenyiReferenceRegularization_posSemidef hσ hε) α
  else
    sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α

/-- Output-side channel-compatible source regularization curve for the finite
PSD-reference strict low-`α` branch.

The output reference is `Φ(σ + εI)`, not `Φσ + εI`; this is the correct
Schrödinger-picture regularization path. -/
def sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) (ε : ℝ) : ℝ :=
  if hε : 0 ≤ ε then
    sandwichedRenyiPSDReferenceLowAlpha (Φ.applyState ρ)
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ hε)) α
  else
    sandwichedRenyiPSDReferenceLowAlpha (Φ.applyState ρ)
      (Φ.map σ) (Φ.mapsPositive σ hσ) α

/-- The strict low-`α` PSD-reference regularized curves satisfy pointwise DPI
eventually along the source filter `ε → 0+`.

Unlike the positive-definite real-reference curve theorem, this uses the
PSD-friendly `Q` branch directly and therefore does not require an output
positive-definiteness assumption on `Φ(σ + εI)`. -/
theorem sandwichedRenyiPSDReferenceLowAlphaRegularizedCurves_eventually_le
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α ε := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hσreg_psd :
      (sandwichedRenyiReferenceRegularization σ ε).PosSemidef :=
    sandwichedRenyiReferenceRegularization_posSemidef hσ hε_nonneg
  have hσreg_pd :
      (sandwichedRenyiReferenceRegularization σ ε).PosDef :=
    sandwichedRenyiReferenceRegularization_posDef hσ hε
  have hQpos :
      0 < sandwichedRenyiQ ρ.matrix
        (sandwichedRenyiReferenceRegularization σ ε)
        ρ.pos hσreg_psd α :=
    sandwichedRenyiQ_pos_of_state_posDef_reference ρ hσreg_pd α
  have hDPI :=
    sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel
      ρ hσreg_psd Φ α hα_half hα_lt_one hQpos
  simpa [sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve,
    sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve, hε_nonneg]
    using hDPI

/-- The input regularization curve converges to the finite PSD-reference
strict low-`α` branch when the limiting `Q` value is positive. -/
theorem sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve_tendsto
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let σF : ℝ → CMatrix a := fun ε =>
    if hε : 0 ≤ ε then sandwichedRenyiReferenceRegularization σ ε else σ
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  have hσF_psd : ∀ ε, (σF ε).PosSemidef := by
    intro ε
    by_cases hε : 0 ≤ ε
    · simpa [σF, hε] using
        sandwichedRenyiReferenceRegularization_posSemidef hσ hε
    · simpa [σF, hε] using hσ
  have hσF_tend : Filter.Tendsto σF l (nhds σ) := by
    have hreg := sandwichedRenyiReferenceRegularization_tendsto (a := a) σ
    have hcongr :
        (fun ε : ℝ => sandwichedRenyiReferenceRegularization σ ε) =ᶠ[l] σF := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      simp [σF, hε_nonneg]
    exact Filter.Tendsto.congr' hcongr hreg
  have hQ_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α)
        l
        (nhds (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos tendsto_const_nhds hσF_tend
      (fun _ => ρ.pos) hσF_psd ρ.pos hσ
  have hlog_tend :
      Filter.Tendsto
        (fun ε => log2 (sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α))
        l
        (nhds (log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α))) := by
    have hraw := Filter.Tendsto.log hQ_tend (ne_of_gt hQpos)
    simpa [log2] using
      hraw.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hdiv_tend :
      Filter.Tendsto
        (fun ε =>
          (1 / (α - 1)) *
            log2 (sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α))
        l
        (nhds
          ((1 / (α - 1)) *
            log2 (sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α))) :=
    hlog_tend.const_mul (1 / (α - 1))
  have hcurve :
      (fun ε =>
          (1 / (α - 1)) *
            log2 (sandwichedRenyiQ ρ.matrix (σF ε) ρ.pos (hσF_psd ε) α))
        =ᶠ[l]
      sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    simp [sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve,
      sandwichedRenyiPSDReferenceLowAlpha, σF, hε_nonneg]
  exact Filter.Tendsto.congr' hcurve hdiv_tend

/-- The output regularization curve converges to the finite PSD-reference
strict low-`α` branch when the limiting output `Q` value is positive. -/
theorem sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve_tendsto
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos :
      0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (sandwichedRenyiPSDReferenceLowAlpha
          (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let σF : ℝ → CMatrix b := fun ε =>
    if hε : 0 ≤ ε then
      Φ.map (sandwichedRenyiReferenceRegularization σ ε)
    else
      Φ.map σ
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
  have hσF_psd : ∀ ε, (σF ε).PosSemidef := by
    intro ε
    by_cases hε : 0 ≤ ε
    · simpa [σF, hε] using
        Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posSemidef hσ hε)
    · simpa [σF, hε] using Φ.mapsPositive σ hσ
  have hσF_tend : Filter.Tendsto σF l (nhds (Φ.map σ)) := by
    have hreg := sandwichedRenyiReferenceRegularization_tendsto (a := a) σ
    have hmap :
        Filter.Tendsto
          (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          l (nhds (Φ.map σ)) :=
      (LinearMap.continuous_of_finiteDimensional Φ.map).tendsto σ |>.comp hreg
    have hcongr :
        (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε)) =ᶠ[l] σF := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      simp [σF, hε_nonneg]
    exact Filter.Tendsto.congr' hcongr hmap
  have hQ_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
          (Φ.applyState ρ).pos (hσF_psd ε) α)
        l
        (nhds
          (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos tendsto_const_nhds hσF_tend
      (fun _ => (Φ.applyState ρ).pos) hσF_psd
      (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ)
  have hlog_tend :
      Filter.Tendsto
        (fun ε => log2
          (sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
            (Φ.applyState ρ).pos (hσF_psd ε) α))
        l
        (nhds (log2
          (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α))) := by
    have hraw := Filter.Tendsto.log hQ_tend (ne_of_gt hQpos)
    simpa [log2] using
      hraw.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hdiv_tend :
      Filter.Tendsto
        (fun ε =>
          (1 / (α - 1)) *
            log2
              (sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
                (Φ.applyState ρ).pos (hσF_psd ε) α))
        l
        (nhds
          ((1 / (α - 1)) *
            log2
              (sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
                (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α))) :=
    hlog_tend.const_mul (1 / (α - 1))
  have hcurve :
      (fun ε =>
          (1 / (α - 1)) *
            log2
              (sandwichedRenyiQ (Φ.applyState ρ).matrix (σF ε)
                (Φ.applyState ρ).pos (hσF_psd ε) α))
        =ᶠ[l]
      sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    simp [sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve,
      sandwichedRenyiPSDReferenceLowAlpha, σF, hε_nonneg]
  exact Filter.Tendsto.congr' hcurve hdiv_tend

private theorem frankLieb_log2_mono_of_pos {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Convert a low-`α` `Q` inequality into a matrix-reference sandwiched Renyi
divergence inequality.

For `α < 1`, the coefficient `1 / (α - 1)` is nonpositive, so the logarithmic
order reverses.  This is the non-normalized-reference analogue of
`sandwichedRenyi_dataProcessing_le_of_lowAlphaQ_ge`. -/
theorem sandwichedRenyiReference_le_of_lowAlphaQ_ge
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρIn : State a) {σIn : CMatrix a}
    (ρOut : State b) {σOut : CMatrix b}
    (hρIn : ρIn.matrix.PosDef) (hσIn : σIn.PosDef)
    (hρOut : ρOut.matrix.PosDef) (hσOut : σOut.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQ :
      sandwichedRenyiQ ρIn.matrix σIn ρIn.pos hσIn.posSemidef α ≤
        sandwichedRenyiQ ρOut.matrix σOut ρOut.pos hσOut.posSemidef α) :
    sandwichedRenyiReference ρOut σOut hρOut hσOut α
        (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyiReference ρIn σIn hρIn hσIn α
        (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  rw [sandwichedRenyiReference_eq_log2_psdTracePower_inner
      ρOut hρOut hσOut α hα_pos hα_ne_one,
    sandwichedRenyiReference_eq_log2_psdTracePower_inner
      ρIn hρIn hσIn α hα_pos hα_ne_one]
  have hpower :
      psdTracePower (sandwichedRenyiReferenceInner ρIn σIn α)
          (sandwichedRenyiReferenceInner_posSemidef ρIn hσIn.posSemidef α) α ≤
        psdTracePower (sandwichedRenyiReferenceInner ρOut σOut α)
          (sandwichedRenyiReferenceInner_posSemidef ρOut hσOut.posSemidef α) α := by
    simpa [sandwichedRenyiQ_eq_psdTracePower_referenceInner] using hQ
  have hin_pos :
      0 <
        psdTracePower (sandwichedRenyiReferenceInner ρIn σIn α)
          (sandwichedRenyiReferenceInner_posSemidef ρIn hσIn.posSemidef α) α :=
    sandwichedRenyiReferenceInner_psdTracePower_pos ρIn hρIn hσIn α
  have hlog := frankLieb_log2_mono_of_pos hin_pos hpower
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  exact mul_le_mul_of_nonpos_left hlog hcoef_nonpos

/-- Strict low-`α` sandwiched Renyi DPI for a positive-definite,
possibly non-normalized matrix reference, proved directly from the PSD
`Q`-functional channel theorem.

This is a source-aligned bridge toward the public PSD-reference statement.  It
still assumes the input and output references are positive definite because the
current `sandwichedRenyiReference` divergence API is real-valued on `PosDef`
references. -/
theorem sandwichedRenyiReference_dataProcessing_channel_of_half_lt_lt_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
        hρΦ hσΦ α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyiReference ρ σ hρ hσ α
        (by linarith) (ne_of_lt hα_lt_one) := by
  have hQ :=
    sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
      ρ hσ.posSemidef Φ α hα_half hα_lt_one
  exact
    sandwichedRenyiReference_le_of_lowAlphaQ_ge
      ρ (Φ.applyState ρ) hρ hσ hρΦ hσΦ α hα_half hα_lt_one hQ

/-- Strict low-`α` full-rank sandwiched Renyi DPI for an arbitrary
finite-dimensional channel.

This is the Gour/Frank--Lieb strict low-`α` proof spine.  It never evaluates the
existing full-rank `sandwichedRenyi` API on the singular Stinespring lift: the
lift is handled by the PSD-friendly `Q` functional, partial-trace monotonicity
is applied at `Q` level, and only the full-rank input/output endpoints are
converted back to the sandwiched Renyi divergence. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_half_lt_lt_one_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  let ρL := stinespringLiftState K hTP ρ
  let σL := stinespringLiftState K hTP σ
  letI : Nonempty a := ρ.nonempty
  letI : Nonempty b := (Φ.applyState ρ).nonempty
  have hPT :
      sandwichedRenyiQ ρL.matrix σL.matrix ρL.pos σL.pos α ≤
        sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL.matrix)
          (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef σL.pos) α := by
    exact sandwichedRenyiQ_marginalA_ge_of_half_lt_lt_one
      (a := b) (b := a × b) (hρ := ρL.pos) (hσ := σL.pos)
      hα_half hα_lt_one
  have hIso :
      sandwichedRenyiQ ρL.matrix σL.matrix ρL.pos σL.pos α =
        sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α := by
    simpa [ρL, σL] using
      sandwichedRenyiQ_stinespringLiftState K hTP ρ σ hα_half hα_lt_one
  have hρout : partialTraceB ρL.matrix = (Φ.applyState ρ).matrix := by
    have hstate := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP ρ
    have hm := congrArg State.matrix hstate
    simpa [ρL, State.marginalA] using hm
  have hσout : partialTraceB σL.matrix = (Φ.applyState σ).matrix := by
    have hstate := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP σ
    have hm := congrArg State.matrix hstate
    simpa [σL, State.marginalA] using hm
  have hQ :
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α ≤
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ).pos α := by
    calc
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α =
          sandwichedRenyiQ ρL.matrix σL.matrix ρL.pos σL.pos α := hIso.symm
      _ ≤ sandwichedRenyiQ (partialTraceB ρL.matrix) (partialTraceB σL.matrix)
          (partialTraceB_posSemidef ρL.pos) (partialTraceB_posSemidef σL.pos) α := hPT
      _ = sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ).pos α := by
        simp [sandwichedRenyiQ, hρout, hσout]
  exact
    sandwichedRenyi_dataProcessing_le_of_lowAlphaQ_ge
      ρ σ Φ hρ hσ hρΦ hσΦ α (le_of_lt hα_half) hα_lt_one hQ

/-- Full-rank sandwiched Renyi DPI for the complete locally proved parameter
range `(1 / 2 ≤ α ∧ α < 1) ∨ 1 < α`.

This combines the fidelity endpoint, the Gour/Frank--Lieb strict low-`α`
argument, and the Beigi high-`α` weighted Schatten contraction theorem.  The
statement remains the current full-rank `State + PosDef` surface; the public
PSD-reference extension is a separate remaining task. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_half_le_lt_one_or_one_lt_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α
      (by
        rcases hα_range with hlow | hhigh
        · exact hlow.1
        · linarith)
      (by
        rcases hα_range with hlow | hhigh
        · exact ne_of_lt hlow.2
        · exact ne_of_gt hhigh) := by
  rcases hα_range with hlow | hhigh
  · rcases hlow with ⟨hhalf, hlt⟩
    by_cases hEq : α = 1 / 2
    · exact sandwichedRenyi_dataProcessing_channel_statement_of_eq_half_or_one_lt
        ρ σ Φ hρ hσ hρΦ hσΦ α (Or.inl hEq)
    · have hhalf_strict : 1 / 2 < α := by
        exact lt_of_le_of_ne hhalf (Ne.symm hEq)
      exact sandwichedRenyi_dataProcessing_channel_statement_of_half_lt_lt_one_channel
        ρ σ Φ hρ hσ hρΦ hσΦ α hhalf_strict hlt
  · exact sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
      ρ σ Φ hρ hσ hρΦ hσΦ α hhigh

/-- Full-rank sandwiched Renyi DPI for a positive-definite, possibly
non-normalized reference operator.

This is the first source-facing reference-domain extension of the full-rank
channel theorem: the reference is a positive-definite matrix rather than a
normalized `State`.  The proof normalizes the reference by its trace, applies
the already proved full-rank `State + PosDef` channel DPI, and cancels the
identical logarithmic scaling shift on both sides.  Singular PSD references
remain a separate regularization/support-continuity task. -/
theorem sandwichedRenyi_dataProcessing_channel_posDef_reference
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) (σ : CMatrix a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ) hρΦ hσΦ α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) ≤
      sandwichedRenyiReference ρ σ hρ hσ α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) := by
  classical
  let lambda : ℝ := (σ.trace.re)⁻¹
  have htr_pos : 0 < σ.trace.re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).1
  have hlambda_pos : 0 < lambda := by
    exact inv_pos.mpr htr_pos
  have hα_pos : 0 < α := by
    rcases hα_range with hlow | hhigh <;> linarith
  have hα_ne_one : α ≠ 1 := by
    rcases hα_range with hlow | hhigh
    · exact ne_of_lt hlow.2
    · exact ne_of_gt hhigh
  let σ₀ : State a := stateOfPosDefReference σ hσ
  have hσ₀ : σ₀.matrix.PosDef := by
    simpa [σ₀] using stateOfPosDefReference_posDef σ hσ
  have hσ₀Φ : (Φ.applyState σ₀).matrix.PosDef := by
    have hmap :
        (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
      change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
      change Φ.map (((lambda : ℝ) : ℂ) • σ) =
        (((lambda : ℝ) : ℂ) • Φ.map σ)
      simp [lambda]
    rw [hmap]
    exact Matrix.PosDef.smul hσΦ hlambda_pos
  have hDPI :=
    sandwichedRenyi_dataProcessing_channel_statement_of_half_le_lt_one_or_one_lt_channel
      ρ σ₀ Φ hρ hσ₀ hρΦ hσ₀Φ α hα_range
  have hin :
      sandwichedRenyi ρ σ₀ hρ hσ₀ α hα_pos hα_ne_one =
        sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one -
          log2 lambda := by
    rw [← sandwichedRenyiReference_state ρ σ₀ hρ hσ₀ α hα_pos hα_ne_one]
    simpa [σ₀, lambda, stateOfPosDefReference] using
      sandwichedRenyiReference_real_smul_reference
        ρ hρ hσ hlambda_pos α hα_pos hα_ne_one
  have hout :
      sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ₀)
          hρΦ hσ₀Φ α hα_pos hα_ne_one =
        sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
          hρΦ hσΦ α hα_pos hα_ne_one - log2 lambda := by
    rw [← sandwichedRenyiReference_state
      (Φ.applyState ρ) (Φ.applyState σ₀) hρΦ hσ₀Φ α hα_pos hα_ne_one]
    have hmap :
        (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
      change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
      change Φ.map (((lambda : ℝ) : ℂ) • σ) =
        (((lambda : ℝ) : ℂ) • Φ.map σ)
      simp [lambda]
    simpa [hmap] using
      sandwichedRenyiReference_real_smul_reference
        (Φ.applyState ρ) hρΦ hσΦ hlambda_pos α hα_pos hα_ne_one
  have hshift :
      sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
          hρΦ hσΦ α hα_pos hα_ne_one - log2 lambda ≤
        sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one -
          log2 lambda := by
    simpa [sandwichedRenyi_dataProcessing_channel_statement, hin, hout] using hDPI
  linarith

/-- A channel sends the source regularization to the channel-compatible output
regularization `Φ(σ + εI) = Φ(σ) + ε Φ(I)`.

This is the correct Schrödinger-picture form used before taking limits; in
general `Φ(I) ≠ I`, so the output regularization must not be simplified to
`Φ(σ) + εI`. -/
theorem Channel.map_sandwichedRenyiReferenceRegularization
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (σ : CMatrix a) (ε : ℝ) :
    Φ.map (sandwichedRenyiReferenceRegularization σ ε) =
      Φ.map σ + ε • Φ.map (1 : CMatrix a) := by
  change Φ.map (σ + (((ε : ℝ) : ℂ) • (1 : CMatrix a))) =
    Φ.map σ + (((ε : ℝ) : ℂ) • Φ.map (1 : CMatrix a))
  simp [map_add]

/-- Every channel image of a PSD reference is supported by the channel image
of the identity.

This follows by applying support preservation to the trivial input-domain
support condition `σ ≪ I`.  It is the first half of the fixed-output-support
description for the Gour source regularization `Φ(σ + εI)`. -/
theorem Channel.map_supports_map_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (_hσ : σ.PosSemidef) :
    Matrix.Supports (Φ.map σ) (Φ.map (1 : CMatrix a)) := by
  exact channel_map_supports Φ Matrix.PosSemidef.one
    (Matrix.Supports.of_right_posDef σ (1 : CMatrix a) Matrix.PosDef.one)

/-- Every channel output state is fixed by the support projector of `Φ(I)`.

This gives the fixed-output-support side of the high-`α` singular-reference
compression route: all states produced by the channel live on the same support
as the channel image of the identity. -/
theorem Channel.applyState_fixed_by_map_one_supportProjector
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (ρ : State a) :
    let Pi : CMatrix b :=
      psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian *
        (Φ.map (1 : CMatrix a)) *
        psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian
    Pi * (Φ.applyState ρ).matrix = (Φ.applyState ρ).matrix ∧
      (Φ.applyState ρ).matrix * Pi = (Φ.applyState ρ).matrix := by
  exact
    _root_.QIT.supportProjector_fixes_of_supports
      (M := (Φ.applyState ρ).matrix)
      (N := Φ.map (1 : CMatrix a))
      (Φ.applyState ρ).pos
      (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
      (channel_applyState_supports_of_supports ρ Matrix.PosSemidef.one Φ
        (Matrix.Supports.of_right_posDef ρ.matrix (1 : CMatrix a)
          Matrix.PosDef.one))

/-- Every channel output state is supported by the channel image of the
identity. -/
theorem Channel.applyState_supports_map_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (ρ : State a) :
    Matrix.Supports (Φ.applyState ρ).matrix (Φ.map (1 : CMatrix a)) :=
  channel_applyState_supports_of_supports ρ Matrix.PosSemidef.one Φ
    (Matrix.Supports.of_right_posDef ρ.matrix (1 : CMatrix a)
      Matrix.PosDef.one)

/-- The channel-compatible regularized output reference
`Φ(σ + εI)` is supported by `Φ(I)`. -/
theorem Channel.map_regularized_reference_supports_map_one
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (_hε : 0 ≤ ε) :
    Matrix.Supports (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (Φ.map (1 : CMatrix a)) := by
  rw [Channel.map_sandwichedRenyiReferenceRegularization]
  exact Matrix.Supports.add_left
    (Channel.map_supports_map_one Φ hσ)
    (Matrix.Supports.smul_left (((ε : ℝ) : ℂ)
      ) (Matrix.Supports.refl (Φ.map (1 : CMatrix a))))

/-- Conversely, for `ε > 0`, `Φ(I)` is supported by the channel-compatible
regularized output reference `Φ(σ + εI)`.

Thus `Φ(σ + εI)` has the same support as `Φ(I)` for every positive
regularization parameter, even when neither is full-rank on the ambient output
space.  This is the fixed-support domain fact needed before restricting the
high-`α` finite branch to the output support. -/
theorem Channel.map_one_supports_regularized_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports (Φ.map (1 : CMatrix a))
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) := by
  rw [Channel.map_sandwichedRenyiReferenceRegularization]
  exact Matrix.Supports.of_pos_smul_right_add
    (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
    (Φ.mapsPositive σ hσ) hε

/-- The fixed support projector of `Φ(I)` fixes the channel-compatible
regularized output reference `Φ(σ + εI)`.

This is the projector form of
`Channel.map_regularized_reference_supports_map_one`, and is the algebraic
entry point for later restricting the high-`α` finite branch to the fixed
output support of `Φ(I)`. -/
theorem Channel.map_regularized_reference_fixed_by_map_one_supportProjector
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) :
    let Pi : CMatrix b :=
      psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian *
        (Φ.map (1 : CMatrix a)) *
        psdInvSqrt (Φ.map (1 : CMatrix a))
          (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one).isHermitian
    Pi * (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) =
        Φ.map (sandwichedRenyiReferenceRegularization σ ε) ∧
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) * Pi =
        Φ.map (sandwichedRenyiReferenceRegularization σ ε) := by
  exact
    _root_.QIT.supportProjector_fixes_of_supports
      (M := Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (N := Φ.map (1 : CMatrix a))
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ hε))
      (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
      (Channel.map_regularized_reference_supports_map_one Φ hσ hε)

/-- For `ε > 0`, the support projector of `Φ(σ + εI)` fixes `Φ(I)`.

Together with
`Channel.map_regularized_reference_fixed_by_map_one_supportProjector`, this
states that positive source regularization does not change the output support
relative to `Φ(I)`, even when that support is a proper subspace of the ambient
codomain. -/
theorem Channel.map_one_fixed_by_regularized_reference_supportProjector
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    let SigmaEps : CMatrix b := Φ.map (sandwichedRenyiReferenceRegularization σ ε)
    let hSigmaEps : SigmaEps.PosSemidef :=
      Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε))
    let Pi : CMatrix b :=
      psdInvSqrt SigmaEps hSigmaEps.isHermitian * SigmaEps *
        psdInvSqrt SigmaEps hSigmaEps.isHermitian
    Pi * (Φ.map (1 : CMatrix a)) = Φ.map (1 : CMatrix a) ∧
      (Φ.map (1 : CMatrix a)) * Pi = Φ.map (1 : CMatrix a) := by
  exact
    _root_.QIT.supportProjector_fixes_of_supports
      (M := Φ.map (1 : CMatrix a))
      (N := Φ.map (sandwichedRenyiReferenceRegularization σ ε))
      (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one)
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posSemidef hσ (le_of_lt hε)))
      (Channel.map_one_supports_regularized_reference Φ hσ hε)

/-- For every positive source regularization parameter, the channel output
state is supported by the channel-compatible output reference `Φ(σ + εI)`.

This is the domain side needed by the Gour high-`α` finite-branch
regularization route when `Φ(σ + εI)` is singular in the ambient output
space: the output state lives on the fixed support of `Φ(I)`, and for
`ε > 0` that support is contained in the support of `Φ(σ + εI)`. -/
theorem Channel.applyState_supports_map_regularized_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    Matrix.Supports (Φ.applyState ρ).matrix
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) := by
  intro v hv
  exact
    (Channel.applyState_supports_map_one Φ ρ) v
      ((Channel.map_one_supports_regularized_reference Φ hσ hε) v hv)

/-- The channel image of a positive regularized PSD reference is positive
definite when supplied with the positive-definiteness witness required by the
current real-valued reference divergence API.

For arbitrary channels, positive definiteness of `Φ(σ + εI)` is a genuine
support/domain condition.  This theorem deliberately keeps it explicit rather
than assuming the Schrödinger-picture channel is faithful or unital. -/
theorem sandwichedRenyiReference_dataProcessing_channel_regularized
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α)
    {ε : ℝ} (hε : 0 < ε)
    (hσΦε :
      (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef) :
    sandwichedRenyiReference (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        hρΦ hσΦε α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) ≤
      sandwichedRenyiReference ρ (sandwichedRenyiReferenceRegularization σ ε)
        hρ (sandwichedRenyiReferenceRegularization_posDef hσ hε) α
        (by
          rcases hα_range with hlow | hhigh
          · linarith
          · linarith)
        (by
          rcases hα_range with hlow | hhigh
          · exact ne_of_lt hlow.2
          · exact ne_of_gt hhigh) :=
  sandwichedRenyi_dataProcessing_channel_posDef_reference
    ρ (sandwichedRenyiReferenceRegularization σ ε) Φ hρ
    (sandwichedRenyiReferenceRegularization_posDef hσ hε) hρΦ hσΦε α hα_range

/-- Source-facing formulation of the remaining singular-reference limit gate.

The public theorem allows an arbitrary PSD reference.  The source proves this
from the positive-definite theorem by taking `ε → 0+` along
`σ_ε = σ + εI` and the channel-compatible output path `Φ(σ_ε)`.  This predicate
records the two one-sided convergence obligations needed to turn a family of
regularized positive-definite divergence inequalities into the singular PSD
statement.  The actual regularized divergence curves are parameters so that
their domain witnesses can be supplied by the caller without pretending that
`sandwichedRenyiReference` already has a singular-PSD semantics. -/
def sandwichedRenyiReferenceRegularizationLimitGate
    (regularizedIn regularizedOut : ℝ → ℝ) (DIn DOut : ℝ) : Prop :=
  Filter.Tendsto regularizedIn (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds DIn) ∧
    Filter.Tendsto regularizedOut (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds DOut)

/-- If a regularized source-facing singular-reference gate has pointwise
regularized DPI near `0+`, then the limiting singular-reference quantities
inherit the DPI inequality.

This is the exact order-theoretic handoff still needed after source
regularization: all analytic content is in the two convergence assumptions and
the eventual regularized inequality. -/
theorem sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le
    {regularizedIn regularizedOut : ℝ → ℝ} {DIn DOut : ℝ}
    (hgate :
      sandwichedRenyiReferenceRegularizationLimitGate
        regularizedIn regularizedOut DIn DOut)
    (hle : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      regularizedOut ε ≤ regularizedIn ε) :
    DOut ≤ DIn :=
  le_of_tendsto_of_tendsto hgate.2 hgate.1 hle

/-- Input-side regularized sandwiched Renyi divergence curve
`ε ↦ D̃_α(ρ || σ + εI)`.

The `if` branch keeps the function total on `ℝ`; along the source filter
`ε → 0+` it always unfolds to the positive-definite branch. -/
def sandwichedRenyiReferenceRegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hρ : ρ.matrix.PosDef) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then
    sandwichedRenyiReference ρ (sandwichedRenyiReferenceRegularization σ ε)
      hρ (sandwichedRenyiReferenceRegularization_posDef hσ hε)
      α hα_pos hα_ne_one
  else
    0

/-- Output-side channel-compatible regularized sandwiched Renyi divergence
curve `ε ↦ D̃_α(Φρ || Φ(σ + εI))`.

The output positive-definiteness witness is deliberately checked in the branch:
not every Schrödinger-picture channel maps positive definite references to
positive definite references unless a support/faithfulness hypothesis is
available. -/
def sandwichedRenyiReferenceRegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (ε : ℝ) : ℝ :=
  by
    classical
    exact
      if hσΦε : (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef then
        sandwichedRenyiReference (Φ.applyState ρ)
          (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          hρΦ hσΦε α hα_pos hα_ne_one
      else
        0

/-- The positive-definite theorem supplies pointwise DPI for the source
regularized input/output divergence curves, eventually along `ε → 0+`. -/
theorem sandwichedRenyiReferenceRegularizedCurves_eventually_le
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiReferenceRegularizedOutputCurve ρ Φ hρΦ α
          (σ := σ)
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh) ε ≤
        sandwichedRenyiReferenceRegularizedInputCurve ρ hρ hσ α
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh) ε := by
  filter_upwards [self_mem_nhdsWithin, hσΦε] with ε hε_mem hσΦε_pos
  have hε_pos : 0 < ε := hε_mem
  simp [sandwichedRenyiReferenceRegularizedInputCurve,
    sandwichedRenyiReferenceRegularizedOutputCurve, hε_pos, hσΦε_pos]
  exact
    sandwichedRenyiReference_dataProcessing_channel_regularized
      ρ hσ Φ hρ hρΦ α hα_range hε_pos hσΦε_pos

/-- Source-regularization reduction of the singular PSD-reference theorem.

If the two source regularized curves converge to the intended singular-reference
input/output quantities and the output regularized references are eventually in
the current positive-definite divergence domain, the singular-reference DPI
follows from the already proved positive-definite regularized theorem. -/
theorem sandwichedRenyiReference_dataProcessing_channel_of_regularizationLimitGate
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α)
    (DIn DOut : ℝ)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef)
    (hgate :
      sandwichedRenyiReferenceRegularizationLimitGate
        (sandwichedRenyiReferenceRegularizedInputCurve ρ hρ hσ α
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh))
        (sandwichedRenyiReferenceRegularizedOutputCurve ρ Φ hρΦ α
          (σ := σ)
          (by
            rcases hα_range with hlow | hhigh
            · linarith
            · linarith)
          (by
            rcases hα_range with hlow | hhigh
            · exact ne_of_lt hlow.2
            · exact ne_of_gt hhigh))
        DIn DOut) :
    DOut ≤ DIn :=
  sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le hgate
    (sandwichedRenyiReferenceRegularizedCurves_eventually_le
      ρ hσ Φ hρ hρΦ α hα_range hσΦε)

/-- The finite strict low-`α` PSD-reference branch satisfies the source
regularization limit gate without any output positive-definiteness assumption.

This is the regularized-limit version of the Gour/Frank--Lieb `Q` route:
because `1 / 2 < α < 1` uses only positive powers, both
`D̃_α(ρ || σ + εI)` and `D̃_α(Φρ || Φ(σ + εI))` converge to the finite
PSD-reference branch whenever the limiting input `Q` value is positive.  The
output positivity needed for `log` follows from the already proved
`Q_α(ρ,σ) ≤ Q_α(Φρ,Φσ)` inequality. -/
theorem sandwichedRenyiPSDReferenceLowAlpha_regularizationLimitGate
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    sandwichedRenyiReferenceRegularizationLimitGate
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve ρ hσ α)
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve ρ hσ Φ α)
      (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α)
      (sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α) := by
  have hQ :=
    sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
      ρ hσ Φ α hα_half hα_lt_one
  have hQout_pos :
      0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α :=
    lt_of_lt_of_le hQpos hQ
  exact
    ⟨sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve_tendsto
        ρ hσ α hα_half hα_lt_one hQpos,
      sandwichedRenyiPSDReferenceLowAlphaRegularizedOutputCurve_tendsto
        ρ hσ Φ α hα_half hα_lt_one hQout_pos⟩

/-- Source-regularization proof of strict low-`α` DPI for the finite PSD
reference branch.

This packages the Gour/Frank--Lieb `Q`-functional DPI in the same shape as the
singular-reference source proof: prove the inequality for the regularized
references `σ + εI`, take `ε → 0+`, and use the finite low-`α` limit gate. -/
theorem sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_of_sourceRegularization
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α) :
    sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α := by
  exact
    sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le
      (sandwichedRenyiPSDReferenceLowAlpha_regularizationLimitGate
        ρ hσ Φ α hα_half hα_lt_one hQpos)
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedCurves_eventually_le
        ρ hσ Φ α hα_half hα_lt_one)

/-- Extended-real strict low-`α` PSD-reference sandwiched Renyi branch.

For `1 / 2 < α < 1`, the source defines singular references through the
positive-power `Q_α` functional.  If `Q_α(ρ, σ) = 0`, the logarithmic branch is
`+∞` because the prefactor `1 / (α - 1)` is negative; otherwise this agrees
with the finite real branch `sandwichedRenyiPSDReferenceLowAlpha`. -/
def sandwichedRenyiPSDReferenceLowAlphaE
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : EReal :=
  if sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α = 0 then
    ⊤
  else
    (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α : EReal)

@[simp]
theorem sandwichedRenyiPSDReferenceLowAlphaE_eq_top_of_Q_eq_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hQzero : sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α = 0) :
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α = ⊤ := by
  simp [sandwichedRenyiPSDReferenceLowAlphaE, hQzero]

@[simp]
theorem sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hQne : sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α ≠ 0) :
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α =
      (sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α : EReal) := by
  simp [sandwichedRenyiPSDReferenceLowAlphaE, hQne]

/-- If the strict low-`α` PSD-reference `Q` value is nonzero, it is positive. -/
theorem sandwichedRenyiQ_pos_of_ne_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ)
    (hQne : sandwichedRenyiQ ρ σ hρ hσ α ≠ 0) :
    0 < sandwichedRenyiQ ρ σ hρ hσ α := by
  have hQnonneg := sandwichedRenyiQ_nonneg hρ hσ α
  rcases lt_or_eq_of_le hQnonneg with hQpos | hQzero
  · exact hQpos
  · exact False.elim (hQne hQzero.symm)

/-- Normalize a nonzero PSD reference matrix into a density state.

This is the PSD analogue of `stateOfPosDefReference`, kept local to the
Frank--Lieb PSD-reference endpoint so that the `α = 1/2` argument can use the
already proved normalized-state fidelity monotonicity theorem. -/
def stateOfPSDReference [Nonempty a] (σ : CMatrix a) (hσ : σ.PosSemidef)
    (htr : 0 < σ.trace.re) : State a where
  matrix := (σ.trace.re)⁻¹ • σ
  pos := by
    exact Matrix.PosSemidef.smul hσ (inv_nonneg.mpr (le_of_lt htr))
  trace_eq_one := by
    have htr_im : σ.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hσ).2.symm
    rw [Matrix.trace_smul]
    apply Complex.ext
    · simp [Complex.real_smul, ne_of_gt htr]
    · simp [Complex.real_smul, htr_im]

@[simp]
theorem stateOfPSDReference_matrix [Nonempty a] (σ : CMatrix a)
    (hσ : σ.PosSemidef) (htr : 0 < σ.trace.re) :
    (stateOfPSDReference σ hσ htr).matrix = (σ.trace.re)⁻¹ • σ :=
  rfl

/-- At `α = 1/2`, scaling the PSD reference by a positive real scales
`Q_{1/2}` by the square root of the scalar. -/
theorem sandwichedRenyiQ_real_smul_reference_half
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    sandwichedRenyiQ ρ.matrix (lambda • σ : CMatrix a)
        ρ.pos (Matrix.PosSemidef.smul hσ (le_of_lt hlambda)) (1 / 2 : ℝ) =
      lambda ^ (1 / 2 : ℝ) *
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) := by
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
  have hscale :=
    sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
      ρ hσ hlambda_nonneg (1 / 2 : ℝ)
  have hfactor :
      ((lambda ^ ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ))) *
          lambda ^ ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)))) ^
          (1 / 2 : ℝ)) =
        lambda ^ (1 / 2 : ℝ) := by
    have hs : (1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    have hmul : lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) = lambda := by
      calc
        lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) =
            lambda ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
              rw [Real.rpow_add hlambda]
        _ = lambda := by norm_num
    rw [hs, hmul]
  have hfactor' :
      ((lambda ^ (1 - (1 / 2 : ℝ)) *
          lambda ^ (1 - (1 / 2 : ℝ))) ^
          (1 / 2 : ℝ)) =
        lambda ^ (1 / 2 : ℝ) := by
    have hone_sub : 1 - (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
      norm_num
    have hmul : lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) = lambda := by
      calc
        lambda ^ (1 / 2 : ℝ) * lambda ^ (1 / 2 : ℝ) =
            lambda ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
              rw [Real.rpow_add hlambda]
        _ = lambda := by norm_num
    rw [hone_sub, hmul]
  have hfactor_two :
      ((lambda ^ (1 - (2 : ℝ)⁻¹) *
          lambda ^ (1 - (2 : ℝ)⁻¹)) ^
          ((2 : ℝ)⁻¹)) =
        lambda ^ ((2 : ℝ)⁻¹) := by
    have hone_sub : 1 - (2 : ℝ)⁻¹ = ((2 : ℝ)⁻¹) := by
      norm_num
    have hmul : lambda ^ ((2 : ℝ)⁻¹) * lambda ^ ((2 : ℝ)⁻¹) = lambda := by
      calc
        lambda ^ ((2 : ℝ)⁻¹) * lambda ^ ((2 : ℝ)⁻¹) =
            lambda ^ (((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) := by
              rw [Real.rpow_add hlambda]
        _ = lambda := by norm_num
    rw [hone_sub, hmul]
  rw [sandwichedRenyiQ_eq_psdTracePower_referenceInner,
    sandwichedRenyiQ_eq_psdTracePower_referenceInner]
  exact hscale.trans (by
    dsimp
    rw [hfactor])

/-- The low-`α` `Q` functional vanishes at the endpoint `α = 1/2` when the
reference matrix is zero. -/
theorem sandwichedRenyiQ_zero_right_half (ρ : State a) :
    sandwichedRenyiQ ρ.matrix (0 : CMatrix a) ρ.pos Matrix.PosSemidef.zero
      (1 / 2 : ℝ) = 0 := by
  have hs : (1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
    norm_num
  have hzero :
      CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) = 0 := by
    simpa using
      (CFC.zero_rpow (A := CMatrix a) (x := (1 / 2 : ℝ)) (by norm_num))
  have hzero_two :
      CFC.rpow (0 : CMatrix a) ((2 : ℝ)⁻¹) = 0 := by
    simpa using
      (CFC.zero_rpow (A := CMatrix a) (x := ((2 : ℝ)⁻¹)) (by norm_num))
  have hzero_sub :
      CFC.rpow (0 : CMatrix a) (1 - (2 : ℝ)⁻¹) = 0 := by
    simpa using
      (CFC.zero_rpow (A := CMatrix a) (x := (1 - (2 : ℝ)⁻¹)) (by norm_num))
  unfold sandwichedRenyiQ
  dsimp
  rw [hs]
  change
    (CFC.rpow
      (CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) * ρ.matrix *
        CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ))
      (1 / 2 : ℝ)).trace.re = 0
  have hinner_zero :
      CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) * ρ.matrix *
          CFC.rpow (0 : CMatrix a) (1 / 2 : ℝ) = 0 := by
    rw [hzero]
    simp
  rw [hinner_zero, hzero]
  simp

/-- Endpoint `α = 1/2` `Q`-functional data processing for a channel acting on
a state and a PSD matrix reference with positive trace.

The proof normalizes the PSD reference, applies the normalized-state fidelity
monotonicity theorem, and cancels the common square-root trace factor. -/
theorem sandwichedRenyiQ_dataProcessing_channel_reference_half_of_trace_pos
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (htr : 0 < σ.trace.re) :
    sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) ≤
      sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
        (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := by
  classical
  letI : Nonempty a := ρ.nonempty
  let lambda : ℝ := (σ.trace.re)⁻¹
  have hlambda_pos : 0 < lambda := inv_pos.mpr htr
  let σ₀ : State a := stateOfPSDReference σ hσ htr
  have hmap :
      (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
    change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
    change Φ.map (((lambda : ℝ) : ℂ) • σ) =
      (((lambda : ℝ) : ℂ) • Φ.map σ)
    simp [lambda]
  have hin_scale :
      sandwichedRenyiQ ρ.matrix σ₀.matrix ρ.pos σ₀.pos (1 / 2 : ℝ) =
        lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) := by
    simpa [σ₀, lambda, stateOfPSDReference] using
      sandwichedRenyiQ_real_smul_reference_half ρ hσ hlambda_pos
  have hout_scale :
      sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ₀).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ₀).pos (1 / 2 : ℝ) =
        lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := by
    simpa [hmap, sandwichedRenyiQ] using
      sandwichedRenyiQ_real_smul_reference_half
        (Φ.applyState ρ) (Φ.mapsPositive σ hσ) hlambda_pos
  have hfid_sq := State.squaredFidelity_le_applyState_squaredFidelity Φ ρ σ₀
  have hfid :
      ρ.fidelity σ₀ ≤ (Φ.applyState ρ).fidelity (Φ.applyState σ₀) := by
    rw [State.squaredFidelity_eq_fidelity_sq,
      State.squaredFidelity_eq_fidelity_sq] at hfid_sq
    exact (sq_le_sq₀ (State.fidelity_nonneg ρ σ₀)
      (State.fidelity_nonneg (Φ.applyState ρ) (Φ.applyState σ₀))).mp hfid_sq
  have hQ_state :
      sandwichedRenyiQ ρ.matrix σ₀.matrix ρ.pos σ₀.pos (1 / 2 : ℝ) ≤
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ₀).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ₀).pos (1 / 2 : ℝ) := by
    rw [sandwichedRenyiQ_eq_psdTracePower_inner,
      sandwichedRenyiInner_psdTracePower_half_eq_fidelity,
      sandwichedRenyiQ_eq_psdTracePower_inner,
      sandwichedRenyiInner_psdTracePower_half_eq_fidelity]
    exact hfid
  have hscaled :
      lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) ≤
        lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := by
    calc
      lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) =
          sandwichedRenyiQ ρ.matrix σ₀.matrix ρ.pos σ₀.pos (1 / 2 : ℝ) := hin_scale.symm
      _ ≤ sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ₀).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ₀).pos (1 / 2 : ℝ) := hQ_state
      _ = lambda ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) := hout_scale
  exact le_of_mul_le_mul_left hscaled
    (Real.rpow_pos_of_pos hlambda_pos (1 / 2 : ℝ))

/-- Endpoint `α = 1/2` finite-branch PSD-reference DPI, conditional on the
input endpoint `Q` value being positive. -/
theorem sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_half
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (htr : 0 < σ.trace.re)
    (hQpos : 0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ)) :
    sandwichedRenyiPSDReferenceLowAlpha
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≤
      sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ (1 / 2 : ℝ) := by
  have hQmono :=
    sandwichedRenyiQ_dataProcessing_channel_reference_half_of_trace_pos
      ρ hσ Φ htr
  unfold sandwichedRenyiPSDReferenceLowAlpha
  have hlog := frankLieb_log2_mono_of_pos hQpos hQmono
  have hcoef : 1 / ((1 / 2 : ℝ) - 1) = -2 := by norm_num
  rw [hcoef]
  exact mul_le_mul_of_nonpos_left hlog (by norm_num)

/-- Endpoint `α = 1/2` DPI for the extended-real PSD-reference low-`α`
branch. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel_half
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b) :
    sandwichedRenyiPSDReferenceLowAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≤
      sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ (1 / 2 : ℝ) := by
  by_cases hQin_zero :
      sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) = 0
  · rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_top_of_Q_eq_zero
      ρ hσ (1 / 2 : ℝ) hQin_zero]
    exact le_top
  · have hQin_pos :
        0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) :=
      sandwichedRenyiQ_pos_of_ne_zero ρ.pos hσ (1 / 2 : ℝ) hQin_zero
    have hσ_ne_zero : σ ≠ 0 := by
      intro hσzero
      exact hQin_zero (by
        simpa [hσzero] using sandwichedRenyiQ_zero_right_half ρ)
    have htr_ne : σ.trace.re ≠ 0 := by
      intro htr_zero
      have htrace_zero : σ.trace = 0 := by
        apply Complex.ext
        · simpa using htr_zero
        · simp [(Matrix.PosSemidef.trace_nonneg hσ).2.symm]
      exact hσ_ne_zero ((Matrix.PosSemidef.trace_eq_zero_iff hσ).mp htrace_zero)
    have htr_pos : 0 < σ.trace.re := by
      exact lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hσ).1 (Ne.symm htr_ne)
    have hQmono :
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ (1 / 2 : ℝ) ≤
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) :=
      sandwichedRenyiQ_dataProcessing_channel_reference_half_of_trace_pos
        ρ hσ Φ htr_pos
    have hQout_pos :
        0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) :=
      lt_of_lt_of_le hQin_pos hQmono
    have hQout_ne :
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≠ 0 :=
      ne_of_gt hQout_pos
    have hDPI :
        sandwichedRenyiPSDReferenceLowAlpha
            (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) ≤
          sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ (1 / 2 : ℝ) :=
      sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_half
        ρ hσ Φ htr_pos hQin_pos
    rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
        (Φ.applyState ρ) (Φ.mapsPositive σ hσ) (1 / 2 : ℝ) hQout_ne,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
        ρ hσ (1 / 2 : ℝ) hQin_zero]
    exact_mod_cast hDPI

/-- Strict low-`α` DPI for the extended-real PSD-reference branch.

This is the singular-reference continuation of the Gour/Frank--Lieb
`Q`-functional route.  When the input `Q` value is zero the right side is
`+∞`; otherwise the already proved finite branch applies, and the
`Q`-monotonicity theorem makes the output branch finite as well. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiPSDReferenceLowAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α := by
  by_cases hQin_zero : sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α = 0
  · simp [sandwichedRenyiPSDReferenceLowAlphaE, hQin_zero]
  · have hQin_pos :
        0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α :=
      sandwichedRenyiQ_pos_of_ne_zero ρ.pos hσ α hQin_zero
    have hQmono :
        sandwichedRenyiQ ρ.matrix σ ρ.pos hσ α ≤
          sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
            (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α :=
      sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
        ρ hσ Φ α hα_half hα_lt_one
    have hQout_pos :
        0 < sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α :=
      lt_of_lt_of_le hQin_pos hQmono
    have hQout_ne :
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.map σ)
          (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ) α ≠ 0 :=
      ne_of_gt hQout_pos
    have hDPI :
        sandwichedRenyiPSDReferenceLowAlpha
            (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
          sandwichedRenyiPSDReferenceLowAlpha ρ σ hσ α :=
      sandwichedRenyiPSDReferenceLowAlpha_dataProcessing_channel_of_sourceRegularization
        ρ hσ Φ α hα_half hα_lt_one hQin_pos
    simp [sandwichedRenyiPSDReferenceLowAlphaE, hQin_zero, hQout_ne,
      EReal.coe_le_coe_iff, hDPI]

/-- On positive-definite references, the extended-real strict low-`α`
PSD-reference branch agrees with the existing real-valued reference divergence.

This is the audit bridge between the source-facing PSD semantics and the
pre-existing `sandwichedRenyiReference` API. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_reference_posDef
    (ρ : State a) {σ : CMatrix a}
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ.posSemidef α =
      (sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one : EReal) := by
  have hQpos := sandwichedRenyiQ_pos_of_state_posDef_reference ρ hσ α
  have hQne :
      sandwichedRenyiQ ρ.matrix σ ρ.pos hσ.posSemidef α ≠ 0 :=
    ne_of_gt hQpos
  rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
    ρ hσ.posSemidef α hQne]
  simp [sandwichedRenyiPSDReferenceLowAlpha_eq_reference_posDef
    ρ hρ hσ α hα_pos hα_ne_one]

/-- Finite support-branch formula for the high-`α` PSD-reference sandwiched
Renyi divergence.

For `α > 1`, the source statement uses the usual support convention:
`D̃_α(ρ || σ) = +∞` unless the support of `ρ` is contained in the support of
`σ`.  This real-valued helper is the finite branch, written with the existing
matrix-reference inner operator and PSD trace-power API.  The extended-real
wrapper below supplies the support-domain split. -/
def sandwichedRenyiPSDReferenceHighAlphaFinite
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : ℝ :=
  (1 / (α - 1)) *
    log2 (psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
      (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) α)

/-- Scaling a positive-definite matrix reference shifts the high-`α`
finite PSD-reference branch by the logarithm of the scaling factor.

Unlike `sandwichedRenyiReference_real_smul_reference`, this finite-branch
version does not need the input state to be positive definite.  It is the
scaling step needed to pass the Beigi finite-branch theorem from normalized
state references to arbitrary positive-definite matrix references. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosDef)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ
        (lambda • σ : CMatrix a)
        (Matrix.PosDef.smul hσ hlambda).posSemidef α =
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α -
        log2 lambda := by
  let s : ℝ := (1 - α) / (2 * α)
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hα_ne_one : α ≠ 1 := ne_of_gt hα
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
  have htrace_scale :
      psdTracePower
          (sandwichedRenyiReferenceInner ρ (lambda • σ : CMatrix a) α)
          (sandwichedRenyiReferenceInner_posSemidef ρ
            (Matrix.PosDef.smul hσ hlambda).posSemidef α)
          α =
        ((lambda ^ s * lambda ^ s) ^ α) *
          psdTracePower
            (sandwichedRenyiReferenceInner ρ σ α)
            (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
            α := by
    simpa [s] using
      sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
        ρ hσ.posSemidef hlambda_nonneg α
  have hfactor :
      (lambda ^ s * lambda ^ s) ^ α = lambda ^ (1 - α) := by
    have hmul : lambda ^ s * lambda ^ s = lambda ^ (s + s) := by
      rw [Real.rpow_add hlambda]
    calc
      (lambda ^ s * lambda ^ s) ^ α = (lambda ^ (s + s)) ^ α := by
        rw [hmul]
      _ = lambda ^ ((s + s) * α) := by
        rw [← Real.rpow_mul hlambda_nonneg]
      _ = lambda ^ (1 - α) := by
        congr 1
        dsimp [s]
        field_simp [ne_of_gt hα_pos]
        ring_nf
  have hfactor_pos : 0 < lambda ^ (1 - α) :=
    Real.rpow_pos_of_pos hlambda _
  have hTpos :
      0 <
        psdTracePower
          (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
          α :=
    sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
      ρ hσ α
  have hlog_factor : log2 (lambda ^ (1 - α)) = (1 - α) * log2 lambda := by
    unfold log2
    rw [Real.log_rpow hlambda]
    ring
  have hcoef :
      (1 / (α - 1)) * ((1 - α) * log2 lambda) = -log2 lambda := by
    field_simp [hα_ne_one]
    ring
  simp only [sandwichedRenyiPSDReferenceHighAlphaFinite]
  rw [htrace_scale, hfactor]
  rw [log2_mul (ne_of_gt hfactor_pos) (ne_of_gt hTpos), hlog_factor]
  rw [mul_add, hcoef]
  ring

/-- High-`α` finite PSD-reference branch DPI for a positive-definite normalized
reference.

This is the Beigi weighted-Schatten contraction in finite-branch form.  It
does not require the input state, or its channel output, to be full-rank; only
the reference and the channel output reference are required to be
positive-definite. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_stateReference_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : State a) (Φ : Channel a b)
    (hσ : σ.matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.applyState σ).matrix (Φ.applyState σ).pos α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ.matrix σ.pos α := by
  have hpower :=
    sandwichedRenyiInner_tracePower_le_of_one_lt_channel
      ρ σ Φ hσ hσΦ α hα
  have hout_pos :
      0 <
        psdTracePower
          (sandwichedRenyiReferenceInner
            (Φ.applyState ρ) (Φ.applyState σ).matrix α)
          (sandwichedRenyiReferenceInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ).pos α)
          α := by
    simpa [sandwichedRenyiInner, sandwichedRenyiReferenceInner] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        (Φ.applyState ρ) (σ := (Φ.applyState σ).matrix) hσΦ α
  have hlog :
      log2
          (psdTracePower
            (sandwichedRenyiReferenceInner
              (Φ.applyState ρ) (Φ.applyState σ).matrix α)
            (sandwichedRenyiReferenceInner_posSemidef
              (Φ.applyState ρ) (Φ.applyState σ).pos α)
            α) ≤
        log2
          (psdTracePower (sandwichedRenyiReferenceInner ρ σ.matrix α)
            (sandwichedRenyiReferenceInner_posSemidef ρ σ.pos α) α) := by
    exact frankLieb_log2_mono_of_pos hout_pos (by
      simpa [sandwichedRenyiInner, sandwichedRenyiReferenceInner] using hpower)
  have hcoef_nonneg : 0 ≤ 1 / (α - 1) := by
    exact le_of_lt (one_div_pos.2 (sub_pos.mpr hα))
  simpa [sandwichedRenyiPSDReferenceHighAlphaFinite] using
    mul_le_mul_of_nonneg_left hlog hcoef_nonneg

/-- High-`α` finite PSD-reference branch DPI for a positive-definite,
possibly non-normalized reference operator.

This extends the normalized-state-reference Beigi finite branch by normalizing
the reference, applying the state-reference theorem, and cancelling the same
`-log₂ λ` scaling shift on input and output.  The singular supported PSD
finite branch remains a separate support-compression/continuity step. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hσ : σ.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α := by
  classical
  let lambda : ℝ := (σ.trace.re)⁻¹
  have htr_pos : 0 < σ.trace.re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).1
  have hlambda_pos : 0 < lambda := by
    exact inv_pos.mpr htr_pos
  let σ₀ : State a := stateOfPosDefReference σ hσ
  have hσ₀ : σ₀.matrix.PosDef := by
    simpa [σ₀] using stateOfPosDefReference_posDef σ hσ
  have hmap :
      (Φ.applyState σ₀).matrix = lambda • Φ.map σ := by
    change Φ.map (lambda • σ : CMatrix a) = lambda • Φ.map σ
    change Φ.map (((lambda : ℝ) : ℂ) • σ) =
      (((lambda : ℝ) : ℂ) • Φ.map σ)
    simp [lambda]
  have hσ₀Φ : (Φ.applyState σ₀).matrix.PosDef := by
    rw [hmap]
    exact Matrix.PosDef.smul hσΦ hlambda_pos
  have hDPI :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_stateReference_posDef
      ρ σ₀ Φ hσ₀ hσ₀Φ α hα
  have hin :
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ₀.matrix σ₀.pos α =
        sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α -
          log2 lambda := by
    simpa [σ₀, lambda, stateOfPosDefReference] using
      sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
        ρ hσ hlambda_pos α hα
  have hout :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.applyState σ₀).matrix
          (Φ.applyState σ₀).pos α =
        sandwichedRenyiPSDReferenceHighAlphaFinite
            (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α -
          log2 lambda := by
    simpa [hmap, lambda] using
      sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
        (Φ.applyState ρ) hσΦ hlambda_pos α hα
  have hshift :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α - log2 lambda ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α -
          log2 lambda := by
    simpa [hin, hout] using hDPI
  linarith

/-- Input-side source regularization curve for the finite high-`α`
PSD-reference branch.

The branch is total on `ℝ`; along the source filter `ε → 0+`, it unfolds to the
finite branch for the positive-definite reference `σ + εI`. -/
def sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ
      (sandwichedRenyiReferenceRegularization σ ε)
      (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α
  else
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α

/-- The input-side high-`α` finite branch regularization curve converges to
the supported singular-reference finite branch.

This is the source-side limit needed by the Gour/source support-domain
regularization route. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve_tendsto_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα : 1 < α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve ρ hσ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have htrace :=
    sandwichedRenyiReferenceInner_tracePower_regularization_tendsto_of_supports
      ρ hσ hSupport α hα_pos
  have htarget_pos :
      0 <
        ((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re := by
    simpa [psdTracePower] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
        ρ hσ hSupport α
  have hlog :
      Filter.Tendsto
        (fun ε : ℝ =>
          log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner ρ
                (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (log2 (((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re))) := by
    have hrawLog := Filter.Tendsto.log htrace (ne_of_gt htarget_pos)
    simpa [log2] using
      hrawLog.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hraw :
      Filter.Tendsto
        (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner ρ
                  (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((1 / (α - 1)) *
            log2
              (((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re))) :=
    tendsto_const_nhds.mul hlog
  have hcurve :
      (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner ρ
                  (sandwichedRenyiReferenceRegularization σ ε) α) α).trace).re))
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve ρ hσ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : 0 < ε := hε
    simp [sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve,
      sandwichedRenyiPSDReferenceHighAlphaFinite, psdTracePower, hε_pos]
  exact Filter.Tendsto.congr' hcurve hraw

/-- The high-`α` raw power trace of the matrix-reference inner operator is
continuous along positive-definite reference paths.

This is the positive-definite counterpart of
`sandwichedRenyiReferenceInner_tracePower_regularization_tendsto_of_supports`:
when the limiting reference is already full-rank, the negative reference power
in the high-`α` inner operator is handled by CFC continuity on the
positive-definite cone. -/
theorem sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_reference
    {X : Type*} {l : Filter X} (ρ : State a)
    {σF : X → CMatrix a} {σ : CMatrix a}
    (hσF : Filter.Tendsto σF l (nhds σ))
    (hσFpd : ∀ᶠ x in l, (σF x).PosDef)
    (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) :
    Filter.Tendsto
      (fun x : X =>
        (((CFC.rpow (sandwichedRenyiReferenceInner ρ (σF x) α) α).trace).re))
      l
      (nhds
        (((CFC.rpow (sandwichedRenyiReferenceInner ρ σ α) α).trace).re)) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hpow :
      Filter.Tendsto (fun x : X => CFC.rpow (σF x) s) l
        (nhds (CFC.rpow σ s)) :=
    _root_.QIT.cMatrix_rpow_tendsto_of_tendsto_posDef s hσF hσFpd hσ
  have hinner :
      Filter.Tendsto (fun x : X => sandwichedRenyiReferenceInner ρ (σF x) α)
        l (nhds (sandwichedRenyiReferenceInner ρ σ α)) := by
    unfold sandwichedRenyiReferenceInner
    exact (hpow.mul tendsto_const_nhds).mul hpow
  have hinner_psd :
      ∀ᶠ x in l, (sandwichedRenyiReferenceInner ρ (σF x) α).PosSemidef := by
    exact hσFpd.mono fun x hx =>
      sandwichedRenyiReferenceInner_posSemidef ρ hx.posSemidef α
  exact
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      hα_pos hinner hinner_psd
      (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)

/-- Output-side channel-compatible source regularization curve for the finite
high-`α` PSD-reference branch.

The output reference is `Φ(σ + εI)`, not `Φσ + εI`.  The current high-`α`
finite theorem requires a positive-definite output reference, so the total
curve carries that witness in its positive branch and falls back to the
unregularized finite expression outside the verified domain. -/
def sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) (ε : ℝ) : ℝ := by
  classical
  exact
    if hσΦε : (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef then
      sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        hσΦε.posSemidef α
    else
      sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
        (Φ.map σ) (Φ.mapsPositive σ hσ) α

/-- If the channel output of the unregularized reference is already
positive-definite, then the channel-compatible source regularization remains
positive-definite for every `ε ≥ 0`.

This is a small reusable domain lemma for the high-`α` source-regularized
finite branch.  It deliberately assumes positivity of `Φσ`; arbitrary channels
need a separate support-compression argument when `Φσ` is singular. -/
theorem Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) {σ : CMatrix a} (_hσ : σ.PosSemidef)
    (hσΦ : (Φ.map σ).PosDef) {ε : ℝ} (hε : 0 ≤ ε) :
    (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef := by
  rw [Channel.map_sandwichedRenyiReferenceRegularization]
  exact hσΦ.add_posSemidef
      (Matrix.PosSemidef.smul
        (Φ.mapsPositive (1 : CMatrix a) Matrix.PosSemidef.one) hε)

/-- The output-side high-`α` finite branch regularization curve converges when
the limiting output reference is already positive definite.

This closes the source-regularized Gour route in the faithful-output
subcase.  The genuinely singular-output case remains separate because
`Φ(σ + εI) = Φσ + ε ΦI` need not be full-rank. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve_tendsto_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
        ρ hσ Φ α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let σF : ℝ → CMatrix b := fun ε =>
    if hε : 0 ≤ ε then
      Φ.map (sandwichedRenyiReferenceRegularization σ ε)
    else
      Φ.map σ
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hσF_pd : ∀ ε, (σF ε).PosDef := by
    intro ε
    by_cases hε : 0 ≤ ε
    · simpa [σF, hε] using
        Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
          Φ hσ hσΦ hε
    · simpa [σF, hε] using hσΦ
  have hσF_tend : Filter.Tendsto σF l (nhds (Φ.map σ)) := by
    have hreg := sandwichedRenyiReferenceRegularization_tendsto (a := a) σ
    have hmap :
        Filter.Tendsto
          (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          l (nhds (Φ.map σ)) :=
      (LinearMap.continuous_of_finiteDimensional Φ.map).tendsto σ |>.comp hreg
    have hcongr :
        (fun ε : ℝ => Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          =ᶠ[l] σF := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      simp [σF, hε_nonneg]
    exact Filter.Tendsto.congr' hcongr hmap
  have htrace :=
    sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_reference
      (Φ.applyState ρ) hσF_tend
      (Filter.Eventually.of_forall (fun ε => hσF_pd ε)) hσΦ α hα_pos
  have htarget_pos :
      0 <
        (((CFC.rpow
          (sandwichedRenyiReferenceInner (Φ.applyState ρ) (Φ.map σ) α)
          α).trace).re) := by
    simpa [psdTracePower] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        (Φ.applyState ρ) hσΦ α
  have hlog :
      Filter.Tendsto
        (fun ε : ℝ =>
          log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner (Φ.applyState ρ) (σF ε) α)
              α).trace).re))
        l
        (nhds
          (log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner (Φ.applyState ρ) (Φ.map σ) α)
              α).trace).re))) := by
    have hrawLog := Filter.Tendsto.log htrace (ne_of_gt htarget_pos)
    simpa [log2] using
      hrawLog.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hraw :
      Filter.Tendsto
        (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner (Φ.applyState ρ) (σF ε) α)
                α).trace).re))
        l
        (nhds
          ((1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner (Φ.applyState ρ) (Φ.map σ) α)
                α).trace).re))) :=
    hlog.const_mul (1 / (α - 1))
  have hcurve :
      (fun ε : ℝ =>
          (1 / (α - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner (Φ.applyState ρ) (σF ε) α)
                α).trace).re))
        =ᶠ[l]
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
        ρ hσ Φ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : 0 < ε := hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
    have hσFε_pos :
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef :=
      Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
        Φ hσ hσΦ hε_nonneg
    simp [sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve,
      sandwichedRenyiPSDReferenceHighAlphaFinite, psdTracePower, σF,
      hε_nonneg, hσFε_pos]
  exact Filter.Tendsto.congr' hcurve hraw

/-- The high-`α` finite PSD-reference source-regularized curves satisfy
eventual DPI whenever the regularized output references are eventually in the
positive-definite domain of the already proved Beigi/Gour finite theorem. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
          ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
          ρ hσ α ε := by
  filter_upwards [self_mem_nhdsWithin, hσΦε] with ε hε_mem hσΦε_pos
  have hε_pos : 0 < ε := hε_mem
  simp [sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve,
    sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve,
    hε_pos, hσΦε_pos]
  exact
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
      ρ Φ (sandwichedRenyiReferenceRegularization_posDef hσ hε_pos)
      hσΦε_pos α hα

/-- PosDef-output specialization of the high-`α` finite regularized curve DPI.

When the limiting output reference `Φσ` is already positive definite, the
channel-compatible regularized output references `Φ(σ + εI)` remain
positive-definite for every `ε ≥ 0`, so the regularized DPI follows directly
from the positive-definite finite theorem.  Singular output references still
require the support-compression/continuity argument isolated by the more general
regularization gate below. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
          ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
          ρ hσ α ε := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le
      ρ hσ Φ α hα ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact
    Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
      Φ hσ hσΦ (le_of_lt hε)

/-- Source-regularization reduction for the finite high-`α` PSD-reference
branch.

If the high-`α` finite input/output regularized curves converge to the intended
singular-reference finite branch, and the regularized output references are
eventually positive-definite, then the supported singular finite-branch DPI
follows from the already proved positive-definite Beigi/Gour theorem. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_regularizationLimitGate
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α)
    (DIn DOut : ℝ)
    (hσΦε :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)).PosDef)
    (hgate :
      sandwichedRenyiReferenceRegularizationLimitGate
        (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
          ρ hσ α)
        (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve
          ρ hσ Φ α)
        DIn DOut) :
    DOut ≤ DIn :=
  sandwichedRenyiReferenceRegularizationLimitGate.le_of_eventually_le hgate
    (sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedCurves_eventually_le
      ρ hσ Φ α hα hσΦε)

/-- Supported finite-branch high-`α` PSD-reference DPI in the faithful-output
subcase.

This is the part of the Gour/source regularization route that is already
closed by the local API: if the input finite branch is in-domain
(`ρ ≪ σ`) and the channel output reference `Φσ` is positive definite, the
positive-definite Beigi/Gour theorem applies to the source-regularized
references and the two finite branches are obtained by taking `ε → 0+`.

The arbitrary singular-output case needs the separate channel-compatible
support-compression continuity theorem for `Φ(σ + εI)`. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_regularizationLimitGate
      ρ hσ Φ α hα
      (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α)
      (sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α)
      ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact
      Channel.map_sandwichedRenyiReferenceRegularization_posDef_of_map_posDef
        Φ hσ hσΦ (le_of_lt hε)
  · exact
      ⟨sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve_tendsto_of_supports
          ρ hσ hSupport α hα,
        sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedOutputCurve_tendsto_of_map_posDef
          ρ hσ Φ hσΦ α hα⟩

/-- Extended-real high-`α` PSD-reference sandwiched Renyi branch.

This matches the source-domain convention for singular references: if
`ρ` is not supported by `σ`, the value is `+∞`; otherwise the finite branch is
the same power-trace expression used by the positive-definite API. -/
noncomputable def sandwichedRenyiPSDReferenceHighAlphaE
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : EReal :=
  by
    classical
    exact
      if Matrix.Supports ρ.matrix σ then
        (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α : EReal)
      else
        ⊤

@[simp]
theorem sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hSupport : ¬ Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α = ⊤ := by
  simp [sandwichedRenyiPSDReferenceHighAlphaE, hSupport]

@[simp]
theorem sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α =
      (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α : EReal) := by
  simp [sandwichedRenyiPSDReferenceHighAlphaE, hSupport]

/-- Positive source regularization always puts the input high-`α`
PSD-reference EReal branch in its finite support case.

This is the input-side domain handoff for the Gour/source regularization
route: `σ + εI` is positive definite for `ε > 0`, so every state is supported
by the regularized reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_regularized_input_eq_coe
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ
        (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α =
      (sandwichedRenyiPSDReferenceHighAlphaFinite ρ
        (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α :
        EReal) := by
  have hSupport :
      Matrix.Supports ρ.matrix
        (sandwichedRenyiReferenceRegularization σ ε) :=
    Matrix.Supports.of_right_posDef ρ.matrix
      (sandwichedRenyiReferenceRegularization σ ε)
      (sandwichedRenyiReferenceRegularization_posDef hσ hε)
  exact
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      ρ
      (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α
      hSupport

/-- Positive source regularization also puts the channel-compatible output
high-`α` PSD-reference EReal branch in its finite support case.

This is the key domain bookkeeping for the singular-output Gour route.  Even
when `Φ(σ + εI)` is singular in the ambient output space, every channel output
state is supported by it for `ε > 0`, so the EReal branch unfolds to the finite
power-trace expression rather than `+∞`. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_regularized_output_eq_coe
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiPSDReferenceHighAlphaE (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α =
      (sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
        (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α :
        EReal) := by
  have hSupport :
      Matrix.Supports (Φ.applyState ρ).matrix
        (Φ.map (sandwichedRenyiReferenceRegularization σ ε)) :=
    Channel.applyState_supports_map_regularized_reference Φ ρ hσ hε
  exact
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Φ.applyState ρ)
      (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
        (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α
      hSupport

/-- Input-side regularized high-`α` PSD-reference EReal curve.

For `ε > 0` this is the source-regularized branch
`D̃_α(ρ || σ + εI)` with the support-aware EReal semantics.  The fallback makes
the curve total on `ℝ`; it is never used along the source filter
`ε → 0+`. -/
noncomputable def sandwichedRenyiPSDReferenceHighAlphaERegularizedInputCurve
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (α : ℝ) (ε : ℝ) : EReal :=
  by
    classical
    exact
      if hε : 0 < ε then
        sandwichedRenyiPSDReferenceHighAlphaE ρ
          (sandwichedRenyiReferenceRegularization σ ε)
          (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef α
      else
        sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α

/-- Output-side channel-compatible regularized high-`α` PSD-reference EReal
curve.

For `ε > 0` this is the Gour/source output path
`D̃_α(Φρ || Φ(σ + εI))`.  It is support-aware, so it remains meaningful even
when `Φ(σ + εI)` is singular in the ambient codomain. -/
noncomputable def sandwichedRenyiPSDReferenceHighAlphaERegularizedOutputCurve
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ) (ε : ℝ) : EReal :=
  by
    classical
    exact
      if hε : 0 < ε then
        sandwichedRenyiPSDReferenceHighAlphaE (Φ.applyState ρ)
          (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
          (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
            (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef) α
      else
        sandwichedRenyiPSDReferenceHighAlphaE (Φ.applyState ρ)
          (Φ.map σ) (Φ.mapsPositive σ hσ) α

/-- Along positive regularization parameters, a finite-branch high-`α`
regularized inequality implies the corresponding EReal regularized inequality.

This theorem isolates the remaining Gour singular-output work: after the
finite branch is proved on the fixed output support of `Φ(I)`, no additional
support-domain bookkeeping is needed to pass to the source-facing EReal curves.
-/
theorem sandwichedRenyiPSDReferenceHighAlphaERegularizedCurves_eventually_le_of_finite
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (α : ℝ)
    (hfinite :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ hε : 0 < ε,
          sandwichedRenyiPSDReferenceHighAlphaFinite (Φ.applyState ρ)
              (Φ.map (sandwichedRenyiReferenceRegularization σ ε))
              (Φ.mapsPositive (sandwichedRenyiReferenceRegularization σ ε)
                (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef)
              α ≤
            sandwichedRenyiPSDReferenceHighAlphaFinite ρ
              (sandwichedRenyiReferenceRegularization σ ε)
              (sandwichedRenyiReferenceRegularization_posDef hσ hε).posSemidef
              α) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      sandwichedRenyiPSDReferenceHighAlphaERegularizedOutputCurve
          ρ hσ Φ α ε ≤
        sandwichedRenyiPSDReferenceHighAlphaERegularizedInputCurve
          ρ hσ α ε := by
  filter_upwards [self_mem_nhdsWithin, hfinite] with ε hε_mem hle
  have hε : 0 < ε := hε_mem
  simp [sandwichedRenyiPSDReferenceHighAlphaERegularizedOutputCurve,
    sandwichedRenyiPSDReferenceHighAlphaERegularizedInputCurve, hε]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_regularized_output_eq_coe
      ρ hσ Φ α hε,
    sandwichedRenyiPSDReferenceHighAlphaE_regularized_input_eq_coe
      ρ hσ α hε]
  exact_mod_cast hle hε

/-- Positive-definite reference specialization of the high-`α` extended-real
PSD-reference DPI, proved through the finite branch.

Compared with the existing real-valued `sandwichedRenyiReference` bridge, this
source-facing theorem does not require the input state or its channel output to
be positive definite.  A positive-definite reference makes both EReal branches
finite, and the finite-branch PosDef-reference theorem supplies the numerical
inequality. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_posDef_reference_finite
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hσ : σ.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ.posSemidef α := by
  have hSupport : Matrix.Supports ρ.matrix σ :=
    Matrix.Supports.of_right_posDef ρ.matrix σ hσ
  have hSupportOut :
      Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
    Matrix.Supports.of_right_posDef (Φ.applyState ρ).matrix (Φ.map σ) hσΦ
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Φ.applyState ρ) hσΦ.posSemidef α hSupportOut,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      ρ hσ.posSemidef α hSupport]
  exact_mod_cast
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
      ρ Φ hσ hσΦ α hα

/-- On positive-definite references, the high-`α` PSD-reference branch agrees
with the existing real-valued matrix-reference divergence.

This is the audit bridge from the source-facing support-aware semantics back
to the current `sandwichedRenyiReference` API. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
    (ρ : State a) {σ : CMatrix a}
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ.posSemidef α =
      (sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one : EReal) := by
  have hSupport : Matrix.Supports ρ.matrix σ :=
    Matrix.Supports.of_right_posDef ρ.matrix σ hσ
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    ρ hσ.posSemidef α hSupport]
  simp [sandwichedRenyiPSDReferenceHighAlphaFinite,
    sandwichedRenyiReference_eq_log2_psdTracePower_inner
      ρ hρ hσ α hα_pos hα_ne_one]

/-- If the input high-`α` support condition fails, the extended-real
PSD-reference DPI is immediate because the input value is `+∞`.

The supported finite branch is the remaining high-`α` PSD task; this theorem
separates the source-domain split from that finite-branch inequality. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_not_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hSupport : ¬ Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  simp [sandwichedRenyiPSDReferenceHighAlphaE, hSupport]

/-- Channel preservation of the finite high-`α` support domain, expressed in
the source-facing PSD-reference branch.

Once the input finite branch is available (`ρ ≪ σ`), the output finite branch
is also in-domain (`Φρ ≪ Φσ`).  The numerical finite-branch inequality remains
the nontrivial high-`α` PSD step. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_output_supports_of_input_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
  channel_applyState_supports_of_supports ρ hσ Φ hSupport

/-- If the input finite high-`α` support condition holds, the spectral support
projector of the output reference `Φσ` fixes the output state on both sides.

This is the first concrete compression lemma for the singular-output case:
it turns the source-domain support preservation `Φρ ≪ Φσ` into the algebraic
projector identities needed before restricting the Beigi/Gour finite theorem
to the support of `Φσ`. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_output_supportProjector_fixes_of_input_supports
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    let Pi : CMatrix b :=
      psdInvSqrt (Φ.map σ) (Φ.mapsPositive σ hσ).isHermitian *
        (Φ.map σ) *
        psdInvSqrt (Φ.map σ) (Φ.mapsPositive σ hσ).isHermitian
    Pi * (Φ.applyState ρ).matrix = (Φ.applyState ρ).matrix ∧
      (Φ.applyState ρ).matrix * Pi = (Φ.applyState ρ).matrix := by
  exact
    _root_.QIT.supportProjector_fixes_of_supports
      (M := (Φ.applyState ρ).matrix) (N := Φ.map σ)
      (Φ.applyState ρ).pos (Φ.mapsPositive σ hσ)
      (sandwichedRenyiPSDReferenceHighAlphaE_output_supports_of_input_supports
        ρ hσ Φ hSupport)

/-- Positive-definite reference specialization of the high-`α` extended-real
PSD-reference DPI.

This reuses the already proved full-rank/non-normalized-reference theorem and
only changes the outer source-facing semantics from real-valued
`sandwichedRenyiReference` to the support-aware EReal branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_posDef_reference
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) hσΦ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ.posSemidef α := by
  have hα_pos : 0 < α := by linarith
  have hα_ne_one : α ≠ 1 := ne_of_gt hα
  have hDPI :
      sandwichedRenyiReference (Φ.applyState ρ) (Φ.map σ)
          hρΦ hσΦ α hα_pos hα_ne_one ≤
        sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one :=
    sandwichedRenyi_dataProcessing_channel_posDef_reference
      ρ σ Φ hρ hσ hρΦ hσΦ α (Or.inr hα)
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
      (Φ.applyState ρ) hρΦ hσΦ α hα_pos hα_ne_one,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
      ρ hρ hσ α hα_pos hα_ne_one]
  exact_mod_cast hDPI

/-- Handoff from the supported high-`α` finite branch to the source-facing
EReal PSD-reference branch.

After support preservation, proving the numeric finite-branch inequality is
enough to obtain the EReal DPI.  This isolates the remaining high-`α` singular
PSD work from the already solved support-domain bookkeeping. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_supported_finite_le
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hSupport : Matrix.Supports ρ.matrix σ)
    (hfinite :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  have hSupportOut :
      Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
    sandwichedRenyiPSDReferenceHighAlphaE_output_supports_of_input_supports
      ρ hσ Φ hSupport
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Φ.applyState ρ) (Φ.mapsPositive σ hσ) α hSupportOut,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      ρ hσ α hSupport]
  exact_mod_cast hfinite

/-- Reduction of high-`α` PSD-reference DPI to the supported finite branch.

The source convention splits high-`α` singular references by support.  The
unsupported input branch is automatic (`+∞` on the right), and the supported
branch is reduced to the numeric finite-branch inequality after channel
support preservation. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_finite_branch
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ)
    (hfinite :
      Matrix.Supports ρ.matrix σ →
        sandwichedRenyiPSDReferenceHighAlphaFinite
            (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
          sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  by_cases hSupport : Matrix.Supports ρ.matrix σ
  · exact
      sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_supported_finite_le
        ρ hσ Φ α hSupport (hfinite hSupport)
  · exact
      sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_not_supports
        ρ hσ Φ α hSupport

/-- High-`α` EReal PSD-reference DPI in the faithful-output subcase.

If `Φσ` is positive definite, the supported finite branch follows from the
source-regularized positive-definite theorem, while the unsupported input branch
is immediate from the source support convention.  The remaining public-scope
high-`α` PSD task is exactly the case where `Φσ` is singular. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_map_posDef
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hσΦ : (Φ.map σ).PosDef)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_finite_branch
      ρ hσ Φ α ?_
  intro hSupport
  have hfinite :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_of_map_posDef
      ρ hσ Φ hSupport hσΦ α hα
  simpa using hfinite

/-- A state supported by a PSD reference compresses to a state on the
reference's positive spectral support.  This is the state-side object needed
for the Gour support-compression route when the output reference is singular:
the compressed reference is positive definite by
`Matrix.psdSupportCompress_self_posDef`, and the compressed output state keeps
trace one by support. -/
noncomputable def psdSupportCompressedState
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    State (psdSupportIndex σ hσ) :=
  _root_.QIT.psdSupportCompressedState ρ hσ hSupport

@[simp]
theorem psdSupportCompressedState_matrix
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    (psdSupportCompressedState ρ hσ hSupport).matrix =
      psdSupportCompress σ hσ ρ.matrix := rfl

theorem psdSupportCompressedState_reference_posDef
    {σ : CMatrix a} (hσ : σ.PosSemidef) :
    (psdSupportCompress σ hσ σ).PosDef :=
  _root_.QIT.psdSupportCompressedState_reference_posDef hσ

theorem psdSupportCompressedState_support_nonempty
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    Nonempty (psdSupportIndex σ hσ) :=
  _root_.QIT.psdSupportCompressedState_support_nonempty ρ hσ hSupport

/-- Embedding map from the positive spectral support of a PSD reference back
to the ambient system. -/
noncomputable def psdSupportEmbeddingMap
    (σ : CMatrix a) (hσ : σ.PosSemidef) :
    MatrixMap (psdSupportIndex σ hσ) a :=
  MatrixMap.ofKraus (fun (_ : Unit) => psdSupportIsometry σ hσ)

@[simp]
theorem psdSupportEmbeddingMap_apply
    (σ : CMatrix a) (hσ : σ.PosSemidef)
    (X : CMatrix (psdSupportIndex σ hσ)) :
    psdSupportEmbeddingMap σ hσ X =
      psdSupportIsometry σ hσ * X *
        Matrix.conjTranspose (psdSupportIsometry σ hσ) := by
  simp [psdSupportEmbeddingMap, MatrixMap.ofKraus]

/-- Compression map from the ambient system to the positive spectral support of
a PSD reference. -/
noncomputable def psdSupportCompressionMap
    (σ : CMatrix a) (hσ : σ.PosSemidef) :
    MatrixMap a (psdSupportIndex σ hσ) :=
  MatrixMap.ofKraus
    (fun (_ : Unit) => Matrix.conjTranspose (psdSupportIsometry σ hσ))

@[simp]
theorem psdSupportCompressionMap_apply
    (σ : CMatrix a) (hσ : σ.PosSemidef) (X : CMatrix a) :
    psdSupportCompressionMap σ hσ X =
      psdSupportCompress σ hσ X := by
  simp [psdSupportCompressionMap, psdSupportCompress, MatrixMap.ofKraus]

/-- Restrict a channel to the positive support of an input PSD reference and
the positive support of its output reference.  This is the Gour support-domain
channel used to reduce the singular high-`α` finite branch to the existing
positive-definite theorem. -/
noncomputable def psdSupportRestrictedChannel
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (σ : CMatrix a) (hσ : σ.PosSemidef) :
    Channel (psdSupportIndex σ hσ)
      (psdSupportIndex (Φ.map σ) (Φ.mapsPositive σ hσ)) where
  map :=
    (psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ)).comp
      (Φ.map.comp (psdSupportEmbeddingMap σ hσ))
  completelyPositive := by
    refine MatrixMap.isCompletelyPositive_comp
      (psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ))
      (Φ.map.comp (psdSupportEmbeddingMap σ hσ)) ?_ ?_
    · exact MatrixMap.ofKraus_completelyPositive _
    · exact MatrixMap.isCompletelyPositive_comp Φ.map
        (psdSupportEmbeddingMap σ hσ)
        Φ.completelyPositive (MatrixMap.ofKraus_completelyPositive _)
  tracePreserving := by
    intro X
    let τ : CMatrix b := Φ.map σ
    let hτ : τ.PosSemidef := Φ.mapsPositive σ hσ
    have hEmbedSupport :
        Matrix.Supports ((psdSupportEmbeddingMap σ hσ) X) σ := by
      simpa [psdSupportEmbeddingMap_apply] using
        _root_.QIT.psdSupportIsometry_conj_supports σ hσ X
    have hOutSupport :
        Matrix.Supports (Φ.map ((psdSupportEmbeddingMap σ hσ) X)) τ := by
      simpa [τ] using channel_map_supports Φ hσ hEmbedSupport
    calc
      ((psdSupportCompressionMap τ hτ).comp
          (Φ.map.comp (psdSupportEmbeddingMap σ hσ)) X).trace =
          (psdSupportCompress τ hτ
            (Φ.map ((psdSupportEmbeddingMap σ hσ) X))).trace := by
            simp [τ, psdSupportCompressionMap_apply]
      _ = (Φ.map ((psdSupportEmbeddingMap σ hσ) X)).trace := by
            exact psdSupportCompress_trace_of_supports_right hτ hOutSupport
      _ = ((psdSupportEmbeddingMap σ hσ) X).trace := Φ.tracePreserving _
      _ = X.trace := by
            simp [psdSupportEmbeddingMap_apply, psdSupportIsometry_conj_trace]
  mapsPositive := by
    intro X hX
    exact
      MatrixMap.isCompletelyPositive_mapsPositive
        ((psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ)).comp
          (Φ.map.comp (psdSupportEmbeddingMap σ hσ)))
        (MatrixMap.isCompletelyPositive_comp
          (psdSupportCompressionMap (Φ.map σ) (Φ.mapsPositive σ hσ))
          (Φ.map.comp (psdSupportEmbeddingMap σ hσ))
          (MatrixMap.ofKraus_completelyPositive _)
          (MatrixMap.isCompletelyPositive_comp Φ.map
            (psdSupportEmbeddingMap σ hσ)
            Φ.completelyPositive (MatrixMap.ofKraus_completelyPositive _)))
        X hX

@[simp]
theorem psdSupportRestrictedChannel_map_reference
    {b : Type v} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (σ : CMatrix a) (hσ : σ.PosSemidef) :
    (psdSupportRestrictedChannel Φ σ hσ).map
        (psdSupportCompress σ hσ σ) =
      psdSupportCompress (Φ.map σ) (Φ.mapsPositive σ hσ) (Φ.map σ) := by
  have hrec :
      psdSupportIsometry σ hσ * psdSupportCompress σ hσ σ *
          Matrix.conjTranspose (psdSupportIsometry σ hσ) = σ := by
    simpa using psdSupportCompress_reconstruct_self σ hσ
  simp [psdSupportRestrictedChannel, psdSupportEmbeddingMap_apply,
    psdSupportCompressionMap_apply, hrec]

@[simp]
theorem psdSupportRestrictedChannel_applyState_compressed
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (Φ : Channel a b) (hSupport : Matrix.Supports ρ.matrix σ) :
    (psdSupportRestrictedChannel Φ σ hσ).applyState
        (psdSupportCompressedState ρ hσ hSupport) =
      psdSupportCompressedState (Φ.applyState ρ) (Φ.mapsPositive σ hσ)
        (channel_applyState_supports_of_supports ρ hσ Φ hSupport) := by
  apply State.ext
  have hrec :
      psdSupportIsometry σ hσ *
          psdSupportCompress σ hσ ρ.matrix *
          Matrix.conjTranspose (psdSupportIsometry σ hσ) =
        ρ.matrix := by
    simpa using
      psdSupportCompress_reconstruct_of_supports
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
  simp [Channel.applyState, psdSupportRestrictedChannel,
    psdSupportEmbeddingMap_apply, psdSupportCompressionMap_apply, hrec]

/-- High-`α` finite-branch DPI after compressing both the input and output
references to their positive spectral supports.

This is the closed Beigi/Gour support-domain core: the restricted channel is
CPTP between support systems, both compressed references are positive
definite, and the existing positive-definite finite-branch theorem applies
without any regularization or support-domain placeholder. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supportCompressed
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (psdSupportCompressedState (Φ.applyState ρ) (Φ.mapsPositive σ hσ)
          (channel_applyState_supports_of_supports ρ hσ Φ hSupport))
        (psdSupportCompress (Φ.map σ) (Φ.mapsPositive σ hσ) (Φ.map σ))
        (psdSupportCompressedState_reference_posDef
          (Φ.mapsPositive σ hσ)).posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite
        (psdSupportCompressedState ρ hσ hSupport)
        (psdSupportCompress σ hσ σ)
        (psdSupportCompressedState_reference_posDef hσ).posSemidef α := by
  classical
  letI : Nonempty (psdSupportIndex σ hσ) :=
    psdSupportCompressedState_support_nonempty ρ hσ hSupport
  let ρc : State (psdSupportIndex σ hσ) :=
    psdSupportCompressedState ρ hσ hSupport
  let σc : CMatrix (psdSupportIndex σ hσ) :=
    psdSupportCompress σ hσ σ
  let Ψ := psdSupportRestrictedChannel Φ σ hσ
  have hσc : σc.PosDef := by
    simpa [σc] using psdSupportCompressedState_reference_posDef hσ
  have hσcΨ : (Ψ.map σc).PosDef := by
    simpa [Ψ, σc] using
      psdSupportCompressedState_reference_posDef (Φ.mapsPositive σ hσ)
  have hDPI :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_posDef_reference
      ρc Ψ hσc hσcΨ α hα
  simpa [ρc, σc, Ψ] using hDPI

/-- Compressing a supported state/reference pair to the positive spectral
support of the reference does not change the high-`α` finite branch.

This is the Gour support-domain reconstruction step: negative reference
powers are computed on the strictly positive support of `σ`, while the final
positive trace power is invariant under embedding by the support isometry. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α =
      sandwichedRenyiPSDReferenceHighAlphaFinite
        (psdSupportCompressedState ρ hσ hSupport)
        (psdSupportCompress σ hσ σ)
        (psdSupportCompressedState_reference_posDef hσ).posSemidef α := by
  classical
  letI : Nonempty (psdSupportIndex σ hσ) :=
    psdSupportCompressedState_support_nonempty ρ hσ hSupport
  let V : Matrix a (psdSupportIndex σ hσ) ℂ := psdSupportIsometry σ hσ
  let ρc : State (psdSupportIndex σ hσ) :=
    psdSupportCompressedState ρ hσ hSupport
  let σc : CMatrix (psdSupportIndex σ hσ) :=
    psdSupportCompress σ hσ σ
  let s : ℝ := (1 - α) / (2 * α)
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    field_simp [ne_of_gt hα_pos]
    linarith
  have hV : Matrix.conjTranspose V * V =
      (1 : CMatrix (psdSupportIndex σ hσ)) := by
    simpa [V] using psdSupportIsometry_isometry σ hσ
  have hρ_embed :
      V * ρc.matrix * Matrix.conjTranspose V = ρ.matrix := by
    simpa [V, ρc, psdSupportCompressedState_matrix] using
      psdSupportCompress_reconstruct_of_supports
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
  have hpow_embed :
      V * CFC.rpow σc s * Matrix.conjTranspose V = CFC.rpow σ s := by
    simpa [V, σc, s] using
      _root_.QIT.cMatrix_rpow_psdSupportCompress_reconstruct_self
        σ hσ hs_ne
  have hinner_embed :
      V * sandwichedRenyiReferenceInner ρc σc α *
          Matrix.conjTranspose V =
        sandwichedRenyiReferenceInner ρ σ α := by
    unfold sandwichedRenyiReferenceInner
    dsimp [ρc, σc, s]
    let P : CMatrix (psdSupportIndex σ hσ) := CFC.rpow σc s
    let R : CMatrix (psdSupportIndex σ hσ) := ρc.matrix
    have halg :
        V * (P * R * P) * Matrix.conjTranspose V =
          (V * P * Matrix.conjTranspose V) *
            (V * R * Matrix.conjTranspose V) *
            (V * P * Matrix.conjTranspose V) := by
      symm
      calc
        (V * P * Matrix.conjTranspose V) *
            (V * R * Matrix.conjTranspose V) *
            (V * P * Matrix.conjTranspose V) =
          V * P * (Matrix.conjTranspose V * V) * R *
            (Matrix.conjTranspose V * V) * P *
            Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
        _ = V * P * R * P * Matrix.conjTranspose V := by
              rw [hV]
              simp [Matrix.mul_assoc]
        _ = V * (P * R * P) * Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
    calc
      V * (CFC.rpow σc s * ρc.matrix * CFC.rpow σc s) *
          Matrix.conjTranspose V =
        (V * CFC.rpow σc s * Matrix.conjTranspose V) *
          (V * ρc.matrix * Matrix.conjTranspose V) *
          (V * CFC.rpow σc s * Matrix.conjTranspose V) := by
            simpa [P, R] using halg
      _ = CFC.rpow σ s * ρ.matrix * CFC.rpow σ s := by
            rw [hpow_embed, hρ_embed]
  let A : CMatrix (psdSupportIndex σ hσ) :=
    sandwichedRenyiReferenceInner ρc σc α
  have hA : A.PosSemidef := by
    simpa [A, ρc, σc] using
      sandwichedRenyiReferenceInner_posSemidef
        ρc (psdSupportCompressedState_reference_posDef hσ).posSemidef α
  have hpower :
      psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) α =
        psdTracePower A hA α := by
    have hiso :=
      _root_.QIT.psdTracePower_isometry_conj
        (V := V) hA hV (p := α) hα_pos
    have hVA :
        V * A * Matrix.conjTranspose V =
          sandwichedRenyiReferenceInner ρ σ α := by
      simpa [A] using hinner_embed
    simpa [A, hVA] using hiso
  simpa [sandwichedRenyiPSDReferenceHighAlphaFinite, A, ρc, σc] using
    congrArg (fun t : ℝ => (1 / (α - 1)) * log2 t) hpower

/-- Supported high-`α` finite-branch DPI for PSD references.

This is the singular-output completion of the Beigi/Gour high-`α` branch:
both sides are compressed to their positive support, the restricted channel
gives the positive-definite finite-branch DPI, and support-compression
invariance transports the result back to the source-facing finite branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supported
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    sandwichedRenyiPSDReferenceHighAlphaFinite
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ α := by
  classical
  have hSupportOut :
      Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ) :=
    channel_applyState_supports_of_supports ρ hσ Φ hSupport
  have hout :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
      (Φ.applyState ρ) (Φ.mapsPositive σ hσ) hSupportOut α hα
  have hin :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
      ρ hσ hSupport α hα
  have hcomp :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supportCompressed
      ρ hσ Φ hSupport α hα
  rw [hout, hin]
  exact hcomp

/-- High-`α` EReal PSD-reference DPI for arbitrary PSD references.

The unsupported branch is handled by the source convention `+∞`; the
supported finite branch is the support-compression theorem above. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel_of_finite_branch
      ρ hσ Φ α ?_
  intro hSupport
  exact
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supported
      ρ hσ Φ α hα hSupport

/-- Source-facing extended-real PSD-reference sandwiched Rényi divergence,
assembled from the low- and high-`α` branches.

For `α < 1` this uses the positive-power `Q_α` branch; for `α ≥ 1` it uses
the support-aware high-`α` branch. -/
noncomputable def sandwichedRenyiPSDReferenceE
    (ρ : State a) (σ : CMatrix a) (hσ : σ.PosSemidef) (α : ℝ) : EReal :=
  if α < 1 then
    sandwichedRenyiPSDReferenceLowAlphaE ρ σ hσ α
  else
    sandwichedRenyiPSDReferenceHighAlphaE ρ σ hσ α

/-- PSD-reference sandwiched Rényi DPI on the already proved source ranges:
strict `1/2 < α < 1` and high `α > 1`.

The remaining public endpoint gap is the singular PSD-reference case
`α = 1/2`; the full-rank endpoint is already proved elsewhere. -/
theorem sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_lt_lt_one_or_one_lt
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_range : (1 / 2 < α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiPSDReferenceE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceE ρ σ hσ α := by
  by_cases hlt : α < 1
  · rw [sandwichedRenyiPSDReferenceE, if_pos hlt,
      sandwichedRenyiPSDReferenceE, if_pos hlt]
    rcases hα_range with hlow | hhigh
    · exact
        sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel
          ρ hσ Φ α hlow.1 hlow.2
    · linarith
  · rw [sandwichedRenyiPSDReferenceE, if_neg hlt,
      sandwichedRenyiPSDReferenceE, if_neg hlt]
    rcases hα_range with hlow | hhigh
    · linarith
    · exact
        sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel
          ρ hσ Φ α hhigh

/-- Source-facing PSD-reference sandwiched Rényi DPI on the full parameter range
`(1 / 2 ≤ α ∧ α < 1) ∨ 1 < α`.

The low branch uses the Gour/Frank--Lieb PSD `Q`-functional route, with the
endpoint `α = 1 / 2` supplied by normalized-reference fidelity monotonicity;
the high branch uses the support-aware Beigi weighted-Schatten route. -/
theorem sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiPSDReferenceE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α ≤
      sandwichedRenyiPSDReferenceE ρ σ hσ α := by
  by_cases hlt : α < 1
  · rw [sandwichedRenyiPSDReferenceE, if_pos hlt,
      sandwichedRenyiPSDReferenceE, if_pos hlt]
    rcases hα_range with hlow | hhigh
    · rcases hlow with ⟨hhalf, hlt_one⟩
      by_cases hEq : α = 1 / 2
      · subst α
        exact sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel_half
          ρ hσ Φ
      · have hhalf_strict : 1 / 2 < α := lt_of_le_of_ne hhalf (Ne.symm hEq)
        exact
          sandwichedRenyiPSDReferenceLowAlphaE_dataProcessing_channel
            ρ hσ Φ α hhalf_strict hlt_one
    · linarith
  · rw [sandwichedRenyiPSDReferenceE, if_neg hlt,
      sandwichedRenyiPSDReferenceE, if_neg hlt]
    rcases hα_range with hlow | hhigh
    · linarith
    · exact
        sandwichedRenyiPSDReferenceHighAlphaE_dataProcessing_channel
          ρ hσ Φ α hhigh

/-- Public-statement orientation of
`sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt`.

This is the same source-facing PSD-reference theorem, written as
`D(ρ || σ) ≥ D(Φρ || Φσ)`. -/
theorem sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef) (Φ : Channel a b)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyiPSDReferenceE ρ σ hσ α ≥
      sandwichedRenyiPSDReferenceE
        (Φ.applyState ρ) (Φ.map σ) (Φ.mapsPositive σ hσ) α := by
  exact
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
      ρ hσ Φ α hα_range

/-- Common-diagonal positive-reference special case of Frank--Lieb low-alpha
joint concavity for the matrix-level sandwiched Renyi `Q` functional.

This is the classical/commuting theorem obtained by reducing the sandwiched
matrix expression to the scalar concave power sum.  It does not assume the
general Frank--Lieb theorem or any sandwiched Renyi DPI wrapper. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha_diagonal
    (ρ₁ ρ₂ σ₁ σ₂ : a → ℝ)
    (hρ₁ : ∀ i, 0 ≤ ρ₁ i) (hρ₂ : ∀ i, 0 ≤ ρ₂ i)
    (hσ₁ : ∀ i, 0 < σ₁ i) (hσ₂ : ∀ i, 0 < σ₂ i)
    {α t : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let ρt : a → ℝ := fun i => t * ρ₁ i + (1 - t) * ρ₂ i
    let σt : a → ℝ := fun i => t * σ₁ i + (1 - t) * σ₂ i
    t * sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₁ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₁ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ₁ hρ₁)
        (cMatrix_diagonal_ofReal_posSemidef σ₁ fun i => (hσ₁ i).le)
        α +
      (1 - t) * sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₂ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₂ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ₂ hρ₂)
        (cMatrix_diagonal_ofReal_posSemidef σ₂ fun i => (hσ₂ i).le)
        α ≤
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρt i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σt i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρt fun i =>
          add_nonneg (mul_nonneg ht0 (hρ₁ i))
            (mul_nonneg (sub_nonneg.mpr ht1) (hρ₂ i)))
        (cMatrix_diagonal_ofReal_posSemidef σt fun i =>
          add_nonneg (mul_nonneg ht0 (hσ₁ i).le)
            (mul_nonneg (sub_nonneg.mpr ht1) (hσ₂ i).le))
        α := by
  let ρt : a → ℝ := fun i => t * ρ₁ i + (1 - t) * ρ₂ i
  let σt : a → ℝ := fun i => t * σ₁ i + (1 - t) * σ₂ i
  have hα_pos : 0 < α := by linarith
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hρt : ∀ i, 0 ≤ ρt i := by
    intro i
    exact add_nonneg (mul_nonneg ht0 (hρ₁ i))
      (mul_nonneg (sub_nonneg.mpr ht1) (hρ₂ i))
  have hσt : ∀ i, 0 < σt i := by
    intro i
    have hmin : 0 < min (σ₁ i) (σ₂ i) := lt_min (hσ₁ i) (hσ₂ i)
    have hsum : t + (1 - t) = 1 := by ring
    have hle :
        min (σ₁ i) (σ₂ i) * (t + (1 - t)) ≤
          t * σ₁ i + (1 - t) * σ₂ i := by
      have hle₁ :
          min (σ₁ i) (σ₂ i) * t ≤ t * σ₁ i := by
        calc
          min (σ₁ i) (σ₂ i) * t = t * min (σ₁ i) (σ₂ i) := by ring
          _ ≤ t * σ₁ i :=
            mul_le_mul_of_nonneg_left (min_le_left (σ₁ i) (σ₂ i)) ht0
      have hle₂ :
          min (σ₁ i) (σ₂ i) * (1 - t) ≤ (1 - t) * σ₂ i := by
        calc
          min (σ₁ i) (σ₂ i) * (1 - t) =
              (1 - t) * min (σ₁ i) (σ₂ i) := by ring
          _ ≤ (1 - t) * σ₂ i :=
            mul_le_mul_of_nonneg_left
              (min_le_right (σ₁ i) (σ₂ i)) (sub_nonneg.mpr ht1)
      calc
        min (σ₁ i) (σ₂ i) * (t + (1 - t)) =
            min (σ₁ i) (σ₂ i) * t + min (σ₁ i) (σ₂ i) * (1 - t) := by ring
        _ ≤ t * σ₁ i + (1 - t) * σ₂ i := add_le_add hle₁ hle₂
    have hpos : 0 < min (σ₁ i) (σ₂ i) * (t + (1 - t)) := by
      rw [hsum, mul_one]
      exact hmin
    exact lt_of_lt_of_le hpos hle
  have heval₁ :
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₁ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₁ i : ℂ) : CMatrix a)
        (Matrix.PosSemidef.diagonal (d := fun i => (ρ₁ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (ρ₁ i : ℂ)
          exact_mod_cast hρ₁ i))
        (Matrix.PosSemidef.diagonal (d := fun i => (σ₁ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (σ₁ i : ℂ)
          exact_mod_cast (hσ₁ i).le))
        α =
        ∑ i, ρ₁ i ^ α * σ₁ i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρ₁ σ₁ hρ₁ hσ₁ hα_pos
  have heval₂ :
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ₂ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ₂ i : ℂ) : CMatrix a)
        (Matrix.PosSemidef.diagonal (d := fun i => (ρ₂ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (ρ₂ i : ℂ)
          exact_mod_cast hρ₂ i))
        (Matrix.PosSemidef.diagonal (d := fun i => (σ₂ i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (σ₂ i : ℂ)
          exact_mod_cast (hσ₂ i).le))
        α =
        ∑ i, ρ₂ i ^ α * σ₂ i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρ₂ σ₂ hρ₂ hσ₂ hα_pos
  have hevalt :
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρt i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σt i : ℂ) : CMatrix a)
        (Matrix.PosSemidef.diagonal (d := fun i => (ρt i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (ρt i : ℂ)
          exact_mod_cast hρt i))
        (Matrix.PosSemidef.diagonal (d := fun i => (σt i : ℂ)) (by
          intro i
          change (0 : ℂ) ≤ (σt i : ℂ)
          exact_mod_cast (hσt i).le))
        α =
        ∑ i, ρt i ^ α * σt i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρt σt hρt hσt hα_pos
  dsimp only
  rw [heval₁, heval₂, hevalt]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    sandwichedRenyiQ_scalarTerm_concave_lowAlpha
      (p₁ := ρ₁ i) (p₂ := ρ₂ i) (q₁ := σ₁ i) (q₂ := σ₂ i)
      (α := α) (t := t)
      (hρ₁ i) (hρ₂ i) (hσ₁ i) (hσ₂ i)
      hα_nonneg hα_le_one ht0 ht1

end State

end

end QIT
