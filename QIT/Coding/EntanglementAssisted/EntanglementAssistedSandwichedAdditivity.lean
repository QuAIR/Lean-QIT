/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwiched
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedPetzAdditivity
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedCBNorm
public import QIT.Information.Renyi.ConditionalRenyiMinimax
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.HypothesisTesting.DPI
public import QIT.Information.Renyi.RenyiDPI
public import QIT.States.Purification.Canonical

/-!
# Product-state scaffolding for sandwiched EA mutual information additivity

This module contains the tensor-product repartitioning facts used by the
source route for Khatri--Wilde, `Chapters/EA_capacity.tex:1169-1217`.

The final optimized product-state additivity theorem for
`State.sandwichedRenyiMutualInformationE` also needs the source alternate
expression `eq-sand_rel_mut_inf_alt`.  This file only adds no-placeholder
infrastructure that the downstream theorem can reuse.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Pointwise

namespace QIT

universe u1 v1 u2 v2

noncomputable section

/-- If a positive-definite matrix is supported by a positive-semidefinite
reference, the reference is positive definite.  This local closure lemma is
used to rule out singular side references in the high-`alpha` KW support
convention. -/
theorem Matrix.Supports.posDef_right_of_left_posDef
    {a : Type u1} [Fintype a] [DecidableEq a]
    {M N : CMatrix a} (hM : M.PosDef) (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) : N.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hN.isHermitian ?_
  intro x hx
  have hnonneg : 0 <= star x ⬝ᵥ N.mulVec x :=
    hN.dotProduct_mulVec_nonneg x
  have hne : star x ⬝ᵥ N.mulVec x ≠ 0 := by
    intro hzero
    have hNzero : N.mulVec x = 0 := (hN.dotProduct_mulVec_zero_iff x).mp hzero
    have hMzero : M.mulVec x = 0 := hSupport x hNzero
    have hMquad_zero : star x ⬝ᵥ M.mulVec x = 0 := by
      rw [hMzero, dotProduct_zero]
    have hpos : 0 < star x ⬝ᵥ M.mulVec x :=
      hM.dotProduct_mulVec_pos hx
    rw [hMquad_zero] at hpos
    exact (lt_irrefl (0 : Complex)) hpos
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- If the right tensor factor is full rank, replacing it by any matrix on the
left-hand side preserves support domination.

This is the finite-dimensional kernel-inclusion form used below to pass from
`rho_A \otimes rho_B` to `rho_A \otimes sigma_B` when `sigma_B` is full rank. -/
theorem Matrix.Supports.kronecker_right_of_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (A : CMatrix a) (B C : CMatrix b) (hC : C.PosDef) :
    Matrix.Supports (Matrix.kronecker A B) (Matrix.kronecker A C) := by
  let L : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) (B * C⁻¹)
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hleft : C⁻¹ * C = (1 : CMatrix b) := Matrix.nonsing_inv_mul C hCdet
  have hfactor :
      Matrix.kronecker A B = L * Matrix.kronecker A C := by
    calc
      Matrix.kronecker A B =
          Matrix.kronecker (A * (1 : CMatrix a)) (B * (1 : CMatrix b)) := by
            simp
      _ = Matrix.kronecker (A * (1 : CMatrix a)) (B * (C⁻¹ * C)) := by
            rw [hleft]
      _ = Matrix.kronecker ((1 : CMatrix a) * A) ((B * C⁻¹) * C) := by
            simp [Matrix.mul_assoc]
      _ = L * Matrix.kronecker A C := by
            simpa [L, Matrix.kronecker] using
              (Matrix.mul_kronecker_mul (1 : CMatrix a) A (B * C⁻¹) C)
  intro v hv
  calc
    Matrix.mulVec (Matrix.kronecker A B) v =
        Matrix.mulVec (L * Matrix.kronecker A C) v := by rw [hfactor]
    _ = Matrix.mulVec L (Matrix.mulVec (Matrix.kronecker A C) v) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by
        rw [hv]
        simp

/-- If a PSD matrix is supported by a nonnegative diagonal reference, then its
diagonal entries vanish wherever the reference diagonal vanishes. -/
theorem Matrix.Supports.diagonal_zero_of_posSemidef
    {a : Type u1} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (_hM : M.PosSemidef) {d : a → ℝ} (_hd : ∀ i, 0 ≤ d i)
    (hSupport :
      Matrix.Supports M (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a))
    {i : a} (hdi : d i = 0) :
    M i i = 0 := by
  let e : a → ℂ := Pi.single i 1
  have hDe : (Matrix.diagonal fun j => ((d j : ℝ) : ℂ) : CMatrix a).mulVec e = 0 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [e, Matrix.mulVec, dotProduct, Matrix.diagonal, hdi]
    · simp [e, Matrix.mulVec, dotProduct, Matrix.diagonal, hji]
  have hMe : M.mulVec e = 0 := hSupport e hDe
  have hii := congrFun hMe i
  have hsum : (∑ x, M i x * e x) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using hii
  have hsingle : (∑ x, M i x * e x) = M i i := by
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j _hj hji
      simp [e, Pi.single_eq_of_ne hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rwa [hsingle] at hsum

/-- PSD support domination is stable under Kronecker products.

This support-closure lemma is the matrix-level support convention needed for
the KW product-state additivity proof: if each factor state is supported by its
factor reference, then the product state is supported by the product reference. -/
theorem Matrix.Supports.kronecker_of_posSemidef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {rhoA refA : CMatrix a} {rhoB refB : CMatrix b}
    (hRhoA : rhoA.PosSemidef) (hRefA : refA.PosSemidef)
    (hRhoB : rhoB.PosSemidef) (hRefB : refB.PosSemidef)
    (h1 : Matrix.Supports rhoA refA) (h2 : Matrix.Supports rhoB refB) :
    Matrix.Supports (Matrix.kronecker rhoA rhoB) (Matrix.kronecker refA refB) := by
  classical
  let U1 : Matrix.unitaryGroup a ℂ := star hRefA.isHermitian.eigenvectorUnitary
  let U2 : Matrix.unitaryGroup b ℂ := star hRefB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (U1 : CMatrix a) (U2 : CMatrix b),
      kronecker_mem_unitaryGroup U1 U2⟩
  let d1 : a → ℝ := fun i => hRefA.isHermitian.eigenvalues i
  let d2 : b → ℝ := fun j => hRefB.isHermitian.eigenvalues j
  let d : Prod a b → ℝ := fun x => d1 x.1 * d2 x.2
  let rhoA' : CMatrix a := (U1 : CMatrix a) * rhoA * star (U1 : CMatrix a)
  let rhoB' : CMatrix b := (U2 : CMatrix b) * rhoB * star (U2 : CMatrix b)
  let D1 : CMatrix a := Matrix.diagonal fun i => ((d1 i : ℝ) : ℂ)
  let D2 : CMatrix b := Matrix.diagonal fun j => ((d2 j : ℝ) : ℂ)
  have hd1_nonneg : ∀ i, 0 ≤ d1 i := by
    intro i
    exact hRefA.eigenvalues_nonneg i
  have hd2_nonneg : ∀ j, 0 ≤ d2 j := by
    intro j
    exact hRefB.eigenvalues_nonneg j
  have hd_nonneg : ∀ x, 0 ≤ d x := by
    intro x
    exact mul_nonneg (hd1_nonneg x.1) (hd2_nonneg x.2)
  have hRefA_diag :
      (U1 : CMatrix a) * refA * star (U1 : CMatrix a) = D1 := by
    let V1 : Matrix.unitaryGroup a ℂ := hRefA.isHermitian.eigenvectorUnitary
    have hspec := hRefA.isHermitian.spectral_theorem
    have hRefA_spec :
        refA = (V1 : CMatrix a) * D1 * star (V1 : CMatrix a) := by
      simpa [V1, D1, d1, Matrix.IsHermitian.spectral_theorem,
        Unitary.conjStarAlgAut_apply]
        using hspec
    have hdiagV : star (V1 : CMatrix a) * refA * (V1 : CMatrix a) = D1 := by
      calc
        star (V1 : CMatrix a) * refA * (V1 : CMatrix a) =
            star (V1 : CMatrix a) * ((V1 : CMatrix a) * D1 * star (V1 : CMatrix a)) *
              (V1 : CMatrix a) := by rw [hRefA_spec]
        _ = (star (V1 : CMatrix a) * (V1 : CMatrix a)) * D1 *
              (star (V1 : CMatrix a) * (V1 : CMatrix a)) := by
              noncomm_ring
        _ = D1 := by
              rw [Unitary.coe_star_mul_self]
              simp
    simpa [U1, V1] using hdiagV
  have hRefB_diag :
      (U2 : CMatrix b) * refB * star (U2 : CMatrix b) = D2 := by
    let V2 : Matrix.unitaryGroup b ℂ := hRefB.isHermitian.eigenvectorUnitary
    have hspec := hRefB.isHermitian.spectral_theorem
    have hRefB_spec :
        refB = (V2 : CMatrix b) * D2 * star (V2 : CMatrix b) := by
      simpa [V2, D2, d2, Matrix.IsHermitian.spectral_theorem,
        Unitary.conjStarAlgAut_apply]
        using hspec
    have hdiagV : star (V2 : CMatrix b) * refB * (V2 : CMatrix b) = D2 := by
      calc
        star (V2 : CMatrix b) * refB * (V2 : CMatrix b) =
            star (V2 : CMatrix b) * ((V2 : CMatrix b) * D2 * star (V2 : CMatrix b)) *
              (V2 : CMatrix b) := by rw [hRefB_spec]
        _ = (star (V2 : CMatrix b) * (V2 : CMatrix b)) * D2 *
              (star (V2 : CMatrix b) * (V2 : CMatrix b)) := by
              noncomm_ring
        _ = D2 := by
              rw [Unitary.coe_star_mul_self]
              simp
    simpa [U2, V2] using hdiagV
  have h1diag : Matrix.Supports rhoA' D1 := by
    simpa [rhoA', D1, hRefA_diag] using h1.unitary_conj U1
  have h2diag : Matrix.Supports rhoB' D2 := by
    simpa [rhoB', D2, hRefB_diag] using h2.unitary_conj U2
  have hRhoA' : rhoA'.PosSemidef := by
    simpa [rhoA', Matrix.star_eq_conjTranspose] using
      hRhoA.conjTranspose_mul_mul_same (star (U1 : CMatrix a))
  have hRhoB' : rhoB'.PosSemidef := by
    simpa [rhoB', Matrix.star_eq_conjTranspose] using
      hRhoB.conjTranspose_mul_mul_same (star (U2 : CMatrix b))
  have hdiagZero1 : ∀ i, d1 i = 0 → rhoA' i i = 0 := by
    intro i hi
    exact Matrix.Supports.diagonal_zero_of_posSemidef hRhoA' hd1_nonneg h1diag hi
  have hdiagZero2 : ∀ j, d2 j = 0 → rhoB' j j = 0 := by
    intro j hj
    exact Matrix.Supports.diagonal_zero_of_posSemidef hRhoB' hd2_nonneg h2diag hj
  have hprodDiag :
      Matrix.Supports (Matrix.kronecker rhoA' rhoB')
        (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ) : CMatrix (Prod a b)) := by
    refine Matrix.Supports.of_posSemidef_diagonal (hRhoA'.kronecker hRhoB') hd_nonneg ?_
    intro x hx
    rcases x with ⟨i, j⟩
    have hcases : d1 i = 0 ∨ d2 j = 0 := mul_eq_zero.mp hx
    rcases hcases with hi | hj
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hdiagZero1 i hi]
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hdiagZero2 j hj]
  have hprodDiag' :
      Matrix.Supports
        ((U : CMatrix (Prod a b)) * Matrix.kronecker rhoA rhoB * star (U : CMatrix (Prod a b)))
        ((U : CMatrix (Prod a b)) * Matrix.kronecker refA refB * star (U : CMatrix (Prod a b))) := by
    have hleft :
        (U : CMatrix (Prod a b)) * Matrix.kronecker rhoA rhoB * star (U : CMatrix (Prod a b)) =
          Matrix.kronecker rhoA' rhoB' := by
      simp [U, rhoA', rhoB', Matrix.conjTranspose_kronecker, Matrix.star_eq_conjTranspose,
        Matrix.mul_kronecker_mul, Matrix.mul_assoc]
    have hright :
        (U : CMatrix (Prod a b)) * Matrix.kronecker refA refB * star (U : CMatrix (Prod a b)) =
          Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ) := by
      calc
        (U : CMatrix (Prod a b)) * Matrix.kronecker refA refB * star (U : CMatrix (Prod a b)) =
            Matrix.kronecker ((U1 : CMatrix a) * refA * star (U1 : CMatrix a))
              ((U2 : CMatrix b) * refB * star (U2 : CMatrix b)) := by
              simp [U, Matrix.conjTranspose_kronecker, Matrix.star_eq_conjTranspose,
                Matrix.mul_kronecker_mul, Matrix.mul_assoc]
        _ = Matrix.kronecker D1 D2 := by
              rw [hRefA_diag, hRefB_diag]
        _ = Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ) := by
              simpa [D1, D2, d] using
                (Matrix.diagonal_kronecker_diagonal
                  (fun i : a => ((d1 i : ℝ) : ℂ))
                  (fun j : b => ((d2 j : ℝ) : ℂ)))
    rw [hleft, hright]
    exact hprodDiag
  intro v hv
  let Umat : CMatrix (Prod a b) := (U : CMatrix (Prod a b))
  let rhoProd : CMatrix (Prod a b) := Matrix.kronecker rhoA rhoB
  let refProd : CMatrix (Prod a b) := Matrix.kronecker refA refB
  have hstarU_U : star Umat * Umat = 1 := by
    simpa [Umat] using (Unitary.coe_star_mul_self U : star (U : CMatrix (Prod a b)) *
      (U : CMatrix (Prod a b)) = 1)
  have hmatRef : (Umat * refProd * star Umat) * Umat = Umat * refProd := by
    calc
      (Umat * refProd * star Umat) * Umat =
          Umat * refProd * (star Umat * Umat) := by
          noncomm_ring
      _ = Umat * refProd := by
          rw [hstarU_U]
          simp
  have hmatRho : (Umat * rhoProd * star Umat) * Umat = Umat * rhoProd := by
    calc
      (Umat * rhoProd * star Umat) * Umat =
          Umat * rhoProd * (star Umat * Umat) := by
          noncomm_ring
      _ = Umat * rhoProd := by
          rw [hstarU_U]
          simp
  have hRefv : refProd.mulVec v = 0 := by
    simpa [refProd] using hv
  have hkill :
      (Umat * refProd * star Umat).mulVec (Umat.mulVec v) = 0 := by
    calc
      (Umat * refProd * star Umat).mulVec (Umat.mulVec v) =
          ((Umat * refProd * star Umat) * Umat).mulVec v := by
          rw [Matrix.mulVec_mulVec]
      _ = (Umat * refProd).mulVec v := by rw [hmatRef]
      _ = Umat.mulVec (refProd.mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [hRefv]
          simp
  have hconj :
      (Umat * rhoProd * star Umat).mulVec (Umat.mulVec v) = 0 :=
    hprodDiag' (Umat.mulVec v) hkill
  have hURho :
      Umat.mulVec (rhoProd.mulVec v) = 0 := by
    calc
      Umat.mulVec (rhoProd.mulVec v) =
          (Umat * rhoProd).mulVec v := by rw [Matrix.mulVec_mulVec]
      _ = ((Umat * rhoProd * star Umat) * Umat).mulVec v := by rw [hmatRho]
      _ = (Umat * rhoProd * star Umat).mulVec (Umat.mulVec v) := by
          rw [Matrix.mulVec_mulVec]
      _ = 0 := hconj
  have hback := congrArg (fun w => (star Umat).mulVec w) hURho
  have hback_zero :
      (star Umat).mulVec (Umat.mulVec (rhoProd.mulVec v)) = 0 := by
    simpa using hback
  have hconj_back :
      (((star Umat * Umat) * rhoProd).mulVec v) = 0 := by
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hback_zero
  have hidRho : (star Umat * Umat) * rhoProd = rhoProd := by
    rw [hstarU_U]
    simp
  calc
    rhoProd.mulVec v = ((star Umat * Umat) * rhoProd).mulVec v := by
        rw [hidRho]
    _ = 0 := hconj_back

/-- Support domination is preserved by relabelling finite bases. -/
theorem Matrix.Supports.reindex
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {M N : CMatrix a} (h : Matrix.Supports M N) (e : a ≃ b) :
    Matrix.Supports (M.submatrix e.symm e.symm) (N.submatrix e.symm e.symm) := by
  intro v hv
  let w : a → ℂ := fun i => v (e i)
  have hNw : N.mulVec w = 0 := by
    ext i
    have hi := congrFun hv (e i)
    simp [Matrix.mulVec, dotProduct] at hi ⊢
    have hsum :
        (∑ x : a, N i x * v (e x)) =
          ∑ y : b, N i (e.symm y) * v y := by
      exact Fintype.sum_equiv e
        (fun x : a => N i x * v (e x))
        (fun y : b => N i (e.symm y) * v y)
        (by intro x; simp)
    rw [hsum]
    exact hi
  have hMw : M.mulVec w = 0 := h w hNw
  ext j
  have hj := congrFun hMw (e.symm j)
  simp [w, Matrix.mulVec, dotProduct] at hj ⊢
  have hsum :
      (∑ x : b, M (e.symm j) (e.symm x) * v x) =
        ∑ y : a, M (e.symm j) y * v (e y) := by
    exact Fintype.sum_equiv e.symm
      (fun x : b => M (e.symm j) (e.symm x) * v x)
      (fun y : a => M (e.symm j) y * v (e y))
      (by intro x; simp)
  rw [hsum]
  exact hj

private theorem cMatrix_reindex_mem_unitary
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (e : a ≃ b) (U : Matrix.unitaryGroup a ℂ) :
    Matrix.reindex e e (U : CMatrix a) ∈ Matrix.unitaryGroup b ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have hU := Matrix.mem_unitaryGroup_iff.mp U.2
  have happ := congrFun (congrFun hU (e.symm i)) (e.symm j)
  simp [Matrix.mul_apply, Matrix.star_apply] at happ ⊢
  have hsum :
      (∑ x : b, (U : CMatrix a) (e.symm i) (e.symm x) *
          starRingEnd ℂ ((U : CMatrix a) (e.symm j) (e.symm x))) =
        ∑ y : a, (U : CMatrix a) (e.symm i) y *
          starRingEnd ℂ ((U : CMatrix a) (e.symm j) y) := by
    exact Fintype.sum_equiv e.symm
      (fun x : b => (U : CMatrix a) (e.symm i) (e.symm x) *
        starRingEnd ℂ ((U : CMatrix a) (e.symm j) (e.symm x)))
      (fun y : a => (U : CMatrix a) (e.symm i) y *
        starRingEnd ℂ ((U : CMatrix a) (e.symm j) y))
      (by intro x; rfl)
  rw [hsum]
  simpa [Matrix.one_apply] using happ

/-- Spectral multiplication rule for PSD matrix powers under the repository's
support convention.

This is deliberately scalar-parametric: callers supply the pointwise
nonnegative-real identity, so singular eigenvalues are handled explicitly
instead of silently adding a positive-definiteness hypothesis. -/
private theorem cMatrix_rpow_mul_rpow_of_posSemidef_scalar
    {a : Type u1} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) {r s t : ℝ}
    (hscalar : ∀ x : ℝ, 0 ≤ x → x ^ r * x ^ s = x ^ t) :
    CFC.rpow A r * CFC.rpow A s = CFC.rpow A t := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.isHermitian.eigenvalues
  let Dr : CMatrix a := Matrix.diagonal fun i => ((d i ^ r : ℝ) : ℂ)
  let Ds : CMatrix a := Matrix.diagonal fun i => ((d i ^ s : ℝ) : ℂ)
  let Dt : CMatrix a := Matrix.diagonal fun i => ((d i ^ t : ℝ) : ℂ)
  have hd : ∀ i, 0 ≤ d i := fun i => hA.eigenvalues_nonneg i
  have hUstar : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hr :
      CFC.rpow A r = (U : CMatrix a) * Dr * star (U : CMatrix a) := by
    simpa [U, d, Dr] using cMatrix_rpow_eq_eigenbasis_diagonal hA r
  have hs :
      CFC.rpow A s = (U : CMatrix a) * Ds * star (U : CMatrix a) := by
    simpa [U, d, Ds] using cMatrix_rpow_eq_eigenbasis_diagonal hA s
  have ht :
      CFC.rpow A t = (U : CMatrix a) * Dt * star (U : CMatrix a) := by
    simpa [U, d, Dt] using cMatrix_rpow_eq_eigenbasis_diagonal hA t
  have hdiag : Dr * Ds = Dt := by
    dsimp [Dr, Ds, Dt]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      rw [← Complex.ofReal_mul, hscalar (d i) (hd i)]
    · simp [Matrix.diagonal, hij]
  rw [hr, hs, ht]
  calc
    ((U : CMatrix a) * Dr * star (U : CMatrix a)) *
        ((U : CMatrix a) * Ds * star (U : CMatrix a)) =
        (U : CMatrix a) * (Dr * Ds) * star (U : CMatrix a) := by
          calc
            ((U : CMatrix a) * Dr * star (U : CMatrix a)) *
                ((U : CMatrix a) * Ds * star (U : CMatrix a)) =
                (U : CMatrix a) * Dr * (star (U : CMatrix a) * (U : CMatrix a)) *
                  Ds * star (U : CMatrix a) := by
                  noncomm_ring
            _ = (U : CMatrix a) * Dr * 1 * Ds * star (U : CMatrix a) := by
                  rw [hUstar]
            _ = (U : CMatrix a) * (Dr * Ds) * star (U : CMatrix a) := by
                  noncomm_ring
    _ = (U : CMatrix a) * Dt * star (U : CMatrix a) := by
          rw [hdiag]

private theorem real_sandwiched_left_rpow_mul_sqrt
    {x alpha : ℝ} (hx : 0 ≤ x) (halpha : 1 < alpha) :
    x ^ ((1 - alpha) / (2 * alpha)) * x ^ (1 / 2 : ℝ) =
      x ^ (1 / (2 * alpha)) := by
  by_cases hx0 : x = 0
  · subst x
    have hs_ne : (1 - alpha) / (2 * alpha) ≠ 0 := by
      have hnum : 1 - alpha ≠ 0 := by linarith
      have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
      exact div_ne_zero hnum hden
    have ht_ne : (1 / (2 * alpha) : ℝ) ≠ 0 := by
      have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
      exact one_div_ne_zero hden
    have ht_ne' : (alpha⁻¹ * 2⁻¹ : ℝ) ≠ 0 := by
      have ha : alpha ≠ 0 := by linarith [lt_trans zero_lt_one halpha]
      exact mul_ne_zero (inv_ne_zero ha) (by norm_num)
    simp [Real.zero_rpow hs_ne, Real.zero_rpow ht_ne']
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [← Real.rpow_add hxpos]
    congr 1
    field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
    ring

/-- PSD version of the KW exponent cancellation
`tau^((1-alpha)/(2 alpha)) * tau^(1/2) = tau^(1/(2 alpha))`.

The positive-definite proof uses `CFC.rpow_add`.  This support-aware variant
keeps the same source equality for singular input states, using the local
spectral convention `0^s = 0`. -/
private theorem cMatrix_sandwiched_left_rpow_mul_sqrt
    {a : Type u1} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
    CFC.rpow A ((1 - alpha) / (2 * alpha)) * CFC.rpow A (1 / 2 : ℝ) =
      CFC.rpow A (1 / (2 * alpha)) :=
  cMatrix_rpow_mul_rpow_of_posSemidef_scalar hA
    (fun _ hx => real_sandwiched_left_rpow_mul_sqrt hx halpha)

/-- Right-handed version of `cMatrix_sandwiched_left_rpow_mul_sqrt`.

Both factors are functions of the same PSD matrix, so the spectral proof is
identical with the scalar factors reversed. -/
private theorem cMatrix_sqrt_mul_sandwiched_left_rpow
    {a : Type u1} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
  CFC.rpow A (1 / 2 : ℝ) * CFC.rpow A ((1 - alpha) / (2 * alpha)) =
      CFC.rpow A (1 / (2 * alpha)) := by
  refine cMatrix_rpow_mul_rpow_of_posSemidef_scalar hA ?_
  intro _ hx
  rw [mul_comm]
  exact real_sandwiched_left_rpow_mul_sqrt hx halpha

/-- Support-convention real powers commute with finite reindexing.

The nonnegative-exponent version follows directly from continuous functional
calculus.  KW's high-`alpha` sandwiched expressions also use the negative
exponent `(1 - alpha) / (2 * alpha)` on possibly singular PSD references; this
finite-dimensional spectral proof records the repository support convention
`0^s = 0` and therefore avoids adding a full-rank hypothesis merely to
repartition product systems. -/
private theorem cMatrix_rpow_reindex_posSemidef_support
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (e : a ≃ b) {A : CMatrix a} (hA : A.PosSemidef) (s : ℝ) :
    CFC.rpow (Matrix.reindex e e A) s =
      Matrix.reindex e e (CFC.rpow A s) := by
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let Ue : Matrix.unitaryGroup b ℂ :=
    ⟨Matrix.reindex e e (U : CMatrix a), cMatrix_reindex_mem_unitary e U⟩
  let d : a → ℝ := hA.isHermitian.eigenvalues
  let de : b → ℝ := fun i => d (e.symm i)
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact hA.eigenvalues_nonneg i
  have hde : ∀ i, 0 ≤ de i := by
    intro i
    exact hd (e.symm i)
  have hA_spec :
      A = Unitary.conjStarAlgAut ℂ _ U
        (Matrix.diagonal (fun i => (d i : ℂ))) := by
    simpa [U, d, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hdiag :
      Matrix.reindex e e (Matrix.diagonal (fun i => (d i : ℂ)) : CMatrix a) =
        Matrix.diagonal (fun i => (de i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [de]
    · simp [Matrix.diagonal, hij]
  have hstarU :
      Matrix.reindex e e (star (U : CMatrix a)) =
        star (Matrix.reindex e e (U : CMatrix a)) := by
    ext i j
    simp [Matrix.star_apply]
  have hdiagAlg :
      (Matrix.reindexAlgEquiv ℂ ℂ e)
          (Matrix.diagonal (fun i => (d i : ℂ)) : CMatrix a) =
        Matrix.diagonal (fun i => (de i : ℂ)) := by
    simpa [Matrix.reindexAlgEquiv_apply] using hdiag
  have hstarUAlg :
      (Matrix.reindexAlgEquiv ℂ ℂ e) (star (U : CMatrix a)) =
        star ((Matrix.reindexAlgEquiv ℂ ℂ e) (U : CMatrix a)) := by
    simpa [Matrix.reindexAlgEquiv_apply] using hstarU
  have hre_spec :
      Matrix.reindex e e A =
        Unitary.conjStarAlgAut ℂ _ Ue
          (Matrix.diagonal (fun i => (de i : ℂ))) := by
    rw [hA_spec]
    change (Matrix.reindexAlgEquiv ℂ ℂ e)
        (((U : CMatrix a) * Matrix.diagonal (fun i => (d i : ℂ))) * star (U : CMatrix a)) =
      ((Ue : CMatrix b) * Matrix.diagonal (fun i => (de i : ℂ))) * star (Ue : CMatrix b)
    rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul]
    rw [hdiagAlg, hstarUAlg]
    rfl
  have hA_rpow :
      CFC.rpow A s =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) := by
    rw [hA_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U d hd s
  have hre_rpow :
      CFC.rpow (Matrix.reindex e e A) s =
        Unitary.conjStarAlgAut ℂ _ Ue
          (Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ))) := by
    rw [hre_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal Ue de hde s
  rw [hre_rpow, hA_rpow]
  have hdiag_pow :
      Matrix.reindex e e (Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix a) =
        Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [de]
    · simp [Matrix.diagonal, hij]
  change ((Ue : CMatrix b) *
        Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ))) *
        star (Ue : CMatrix b) =
      (Matrix.reindexAlgEquiv ℂ ℂ e)
        (((U : CMatrix a) * Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) *
          star (U : CMatrix a))
  rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul]
  have hdiagPowAlg :
      (Matrix.reindexAlgEquiv ℂ ℂ e)
          (Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix a) =
        Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ)) := by
    simpa [Matrix.reindexAlgEquiv_apply] using hdiag_pow
  rw [hdiagPowAlg, hstarUAlg]
  rfl

private theorem additivity_finset_sum_b_b_a_reorder
    {a : Type u1} {b : Type v1} [Fintype a] [Fintype b]
    {R : Type*} [AddCommMonoid R]
    (F : a -> b -> b -> R) :
    (∑ j : b, ∑ k : b, ∑ i : a, F i j k) =
      ∑ i : a, ∑ j : b, ∑ k : b, F i j k := by
  calc
    (∑ j : b, ∑ k : b, ∑ i : a, F i j k) =
        ∑ k : b, ∑ j : b, ∑ i : a, F i j k := by
      rw [Finset.sum_comm]
    _ = ∑ k : b, ∑ i : a, ∑ j : b, F i j k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ i : a, ∑ k : b, ∑ j : b, F i j k := by
      rw [Finset.sum_comm]
    _ = ∑ i : a, ∑ j : b, ∑ k : b, F i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

private theorem additivity_partialTraceA_quadratic_eq_sum_slice
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (M : CMatrix (Prod a b)) (y : b -> ℂ) :
    let z : a -> Prod a b -> ℂ := fun i p => if p.1 = i then y p.2 else 0
    star y ⬝ᵥ (partialTraceA (a := a) (b := b) M).mulVec y =
      ∑ i, star (z i) ⬝ᵥ M.mulVec (z i) := by
  intro z
  simp [z, partialTraceA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, apply_ite]
  rw [additivity_finset_sum_b_b_a_reorder (a := a) (b := b)
    (F := fun i j k => starRingEnd ℂ (y j) * (M (i, j) (i, k) * y k))]

private theorem additivity_partialTraceA_posDef_of_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Nonempty a]
    {M : CMatrix (Prod a b)} (hM : M.PosDef) :
    (partialTraceA (a := a) (b := b) M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (partialTraceA_posSemidef (a := a) (b := b) hM.posSemidef).1 ?_
  intro y hy
  let z : a -> Prod a b -> ℂ := fun i p => if p.1 = i then y p.2 else 0
  have hz (i : a) : z i ≠ 0 := by
    intro hzi
    apply hy
    funext j
    have h := congr_fun hzi (i, j)
    simpa [z] using h
  have hnonneg : ∀ i : a, 0 <= star (z i) ⬝ᵥ M.mulVec (z i) := by
    intro i
    exact hM.posSemidef.dotProduct_mulVec_nonneg (z i)
  have hpos :
      0 < star (z (Classical.choice inferInstance)) ⬝ᵥ
        M.mulVec (z (Classical.choice inferInstance)) :=
    hM.dotProduct_mulVec_pos (hz (Classical.choice inferInstance))
  rw [additivity_partialTraceA_quadratic_eq_sum_slice (M := M) (y := y)]
  exact Finset.sum_pos' (fun i _ => hnonneg i)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, hpos⟩

private theorem State.marginalB_posDef_of_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) (hrho : rhoAB.matrix.PosDef) :
    rhoAB.marginalB.matrix.PosDef := by
  letI : Nonempty a := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  simpa [State.marginalB_matrix] using
    (additivity_partialTraceA_posDef_of_posDef
      (a := a) (b := b) (M := rhoAB.matrix) hrho)

private theorem State.marginalA_posDef_of_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) (hrho : rhoAB.matrix.PosDef) :
    rhoAB.marginalA.matrix.PosDef := by
  let rhoBA : State (Prod b a) := rhoAB.reindex (Equiv.prodComm a b)
  have hrhoBA : rhoBA.matrix.PosDef := by
    simpa [rhoBA] using State.reindex_posDef rhoAB (Equiv.prodComm a b) hrho
  have hmarg : rhoAB.marginalA = rhoBA.marginalB := by
    apply State.ext
    ext i j
    simp [rhoBA, State.marginalA, State.marginalB, State.reindex,
      partialTraceA, partialTraceB]
  rw [hmarg]
  exact State.marginalB_posDef_of_posDef rhoBA hrhoBA

private theorem State.prod_right_posDef_of_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Nonempty a]
    (rhoA : State a) (sigmaB : State b)
    (hprod : (rhoA.prod sigmaB).matrix.PosDef) :
    sigmaB.matrix.PosDef := by
  have hpt :
      (partialTraceA (a := a) (b := b) (rhoA.prod sigmaB).matrix).PosDef :=
    additivity_partialTraceA_posDef_of_posDef
      (a := a) (b := b) (M := (rhoA.prod sigmaB).matrix) hprod
  simpa [State.partialTraceA_prod rhoA sigmaB] using hpt

/-- Positive-argument logarithm rule for `log2` and real powers. -/
private theorem log2_rpow_pos {x y : ℝ} (hx : 0 < x) :
    log2 (Real.rpow x y) = y * log2 x := by
  unfold log2
  change Real.log (x ^ y) / Real.log 2 = y * (Real.log x / Real.log 2)
  rw [Real.log_rpow hx]
  ring

/-- Infimum of independently optimized real-valued objectives over a product
domain.  This is the order-theoretic scalar step used in the KW source when an
`inf` over product side-information states separates into two independent
`inf`s. -/
theorem real_sInf_range_prod_add_eq_add_sInf_range
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) :
    sInf (Set.range fun p : ι × κ => f p.1 + g p.2) =
      sInf (Set.range f) + sInf (Set.range g) := by
  let hpair : BddBelow (Set.range fun p : ι × κ => f p.1 + g p.2) := by
    rcases hf with ⟨lf, hlf⟩
    rcases hg with ⟨lg, hlg⟩
    refine ⟨lf + lg, ?_⟩
    rintro x ⟨p, rfl⟩
    exact add_le_add (hlf ⟨p.1, rfl⟩) (hlg ⟨p.2, rfl⟩)
  apply le_antisymm
  · rw [Real.sInf_le_iff hpair (Set.range_nonempty _)]
    intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    rcases Real.lt_sInf_add_pos (s := Set.range f) (Set.range_nonempty f) hhalf with
      ⟨xf, ⟨i, rfl⟩, hi⟩
    rcases Real.lt_sInf_add_pos (s := Set.range g) (Set.range_nonempty g) hhalf with
      ⟨xg, ⟨j, rfl⟩, hj⟩
    refine ⟨f i + g j, ⟨(i, j), rfl⟩, ?_⟩
    linarith
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro x ⟨p, rfl⟩
    exact add_le_add (csInf_le hf ⟨p.1, rfl⟩) (csInf_le hg ⟨p.2, rfl⟩)

/-- Coercion from real-valued bounded-below objectives to `EReal` preserves
the infimum.  This is the scalar bridge between the real KW full-rank branch
and the repository's extended-real optimized definitions. -/
theorem ereal_sInf_range_coe_eq_coe_real_sInf
    {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hf : BddBelow (Set.range f)) :
    sInf (Set.range fun i : ι => (f i : EReal)) =
      ((sInf (Set.range f) : ℝ) : EReal) := by
  let S : Set (WithTop ℝ) := Set.range fun i : ι => ((f i : ℝ) : WithTop ℝ)
  have hS_bdd : BddBelow S := by
    rcases hf with ⟨lb, hlb⟩
    refine ⟨(lb : WithTop ℝ), ?_⟩
    rintro y ⟨i, rfl⟩
    exact WithTop.coe_le_coe.mpr (hlb ⟨i, rfl⟩)
  have htop : sInf S = ((sInf (Set.range f) : ℝ) : WithTop ℝ) := by
    have h := WithTop.coe_sInf' (s := Set.range f) (Set.range_nonempty f) hf
    have himage : ((fun a : ℝ => (a : WithTop ℝ)) '' Set.range f) = S := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    rw [himage] at h
    exact h.symm
  have hbot := WithBot.coe_sInf' (s := S) hS_bdd
  have hrange : (Set.range fun i : ι => (f i : EReal)) =
      ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(f i : WithTop ℝ), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange]
  calc
    sInf ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) =
        ((sInf S : WithTop ℝ) : WithBot (WithTop ℝ)) := hbot.symm
    _ = (((sInf (Set.range f) : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      rw [htop]

/-- Infimum of a nonnegative extended-real family, computed in `ENNReal`.

Sandwiched-Renyi divergence candidates are never negative; this bridge lets the
KW product-side-state `inf` split use the `ENNReal` complete-lattice API rather
than full-rank real-valued reductions. -/
theorem ereal_sInf_range_nonneg_eq_coe_ennreal_iInf
    {ι : Type*} [Nonempty ι] (f : ι → EReal) (hf : ∀ i, 0 ≤ f i) :
    sInf (Set.range f) = ENNReal.toEReal (⨅ i, (f i).toENNReal) := by
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hf i
  apply le_antisymm
  · rw [csInf_le_iff hbdd (Set.range_nonempty f)]
    intro b hb
    by_cases hb_nonpos : b ≤ 0
    · exact hb_nonpos.trans (EReal.coe_ennreal_nonneg _)
    · have hb_nonneg : 0 ≤ b := le_of_lt (lt_of_not_ge hb_nonpos)
      have hb_to :
          b.toENNReal ≤ ⨅ i, (f i).toENNReal := by
        refine le_iInf fun i => ?_
        exact EReal.toENNReal_le_toENNReal (hb ⟨i, rfl⟩)
      rw [← EReal.coe_toENNReal hb_nonneg]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hb_to
  · refine le_csInf (Set.range_nonempty f) ?_
    rintro _ ⟨i, rfl⟩
    have hi :
        (⨅ j, (f j).toENNReal) ≤ (f i).toENNReal :=
      iInf_le (fun j => (f j).toENNReal) i
    have hE :
        ENNReal.toEReal (⨅ j, (f j).toENNReal) ≤ ((f i).toENNReal : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr hi
    simpa [EReal.coe_toENNReal (hf i)] using hE

/-- Product infimum split for nonnegative extended-real objectives.

This is the order-theoretic form of the KW step that separates the independent
`inf_{sigma_1, sigma_2}` after the fixed product candidate has been rewritten
as a sum of two factor candidates. -/
theorem ereal_sInf_range_prod_add_eq_add_sInf_range_nonneg
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → EReal) (g : κ → EReal)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) :
    sInf (Set.range fun p : ι × κ => f p.1 + g p.2) =
      sInf (Set.range f) + sInf (Set.range g) := by
  have hfg : ∀ p : ι × κ, 0 ≤ f p.1 + g p.2 := by
    intro p
    exact add_nonneg (hf p.1) (hg p.2)
  rw [ereal_sInf_range_nonneg_eq_coe_ennreal_iInf
        (fun p : ι × κ => f p.1 + g p.2) hfg]
  rw [ereal_sInf_range_nonneg_eq_coe_ennreal_iInf f hf]
  rw [ereal_sInf_range_nonneg_eq_coe_ennreal_iInf g hg]
  rw [← EReal.coe_ennreal_add]
  congr 1
  have hterm : ∀ p : ι × κ,
      (f p.1 + g p.2).toENNReal = (f p.1).toENNReal + (g p.2).toENNReal := by
    intro p
    exact EReal.toENNReal_add (hf p.1) (hg p.2)
  simp_rw [hterm]
  calc
    (⨅ p : ι × κ, (f p.1).toENNReal + (g p.2).toENNReal) =
        ⨅ i : ι, ⨅ j : κ, (f i).toENNReal + (g j).toENNReal := by
          simp [iInf_prod]
    _ = ⨅ i : ι, (f i).toENNReal + ⨅ j : κ, (g j).toENNReal := by
          simp_rw [ENNReal.add_iInf]
    _ = (⨅ i : ι, (f i).toENNReal) + ⨅ j : κ, (g j).toENNReal := by
          rw [ENNReal.iInf_add]

/-- Supremum of independently optimized real-valued objectives over a product
domain.  This is the scalar optimization split used in the product-input
superadditivity step of KW `EA_capacity.tex:1239-1244`. -/
theorem real_sSup_range_prod_add_eq_add_sSup_range
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    sSup (Set.range fun p : ι × κ => f p.1 + g p.2) =
      sSup (Set.range f) + sSup (Set.range g) := by
  let hpair : BddAbove (Set.range fun p : ι × κ => f p.1 + g p.2) := by
    rcases hf with ⟨uf, huf⟩
    rcases hg with ⟨ug, hug⟩
    refine ⟨uf + ug, ?_⟩
    rintro x ⟨p, rfl⟩
    exact add_le_add (huf ⟨p.1, rfl⟩) (hug ⟨p.2, rfl⟩)
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro x ⟨p, rfl⟩
    exact add_le_add (le_csSup hf ⟨p.1, rfl⟩) (le_csSup hg ⟨p.2, rfl⟩)
  · rw [Real.le_sSup_iff hpair (Set.range_nonempty _)]
    intro ε hε
    have hhalf : ε / 2 < 0 := by linarith
    rcases Real.add_neg_lt_sSup (s := Set.range f) (Set.range_nonempty f) hhalf with
      ⟨xf, ⟨i, rfl⟩, hi⟩
    rcases Real.add_neg_lt_sSup (s := Set.range g) (Set.range_nonempty g) hhalf with
      ⟨xg, ⟨j, rfl⟩, hj⟩
    refine ⟨f i + g j, ⟨(i, j), rfl⟩, ?_⟩
    linarith

/-- Coercion from real-valued bounded-above objectives to `EReal` preserves
the supremum.  This is the scalar bridge used when the KW alternate expression
is optimized over full-rank purifying side states. -/
theorem ereal_sSup_range_coe_eq_coe_real_sSup
    {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hf : BddAbove (Set.range f)) :
    sSup (Set.range fun i : ι => (f i : EReal)) =
      ((sSup (Set.range f) : ℝ) : EReal) := by
  let S : Set (WithTop ℝ) := Set.range fun i : ι => ((f i : ℝ) : WithTop ℝ)
  have hS_nonempty : S.Nonempty := Set.range_nonempty _
  have hS_bdd : BddAbove S := ⟨⊤, by intro y _hy; exact le_top⟩
  have htop : sSup S = ((sSup (Set.range f) : ℝ) : WithTop ℝ) := by
    have h := WithTop.coe_sSup' (s := Set.range f) hf
    have himage : ((fun a : ℝ => (a : WithTop ℝ)) '' Set.range f) = S := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    rw [himage] at h
    exact h.symm
  have hbot := WithBot.coe_sSup' (s := S) hS_nonempty hS_bdd
  have hrange : (Set.range fun i : ι => (f i : EReal)) =
      ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(f i : WithTop ℝ), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange]
  calc
    sSup ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) =
        ((sSup S : WithTop ℝ) : WithBot (WithTop ℝ)) := hbot.symm
    _ = (((sSup (Set.range f) : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      rw [htop]

/-- On a nonempty positive bounded-above real set, `log2` sends the supremum
to the supremum of the image.  This is the local logarithm-transport step used
before splitting a product-state optimization into independent optimizations. -/
theorem real_log2_sSup_image_eq {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddAbove s) (hpos : ∀ x ∈ s, 0 < x) :
    sSup (log2 '' s) = log2 (sSup s) := by
  unfold log2
  have hsup_pos : 0 < sSup s := by
    rcases hne with ⟨x, hx⟩
    exact lt_of_lt_of_le (hpos x hx) (le_csSup hbdd hx)
  have hcont : ContinuousWithinAt (fun x : ℝ => Real.log x / Real.log 2) s (sSup s) :=
    (Real.continuousAt_log hsup_pos.ne').div_const _ |>.continuousWithinAt
  have hmono : MonotoneOn (fun x : ℝ => Real.log x / Real.log 2) s := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_right (Real.log_le_log (hpos x hx) hxy)
      (le_of_lt (Real.log_pos one_lt_two))
  have hmap := MonotoneOn.map_csSup_of_continuousWithinAt
    (f := fun x : ℝ => Real.log x / Real.log 2) (A := s) hcont hmono hne hbdd
  simpa using hmap.symm

/-- On a nonempty bounded-below set with strictly positive infimum, `log2`
sends the infimum to the infimum of the image. -/
theorem real_log2_sInf_image_eq {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddBelow s) (hinf_pos : 0 < sInf s) :
    sInf (log2 '' s) = log2 (sInf s) := by
  unfold log2
  have hcont : ContinuousWithinAt (fun x : ℝ => Real.log x / Real.log 2) s (sInf s) :=
    (Real.continuousAt_log hinf_pos.ne').div_const _ |>.continuousWithinAt
  have hmono : MonotoneOn (fun x : ℝ => Real.log x / Real.log 2) s := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le hinf_pos (csInf_le hbdd hx)
    exact div_le_div_of_nonneg_right (Real.log_le_log hxpos hxy)
      (le_of_lt (Real.log_pos one_lt_two))
  have hmap := MonotoneOn.map_csInf_of_continuousWithinAt
    (f := fun x : ℝ => Real.log x / Real.log 2) (A := s) hcont hmono hne hbdd
  simpa using hmap.symm

/-- KW scalar optimization split for the reverse product-state inequality:
after restricting the source supremum to product side-information states, the
logarithm of the supremum of products separates into the sum of two independent
logarithmic suprema. -/
theorem real_log2_sSup_range_prod_mul_eq_add
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfpos : ∀ i, 0 < f i) (hgpos : ∀ j, 0 < g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2))
    (hlogf : BddAbove (Set.range fun i : ι => log2 (f i)))
    (hlogg : BddAbove (Set.range fun j : κ => log2 (g j))) :
    log2 (sSup (Set.range fun p : ι × κ => f p.1 * g p.2)) =
      sSup (Set.range fun i : ι => log2 (f i)) +
        sSup (Set.range fun j : κ => log2 (g j)) := by
  let prodSet : Set ℝ := Set.range fun p : ι × κ => f p.1 * g p.2
  have hprod_nonempty : prodSet.Nonempty := Set.range_nonempty _
  have hprod_pos : ∀ x ∈ prodSet, 0 < x := by
    rintro x ⟨p, rfl⟩
    exact mul_pos (hfpos p.1) (hgpos p.2)
  have hlogsup :
      sSup (log2 '' prodSet) = log2 (sSup prodSet) :=
    real_log2_sSup_image_eq hprod_nonempty hprod hprod_pos
  have himage :
      log2 '' prodSet =
        Set.range fun p : ι × κ => log2 (f p.1 * g p.2) := by
    ext x
    constructor
    · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨f p.1 * g p.2, ⟨p, rfl⟩, rfl⟩
  have hlogpoint :
      (fun p : ι × κ => log2 (f p.1 * g p.2)) =
        (fun p : ι × κ => log2 (f p.1) + log2 (g p.2)) := by
    funext p
    rw [log2_mul (ne_of_gt (hfpos p.1)) (ne_of_gt (hgpos p.2))]
  rw [← hlogsup]
  rw [himage, hlogpoint]
  exact real_sSup_range_prod_add_eq_add_sSup_range
    (fun i : ι => log2 (f i)) (fun j : κ => log2 (g j)) hlogf hlogg

/-- Supremum of a product objective factors into the product of independent
suprema when both objectives are nonnegative.

This is the scalar form needed for the all-state `tau_C` side of the KW
alternate expression, where singular references are allowed and pointwise
strict positivity is therefore unavailable. -/
theorem real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfnonneg : ∀ i, 0 ≤ f i) (hgnonneg : ∀ j, 0 ≤ g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2)) :
    sSup (Set.range fun p : ι × κ => f p.1 * g p.2) =
      sSup (Set.range f) * sSup (Set.range g) := by
  rw [sSup_range, sSup_range, sSup_range]
  rw [ciSup_prod hprod]
  calc
    (⨆ (i : ι) (j : κ), f i * g j) =
        ⨆ i : ι, f i * (⨆ j : κ, g j) := by
      congr
      ext i
      rw [Real.mul_iSup_of_nonneg (hfnonneg i)]
    _ = (⨆ i : ι, f i) * (⨆ j : κ, g j) := by
      rw [Real.iSup_mul_of_nonneg (Real.iSup_nonneg hgnonneg)]

/-- Logarithmic version of
`real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg`.  The assumptions only
require strict positivity of the two independent suprema, not pointwise
strict positivity. -/
theorem real_log2_sSup_range_prod_mul_eq_add_of_nonneg
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfnonneg : ∀ i, 0 ≤ f i) (hgnonneg : ∀ j, 0 ≤ g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2))
    (hfsup_pos : 0 < sSup (Set.range f)) (hgsup_pos : 0 < sSup (Set.range g)) :
    log2 (sSup (Set.range fun p : ι × κ => f p.1 * g p.2)) =
      log2 (sSup (Set.range f)) + log2 (sSup (Set.range g)) := by
  rw [real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg f g hfnonneg hgnonneg hprod]
  exact log2_mul (ne_of_gt hfsup_pos) (ne_of_gt hgsup_pos)

/-- Coefficient-weighted form of
`real_log2_sSup_range_prod_mul_eq_add`, matching the scalar shell of
KW `EA_capacity.tex:1208-1214` for `alpha > 1`. -/
theorem real_sandwichedCoeff_log2_sSup_range_prod_mul_eq_add
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfpos : ∀ i, 0 < f i) (hgpos : ∀ j, 0 < g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2))
    (hlogf : BddAbove (Set.range fun i : ι => log2 (f i)))
    (hlogg : BddAbove (Set.range fun j : κ => log2 (g j)))
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2 (sSup (Set.range fun p : ι × κ => f p.1 * g p.2)) =
      alpha / (alpha - 1) *
          sSup (Set.range fun i : ι => log2 (f i)) +
        alpha / (alpha - 1) *
          sSup (Set.range fun j : κ => log2 (g j)) := by
  have _halpha_ne : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt halpha)
  rw [real_log2_sSup_range_prod_mul_eq_add f g hfpos hgpos hprod hlogf hlogg]
  ring

/-- For `alpha > 1`, the source exponent `(alpha - 1) / alpha` lies in
`(0, 1)`.  This is the parameter conversion used in KW
`EA_capacity.tex:2016-2023` before invoking Sion. -/
theorem sandwichedAlphaPrime_pos_lt_one {alpha : ℝ} (halpha : 1 < alpha) :
    0 < (alpha - 1) / alpha ∧ (alpha - 1) / alpha < 1 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  constructor
  · exact div_pos (sub_pos.mpr halpha) halpha_pos
  · rw [div_lt_one halpha_pos]
    linarith

/-- Closed-interval form of `sandwichedAlphaPrime_pos_lt_one`, matching the
operator-concavity side condition in the Sion step of KW
`EA_capacity.tex:2032-2039`. -/
theorem sandwichedAlphaPrime_mem_Icc_zero_one {alpha : ℝ} (halpha : 1 < alpha) :
    (alpha - 1) / alpha ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  exact ⟨le_of_lt hp.1, le_of_lt hp.2⟩

/-- KW high-`alpha` specialization of the Sion exchange for the raw
alternate-expression trace bracket.

This packages the minimax step in `EA_capacity.tex:2020-2025` with the exact
parameter `p = (alpha - 1) / alpha`.  The compact full-support lower-bound
domain is kept explicit; removing this restriction and passing to all side
states is part of the remaining alternate-expression closure. -/
theorem sandwichedAlpha_sion_abcSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (halpha : 1 < alpha) :
    (⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
        ⨆ τ ∈ State.densityMatrixSet c,
          (State.abcSidePowerTraceRe (a := a) R σ τ ((alpha - 1) / alpha) :
            EReal)) =
      ⨆ τ ∈ State.densityMatrixSet c,
        ⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          (State.abcSidePowerTraceRe (a := a) R σ τ ((alpha - 1) / alpha) :
            EReal) := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  exact State.uniformlyPositiveDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
    (a := a) (b := b) (c := c)
    hdelta_pos
    (State.uniformlyPositiveDensityMatrixSet_nonempty (a := b) hdelta_le)
    hR hp.1 (le_of_lt hp.2)

/-- On normalized side states, the matrix-domain Sion function used above is
the real part of the source pure-state bracket.

This bridges the reusable `ConditionalRenyiMinimax` matrix API back to the
KW trace expression in `EA_capacity.tex:2016-2025`. -/
theorem upwardRenyiDualityBracketRe_state_matrices
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c)) (σB : State b) (τC : State c)
    (alphaPrime : ℝ) :
    State.upwardRenyiDualityBracketRe (a := a)
        ψ σB.matrix τC.matrix alphaPrime =
      (ψ.upwardRenyiDualityCommonBracket σB τC alphaPrime).re := by
  have hσ :
      State.densityMatrixSetState σB.matrix
          (State.state_matrix_mem_densityMatrixSet σB) = σB := by
    apply State.ext
    exact State.densityMatrixSetState_matrix σB.matrix
      (State.state_matrix_mem_densityMatrixSet σB)
  have hτ :
      State.densityMatrixSetState τC.matrix
          (State.state_matrix_mem_densityMatrixSet τC) = τC := by
    apply State.ext
    exact State.densityMatrixSetState_matrix τC.matrix
      (State.state_matrix_mem_densityMatrixSet τC)
  rw [State.upwardRenyiDualityBracketRe_of_mem (a := a) ψ
    (State.state_matrix_mem_densityMatrixSet σB)
    (State.state_matrix_mem_densityMatrixSet τC)
    alphaPrime]
  rw [hσ, hτ]

/-- Negation changes an extended-real infimum into the corresponding supremum.

This order-theoretic bridge is used when applying Sion to the negative of the
KW trace bracket and then returning to the original bracket. -/
theorem ereal_neg_iInf_eq_iSup_neg {ι : Sort _} (f : ι → EReal) :
    -(⨅ i, f i) = ⨆ i, -f i := by
  have h := OrderIso.map_iInf EReal.negOrderIso f
  change OrderDual.ofDual (EReal.negOrderIso (⨅ i, f i)) = _
  rw [h]
  rfl

/-- Negation changes an extended-real supremum into the corresponding
infimum. -/
theorem ereal_neg_iSup_eq_iInf_neg {ι : Sort _} (f : ι → EReal) :
    -(⨆ i, f i) = ⨅ i, -f i := by
  have h := OrderIso.map_iSup EReal.negOrderIso f
  change OrderDual.ofDual (EReal.negOrderIso (⨆ i, f i)) = _
  rw [h]
  rfl

/-- Convert a Sion equality proved for the negative saddle function back to
the source `inf sup = sup inf` equality for the original function. -/
theorem ereal_sion_from_neg
    {ι κ : Sort _} (F : ι → κ → EReal)
    (h :
      (⨅ k : κ, ⨆ i : ι, -F i k) =
        ⨆ i : ι, ⨅ k : κ, -F i k) :
    (⨅ i : ι, ⨆ k : κ, F i k) =
      ⨆ k : κ, ⨅ i : ι, F i k := by
  have hneg := congrArg Neg.neg h
  rw [ereal_neg_iInf_eq_iSup_neg, ereal_neg_iSup_eq_iInf_neg] at hneg
  simp_rw [ereal_neg_iSup_eq_iInf_neg, ereal_neg_iInf_eq_iSup_neg, neg_neg] at hneg
  exact hneg.symm

/-- The scalar map `x ↦ -(x : EReal)` is antitone. -/
theorem antitone_ereal_neg_coe : Antitone (fun x : ℝ => -((x : EReal))) := by
  intro x y hxy
  exact EReal.neg_le_neg_iff.mpr (EReal.coe_le_coe_iff.mpr hxy)

/-- Optimizing a matrix functional over normalized `State`s is the same as
optimizing it over the matrix-level density set used by the Sion API. -/
theorem state_iInf_matrix_eq_densityMatrixSet_iInf
    {b : Type v1} [Fintype b] [DecidableEq b] (f : CMatrix b → EReal) :
    (⨅ σ : State b, f σ.matrix) =
      ⨅ M : CMatrix b, ⨅ _hM : M ∈ State.densityMatrixSet b, f M := by
  apply le_antisymm
  · refine le_iInf ?_
    intro M
    refine le_iInf ?_
    intro hM
    calc
      (⨅ σ : State b, f σ.matrix) ≤
          f (State.densityMatrixSetState M hM).matrix := iInf_le _ _
      _ = f M := by rw [State.densityMatrixSetState_matrix]
  · refine le_iInf ?_
    intro σ
    exact le_trans
      (iInf_le (fun M : CMatrix b => ⨅ hM : M ∈ State.densityMatrixSet b, f M)
        σ.matrix)
      (iInf_le (fun hM : σ.matrix ∈ State.densityMatrixSet b => f σ.matrix)
        (State.state_matrix_mem_densityMatrixSet σ))

/-- Supremum version of `state_iInf_matrix_eq_densityMatrixSet_iInf`. -/
theorem state_iSup_matrix_eq_densityMatrixSet_iSup
    {b : Type v1} [Fintype b] [DecidableEq b] (f : CMatrix b → EReal) :
    (⨆ σ : State b, f σ.matrix) =
      ⨆ M : CMatrix b, ⨆ _hM : M ∈ State.densityMatrixSet b, f M := by
  apply le_antisymm
  · refine iSup_le ?_
    intro σ
    calc
      f σ.matrix ≤
          (⨆ hM : σ.matrix ∈ State.densityMatrixSet b, f σ.matrix) :=
        le_iSup
          (fun hM : σ.matrix ∈ State.densityMatrixSet b => f σ.matrix)
          (State.state_matrix_mem_densityMatrixSet σ)
      _ ≤ ⨆ M : CMatrix b, ⨆ hM : M ∈ State.densityMatrixSet b, f M :=
        le_iSup
          (fun M : CMatrix b => ⨆ hM : M ∈ State.densityMatrixSet b, f M)
          σ.matrix
  · refine iSup_le ?_
    intro M
    refine iSup_le ?_
    intro hM
    calc
      f M = f (State.densityMatrixSetState M hM).matrix := by
        rw [State.densityMatrixSetState_matrix]
      _ ≤ (⨆ σ : State b, f σ.matrix) :=
        le_iSup (fun σ : State b => f σ.matrix) (State.densityMatrixSetState M hM)

/-- The full-rank matrix domain is equivalent to optimizing over states whose
density matrix is positive definite. -/
theorem fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
    {b : Type v1} [Fintype b] [DecidableEq b] (f : CMatrix b → EReal) :
    (⨅ sigma : {sigma : State b // sigma.matrix.PosDef}, f sigma.val.matrix) =
      ⨅ M : CMatrix b, ⨅ _hM : M ∈ State.fullRankDensityMatrixSet b, f M := by
  apply le_antisymm
  · refine le_iInf ?_
    intro M
    refine le_iInf ?_
    intro hM
    let sigma : {sigma : State b // sigma.matrix.PosDef} :=
      ⟨{ matrix := M, pos := hM.1.posSemidef, trace_eq_one := hM.2 }, hM.1⟩
    calc
      (⨅ sigma : {sigma : State b // sigma.matrix.PosDef}, f sigma.val.matrix) ≤
          f sigma.val.matrix := iInf_le _ _
      _ = f M := rfl
  · refine le_iInf ?_
    intro sigma
    exact le_trans
      (iInf_le
        (fun M : CMatrix b =>
          ⨅ hM : M ∈ State.fullRankDensityMatrixSet b, f M)
        sigma.val.matrix)
      (iInf_le
        (fun hM : sigma.val.matrix ∈ State.fullRankDensityMatrixSet b =>
          f sigma.val.matrix)
        ⟨sigma.property, sigma.val.trace_eq_one⟩)

/-- Supremum version of
`fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf`. -/
theorem fullRankState_iSup_matrix_eq_fullRankDensityMatrixSet_iSup
    {b : Type v1} [Fintype b] [DecidableEq b] (f : CMatrix b → EReal) :
    (⨆ sigma : {sigma : State b // sigma.matrix.PosDef}, f sigma.val.matrix) =
      ⨆ M : CMatrix b, ⨆ _hM : M ∈ State.fullRankDensityMatrixSet b, f M := by
  apply le_antisymm
  · refine iSup_le ?_
    intro sigma
    calc
      f sigma.val.matrix ≤
          (⨆ hM : sigma.val.matrix ∈ State.fullRankDensityMatrixSet b,
            f sigma.val.matrix) :=
        le_iSup
          (fun hM : sigma.val.matrix ∈ State.fullRankDensityMatrixSet b =>
            f sigma.val.matrix)
          ⟨sigma.property, sigma.val.trace_eq_one⟩
      _ ≤ ⨆ M : CMatrix b, ⨆ hM : M ∈ State.fullRankDensityMatrixSet b, f M :=
        le_iSup
          (fun M : CMatrix b =>
            ⨆ hM : M ∈ State.fullRankDensityMatrixSet b, f M)
          sigma.val.matrix
  · refine iSup_le ?_
    intro M
    refine iSup_le ?_
    intro hM
    let sigma : {sigma : State b // sigma.matrix.PosDef} :=
      ⟨{ matrix := M, pos := hM.1.posSemidef, trace_eq_one := hM.2 }, hM.1⟩
    calc
      f M = f sigma.val.matrix := rfl
      _ ≤ (⨆ sigma : {sigma : State b // sigma.matrix.PosDef}, f sigma.val.matrix) :=
        le_iSup
          (fun sigma : {sigma : State b // sigma.matrix.PosDef} =>
            f sigma.val.matrix)
          sigma

/-- The compact full-support matrix domain used by Sion is equivalent to
optimizing over states whose density matrix has the same lower spectral bound. -/
theorem uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
    {b : Type v1} [Fintype b] [DecidableEq b] {delta : ℝ}
    (f : CMatrix b → EReal) :
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        f σ.val.matrix) =
      ⨅ M : CMatrix b,
        ⨅ _hM : M ∈ State.uniformlyPositiveDensityMatrixSet delta b, f M := by
  apply le_antisymm
  · refine le_iInf ?_
    intro M
    refine le_iInf ?_
    intro hM
    let σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix} :=
      ⟨State.densityMatrixSetState M hM.1, by
        rw [State.densityMatrixSetState_matrix]
        exact hM.2⟩
    calc
      (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          f σ.val.matrix) ≤ f σ.val.matrix := iInf_le _ _
      _ = f M := by rw [State.densityMatrixSetState_matrix]
  · refine le_iInf ?_
    intro σ
    exact le_trans
      (iInf_le
        (fun M : CMatrix b =>
          ⨅ hM : M ∈ State.uniformlyPositiveDensityMatrixSet delta b, f M)
        σ.val.matrix)
      (iInf_le
        (fun hM : σ.val.matrix ∈ State.uniformlyPositiveDensityMatrixSet delta b =>
          f σ.val.matrix)
        ⟨State.state_matrix_mem_densityMatrixSet σ.val, σ.property⟩)

/-- Supremum version of
`uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf`. -/
theorem uniformlyPositiveState_iSup_matrix_eq_uniformlyPositiveDensityMatrixSet_iSup
    {b : Type v1} [Fintype b] [DecidableEq b] {delta : ℝ}
    (f : CMatrix b → EReal) :
    (⨆ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        f σ.val.matrix) =
      ⨆ M : CMatrix b,
        ⨆ _hM : M ∈ State.uniformlyPositiveDensityMatrixSet delta b, f M := by
  apply le_antisymm
  · refine iSup_le ?_
    intro σ
    calc
      f σ.val.matrix ≤
          (⨆ hM : σ.val.matrix ∈ State.uniformlyPositiveDensityMatrixSet delta b,
            f σ.val.matrix) :=
        le_iSup
          (fun hM : σ.val.matrix ∈ State.uniformlyPositiveDensityMatrixSet delta b =>
            f σ.val.matrix)
          ⟨State.state_matrix_mem_densityMatrixSet σ.val, σ.property⟩
      _ ≤ ⨆ M : CMatrix b,
          ⨆ hM : M ∈ State.uniformlyPositiveDensityMatrixSet delta b, f M :=
        le_iSup
          (fun M : CMatrix b =>
            ⨆ hM : M ∈ State.uniformlyPositiveDensityMatrixSet delta b, f M)
          σ.val.matrix
  · refine iSup_le ?_
    intro M
    refine iSup_le ?_
    intro hM
    let σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix} :=
      ⟨State.densityMatrixSetState M hM.1, by
        rw [State.densityMatrixSetState_matrix]
        exact hM.2⟩
    calc
      f M = f σ.val.matrix := by rw [State.densityMatrixSetState_matrix]
      _ ≤ (⨆ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          f σ.val.matrix) :=
        le_iSup
          (fun σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix} =>
            f σ.val.matrix)
          σ

/-- The uniformly-positive state domain used by the compact Sion step is a
subdomain of the full-rank state domain.

This is the EReal order bridge used when passing from the compact
`delta • I ≤ sigma_B` domain back to the full-rank branch of the KW
alternate-expression proof. -/
theorem fullRankState_iInf_le_uniformlyPositiveState_iInf_EReal
    {b : Type v1} [Fintype b] [DecidableEq b] {delta : ℝ}
    (hdelta : 0 < delta) (f : State b → EReal) :
    (⨅ σ : {σ : State b // σ.matrix.PosDef}, f σ.val) ≤
      ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix}, f σ.val := by
  refine le_iInf ?_
  intro σ
  have hσpos : σ.val.matrix.PosDef :=
    State.uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta
      ⟨State.state_matrix_mem_densityMatrixSet σ.val, σ.property⟩
  exact iInf_le (fun τ : {σ : State b // σ.matrix.PosDef} => f τ.val)
    ⟨σ.val, hσpos⟩

namespace State

/-- Raw weighted matrix form of the KW Sion trace bracket
`Tr[(A_A ⊗ σ_B^{-p} ⊗ τ_C^p) R]`.

The reusable minimax theorem in `ConditionalRenyiMinimax` treats the special
case `A_A = I_A`.  The sandwiched mutual-information alternate expression in
KW `EA_capacity.tex:2020-2025` instead keeps the fixed marginal weight
`rho_A^((1 - alpha) / alpha)` on the `A` leg, so this definition records the
exact source-shaped bracket before the remaining fixed-weight Sion layer is
proved. -/
def abcWeightedSidePowerTraceRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c))
    (σ : CMatrix b) (τ : CMatrix c) (p : ℝ) : ℝ :=
  ((Matrix.kronecker (Matrix.kronecker A (CFC.rpow σ (-p)))
      (CFC.rpow τ p) * R).trace).re

/-- The fixed-`A` KW trace bracket is nonnegative on PSD inputs. -/
theorem abcWeightedSidePowerTraceRe_nonneg
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef) (p : ℝ) :
    0 ≤ abcWeightedSidePowerTraceRe (a := a) A R σ τ p := by
  let S : CMatrix b := CFC.rpow σ (-p)
  let T : CMatrix c := CFC.rpow τ p
  have hS : S.PosSemidef := cMatrix_rpow_posSemidef (A := σ) (s := -p) hσ
  have hT : T.PosSemidef := cMatrix_rpow_posSemidef (A := τ) (s := p) hτ
  have hleft : (Matrix.kronecker A S).PosSemidef := hA.kronecker hS
  have hfull : (Matrix.kronecker (Matrix.kronecker A S) T).PosSemidef :=
    hleft.kronecker hT
  simpa [abcWeightedSidePowerTraceRe, S, T] using
    cMatrix_trace_mul_posSemidef_re_nonneg hfull hR

/-- The existing unweighted Sion bracket is the identity-weight instance of
the fixed-`A` bracket. -/
theorem abcWeightedSidePowerTraceRe_one
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b) (τ : CMatrix c) (p : ℝ) :
    abcWeightedSidePowerTraceRe (a := a) (b := b) (c := c)
        (1 : CMatrix a) R σ τ p =
      abcSidePowerTraceRe (a := a) R σ τ p := by
  rfl

private theorem trace_weighted_kronecker_right_add_smul_add_smul_re
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (K : CMatrix (Prod a b)) (R : CMatrix (Prod (Prod a b) c))
    (T U V : CMatrix c) (s t : ℝ) :
    ((Matrix.kronecker K (T + (s • U + t • V)) * R).trace).re =
      ((Matrix.kronecker K T * R).trace).re +
        (s * ((Matrix.kronecker K U * R).trace).re +
          t * ((Matrix.kronecker K V * R).trace).re) := by
  unfold Matrix.kronecker
  rw [Matrix.kronecker_add K T (s • U + t • V)]
  rw [Matrix.kronecker_add K (s • U) (t • V)]
  rw [Matrix.kronecker_smul s K U, Matrix.kronecker_smul t K V]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]

private theorem trace_weighted_kronecker_middle_add_smul_add_smul_re
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (K : CMatrix c)
    (T U V : CMatrix b) (s t : ℝ) :
    ((Matrix.kronecker (Matrix.kronecker A (T + (s • U + t • V))) K *
          R).trace).re =
      ((Matrix.kronecker (Matrix.kronecker A T) K * R).trace).re +
        (s * ((Matrix.kronecker (Matrix.kronecker A U) K * R).trace).re +
          t * ((Matrix.kronecker (Matrix.kronecker A V) K * R).trace).re) := by
  unfold Matrix.kronecker
  rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
    (by intro x y z; exact mul_add x y z) A T (s • U + t • V)]
  rw [Matrix.kroneckerMap_add_left (fun x y : ℂ => x * y)
    (by intro x y z; exact add_mul x y z)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A T)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A (s • U + t • V))
    K]
  rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
    (by intro x y z; exact mul_add x y z) A (s • U) (t • V)]
  rw [Matrix.kroneckerMap_add_left (fun x y : ℂ => x * y)
    (by intro x y z; exact add_mul x y z)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A (s • U))
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A (t • V))
    K]
  rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) s
    (by intro x y; exact mul_smul_comm s x y) A U]
  rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) t
    (by intro x y; exact mul_smul_comm t x y) A V]
  rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) s
    (by intro x y; exact smul_mul_assoc s x y)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A U) K]
  rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) t
    (by intro x y; exact smul_mul_assoc t x y)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A V) K]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]

private theorem trace_weighted_kronecker_right_continuous
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (K : CMatrix (Prod a b)) (R : CMatrix (Prod (Prod a b) c)) :
    Continuous fun T : CMatrix c => ((Matrix.kronecker K T * R).trace).re := by
  have hkr :
      Continuous fun T : CMatrix c => Matrix.kronecker K T := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace (hkr.matrix_mul continuous_const))

private theorem trace_weighted_kronecker_middle_continuous
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (K : CMatrix c) :
    Continuous fun T : CMatrix b =>
      ((Matrix.kronecker (Matrix.kronecker A T) K * R).trace).re := by
  have hinner :
      Continuous fun T : CMatrix b => Matrix.kronecker A T := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  have hkr :
      Continuous fun T : CMatrix b => Matrix.kronecker (Matrix.kronecker A T) K := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        ((hinner.matrix_elem x.1 y.1).mul continuous_const)
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace (hkr.matrix_mul continuous_const))

/-- The fixed-`A` KW bracket is concave in the positive-power side variable. -/
theorem abcWeightedSidePowerTraceRe_concaveOn_tau
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c))
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) := by
  constructor
  · intro x hx y hy s t hs ht hst
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx hs)
      (Matrix.PosSemidef.smul hy ht)
  · intro x hx y hy s t hs ht hst
    let S : CMatrix b := CFC.rpow σ (-p)
    let K : CMatrix (Prod a b) := Matrix.kronecker A S
    let T : CMatrix c := CFC.rpow (s • x + t • y) p
    let U : CMatrix c := CFC.rpow x p
    let V : CMatrix c := CFC.rpow y p
    let D : CMatrix c :=
      T + ((-s) • U + (-t) • V)
    have hpow :=
      (cMatrix_rpow_concaveOn_posSemidef_of_pos (a := c) hp0 hp1).2 hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ CFC.rpow (s • x + t • y) p -
          (s • CFC.rpow x p + t • CFC.rpow y p) := by
      exact sub_nonneg.mpr hpow
    have hD_nonneg : 0 ≤ D := by
      simpa [D, T, U, V, sub_eq_add_neg, neg_add_rev, add_comm, add_left_comm, add_assoc]
        using hdiff_nonneg
    have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hD_nonneg
    have hS : S.PosSemidef :=
      cMatrix_rpow_posSemidef (A := σ) (s := -p) hσ
    have hleft : K.PosSemidef :=
      hA.kronecker hS
    have hfull : (Matrix.kronecker K D).PosSemidef :=
      hleft.kronecker hD
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hfull hR
    change 0 ≤ ((Matrix.kronecker K D * R).trace).re at htrace
    have htrace' :
        0 ≤ abcWeightedSidePowerTraceRe (a := a) A R σ (s • x + t • y) p +
          (-s * abcWeightedSidePowerTraceRe (a := a) A R σ x p +
            -t * abcWeightedSidePowerTraceRe (a := a) A R σ y p) := by
      rw [trace_weighted_kronecker_right_add_smul_add_smul_re K R T U V (-s) (-t)]
        at htrace
      have hT :
          ((Matrix.kronecker K T * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R σ (s • x + t • y) p := by
        simp [abcWeightedSidePowerTraceRe, K, S, T]
      have hU :
          ((Matrix.kronecker K U * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R σ x p := by
        simp [abcWeightedSidePowerTraceRe, K, S, U]
      have hV :
          ((Matrix.kronecker K V * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R σ y p := by
        simp [abcWeightedSidePowerTraceRe, K, S, V]
      rw [hT, hU, hV] at htrace
      exact htrace
    have hle :
        s * abcWeightedSidePowerTraceRe (a := a) A R σ x p +
          t * abcWeightedSidePowerTraceRe (a := a) A R σ y p ≤
            abcWeightedSidePowerTraceRe (a := a) A R σ (s • x + t • y) p := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- The fixed-`A` KW bracket is quasiconcave in the positive-power side variable. -/
theorem abcWeightedSidePowerTraceRe_quasiconcaveOn_tau
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconcaveOn ℝ ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c))
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) :=
  (abcWeightedSidePowerTraceRe_concaveOn_tau (a := a) hA hR hσ hp0 hp1).quasiconcaveOn

/-- Continuity of the fixed-`A` KW bracket in the positive-power side variable. -/
theorem abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    ContinuousOn
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) := by
  let K : CMatrix (Prod a b) := Matrix.kronecker A (CFC.rpow σ (-p))
  have htrace := trace_weighted_kronecker_right_continuous (a := a) (b := b) K R
  have hpow := cMatrix_rpow_continuousOn_posSemidef_of_pos (a := c) hp0
  simpa [abcWeightedSidePowerTraceRe, K, Function.comp_def] using
    htrace.comp_continuousOn hpow

/-- Lower semicontinuity of the fixed-`A` KW bracket in the negative-power side
variable on the PSD cone. -/
theorem abcWeightedSidePowerTraceRe_lowerSemicontinuousOn_tau_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    LowerSemicontinuousOn
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) :=
  ContinuousOn.lowerSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef (a := a) A R σ hp0)

/-- Upper semicontinuity of the fixed-`A` KW bracket in the positive-power side
variable on the PSD cone. -/
theorem abcWeightedSidePowerTraceRe_upperSemicontinuousOn_tau_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    UpperSemicontinuousOn
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) :=
  ContinuousOn.upperSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef (a := a) A R σ hp0)

/-- The fixed-`A` KW bracket is convex in the negative-power side variable on
the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_convexOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b))
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) := by
  constructor
  · exact posDefMatrixSet_convex (a := b)
  · intro x hx y hy s t hs ht hst
    let S : CMatrix b := CFC.rpow (s • x + t • y) (-p)
    let U : CMatrix b := CFC.rpow x (-p)
    let V : CMatrix b := CFC.rpow y (-p)
    let T : CMatrix c := CFC.rpow τ p
    let D : CMatrix b := (-1 : ℝ) • S + (s • U + t • V)
    have hp_neg : -p ∈ Set.Icc (-1 : ℝ) 0 := by
      constructor <;> linarith
    have hpow :=
      (cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero (a := b) hp_neg).2
        hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ (s • CFC.rpow x (-p) + t • CFC.rpow y (-p)) -
          CFC.rpow (s • x + t • y) (-p) := by
      exact sub_nonneg.mpr hpow
    have hD_nonneg : 0 ≤ D := by
      simpa [D, S, U, V, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hdiff_nonneg
    have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hD_nonneg
    have hT : T.PosSemidef :=
      cMatrix_rpow_posSemidef (A := τ) (s := p) hτ
    have hleft : (Matrix.kronecker A D).PosSemidef :=
      hA.kronecker hD
    have hfull : (Matrix.kronecker (Matrix.kronecker A D) T).PosSemidef :=
      hleft.kronecker hT
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hfull hR
    change 0 ≤
      ((Matrix.kronecker (Matrix.kronecker A D) T * R).trace).re at htrace
    have htrace' :
        0 ≤ -abcWeightedSidePowerTraceRe (a := a) A R (s • x + t • y) τ p +
          (s * abcWeightedSidePowerTraceRe (a := a) A R x τ p +
            t * abcWeightedSidePowerTraceRe (a := a) A R y τ p) := by
      rw [trace_weighted_kronecker_middle_add_smul_add_smul_re A R T
        ((-1 : ℝ) • S) U V s t] at htrace
      have hS :
          ((Matrix.kronecker (Matrix.kronecker A ((-1 : ℝ) • S)) T * R).trace).re =
            -abcWeightedSidePowerTraceRe (a := a) A R (s • x + t • y) τ p := by
        simp only [abcWeightedSidePowerTraceRe, S, T]
        unfold Matrix.kronecker
        rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) (-1 : ℝ)
          (by intro x y; exact mul_smul_comm (-1 : ℝ) x y) A
          (CFC.rpow (s • x + t • y) (-p))]
        rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) (-1 : ℝ)
          (by intro x y; exact smul_mul_assoc (-1 : ℝ) x y)
          (Matrix.kroneckerMap (fun x y : ℂ => x * y) A
            (CFC.rpow (s • x + t • y) (-p)))
          (CFC.rpow τ p)]
        rw [Matrix.smul_mul, Matrix.trace_smul]
        simp
      have hU :
          ((Matrix.kronecker (Matrix.kronecker A U) T * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R x τ p := by
        simp [abcWeightedSidePowerTraceRe, U, T]
      have hV :
          ((Matrix.kronecker (Matrix.kronecker A V) T * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R y τ p := by
        simp [abcWeightedSidePowerTraceRe, V, T]
      rw [hS, hU, hV] at htrace
      exact htrace
    have hle :
        abcWeightedSidePowerTraceRe (a := a) A R (s • x + t • y) τ p ≤
          s * abcWeightedSidePowerTraceRe (a := a) A R x τ p +
            t * abcWeightedSidePowerTraceRe (a := a) A R y τ p := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- The fixed-`A` KW bracket is quasiconvex in the negative-power side variable
on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_quasiconvexOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconvexOn ℝ ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b))
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) :=
  (abcWeightedSidePowerTraceRe_convexOn_sigma_posDef (a := a) hA hR hτ hp0 hp1)
    |>.quasiconvexOn

/-- Continuity of the fixed-`A` KW bracket in the negative-power side variable
on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    ContinuousOn
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) := by
  have htrace :=
    trace_weighted_kronecker_middle_continuous (a := a) (b := b) A R (CFC.rpow τ p)
  have hpow := cMatrix_rpow_continuousOn_posDef (a := b) (-p)
  simpa [abcWeightedSidePowerTraceRe, Function.comp_def] using
    htrace.comp_continuousOn hpow

/-- Lower semicontinuity of the fixed-`A` KW bracket in the negative-power side
variable on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_lowerSemicontinuousOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    LowerSemicontinuousOn
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) :=
  ContinuousOn.lowerSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef (a := a) A R τ p)

/-- Upper semicontinuity of the fixed-`A` KW bracket in the negative-power side
variable on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_upperSemicontinuousOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    UpperSemicontinuousOn
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) :=
  ContinuousOn.upperSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef (a := a) A R τ p)

/-- Source-faithful Sion minimax equality for the fixed-`A` KW trace bracket on
a compact full-support `sigma` domain.

This is the fixed-marginal-weight version needed for the sandwiched
mutual-information alternate expression in KW `EA_capacity.tex:2020-2025`. -/
theorem uniformlyPositiveDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    {delta p : ℝ} (hdelta : 0 < delta)
    (hneB : (uniformlyPositiveDensityMatrixSet delta b).Nonempty)
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (⨅ σ ∈ uniformlyPositiveDensityMatrixSet delta b, ⨆ τ ∈ densityMatrixSet c,
        (abcWeightedSidePowerTraceRe (a := a) A R σ τ p : EReal)) =
      ⨆ τ ∈ densityMatrixSet c, ⨅ σ ∈ uniformlyPositiveDensityMatrixSet delta b,
        (abcWeightedSidePowerTraceRe (a := a) A R σ τ p : EReal) := by
  exact sion_iInf_iSup_eq_iSup_iInf
    hneB
    (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta))
    (uniformlyPositiveDensityMatrixSet_isCompact (a := b) (delta := delta))
    (fun τ hτ => by
      exact continuous_coe_real_ereal.comp_lowerSemicontinuousOn
        ((abcWeightedSidePowerTraceRe_lowerSemicontinuousOn_sigma_posDef
          (a := a) A R τ p).mono
          (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta))
        EReal.coe_strictMono.monotone)
    (fun τ hτ => by
      simpa [Function.comp_def] using
        (Convex.quasiconvexOn_restrict
          (abcWeightedSidePowerTraceRe_quasiconvexOn_sigma_posDef
            (a := a) hA hR hτ.1 hp0 hp1)
          (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta)
          (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta)))
            |>.monotone_comp EReal.coe_strictMono.monotone)
    (densityMatrixSet_convex (a := c))
    (fun σ hσ => by
      exact continuous_coe_real_ereal.comp_upperSemicontinuousOn
        ((abcWeightedSidePowerTraceRe_upperSemicontinuousOn_tau_posSemidef
          (a := a) A R σ hp0).mono
          (fun τ hτ => hτ.1))
        EReal.coe_strictMono.monotone)
    (fun σ hσ => by
      simpa [Function.comp_def] using
        (Convex.quasiconcaveOn_restrict
          (abcWeightedSidePowerTraceRe_quasiconcaveOn_tau
            (a := a) hA hR hσ.1.1 hp0 hp1)
          (fun τ hτ => hτ.1)
          (densityMatrixSet_convex (a := c))).monotone_comp
            EReal.coe_strictMono.monotone)

/-- Source-faithful Sion minimax equality for the fixed-`A` KW trace bracket
on the full-rank `sigma` domain.

Unlike the compact-cutoff lemma above, this uses the purifying-side density
matrices as Sion's compact variable and applies Sion to the negative saddle
function.  It is the no-cutoff exchange needed for the reverse half of the
state alternate-expression proof in KW `EA_capacity.tex:2018-2035`. -/
theorem fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    {p : ℝ}
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : (fullRankDensityMatrixSet b) sigma,
        ⨆ tau : CMatrix c,
          ⨆ _hTau : (densityMatrixSet c) tau,
            (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal)) =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : (densityMatrixSet c) tau,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (fullRankDensityMatrixSet b) sigma,
              (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal) := by
  let F : {sigma : CMatrix b // (fullRankDensityMatrixSet b) sigma} →
      {tau : CMatrix c // (densityMatrixSet c) tau} → EReal :=
    fun sigma tau =>
      (abcWeightedSidePowerTraceRe (a := a) A R sigma.1 tau.1 p : EReal)
  have hnegMem :
      (⨅ tau : CMatrix c,
        ⨅ _hTau : (densityMatrixSet c) tau,
          ⨆ sigma : CMatrix b,
            ⨆ _hSigma : (fullRankDensityMatrixSet b) sigma,
              -((abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal))) =
        ⨆ sigma : CMatrix b,
          ⨆ _hSigma : (fullRankDensityMatrixSet b) sigma,
            ⨅ tau : CMatrix c,
              ⨅ _hTau : (densityMatrixSet c) tau,
                -((abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal)) := by
    exact State.sion_iInf_iSup_eq_iSup_iInf
      (densityMatrixSet_nonempty (a := c))
      (densityMatrixSet_convex (a := c))
      (densityMatrixSet_isCompact (a := c))
      (fun sigma hSigma => by
        have hcontReal : ContinuousOn
            (fun tau : CMatrix c =>
              abcWeightedSidePowerTraceRe (a := a) A R sigma tau p)
            (densityMatrixSet c) :=
          (abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef
            (a := a) A R sigma hp0).mono (fun tau hTau => hTau.1)
        have hcontE : ContinuousOn
            (fun tau : CMatrix c =>
              (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal))
            (densityMatrixSet c) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.lowerSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun sigma hSigma => by
        simpa [Function.comp_def] using
          (Convex.quasiconcaveOn_restrict
            (abcWeightedSidePowerTraceRe_quasiconcaveOn_tau
              (a := a) hA hR hSigma.1.posSemidef hp0 hp1)
            (fun tau hTau => hTau.1)
            (densityMatrixSet_convex (a := c))).antitone_comp
              antitone_ereal_neg_coe)
      (fullRankDensityMatrixSet_convex (a := b))
      (fun tau hTau => by
        have hcontReal : ContinuousOn
            (fun sigma : CMatrix b =>
              abcWeightedSidePowerTraceRe (a := a) A R sigma tau p)
            (fullRankDensityMatrixSet b) :=
          (abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef
            (a := a) A R tau p).mono (fun sigma hSigma => hSigma.1)
        have hcontE : ContinuousOn
            (fun sigma : CMatrix b =>
              (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal))
            (fullRankDensityMatrixSet b) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.upperSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun tau hTau => by
        simpa [Function.comp_def] using
          (Convex.quasiconvexOn_restrict
            (abcWeightedSidePowerTraceRe_quasiconvexOn_sigma_posDef
              (a := a) hA hR hTau.1 hp0 hp1)
            (fun sigma hSigma => hSigma.1)
            (fullRankDensityMatrixSet_convex (a := b))).antitone_comp
              antitone_ereal_neg_coe)
  have hnegSub :
      (⨅ tau : {tau : CMatrix c // (densityMatrixSet c) tau},
        ⨆ sigma : {sigma : CMatrix b // (fullRankDensityMatrixSet b) sigma},
          -F sigma tau) =
        ⨆ sigma : {sigma : CMatrix b // (fullRankDensityMatrixSet b) sigma},
          ⨅ tau : {tau : CMatrix c // (densityMatrixSet c) tau},
            -F sigma tau := by
    simpa [F, iInf_subtype', iSup_subtype'] using hnegMem
  have hsub := ereal_sion_from_neg F hnegSub
  simpa [F, iInf_subtype', iSup_subtype'] using hsub

end State

/-- KW high-`alpha` specialization of the fixed-`A` Sion exchange for the raw
alternate-expression trace bracket.

This is the fixed marginal-weight version of
`sandwichedAlpha_sion_abcSidePowerTraceRe_EReal`. -/
theorem sandwichedAlpha_sion_abcWeightedSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (halpha : 1 < alpha) :
    (⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
        ⨆ τ ∈ State.densityMatrixSet c,
          (State.abcWeightedSidePowerTraceRe (a := a) A R σ τ
            ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ ∈ State.densityMatrixSet c,
        ⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          (State.abcWeightedSidePowerTraceRe (a := a) A R σ τ
            ((alpha - 1) / alpha) : EReal) := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  exact State.uniformlyPositiveDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
    (a := a) (b := b) (c := c)
    hdelta_pos
    (State.uniformlyPositiveDensityMatrixSet_nonempty (a := b) hdelta_le)
    hA hR hp.1 (le_of_lt hp.2)

namespace PureVector

/-- Reindex `(A1B1C1) x (A2B2C2)` into the KW product-purification order
`((A1 x A2) x (B1 x B2)) x (C1 x C2)`. -/
def bipartiteProductPurificationEquiv
    {a1 b1 c1 a2 b2 c2 : Type*} :
    Prod (Prod (Prod a1 b1) c1) (Prod (Prod a2 b2) c2) ≃
      Prod (Prod (Prod a1 a2) (Prod b1 b2)) (Prod c1 c2) where
  toFun x := (((x.1.1.1, x.2.1.1), (x.1.1.2, x.2.1.2)), (x.1.2, x.2.2))
  invFun x := (((x.1.1.1, x.1.2.1), x.2.1), ((x.1.1.2, x.1.2.2), x.2.2))
  left_inv := by
    intro x
    rcases x with ⟨⟨⟨i1, j1⟩, k1⟩, ⟨⟨i2, j2⟩, k2⟩⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨⟨i1, i2⟩, ⟨j1, j2⟩⟩, ⟨k1, k2⟩⟩
    rfl

/-- Product purification arranged in the KW order
`((A1 x A2) x (B1 x B2)) x (C1 x C2)`.

This is the concrete product purification used in
`EA_capacity.tex:1200-1207` when the alternate expression is restricted to
product side-information states on the purifying systems. -/
def bipartiteProductPurification
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2)) :
    PureVector (Prod (Prod (Prod a1 a2) (Prod b1 b2)) (Prod c1 c2)) :=
  (psi.prod phi).reindex bipartiteProductPurificationEquiv

@[simp]
theorem bipartiteProductPurification_amp
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (p : Prod (Prod (Prod a1 a2) (Prod b1 b2)) (Prod c1 c2)) :
    (bipartiteProductPurification psi phi).amp p =
      psi.amp ((p.1.1.1, p.1.2.1), p.2.1) *
        phi.amp ((p.1.1.2, p.1.2.2), p.2.2) :=
  rfl

/-- Definition-level bridge from the source common bracket to the raw matrix
trace functional used by the Sion API. -/
theorem upwardRenyiDualityCommonBracket_re_eq_abcSidePowerTraceRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c)) (σB : State b) (τC : State c)
    (alphaPrime : ℝ) :
    (ψ.upwardRenyiDualityCommonBracket σB τC alphaPrime).re =
      State.abcSidePowerTraceRe (a := a) ψ.state.matrix σB.matrix τC.matrix
        alphaPrime := by
  rfl

/-- KW mutual-information Sion bracket with the fixed `rho_A` side weight from
`EA_capacity.tex:2020-2025`. -/
def sandwichedMutualInformationSionBracketRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) : ℝ :=
  State.abcWeightedSidePowerTraceRe
    (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
    ψ.state.matrix σB.matrix τC.matrix ((alpha - 1) / alpha)

/-- The KW sandwiched mutual-information Sion bracket is nonnegative. -/
theorem sandwichedMutualInformationSionBracketRe_nonneg
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha := by
  unfold sandwichedMutualInformationSionBracketRe
  exact State.abcWeightedSidePowerTraceRe_nonneg
    (cMatrix_rpow_posSemidef
      (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos)
    ψ.state.pos σB.pos τC.pos ((alpha - 1) / alpha)

/-- Definition-level source form of the KW fixed-`rho_A` Sion bracket. -/
theorem sandwichedMutualInformationSionBracketRe_eq_source
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          (CFC.rpow τC.matrix ((alpha - 1) / alpha)) *
        ψ.state.matrix).trace).re := by
  unfold sandwichedMutualInformationSionBracketRe State.abcWeightedSidePowerTraceRe
  have hsigma_exp : -((alpha - 1) / alpha) = (1 - alpha) / alpha := by
    ring
  rw [hsigma_exp]

/-- The `B`-system matrix obtained by tracing the `A` and `C` legs after
applying the fixed `rho_A` and `tau_C` powers from KW
`EA_capacity.tex:2028-2032`. -/
def sandwichedMutualInformationACTraceMatrix
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) : CMatrix b :=
  fun j j' =>
    ∑ i : a, ∑ k : c,
      ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (1 : CMatrix b))
          (CFC.rpow τC.matrix ((alpha - 1) / alpha)) *
        ψ.state.matrix) ((i, j), k) ((i, j'), k))

/-- The `AC`-side weight from KW `EA_capacity.tex:2028-2035`, after
grouping the traced systems together. -/
def sandwichedMutualInformationACWeight
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) : CMatrix (Prod a c) :=
  Matrix.kronecker
    (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
    (CFC.rpow τC.matrix ((alpha - 1) / alpha))

/-- Coordinate form of the KW trace-out-`AC` matrix. -/
theorem sandwichedMutualInformationACTraceMatrix_apply
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) (j j' : b) :
    sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha j j' =
      ∑ i : a, ∑ k : c, ∑ i' : a, ∑ k' : c,
        sandwichedMutualInformationACWeight rhoA τC alpha (i, k) (i', k') *
          ψ.amp ((i', j), k') * star (ψ.amp ((i, j'), k)) := by
  simp [sandwichedMutualInformationACTraceMatrix, sandwichedMutualInformationACWeight,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    PureVector.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type, mul_assoc]

/-- The `AC`-grouped amplitude obtained by applying the square-root of the
KW `AC` weight and leaving the `B` system untouched.  Its rank-one matrix is
the PSD representative of the trace-cyclic expression in
KW `EA_capacity.tex:2028-2035`. -/
def sandwichedMutualInformationACWeightedAmp
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) : Prod (Prod a c) b → ℂ :=
  Matrix.mulVec
    (Matrix.kronecker
      (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha))
      (1 : CMatrix b))
    (fun p : Prod (Prod a c) b => ψ.amp ((p.1.1, p.2), p.1.2))

/-- The KW `AC` weight is positive semidefinite. -/
theorem sandwichedMutualInformationACWeight_posSemidef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) :
    (sandwichedMutualInformationACWeight rhoA τC alpha).PosSemidef := by
  exact
    (cMatrix_rpow_posSemidef
        (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos).kronecker
      (cMatrix_rpow_posSemidef
        (A := τC.matrix) (s := (alpha - 1) / alpha) τC.pos)

/-- The KW `AC` weight is positive definite when both side weights are full
rank. -/
theorem sandwichedMutualInformationACWeight_posDef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef) (alpha : ℝ) :
    (sandwichedMutualInformationACWeight rhoA τC alpha).PosDef := by
  exact
    (cMatrix_rpow_posDef_of_posDef hrhoA ((1 - alpha) / alpha)).kronecker
      (cMatrix_rpow_posDef_of_posDef hτC ((alpha - 1) / alpha))

/-- The square root of the KW `AC` weight squares back to the weight. -/
theorem sandwichedMutualInformationACWeight_sqrt_mul_self
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) :
    CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha) *
        CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha) =
      sandwichedMutualInformationACWeight rhoA τC alpha := by
  exact CFC.sqrt_mul_sqrt_self _
    (sandwichedMutualInformationACWeight_posSemidef rhoA τC alpha).nonneg

/-- The square root of the KW `AC` weight is Hermitian. -/
theorem sandwichedMutualInformationACWeight_sqrt_isHermitian
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) :
    (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)).IsHermitian := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    (CFC.sqrt_nonneg (sandwichedMutualInformationACWeight rhoA τC alpha))).isHermitian

/-- The square root of a full-rank KW `AC` weight is invertible. -/
theorem sandwichedMutualInformationACWeight_sqrt_isUnit_posDef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef) (alpha : ℝ) :
    IsUnit (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)) := by
  have hW : (sandwichedMutualInformationACWeight rhoA τC alpha).PosDef :=
    sandwichedMutualInformationACWeight_posDef rhoA τC hrhoA hτC alpha
  have hsqrt :
      (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)).PosDef := by
    rw [CFC.sqrt_eq_rpow]
    exact cMatrix_rpow_posDef_of_posDef hW (1 / 2)
  exact hsqrt.isUnit

/-- The rank-one matrix built from the KW `AC` square-root-weighted amplitude is
positive semidefinite. -/
theorem sandwichedMutualInformationACWeightedAmp_rankOne_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) :
    (rankOneMatrix
      (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)).PosSemidef :=
  rankOneMatrix_pos (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)

/-- A rank-one kernel is zero exactly when its generating vector is zero. -/
private theorem rankOneMatrix_eq_zero_iff
    {d : Type*} (v : d → Complex) :
    rankOneMatrix v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hdiag := congrFun (congrFun h i) i
    simp [rankOneMatrix_apply] at hdiag
    exact hdiag
  · intro h
    ext i j
    simp [rankOneMatrix_apply, h]

/-- Repartitioning a normalized `ABC` pure vector as an `ACB` amplitude does not
make it zero. -/
private theorem pureVector_acb_amp_ne_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    (fun p : Prod (Prod a c) b => ψ.amp ((p.1.1, p.2), p.1.2)) ≠ 0 := by
  intro hzero
  have hamp_zero : ψ.amp = 0 := by
    funext x
    rcases x with ⟨⟨i, j⟩, k⟩
    have hentry := congrFun hzero ((i, k), j)
    simpa using hentry
  have htrace_zero : (rankOneMatrix ψ.amp).trace = 0 := by
    rw [hamp_zero]
    simp [rankOneMatrix]
  rw [ψ.trace_rankOne_eq_one] at htrace_zero
  norm_num at htrace_zero

/-- Full-rank side weights keep the KW `AC` square-root-weighted amplitude
nonzero. -/
theorem sandwichedMutualInformationACWeightedAmp_ne_zero_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    (alpha : ℝ) :
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha ≠ 0 := by
  let S : CMatrix (Prod a c) := CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)
  let psiACB : Prod (Prod a c) b → Complex := fun p => ψ.amp ((p.1.1, p.2), p.1.2)
  have hpsi : psiACB ≠ 0 := by
    simpa [psiACB] using pureVector_acb_amp_ne_zero ψ
  have hS : IsUnit S := by
    simpa [S] using
      sandwichedMutualInformationACWeight_sqrt_isUnit_posDef rhoA τC hrhoA hτC alpha
  have hK : IsUnit (Matrix.kronecker S (1 : CMatrix b)) := by
    exact Matrix.IsUnit.kronecker hS isUnit_one
  intro hzero
  have hmul :
      Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB = 0 := by
    simpa [sandwichedMutualInformationACWeightedAmp, S, psiACB] using hzero
  have hmul' :
      Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB =
        Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) 0 := by
    simpa using hmul
  exact hpsi ((Matrix.mulVec_injective_of_isUnit hK) hmul')

/-- Coordinate form of the KW `AC` square-root-weighted amplitude. -/
theorem sandwichedMutualInformationACWeightedAmp_apply
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) (i : a) (k : c) (j : b) :
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha ((i, k), j) =
      ∑ i' : a, ∑ k' : c,
        (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)) (i, k) (i', k') *
          ψ.amp ((i', j), k') := by
  unfold sandwichedMutualInformationACWeightedAmp
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  simp [Fintype.sum_prod_type]

/-- Moving a Hermitian square-root weight from a rank-one vector back to the
left-hand weight before tracing out the weighted system. -/
theorem partialTraceA_rankOne_kron_left_mulVec_eq_weight_mul
    {d : Type u1} {b : Type v1} [Fintype d] [DecidableEq d]
    [Fintype b] [DecidableEq b]
    (S : CMatrix d) (hS : S.IsHermitian) (psi : Prod d b → ℂ) :
    partialTraceA (a := d) (b := b)
        (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psi)) =
      partialTraceA (a := d) (b := b)
        (Matrix.kronecker (S * S) (1 : CMatrix b) * rankOneMatrix psi) := by
  ext j j'
  have hstar : ∀ x y : d, star (S x y) = S y x := by
    intro x y
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS.eq y) x
  have hstar' : ∀ x y : d, (starRingEnd ℂ) (S x y) = S y x := hstar
  simp [partialTraceA, rankOneMatrix_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simp_rw [hstar']
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, z]
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_congr rfl ?_
  intro x_1 _
  refine Finset.sum_congr rfl ?_
  intro x_2 _
  ring_nf

/-- The KW trace-out-`AC` matrix is the partial trace of the square-root
weighted rank-one vector.  This provides the PSD representative needed for the
reverse-Holder variational formula in `EA_capacity.tex:2032-2035`. -/
theorem partialTraceA_rankOne_ACWeightedAmp_eq_ACTraceMatrix
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) :
    partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)) =
      sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha := by
  let S : CMatrix (Prod a c) :=
    CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)
  let psiACB : Prod (Prod a c) b → ℂ := fun p => ψ.amp ((p.1.1, p.2), p.1.2)
  have hmove :
      partialTraceA (a := Prod a c) (b := b)
          (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB)) =
        partialTraceA (a := Prod a c) (b := b)
          (Matrix.kronecker (S * S) (1 : CMatrix b) * rankOneMatrix psiACB) := by
    exact partialTraceA_rankOne_kron_left_mulVec_eq_weight_mul S
      (by
        simpa [S] using
          (sandwichedMutualInformationACWeight_sqrt_isHermitian rhoA τC alpha))
      psiACB
  have hsqrt :
      S * S = sandwichedMutualInformationACWeight rhoA τC alpha := by
    simpa [S] using
      (sandwichedMutualInformationACWeight_sqrt_mul_self rhoA τC alpha)
  calc
    partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha))
        =
      partialTraceA (a := Prod a c) (b := b)
          (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB)) := by
        simp [sandwichedMutualInformationACWeightedAmp, S, psiACB]
    _ =
      partialTraceA (a := Prod a c) (b := b)
        (Matrix.kronecker (S * S) (1 : CMatrix b) * rankOneMatrix psiACB) := hmove
    _ =
      partialTraceA (a := Prod a c) (b := b)
        (Matrix.kronecker (sandwichedMutualInformationACWeight rhoA τC alpha)
          (1 : CMatrix b) * rankOneMatrix psiACB) := by
        rw [hsqrt]
    _ = sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha := by
        ext j j'
        rw [sandwichedMutualInformationACTraceMatrix_apply]
        simp [partialTraceA, rankOneMatrix_apply, Matrix.mul_apply, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
          mul_assoc, psiACB]

/-- The KW trace-out-`AC` matrix is positive semidefinite, as required by the
positive reverse-Holder variational formula. -/
theorem sandwichedMutualInformationACTraceMatrix_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) :
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha).PosSemidef := by
  have hpt :
      (partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha))).PosSemidef :=
    partialTraceA_posSemidef
      (sandwichedMutualInformationACWeightedAmp_rankOne_posSemidef rhoA ψ τC alpha)
  have heq := partialTraceA_rankOne_ACWeightedAmp_eq_ACTraceMatrix rhoA ψ τC alpha
  simpa [heq] using hpt

/-- Full-rank side weights make the KW `AC` trace matrix nonzero. -/
theorem sandwichedMutualInformationACTraceMatrix_ne_zero_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    (alpha : ℝ) :
    sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0 := by
  let v : Prod (Prod a c) b → Complex :=
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha
  have hvne : v ≠ 0 := by
    simpa [v] using
      sandwichedMutualInformationACWeightedAmp_ne_zero_posDef
        rhoA ψ τC hrhoA hτC alpha
  intro hzero
  have hptzero :
      partialTraceA (a := Prod a c) (b := b) (rankOneMatrix v) = 0 := by
    rw [partialTraceA_rankOne_ACWeightedAmp_eq_ACTraceMatrix]
    simpa [v] using hzero
  have htrace_zero : (rankOneMatrix v).trace = 0 := by
    have htrace := congrArg Matrix.trace hptzero
    simpa [partialTraceA_trace] using htrace
  have hrank_zero : rankOneMatrix v = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (rankOneMatrix_pos v)).mp htrace_zero
  exact hvne ((rankOneMatrix_eq_zero_iff v).mp hrank_zero)

/-- Full-rank side weights make the KW `AC` trace-matrix Schatten norm strictly
positive on the high-alpha branch. -/
theorem psdSchattenPNorm_ACTraceMatrix_pos_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    {alpha : ℝ} (_halpha : 1 < alpha) :
    0 <
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1)) := by
  exact psdSchattenPNorm_pos_of_ne_zero
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
    (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
    (sandwichedMutualInformationACTraceMatrix_ne_zero_posDef
      rhoA ψ τC hrhoA hτC alpha)

private theorem sum_b_a_c_a_b_c_reorder
    {aa bb cc : Type*} [Fintype aa] [Fintype bb] [Fintype cc]
    (f : bb -> aa -> cc -> aa -> bb -> cc -> ℂ) :
    (∑ j : bb, ∑ i : aa, ∑ k : cc, ∑ i' : aa, ∑ j' : bb, ∑ k' : cc,
        f j i k i' j' k') =
      ∑ k : cc, ∑ i : aa, ∑ j : bb, ∑ i' : aa, ∑ j' : bb, ∑ k' : cc,
        f j i k i' j' k' := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  conv_rhs =>
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
  let e : (((((bb × aa) × cc) × aa) × bb) × cc) ≃
      (((((cc × aa) × bb) × aa) × bb) × cc) := {
    toFun := fun t =>
      (((((t.1.1.1.2, t.1.1.1.1.2), t.1.1.1.1.1), t.1.1.2), t.1.2), t.2)
    invFun := fun s =>
      (((((s.1.1.1.2, s.1.1.1.1.2), s.1.1.1.1.1), s.1.1.2), s.1.2), s.2)
    left_inv := by
      intro t
      rcases t with ⟨⟨⟨⟨⟨j, i⟩, k⟩, i'⟩, j'⟩, k'⟩
      rfl
    right_inv := by
      intro s
      rcases s with ⟨⟨⟨⟨⟨k, i⟩, j⟩, i'⟩, j'⟩, k'⟩
      rfl }
  simpa [e] using
    (Finset.sum_equiv e (s := Finset.univ) (t := Finset.univ)
      (fun _ => by simp)
      (fun t _ => by
        rcases t with ⟨⟨⟨⟨⟨j, i⟩, k⟩, i'⟩, j'⟩, k'⟩
        rfl))

/-- Trace-out-`AC` form of the KW Sion bracket.

This is the Lean trace-cyclic/partial-trace step in
`EA_capacity.tex:2026-2032`, before applying the positive reverse-Holder
variational formula in the `B` system. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_sigma_mul_ACTraceMatrix
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((CFC.rpow σB.matrix ((1 - alpha) / alpha) *
        sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha).trace).re := by
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  simp only [sandwichedMutualInformationACTraceMatrix, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  congr 1
  simp only [Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp_rw [Finset.mul_sum]
  conv_rhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y, 2, y_1]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y, 2, y_1, 2, x_2]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y, 2, y_1, 2, x_2, 2, y_2]
    rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  conv_rhs =>
    rw [sum_b_a_c_a_b_c_reorder]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i' _
  refine Finset.sum_congr rfl ?_
  intro j' _
  refine Finset.sum_congr rfl ?_
  intro k' _
  ring_nf

/-- Reverse-Holder-facing trace direction for the KW Sion bracket. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha *
        CFC.rpow σB.matrix ((1 - alpha) / alpha)).trace).re := by
  rw [sandwichedMutualInformationSionBracketRe_eq_trace_sigma_mul_ACTraceMatrix]
  exact congrArg Complex.re (Matrix.trace_mul_comm
    (CFC.rpow σB.matrix ((1 - alpha) / alpha))
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha))

/-- The `AB`-side weight in the proof of KW `eq-sand_rel_mut_inf_alt`. -/
def sandwichedMutualInformationABWeight
    {a : Type u1} {b : Type v1}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoA : State a) (σB : State b) (alpha : ℝ) : CMatrix (Prod a b) :=
  Matrix.kronecker
    (CFC.rpow rhoA.matrix ((1 - alpha) / (2 * alpha)))
    (CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha)))

/-- Coordinate form of a left tensor factor acting on a bipartite vector. -/
theorem kronecker_left_one_mulVec_apply
    {d : Type u1} {c : Type u2} [Fintype d] [DecidableEq d]
    [Fintype c] [DecidableEq c]
    (W : CMatrix d) (psi : Prod d c → ℂ) (i : d) (k : c) :
    (Matrix.kronecker W (1 : CMatrix c)).mulVec psi (i, k) =
      W.mulVec (fun j => psi (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Applying `W ⊗ I` to a bipartite rank-one vector and tracing out the
second system sandwiches the original first-system marginal by `W`.

This is the finite-sum kernel of the weighted-purification identity in
KW `EA_capacity.tex:1989-1996`. -/
theorem partialTraceB_rankOne_kron_left_mulVec_eq
    {d : Type u1} {c : Type u2} [Fintype d] [DecidableEq d]
    [Fintype c] [DecidableEq c]
    (W : CMatrix d) (psi : Prod d c → ℂ) :
    partialTraceB (a := d) (b := c)
        (rankOneMatrix (Matrix.mulVec (Matrix.kronecker W (1 : CMatrix c)) psi)) =
      W * partialTraceB (a := d) (b := c) (rankOneMatrix psi) *
        Matrix.conjTranspose W := by
  ext x y
  have hmulVec :
      Matrix.mulVec (Matrix.kronecker W (1 : CMatrix c)) psi =
        fun p : Prod d c => W.mulVec (fun i => psi (i, p.2)) p.1 := by
    ext p
    exact kronecker_left_one_mulVec_apply W psi p.1 p.2
  rw [hmulVec]
  let F : c → d → d → ℂ := fun k i j =>
    W x i * (psi (i, k) * (star (W y j) * star (psi (j, k))))
  calc
    partialTraceB (a := d) (b := c)
        (rankOneMatrix (fun p : Prod d c => W.mulVec (fun i => psi (i, p.2)) p.1)) x y
        =
      ∑ k : c, ∑ j : d, ∑ i : d, F k i j := by
        simp [F, partialTraceB, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = ∑ j : d, ∑ k : c, ∑ i : d, F k i j := by
        rw [Finset.sum_comm]
    _ = ∑ j : d, ∑ i : d, ∑ k : c, F k i j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
    _ = ∑ j : d, star (W y j) *
          ∑ i : d, W x i * ∑ k : c, psi (i, k) * star (psi (j, k)) := by
        simp [F, Finset.mul_sum, mul_left_comm]
    _ =
      (W * partialTraceB (a := d) (b := c) (rankOneMatrix psi) *
        Matrix.conjTranspose W) x y := by
        simp [partialTraceB, rankOneMatrix_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, mul_comm]

/-- The weighted purification vector used in the proof of KW
`eq-sand_rel_mut_inf_alt`.

It is obtained from the purification `psi_ABC` by applying
`rho_A^((1-alpha)/(2 alpha)) ⊗ sigma_B^((1-alpha)/(2 alpha))` on the `AB`
legs and the identity on the purifying `C` leg. -/
def sandwichedMutualInformationWeightedPurificationAmp
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (σB : State b)
    (ψ : PureVector (Prod (Prod a b) c)) (alpha : ℝ) :
    Prod (Prod a b) c → ℂ :=
  Matrix.mulVec
    (Matrix.kronecker
      (sandwichedMutualInformationABWeight rhoA σB alpha)
      (1 : CMatrix c))
    ψ.amp

/-- Partial tracing the KW weighted purification over the purifying system
produces the sandwich of the original `AB` marginal by the source weight.

This is the matrix identity behind KW `EA_capacity.tex:1989-1996`. -/
theorem partialTraceB_rankOne_weightedPurificationAmp_eq
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (σB : State b)
    (ψ : PureVector (Prod (Prod a b) c)) (alpha : ℝ) :
    partialTraceB (a := Prod a b) (b := c)
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) =
      sandwichedMutualInformationABWeight rhoA σB alpha *
        partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
        Matrix.conjTranspose (sandwichedMutualInformationABWeight rhoA σB alpha) := by
  exact partialTraceB_rankOne_kron_left_mulVec_eq
    (sandwichedMutualInformationABWeight rhoA σB alpha) ψ.amp

private theorem sandwiched_partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne
    {d : Type u1} {c : Type u2} [Fintype d] [DecidableEq d] [Fintype c] [DecidableEq c]
    (X : CMatrix (Prod d c)) (T : CMatrix c) :
    ((partialTraceA (a := d) (b := c) X) * T).trace =
      (X * Matrix.kronecker (1 : CMatrix d) T).trace := by
  rw [← partialTraceA_mul_rightKroneckerOne X T]
  exact partialTraceA_trace (a := d) (b := c)
    (X * Matrix.kronecker (1 : CMatrix d) T)

private theorem rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
    {d : Type u1} [Fintype d] [DecidableEq d] (M : CMatrix d) (v : d → ℂ) :
    rankOneMatrix (M.mulVec v) = M * rankOneMatrix v * Matrix.conjTranspose M := by
  rw [rankOneMatrix, rankOneMatrix]
  rw [Matrix.mul_vecMulVec]
  rw [Matrix.vecMulVec_mul]
  congr
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]

/-- Trace-pairing form of the KW weighted-purification bracket.

This is the cyclic trace/partial-trace bridge in `EA_capacity.tex:2006-2025`:
after applying the `AB` square weights to the purification, pairing the
purifying marginal with `tau_C^((alpha-1)/alpha)` is exactly the Sion trace
bracket on the full-rank side-reference branch. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) *
        CFC.rpow τC.matrix ((alpha - 1) / alpha)).trace).re := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let T : CMatrix c := CFC.rpow τC.matrix ((alpha - 1) / alpha)
  let Wab : CMatrix (Prod a b) := sandwichedMutualInformationABWeight rhoA σB alpha
  let W : CMatrix (Prod (Prod a b) c) := Matrix.kronecker Wab (1 : CMatrix c)
  let K : CMatrix (Prod (Prod a b) c) := Matrix.kronecker (1 : CMatrix (Prod a b)) T
  have hρpow :
      CFC.rpow rhoA.matrix s * CFC.rpow rhoA.matrix s =
        CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
    calc
      CFC.rpow rhoA.matrix s * CFC.rpow rhoA.matrix s =
          CFC.rpow rhoA.matrix (s + s) := by
            exact (CFC.rpow_add (a := rhoA.matrix) (x := s) (y := s) hrhoA.isUnit).symm
      _ = CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hσpow :
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
        CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
    calc
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
          CFC.rpow σB.matrix (s + s) := by
            exact (CFC.rpow_add (a := σB.matrix) (x := s) (y := s) hσB.isUnit).symm
      _ = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hWstar : Matrix.conjTranspose W = W := by
    have hWab : Wab.IsHermitian := by
      unfold Wab sandwichedMutualInformationABWeight
      exact kronecker_isHermitian
        (CFC.rpow rhoA.matrix s)
        (CFC.rpow σB.matrix s)
        (cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := s) rhoA.pos).isHermitian
        (cMatrix_rpow_posSemidef (A := σB.matrix) (s := s) σB.pos).isHermitian
    unfold W
    exact (kronecker_isHermitian Wab (1 : CMatrix c) hWab (by simp)).eq
  have hWKW :
      W * K * W =
        Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T := by
    have hWK : W * K = Matrix.kronecker Wab T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (Prod a b)) (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
      unfold Wab sandwichedMutualInformationABWeight
      let R : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / (2 * alpha))
      let S : CMatrix b := CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha))
      have hR :
          R * R = CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
        simpa [R, s, mul_comm] using hρpow
      have hS :
          S * S = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
        simpa [S, s, mul_comm] using hσpow
      calc
        Matrix.kronecker R S * Matrix.kronecker R S =
            Matrix.kronecker (R * R) (S * S) := by
              exact (Matrix.mul_kronecker_mul R R S S).symm
        _ = Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
              rw [hR, hS]
    calc
      W * K * W = Matrix.kronecker Wab T * W := by rw [hWK]
      _ = Matrix.kronecker Wab T * Matrix.kronecker Wab (1 : CMatrix c) := by
            rfl
      _ = Matrix.kronecker (Wab * Wab) (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = Matrix.kronecker
            (Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
            T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) =
        W * rankOneMatrix ψ.amp * W := by
    unfold sandwichedMutualInformationWeightedPurificationAmp W Wab
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [hWstar]
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  rw [sandwiched_partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne]
  change
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
      ((rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) *
        K).trace).re
  rw [hrank]
  calc
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
        ((W * K * W * rankOneMatrix ψ.amp).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix ψ.amp * W) * K).trace).re := by
          congr 1
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle W K (W * rankOneMatrix ψ.amp)

/-- Support-convention trace-pairing form of the KW weighted-purification
bracket.

The older lemma
`sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau`
used `CFC.rpow_add` and therefore required `rho_A` to be full rank.  KW
`EA_capacity.tex:2006-2025` does not impose that hypothesis.  This sibling
keeps the source statement: only the optimized side state `sigma_B` is
full-rank, while the fixed `rho_A` is an arbitrary state.  The `rho_A` square
weight is multiplied using the repository support convention for PSD real
powers. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hσB : σB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) *
        CFC.rpow τC.matrix ((alpha - 1) / alpha)).trace).re := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let T : CMatrix c := CFC.rpow τC.matrix ((alpha - 1) / alpha)
  let Wab : CMatrix (Prod a b) := sandwichedMutualInformationABWeight rhoA σB alpha
  let W : CMatrix (Prod (Prod a b) c) := Matrix.kronecker Wab (1 : CMatrix c)
  let K : CMatrix (Prod (Prod a b) c) := Matrix.kronecker (1 : CMatrix (Prod a b)) T
  have hρpow :
      CFC.rpow rhoA.matrix s * CFC.rpow rhoA.matrix s =
        CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
    refine cMatrix_rpow_mul_rpow_of_posSemidef_scalar rhoA.pos ?_
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      have hs_ne : s ≠ 0 := by
        have hnum : 1 - alpha ≠ 0 := by linarith
        have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
        exact div_ne_zero hnum hden
      have ht_ne : (1 - alpha) / alpha ≠ 0 := by
        have hnum : 1 - alpha ≠ 0 := by linarith
        have hden : alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
        exact div_ne_zero hnum hden
      simp [Real.zero_rpow hs_ne, Real.zero_rpow ht_ne]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      rw [← Real.rpow_add hxpos]
      congr 1
      simp [s]
      ring
  have hσpow :
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
        CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
    calc
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
          CFC.rpow σB.matrix (s + s) := by
            exact (CFC.rpow_add (a := σB.matrix) (x := s) (y := s) hσB.isUnit).symm
      _ = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hWstar : Matrix.conjTranspose W = W := by
    have hWab : Wab.IsHermitian := by
      unfold Wab sandwichedMutualInformationABWeight
      exact kronecker_isHermitian
        (CFC.rpow rhoA.matrix s)
        (CFC.rpow σB.matrix s)
        (cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := s) rhoA.pos).isHermitian
        (cMatrix_rpow_posSemidef (A := σB.matrix) (s := s) σB.pos).isHermitian
    unfold W
    exact (kronecker_isHermitian Wab (1 : CMatrix c) hWab (by simp)).eq
  have hWKW :
      W * K * W =
        Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T := by
    have hWK : W * K = Matrix.kronecker Wab T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (Prod a b)) (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
      unfold Wab sandwichedMutualInformationABWeight
      let R : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / (2 * alpha))
      let S : CMatrix b := CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha))
      have hR :
          R * R = CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
        simpa [R, s, mul_comm] using hρpow
      have hS :
          S * S = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
        simpa [S, s, mul_comm] using hσpow
      calc
        Matrix.kronecker R S * Matrix.kronecker R S =
            Matrix.kronecker (R * R) (S * S) := by
              exact (Matrix.mul_kronecker_mul R R S S).symm
        _ = Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
              rw [hR, hS]
    calc
      W * K * W = Matrix.kronecker Wab T * W := by rw [hWK]
      _ = Matrix.kronecker Wab T * Matrix.kronecker Wab (1 : CMatrix c) := by
            rfl
      _ = Matrix.kronecker (Wab * Wab) (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = Matrix.kronecker
            (Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
            T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) =
        W * rankOneMatrix ψ.amp * W := by
    unfold sandwichedMutualInformationWeightedPurificationAmp W Wab
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [hWstar]
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  rw [sandwiched_partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne]
  change
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
      ((rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) *
        K).trace).re
  rw [hrank]
  calc
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
        ((W * K * W * rankOneMatrix ψ.amp).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix ψ.amp * W) * K).trace).re := by
          congr 1
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle W K (W * rankOneMatrix ψ.amp)

/-- Every full-rank side-reference Sion bracket value lies below the Holder
unit-ball supremum of the KW weighted purification marginal.

This is the inequality direction of the variational step in
`EA_capacity.tex:2006-2025`, after the trace-pairing identity has moved the
`tau_C` power onto the purifying marginal. -/
theorem sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ≤
      sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate (Real.conjExponent alpha) :=
    Real.HolderConjugate.conjExponent halpha
  have hr : r = 1 / Real.conjExponent alpha := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hτtrace : τC.matrix.trace.re = 1 := by
    simpa using congrArg Complex.re τC.trace_eq_one
  have hvar :
      ((M * CFC.rpow τC.matrix r).trace).re ≤ psdSchattenPNorm M hM alpha := by
    exact psd_trace_rpow_holder_variational_upper
      (M := M) (N := τC.matrix) hM τC.pos hτtrace hpq hr
  have htrace :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        ((M * CFC.rpow τC.matrix r).trace).re := by
    simpa [M, r] using
      sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
        rhoA ψ σB τC hrhoA hσB alpha
  rw [htrace]
  rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
    (q := Real.conjExponent alpha) hpq]
  exact hvar

/-- Support-convention version of
`sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup`.

This removes the artificial full-rank assumption on the fixed source marginal
`rho_A`; the only full-rank assumption left is on the optimized side state
`sigma_B`, exactly as in the full-rank-side branch of KW
`EA_capacity.tex:2006-2025`. -/
theorem sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ≤
      sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate (Real.conjExponent alpha) :=
    Real.HolderConjugate.conjExponent halpha
  have hr : r = 1 / Real.conjExponent alpha := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hτtrace : τC.matrix.trace.re = 1 := by
    simpa using congrArg Complex.re τC.trace_eq_one
  have hvar :
      ((M * CFC.rpow τC.matrix r).trace).re ≤ psdSchattenPNorm M hM alpha := by
    exact psd_trace_rpow_holder_variational_upper
      (M := M) (N := τC.matrix) hM τC.pos hτtrace hpq hr
  have htrace :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        ((M * CFC.rpow τC.matrix r).trace).re := by
    simpa [M, r] using
      sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
        rhoA ψ σB τC hσB halpha
  rw [htrace]
  rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
    (q := Real.conjExponent alpha) hpq]
  exact hvar

/-- The Holder unit-ball supremum in the KW variational step is controlled by
optimizing the trace bracket over normalized purifying side states.

This is the converse direction to
`sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup`
and formalizes the normalization step in KW `EA_capacity.tex:2010-2018`: a PSD
Holder witness `B` with `Tr B^q <= 1` is either zero, or its normalized
`q`-power is a state `tau_C` whose `q`-root dominates the original witness. -/
theorem weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) ≤
      sSup (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let q : ℝ := Real.conjExponent alpha
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent halpha
  have hq_pos : 0 < q := hpq.symm.pos
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hr : r = 1 / q := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r q Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact hpq.symm.one_div_nonneg
  have hqr : q * r = 1 := by
    rw [hr]
    exact mul_one_div_cancel hq_pos.ne'
  have hstateBdd :
      BddAbove (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    refine ⟨psdSchattenPNorm M hM alpha, ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle :=
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ σB τC hrhoA hσB halpha
    rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
      (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)] at hle
    simpa [M, q] using hle
  have hholderNonempty :
      (psdTraceHolderUnitBallValueSet M q).Nonempty :=
    Set.nonempty_of_mem (psdTraceHolderUnitBall_isGreatest hM hpq).1
  change sSup (psdTraceHolderUnitBallValueSet M q) ≤
    sSup (Set.range fun τC : State c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha)
  refine csSup_le hholderNonempty ?_
  intro x hx
  rcases hx with ⟨B, hB, hBq, rfl⟩
  by_cases hBzero : B = 0
  · have hvalue_zero : ((M * B).trace).re = 0 := by
      simp [hBzero]
    rw [hvalue_zero]
    let τ0 : State c := State.maximallyMixed c
    have hτ0_nonneg :
        0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha := by
      have htrace :
          sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha =
            ((M * CFC.rpow τ0.matrix r).trace).re := by
        simpa [M, r] using
          sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
            rhoA ψ σB τ0 hrhoA hσB alpha
      rw [htrace]
      exact cMatrix_trace_mul_posSemidef_re_nonneg hM
        (cMatrix_rpow_posSemidef (A := τ0.matrix) (s := r) τ0.pos)
    exact hτ0_nonneg.trans (le_csSup hstateBdd ⟨τ0, rfl⟩)
  · let S : ℝ := psdTracePower B hB q
    have hSpos : 0 < S := by
      simpa [S] using psdTracePower_pos_of_ne_zero B hB hBzero
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    let scale : ℝ := S ^ (-(1 / q))
    have hscale_nonneg : 0 ≤ scale := by
      exact Real.rpow_nonneg hSnonneg (-(1 / q))
    let N : CMatrix c := scale • B
    have hN : N.PosSemidef := by
      simpa [N, scale] using Matrix.PosSemidef.smul hB hscale_nonneg
    have hNq : psdTracePower N hN q = 1 := by
      simpa [N, S, scale, hN] using
        psdTracePower_normalized_real_smul_eq_one_of_ne_zero hB hBzero hq_pos
    let T : CMatrix c := CFC.rpow N q
    have hT : T.PosSemidef := by
      simpa [T] using cMatrix_rpow_posSemidef (A := N) (s := q) hN
    have hTtrace_re : T.trace.re = 1 := by
      change psdTracePower N hN q = 1
      exact hNq
    have hTtrace : T.trace = 1 := by
      apply Complex.ext
      · exact hTtrace_re
      · simpa using (Matrix.PosSemidef.trace_nonneg hT).2.symm
    let τC : State c := { matrix := T, pos := hT, trace_eq_one := hTtrace }
    have hτpow : CFC.rpow τC.matrix r = N := by
      dsimp [τC, T]
      change (N ^ q) ^ r = N
      rw [CFC.rpow_rpow_of_exponent_nonneg N q r hq_nonneg hr_nonneg
        (Matrix.nonneg_iff_posSemidef.mpr hN)]
      rw [hqr]
      simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
    have hbracket :
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
          ((M * N).trace).re := by
      have htrace :=
        sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
          rhoA ψ σB τC hrhoA hσB alpha
      rw [hτpow] at htrace
      simpa [M, r] using htrace
    have htrace_smul : ((M * N).trace).re = scale * ((M * B).trace).re := by
      simp [N, Matrix.trace_smul, Complex.mul_re, scale]
    have hscale_ge_one : 1 ≤ scale := by
      have hnonpos : -(1 / q) ≤ 0 := by
        have hone_div_pos : 0 < 1 / q := one_div_pos.mpr hq_pos
        linarith
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hSpos hBq hnonpos
    have hvalue_nonneg : 0 ≤ ((M * B).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg hM hB
    have hvalue_le : ((M * B).trace).re ≤ ((M * N).trace).re := by
      rw [htrace_smul]
      exact le_mul_of_one_le_left hvalue_nonneg hscale_ge_one
    exact hvalue_le.trans (by
      rw [← hbracket]
      exact le_csSup hstateBdd ⟨τC, rfl⟩)

/-- Support-convention converse direction to
`sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef`.

This is the normalized-witness step in KW `EA_capacity.tex:2010-2018` without a
full-rank assumption on the fixed `rho_A`.  A PSD Holder witness is normalized
through its `q`-power to a state `tau_C`, and the support-convention trace
bridge identifies the resulting value with the Sion bracket. -/
theorem weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) ≤
      sSup (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let q : ℝ := Real.conjExponent alpha
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent halpha
  have hq_pos : 0 < q := hpq.symm.pos
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hr : r = 1 / q := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r q Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact hpq.symm.one_div_nonneg
  have hqr : q * r = 1 := by
    rw [hr]
    exact mul_one_div_cancel hq_pos.ne'
  have hstateBdd :
      BddAbove (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    refine ⟨psdSchattenPNorm M hM alpha, ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle :=
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ σB τC hσB halpha
    rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
      (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)] at hle
    simpa [M, q] using hle
  have hholderNonempty :
      (psdTraceHolderUnitBallValueSet M q).Nonempty :=
    Set.nonempty_of_mem (psdTraceHolderUnitBall_isGreatest hM hpq).1
  change sSup (psdTraceHolderUnitBallValueSet M q) ≤
    sSup (Set.range fun τC : State c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha)
  refine csSup_le hholderNonempty ?_
  intro x hx
  rcases hx with ⟨B, hB, hBq, rfl⟩
  by_cases hBzero : B = 0
  · have hvalue_zero : ((M * B).trace).re = 0 := by
      simp [hBzero]
    rw [hvalue_zero]
    let τ0 : State c := State.maximallyMixed c
    have hτ0_nonneg :
        0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha := by
      have htrace :
          sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha =
            ((M * CFC.rpow τ0.matrix r).trace).re := by
        simpa [M, r] using
          sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
            rhoA ψ σB τ0 hσB halpha
      rw [htrace]
      exact cMatrix_trace_mul_posSemidef_re_nonneg hM
        (cMatrix_rpow_posSemidef (A := τ0.matrix) (s := r) τ0.pos)
    exact hτ0_nonneg.trans (le_csSup hstateBdd ⟨τ0, rfl⟩)
  · let S : ℝ := psdTracePower B hB q
    have hSpos : 0 < S := by
      simpa [S] using psdTracePower_pos_of_ne_zero B hB hBzero
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    let scale : ℝ := S ^ (-(1 / q))
    have hscale_nonneg : 0 ≤ scale := by
      exact Real.rpow_nonneg hSnonneg (-(1 / q))
    let N : CMatrix c := scale • B
    have hN : N.PosSemidef := by
      simpa [N, scale] using Matrix.PosSemidef.smul hB hscale_nonneg
    have hNq : psdTracePower N hN q = 1 := by
      simpa [N, S, scale, hN] using
        psdTracePower_normalized_real_smul_eq_one_of_ne_zero hB hBzero hq_pos
    let T : CMatrix c := CFC.rpow N q
    have hT : T.PosSemidef := by
      simpa [T] using cMatrix_rpow_posSemidef (A := N) (s := q) hN
    have hTtrace_re : T.trace.re = 1 := by
      change psdTracePower N hN q = 1
      exact hNq
    have hTtrace : T.trace = 1 := by
      apply Complex.ext
      · exact hTtrace_re
      · simpa using (Matrix.PosSemidef.trace_nonneg hT).2.symm
    let τC : State c := { matrix := T, pos := hT, trace_eq_one := hTtrace }
    have hτpow : CFC.rpow τC.matrix r = N := by
      dsimp [τC, T]
      change (N ^ q) ^ r = N
      rw [CFC.rpow_rpow_of_exponent_nonneg N q r hq_nonneg hr_nonneg
        (Matrix.nonneg_iff_posSemidef.mpr hN)]
      rw [hqr]
      simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
    have hbracket :
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
          ((M * N).trace).re := by
      have htrace :=
        sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
          rhoA ψ σB τC hσB halpha
      rw [hτpow] at htrace
      simpa [M, r] using htrace
    have htrace_smul : ((M * N).trace).re = scale * ((M * B).trace).re := by
      simp [N, Matrix.trace_smul, Complex.mul_re, scale]
    have hscale_ge_one : 1 ≤ scale := by
      have hnonpos : -(1 / q) ≤ 0 := by
        have hone_div_pos : 0 < 1 / q := one_div_pos.mpr hq_pos
        linarith
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hSpos hBq hnonpos
    have hvalue_nonneg : 0 ≤ ((M * B).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg hM hB
    have hvalue_le : ((M * B).trace).re ≤ ((M * N).trace).re := by
      rw [htrace_smul]
      exact le_mul_of_one_le_left hvalue_nonneg hscale_ge_one
    exact hvalue_le.trans (by
      rw [← hbracket]
      exact le_csSup hstateBdd ⟨τC, rfl⟩)

/-- The `AB` marginal of the KW weighted purification is exactly the
sandwiched-Renyi inner operator for the source reference
`rho_A ⊗ sigma_B`.

This is the Lean matrix form of KW `EA_capacity.tex:1989-1996` in the
full-rank high-`alpha` branch. -/
theorem partialTraceB_rankOne_weightedPurificationAmp_eq_referenceInner
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hσ : σB.matrix.PosDef) (alpha : ℝ) :
    partialTraceB (a := Prod a b) (b := c)
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.marginalA σB ψ alpha)) =
      State.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.marginalA.prod σB).matrix alpha := by
  let W : CMatrix (Prod a b) :=
    sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha
  have hW :
      Matrix.conjTranspose W = W := by
    unfold W sandwichedMutualInformationABWeight
    exact (kronecker_isHermitian
      (CFC.rpow ψ.state.marginalAB.marginalA.matrix ((1 - alpha) / (2 * alpha)))
      (CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha)))
      (cMatrix_rpow_posSemidef
        (A := ψ.state.marginalAB.marginalA.matrix)
        (s := (1 - alpha) / (2 * alpha))
        ψ.state.marginalAB.marginalA.pos).isHermitian
      (cMatrix_rpow_posSemidef
        (A := σB.matrix)
        (s := (1 - alpha) / (2 * alpha))
        σB.pos).isHermitian).eq
  rw [partialTraceB_rankOne_weightedPurificationAmp_eq]
  unfold State.sandwichedRenyiReferenceInner
  rw [show (ψ.state.marginalAB.marginalA.prod σB).matrix =
      Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix from rfl]
  change sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha *
      partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
        Matrix.conjTranspose
          (sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha) =
    CFC.rpow (Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix)
        ((1 - alpha) / (2 * alpha)) *
      ψ.state.marginalAB.matrix *
      CFC.rpow (Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix)
        ((1 - alpha) / (2 * alpha))
  rw [cMatrix_rpow_kronecker_posDef hA hσ ((1 - alpha) / (2 * alpha))]
  change W * partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
      Matrix.conjTranspose W =
    W * ψ.state.marginalAB.matrix * W
  rw [hW]
  rfl

/-- The two partial traces of the KW weighted purification rank-one operator
have equal Schatten `p` norms.

This is the Lean form of the same-nonzero-eigenvalues step in
KW `EA_capacity.tex:1990-2004`, before the reverse-Holder variational formula
is applied. -/
theorem psdSchattenPNorm_weightedPurification_partialTraceC_eq_partialTraceAB
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (σB : State b)
    (ψ : PureVector (Prod (Prod a b) c)) (alpha : ℝ)
    {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (partialTraceB_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        p =
      psdSchattenPNorm
        (partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (partialTraceA_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        p := by
  exact psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
    (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) hp

/-- Schatten-norm form of the KW weighted-purification bridge.

The reference-inner Schatten expression on the `AB` system equals the Schatten
expression of the complementary `C` marginal of the weighted purification,
matching KW `EA_capacity.tex:1990-2004`. -/
theorem psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hσ : σB.matrix.PosDef) (alpha : ℝ) {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.marginalA.prod σB).matrix alpha)
        (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
          (State.prod_posDef hA hσ).posSemidef alpha)
        p =
      psdSchattenPNorm
        (partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.marginalA σB ψ alpha)))
        (partialTraceA_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.marginalA σB ψ alpha)))
        p := by
  let amp :=
    sandwichedMutualInformationWeightedPurificationAmp
      ψ.state.marginalAB.marginalA σB ψ alpha
  let hB : (partialTraceB (a := Prod a b) (b := c)
      (rankOneMatrix amp)).PosSemidef :=
    partialTraceB_posSemidef (rankOneMatrix_pos amp)
  let hRef :
      (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.marginalA.prod σB).matrix alpha).PosSemidef :=
    State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
      (State.prod_posDef hA hσ).posSemidef alpha
  have hmatrix :
      partialTraceB (a := Prod a b) (b := c) (rankOneMatrix amp) =
        State.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.marginalA.prod σB).matrix alpha := by
    simpa [amp] using
      partialTraceB_rankOne_weightedPurificationAmp_eq_referenceInner
        σB ψ hA hσ alpha
  have hnormB :
      psdSchattenPNorm (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix amp)) hB p =
        psdSchattenPNorm
          (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod σB).matrix alpha)
          hRef p :=
    psdSchattenPNorm_congr hmatrix hB hRef p
  have hBA :
      psdSchattenPNorm (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix amp)) hB p =
        psdSchattenPNorm
          (partialTraceA (a := Prod a b) (b := c) (rankOneMatrix amp))
          (partialTraceA_posSemidef (rankOneMatrix_pos amp)) p := by
    simpa [amp, hB] using
      psdSchattenPNorm_weightedPurification_partialTraceC_eq_partialTraceAB
        ψ.state.marginalAB.marginalA σB ψ alpha hp
  exact hnormB.symm.trans hBA

/-- Pure-state specialization of the KW high-`alpha` Sion exchange. -/
theorem sandwichedAlpha_sion_abcSidePowerTraceRe_state_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
        ⨆ τ ∈ State.densityMatrixSet c,
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ τ
              ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ ∈ State.densityMatrixSet c,
        ⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ τ
              ((alpha - 1) / alpha) : EReal) := by
  exact sandwichedAlpha_sion_abcSidePowerTraceRe_EReal
    (a := a) (b := b) (c := c)
    hdelta_pos hdelta_le ψ.state.pos halpha

/-- State-domain form of the KW high-`alpha` Sion exchange.

The sigma side remains restricted to the compact full-support lower-bound
domain used by the already proved Sion theorem; the tau side is the ordinary
state domain. -/
theorem sandwichedAlpha_sion_uniformlyPositiveState_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ.val.matrix τ.matrix
              ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ.val.matrix τ.matrix
              ((alpha - 1) / alpha) : EReal) := by
  let F : CMatrix b → CMatrix c → EReal := fun σ τ =>
    (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ τ ((alpha - 1) / alpha) :
      EReal)
  calc
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c, F σ.val.matrix τ.matrix)
        =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : State c, F σ τ.matrix := by
        exact uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
          (fun σ => ⨆ τ : State c, F σ τ.matrix)
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : CMatrix c, ⨆ hτ : τ ∈ State.densityMatrixSet c, F σ τ := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : CMatrix b,
            ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b, F σ τ := by
        exact sandwichedAlpha_sion_abcSidePowerTraceRe_state_EReal
          (a := a) (b := b) (c := c) ψ hdelta_pos hdelta_le halpha
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ := by
        simp_rw [
          ← uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf]
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          F σ.val.matrix τ.matrix := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun τ => ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ)).symm

/-- Source-bracket form of the compact-domain Sion exchange in KW
`EA_capacity.tex:2020-2025`. -/
theorem sandwichedAlpha_sion_commonBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          ((ψ.upwardRenyiDualityCommonBracket σ.val τ ((alpha - 1) / alpha)).re :
            EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          ((ψ.upwardRenyiDualityCommonBracket σ.val τ ((alpha - 1) / alpha)).re :
            EReal) := by
  simpa [upwardRenyiDualityCommonBracket_re_eq_abcSidePowerTraceRe] using
    sandwichedAlpha_sion_uniformlyPositiveState_EReal
      (a := a) (b := b) (c := c) ψ hdelta_pos hdelta_le halpha

/-- Fixed-marginal source-bracket form of the compact-domain Sion exchange in
KW `EA_capacity.tex:2020-2025`. -/
theorem sandwichedAlpha_sion_mutualInformationBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  let A : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / alpha)
  let F : CMatrix b -> CMatrix c -> EReal := fun σ τ =>
    (State.abcWeightedSidePowerTraceRe (a := a) A ψ.state.matrix σ τ
      ((alpha - 1) / alpha) : EReal)
  have hA : A.PosSemidef :=
    cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos
  calc
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        =
      ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c, F σ.val.matrix τ.matrix := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : State c, F σ τ.matrix := by
        exact uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
          (fun σ => ⨆ τ : State c, F σ τ.matrix)
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : CMatrix c, ⨆ hτ : τ ∈ State.densityMatrixSet c, F σ τ := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : CMatrix b,
            ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b, F σ τ := by
        exact sandwichedAlpha_sion_abcWeightedSidePowerTraceRe_EReal
          (a := a) (b := b) (c := c) hdelta_pos hdelta_le hA ψ.state.pos halpha
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ := by
        simp_rw [
          ← uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf]
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          F σ.val.matrix τ.matrix := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun τ => ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ)).symm
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]

/-- Full-rank state-domain Sion exchange for the KW sandwiched mutual
information bracket.

This is the state-language form of
`State.fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal` and
matches the no-cutoff route in KW `EA_capacity.tex:2018-2035`. -/
theorem sandwichedAlpha_fullRank_sion_mutualInformationBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // σ.matrix.PosDef},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  let A : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / alpha)
  let F : CMatrix b → CMatrix c → EReal := fun sigma tau =>
    (State.abcWeightedSidePowerTraceRe (a := a) A ψ.state.matrix sigma tau
      ((alpha - 1) / alpha) : EReal)
  have hA : A.PosSemidef :=
    cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  calc
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma,
          ⨆ τ : State c, F sigma τ.matrix := by
        exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
          (fun sigma => ⨆ τ : State c, F sigma τ.matrix)
    _ =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma,
          ⨆ tau : CMatrix c,
            ⨆ _hTau : (State.densityMatrixSet c) tau, F sigma tau := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
        rfl
    _ =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : (State.densityMatrixSet c) tau,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma, F sigma tau := by
        exact State.fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
          (a := a) (b := b) (c := c) hA ψ.state.pos hp.1 (le_of_lt hp.2)
    _ =
      ⨆ τ : State c,
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma, F sigma τ.matrix := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun tau => ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma, F sigma tau)).symm
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // σ.matrix.PosDef}, F σ.val.matrix τ.matrix := by
        apply iSup_congr
        intro τ
        exact (fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
          (fun sigma => F sigma τ.matrix)).symm
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // σ.matrix.PosDef},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]

/-- Full-rank branch followed by the compact-domain Sion exchange.

KW first works on compact domains `delta • I ≤ sigma_B` and then removes the
regularization.  This lemma records the order direction that embeds the
uniformly-positive domain into the full-rank side-reference branch before
using `sandwichedAlpha_sion_mutualInformationBracket_EReal`. -/
theorem sandwichedAlpha_fullRank_iInf_iSup_le_uniformlyPositive_iSup_iInf
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) ≤
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  calc
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        ≤
      (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) := by
        exact fullRankState_iInf_le_uniformlyPositiveState_iInf_EReal hdelta_pos
          (fun σ : State b =>
            ⨆ τ : State c,
              (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha : EReal))
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) :=
        sandwichedAlpha_sion_mutualInformationBracket_EReal
          rhoA ψ hdelta_pos hdelta_le halpha

end PureVector

/-- Every full-rank state belongs to some uniformly-positive compact Sion
domain with the source normalization bound `delta <= 1 / |B|`.

This is the local regularization bookkeeping used when the KW proof removes
the compact full-support cutoff after applying Sion: positive definiteness gives
a scalar lower spectral bound, and we shrink it if needed to meet the
`uniformlyPositiveDensityMatrixSet_nonempty` side condition. -/
theorem exists_uniformlyPositiveDensityMatrixSet_mem_of_posDef
    {b : Type v1} [Fintype b] [DecidableEq b]
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹ ∧
      σ.matrix ∈ State.uniformlyPositiveDensityMatrixSet delta b := by
  classical
  haveI : Nonempty b := σ.nonempty
  rcases σ.exists_pos_scalar_smul_one_le_matrix_of_posDef hσ with ⟨c, hc_pos, hc_le⟩
  have hcard_pos : 0 < (Fintype.card b : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty b›
  let delta : ℝ := min (c / 2) ((Fintype.card b : ℝ)⁻¹)
  have hdelta_pos : 0 < delta := by
    exact lt_min (half_pos hc_pos) (inv_pos.mpr hcard_pos)
  have hdelta_le_card : delta ≤ (Fintype.card b : ℝ)⁻¹ := by
    exact min_le_right _ _
  have hdelta_le_c : delta ≤ c := by
    exact (min_le_left _ _).trans (by linarith)
  have hdelta_one_le_c_one :
      delta • (1 : CMatrix b) ≤ c • (1 : CMatrix b) := by
    rw [Matrix.le_iff]
    rw [← sub_smul]
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (sub_nonneg.mpr hdelta_le_c)
  refine ⟨delta, hdelta_pos, hdelta_le_card, ?_⟩
  exact ⟨State.state_matrix_mem_densityMatrixSet σ, hdelta_one_le_c_one.trans hc_le⟩

/-- Pointwise removal of the compact uniformly-positive cutoff.

For a fixed objective over side states, optimizing over all full-rank states is
the same as first imposing a source-valid cutoff `delta • I <= sigma` and then
letting `delta` range over all positive values allowed by the Sion compactness
side condition.  This is the order-theoretic core of the KW `delta downarrow 0`
step before any supremum over the purifying side is considered. -/
theorem fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
    {b : Type v1} [Fintype b] [DecidableEq b] (f : State b → EReal) :
    (⨅ σ : {σ : State b // σ.matrix.PosDef}, f σ.val) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : State b // delta.val • (1 : CMatrix b) ≤ σ.matrix}, f σ.val := by
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro delta
    exact fullRankState_iInf_le_uniformlyPositiveState_iInf_EReal delta.property.1 f
  · refine le_iInf ?_
    intro σ
    rcases exists_uniformlyPositiveDensityMatrixSet_mem_of_posDef σ.val σ.property with
      ⟨delta, hdelta_pos, hdelta_le, hσmem⟩
    have hleft :
        (⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
          ⨅ τ : {τ : State b // delta.val • (1 : CMatrix b) ≤ τ.matrix}, f τ.val) ≤
          ⨅ τ : {τ : State b // delta • (1 : CMatrix b) ≤ τ.matrix}, f τ.val :=
      iInf_le
        (fun delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹} =>
          ⨅ τ : {τ : State b // delta.val • (1 : CMatrix b) ≤ τ.matrix}, f τ.val)
        ⟨delta, hdelta_pos, hdelta_le⟩
    have hright :
        (⨅ τ : {τ : State b // delta • (1 : CMatrix b) ≤ τ.matrix}, f τ.val) ≤
          f σ.val :=
      iInf_le
        (fun τ : {τ : State b // delta • (1 : CMatrix b) ≤ τ.matrix} => f τ.val)
        ⟨σ.val, hσmem.2⟩
    exact hleft.trans hright

namespace PureVector

/-- Fixed-`tau_C` specialization of the pointwise `delta downarrow 0` removal
for the KW Sion bracket.

This is the exact statement obtained by applying
`fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal` to the source
bracket.  It is intentionally pointwise in `tau_C`; the remaining reverse
alternate-expression step must still justify moving this cutoff removal through
the `tau_C` supremum. -/
theorem sandwichedMutualInformationSionBracketRe_fullRank_iInf_eq_iInf_uniformlyPositive
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τ : State c) {alpha : ℝ} :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : State b // delta.val • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  simpa using
    fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
      (b := b)
      (fun σ : State b =>
        (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha : EReal))

/-- Logarithmic fixed-`tau_C` form of the pointwise `delta downarrow 0`
removal for the KW Sion bracket. -/
theorem sandwichedMutualInformationSionBracketLog_fullRank_iInf_eq_iInf_uniformlyPositive
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τ : State c) {alpha : ℝ} :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ((alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha) : ℝ) :
          EReal)) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : State b // delta.val • (1 : CMatrix b) ≤ σ.matrix},
          ((alpha / (alpha - 1) *
            log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha) : ℝ) :
            EReal) := by
  simpa using
    fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
      (b := b)
      (fun σ : State b =>
        ((alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha) : ℝ) :
          EReal))

end PureVector

/-- The positive prefactor `alpha / (alpha - 1)` appearing in every
sandwiched-Renyi alternate expression for `alpha > 1`. -/
theorem sandwichedCoeff_pos {alpha : ℝ} (halpha : 1 < alpha) :
    0 < alpha / (alpha - 1) := by
  exact div_pos (lt_trans zero_lt_one halpha) (sub_pos.mpr halpha)

/-- Monotonicity of base-two logarithms on the positive half-line. -/
theorem log2_mono_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos one_lt_two))

/-- The output-side weighting exponent used in
`S_sigma^(alpha)` is negative on the high-alpha branch. -/
theorem sandwichedSideWeightExponent_neg {alpha : ℝ} (halpha : 1 < alpha) :
    (1 - alpha) / (2 * alpha) < 0 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_pos : 0 < 2 * alpha := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hden_pos

/-- Doubling the two-sided sandwich exponent gives the one-sided exponent in
the trace-bracket expression of KW `eq-sand_rel_mut_inf_alt`. -/
theorem sandwichedSideWeightExponent_two_mul
    {alpha : ℝ} (halpha : 1 < alpha) :
    2 * ((1 - alpha) / (2 * alpha)) = (1 - alpha) / alpha := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  field_simp [ne_of_gt halpha_pos]

/-- In the channel alternate expression, multiplying the polar-decomposition
factor `tau_R^(1/2)` by the source sandwich `tau_R^((1-alpha)/(2alpha))`
leaves the CB-norm input exponent `1/(2alpha)`. -/
theorem sandwichedPolarInputExponent_add
    {alpha : ℝ} (halpha : 1 < alpha) :
    (1 - alpha) / (2 * alpha) + 1 / 2 = 1 / (2 * alpha) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  field_simp [ne_of_gt halpha_pos]
  all_goals ring

/-- The Sion parameter in the source proof is the negative of the high-alpha
side-information exponent. -/
theorem sandwichedAlphaPrime_eq_neg_sideExponent
    {alpha : ℝ} (_halpha : 1 < alpha) :
    (alpha - 1) / alpha = -((1 - alpha) / alpha) := by
  have hnum : alpha - 1 = -(1 - alpha) := by ring
  rw [hnum, neg_div]

/-- The high-alpha side-information exponent belongs to the operator-convexity
interval `[-1,0]`; this is the scalar side condition for
`sigma_B ↦ sigma_B^((1-alpha)/alpha)` in KW `EA_capacity.tex:2032-2039`. -/
theorem sandwichedSideExponent_mem_Icc_neg_one_zero
    {alpha : ℝ} (halpha : 1 < alpha) :
    (1 - alpha) / alpha ∈ Set.Icc (-1 : ℝ) 0 := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  have hside : (1 - alpha) / alpha = -((alpha - 1) / alpha) := by
    ring_nf
  rw [hside]
  exact ⟨by linarith [hp.2], by linarith [hp.1]⟩

/-- The Schatten exponent in the state alternate expression,
`alpha / (2 * alpha - 1)`, lies in `(0, 1)` for `alpha > 1`. -/
theorem sandwichedAlternateSchattenExponent_pos_lt_one
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < alpha / (2 * alpha - 1) ∧ alpha / (2 * alpha - 1) < 1 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_pos : 0 < 2 * alpha - 1 := by linarith
  exact ⟨div_pos halpha_pos hden_pos, by
    rw [div_lt_one hden_pos]
    linarith⟩

/-- Reverse-Holder exponent conversion used at the last line of
`eq-sand_rel_mut_inf_alt`: for
`p = alpha / (2 * alpha - 1)`, the exponent `1 - 1 / p` is
`(1 - alpha) / alpha`. -/
theorem sandwichedAlternate_reverseHolderExponent
    {alpha : ℝ} (halpha : 1 < alpha) :
    1 - 1 / (alpha / (2 * alpha - 1)) = (1 - alpha) / alpha := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_ne : 2 * alpha - 1 ≠ 0 := by linarith
  field_simp [ne_of_gt halpha_pos, hden_ne]
  all_goals ring_nf

namespace PureVector

/-- Each supported side-information state gives a reverse-Holder objective
value for the KW `AC` trace matrix. -/
theorem sandwichedMutualInformationSionBracketRe_mem_reverseHolderStateValueSet
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ∈
      psdTraceReverseHolderStateValueSet
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1)) := by
  refine ⟨σB.matrix, σB.pos, ?_, hSupport, ?_⟩
  · simpa using congrArg Complex.re σB.trace_eq_one
  · rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    rw [sandwichedAlternate_reverseHolderExponent halpha]

/-- Reverse-Holder lower-bound direction for a fixed supported `σ_B` in the
KW Sion bracket. -/
theorem psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix) :
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1)) ≤
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  have hp := sandwichedAlternateSchattenExponent_pos_lt_one halpha
  have hx :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ∈
        psdTraceReverseHolderStateValueSet M (alpha / (2 * alpha - 1)) := by
    simpa [M] using
      sandwichedMutualInformationSionBracketRe_mem_reverseHolderStateValueSet
        rhoA ψ σB τC halpha hSupport
  exact
    (psdTraceReverseHolderStateValueSet_lowerBound
      (M := M) hM hp.1 hp.2) hx

/-- Logarithmic form of the reverse-Holder lower-bound direction used after
the Sion exchange in KW `EA_capacity.tex:2030-2035`.

The previous theorem gives the norm inequality.  This lemma performs only the
source scalar step: `log2` monotonicity and multiplication by the positive
coefficient `alpha / (alpha - 1)`. -/
theorem sandwichedACTraceMatrixLog_le_SionBracketLog_of_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
            (alpha / (2 * alpha - 1))) ≤
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef := sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  have hnorm_le :
      psdSchattenPNorm M hM (alpha / (2 * alpha - 1)) ≤
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha := by
    simpa [M, hM] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA ψ σB τC halpha hSupport
  have hnorm_pos :
      0 < psdSchattenPNorm M hM (alpha / (2 * alpha - 1)) := by
    simpa [M, hM] using
      psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA ψ τC hrhoA hτC halpha
  have hlog :
      log2 (psdSchattenPNorm M hM (alpha / (2 * alpha - 1))) ≤
        log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hnorm_pos hnorm_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact mul_le_mul_of_nonneg_left hlog (le_of_lt (sandwichedCoeff_pos halpha))

/-- Full-rank side-information specialization of
`sandwichedACTraceMatrixLog_le_SionBracketLog_of_support`.

This is the form needed on the full-rank `sigma_B` branch of the KW
alternate-expression proof. -/
theorem sandwichedACTraceMatrixLog_le_SionBracketLog_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef)
    (hτC : τC.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
            (alpha / (2 * alpha - 1))) ≤
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) :=
  sandwichedACTraceMatrixLog_le_SionBracketLog_of_support
    rhoA ψ σB τC hrhoA hτC halpha
    (Matrix.Supports.of_right_posDef _ _ hσB)

/-- Reverse-Holder lower bound after optimizing over full-rank `sigma_B`.

This is the `inf_{sigma_B}` form of
`sandwichedACTraceMatrixLog_le_SionBracketLog_posDef`, matching the order in
KW immediately after the Sion exchange. -/
theorem sandwichedACTraceMatrixLog_le_fullRankSionBracketLog_iInf
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty b] [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
            (alpha / (2 * alpha - 1))) ≤
      sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) := by
  haveI : Nonempty {σ : State b // σ.matrix.PosDef} :=
    ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro y ⟨σB, rfl⟩
  exact sandwichedACTraceMatrixLog_le_SionBracketLog_posDef
    rhoA ψ σB.1 τC hrhoA σB.2 hτC halpha

/-- Reverse-Holder optimizer as a genuine side-information state for a nonzero
KW `AC` trace matrix. -/
theorem exists_state_SionBracketRe_eq_psdSchattenPNorm_of_ACTraceMatrix_ne_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0) :
    ∃ σB : State b,
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix ∧
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (alpha / (2 * alpha - 1)) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  have hp := sandwichedAlternateSchattenExponent_pos_lt_one halpha
  have hMne' : M ≠ 0 := by simpa [M] using hMne
  have hpower_pos : 0 < psdTracePower M hM (alpha / (2 * alpha - 1)) :=
    psdTracePower_pos_of_ne_zero M hM hMne'
  rcases exists_psdTraceReverseHolder_sideState_attaining
      (M := M) hM hp.1 hpower_pos with
    ⟨N, hN, hNtr, hSupport, hattain⟩
  have hNtrace : N.trace = 1 := by
    apply Complex.ext
    · simpa using hNtr
    · simpa using (Matrix.PosSemidef.trace_nonneg hN).2.symm
  have hattain' :
      psdSchattenPNorm M hM (alpha / (2 * alpha - 1)) =
        (M * CFC.rpow N ((1 - alpha) / alpha)).trace.re := by
    rw [sandwichedAlternate_reverseHolderExponent halpha] at hattain
    exact hattain
  let σB : State b := { matrix := N, pos := hN, trace_eq_one := hNtrace }
  refine ⟨σB, ?_, ?_⟩
  · simpa [σB, M] using hSupport
  · rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    simpa [σB, M, hM] using hattain'.symm

/-- Exact reverse-Holder `sInf` formula for the KW Sion bracket on the
support-restricted side-state domain.

This is the formal counterpart of the last transition in
`EA_capacity.tex:2030-2035` after the `AC` trace matrix has been identified as
positive semidefinite. -/
theorem sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0) :
    sInf (Set.range fun σB :
        {σ : State b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            σ.matrix} =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (alpha / (2 * alpha - 1)) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  let target : ℝ := psdSchattenPNorm M hM (alpha / (2 * alpha - 1))
  let S : Set ℝ := Set.range fun σB :
      {σ : State b // Matrix.Supports M σ.matrix} =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  rcases exists_state_SionBracketRe_eq_psdSchattenPNorm_of_ACTraceMatrix_ne_zero
      rhoA ψ τC halpha hMne with
    ⟨σ0, hσ0Support, hσ0⟩
  have hmem : target ∈ S := by
    refine ⟨⟨σ0, ?_⟩, ?_⟩
    · simpa [M] using hσ0Support
    · simpa [S, target, M, hM] using hσ0
  have hLower : target ∈ lowerBounds S := by
    intro y hy
    rcases hy with ⟨σB, rfl⟩
    exact psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
      rhoA ψ σB.1 τC halpha (by simpa [M] using σB.2)
  have hBdd : BddBelow S := ⟨target, hLower⟩
  apply le_antisymm
  · exact csInf_le hBdd hmem
  · exact le_csInf (Set.nonempty_of_mem hmem) hLower

/-- Zero-`AC` branch of the exact reverse-Holder `sInf` formula for the KW
Sion bracket. -/
theorem sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha)
    (hMzero : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha = 0) :
    sInf (Set.range fun sigmaB :
        {sigma : State b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            sigma.matrix} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (alpha / (2 * alpha - 1)) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha
  let hM : M.PosSemidef := sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha
  let target : Real := psdSchattenPNorm M hM (alpha / (2 * alpha - 1))
  let S : Set Real := Set.range fun sigmaB :
      {sigma : State b // Matrix.Supports M sigma.matrix} =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  have hMzero' : M = 0 := by
    simpa [M] using hMzero
  have htarget : target = 0 := by
    have hp := sandwichedAlternateSchattenExponent_pos_lt_one halpha
    have hcongr :
        psdSchattenPNorm M hM (alpha / (2 * alpha - 1)) =
          psdSchattenPNorm (0 : CMatrix b) Matrix.PosSemidef.zero
            (alpha / (2 * alpha - 1)) :=
      psdSchattenPNorm_congr hMzero' hM Matrix.PosSemidef.zero
        (alpha / (2 * alpha - 1))
    change psdSchattenPNorm M hM (alpha / (2 * alpha - 1)) = 0
    rw [hcongr]
    exact psdSchattenPNorm_zero (alpha / (2 * alpha - 1)) (ne_of_gt hp.1)
  have hvalue :
      forall sigmaB : {sigma : State b // Matrix.Supports M sigma.matrix},
        sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha = 0 := by
    intro sigmaB
    rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    simp [M, hMzero']
  let sigma0 : {sigma : State b // Matrix.Supports M sigma.matrix} :=
    ⟨State.maximallyMixed b, by
      intro v hv
      simp [M, hMzero']⟩
  have hmem : (0 : Real) ∈ S := by
    refine ⟨sigma0, ?_⟩
    exact hvalue sigma0
  have hLower : (0 : Real) ∈ lowerBounds S := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    change (0 : Real) <=
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
    rw [hvalue sigmaB]
  have hS : sInf S = 0 := by
    apply le_antisymm
    · exact csInf_le ⟨0, hLower⟩ hmem
    · exact le_csInf (Set.nonempty_of_mem hmem) hLower
  change sInf S = target
  rw [hS, htarget]

/-- Exact reverse-Holder `sInf` formula for the KW Sion bracket on the
support-restricted side-state domain, including both the nonzero and zero
`AC` trace-matrix branches. -/
theorem sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm_all
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB :
        {sigma : State b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            sigma.matrix} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (alpha / (2 * alpha - 1)) := by
  by_cases hMne : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha ≠ 0
  · exact sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm
      rhoA psi tauC halpha hMne
  · exact sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm_zero
      rhoA psi tauC halpha (not_ne_iff.mp hMne)

/-- Exact reverse-Holder `sInf` formula after closing the full-rank side-state
regularization.

This upgrades `sandwichedMutualInformationSionBracketRe_supported_sInf_eq_...`
from the support-restricted reverse-Holder domain to the full-rank state domain
appearing just before and after the Sion exchange in KW
`EA_capacity.tex:2020-2035`.  The nonzero branch uses the support-aware
identity regularization lemma from `QIT.States.Schatten`; the zero branch is
immediate from the trace form of the bracket. -/
theorem sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (alpha / (2 * alpha - 1)) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha
  let p : Real := alpha / (2 * alpha - 1)
  let r : Real := (1 - alpha) / alpha
  let target : Real := psdSchattenPNorm M hM p
  let S := {sigma : State b // sigma.matrix.PosDef}
  let f : S -> Real := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hLower : target ∈ lowerBounds (Set.range f) := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    simpa [target, p, f, M, hM] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA psi sigmaB.1 tauC halpha
        (Matrix.Supports.of_right_posDef M sigmaB.1.matrix sigmaB.2)
  have hBdd : BddBelow (Set.range f) := ⟨target, hLower⟩
  change sInf (Set.range f) = target
  by_cases hMzero : M = 0
  · have hvalue (sigmaB : S) : f sigmaB = 0 := by
      change sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha = 0
      rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
      simp [M, hMzero]
    have htarget : target = 0 := by
      have hp : 0 < p := by
        simpa [p] using (sandwichedAlternateSchattenExponent_pos_lt_one halpha).1
      calc
        target = psdSchattenPNorm (0 : CMatrix b) Matrix.PosSemidef.zero p := by
          exact psdSchattenPNorm_congr hMzero hM Matrix.PosSemidef.zero p
        _ = 0 := psdSchattenPNorm_zero p (ne_of_gt hp)
    apply le_antisymm
    · rw [htarget]
      exact csInf_le hBdd ⟨Classical.choice inferInstance, hvalue (Classical.choice inferInstance)⟩
    · exact le_csInf (Set.range_nonempty f) hLower
  · have hMne : M ≠ 0 := hMzero
    rcases exists_state_SionBracketRe_eq_psdSchattenPNorm_of_ACTraceMatrix_ne_zero
        rhoA psi tauC halpha (by simpa [M] using hMne) with
      ⟨sigma0, hSupport0, hsigma0⟩
    let N0 : CMatrix b := sigma0.matrix
    have hN0 : N0.PosSemidef := sigma0.pos
    have hN0trace : N0.trace = 1 := sigma0.trace_eq_one
    have hN0trace_re : N0.trace.re = 1 := by
      simpa [N0] using congrArg Complex.re hN0trace
    have htrace_target :
        ((M * CFC.rpow N0 r).trace).re = target := by
      have h := hsigma0
      rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma] at h
      simpa [M, N0, r, target, p, hM] using h
    let raw : Real -> Real := fun eps =>
      ((M * CFC.rpow (N0 + eps • (1 : CMatrix b)) r).trace).re
    let scale : Real -> Real := fun eps =>
      ((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹
    let reg : Real -> CMatrix b := fun eps =>
      scale eps • (N0 + eps • (1 : CMatrix b))
    have hraw :
        Filter.Tendsto raw (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds target) := by
      have h :=
        trace_mul_cMatrix_rpow_add_pos_smul_one_tendsto_of_support
          hN0 (by simpa [M, N0] using hSupport0) r
      have h' :
          Filter.Tendsto raw (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds ((M * CFC.rpow N0 r).trace.re)) := by
        simpa [raw, M, N0] using h
      rw [← htrace_target]
      exact h'
    have htraceScale :
        Filter.Tendsto scale (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) := by
      have htrace :
          Filter.Tendsto (fun eps : Real => (N0 + eps • (1 : CMatrix b)).trace.re)
            (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) := by
        have hcont : Continuous fun eps : Real =>
            (N0 + eps • (1 : CMatrix b)).trace.re := by
          fun_prop
        have hlim := (hcont.tendsto (0 : Real)).mono_left
          (nhdsWithin_le_nhds (a := (0 : Real)) (s := Set.Ioi (0 : Real)))
        simpa [N0, hN0trace_re] using hlim
      simpa [scale] using htrace.inv₀ one_ne_zero
    have hscalePow :
        Filter.Tendsto (fun eps : Real => scale eps ^ r)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 : Real)) := by
      have hpow :=
        (Real.continuousAt_rpow_const (1 : Real) r (Or.inl one_ne_zero)).tendsto.comp
          htraceScale
      simpa using hpow
    have hregValue :
        Filter.Tendsto
          (fun eps : Real => ((M * CFC.rpow (reg eps) r).trace).re)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds target) := by
      have heq :
          (fun eps : Real => ((M * CFC.rpow (reg eps) r).trace).re)
            =ᶠ[nhdsWithin (0 : Real) (Set.Ioi 0)]
          fun eps : Real => scale eps ^ r * raw eps := by
        filter_upwards [self_mem_nhdsWithin] with eps heps
        have hBpos : (N0 + eps • (1 : CMatrix b)).PosDef :=
          State.cMatrix_posSemidef_add_pos_smul_one_posDef hN0 heps
        have hscale_pos : 0 < scale eps := by
          have htr_pos : 0 < (N0 + eps • (1 : CMatrix b)).trace.re := by
            exact (Matrix.PosDef.trace_pos hBpos).1
          exact inv_pos.mpr htr_pos
        have hpow :
            CFC.rpow (reg eps) r =
              (scale eps ^ r : Real) •
                CFC.rpow (N0 + eps • (1 : CMatrix b)) r := by
          simpa [reg] using
            cMatrix_rpow_real_smul_posSemidef_schatten hBpos.posSemidef
              (le_of_lt hscale_pos) (s := r)
        change ((M * CFC.rpow (reg eps) r).trace).re = scale eps ^ r * raw eps
        rw [hpow]
        simp [raw, Matrix.trace_smul, Complex.real_smul]
      have hprod :
          Filter.Tendsto (fun eps : Real => scale eps ^ r * raw eps)
            (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds target) := by
        simpa using hscalePow.mul hraw
      exact hprod.congr' heq.symm
    have hupper : sInf (Set.range f) <= target := by
      exact ge_of_tendsto hregValue (by
        filter_upwards [self_mem_nhdsWithin] with eps heps
        have hBpos : (N0 + eps • (1 : CMatrix b)).PosDef :=
          State.cMatrix_posSemidef_add_pos_smul_one_posDef hN0 heps
        have htr_pos : 0 < (N0 + eps • (1 : CMatrix b)).trace.re := by
          exact (Matrix.PosDef.trace_pos hBpos).1
        have hscale_pos : 0 < scale eps := inv_pos.mpr htr_pos
        have hreg_pos : (reg eps).PosDef := by
          simpa [reg] using Matrix.PosDef.smul hBpos hscale_pos
        have hreg_trace : (reg eps).trace = 1 := by
          have htr_real :
              (N0 + eps • (1 : CMatrix b)).trace =
                ((N0 + eps • (1 : CMatrix b)).trace.re : Complex) := by
            exact posSemidef_trace_eq_re_coe hBpos.posSemidef
          have htr_ne : (N0 + eps • (1 : CMatrix b)).trace.re ≠ 0 :=
            ne_of_gt htr_pos
          calc
            (reg eps).trace =
                (scale eps : Complex) * (N0 + eps • (1 : CMatrix b)).trace := by
                  change (scale eps • (N0 + eps • (1 : CMatrix b))).trace =
                    (scale eps : Complex) * (N0 + eps • (1 : CMatrix b)).trace
                  rw [Matrix.trace_smul]
                  simpa using (Complex.real_smul (x := scale eps)
                    (z := (N0 + eps • (1 : CMatrix b)).trace))
            _ = (scale eps : Complex) *
                ((N0 + eps • (1 : CMatrix b)).trace.re : Complex) := by
                  exact congrArg (fun z : Complex => (scale eps : Complex) * z) htr_real
            _ = 1 := by
                  have htr_ne_complex :
                      ((N0 + eps • (1 : CMatrix b)).trace.re : Complex) ≠ 0 := by
                    exact_mod_cast htr_ne
                  have hscale_eq :
                      (scale eps : Complex) =
                        ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : Real) : Complex) := by
                    change ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : Real) : Complex) =
                      ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : Real) : Complex)
                    rfl
                  rw [hscale_eq]
                  simpa using inv_mul_cancel₀ htr_ne_complex
        let sigmaReg : State b :=
          { matrix := reg eps, pos := hreg_pos.posSemidef, trace_eq_one := hreg_trace }
        have hsigmaReg : sigmaReg.matrix.PosDef := hreg_pos
        have hmem :
            ((M * CFC.rpow (reg eps) r).trace).re ∈ Set.range f := by
          refine ⟨⟨sigmaReg, hsigmaReg⟩, ?_⟩
          change sandwichedMutualInformationSionBracketRe rhoA psi sigmaReg tauC alpha =
            ((M * CFC.rpow (reg eps) r).trace).re
          simpa [sigmaReg, M, r] using
            sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma
              rhoA psi sigmaReg tauC alpha
        exact csInf_le hBdd hmem)
    have hlower : target <= sInf (Set.range f) :=
      le_csInf (Set.range_nonempty f) hLower
    exact le_antisymm hupper hlower

/-- Fixed-`tau_C` logarithmic form of the KW reverse-Holder infimum after
closing the full-rank side-state regularization.

This is the post-Sion rewrite target in `EA_capacity.tex:2028-2035`: once the
`sigma_B` infimum has been exchanged past the `tau_C` supremum, the full-rank
infimum of the logarithmic Sion bracket is exactly the logarithmic Schatten
`AC` trace-matrix expression. -/
theorem sandwichedMutualInformationSionBracketLog_fullRank_sInf_eq_ACTraceMatrixLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) (hrhoA : rhoA.matrix.PosDef) (htauC : tauC.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha)) =
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
            (alpha / (2 * alpha - 1))) := by
  let S := {sigma : State b // sigma.matrix.PosDef}
  let raw : S → ℝ := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let target : ℝ :=
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
      (alpha / (2 * alpha - 1))
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hraw_sInf : sInf (Set.range raw) = target := by
    simpa [S, raw, target] using
      sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA psi tauC halpha
  have htarget_lower : target ∈ lowerBounds (Set.range raw) := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    simpa [raw, target] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA psi sigmaB.1 tauC halpha
        (Matrix.Supports.of_right_posDef
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          sigmaB.1.matrix sigmaB.2)
  have hraw_bdd : BddBelow (Set.range raw) := ⟨target, htarget_lower⟩
  have htarget_pos : 0 < target := by
    simpa [target] using
      psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA psi tauC hrhoA htauC halpha
  have hinf_pos : 0 < sInf (Set.range raw) := by
    rw [hraw_sInf]
    exact htarget_pos
  have hlog_sInf :
      sInf (Set.range fun sigmaB : S => log2 (raw sigmaB)) = log2 target := by
    have himage :
        Set.range (fun sigmaB : S => log2 (raw sigmaB)) =
          log2 '' Set.range raw := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨raw sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty raw) hraw_bdd hinf_pos,
      hraw_sInf]
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using sandwichedCoeff_pos halpha)
  have hscaled :
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
        coeff * log2 target := by
    let logs : S → ℝ := fun sigmaB => log2 (raw sigmaB)
    have himage :
        Set.range (fun sigmaB : S => coeff * logs sigmaB) =
          (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨logs sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨y, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨y, hy, hxy⟩
        exact ⟨y, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 target := by
            rw [hlog_sInf]
  simpa [S, raw, coeff, target] using hscaled

/-- Fixed-`tau_C` logarithmic reverse-Holder formula when the KW `AC` trace
matrix is nonzero.

This is the same post-Sion reverse-Holder step as
`sandwichedMutualInformationSionBracketLog_fullRank_sInf_eq_ACTraceMatrixLog`,
but it records the actual logarithm side condition: strict positivity of the
Schatten expression follows from a nonzero PSD `AC` trace matrix.  It is the
form needed before the full-rank `tau_C` closure, where singular states are
approximated by full-rank regularizations. -/
theorem sandwichedMutualInformationSionBracketLog_fullRank_sInf_eq_ACTraceMatrixLog_of_ne_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha ≠ 0) :
    sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha)) =
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
            (alpha / (2 * alpha - 1))) := by
  let S := {sigma : State b // sigma.matrix.PosDef}
  let raw : S → ℝ := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let target : ℝ :=
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
      (alpha / (2 * alpha - 1))
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hraw_sInf : sInf (Set.range raw) = target := by
    simpa [S, raw, target] using
      sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA psi tauC halpha
  have htarget_lower : target ∈ lowerBounds (Set.range raw) := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    simpa [raw, target] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA psi sigmaB.1 tauC halpha
        (Matrix.Supports.of_right_posDef
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          sigmaB.1.matrix sigmaB.2)
  have hraw_bdd : BddBelow (Set.range raw) := ⟨target, htarget_lower⟩
  have htarget_pos : 0 < target := by
    convert
      psdSchattenPNorm_pos_of_ne_zero
        (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
        (p := alpha / (2 * alpha - 1))
        hMne using 1
  have hinf_pos : 0 < sInf (Set.range raw) := by
    rw [hraw_sInf]
    exact htarget_pos
  have hlog_sInf :
      sInf (Set.range fun sigmaB : S => log2 (raw sigmaB)) = log2 target := by
    have himage :
        Set.range (fun sigmaB : S => log2 (raw sigmaB)) =
          log2 '' Set.range raw := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨raw sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty raw) hraw_bdd hinf_pos,
      hraw_sInf]
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using sandwichedCoeff_pos halpha)
  have hscaled :
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
        coeff * log2 target := by
    let logs : S → ℝ := fun sigmaB => log2 (raw sigmaB)
    have himage :
        Set.range (fun sigmaB : S => coeff * logs sigmaB) =
          (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨logs sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨_, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨_, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨_, hy, hxy⟩
        exact ⟨_, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 target := by
            rw [hlog_sInf]
  simpa [S, raw, coeff, target] using hscaled

end PureVector

namespace State

/-- Singular side-information references are outside the finite high-`alpha`
branch when the joint state is full rank.

This is the local support-closure step behind the KW reduction of the
`sigma_B` optimization to the full-rank side-reference domain: if
`rho_AB` is positive definite and `rho_AB` is supported by
`rho_A ⊗ sigma_B`, then `rho_A ⊗ sigma_B` is positive definite, hence
`sigma_B` is positive definite after tracing out `A`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_side_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrho : rhoAB.matrix.PosDef) (hsigma : ¬ sigmaB.matrix.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alphaR = ⊤ := by
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [State.sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
  refine State.sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
    rhoAB (rhoAB.marginalA.prod sigmaB).pos alphaR ?_
  intro hSupport
  have hrefPD : (rhoAB.marginalA.prod sigmaB).matrix.PosDef :=
    Matrix.Supports.posDef_right_of_left_posDef hrho
      (rhoAB.marginalA.prod sigmaB).pos hSupport
  haveI : Nonempty a := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  exact hsigma
    (State.prod_right_posDef_of_posDef rhoAB.marginalA sigmaB hrefPD)

theorem sandwichedRenyiReference_reindex {alpha : Type u1} {beta : Type u2}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho : State alpha) (sigma : CMatrix alpha) (e : alpha ≃ beta)
    (hrho : rho.matrix.PosDef) (hsigma : sigma.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1) :
    sandwichedRenyiReference (rho.reindex e) (Matrix.reindex e e sigma)
        (State.reindex_posDef rho e hrho)
        (hsigma.submatrix e.symm.injective)
        alphaR halpha_pos halpha_ne_one =
      sandwichedRenyiReference rho sigma hrho hsigma
        alphaR halpha_pos halpha_ne_one := by
  unfold sandwichedRenyiReference
  let s := (1 - alphaR) / (2 * alphaR)
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow
        (CFC.rpow (Matrix.reindex e e sigma) s *
          Matrix.reindex e e rho.matrix *
          CFC.rpow (Matrix.reindex e e sigma) s) alphaR).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (CFC.rpow sigma s * rho.matrix * CFC.rpow sigma s)
        alphaR).trace).re)
  rw [cMatrix_rpow_reindex_posDef e sigma hsigma s]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow
        (((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s)) *
          ((Matrix.reindexAlgEquiv ℂ ℂ e) rho.matrix) *
          ((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s))) alphaR).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (CFC.rpow sigma s * rho.matrix * CFC.rpow sigma s)
        alphaR).trace).re)
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
    (CFC.rpow sigma s) rho.matrix]
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
    (CFC.rpow sigma s * rho.matrix) (CFC.rpow sigma s)]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow
        (Matrix.reindex e e (CFC.rpow sigma s * rho.matrix * CFC.rpow sigma s))
        alphaR).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (CFC.rpow sigma s * rho.matrix * CFC.rpow sigma s)
        alphaR).trace).re)
  rw [cMatrix_rpow_reindex_posDef e
    (CFC.rpow sigma s * rho.matrix * CFC.rpow sigma s) ?_ alphaR]
  rw [cMatrix_trace_reindex e]
  have hC : (CFC.rpow sigma s).PosDef := by
    exact cMatrix_rpow_posDef_of_posDef hsigma s
  have hChm : (CFC.rpow sigma s).IsHermitian := by
    exact (cMatrix_rpow_posSemidef (A := sigma) (s := s) hsigma.posSemidef).isHermitian
  have hinner := hrho.mul_mul_conjTranspose_same (B := CFC.rpow sigma s) ?_
  · rwa [hChm.eq] at hinner
  · exact Matrix.vecMul_injective_of_isUnit hC.isUnit

/-- The finite high-`alpha` PSD-reference branch is invariant under finite
reindexing.

This is the support-convention replacement for the older full-rank
`sandwichedRenyiReference_reindex`: KW's product-state proof only repartitions
the tensor factors, so the value of the finite PSD-reference expression should
not depend on the chosen product association. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_reindex
    {alpha : Type u1} {beta : Type u2}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho : State alpha) (sigma : CMatrix alpha) (e : alpha ≃ beta)
    (hsigma : sigma.PosSemidef) (alphaR : ℝ) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.reindex e)
        (Matrix.reindex e e sigma) (hsigma.submatrix e.symm) alphaR =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alphaR := by
  unfold sandwichedRenyiPSDReferenceHighAlphaFinite sandwichedRenyiReferenceInner
  let s : ℝ := (1 - alphaR) / (2 * alphaR)
  have hpow_sigma :
      CFC.rpow (Matrix.reindex e e sigma) s =
        Matrix.reindex e e (CFC.rpow sigma s) :=
    cMatrix_rpow_reindex_posSemidef_support e hsigma s
  let inner : CMatrix alpha := CFC.rpow sigma s * rho.matrix * CFC.rpow sigma s
  have hinner_psd : inner.PosSemidef := by
    simpa [inner, s] using
      sandwichedRenyiReferenceInner_posSemidef rho hsigma alphaR
  have hinner_reindex :
      CFC.rpow (Matrix.reindex e e sigma) s *
            (rho.reindex e).matrix *
          CFC.rpow (Matrix.reindex e e sigma) s =
        Matrix.reindex e e inner := by
    rw [hpow_sigma]
    change
      (Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s) *
            (Matrix.reindexAlgEquiv ℂ ℂ e) rho.matrix *
          (Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s) =
        (Matrix.reindexAlgEquiv ℂ ℂ e) inner
    rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
      (CFC.rpow sigma s) rho.matrix]
    rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
      (CFC.rpow sigma s * rho.matrix) (CFC.rpow sigma s)]
  have hpow_inner :
      CFC.rpow
          (CFC.rpow (Matrix.reindex e e sigma) s *
              (rho.reindex e).matrix *
            CFC.rpow (Matrix.reindex e e sigma) s)
          alphaR =
        Matrix.reindex e e (CFC.rpow inner alphaR) := by
    rw [hinner_reindex]
    exact cMatrix_rpow_reindex_posSemidef_support e hinner_psd alphaR
  unfold psdTracePower
  apply congrArg (fun x : ℝ => 1 / (alphaR - 1) * log2 x)
  change
    (CFC.rpow
          (CFC.rpow (Matrix.reindex e e sigma) s *
              (rho.reindex e).matrix *
            CFC.rpow (Matrix.reindex e e sigma) s)
          alphaR).trace.re =
      (CFC.rpow inner alphaR).trace.re
  rw [hpow_inner]
  rw [cMatrix_trace_reindex e]

/-- State-reference form of
`sandwichedRenyiPSDReferenceHighAlphaFinite_reindex`.

Keeping the reference as a `State` packages the PSD witness together with the
matrix equality, avoiding dependent proof-object rewrites when a product
reference is merely repartitioned. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_reindex_stateReference
    {alpha : Type u1} {beta : Type u2}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho : State alpha) (sigma : State alpha) (e : alpha ≃ beta)
    (alphaR : ℝ) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.reindex e)
        (sigma.reindex e).matrix (sigma.reindex e).pos alphaR =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma.matrix sigma.pos alphaR := by
  simpa [State.reindex_matrix] using
    sandwichedRenyiPSDReferenceHighAlphaFinite_reindex
      (rho := rho) (sigma := sigma.matrix) (e := e) (hsigma := sigma.pos) alphaR

/-- Local support-convention Kronecker rule for matrix real powers.

The public theorem `cMatrix_rpow_kronecker_nonneg` covers PSD matrices with
nonnegative exponents.  The KW sandwiched-Renyi product calculation also needs
the negative exponent `s = (1 - alpha) / (2 * alpha)`, so this lemma follows the
same finite-dimensional diagonal/unitary route and uses the repository's
`0^s = 0` support convention. -/
theorem cMatrix_rpow_kronecker_posSemidef_support
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    {A : CMatrix x} {B : CMatrix y} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : ℝ) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) := by
  let UA := hA.isHermitian.eigenvectorUnitary
  let UB := hB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod x y) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix x) (UB : CMatrix y),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let da : x → ℝ := hA.isHermitian.eigenvalues
  let db : y → ℝ := hB.isHermitian.eigenvalues
  let dprod : Prod x y → ℝ := fun i => da i.1 * db i.2
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
    simp [U, dprod, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  have hA_rpow :
      CFC.rpow A s =
        Unitary.conjStarAlgAut ℂ _ UA
          (Matrix.diagonal (fun i => ((da i ^ s : ℝ) : ℂ))) := by
    rw [hA_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal UA da hda s
  have hB_rpow :
      CFC.rpow B s =
        Unitary.conjStarAlgAut ℂ _ UB
          (Matrix.diagonal (fun i => ((db i ^ s : ℝ) : ℂ))) := by
    rw [hB_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal UB db hdb s
  have hleft :
      CFC.rpow (Matrix.kronecker A B) s =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => ((dprod i ^ s : ℝ) : ℂ))) := by
    rw [hAB_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U dprod hdprod s
  have hdiag :
      Matrix.diagonal (fun i : Prod x y => ((dprod i ^ s : ℝ) : ℂ)) =
        Matrix.diagonal
          (fun i : Prod x y => (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [dprod, Real.mul_rpow (hda i.1) (hdb i.2)]
    · simp [Matrix.diagonal, hij]
  have hright :
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal
            (fun i : Prod x y => (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ))) := by
    rw [hA_rpow, hB_rpow]
    simp [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  rw [hleft, hdiag, hright]

/-- Support-convention product rule for the sandwiched `Q` functional.

This is the PSD/high-`alpha` algebra hidden in KW
`EA_capacity.tex:1183-1186`: even when references are singular, the
repository support convention for `CFC.rpow` makes the tensor-product trace
factorize. -/
theorem sandwichedRenyiQ_kronecker_posSemidef_support
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    {rho1 sigma1 : CMatrix x} {rho2 sigma2 : CMatrix y}
    (hrho1 : rho1.PosSemidef) (hsigma1 : sigma1.PosSemidef)
    (hrho2 : rho2.PosSemidef) (hsigma2 : sigma2.PosSemidef)
    (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha) :
    State.sandwichedRenyiQ
        (Matrix.kronecker rho1 rho2)
        (Matrix.kronecker sigma1 sigma2)
        (hrho1.kronecker hrho2) (hsigma1.kronecker hsigma2) alpha =
      State.sandwichedRenyiQ rho1 sigma1 hrho1 hsigma1 alpha *
        State.sandwichedRenyiQ rho2 sigma2 hrho2 hsigma2 alpha := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let C1 : CMatrix x := CFC.rpow sigma1 s
  let C2 : CMatrix y := CFC.rpow sigma2 s
  let inner1 : CMatrix x := C1 * rho1 * C1
  let inner2 : CMatrix y := C2 * rho2 * C2
  have hC :
      CFC.rpow (Matrix.kronecker sigma1 sigma2) s =
        Matrix.kronecker C1 C2 := by
    simpa [C1, C2, s] using
      cMatrix_rpow_kronecker_posSemidef_support hsigma1 hsigma2 s
  have hinner :
      CFC.rpow (Matrix.kronecker sigma1 sigma2) s *
          Matrix.kronecker rho1 rho2 *
          CFC.rpow (Matrix.kronecker sigma1 sigma2) s =
        Matrix.kronecker inner1 inner2 := by
    rw [hC]
    simp [inner1, inner2, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  have hC1_hm : C1.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := sigma1) (s := s) hsigma1).isHermitian
  have hC2_hm : C2.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := sigma2) (s := s) hsigma2).isHermitian
  have hinner1_psd : inner1.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hrho1 C1
    rwa [hC1_hm.eq] at h
  have hinner2_psd : inner2.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hrho2 C2
    rwa [hC2_hm.eq] at h
  have htraceC :
      (CFC.rpow
        (CFC.rpow (Matrix.kronecker sigma1 sigma2) s * Matrix.kronecker rho1 rho2 *
          CFC.rpow (Matrix.kronecker sigma1 sigma2) s) alpha).trace =
        (CFC.rpow inner1 alpha).trace * (CFC.rpow inner2 alpha).trace := by
    rw [hinner]
    rw [cMatrix_rpow_kronecker_nonneg hinner1_psd hinner2_psd halpha_nonneg]
    change
      (Matrix.kroneckerMap (fun x y => x * y)
        (CFC.rpow inner1 alpha) (CFC.rpow inner2 alpha)).trace =
        (CFC.rpow inner1 alpha).trace * (CFC.rpow inner2 alpha).trace
    rw [Matrix.trace_kronecker]
  have him1 : ((CFC.rpow inner1 alpha).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner1 alpha).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner1) (y := alpha)))
    exact htrace_nonneg.2.symm
  have him2 : ((CFC.rpow inner2 alpha).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner2 alpha).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner2) (y := alpha)))
    exact htrace_nonneg.2.symm
  unfold State.sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.kronecker sigma1 sigma2) s * Matrix.kronecker rho1 rho2 *
        CFC.rpow (Matrix.kronecker sigma1 sigma2) s) alpha).trace.re =
      (CFC.rpow inner1 alpha).trace.re * (CFC.rpow inner2 alpha).trace.re
  rw [htraceC, Complex.mul_re, him1, him2]
  ring

/-- Product rule for the supported high-`alpha` finite PSD-reference branch.

This is the finite-branch form of the KW step
`EA_capacity.tex:1183-1186`, where the sandwiched Renyi divergence of product
states against product references splits into the sum of the two divergences.
The hypotheses are support-convention hypotheses, not full-rank assumptions. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_prod_of_supports
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    (rho1 : State x) (rho2 : State y)
    {sigma1 : CMatrix x} {sigma2 : CMatrix y}
    (hsigma1 : sigma1.PosSemidef) (hsigma2 : sigma2.PosSemidef)
    (hsupport1 : Matrix.Supports rho1.matrix sigma1)
    (hsupport2 : Matrix.Supports rho2.matrix sigma2)
    {alpha : ℝ} (halpha : 1 < alpha) :
    State.sandwichedRenyiPSDReferenceHighAlphaFinite (rho1.prod rho2)
        (Matrix.kronecker sigma1 sigma2) (hsigma1.kronecker hsigma2) alpha =
      State.sandwichedRenyiPSDReferenceHighAlphaFinite rho1 sigma1 hsigma1 alpha +
        State.sandwichedRenyiPSDReferenceHighAlphaFinite rho2 sigma2 hsigma2 alpha := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hq :=
    sandwichedRenyiQ_kronecker_posSemidef_support
      (rho1 := rho1.matrix) (sigma1 := sigma1)
      (rho2 := rho2.matrix) (sigma2 := sigma2)
      rho1.pos hsigma1 rho2.pos hsigma2 alpha (le_of_lt halpha_pos)
  have htrace :
      psdTracePower
          (State.sandwichedRenyiReferenceInner (rho1.prod rho2)
            (Matrix.kronecker sigma1 sigma2) alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef (rho1.prod rho2)
            (hsigma1.kronecker hsigma2) alpha)
          alpha =
        psdTracePower (State.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
            (State.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha)
            alpha *
          psdTracePower (State.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
            (State.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha)
            alpha := by
    simpa [State.sandwichedRenyiQ, State.sandwichedRenyiReferenceInner,
      State.prod_matrix_kronecker, psdTracePower] using hq
  have hq1_pos :
      0 <
        psdTracePower (State.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha) alpha := by
    exact State.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports rho1 hsigma1
      hsupport1 alpha
  have hq2_pos :
      0 <
        psdTracePower (State.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha) alpha := by
    exact State.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports rho2 hsigma2
      hsupport2 alpha
  have hqprod_pos :
      0 <
        psdTracePower
          (State.sandwichedRenyiReferenceInner (rho1.prod rho2)
            (Matrix.kronecker sigma1 sigma2) alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef (rho1.prod rho2)
            (hsigma1.kronecker hsigma2) alpha)
          alpha := by
    rw [htrace]
    exact mul_pos hq1_pos hq2_pos
  unfold State.sandwichedRenyiPSDReferenceHighAlphaFinite
  rw [htrace]
  have hlog :
      log2
          (psdTracePower (State.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
              (State.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha) alpha *
            psdTracePower (State.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
              (State.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha) alpha) =
        log2
            (psdTracePower (State.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
              (State.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha) alpha) +
          log2
            (psdTracePower (State.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
              (State.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha) alpha) := by
    exact log2_mul hq1_pos.ne' hq2_pos.ne'
  rw [hlog]
  ring

/-- Real-valued full-rank candidate for sandwiched-Renyi mutual information.

This is the positive-definite branch of
`State.sandwichedRenyiMutualInformationCandidateE`, kept as a real-valued
quantity so the KW product `inf` split can use real scalar order lemmas before
the singular-reference closure is proved. -/
def sandwichedRenyiMutualInformationCandidateRealPosDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    (hsigma : sigmaB.matrix.PosDef) (alphaR : ℝ) (halpha : 1 < alphaR) : ℝ :=
  sandwichedRenyiReference rhoAB (rhoAB.marginalA.prod sigmaB).matrix
    hrho (State.prod_posDef hA hsigma)
    alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)

/-- Full-rank sandwiched mutual-information candidates are nonnegative in the
proved high-`alpha` range. -/
theorem sandwichedRenyiMutualInformationCandidateRealPosDef_nonneg
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    (hsigma : sigmaB.matrix.PosDef) {alphaR : ℝ} (halpha : 1 < alphaR) :
    0 ≤ sandwichedRenyiMutualInformationCandidateRealPosDef
      rhoAB sigmaB hrho hA hsigma alphaR halpha := by
  unfold sandwichedRenyiMutualInformationCandidateRealPosDef
  rw [sandwichedRenyiReference_state rhoAB (rhoAB.marginalA.prod sigmaB)
    hrho (State.prod_posDef hA hsigma)
    alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)]
  exact sandwichedRenyi_nonneg_of_one_lt rhoAB (rhoAB.marginalA.prod sigmaB)
    hrho (State.prod_posDef hA hsigma) alphaR halpha

/-- The full-rank side-reference candidate family is bounded below. -/
theorem sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b))
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    BddBelow (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
      sandwichedRenyiMutualInformationCandidateRealPosDef
        rhoAB sigmaB.1 hrho hA sigmaB.2 alphaR halpha) := by
  refine ⟨0, ?_⟩
  rintro y ⟨sigmaB, rfl⟩
  exact sandwichedRenyiMutualInformationCandidateRealPosDef_nonneg
    rhoAB sigmaB.1 hrho hA sigmaB.2 halpha

/-- The extended-real candidate is the coercion of the real full-rank branch. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    (hsigma : sigmaB.matrix.PosDef) {alphaR : ℝ} (halpha : 1 < alphaR) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alphaR =
      (sandwichedRenyiMutualInformationCandidateRealPosDef
        rhoAB sigmaB hrho hA hsigma alphaR halpha : EReal) := by
  unfold sandwichedRenyiMutualInformationCandidateRealPosDef
  exact State.sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    rhoAB sigmaB hrho hA hsigma halpha

/-- The high-`alpha` side-information optimization may be restricted to
full-rank side references when the state and its `A` marginal are full rank.

This packages the KW support convention: singular references contribute
`⊤`, while full-rank references are exactly the real-valued finite branch. -/
theorem sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (rhoAB : State (Prod a b))
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    rhoAB.sandwichedRenyiMutualInformationE alphaR =
      sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
        (sandwichedRenyiMutualInformationCandidateRealPosDef
          rhoAB sigmaB.1 hrho hA sigmaB.2 alphaR halpha : EReal)) := by
  haveI : Nonempty {sigma : State b // sigma.matrix.PosDef} :=
    ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
  apply le_antisymm
  · refine le_csInf (Set.range_nonempty _) ?_
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    have hle :=
      sInf_le
      (State.sandwichedRenyiMutualInformationCandidateE_mem_valueSet rhoAB sigmaB.1 alphaR)
    have heq :=
      sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
        rhoAB sigmaB.1 hrho hA sigmaB.2 halpha
    simpa [heq] using hle
  · refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alphaR) ?_
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    by_cases hsigma : sigmaB.matrix.PosDef
    · have hle :
          sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
            (sandwichedRenyiMutualInformationCandidateRealPosDef
              rhoAB sigmaB.1 hrho hA sigmaB.2 alphaR halpha : EReal)) ≤
            (sandwichedRenyiMutualInformationCandidateRealPosDef
              rhoAB sigmaB hrho hA hsigma alphaR halpha : EReal) :=
        sInf_le ⟨⟨sigmaB, hsigma⟩, rfl⟩
      have heq :=
        sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
          rhoAB sigmaB hrho hA hsigma halpha
      simpa [heq] using hle
    · have heq :=
        sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_side_posDef
          rhoAB sigmaB hrho hsigma halpha
      simp [heq]

variable {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
variable [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
variable [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]

/-- Repartition `(A1 x B1) x (A2 x B2)` as `(A1 x A2) x (B1 x B2)`. -/
def bipartiteProductEquiv :
    Prod (Prod a1 b1) (Prod a2 b2) ≃ Prod (Prod a1 a2) (Prod b1 b2) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

/-- Product of bipartite states, repartitioned as a bipartite state
`(A1 x A2) : (B1 x B2)`. -/
def bipartiteProduct (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2)) :
    State (Prod (Prod a1 a2) (Prod b1 b2)) :=
  (xi.prod omega).reindex bipartiteProductEquiv

/-- Positive definiteness is preserved by forming and repartitioning a product
of bipartite states. -/
theorem bipartiteProduct_posDef
    {xi : State (Prod a1 b1)} {omega : State (Prod a2 b2)}
    (hxi : xi.matrix.PosDef) (homega : omega.matrix.PosDef) :
    (xi.bipartiteProduct omega).matrix.PosDef := by
  unfold bipartiteProduct
  exact State.reindex_posDef (xi.prod omega) bipartiteProductEquiv
    (State.prod_posDef hxi homega)

/-- The left marginal of a repartitioned product bipartite state is the product
of the two left marginals. -/
theorem bipartiteProduct_marginalA
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2)) :
    (xi.bipartiteProduct omega).marginalA = xi.marginalA.prod omega.marginalA := by
  apply State.ext
  ext x y
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp [bipartiteProduct, bipartiteProductEquiv, State.reindex, State.marginalA,
    partialTraceB, State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-- The right marginal of a repartitioned product bipartite state is the product
of the two right marginals. -/
theorem bipartiteProduct_marginalB
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2)) :
    (xi.bipartiteProduct omega).marginalB = xi.marginalB.prod omega.marginalB := by
  apply State.ext
  ext x y
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp [bipartiteProduct, bipartiteProductEquiv, State.reindex, State.marginalB,
    partialTraceA, State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-- Any bipartite state is supported by its left marginal tensored with a
full-rank right-side state.

This is the support-convention form of the side-information branch in KW
`EA_capacity.tex:1983-1986`: the optimized side state can be full-rank even
when the left marginal of the bipartite state is singular. -/
theorem supports_marginalA_prod_of_side_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hsigmaB : sigmaB.matrix.PosDef) :
    Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix := by
  have hside :
      Matrix.Supports (rhoAB.marginalA.prod rhoAB.marginalB).matrix
        (rhoAB.marginalA.prod sigmaB).matrix := by
    simpa [State.prod] using
      Matrix.Supports.kronecker_right_of_posDef
        rhoAB.marginalA.matrix rhoAB.marginalB.matrix sigmaB.matrix hsigmaB
  exact rhoAB.matrix_supports_prod_marginals.trans hside

/-- Product side-information references repartition in the same way as product
bipartite states. -/
theorem bipartiteProduct_candidateReference
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    (sigma1 : State b1) (sigma2 : State b2) :
    (xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2) =
      ((xi.marginalA.prod sigma1).prod (omega.marginalA.prod sigma2)).reindex
        (bipartiteProductEquiv (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2)) := by
  rw [bipartiteProduct_marginalA]
  apply State.ext
  ext x y
  rcases x with ⟨⟨xA1, xA2⟩, ⟨xB1, xB2⟩⟩
  rcases y with ⟨⟨yA1, yA2⟩, ⟨yB1, yB2⟩⟩
  simp [bipartiteProductEquiv, State.reindex, State.prod, Matrix.kronecker,
    Matrix.kroneckerMap_apply, mul_assoc, mul_left_comm]

/-- Factor support hypotheses imply support for the repartitioned product
candidate reference.

This is the support-convention bridge used in the KW state-product proof:
from
`xi_AB << xi_A ⊗ sigma_B` and `omega_AB << omega_A ⊗ tau_B`, the product state
is supported by the product candidate reference after repartitioning
`(A1B1)(A2B2)` as `(A1A2)(B1B2)`. -/
theorem bipartiteProduct_candidateReference_supports_of_supports
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    (sigma1 : State b1) (sigma2 : State b2)
    (hsupport1 :
      Matrix.Supports xi.matrix (xi.marginalA.prod sigma1).matrix)
    (hsupport2 :
      Matrix.Supports omega.matrix (omega.marginalA.prod sigma2).matrix) :
    Matrix.Supports (xi.bipartiteProduct omega).matrix
      ((xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2)).matrix := by
  let ref1 : State (Prod a1 b1) := xi.marginalA.prod sigma1
  let ref2 : State (Prod a2 b2) := omega.marginalA.prod sigma2
  let e := bipartiteProductEquiv (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2)
  have hraw :
      Matrix.Supports (Matrix.kronecker xi.matrix omega.matrix)
        (Matrix.kronecker ref1.matrix ref2.matrix) := by
    simpa [ref1, ref2, State.prod_matrix_kronecker] using
      Matrix.Supports.kronecker_of_posSemidef xi.pos ref1.pos omega.pos ref2.pos
        hsupport1 hsupport2
  have hreindex := Matrix.Supports.reindex hraw e
  have hrefState :
      (xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2) =
        (ref1.prod ref2).reindex e := by
    simpa [e, ref1, ref2] using
      State.bipartiteProduct_candidateReference xi omega sigma1 sigma2
  have hleftMatrix :
      (xi.bipartiteProduct omega).matrix =
        (Matrix.kronecker xi.matrix omega.matrix).submatrix e.symm e.symm := by
    simp [e, State.bipartiteProduct, State.reindex_matrix, State.prod_matrix_kronecker]
  have hrightMatrix :
      ((xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2)).matrix =
        (Matrix.kronecker ref1.matrix ref2.matrix).submatrix e.symm e.symm := by
    rw [hrefState]
    simp [e, State.reindex_matrix, State.prod_matrix_kronecker]
  rw [hleftMatrix, hrightMatrix]
  exact hreindex

end State

namespace PureVector

/-- The KW product purification reduces on `A1A2B1B2` to the repartitioned
product of the two `AB` marginals.

This is the finite-dimensional matrix form of the source step in
`EA_capacity.tex:1200-1207` where a product purification of
`xi_{A1B1} ⊗ omega_{A2B2}` is chosen before restricting the `tau` optimization
to product states. -/
theorem bipartiteProductPurification_marginalAB
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2)) :
    (bipartiteProductPurification psi phi).state.marginalAB =
      psi.state.marginalAB.bipartiteProduct phi.state.marginalAB := by
  apply State.ext
  ext x y
  rcases x with ⟨⟨i1, i2⟩, ⟨j1, j2⟩⟩
  rcases y with ⟨⟨i1', i2'⟩, ⟨j1', j2'⟩⟩
  simp [bipartiteProductPurification, bipartiteProductPurificationEquiv,
    PureVector.reindex_state, State.reindex, State.bipartiteProduct, State.marginalAB,
    State.bipartiteProductEquiv, State.marginalA, partialTraceB, State.prod, Matrix.kronecker,
    Matrix.kroneckerMap_apply, PureVector.state_matrix, rankOneMatrix_apply,
    Fintype.sum_prod_type, mul_assoc]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k1 _hk1
  apply Finset.sum_congr rfl
  intro k2 _hk2
  ring

/-- The `A1A2` marginal of the KW product purification is the product of the
two `A` marginals. -/
theorem bipartiteProductPurification_marginalA
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2)) :
    (bipartiteProductPurification psi phi).state.marginalAB.marginalA =
      psi.state.marginalAB.marginalA.prod phi.state.marginalAB.marginalA := by
  rw [bipartiteProductPurification_marginalAB, State.bipartiteProduct_marginalA]

/-- The KW `AC` weight factorizes over product input and reference states on
the positive-definite branch.

This is the pointwise matrix version of the product factorization used in
`EA_capacity.tex:1201-1208`. -/
theorem sandwichedMutualInformationACWeight_prod_posDef
    {a1 c1 a2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype c1] [DecidableEq c1]
    [Fintype a2] [DecidableEq a2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    (htauC1 : tauC1.matrix.PosDef) (htauC2 : tauC2.matrix.PosDef)
    (alpha : Real) (i1 i1' : a1) (i2 i2' : a2)
    (k1 k1' : c1) (k2 k2' : c2) :
    sandwichedMutualInformationACWeight (rhoA1.prod rhoA2) (tauC1.prod tauC2) alpha
        ((i1, i2), (k1, k2)) ((i1', i2'), (k1', k2')) =
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k1) (i1', k1') *
        sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (i2, k2) (i2', k2') := by
  simp only [sandwichedMutualInformationACWeight]
  rw [State.prod_matrix_kronecker rhoA1 rhoA2]
  rw [State.prod_matrix_kronecker tauC1 tauC2]
  rw [cMatrix_rpow_kronecker_posDef hrhoA1 hrhoA2 ((1 - alpha) / alpha)]
  rw [cMatrix_rpow_kronecker_posDef htauC1 htauC2 ((alpha - 1) / alpha)]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc, mul_left_comm, mul_comm]

/-- The KW `AC` weight factorizes over product input and reference states on
the PSD `tau_C` branch.

The `rho_A` exponent can be negative and therefore still uses full-rank
`rho_A`; the `tau_C` exponent is `(alpha - 1) / alpha ≥ 0`, so the PSD
Kronecker-power theorem suffices. -/
theorem sandwichedMutualInformationACWeight_prod
    {a1 c1 a2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype c1] [DecidableEq c1]
    [Fintype a2] [DecidableEq a2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha)
    (i1 i1' : a1) (i2 i2' : a2)
    (k1 k1' : c1) (k2 k2' : c2) :
    sandwichedMutualInformationACWeight (rhoA1.prod rhoA2) (tauC1.prod tauC2) alpha
        ((i1, i2), (k1, k2)) ((i1', i2'), (k1', k2')) =
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k1) (i1', k1') *
        sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (i2, k2) (i2', k2') := by
  simp only [sandwichedMutualInformationACWeight]
  rw [State.prod_matrix_kronecker rhoA1 rhoA2]
  rw [State.prod_matrix_kronecker tauC1 tauC2]
  rw [cMatrix_rpow_kronecker_posDef hrhoA1 hrhoA2 ((1 - alpha) / alpha)]
  rw [cMatrix_rpow_kronecker_nonneg tauC1.pos tauC2.pos
    (le_of_lt (sandwichedAlphaPrime_pos_lt_one halpha).1)]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc, mul_left_comm, mul_comm]

/-- Support-convention version of the KW `AC` weight product identity.

Unlike `sandwichedMutualInformationACWeight_prod`, this version also uses the
PSD support convention for the possibly negative `rho_A` exponent.  This is the
source-faithful singular-state branch of the factorization in
`EA_capacity.tex:1201-1208`. -/
theorem sandwichedMutualInformationACWeight_prod_support
    {a1 c1 a2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype c1] [DecidableEq c1]
    [Fintype a2] [DecidableEq a2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (tauC1 : State c1) (tauC2 : State c2)
    {alpha : Real} (halpha : 1 < alpha)
    (i1 i1' : a1) (i2 i2' : a2)
    (k1 k1' : c1) (k2 k2' : c2) :
    sandwichedMutualInformationACWeight (rhoA1.prod rhoA2) (tauC1.prod tauC2) alpha
        ((i1, i2), (k1, k2)) ((i1', i2'), (k1', k2')) =
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k1) (i1', k1') *
        sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (i2, k2) (i2', k2') := by
  simp only [sandwichedMutualInformationACWeight]
  rw [State.prod_matrix_kronecker rhoA1 rhoA2]
  rw [State.prod_matrix_kronecker tauC1 tauC2]
  rw [State.cMatrix_rpow_kronecker_posSemidef_support
    rhoA1.pos rhoA2.pos ((1 - alpha) / alpha)]
  rw [cMatrix_rpow_kronecker_nonneg tauC1.pos tauC2.pos
    (le_of_lt (sandwichedAlphaPrime_pos_lt_one halpha).1)]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc, mul_left_comm, mul_comm]

/-- Finite-sum factorization used after the KW product `AC` trace entries have
been reduced to componentwise products. -/
private theorem sum_three_mul_sum_three
    {x1 y1 z1 x2 y2 z2 : Type*}
    [Fintype x1] [DecidableEq x1] [Fintype y1] [DecidableEq y1]
    [Fintype z1] [DecidableEq z1] [Fintype x2] [DecidableEq x2]
    [Fintype y2] [DecidableEq y2] [Fintype z2] [DecidableEq z2]
    (f : x1 → y1 → z1 → Complex) (g : x2 → y2 → z2 → Complex) :
    (∑ a1, ∑ b1, ∑ c1, f a1 b1 c1) *
        (∑ a2, ∑ b2, ∑ c2, g a2 b2 c2) =
      ∑ a1, ∑ a2, ∑ b1, ∑ b2, ∑ c1, ∑ c2,
        f a1 b1 c1 * g a2 b2 c2 := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a1 _ha1
  refine Finset.sum_congr rfl ?_
  intro a2 _ha2
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b1 _hb1
  refine Finset.sum_congr rfl ?_
  intro b2 _hb2
  rw [Finset.sum_mul_sum]

/-- For full-rank product `A`- and `C`-side weights, the KW `AC` trace matrix
of the product purification factors as the Kronecker product of the component
`AC` trace matrices.

This is the matrix factorization behind the middle equality in
`EA_capacity.tex:1201-1208`, before applying Schatten-norm multiplicativity. -/
theorem sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod_posDef
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    (htauC1 : tauC1.matrix.PosDef) (htauC2 : tauC2.matrix.PosDef)
    (alpha : Real) :
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
        (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha =
      Matrix.kronecker
        (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
        (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha) := by
  ext j j'
  rcases j with ⟨j1, j2⟩
  rcases j' with ⟨j1', j2'⟩
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  change _ =
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha j1 j1' *
      sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha j2 j2'
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [sandwichedMutualInformationACWeight_prod_posDef rhoA1 rhoA2 tauC1 tauC2
    hrhoA1 hrhoA2 htauC1 htauC2 alpha, bipartiteProductPurification_amp,
    star_mul]
  ring_nf
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i1 _hi1
  apply Finset.sum_congr rfl
  intro k1 _hk1
  rw [sum_three_mul_sum_three
    (f := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k) (i', k') *
        psi.amp ((i', j1), k') * star (psi.amp ((i1, j1'), k)))
    (g := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (k1, k) (i', k') *
        phi.amp ((i', j2), k') * star (phi.amp ((k1, j2'), k)))]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro x_1 _hx_1
  apply Finset.sum_congr rfl
  intro x_2 _hx_2
  apply Finset.sum_congr rfl
  intro x_3 _hx_3
  apply Finset.sum_congr rfl
  intro x_4 _hx_4
  apply Finset.sum_congr rfl
  intro x_5 _hx_5
  ring

/-- PSD-side version of the KW product-purification `AC` trace-matrix
factorization.

This is the same finite-sum source step as
`sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod_posDef`,
but with the `tau_C` powers justified by the nonnegative-exponent
Kronecker-power theorem. -/
theorem sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
        (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha =
      Matrix.kronecker
        (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
        (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha) := by
  ext j j'
  rcases j with ⟨j1, j2⟩
  rcases j' with ⟨j1', j2'⟩
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  change _ =
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha j1 j1' *
      sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha j2 j2'
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [sandwichedMutualInformationACWeight_prod rhoA1 rhoA2 tauC1 tauC2
    hrhoA1 hrhoA2 halpha, bipartiteProductPurification_amp, star_mul]
  ring_nf
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i1 _hi1
  apply Finset.sum_congr rfl
  intro k1 _hk1
  rw [sum_three_mul_sum_three
    (f := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k) (i', k') *
        psi.amp ((i', j1), k') * star (psi.amp ((i1, j1'), k)))
    (g := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (k1, k) (i', k') *
        phi.amp ((i', j2), k') * star (phi.amp ((k1, j2'), k)))]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro x_1 _hx_1
  apply Finset.sum_congr rfl
  intro x_2 _hx_2
  apply Finset.sum_congr rfl
  intro x_3 _hx_3
  apply Finset.sum_congr rfl
  intro x_4 _hx_4
  apply Finset.sum_congr rfl
  intro x_5 _hx_5
  ring

/-- Support-convention version of the KW product-purification `AC` trace-matrix
factorization.

This removes the full-rank assumptions on the source `A` marginals by using
the support-convention weight factorization above, while keeping the same
finite-sum identity from `EA_capacity.tex:1201-1208`. -/
theorem sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod_support
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    {alpha : Real} (halpha : 1 < alpha) :
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
        (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha =
      Matrix.kronecker
        (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
        (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha) := by
  ext j j'
  rcases j with ⟨j1, j2⟩
  rcases j' with ⟨j1', j2'⟩
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  change _ =
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha j1 j1' *
      sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha j2 j2'
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [sandwichedMutualInformationACWeight_prod_support rhoA1 rhoA2 tauC1 tauC2
    halpha, bipartiteProductPurification_amp, star_mul]
  ring_nf
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i1 _hi1
  apply Finset.sum_congr rfl
  intro k1 _hk1
  rw [sum_three_mul_sum_three
    (f := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k) (i', k') *
        psi.amp ((i', j1), k') * star (psi.amp ((i1, j1'), k)))
    (g := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (k1, k) (i', k') *
        phi.amp ((i', j2), k') * star (phi.amp ((k1, j2'), k)))]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro x_1 _hx_1
  apply Finset.sum_congr rfl
  intro x_2 _hx_2
  apply Finset.sum_congr rfl
  intro x_3 _hx_3
  apply Finset.sum_congr rfl
  intro x_4 _hx_4
  apply Finset.sum_congr rfl
  intro x_5 _hx_5
  ring

/-- Schatten-norm multiplicativity for the KW product-purification `AC` trace
matrix.

This is the norm step in `EA_capacity.tex:1208` after the product purification
and product side-information restriction have made the `AC` trace matrix a
Kronecker product. -/
theorem psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod_posDef
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    (htauC1 : tauC1.matrix.PosDef) (htauC2 : tauC2.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
          (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef
          (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
          (tauC1.prod tauC2) alpha)
        (alpha / (2 * alpha - 1)) =
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
          (alpha / (2 * alpha - 1)) *
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
          (alpha / (2 * alpha - 1)) := by
  let matrixProd : CMatrix (Prod b1 b2) :=
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
      (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha
  let matrixLeft : CMatrix b1 :=
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha
  let matrixRight : CMatrix b2 :=
    sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha
  let hmatrixProd : matrixProd.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef
      (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
      (tauC1.prod tauC2) alpha
  let hmatrixLeft : matrixLeft.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha
  let hmatrixRight : matrixRight.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha
  have hmat : matrixProd = Matrix.kronecker matrixLeft matrixRight := by
    simpa [matrixProd, matrixLeft, matrixRight] using
      sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod_posDef
        rhoA1 rhoA2 psi phi tauC1 tauC2 hrhoA1 hrhoA2 htauC1 htauC2 alpha
  calc
    psdSchattenPNorm matrixProd hmatrixProd (alpha / (2 * alpha - 1))
        = psdSchattenPNorm (Matrix.kronecker matrixLeft matrixRight)
            (hmatrixLeft.kronecker hmatrixRight)
            (alpha / (2 * alpha - 1)) := by
          exact psdSchattenPNorm_congr hmat hmatrixProd
            (hmatrixLeft.kronecker hmatrixRight) (alpha / (2 * alpha - 1))
    _ = psdSchattenPNorm matrixLeft hmatrixLeft (alpha / (2 * alpha - 1)) *
        psdSchattenPNorm matrixRight hmatrixRight (alpha / (2 * alpha - 1)) := by
          exact psdSchattenPNorm_kronecker hmatrixLeft hmatrixRight
            (sandwichedAlternateSchattenExponent_pos_lt_one halpha).1

/-- PSD-side Schatten-norm multiplicativity for the KW product-purification
`AC` trace matrix.

This is the all-side-state version needed after the state alternate expression
has been rewritten as a supremum over `tau_C` Schatten norms. -/
theorem psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
          (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef
          (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
          (tauC1.prod tauC2) alpha)
        (alpha / (2 * alpha - 1)) =
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
          (alpha / (2 * alpha - 1)) *
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
          (alpha / (2 * alpha - 1)) := by
  let matrixProd : CMatrix (Prod b1 b2) :=
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
      (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha
  let matrixLeft : CMatrix b1 :=
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha
  let matrixRight : CMatrix b2 :=
    sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha
  let hmatrixProd : matrixProd.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef
      (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
      (tauC1.prod tauC2) alpha
  let hmatrixLeft : matrixLeft.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha
  let hmatrixRight : matrixRight.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha
  have hmat : matrixProd = Matrix.kronecker matrixLeft matrixRight := by
    simpa [matrixProd, matrixLeft, matrixRight] using
      sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod
        rhoA1 rhoA2 psi phi tauC1 tauC2 hrhoA1 hrhoA2 halpha
  calc
    psdSchattenPNorm matrixProd hmatrixProd (alpha / (2 * alpha - 1))
        = psdSchattenPNorm (Matrix.kronecker matrixLeft matrixRight)
            (hmatrixLeft.kronecker hmatrixRight)
            (alpha / (2 * alpha - 1)) := by
          exact psdSchattenPNorm_congr hmat hmatrixProd
            (hmatrixLeft.kronecker hmatrixRight) (alpha / (2 * alpha - 1))
    _ = psdSchattenPNorm matrixLeft hmatrixLeft (alpha / (2 * alpha - 1)) *
        psdSchattenPNorm matrixRight hmatrixRight (alpha / (2 * alpha - 1)) := by
          exact psdSchattenPNorm_kronecker hmatrixLeft hmatrixRight
            (sandwichedAlternateSchattenExponent_pos_lt_one halpha).1

/-- Support-convention Schatten-norm multiplicativity for the KW
product-purification `AC` trace matrix.

This is the singular-state version of the norm factorization in
`EA_capacity.tex:1208`; the proof is the same Kronecker-product Schatten norm
step, fed by the support-convention trace-matrix identity. -/
theorem psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod_support
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    {alpha : Real} (halpha : 1 < alpha) :
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
          (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef
          (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
          (tauC1.prod tauC2) alpha)
        (alpha / (2 * alpha - 1)) =
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
          (alpha / (2 * alpha - 1)) *
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
          (alpha / (2 * alpha - 1)) := by
  let matrixProd : CMatrix (Prod b1 b2) :=
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
      (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha
  let matrixLeft : CMatrix b1 :=
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha
  let matrixRight : CMatrix b2 :=
    sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha
  let hmatrixProd : matrixProd.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef
      (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
      (tauC1.prod tauC2) alpha
  let hmatrixLeft : matrixLeft.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha
  let hmatrixRight : matrixRight.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha
  have hmat : matrixProd = Matrix.kronecker matrixLeft matrixRight := by
    simpa [matrixProd, matrixLeft, matrixRight] using
      sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod_support
        rhoA1 rhoA2 psi phi tauC1 tauC2 halpha
  calc
    psdSchattenPNorm matrixProd hmatrixProd (alpha / (2 * alpha - 1))
        = psdSchattenPNorm (Matrix.kronecker matrixLeft matrixRight)
            (hmatrixLeft.kronecker hmatrixRight)
            (alpha / (2 * alpha - 1)) := by
          exact psdSchattenPNorm_congr hmat hmatrixProd
            (hmatrixLeft.kronecker hmatrixRight) (alpha / (2 * alpha - 1))
    _ = psdSchattenPNorm matrixLeft hmatrixLeft (alpha / (2 * alpha - 1)) *
        psdSchattenPNorm matrixRight hmatrixRight (alpha / (2 * alpha - 1)) := by
          exact psdSchattenPNorm_kronecker hmatrixLeft hmatrixRight
            (sandwichedAlternateSchattenExponent_pos_lt_one halpha).1

/-- Log-additivity for the KW product-purification `AC` trace-matrix norm,
with the logarithm side conditions stated explicitly.

The positivity assumptions are discharged later from the full-rank side weights;
this lemma is only the scalar `log xy = log x + log y` step following
`EA_capacity.tex:1208`. -/
theorem sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_posDef_of_pos
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    (htauC1 : tauC1.matrix.PosDef) (htauC2 : tauC2.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha)
    (hM1pos :
      0 <
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
          (alpha / (2 * alpha - 1)))
    (hM2pos :
      0 <
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
          (alpha / (2 * alpha - 1))) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
              (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
              (tauC1.prod tauC2) alpha)
            (alpha / (2 * alpha - 1))) =
      alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
              (alpha / (2 * alpha - 1))) +
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
              (alpha / (2 * alpha - 1))) := by
  rw [psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod_posDef
    rhoA1 rhoA2 psi phi tauC1 tauC2 hrhoA1 hrhoA2 htauC1 htauC2 halpha]
  rw [log2_mul (ne_of_gt hM1pos) (ne_of_gt hM2pos)]
  ring

/-- Log-additivity for the KW product-purification `AC` trace-matrix norm on
the full-rank branch.

This discharges the positivity side conditions in
`sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_posDef_of_pos`
from the full-rank `A` and `C` side weights. -/
theorem sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_posDef
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (tauC1 : State c1) (tauC2 : State c2)
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    (htauC1 : tauC1.matrix.PosDef) (htauC2 : tauC2.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
              (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
              (tauC1.prod tauC2) alpha)
            (alpha / (2 * alpha - 1))) =
      alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
              (alpha / (2 * alpha - 1))) +
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
              (alpha / (2 * alpha - 1))) := by
  exact
    sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_posDef_of_pos
      rhoA1 rhoA2 psi phi tauC1 tauC2 hrhoA1 hrhoA2 htauC1 htauC2 halpha
      (psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA1 psi tauC1 hrhoA1 htauC1 halpha)
      (psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA2 phi tauC2 hrhoA2 htauC2 halpha)

/-- Supremum split for the KW product-purification `AC` trace-matrix
alternate expression on full-rank product purifying references.

This is the product-`tau` optimization step in `EA_capacity.tex:1208-1214`,
after the product purification has reduced the norm to a product and before the
remaining source closure removes the full-rank/product-domain restrictions. -/
theorem sandwichedACTraceMatrixLog_fullRankProduct_sSup_eq_add
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Nonempty c1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    [Fintype c2] [DecidableEq c2] [Nonempty c2]
    (rhoA1 : State a1) (rhoA2 : State a2)
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (hrhoA1 : rhoA1.matrix.PosDef) (hrhoA2 : rhoA2.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha)
    (hBdd1 :
      BddAbove (Set.range fun tauC1 : {tau : State c1 // tau.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA1 psi tauC1.1 alpha)
              (alpha / (2 * alpha - 1)))))
    (hBdd2 :
      BddAbove (Set.range fun tauC2 : {tau : State c2 // tau.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA2 phi tauC2.1 alpha)
              (alpha / (2 * alpha - 1))))) :
    sSup (Set.range fun
        p : {tau : State c1 // tau.matrix.PosDef} ×
            {tau : State c2 // tau.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
              (bipartiteProductPurification psi phi) (p.1.1.prod p.2.1) alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
              (p.1.1.prod p.2.1) alpha)
            (alpha / (2 * alpha - 1)))) =
      sSup (Set.range fun tauC1 : {tau : State c1 // tau.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA1 psi tauC1.1 alpha)
              (alpha / (2 * alpha - 1)))) +
      sSup (Set.range fun tauC2 : {tau : State c2 // tau.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA2 phi tauC2.1 alpha)
              (alpha / (2 * alpha - 1)))) := by
  let S1 := {tau : State c1 // tau.matrix.PosDef}
  let S2 := {tau : State c2 // tau.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed c1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed c2, State.maximallyMixed_posDef⟩⟩
  let f : S1 → Real := fun tauC1 =>
    alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1.1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1.1 alpha)
          (alpha / (2 * alpha - 1)))
  let g : S2 → Real := fun tauC2 =>
    alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2.1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2.1 alpha)
          (alpha / (2 * alpha - 1)))
  have hpoint :
      (fun p : S1 × S2 =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
                (bipartiteProductPurification psi phi) (p.1.1.prod p.2.1) alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
                (p.1.1.prod p.2.1) alpha)
              (alpha / (2 * alpha - 1)))) =
        (fun p : S1 × S2 => f p.1 + g p.2) := by
    funext p
    exact sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_posDef
      rhoA1 rhoA2 psi phi p.1.1 p.2.1 hrhoA1 hrhoA2 p.1.2 p.2.2 halpha
  rw [hpoint]
  exact real_sSup_range_prod_add_eq_add_sSup_range f g hBdd1 hBdd2

end PureVector

namespace State

variable {a : Type u1} {b : Type v1}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Fixed-candidate Schatten-norm form of the sandwiched mutual-information
definition on the supported PSD-reference branch.

This is the singular-reference version needed by KW's support convention: the
product reference `rho_A \otimes sigma_B` may be singular on the `A` side, but
as long as it supports `rho_AB`, the high-`alpha` branch is finite and the same
Schatten-norm logarithmic formula follows from the PSD-reference definition. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hSupport :
      Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix)
    {alpha : Real} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.marginalA.prod sigmaB).matrix alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (rhoAB.marginalA.prod sigmaB).pos alpha)
            alpha) : EReal) := by
  let ref : CMatrix (Prod a b) := (rhoAB.marginalA.prod sigmaB).matrix
  let href : ref.PosSemidef := by
    simpa [ref] using (rhoAB.marginalA.prod sigmaB).pos
  let inner : CMatrix (Prod a b) := sandwichedRenyiReferenceInner rhoAB ref alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rhoAB href alpha
  have htrace_pos :
      0 < psdTracePower inner hinner alpha := by
    simpa [inner, hinner, ref, href] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
        rhoAB href hSupport alpha
  have hlog :
      log2 (psdSchattenPNorm inner hinner alpha) =
        (1 / alpha) * log2 (psdTracePower inner hinner alpha) := by
    simpa [psdSchattenPNorm, inner, hinner] using
      log2_rpow_pos (x := psdTracePower inner hinner alpha) (y := 1 / alpha)
        htrace_pos
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    rhoAB href alpha hSupport]
  change (((1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) : Real) :
      EReal) =
    (((alpha / (alpha - 1)) * log2 (psdSchattenPNorm inner hinner alpha) : Real) :
      EReal)
  rw [hlog]
  congr 1
  field_simp [ne_of_gt (lt_trans zero_lt_one halpha), sub_ne_zero.mpr (ne_of_gt halpha)]

/-- Fixed-candidate Schatten-norm form for a full-rank side state, without
assuming the bipartite state or its left marginal is full rank.

This is the KW support-convention replacement for the older positive-definite
branch: a full-rank `sigma_B` makes `rho_A ⊗ sigma_B` support `rho_AB`, so the
high-`alpha` PSD-reference expression is finite and has the same Schatten-norm
form used in `EA_capacity.tex:1983-1986`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_side_posDef
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hsigmaB : sigmaB.matrix.PosDef) {alpha : Real} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.marginalA.prod sigmaB).matrix alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (rhoAB.marginalA.prod sigmaB).pos alpha)
            alpha) : EReal) := by
  exact sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
    rhoAB sigmaB
      (State.supports_marginalA_prod_of_side_posDef rhoAB sigmaB hsigmaB) halpha

/-- Full-rank side candidates are exactly the finite PSD-reference branch, with
no full-rank assumption on the bipartite state or its left marginal. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_highAlphaFinite_of_side_posDef
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hsigmaB : sigmaB.matrix.PosDef) {alpha : Real} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
        (rhoAB.marginalA.prod sigmaB).matrix (rhoAB.marginalA.prod sigmaB).pos alpha :
        EReal) := by
  have hsupport :
      Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix :=
    State.supports_marginalA_prod_of_side_posDef rhoAB sigmaB hsigmaB
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    rhoAB (rhoAB.marginalA.prod sigmaB).pos alpha hsupport]

/-- The unit-output high-`alpha` PSD-reference finite branch is zero. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_unit_one_eq_zero
    (alpha : ℝ) (_halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (State.unit : State PUnit.{1})
      (1 : CMatrix PUnit.{1}) Matrix.PosSemidef.one alpha = 0 := by
  have htrace :
      ((Matrix.trace ((State.unit.matrix : CMatrix PUnit.{1}) ^ alpha)).re) = 1 := by
    rw [show (State.unit.matrix : CMatrix PUnit.{1}) = 1 by rfl]
    rw [CFC.one_rpow]
    simp
  simp [sandwichedRenyiPSDReferenceHighAlphaFinite, sandwichedRenyiReferenceInner,
    psdTracePower, log2, CFC.one_rpow, htrace]

/-- Supported state-reference high-`alpha` finite candidates are nonnegative.

This is the support-convention version of the usual nonnegativity of
sandwiched Renyi divergence, obtained by applying the already proved supported
PSD-reference DPI to the terminal measurement channel. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_state_reference_supports
    (rho sigma : State a) (hSupport : Matrix.Supports rho.matrix sigma.matrix)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 ≤ sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma.matrix sigma.pos alpha := by
  let Phi : Channel a PUnit.{1} := terminalMeasureChannel a
  have hDPI :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supported
      rho sigma.pos Phi alpha halpha hSupport
  have hrhoPhi : Phi.applyState rho = State.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState rho
  have hsigmaPhiState : Phi.applyState sigma = State.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState sigma
  have hsigmaPhi : Phi.map sigma.matrix = (1 : CMatrix PUnit.{1}) := by
    have h := congrArg State.matrix hsigmaPhiState
    simpa [Phi, Channel.applyState, State.unit] using h
  have hzero :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Phi.applyState rho) (Phi.map sigma.matrix)
          (Phi.mapsPositive sigma.matrix sigma.pos) alpha = 0 := by
    simpa [hrhoPhi, hsigmaPhi] using
      sandwichedRenyiPSDReferenceHighAlphaFinite_unit_one_eq_zero alpha halpha
  linarith

/-- Every high-`alpha` side-information candidate is nonnegative.

On the supported branch this is the usual nonnegativity of sandwiched Renyi
divergence; on the unsupported branch the extended-real candidate is `+∞`.
This is the all-side-state nonnegativity needed to split the KW product
infimum without restricting to full-rank side states. -/
theorem sandwichedRenyiMutualInformationCandidateE_nonneg
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 ≤ rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  by_cases hSupport :
      Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix
  · have hfinite :
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
          (State.sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos alpha : EReal) := by
      rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
      rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
      rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        rhoAB (rhoAB.marginalA.prod sigmaB).pos alpha hSupport]
    rw [hfinite]
    exact_mod_cast
      State.sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_state_reference_supports
        rhoAB (rhoAB.marginalA.prod sigmaB) hSupport halpha
  · rw [State.sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
      rhoAB sigmaB halpha hSupport]
    exact le_top

/-- Fixed product side-information candidates are additive on the supported
high-`alpha` branch.

This is the support-convention version of KW
`EA_capacity.tex:1177-1186`: no full-rank hypothesis is imposed on the
bipartite states, their left marginals, or the side states.  The hypotheses are
exactly the support-convention branch of the extended sandwiched divergence:
the product reference supports the product state and each factor reference
supports its factor state. -/
theorem sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    (sigma1 : State b1) (sigma2 : State b2)
    (hsupportProd :
      Matrix.Supports (xi.bipartiteProduct omega).matrix
        ((xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2)).matrix)
    (hsupport1 :
      Matrix.Supports xi.matrix (xi.marginalA.prod sigma1).matrix)
    (hsupport2 :
      Matrix.Supports omega.matrix (omega.marginalA.prod sigma2).matrix)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
        (sigma1.prod sigma2) alphaR =
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR +
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR := by
  let ref1 : State (Prod a1 b1) := xi.marginalA.prod sigma1
  let ref2 : State (Prod a2 b2) := omega.marginalA.prod sigma2
  have hleft :
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
          (sigma1.prod sigma2) alphaR =
        (State.sandwichedRenyiPSDReferenceHighAlphaFinite (xi.prod omega)
          (ref1.prod ref2).matrix (ref1.prod ref2).pos alphaR : EReal) := by
    let e := State.bipartiteProductEquiv (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2)
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (xi.bipartiteProduct omega)
      ((xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2)).pos
      alphaR hsupportProd]
    change
      (State.sandwichedRenyiPSDReferenceHighAlphaFinite
          ((xi.prod omega).reindex e)
          (((xi.prod omega).reindex e).marginalA.prod (sigma1.prod sigma2)).matrix
          (((xi.prod omega).reindex e).marginalA.prod (sigma1.prod sigma2)).pos alphaR :
        EReal) =
        (State.sandwichedRenyiPSDReferenceHighAlphaFinite (xi.prod omega)
          (ref1.prod ref2).matrix (ref1.prod ref2).pos alphaR : EReal)
    have hrefState :
        ((xi.prod omega).reindex e).marginalA.prod (sigma1.prod sigma2) =
          (ref1.prod ref2).reindex e := by
      simpa [e, State.bipartiteProduct, ref1, ref2] using
        State.bipartiteProduct_candidateReference xi omega sigma1 sigma2
    have hfiniteRef :
        State.sandwichedRenyiPSDReferenceHighAlphaFinite
            ((xi.prod omega).reindex e)
            (((xi.prod omega).reindex e).marginalA.prod (sigma1.prod sigma2)).matrix
            (((xi.prod omega).reindex e).marginalA.prod (sigma1.prod sigma2)).pos alphaR =
          State.sandwichedRenyiPSDReferenceHighAlphaFinite
            ((xi.prod omega).reindex e)
            ((ref1.prod ref2).reindex e).matrix
            ((ref1.prod ref2).reindex e).pos alphaR := by
      exact congrArg
        (fun tau : State (Prod (Prod a1 a2) (Prod b1 b2)) =>
          State.sandwichedRenyiPSDReferenceHighAlphaFinite
            ((xi.prod omega).reindex e) tau.matrix tau.pos alphaR)
        hrefState
    rw [hfiniteRef]
    simpa [e, State.bipartiteProduct, State.reindex_matrix, ref1, ref2] using
      congrArg (fun x : ℝ => (x : EReal))
        (State.sandwichedRenyiPSDReferenceHighAlphaFinite_reindex_stateReference
          (rho := xi.prod omega) (sigma := ref1.prod ref2) (e := e) alphaR)
  have hright1 :
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR =
        (State.sandwichedRenyiPSDReferenceHighAlphaFinite xi ref1.matrix ref1.pos alphaR :
          EReal) := by
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      xi ref1.pos alphaR hsupport1]
  have hright2 :
      omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR =
        (State.sandwichedRenyiPSDReferenceHighAlphaFinite omega ref2.matrix ref2.pos alphaR :
          EReal) := by
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      omega ref2.pos alphaR hsupport2]
  rw [hleft, hright1, hright2]
  have hprodFinite :=
    State.sandwichedRenyiPSDReferenceHighAlphaFinite_prod_of_supports
      xi omega (sigma1 := ref1.matrix) (sigma2 := ref2.matrix)
      ref1.pos ref2.pos hsupport1 hsupport2 halpha
  rw [← EReal.coe_add]
  exact congrArg (fun x : ℝ => (x : EReal)) (by
    simpa [ref1, ref2, State.prod_matrix_kronecker] using hprodFinite)

/-- Fixed product side-information candidates are additive for full-rank side
states.

This is a corollary of
`sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports`;
the positive-definite side states only discharge the support-convention
premises. -/
theorem sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
        (sigma1.prod sigma2) alphaR =
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR +
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR := by
  have hsigmaProd : (sigma1.prod sigma2).matrix.PosDef :=
    State.prod_posDef hsigma1 hsigma2
  exact
    State.sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports
      xi omega sigma1 sigma2
      (State.supports_marginalA_prod_of_side_posDef
        (xi.bipartiteProduct omega) (sigma1.prod sigma2) hsigmaProd)
      (by
        simpa using
          State.supports_marginalA_prod_of_side_posDef xi sigma1 hsigma1)
      (by
        simpa using
          State.supports_marginalA_prod_of_side_posDef omega sigma2 hsigma2)
      halpha

/-- Product side-information candidates are subadditive for all side states.

This is the pointwise KW product-candidate step without full-rank side-state
restriction.  If both factor support conventions hold, the fixed-candidate
equality applies.  If either factor is unsupported, the right-hand side is
`+∞`, so the inequality is automatic. -/
theorem sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_le
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    (sigma1 : State b1) (sigma2 : State b2)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
        (sigma1.prod sigma2) alphaR ≤
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR +
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR := by
  by_cases hsupport1 :
      Matrix.Supports xi.matrix (xi.marginalA.prod sigma1).matrix
  · by_cases hsupport2 :
        Matrix.Supports omega.matrix (omega.marginalA.prod sigma2).matrix
    · have hsupportProd :
          Matrix.Supports (xi.bipartiteProduct omega).matrix
            ((xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2)).matrix :=
        State.bipartiteProduct_candidateReference_supports_of_supports
          xi omega sigma1 sigma2 hsupport1 hsupport2
      rw [State.sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports
        xi omega sigma1 sigma2 hsupportProd hsupport1 hsupport2 halpha]
    · rw [State.sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
        omega sigma2 halpha hsupport2]
      have hxi_ne_bot :
          xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR ≠ ⊥ :=
        ne_bot_of_gt (EReal.bot_lt_zero.trans_le
          (State.sandwichedRenyiMutualInformationCandidateE_nonneg xi sigma1 halpha))
      rw [EReal.add_top_of_ne_bot hxi_ne_bot]
      exact le_top
  · rw [State.sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
      xi sigma1 halpha hsupport1]
    have homega_ne_bot :
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR ≠ ⊥ :=
      ne_bot_of_gt (EReal.bot_lt_zero.trans_le
        (State.sandwichedRenyiMutualInformationCandidateE_nonneg omega sigma2 halpha))
    rw [EReal.top_add_of_ne_bot homega_ne_bot]
    exact le_top

/-- Optimized state sandwiched-Renyi mutual information is subadditive on
bipartite product states, without any full-rank hypothesis on the states.

This is the completed `≤` half of KW `EA_capacity.tex:1177-1191`: restrict the
optimization to product side states, split the fixed-candidate value
pointwise, and separate the independent infimum directly in the extended-real
all-side-state objective. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProduct_le_add
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    [Nonempty b1] [Nonempty b2]
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha ≤
      xi.sandwichedRenyiMutualInformationE alpha +
        omega.sandwichedRenyiMutualInformationE alpha := by
  let f : State b1 → EReal := fun sigma1 =>
    xi.sandwichedRenyiMutualInformationCandidateE sigma1 alpha
  let g : State b2 → EReal := fun sigma2 =>
    omega.sandwichedRenyiMutualInformationCandidateE sigma2 alpha
  let prodF : State b1 × State b2 → EReal := fun p =>
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
      (p.1.prod p.2) alpha
  haveI : Nonempty (State b1) := ⟨State.maximallyMixed b1⟩
  haveI : Nonempty (State b2) := ⟨State.maximallyMixed b2⟩
  have hfNonneg : ∀ sigma1 : State b1, 0 ≤ f sigma1 := by
    intro sigma1
    exact State.sandwichedRenyiMutualInformationCandidateE_nonneg xi sigma1 halpha
  have hgNonneg : ∀ sigma2 : State b2, 0 ≤ g sigma2 := by
    intro sigma2
    exact State.sandwichedRenyiMutualInformationCandidateE_nonneg omega sigma2 halpha
  have hleft :
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha ≤
        sInf (Set.range prodF) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨p, rfl⟩
    exact
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE_le_candidate
        (p.1.prod p.2) alpha
  have hprodToSum :
      sInf (Set.range prodF) ≤
        sInf (Set.range fun p : State b1 × State b2 => f p.1 + g p.2) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨p, rfl⟩
    exact le_trans (sInf_le ⟨p, rfl⟩)
      (State.sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_le
        xi omega p.1 p.2 halpha)
  have hsplit :
      sInf (Set.range fun p : State b1 × State b2 => f p.1 + g p.2) =
        sInf (Set.range f) + sInf (Set.range g) :=
    ereal_sInf_range_prod_add_eq_add_sInf_range_nonneg f g hfNonneg hgNonneg
  have hxi :
      xi.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range f) := by
    rfl
  have homega :
      omega.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range g) := by
    rfl
  calc
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha ≤
        sInf (Set.range prodF) := hleft
    _ ≤ sInf (Set.range fun p : State b1 × State b2 => f p.1 + g p.2) :=
        hprodToSum
    _ = sInf (Set.range f) + sInf (Set.range g) := hsplit
    _ = xi.sandwichedRenyiMutualInformationE alpha +
          omega.sandwichedRenyiMutualInformationE alpha := by
        rw [hxi, homega]

/-- Fixed-candidate Schatten-norm form of the sandwiched mutual-information
definition when the product reference is positive definite.

This is the support-aware version of the positive-definite branch used in
KW `EA_capacity.tex:1983-1986`: the input state `rhoAB` may be singular, because
the full-rank product reference `rho_A \otimes sigma_B` supports it and the
PSD-reference high-`alpha` branch is finite. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_reference_posDef
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hA : rhoAB.marginalA.matrix.PosDef)
    (hsigma : sigmaB.matrix.PosDef) {alpha : Real} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.marginalA.prod sigmaB).matrix alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (State.prod_posDef hA hsigma).posSemidef alpha)
            alpha) : EReal) := by
  let ref : CMatrix (Prod a b) := (rhoAB.marginalA.prod sigmaB).matrix
  let hRef : ref.PosDef := by
    simpa [ref] using State.prod_posDef hA hsigma
  let inner : CMatrix (Prod a b) := sandwichedRenyiReferenceInner rhoAB ref alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rhoAB hRef.posSemidef alpha
  have htrace_pos :
      0 < psdTracePower inner hinner alpha := by
    simpa [inner, hinner, ref, hRef] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        rhoAB hRef alpha
  have hlog :
      log2 (psdSchattenPNorm inner hinner alpha) =
        (1 / alpha) * log2 (psdTracePower inner hinner alpha) := by
    simpa [psdSchattenPNorm, inner, hinner] using
      log2_rpow_pos (x := psdTracePower inner hinner alpha) (y := 1 / alpha)
        htrace_pos
  have hSupport : Matrix.Supports rhoAB.matrix ref :=
    Matrix.Supports.of_right_posDef rhoAB.matrix ref hRef
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha))]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    rhoAB hRef.posSemidef alpha hSupport]
  change (((1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) : Real) :
      EReal) =
    (((alpha / (alpha - 1)) * log2 (psdSchattenPNorm inner hinner alpha) : Real) :
      EReal)
  rw [hlog]
  congr 1
  field_simp [ne_of_gt (lt_trans zero_lt_one halpha), sub_ne_zero.mpr (ne_of_gt halpha)]

/-- Fixed-candidate Schatten-norm form of the sandwiched mutual-information
definition on the positive-definite branch.

This is the Lean fixed-reference version of
`EA_capacity.tex:1983-1986`, before optimizing over the side-information
state. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_posDef
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    (hsigma : sigmaB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.marginalA.prod sigmaB).matrix alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (State.prod_posDef hA hsigma).posSemidef alpha)
            alpha) : EReal) := by
  let ref : CMatrix (Prod a b) := (rhoAB.marginalA.prod sigmaB).matrix
  let inner : CMatrix (Prod a b) := sandwichedRenyiReferenceInner rhoAB ref alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rhoAB
      (State.prod_posDef hA hsigma).posSemidef alpha
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have halpha_ne : alpha ≠ 1 := ne_of_gt halpha
  have htrace_pos :
      0 < psdTracePower inner hinner alpha := by
    simpa [inner, hinner, ref] using
      sandwichedRenyiReferenceInner_psdTracePower_pos rhoAB hrho
        (State.prod_posDef hA hsigma) alpha
  have hlog :
      log2 (psdSchattenPNorm inner hinner alpha) =
        (1 / alpha) * log2 (psdTracePower inner hinner alpha) := by
    simpa [psdSchattenPNorm, inner, hinner] using
      log2_rpow_pos (x := psdTracePower inner hinner alpha) (y := 1 / alpha)
        htrace_pos
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB := rhoAB) (sigmaB := sigmaB) hrho hA hsigma halpha]
  rw [sandwichedRenyiReference_eq_log2_psdTracePower_inner
    rhoAB hrho (State.prod_posDef hA hsigma) alpha halpha_pos halpha_ne]
  change (((1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) : ℝ) :
      EReal) =
    ((alpha / (alpha - 1)) * log2 (psdSchattenPNorm inner hinner alpha) : ℝ)
  rw [hlog]
  congr 1
  field_simp [ne_of_gt halpha_pos, sub_ne_zero.mpr halpha_ne]

/-- Local-channel data processing for sandwiched mutual information on the
left system.

This is the KW data-processing step used by the purification/isometry bridge:
for each side state `sigmaB`, PSD-reference sandwiched-Renyi DPI compares the
candidate after `Phi ⊗ id` with the original candidate; taking the infimum over
`sigmaB` gives the optimized inequality. -/
theorem sandwichedRenyiMutualInformationE_dataProcessing_left
    {c : Type u2} [Fintype c] [DecidableEq c]
    (rhoAB : State (Prod a b)) (Phi : Channel a c)
    {alpha : Real} (halpha : 1 < alpha) :
    (((Phi.prod (Channel.idChannel b)).applyState rhoAB).sandwichedRenyiMutualInformationE
        alpha) ≤
      rhoAB.sandwichedRenyiMutualInformationE alpha := by
  classical
  let rhoOut : State (Prod c b) := (Phi.prod (Channel.idChannel b)).applyState rhoAB
  haveI : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
  refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  intro y hy
  rcases hy with ⟨sigmaB, rfl⟩
  have hOutLe :
      rhoOut.sandwichedRenyiMutualInformationE alpha ≤
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaB alpha :=
    rhoOut.sandwichedRenyiMutualInformationE_le_candidate sigmaB alpha
  have hRefState :
      (Phi.prod (Channel.idChannel b)).applyState (rhoAB.marginalA.prod sigmaB) =
        rhoOut.marginalA.prod sigmaB := by
    calc
      (Phi.prod (Channel.idChannel b)).applyState (rhoAB.marginalA.prod sigmaB) =
          (Phi.applyState rhoAB.marginalA).prod sigmaB := by
            exact State.applyState_prod_id_prod rhoAB.marginalA sigmaB Phi
      _ = rhoOut.marginalA.prod sigmaB := by
            have hmarg :
                rhoOut.marginalA = Phi.applyState rhoAB.marginalA := by
              simpa [rhoOut] using State.marginalA_applyState_prod_id rhoAB Phi
            rw [hmarg]
  have hRefMap :
      (Phi.prod (Channel.idChannel b)).map (rhoAB.marginalA.prod sigmaB).matrix =
        (rhoOut.marginalA.prod sigmaB).matrix := by
    simpa [Channel.applyState] using congrArg State.matrix hRefState
  have hDPI :
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha ≥
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq,
      State.sandwichedRenyiMutualInformationCandidateE_eq]
    have hbase :=
      sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
        rhoAB (rhoAB.marginalA.prod sigmaB).pos (Phi.prod (Channel.idChannel b))
        alpha (Or.inr halpha)
    simpa [rhoOut, hRefMap] using hbase
  exact hOutLe.trans hDPI

/-- Local-channel data processing for sandwiched mutual information on the
right system.

This is the right-register counterpart of
`sandwichedRenyiMutualInformationE_dataProcessing_left`.  The side-information
candidate is pushed forward by the channel, matching the product-reference
step in KW's purification/isometry reduction. -/
theorem sandwichedRenyiMutualInformationE_dataProcessing_right
    {c : Type u2} [Fintype c] [DecidableEq c]
    (rhoAB : State (Prod a b)) (Psi : Channel b c)
    {alpha : Real} (halpha : 1 < alpha) :
    (((Channel.idChannel a).prod Psi).applyState rhoAB).sandwichedRenyiMutualInformationE
        alpha ≤
      rhoAB.sandwichedRenyiMutualInformationE alpha := by
  classical
  let rhoOut : State (Prod a c) := ((Channel.idChannel a).prod Psi).applyState rhoAB
  haveI : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
  refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  intro y hy
  rcases hy with ⟨sigmaB, rfl⟩
  let sigmaC : State c := Psi.applyState sigmaB
  have hOutLe :
      rhoOut.sandwichedRenyiMutualInformationE alpha ≤
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaC alpha :=
    rhoOut.sandwichedRenyiMutualInformationE_le_candidate sigmaC alpha
  have hRefState :
      ((Channel.idChannel a).prod Psi).applyState (rhoAB.marginalA.prod sigmaB) =
        rhoOut.marginalA.prod sigmaC := by
    calc
      ((Channel.idChannel a).prod Psi).applyState (rhoAB.marginalA.prod sigmaB) =
          rhoAB.marginalA.prod (Psi.applyState sigmaB) := by
            exact State.applyState_id_prod_prod rhoAB.marginalA sigmaB Psi
      _ = rhoOut.marginalA.prod sigmaC := by
            have hmarg :
                rhoOut.marginalA = rhoAB.marginalA := by
              simpa [rhoOut] using State.marginalA_applyState_id_prod rhoAB Psi
            rw [hmarg]
  have hRefMap :
      ((Channel.idChannel a).prod Psi).map (rhoAB.marginalA.prod sigmaB).matrix =
        (rhoOut.marginalA.prod sigmaC).matrix := by
    simpa [Channel.applyState] using congrArg State.matrix hRefState
  have hDPI :
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha ≥
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaC alpha := by
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq,
      State.sandwichedRenyiMutualInformationCandidateE_eq]
    have hbase :=
      sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
        rhoAB (rhoAB.marginalA.prod sigmaB).pos ((Channel.idChannel a).prod Psi)
        alpha (Or.inr halpha)
    simpa [rhoOut, sigmaC, hRefMap] using hbase
  exact hOutLe.trans hDPI

end State

namespace PureVector

/-- Support-convention version of
`partialTraceB_rankOne_weightedPurificationAmp_eq_referenceInner`.

The matrix identity in KW `EA_capacity.tex:1989-1996` only uses the PSD
functional calculus support convention for the source weight
`rho_A^((1-alpha)/(2 alpha)) \otimes sigma_B^((1-alpha)/(2 alpha))`; it does
not require either factor to be full rank. -/
theorem partialTraceB_rankOne_weightedPurificationAmp_eq_referenceInner_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c)) (alpha : ℝ) :
    partialTraceB (a := Prod a b) (b := c)
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.marginalA σB ψ alpha)) =
      State.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.marginalA.prod σB).matrix alpha := by
  let W : CMatrix (Prod a b) :=
    sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha
  have hW :
      Matrix.conjTranspose W = W := by
    unfold W sandwichedMutualInformationABWeight
    exact (kronecker_isHermitian
      (CFC.rpow ψ.state.marginalAB.marginalA.matrix ((1 - alpha) / (2 * alpha)))
      (CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha)))
      (cMatrix_rpow_posSemidef
        (A := ψ.state.marginalAB.marginalA.matrix)
        (s := (1 - alpha) / (2 * alpha))
        ψ.state.marginalAB.marginalA.pos).isHermitian
      (cMatrix_rpow_posSemidef
        (A := σB.matrix)
        (s := (1 - alpha) / (2 * alpha))
        σB.pos).isHermitian).eq
  rw [partialTraceB_rankOne_weightedPurificationAmp_eq]
  unfold State.sandwichedRenyiReferenceInner
  rw [show (ψ.state.marginalAB.marginalA.prod σB).matrix =
      Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix from rfl]
  change sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha *
      partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
        Matrix.conjTranspose
          (sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha) =
    CFC.rpow (Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix)
        ((1 - alpha) / (2 * alpha)) *
      ψ.state.marginalAB.matrix *
      CFC.rpow (Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix)
        ((1 - alpha) / (2 * alpha))
  rw [State.cMatrix_rpow_kronecker_posSemidef_support
    ψ.state.marginalAB.marginalA.pos σB.pos ((1 - alpha) / (2 * alpha))]
  change W * partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
      Matrix.conjTranspose W =
    W * ψ.state.marginalAB.matrix * W
  rw [hW]
  rfl

/-- Support-convention Schatten-norm form of the KW weighted-purification
bridge.

This removes the historical full-rank assumptions from
`psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA`; the
matrix identity itself follows from the PSD support convention for real powers
and the complementary partial-trace Schatten-norm equality. -/
theorem psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (alpha : ℝ) {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.marginalA.prod σB).matrix alpha)
        (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
          (ψ.state.marginalAB.marginalA.prod σB).pos alpha)
        p =
      psdSchattenPNorm
        (partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.marginalA σB ψ alpha)))
        (partialTraceA_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.marginalA σB ψ alpha)))
        p := by
  let amp :=
    sandwichedMutualInformationWeightedPurificationAmp
      ψ.state.marginalAB.marginalA σB ψ alpha
  let hB : (partialTraceB (a := Prod a b) (b := c)
      (rankOneMatrix amp)).PosSemidef :=
    partialTraceB_posSemidef (rankOneMatrix_pos amp)
  let hRef :
      (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.marginalA.prod σB).matrix alpha).PosSemidef :=
    State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
      (ψ.state.marginalAB.marginalA.prod σB).pos alpha
  have hmatrix :
      partialTraceB (a := Prod a b) (b := c) (rankOneMatrix amp) =
        State.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.marginalA.prod σB).matrix alpha := by
    simpa [amp] using
      partialTraceB_rankOne_weightedPurificationAmp_eq_referenceInner_support σB ψ alpha
  have hnormB :
      psdSchattenPNorm (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix amp)) hB p =
        psdSchattenPNorm
          (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod σB).matrix alpha)
          hRef p :=
    psdSchattenPNorm_congr hmatrix hB hRef p
  have hBA :
      psdSchattenPNorm (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix amp)) hB p =
        psdSchattenPNorm
          (partialTraceA (a := Prod a b) (b := c) (rankOneMatrix amp))
          (partialTraceA_posSemidef (rankOneMatrix_pos amp)) p := by
    simpa [amp, hB] using
      psdSchattenPNorm_weightedPurification_partialTraceC_eq_partialTraceAB
        ψ.state.marginalAB.marginalA σB ψ alpha hp
  exact hnormB.symm.trans hBA

/-- Fixed-candidate sandwiched mutual information as the Schatten norm of the
`C`-side marginal of the KW weighted purification.

This combines the definition-level positive-reference formula with the
same-nonzero-eigenvalues step in KW `EA_capacity.tex:1983-2004`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_partialTraceA
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hσ : σB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (partialTraceA (a := Prod a b) (b := c)
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.marginalA σB ψ alpha)))
            (partialTraceA_posSemidef
              (rankOneMatrix_pos
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.marginalA σB ψ alpha)))
            alpha) : EReal) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_posDef
    (rhoAB := ψ.state.marginalAB) (sigmaB := σB) hAB hA hσ halpha]
  rw [psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA
    σB ψ hA hσ alpha halpha_pos]

/-- Support-convention fixed-candidate sandwiched mutual information as the
Schatten norm of the `C`-side marginal of the KW weighted purification.

This is the source-shaped replacement for the older positive-definite branch:
the side state `sigma_B` is full rank because the optimization is restricted to
that dense domain, but the bipartite state and its `A` marginal may be
singular. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_partialTraceA_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hσ : σB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (partialTraceA (a := Prod a b) (b := c)
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.marginalA σB ψ alpha)))
            (partialTraceA_posSemidef
              (rankOneMatrix_pos
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.marginalA σB ψ alpha)))
            alpha) : EReal) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_side_posDef
    (rhoAB := ψ.state.marginalAB) (sigmaB := σB) hσ halpha]
  rw [psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA_support
    σB ψ alpha halpha_pos]

/-- Holder variational form of the weighted-purification Schatten expression.

This is the Lean version of the first variational step in KW
`EA_capacity.tex:2006-2018`: after the rank-one purification reduction, the
positive `C`-side marginal's `alpha`-Schatten expression is the supremum over
the PSD Holder dual unit ball. -/
theorem weightedPurification_partialTraceA_schattenNorm_eq_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    let M : CMatrix c :=
      partialTraceA (a := Prod a b) (b := c)
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.marginalA σB ψ alpha))
    let hM : M.PosSemidef :=
      partialTraceA_posSemidef
        (rankOneMatrix_pos
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.marginalA σB ψ alpha))
    psdSchattenPNorm M hM alpha =
      sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA σB ψ alpha))
  exact
    (psdTraceHolderUnitBall_sSup_eq
      (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)).symm

/-- Fixed-side-information candidate in the Holder unit-ball form used before
the Sion exchange in KW `EA_capacity.tex:2006-2025`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hσ : σB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (sSup
            (psdTraceHolderUnitBallValueSet
              (partialTraceA (a := Prod a b) (b := c)
                (rankOneMatrix
                  (sandwichedMutualInformationWeightedPurificationAmp
                    ψ.state.marginalAB.marginalA σB ψ alpha)))
              (Real.conjExponent alpha))) : EReal) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA σB ψ alpha))
  rw [sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_partialTraceA
    σB ψ hAB hA hσ halpha]
  have hholder :
      psdSchattenPNorm M hM alpha =
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    exact weightedPurification_partialTraceA_schattenNorm_eq_holderUnitBall_sSup
      σB ψ halpha
  change
    ((alpha / (alpha - 1) * log2 (psdSchattenPNorm M hM alpha) : ℝ) : EReal) =
      ((alpha / (alpha - 1) *
        log2 (sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))) : ℝ) :
          EReal)
  rw [hholder]

/-- Support-convention fixed-side-information candidate in the Holder
unit-ball form used before the Sion exchange in KW
`EA_capacity.tex:2006-2025`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hσ : σB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (sSup
            (psdTraceHolderUnitBallValueSet
              (partialTraceA (a := Prod a b) (b := c)
                (rankOneMatrix
                  (sandwichedMutualInformationWeightedPurificationAmp
                    ψ.state.marginalAB.marginalA σB ψ alpha)))
              (Real.conjExponent alpha))) : EReal) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA σB ψ alpha))
  rw [sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_partialTraceA_of_side_posDef
    σB ψ hσ halpha]
  have hholder :
      psdSchattenPNorm M hM alpha =
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    exact weightedPurification_partialTraceA_schattenNorm_eq_holderUnitBall_sSup
      σB ψ halpha
  change
    ((alpha / (alpha - 1) * log2 (psdSchattenPNorm M hM alpha) : ℝ) : EReal) =
      ((alpha / (alpha - 1) *
        log2 (sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))) : ℝ) :
          EReal)
  rw [hholder]

/-- Real-valued full-rank candidate in the Holder unit-ball form used before
the Sion exchange in KW `EA_capacity.tex:2006-2025`.

This is the real branch of
`sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup`,
extracted so the optimized full-rank `inf` can be rewritten before the Sion
minimax exchange. -/
theorem sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hσ : σB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    State.sandwichedRenyiMutualInformationCandidateRealPosDef
        ψ.state.marginalAB σB hAB hA hσ alpha halpha =
      alpha / (alpha - 1) *
        log2
          (sSup
            (psdTraceHolderUnitBallValueSet
              (partialTraceA (a := Prod a b) (b := c)
                (rankOneMatrix
                  (sandwichedMutualInformationWeightedPurificationAmp
                    ψ.state.marginalAB.marginalA σB ψ alpha)))
              (Real.conjExponent alpha))) := by
  have hreal :=
    State.sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
      (rhoAB := ψ.state.marginalAB) (sigmaB := σB) hAB hA hσ halpha
  have hholder :=
    sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup
      σB ψ hAB hA hσ halpha
  exact EReal.coe_eq_coe_iff.mp (hreal.symm.trans hholder)

/-- Optimized state sandwiched-Renyi mutual information as the full-rank
side-reference infimum of the KW Holder unit-ball expression.

This is the source-shaped bridge between the repository definition
`inf_{sigma_B} D_alpha(rho_AB || rho_A ⊗ sigma_B)` and the first variational
form of KW `EA_capacity.tex:2006-2025`.  It is still before the Sion exchange
and before the reverse-Holder reduction to the `AC` trace-matrix norm. -/
theorem sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (partialTraceA (a := Prod a b) (b := c)
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal)) := by
  rw [State.sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
    ψ.state.marginalAB hAB hA halpha]
  have hfun :
      (fun σB : {σ : State b // σ.matrix.PosDef} =>
        (State.sandwichedRenyiMutualInformationCandidateRealPosDef
          ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha : EReal)) =
      (fun σB : {σ : State b // σ.matrix.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (partialTraceA (a := Prod a b) (b := c)
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal)) := by
    funext σB
    rw [sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
      σB.1 ψ hAB hA σB.2 halpha]
  rw [hfun]

/-- Support-convention optimized state sandwiched-Renyi mutual information as
the full-rank side-reference infimum of the KW Holder unit-ball expression.

This is the source-shaped variant of
`sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup`.
The full-rank restriction is only on the optimized side state `sigma_B`; the
input bipartite state and its `A` marginal are allowed to be singular, matching
the support convention in KW `EA_capacity.tex:2006-2025`. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf_fullRank_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ σB : {σ : State b // σ.matrix.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (partialTraceA (a := Prod a b) (b := c)
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal) := by
  rw [State.sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha
    ψ.state.marginalAB halpha]
  apply iInf_congr
  intro σB
  exact
    sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup_of_side_posDef
      σB.1 ψ σB.2 halpha

/-- For a fixed full-rank `sigma_B`, the Holder unit-ball supremum equals the
source supremum over purifying side states `tau_C`.

This is the exact equality form of KW `EA_capacity.tex:2010-2018`, combining
the two one-sided bridges already proved above. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (sigmaB : State b) (hrhoA : rhoA.matrix.PosDef) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun tauC : State c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) =
      sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha))
  let holder : ℝ := sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  have hupper :
      BddAbove (Set.range fun tauC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) := by
    refine ⟨holder, ?_⟩
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ sigmaB tauC hrhoA hsigmaB halpha
  haveI : Nonempty (State c) := ⟨State.maximallyMixed c⟩
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ sigmaB tauC hrhoA hsigmaB halpha
  · simpa [holder, M] using
      weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup
        rhoA ψ sigmaB hrhoA hsigmaB halpha

/-- Support-convention equality between the `tau_C`-optimized KW Sion bracket
and the Holder unit-ball supremum.

This is the source-shaped version of
`sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup`: the
fixed `rho_A` may be singular, and only the side state `sigma_B` is restricted
to the full-rank branch used for the dense side optimization. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun tauC : State c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) =
      sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha))
  let holder : ℝ := sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  have hupper :
      BddAbove (Set.range fun tauC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) := by
    refine ⟨holder, ?_⟩
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ sigmaB tauC hsigmaB halpha
  haveI : Nonempty (State c) := ⟨State.maximallyMixed c⟩
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ sigmaB tauC hsigmaB halpha
  · simpa [holder, M] using
      weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
        rhoA ψ sigmaB hsigmaB halpha

/-- The KW `tau_C`-optimized Sion bracket is strictly positive on a full-rank
`sigma_B` branch.

This is the positivity side condition for moving `log2` across the
`tau_C` supremum in the state alternate-expression proof. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_pos
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (sigmaB : State b)
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hsigmaB : sigmaB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    0 < sSup (Set.range fun tauC : State c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.marginalA ψ sigmaB tauC alpha) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA sigmaB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA sigmaB ψ alpha))
  have hholder_eq :
      sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) =
        psdSchattenPNorm M hM alpha := by
    exact psdTraceHolderUnitBall_sSup_eq
      (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)
  have href_pos :
      0 <
        psdTracePower
          (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod sigmaB).matrix alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (State.prod_posDef hA hsigmaB).posSemidef alpha)
          alpha :=
    State.sandwichedRenyiReferenceInner_psdTracePower_pos ψ.state.marginalAB hAB
      (State.prod_posDef hA hsigmaB) alpha
  have hnorm_pos :
      0 <
        psdSchattenPNorm
          (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod sigmaB).matrix alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (State.prod_posDef hA hsigmaB).posSemidef alpha)
          alpha := by
    unfold psdSchattenPNorm
    exact Real.rpow_pos_of_pos href_pos (1 / alpha)
  have hholder_pos :
      0 < sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    rw [hholder_eq]
    simpa [M, hM] using
      (hnorm_pos.trans_eq
        (psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA
          sigmaB ψ hA hsigmaB alpha (lt_trans zero_lt_one halpha)))
  have hsup_eq :=
    sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
      ψ.state.marginalAB.marginalA ψ sigmaB hA hsigmaB halpha
  rwa [hsup_eq]

/-- On each full-rank `sigma_B` branch, the KW `tau_C`-optimized raw bracket
is at least one.

This is the scalar consequence of nonnegativity of the corresponding
sandwiched-Renyi candidate, and it supplies the strict lower bound needed for
the `log2`/`sInf` transport in the alternate-expression proof. -/
theorem one_le_sandwichedMutualInformationSionBracketRe_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (sigmaB : State b)
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hsigmaB : sigmaB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    1 ≤ sSup (Set.range fun tauC : State c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.marginalA ψ sigmaB tauC alpha) := by
  let x : ℝ := sSup (Set.range fun tauC : State c =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.marginalA ψ sigmaB tauC alpha)
  have hxpos : 0 < x := by
    simpa [x] using
      sandwichedMutualInformationSionBracketRe_sSup_pos
        ψ sigmaB hAB hA hsigmaB halpha
  have hcandidate_nonneg :
      0 ≤ State.sandwichedRenyiMutualInformationCandidateRealPosDef
        ψ.state.marginalAB sigmaB hAB hA hsigmaB alpha halpha :=
    State.sandwichedRenyiMutualInformationCandidateRealPosDef_nonneg
      ψ.state.marginalAB sigmaB hAB hA hsigmaB halpha
  have hcandidate_eq :
      State.sandwichedRenyiMutualInformationCandidateRealPosDef
          ψ.state.marginalAB sigmaB hAB hA hsigmaB alpha halpha =
        alpha / (alpha - 1) * log2 x := by
    rw [sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
      sigmaB ψ hAB hA hsigmaB halpha]
    have hsup_eq :=
      sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
        ψ.state.marginalAB.marginalA ψ sigmaB hA hsigmaB halpha
    simpa [x] using congrArg (fun y : ℝ => alpha / (alpha - 1) * log2 y) hsup_eq.symm
  have hlog_nonneg : 0 ≤ log2 x := by
    have hmul : 0 ≤ alpha / (alpha - 1) * log2 x := by
      rw [hcandidate_eq] at hcandidate_nonneg
      exact hcandidate_nonneg
    have hmul' : 0 ≤ log2 x * (alpha / (alpha - 1)) := by
      simpa [mul_comm] using hmul
    exact nonneg_of_mul_nonneg_left hmul' (sandwichedCoeff_pos halpha)
  unfold log2 at hlog_nonneg
  have hlog_nonneg' : 0 ≤ Real.log x := by
    have hden_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    rcases (div_nonneg_iff.mp hlog_nonneg) with h | h
    · exact h.1
    · exact (not_le_of_gt hden_pos h.2).elim
  exact (Real.log_nonneg_iff hxpos).mp hlog_nonneg'

/-- Support-convention positivity of the KW `tau_C`-optimized Sion bracket on a
full-rank `sigma_B` branch.

The input bipartite state and its left marginal may be singular.  Positivity is
obtained from the supported PSD-reference branch for
`rho_AB || rho_A \otimes sigma_B`, using that a full-rank `sigma_B` supports the
side-information reference. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_pos_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < sSup (Set.range fun tauC : State c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.marginalA ψ sigmaB tauC alpha) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA sigmaB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.marginalA sigmaB ψ alpha))
  have hholder_eq :
      sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) =
        psdSchattenPNorm M hM alpha := by
    exact psdTraceHolderUnitBall_sSup_eq
      (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)
  have hsupport :
      Matrix.Supports ψ.state.marginalAB.matrix
        (ψ.state.marginalAB.marginalA.prod sigmaB).matrix :=
    State.supports_marginalA_prod_of_side_posDef ψ.state.marginalAB sigmaB hsigmaB
  have href_pos :
      0 <
        psdTracePower
          (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod sigmaB).matrix alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod sigmaB).pos alpha)
          alpha :=
    State.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
      ψ.state.marginalAB (ψ.state.marginalAB.marginalA.prod sigmaB).pos
      hsupport alpha
  have hnorm_pos :
      0 <
        psdSchattenPNorm
          (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod sigmaB).matrix alpha)
          (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod sigmaB).pos alpha)
          alpha := by
    unfold psdSchattenPNorm
    exact Real.rpow_pos_of_pos href_pos (1 / alpha)
  have hholder_pos :
      0 < sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    rw [hholder_eq]
    simpa [M, hM] using
      (hnorm_pos.trans_eq
        (psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA_support
          sigmaB ψ alpha (lt_trans zero_lt_one halpha)))
  have hsup_eq :=
    sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
      ψ.state.marginalAB.marginalA ψ sigmaB hsigmaB halpha
  rwa [hsup_eq]

/-- Support-convention scalar lower bound for the KW `tau_C`-optimized Sion
bracket on a full-rank `sigma_B` branch.

This is the no-full-support replacement for
`one_le_sandwichedMutualInformationSionBracketRe_sSup`; it is the scalar fact
needed to move `log2` through the full-rank side-reference infimum. -/
theorem one_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    1 ≤ sSup (Set.range fun tauC : State c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.marginalA ψ sigmaB tauC alpha) := by
  let x : ℝ := sSup (Set.range fun tauC : State c =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.marginalA ψ sigmaB tauC alpha)
  have hxpos : 0 < x := by
    simpa [x] using
      sandwichedMutualInformationSionBracketRe_sSup_pos_of_side_posDef
        ψ sigmaB hsigmaB halpha
  let finite : ℝ :=
    State.sandwichedRenyiPSDReferenceHighAlphaFinite ψ.state.marginalAB
      (ψ.state.marginalAB.marginalA.prod sigmaB).matrix
      (ψ.state.marginalAB.marginalA.prod sigmaB).pos alpha
  have hsupport :
      Matrix.Supports ψ.state.marginalAB.matrix
        (ψ.state.marginalAB.marginalA.prod sigmaB).matrix :=
    State.supports_marginalA_prod_of_side_posDef ψ.state.marginalAB sigmaB hsigmaB
  have hfinite_nonneg : 0 ≤ finite := by
    simpa [finite] using
      State.sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_state_reference_supports
        ψ.state.marginalAB (ψ.state.marginalAB.marginalA.prod sigmaB) hsupport halpha
  have hcandidate_finite :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        (finite : EReal) := by
    simpa [finite] using
      State.sandwichedRenyiMutualInformationCandidateE_eq_coe_highAlphaFinite_of_side_posDef
        ψ.state.marginalAB sigmaB hsigmaB halpha
  have hcandidate_holder :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        ((alpha / (alpha - 1) * log2 x : ℝ) : EReal) := by
    rw [sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup_of_side_posDef
      sigmaB ψ hsigmaB halpha]
    have hsup_eq :=
      sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
        ψ.state.marginalAB.marginalA ψ sigmaB hsigmaB halpha
    simpa [x] using congrArg
      (fun y : ℝ => ((alpha / (alpha - 1) * log2 y : ℝ) : EReal))
      hsup_eq.symm
  have hreal_eq : finite = alpha / (alpha - 1) * log2 x :=
    EReal.coe_eq_coe_iff.mp (hcandidate_finite.symm.trans hcandidate_holder)
  have hlog_nonneg : 0 ≤ log2 x := by
    have hmul : 0 ≤ alpha / (alpha - 1) * log2 x := by
      rwa [← hreal_eq]
    have hmul' : 0 ≤ log2 x * (alpha / (alpha - 1)) := by
      simpa [mul_comm] using hmul
    exact nonneg_of_mul_nonneg_left hmul' (sandwichedCoeff_pos halpha)
  unfold log2 at hlog_nonneg
  have hlog_nonneg' : 0 ≤ Real.log x := by
    have hden_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    rcases (div_nonneg_iff.mp hlog_nonneg) with h | h
    · exact h.1
    · exact (not_le_of_gt hden_pos h.2).elim
  exact (Real.log_nonneg_iff hxpos).mp hlog_nonneg'

/-- Equality version of the KW bridge from the optimized state quantity to the
full-rank `sigma_B` infimum of the `tau_C`-optimized Sion bracket. -/
theorem sandwichedRenyiMutualInformationE_eq_sInf_fullRank_sSup_sionBracketLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup (Set.range fun τC : State c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)) : ℝ) : EReal)) := by
  rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
    ψ hAB hA halpha]
  have hfun :
      (fun σB : {σ : State b // σ.matrix.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (partialTraceA (a := Prod a b) (b := c)
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal)) =
        (fun σB : {σ : State b // σ.matrix.PosDef} =>
          ((alpha / (alpha - 1) *
            log2
              (sSup (Set.range fun τC : State c =>
                sandwichedMutualInformationSionBracketRe
                  ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)) : ℝ) : EReal)) := by
    funext σB
    rw [sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
      ψ.state.marginalAB.marginalA ψ σB.1 hA σB.2 halpha]
  rw [hfun]

/-- Support-convention pointwise logarithmic bridge from the optimized state
quantity to the full-rank `sigma_B` infimum of the `tau_C`-optimized Sion
bracket.

Unlike the subsequent scalar transport theorem, this statement does not move
`log2` through the outer infimum.  It is therefore the exact safe API supplied
by the KW Holder/Sion variational step before proving the extra positivity and
boundedness needed for `log inf = inf log`. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf_fullRank_sSup_sionBracketLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ σB : {σ : State b // σ.matrix.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (sSup (Set.range fun τC : State c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_iInf_fullRank_holderUnitBall_sSup
    ψ halpha]
  apply iInf_congr
  intro σB
  rw [sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
    ψ.state.marginalAB.marginalA ψ σB.1 σB.2 halpha]

/-- Logarithmic scalar transport for the pre-Sion side of the KW state
alternate expression.

After the Holder variational equality, the optimized state quantity is the
positive coefficient times the logarithm of the raw `inf_sigma sup_tau`
Sion bracket. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
            sSup (Set.range fun τC : State c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.marginalA ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  let S := {σ : State b // σ.matrix.PosDef}
  let raw : S → State c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.marginalA ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : State c => raw σB τC)
  let coeff : ℝ := alpha / (alpha - 1)
  let logs : S → ℝ := fun σB => log2 (supRaw σB)
  let scaled : S → ℝ := fun σB => coeff * logs σB
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hsup_one (σB : S) : 1 ≤ supRaw σB := by
    simpa [supRaw, raw] using
      one_le_sandwichedMutualInformationSionBracketRe_sSup
        ψ σB.1 hAB hA σB.2 halpha
  have hsup_bddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨1, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsup_one σB
  have hsup_inf_pos : 0 < sInf (Set.range supRaw) := by
    exact zero_lt_one.trans_le (le_csInf (Set.range_nonempty supRaw) (by
      rintro y ⟨σB, rfl⟩
      exact hsup_one σB))
  have hlogs_sInf :
      sInf (Set.range logs) = log2 (sInf (Set.range supRaw)) := by
    have himage : Set.range logs = log2 '' Set.range supRaw := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨supRaw σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty supRaw)
      hsup_bddBelow hsup_inf_pos]
  have hlogs_nonneg (σB : S) : 0 ≤ logs σB := by
    unfold logs log2
    have hxpos : 0 < supRaw σB := zero_lt_one.trans_le (hsup_one σB)
    have hxlog : 0 ≤ Real.log (supRaw σB) :=
      (Real.log_nonneg_iff hxpos).mpr (hsup_one σB)
    exact div_nonneg hxlog (le_of_lt (Real.log_pos one_lt_two))
  have hscaled_bddBelow : BddBelow (Set.range scaled) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact mul_nonneg (le_of_lt (sandwichedCoeff_pos halpha)) (hlogs_nonneg σB)
  have hscaled_sInf :
      sInf (Set.range scaled) =
        coeff * log2 (sInf (Set.range supRaw)) := by
    have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
      simpa [coeff] using sandwichedCoeff_pos halpha)
    have himage :
        Set.range scaled = (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨logs σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨_, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨_, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨_, hy, hxy⟩
        exact ⟨_, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range scaled) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 (sInf (Set.range supRaw)) := by
            rw [hlogs_sInf]
  rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_sSup_sionBracketLog
    ψ hAB hA halpha]
  change sInf (Set.range fun σB : S => (scaled σB : EReal)) =
    ((coeff * log2 (sInf (Set.range supRaw)) : ℝ) : EReal)
  rw [ereal_sInf_range_coe_eq_coe_real_sInf scaled hscaled_bddBelow]
  rw [hscaled_sInf]

/-- Support-convention logarithmic scalar transport for the pre-Sion side of the
KW state alternate expression.

This is the no-full-support version of
`sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe`.
It uses the supported full-rank side-candidate branch, so neither the input
bipartite state nor its left marginal is assumed positive definite. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
            sSup (Set.range fun τC : State c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.marginalA ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  let S := {σ : State b // σ.matrix.PosDef}
  let raw : S → State c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.marginalA ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : State c => raw σB τC)
  let coeff : ℝ := alpha / (alpha - 1)
  let logs : S → ℝ := fun σB => log2 (supRaw σB)
  let scaled : S → ℝ := fun σB => coeff * logs σB
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hsup_one (σB : S) : 1 ≤ supRaw σB := by
    simpa [supRaw, raw] using
      one_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
        ψ σB.1 σB.2 halpha
  have hsup_bddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨1, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsup_one σB
  have hsup_inf_pos : 0 < sInf (Set.range supRaw) := by
    exact zero_lt_one.trans_le (le_csInf (Set.range_nonempty supRaw) (by
      rintro y ⟨σB, rfl⟩
      exact hsup_one σB))
  have hlogs_sInf :
      sInf (Set.range logs) = log2 (sInf (Set.range supRaw)) := by
    have himage : Set.range logs = log2 '' Set.range supRaw := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨supRaw σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty supRaw)
      hsup_bddBelow hsup_inf_pos]
  have hlogs_nonneg (σB : S) : 0 ≤ logs σB := by
    unfold logs log2
    have hxpos : 0 < supRaw σB := zero_lt_one.trans_le (hsup_one σB)
    have hxlog : 0 ≤ Real.log (supRaw σB) :=
      (Real.log_nonneg_iff hxpos).mpr (hsup_one σB)
    exact div_nonneg hxlog (le_of_lt (Real.log_pos one_lt_two))
  have hscaled_bddBelow : BddBelow (Set.range scaled) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact mul_nonneg (le_of_lt (sandwichedCoeff_pos halpha)) (hlogs_nonneg σB)
  have hscaled_sInf :
      sInf (Set.range scaled) =
        coeff * log2 (sInf (Set.range supRaw)) := by
    have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
      simpa [coeff] using sandwichedCoeff_pos halpha)
    have himage :
        Set.range scaled = (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨logs σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨_, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨_, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨_, hy, hxy⟩
        exact ⟨_, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range scaled) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 (sInf (Set.range supRaw)) := by
            rw [hlogs_sInf]
  rw [sandwichedRenyiMutualInformationE_eq_iInf_fullRank_sSup_sionBracketLog
    ψ halpha]
  change sInf (Set.range fun σB : S => (scaled σB : EReal)) =
    ((coeff * log2 (sInf (Set.range supRaw)) : ℝ) : EReal)
  rw [ereal_sInf_range_coe_eq_coe_real_sInf scaled hscaled_bddBelow]
  rw [hscaled_sInf]

/-- Real-valued form of the full-rank Sion exchange for the KW sandwiched
mutual-information bracket. -/
theorem sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (hrhoA : rhoA.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
      sSup (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) =
      sSup (Set.range fun τC : State c =>
        sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
          sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) := by
  let S := {σ : State b // σ.matrix.PosDef}
  let raw : S → State c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : State c => raw σB τC)
  let infRaw : State c → ℝ := fun τC => sInf (Set.range fun σB : S => raw σB τC)
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty (State c) := ⟨State.maximallyMixed c⟩
  have hrawBddAbove (σB : S) :
      BddAbove (Set.range fun τC : State c => raw σB τC) := by
    refine ⟨sSup
      (psdTraceHolderUnitBallValueSet
        (partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB.1 ψ alpha)))
        (Real.conjExponent alpha)), ?_⟩
    rintro y ⟨τC, rfl⟩
    simpa [raw] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ σB.1 τC hrhoA σB.2 halpha
  have hrawBddBelowSigma (τC : State c) :
      BddBelow (Set.range fun σB : S => raw σB τC) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hsupRaw_nonneg (σB : S) : 0 ≤ supRaw σB := by
    exact (sandwichedMutualInformationSionBracketRe_nonneg
      rhoA ψ σB.1 (State.maximallyMixed c) alpha).trans
        (le_csSup (hrawBddAbove σB)
          ⟨State.maximallyMixed c, by simp [raw]⟩)
  have hsupRawBddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsupRaw_nonneg σB
  have hinfRawBddAbove : BddAbove (Set.range infRaw) := by
    let σ0 : S := ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
    refine ⟨supRaw σ0, ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle_inf : infRaw τC ≤ raw σ0 τC := by
      exact csInf_le (hrawBddBelowSigma τC) ⟨σ0, rfl⟩
    have hle_sup : raw σ0 τC ≤ supRaw σ0 := by
      exact le_csSup (hrawBddAbove σ0) ⟨τC, rfl⟩
    exact hle_inf.trans hle_sup
  have hleftE :
      (⨅ σB : S, ⨆ τC : State c, (raw σB τC : EReal)) =
        ((sInf (Set.range supRaw) : ℝ) : EReal) := by
    calc
      (⨅ σB : S, ⨆ τC : State c, (raw σB τC : EReal))
          = ⨅ σB : S, (supRaw σB : EReal) := by
            apply iInf_congr
            intro σB
            exact ereal_sSup_range_coe_eq_coe_real_sSup
              (fun τC : State c => raw σB τC) (hrawBddAbove σB)
      _ = ((sInf (Set.range supRaw) : ℝ) : EReal) := by
            exact ereal_sInf_range_coe_eq_coe_real_sInf supRaw hsupRawBddBelow
  have hrightE :
      (⨆ τC : State c, ⨅ σB : S, (raw σB τC : EReal)) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    calc
      (⨆ τC : State c, ⨅ σB : S, (raw σB τC : EReal))
          = ⨆ τC : State c, (infRaw τC : EReal) := by
            apply iSup_congr
            intro τC
            exact ereal_sInf_range_coe_eq_coe_real_sInf
              (fun σB : S => raw σB τC) (hrawBddBelowSigma τC)
      _ = ((sSup (Set.range infRaw) : ℝ) : EReal) := by
            exact ereal_sSup_range_coe_eq_coe_real_sSup infRaw hinfRawBddAbove
  have hSion := sandwichedAlpha_fullRank_sion_mutualInformationBracket_EReal
    rhoA ψ halpha
  have hE :
      ((sInf (Set.range supRaw) : ℝ) : EReal) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    rw [← hleftE, ← hrightE]
    simpa [S, raw] using hSion
  exact EReal.coe_eq_coe_iff.mp hE

/-- Support-convention real-valued form of the full-rank Sion exchange for the
KW sandwiched mutual-information bracket.

This removes the old full-rank assumption on the fixed source marginal
`rho_A`.  The proof is the same EReal Sion wrapper as
`sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf`, with
the raw upper bound supplied by the support-convention Holder bridge. -/
theorem sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
      sSup (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) =
      sSup (Set.range fun τC : State c =>
        sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
          sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) := by
  let S := {σ : State b // σ.matrix.PosDef}
  let raw : S → State c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : State c => raw σB τC)
  let infRaw : State c → ℝ := fun τC => sInf (Set.range fun σB : S => raw σB τC)
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty (State c) := ⟨State.maximallyMixed c⟩
  have hrawBddAbove (σB : S) :
      BddAbove (Set.range fun τC : State c => raw σB τC) := by
    refine ⟨sSup
      (psdTraceHolderUnitBallValueSet
        (partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB.1 ψ alpha)))
        (Real.conjExponent alpha)), ?_⟩
    rintro y ⟨τC, rfl⟩
    simpa [raw] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ σB.1 τC σB.2 halpha
  have hrawBddBelowSigma (τC : State c) :
      BddBelow (Set.range fun σB : S => raw σB τC) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hsupRaw_nonneg (σB : S) : 0 ≤ supRaw σB := by
    exact (sandwichedMutualInformationSionBracketRe_nonneg
      rhoA ψ σB.1 (State.maximallyMixed c) alpha).trans
        (le_csSup (hrawBddAbove σB)
          ⟨State.maximallyMixed c, by simp [raw]⟩)
  have hsupRawBddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsupRaw_nonneg σB
  have hinfRawBddAbove : BddAbove (Set.range infRaw) := by
    let σ0 : S := ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
    refine ⟨supRaw σ0, ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle_inf : infRaw τC ≤ raw σ0 τC := by
      exact csInf_le (hrawBddBelowSigma τC) ⟨σ0, rfl⟩
    have hle_sup : raw σ0 τC ≤ supRaw σ0 := by
      exact le_csSup (hrawBddAbove σ0) ⟨τC, rfl⟩
    exact hle_inf.trans hle_sup
  have hleftE :
      (⨅ σB : S, ⨆ τC : State c, (raw σB τC : EReal)) =
        ((sInf (Set.range supRaw) : ℝ) : EReal) := by
    calc
      (⨅ σB : S, ⨆ τC : State c, (raw σB τC : EReal))
          = ⨅ σB : S, (supRaw σB : EReal) := by
            apply iInf_congr
            intro σB
            exact ereal_sSup_range_coe_eq_coe_real_sSup
              (fun τC : State c => raw σB τC) (hrawBddAbove σB)
      _ = ((sInf (Set.range supRaw) : ℝ) : EReal) := by
            exact ereal_sInf_range_coe_eq_coe_real_sInf supRaw hsupRawBddBelow
  have hrightE :
      (⨆ τC : State c, ⨅ σB : S, (raw σB τC : EReal)) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    calc
      (⨆ τC : State c, ⨅ σB : S, (raw σB τC : EReal))
          = ⨆ τC : State c, (infRaw τC : EReal) := by
            apply iSup_congr
            intro τC
            exact ereal_sInf_range_coe_eq_coe_real_sInf
              (fun σB : S => raw σB τC) (hrawBddBelowSigma τC)
      _ = ((sSup (Set.range infRaw) : ℝ) : EReal) := by
            exact ereal_sSup_range_coe_eq_coe_real_sSup infRaw hinfRawBddAbove
  have hSion := sandwichedAlpha_fullRank_sion_mutualInformationBracket_EReal
    rhoA ψ halpha
  have hE :
      ((sInf (Set.range supRaw) : ℝ) : EReal) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    rw [← hleftE, ← hrightE]
    simpa [S, raw] using hSion
  exact EReal.coe_eq_coe_iff.mp hE

/-- Post-Sion logarithmic form of the KW state alternate expression.

This combines the pre-Sion logarithmic transport with the source Sion exchange,
leaving only the fixed-`tau_C` reverse-Holder replacement of the inner
`sigma_B` infimum. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : State c =>
            sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.marginalA ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe
    ψ hAB hA halpha]
  rw [sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf
    ψ.state.marginalAB.marginalA ψ hA halpha]

/-- Support-convention post-Sion logarithmic form of the KW state alternate
expression. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : State c =>
            sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.marginalA ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe_support
    ψ halpha]
  rw [sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf_of_side_posDef
    ψ.state.marginalAB.marginalA ψ halpha]

/-- Reverse-Holder replacement of the post-Sion inner infimum in the KW state
alternate expression.

This is the source formula after `EA_capacity.tex:2030-2035`, before deciding
whether to state the final `tau_C` optimization over all side states or the
full-rank dense subdomain used for logarithmic product splitting. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : State c =>
            psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix
                ψ.state.marginalAB.marginalA ψ τC alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                ψ.state.marginalAB.marginalA ψ τC alpha)
              (alpha / (2 * alpha - 1)))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe
    ψ hAB hA halpha]
  have hsets :
      Set.range (fun τC : State c =>
        sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
          sandwichedMutualInformationSionBracketRe
            ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)) =
        Set.range (fun τC : State c =>
          psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (alpha / (2 * alpha - 1))) := by
    ext x
    constructor
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.marginalA ψ τC halpha).symm⟩
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.marginalA ψ τC halpha⟩
  rw [hsets]

/-- Support-convention reverse-Holder replacement of the post-Sion inner
infimum in the KW state alternate expression.

This is the singular-state version of
`sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm`, matching
KW `EA_capacity.tex:1193-1214` and `2030-2035`. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : State c =>
            psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix
                ψ.state.marginalAB.marginalA ψ τC alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                ψ.state.marginalAB.marginalA ψ τC alpha)
              (alpha / (2 * alpha - 1)))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe_support
    ψ halpha]
  have hsets :
      Set.range (fun τC : State c =>
        sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
          sandwichedMutualInformationSionBracketRe
            ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)) =
        Set.range (fun τC : State c =>
          psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (alpha / (2 * alpha - 1))) := by
    ext x
    constructor
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.marginalA ψ τC halpha).symm⟩
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.marginalA ψ τC halpha⟩
  rw [hsets]

/-- The all-state `tau_C` norm branch in the KW alternate expression is
bounded above.

For a fixed full-rank `sigma_B`, reverse Holder identifies the norm with an
infimum over `sigma_B`, and the pointwise Sion bracket is bounded by the
Holder unit-ball supremum. -/
theorem psdSchattenPNorm_ACTraceMatrix_bddAbove
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (hrhoA : rhoA.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun τC : State c =>
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1))) := by
  let σ0 : {σ : State b // σ.matrix.PosDef} :=
    ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σ0.1 ψ alpha))
  let holder : ℝ :=
    sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  refine ⟨holder, ?_⟩
  rintro y ⟨τC, rfl⟩
  let raw : {σ : State b // σ.matrix.PosDef} → ℝ := fun σB =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  have hrawBelow : BddBelow (Set.range raw) := by
    refine ⟨0, ?_⟩
    rintro z ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hnorm_eq :
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (alpha / (2 * alpha - 1)) =
        sInf (Set.range raw) := by
    simpa [raw] using
      (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA ψ τC halpha).symm
  have hinf_le : sInf (Set.range raw) ≤ raw σ0 :=
    csInf_le hrawBelow ⟨σ0, rfl⟩
  have hraw_le_holder : raw σ0 ≤ holder := by
    simpa [raw, M, holder] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ σ0.1 τC hrhoA σ0.2 halpha
  change
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1)) ≤ holder
  rw [hnorm_eq]
  exact hinf_le.trans hraw_le_holder

/-- Support-convention boundedness of the all-state `tau_C` norm branch in the
KW alternate expression.

This is the same boundedness argument as
`psdSchattenPNorm_ACTraceMatrix_bddAbove`, but with the Holder upper bound
supplied by the support-convention branch.  It is the boundedness side
condition needed for the singular-state product lower bound in
`EA_capacity.tex:1193-1214`. -/
theorem psdSchattenPNorm_ACTraceMatrix_bddAbove_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun τC : State c =>
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1))) := by
  let σ0 : {σ : State b // σ.matrix.PosDef} :=
    ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σ0.1 ψ alpha))
  let holder : ℝ :=
    sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  refine ⟨holder, ?_⟩
  rintro y ⟨τC, rfl⟩
  let raw : {σ : State b // σ.matrix.PosDef} → ℝ := fun σB =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  have hrawBelow : BddBelow (Set.range raw) := by
    refine ⟨0, ?_⟩
    rintro z ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hnorm_eq :
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (alpha / (2 * alpha - 1)) =
        sInf (Set.range raw) := by
    simpa [raw] using
      (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA ψ τC halpha).symm
  have hinf_le : sInf (Set.range raw) ≤ raw σ0 :=
    csInf_le hrawBelow ⟨σ0, rfl⟩
  have hraw_le_holder : raw σ0 ≤ holder := by
    simpa [raw, M, holder] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ σ0.1 τC σ0.2 halpha
  change
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1)) ≤ holder
  rw [hnorm_eq]
  exact hinf_le.trans hraw_le_holder

/-- The support-convention `AC` trace-matrix norm branch has supremum at least
one.

This is the scalar positivity needed for the logarithmic product split in
KW `EA_capacity.tex:1208-1214`.  It follows from the full-rank side-state
support branch (`sup_tau >= 1`), the Sion exchange, and the reverse-Holder
identification of the post-Sion inner infimum with the `AC` Schatten norm. -/
theorem one_le_sSup_ACTraceMatrixNorm_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    1 ≤ sSup (Set.range fun τC : State c =>
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix
          ψ.state.marginalAB.marginalA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef
          ψ.state.marginalAB.marginalA ψ τC alpha)
        (alpha / (2 * alpha - 1))) := by
  let S := {σ : State b // σ.matrix.PosDef}
  let raw : S → State c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.marginalA ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : State c => raw σB τC)
  let infRaw : State c → ℝ := fun τC => sInf (Set.range fun σB : S => raw σB τC)
  let F : State c → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        ψ.state.marginalAB.marginalA ψ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        ψ.state.marginalAB.marginalA ψ τC alpha)
      (alpha / (2 * alpha - 1))
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hsup_one (σB : S) : 1 ≤ supRaw σB := by
    simpa [supRaw, raw] using
      one_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
        ψ σB.1 σB.2 halpha
  have hsion :
      sInf (Set.range supRaw) = sSup (Set.range infRaw) := by
    simpa [supRaw, infRaw, raw, S] using
      sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf_of_side_posDef
        ψ.state.marginalAB.marginalA ψ halpha
  have hleft : 1 ≤ sInf (Set.range supRaw) := by
    refine le_csInf (Set.range_nonempty supRaw) ?_
    rintro y ⟨σB, rfl⟩
    exact hsup_one σB
  have hsets : Set.range infRaw = Set.range F := by
    ext x
    constructor
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.marginalA ψ τC halpha).symm⟩
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.marginalA ψ τC halpha⟩
  rw [hsion, hsets] at hleft
  simpa [F] using hleft

/-- Product-purification lower bound from the KW all-state alternate
expression.

This is the missing reverse half of the state product argument on the
source-shaped purification branch: restrict the product-side `tau_C`
optimization to product states, use the `AC` trace-matrix product identity and
Schatten-norm multiplicativity, then split the logarithm of the product
supremum. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProductPurification_ge_add
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1] [Nonempty b1]
    [Fintype c1] [DecidableEq c1] [Nonempty c1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2] [Nonempty b2]
    [Fintype c2] [DecidableEq c2] [Nonempty c2]
    (ψ : PureVector (Prod (Prod a1 b1) c1))
    (φ : PureVector (Prod (Prod a2 b2) c2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha +
        φ.state.marginalAB.sandwichedRenyiMutualInformationE alpha ≤
      (bipartiteProductPurification ψ φ).state.marginalAB.sandwichedRenyiMutualInformationE
        alpha := by
  let Fψ : State c1 → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        ψ.state.marginalAB.marginalA ψ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        ψ.state.marginalAB.marginalA ψ τC alpha)
      (alpha / (2 * alpha - 1))
  let Fφ : State c2 → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        φ.state.marginalAB.marginalA φ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        φ.state.marginalAB.marginalA φ τC alpha)
      (alpha / (2 * alpha - 1))
  let ψφ := bipartiteProductPurification ψ φ
  let rhoProdA : State (Prod a1 a2) :=
    ψ.state.marginalAB.marginalA.prod φ.state.marginalAB.marginalA
  let Fprod : State (Prod c1 c2) → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        rhoProdA ψφ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        rhoProdA ψφ τC alpha)
      (alpha / (2 * alpha - 1))
  have hψφA :
      ψφ.state.marginalAB.marginalA =
        ψ.state.marginalAB.marginalA.prod φ.state.marginalAB.marginalA := by
    dsimp [ψφ]
    exact bipartiteProductPurification_marginalA ψ φ
  have hψφA_unfolded :
      ψφ.state.marginalA.marginalA =
        ψ.state.marginalA.marginalA.prod φ.state.marginalA.marginalA := by
    simpa using hψφA
  have hFψBdd : BddAbove (Set.range Fψ) := by
    simpa [Fψ] using
      psdSchattenPNorm_ACTraceMatrix_bddAbove_support
        ψ.state.marginalAB.marginalA ψ halpha
  have hFφBdd : BddAbove (Set.range Fφ) := by
    simpa [Fφ] using
      psdSchattenPNorm_ACTraceMatrix_bddAbove_support
        φ.state.marginalAB.marginalA φ halpha
  have hFprodBdd : BddAbove (Set.range Fprod) := by
    simpa [Fprod, ψφ] using
      psdSchattenPNorm_ACTraceMatrix_bddAbove_support
        rhoProdA ψφ halpha
  have hFψ_nonneg : ∀ τC : State c1, 0 ≤ Fψ τC := by
    intro τC
    exact psdSchattenPNorm_nonneg _ _ _
  have hFφ_nonneg : ∀ τC : State c2, 0 ≤ Fφ τC := by
    intro τC
    exact psdSchattenPNorm_nonneg _ _ _
  have hFψ_sup_pos : 0 < sSup (Set.range Fψ) := by
    exact zero_lt_one.trans_le (by
      simpa [Fψ] using one_le_sSup_ACTraceMatrixNorm_support ψ halpha)
  have hFφ_sup_pos : 0 < sSup (Set.range Fφ) := by
    exact zero_lt_one.trans_le (by
      simpa [Fφ] using one_le_sSup_ACTraceMatrixNorm_support φ halpha)
  haveI : Nonempty (State c1) := ⟨State.maximallyMixed c1⟩
  haveI : Nonempty (State c2) := ⟨State.maximallyMixed c2⟩
  let Fpair : State c1 × State c2 → ℝ := fun p => Fψ p.1 * Fφ p.2
  have hFpairBdd : BddAbove (Set.range Fpair) := by
    refine ⟨sSup (Set.range Fprod), ?_⟩
    rintro y ⟨p, rfl⟩
    have hpoint : Fprod (p.1.prod p.2) = Fpair p := by
      dsimp [Fprod, Fpair, Fψ, Fφ, rhoProdA]
      exact
        psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod_support
          ψ.state.marginalAB.marginalA φ.state.marginalAB.marginalA
          ψ φ p.1 p.2 halpha
    exact le_csSup hFprodBdd ⟨p.1.prod p.2, by simp [hpoint]⟩
  have hFpair_log :
      log2 (sSup (Set.range Fpair)) =
        log2 (sSup (Set.range Fψ)) + log2 (sSup (Set.range Fφ)) := by
    simpa [Fpair] using
      real_log2_sSup_range_prod_mul_eq_add_of_nonneg
        Fψ Fφ hFψ_nonneg hFφ_nonneg hFpairBdd hFψ_sup_pos hFφ_sup_pos
  have hFpair_le_prod : sSup (Set.range Fpair) ≤ sSup (Set.range Fprod) := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨p, rfl⟩
    have hpoint : Fprod (p.1.prod p.2) = Fpair p := by
      dsimp [Fprod, Fpair, Fψ, Fφ, rhoProdA]
      exact
        psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod_support
          ψ.state.marginalAB.marginalA φ.state.marginalAB.marginalA
          ψ φ p.1 p.2 halpha
    exact le_csSup hFprodBdd ⟨p.1.prod p.2, by simp [hpoint]⟩
  have hFpair_pos : 0 < sSup (Set.range Fpair) := by
    rw [real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg
      Fψ Fφ hFψ_nonneg hFφ_nonneg hFpairBdd]
    exact mul_pos hFψ_sup_pos hFφ_sup_pos
  have hlog_le :
      log2 (sSup (Set.range Fψ)) + log2 (sSup (Set.range Fφ)) ≤
        log2 (sSup (Set.range Fprod)) := by
    rw [← hFpair_log]
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hFpair_pos hFpair_le_prod)
      (le_of_lt (Real.log_pos one_lt_two))
  have hψ :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((alpha / (alpha - 1) * log2 (sSup (Set.range Fψ)) : ℝ) : EReal) := by
    simpa [Fψ] using
      sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        ψ halpha
  have hφ :
      φ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((alpha / (alpha - 1) * log2 (sSup (Set.range Fφ)) : ℝ) : EReal) := by
    simpa [Fφ] using
      sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        φ halpha
  have hprod :
      ψφ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((alpha / (alpha - 1) * log2 (sSup (Set.range Fprod)) : ℝ) : EReal) := by
    simpa [Fprod, rhoProdA, hψφA_unfolded] using
      sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        ψφ halpha
  rw [hψ, hφ, hprod]
  rw [← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr
    (by
      have hcoeff_nonneg : 0 ≤ alpha / (alpha - 1) :=
        le_of_lt (sandwichedCoeff_pos halpha)
      nlinarith [mul_le_mul_of_nonneg_left hlog_le hcoeff_nonneg])

/-- KW `EA_capacity.tex:2010-2018`: after the Holder unit-ball variational
formula, each full-rank `sigma_B` branch is bounded by optimizing the source
Sion bracket over purifying states `tau_C`.

This is the source-shaped bridge from `inf_sigma sup_B` to
`inf_sigma sup_tau`.  It deliberately stops before the Sion exchange/removal of
the compact full-support regularization. -/
theorem sandwichedRenyiMutualInformationE_le_sInf_fullRank_sSup_sionBracketLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha ≤
      sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup (Set.range fun τC : State c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)) : ℝ) : EReal)) := by
  let S := {σ : State b // σ.matrix.PosDef}
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  let holder : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2
        (sSup
          (psdTraceHolderUnitBallValueSet
            (partialTraceA (a := Prod a b) (b := c)
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
            (Real.conjExponent alpha)))
  let bracket : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2
        (sSup (Set.range fun τC : State c =>
          sandwichedMutualInformationSionBracketRe
            ψ.state.marginalAB.marginalA ψ σB.1 τC alpha))
  have hpoint : ∀ σB : S, holder σB ≤ bracket σB := by
    intro σB
    let M : CMatrix c :=
      partialTraceA (a := Prod a b) (b := c)
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.marginalA σB.1 ψ alpha))
    let hM : M.PosSemidef :=
      partialTraceA_posSemidef
        (rankOneMatrix_pos
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.marginalA σB.1 ψ alpha))
    have hholder_eq :
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) =
          psdSchattenPNorm M hM alpha := by
      exact psdTraceHolderUnitBall_sSup_eq
        (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
        (Real.HolderConjugate.conjExponent halpha)
    have hholder_pos :
        0 < sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
      rw [hholder_eq]
      have href_pos :
          0 <
            psdTracePower
              (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
                (ψ.state.marginalAB.marginalA.prod σB.1).matrix alpha)
              (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
                (State.prod_posDef hA σB.2).posSemidef alpha)
              alpha :=
        State.sandwichedRenyiReferenceInner_psdTracePower_pos ψ.state.marginalAB hAB
          (State.prod_posDef hA σB.2) alpha
      have hnorm_pos :
          0 <
            psdSchattenPNorm
              (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
                (ψ.state.marginalAB.marginalA.prod σB.1).matrix alpha)
              (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
                (State.prod_posDef hA σB.2).posSemidef alpha)
              alpha := by
        unfold psdSchattenPNorm
        exact Real.rpow_pos_of_pos href_pos (1 / alpha)
      simpa [M, hM] using
        (hnorm_pos.trans_eq
          (psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA
            σB.1 ψ hA σB.2 alpha (lt_trans zero_lt_one halpha)))
    have hle :
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) ≤
          sSup (Set.range fun τC : State c =>
            sandwichedMutualInformationSionBracketRe
              ψ.state.marginalAB.marginalA ψ σB.1 τC alpha) := by
      simpa [M] using
        weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup
          ψ.state.marginalAB.marginalA ψ σB.1 hA σB.2 halpha
    have hlog :
        log2 (sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))) ≤
          log2 (sSup (Set.range fun τC : State c =>
            sandwichedMutualInformationSionBracketRe
              ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)) := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hholder_pos hle)
        (le_of_lt (Real.log_pos one_lt_two))
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt (sandwichedCoeff_pos halpha))
  have hfBelow : BddBelow (Set.range holder) := by
    have hfCandidate :
        BddBelow (Set.range fun σB : S =>
          State.sandwichedRenyiMutualInformationCandidateRealPosDef
            ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha) := by
      simpa [S] using
        State.sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
          ψ.state.marginalAB hAB hA halpha
    have hholder_eq_candidate :
        holder =
          (fun σB : S =>
            State.sandwichedRenyiMutualInformationCandidateRealPosDef
              ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha) := by
      funext σB
      simpa [holder] using
        (sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
          σB.1 ψ hAB hA σB.2 halpha).symm
    simpa [hholder_eq_candidate] using hfCandidate
  have hgBelow : BddBelow (Set.range bracket) := by
    rcases hfBelow with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact (hC ⟨σB, rfl⟩).trans (hpoint σB)
  have hinf_le : sInf (Set.range holder) ≤ sInf (Set.range bracket) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨σB, rfl⟩
    exact (csInf_le hfBelow ⟨σB, rfl⟩).trans (hpoint σB)
  have hstate :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range holder) : ℝ) : EReal) := by
    rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
      ψ hAB hA halpha]
    change sInf (Set.range fun σB : S => (holder σB : EReal)) =
      ((sInf (Set.range holder) : ℝ) : EReal)
    exact ereal_sInf_range_coe_eq_coe_real_sInf holder hfBelow
  rw [hstate]
  change ((sInf (Set.range holder) : ℝ) : EReal) ≤
    sInf (Set.range fun σB : S => (bracket σB : EReal))
  rw [ereal_sInf_range_coe_eq_coe_real_sInf bracket hgBelow]
  exact EReal.coe_le_coe_iff.mpr hinf_le

/-- A fixed full-rank `tau_C` value in the KW `AC` trace-matrix alternate
expression is bounded above by the optimized state sandwiched-Renyi mutual
information.

This is the one-sided closure obtained by following
KW `EA_capacity.tex:2006-2035`: Holder variational form, Sion bracket, and
reverse Holder.  It does not replace the remaining equality/approximation
direction of the full alternate-expression lemma. -/
theorem sandwichedACTraceMatrixLog_le_sandwichedRenyiMutualInformationE_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c)
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hτC : τC.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ((alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix
            ψ.state.marginalAB.marginalA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef
            ψ.state.marginalAB.marginalA ψ τC alpha)
          (alpha / (2 * alpha - 1))) : ℝ) : EReal) ≤
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha := by
  let S := {σ : State b // σ.matrix.PosDef}
  let acLog : ℝ :=
    alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix
            ψ.state.marginalAB.marginalA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef
            ψ.state.marginalAB.marginalA ψ τC alpha)
          (alpha / (2 * alpha - 1)))
  let f : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2 (sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.marginalA ψ σB.1 τC alpha)
  let g : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2
        (sSup
          (psdTraceHolderUnitBallValueSet
            (partialTraceA (a := Prod a b) (b := c)
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
            (Real.conjExponent alpha)))
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hAC_le_f (σB : S) : acLog ≤ f σB := by
    simpa [acLog, f, S] using
      sandwichedACTraceMatrixLog_le_SionBracketLog_posDef
        ψ.state.marginalAB.marginalA ψ σB.1 τC hA σB.2 hτC halpha
  have hf_le_g (σB : S) : f σB ≤ g σB := by
    let bracket :=
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.marginalA ψ σB.1 τC alpha
    let holder :=
      sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp
                ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
          (Real.conjExponent alpha))
    have hnorm_pos :
        0 <
          psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (alpha / (2 * alpha - 1)) := by
      simpa using
        psdSchattenPNorm_ACTraceMatrix_pos_posDef
          ψ.state.marginalAB.marginalA ψ τC hA hτC halpha
    have hnorm_le_bracket :
        psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.marginalA ψ τC alpha)
            (alpha / (2 * alpha - 1)) ≤ bracket := by
      simpa [bracket] using
        psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
          ψ.state.marginalAB.marginalA ψ σB.1 τC halpha
          (Matrix.Supports.of_right_posDef
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC alpha)
            σB.1.matrix σB.2)
    have hbracket_pos : 0 < bracket := lt_of_lt_of_le hnorm_pos hnorm_le_bracket
    have hbracket_le_holder : bracket ≤ holder := by
      simpa [bracket, holder] using
        sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
          ψ.state.marginalAB.marginalA ψ σB.1 τC hA σB.2 halpha
    have hlog_le : log2 bracket ≤ log2 holder := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hbracket_pos hbracket_le_holder)
        (le_of_lt (Real.log_pos one_lt_two))
    exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt (sandwichedCoeff_pos halpha))
  have hfBelow : BddBelow (Set.range f) := by
    refine ⟨acLog, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hAC_le_f σB
  have hgBelow : BddBelow (Set.range g) := by
    refine ⟨acLog, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact (hAC_le_f σB).trans (hf_le_g σB)
  have hAC_le_inf_f : acLog ≤ sInf (Set.range f) := by
    exact le_csInf (Set.range_nonempty _) (by
      rintro y ⟨σB, rfl⟩
      exact hAC_le_f σB)
  have hinf_f_le_inf_g : sInf (Set.range f) ≤ sInf (Set.range g) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨σB, rfl⟩
    exact (csInf_le hfBelow ⟨σB, rfl⟩).trans (hf_le_g σB)
  have hAC_le_inf_g : acLog ≤ sInf (Set.range g) :=
    hAC_le_inf_f.trans hinf_f_le_inf_g
  have hstate :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range g) : ℝ) : EReal) := by
    rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
      ψ hAB hA halpha]
    have hgfun :
        (fun σB : S => (g σB : EReal)) =
          (fun σB : {σ : State b // σ.matrix.PosDef} =>
            ((alpha / (alpha - 1) *
              log2
                (sSup
                  (psdTraceHolderUnitBallValueSet
                    (partialTraceA (a := Prod a b) (b := c)
                      (rankOneMatrix
                        (sandwichedMutualInformationWeightedPurificationAmp
                          ψ.state.marginalAB.marginalA σB.1 ψ alpha)))
                    (Real.conjExponent alpha))) : ℝ) : EReal)) := by
      funext σB
      rfl
    change sInf (Set.range fun σB : S => (g σB : EReal)) =
      ((sInf (Set.range g) : ℝ) : EReal)
    exact ereal_sInf_range_coe_eq_coe_real_sInf g hgBelow
  rw [hstate]
  exact EReal.coe_le_coe_iff.mpr hAC_le_inf_g

/-- The KW `AC` trace-matrix logarithmic objective over full-rank purifying
side states is bounded above by a real number.

The bound is obtained from the already source-shaped direction
`ACLog tau_C <= I~_alpha(A;B)` and the full-rank real branch of the
state sandwiched-Renyi mutual information. -/
theorem sandwichedACTraceMatrixLog_fullRank_bddAbove
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun τC : {τ : State c // τ.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC.1 alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.marginalA ψ τC.1 alpha)
            (alpha / (2 * alpha - 1)))) := by
  let S := {σ : State b // σ.matrix.PosDef}
  haveI : Nonempty S := ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
  let f : S → ℝ := fun σB =>
    State.sandwichedRenyiMutualInformationCandidateRealPosDef
      ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha
  have hfBelow : BddBelow (Set.range f) := by
    simpa [S, f] using
      State.sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
        ψ.state.marginalAB hAB hA halpha
  have hstate :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range f) : ℝ) : EReal) := by
    rw [State.sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
      ψ.state.marginalAB hAB hA halpha]
    exact ereal_sInf_range_coe_eq_coe_real_sInf f hfBelow
  refine ⟨sInf (Set.range f), ?_⟩
  rintro y ⟨τC, rfl⟩
  have hleE :=
    sandwichedACTraceMatrixLog_le_sandwichedRenyiMutualInformationE_posDef
      ψ τC.1 hAB hA τC.2 halpha
  rw [hstate] at hleE
  exact EReal.coe_le_coe_iff.mp hleE

/-- The full-rank `tau_C` AC-log supremum can be moved through the real-to-`EReal`
coercion once the source-shaped upper bound above is available. -/
theorem sandwichedACTraceMatrixLog_fullRank_ereal_sSup_eq
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun τC : {τ : State c // τ.matrix.PosDef} =>
      ((alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC.1 alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.marginalA ψ τC.1 alpha)
            (alpha / (2 * alpha - 1))) : ℝ) : EReal)) =
      ((sSup (Set.range fun τC : {τ : State c // τ.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix
                ψ.state.marginalAB.marginalA ψ τC.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                ψ.state.marginalAB.marginalA ψ τC.1 alpha)
              (alpha / (2 * alpha - 1)))) : ℝ) : EReal) := by
  haveI : Nonempty {τ : State c // τ.matrix.PosDef} :=
    ⟨⟨State.maximallyMixed c, State.maximallyMixed_posDef⟩⟩
  exact ereal_sSup_range_coe_eq_coe_real_sSup _
    (sandwichedACTraceMatrixLog_fullRank_bddAbove ψ hAB hA halpha)

/-- The already-proved KW direction after optimizing the full-rank `tau_C`
side of the alternate expression.  This is one half of the pending state
alternate-expression equality. -/
theorem sandwichedACTraceMatrixLog_fullRank_sSup_le_sandwichedRenyiMutualInformationE
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hAB : ψ.state.marginalAB.matrix.PosDef)
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun τC : {τ : State c // τ.matrix.PosDef} =>
      ((alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.marginalA ψ τC.1 alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.marginalA ψ τC.1 alpha)
            (alpha / (2 * alpha - 1))) : ℝ) : EReal)) ≤
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha := by
  haveI : Nonempty {τ : State c // τ.matrix.PosDef} :=
    ⟨⟨State.maximallyMixed c, State.maximallyMixed_posDef⟩⟩
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨τC, rfl⟩
  exact sandwichedACTraceMatrixLog_le_sandwichedRenyiMutualInformationE_posDef
    ψ τC.1 hAB hA τC.2 halpha

end PureVector

namespace State

/-- Swapping the canonical purification of a bipartite state puts the purified
`AB` system in the left factor, so the `marginalAB` used by the KW
alternate-expression lemmas is the original state. -/
theorem canonicalPurification_swap_marginalAB
    {a : Type u1} {b : Type v1}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoAB : State (Prod a b)) :
    ((rhoAB.canonicalPurification.reindex
        (Equiv.prodComm (Prod a b) (Prod a b))).state.marginalAB) = rhoAB := by
  apply State.ext
  ext x y
  have hpur := rhoAB.canonicalPurification_purifies
  simpa [State.marginalAB_eq_marginalA, PureVector.reindex_state, State.reindex,
    State.marginalA, partialTraceA, partialTraceB] using
      congrFun (congrFun hpur x) y

/-- Swapping the canonical purification of a state puts the purified system in
the left factor, so its `marginalA` is the original state.

This is the finite-dimensional Lean form of the KW channel alternate-expression
step where the polar-decomposition reference state `tau_R` is recovered from
`(sqrt tau_R \otimes I_A)|Gamma⟩`. -/
theorem canonicalPurification_reindex_prodComm_marginalA
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : State a) :
    (rho.canonicalPurification.reindex (Equiv.prodComm a a)).state.marginalA = rho := by
  apply State.ext
  ext i j
  have hp : partialTraceA (a := a) (b := a)
      rho.canonicalPurification.state.matrix = rho.matrix := by
    exact PureVector.partialTraceA_state_matrix_eq_of_purifies
      rho.canonicalPurification_purifies
  have hpij := congrFun (congrFun hp i) j
  simpa [State.marginalA, partialTraceB, partialTraceA,
    PureVector.reindex_state, State.reindex] using hpij

/-- The reference marginal of the unswapped canonical purification is the
transpose of the purified state.

This is the matrix bookkeeping behind the KW polar-decomposition route: a
full-rank input marginal also gives a full-rank reference marginal for the
canonical purification, up to transpose. -/
theorem canonicalPurification_marginalA_matrix
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : State a) :
    rho.canonicalPurification.state.marginalA.matrix = rho.matrix.transpose := by
  ext i j
  change (∑ k : a, rho.sqrtMatrix k i * star (rho.sqrtMatrix k j)) =
    rho.matrix.transpose i j
  rw [Matrix.transpose_apply]
  rw [← rho.sqrtMatrix_mul_self, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [rho.sqrtMatrix_isHermitian.apply j k]
  ring

/-- Full-rank states have full-rank reference marginals in their unswapped
canonical purifications. -/
theorem canonicalPurification_marginalA_posDef
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : State a)
    (hrho : rho.matrix.PosDef) :
    rho.canonicalPurification.state.marginalA.matrix.PosDef := by
  rw [canonicalPurification_marginalA_matrix rho]
  exact hrho.transpose

/-- Square-root matrices vary continuously along PSD state paths. -/
theorem sqrtMatrix_tendsto_of_tendsto
    {a : Type u1} [Fintype a] [DecidableEq a]
    {X : Type*} {l : Filter X} {rhoF : X → State a} {rho : State a}
    (hrhoF : Filter.Tendsto rhoF l (nhds rho)) :
    Filter.Tendsto (fun x : X => (rhoF x).sqrtMatrix) l
      (nhds rho.sqrtMatrix) := by
  have hmatrix :
      Filter.Tendsto (fun x : X => (rhoF x).matrix) l (nhds rho.matrix) :=
    State.continuous_matrix.tendsto rho |>.comp hrhoF
  have hpsd : ∀ᶠ x in l, (rhoF x).matrix.PosSemidef :=
    Filter.Eventually.of_forall fun x => (rhoF x).pos
  have hpow :=
    _root_.QIT.cMatrix_rpow_tendsto_of_tendsto_posSemidef
      (a := a) (p := (1 / 2 : ℝ)) (by norm_num)
      hmatrix hpsd rho.pos
  simpa [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow] using hpow

/-- Canonical purifications vary continuously with the purified state.

This is the local topological bridge needed in the KW full-rank approximation
step: after regularizing the input marginal, its canonical purification
converges back to the original canonical purification. -/
theorem canonicalPurification_tendsto_of_tendsto
    {a : Type u1} [Fintype a] [DecidableEq a]
    {X : Type*} {l : Filter X} {rhoF : X → State a} {rho : State a}
    (hrhoF : Filter.Tendsto rhoF l (nhds rho)) :
    Filter.Tendsto (fun x : X => (rhoF x).canonicalPurification) l
      (nhds rho.canonicalPurification) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  change
    Filter.Tendsto
      (fun x : X => fun p : Prod a a => (rhoF x).sqrtMatrix p.2 p.1)
      l
      (nhds (fun p : Prod a a => rho.sqrtMatrix p.2 p.1))
  refine tendsto_pi_nhds.mpr ?_
  intro p
  exact ((continuous_id.matrix_elem p.2 p.1).tendsto rho.sqrtMatrix).comp
    (sqrtMatrix_tendsto_of_tendsto hrhoF)

/-- KW support-convention power algebra for a possibly singular input state.

For `alpha > 1` and `s = (1 - alpha) / (2 * alpha)`, the source expression
`rho^s rho rho^s` is interpreted on the positive spectral support of `rho`;
after embedding back it is exactly `rho^(1 / alpha)`. -/
theorem rpow_sandwich_self_eq_rpow_one_div
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : State a)
    {alpha : ℝ} (halpha : 1 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    CFC.rpow rho.matrix s * rho.matrix * CFC.rpow rho.matrix s =
      CFC.rpow rho.matrix (1 / alpha) := by
  classical
  intro s
  let V : Matrix a (psdSupportIndex rho.matrix rho.pos) ℂ :=
    psdSupportIsometry rho.matrix rho.pos
  let rhoc : CMatrix (psdSupportIndex rho.matrix rho.pos) :=
    psdSupportCompress rho.matrix rho.pos rho.matrix
  let P : CMatrix (psdSupportIndex rho.matrix rho.pos) := CFC.rpow rhoc s
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    field_simp [ne_of_gt halpha_pos]
    linarith
  have hone_div_ne : (1 / alpha : ℝ) ≠ 0 := by
    exact one_div_ne_zero (ne_of_gt halpha_pos)
  have hV : Matrix.conjTranspose V * V =
      (1 : CMatrix (psdSupportIndex rho.matrix rho.pos)) := by
    simpa [V] using psdSupportIsometry_isometry rho.matrix rho.pos
  have hrec : V * rhoc * Matrix.conjTranspose V = rho.matrix := by
    simpa [V, rhoc] using psdSupportCompress_reconstruct_self rho.matrix rho.pos
  have hpow_s : V * P * Matrix.conjTranspose V = CFC.rpow rho.matrix s := by
    simpa [V, P, rhoc] using
      cMatrix_rpow_psdSupportCompress_reconstruct_self rho.matrix rho.pos hs_ne
  have hpow_one_div :
      V * CFC.rpow rhoc (1 / alpha) * Matrix.conjTranspose V =
        CFC.rpow rho.matrix (1 / alpha) := by
    simpa [V, rhoc] using
      cMatrix_rpow_psdSupportCompress_reconstruct_self
        rho.matrix rho.pos hone_div_ne
  have hRhoc : rhoc.PosDef := by
    simpa [rhoc] using psdSupportCompress_self_posDef rho.matrix rho.pos
  have hnonneg : 0 ≤ rhoc :=
    Matrix.nonneg_iff_posSemidef.mpr hRhoc.posSemidef
  have hpow_one : CFC.rpow rhoc (1 : ℝ) = rhoc :=
    CFC.rpow_one rhoc (ha := hnonneg)
  have hs_left :
      CFC.rpow rhoc s * rhoc = CFC.rpow rhoc (s + 1) := by
    calc
      CFC.rpow rhoc s * rhoc =
          CFC.rpow rhoc s * CFC.rpow rhoc (1 : ℝ) := by
            rw [hpow_one]
      _ = CFC.rpow rhoc (s + 1) := by
            exact (CFC.rpow_add (a := rhoc) (x := s) (y := 1) hRhoc.isUnit).symm
  have hs_total :
      CFC.rpow rhoc (s + 1) * CFC.rpow rhoc s =
        CFC.rpow rhoc ((s + 1) + s) := by
    exact (CFC.rpow_add (a := rhoc) (x := s + 1) (y := s) hRhoc.isUnit).symm
  have hexp : (s + 1) + s = 1 / alpha := by
    dsimp [s]
    field_simp [ne_of_gt halpha_pos]
    ring
  have hcompressed :
      P * rhoc * P = CFC.rpow rhoc (1 / alpha) := by
    calc
      P * rhoc * P =
          CFC.rpow rhoc s * rhoc * CFC.rpow rhoc s := by
            rfl
      _ = (CFC.rpow rhoc s * rhoc) * CFC.rpow rhoc s := by
            rw [Matrix.mul_assoc]
      _ = CFC.rpow rhoc (s + 1) * CFC.rpow rhoc s := by
            rw [hs_left]
      _ = CFC.rpow rhoc ((s + 1) + s) := hs_total
      _ = CFC.rpow rhoc (1 / alpha) := by rw [hexp]
  have houter :
      CFC.rpow rho.matrix s * rho.matrix * CFC.rpow rho.matrix s =
        (V * P * Matrix.conjTranspose V) * rho.matrix *
          (V * P * Matrix.conjTranspose V) := by
    exact congrArg (fun M : CMatrix a => M * rho.matrix * M) hpow_s.symm
  have hmiddle :
      (V * P * Matrix.conjTranspose V) * rho.matrix *
          (V * P * Matrix.conjTranspose V) =
        (V * P * Matrix.conjTranspose V) *
            (V * rhoc * Matrix.conjTranspose V) *
          (V * P * Matrix.conjTranspose V) := by
    exact congrArg
      (fun M : CMatrix a =>
        (V * P * Matrix.conjTranspose V) * M * (V * P * Matrix.conjTranspose V))
      hrec.symm
  calc
    CFC.rpow rho.matrix s * rho.matrix * CFC.rpow rho.matrix s =
        (V * P * Matrix.conjTranspose V) * rho.matrix *
          (V * P * Matrix.conjTranspose V) := houter
    _ =
        (V * P * Matrix.conjTranspose V) *
            (V * rhoc * Matrix.conjTranspose V) *
          (V * P * Matrix.conjTranspose V) := hmiddle
    _ = V * (P * rhoc * P) * Matrix.conjTranspose V := by
          calc
            (V * P * Matrix.conjTranspose V) *
                (V * rhoc * Matrix.conjTranspose V) *
              (V * P * Matrix.conjTranspose V) =
                V * P * (Matrix.conjTranspose V * V) * rhoc *
                  (Matrix.conjTranspose V * V) * P * Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
            _ = V * P * (1 : CMatrix (psdSupportIndex rho.matrix rho.pos)) * rhoc *
                  (1 : CMatrix (psdSupportIndex rho.matrix rho.pos)) *
                P * Matrix.conjTranspose V := by
              rw [hV]
            _ = V * (P * rhoc * P) * Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
    _ = V * CFC.rpow rhoc (1 / alpha) * Matrix.conjTranspose V := by
          rw [hcompressed]
    _ = CFC.rpow rho.matrix (1 / alpha) := hpow_one_div

/-- PSD version of the normalized interpolation endpoint
`Tr((rho^(1 / alpha))^alpha) = 1`.

Unlike the older full-rank endpoint lemma, this only uses the source
support-convention functional calculus for PSD states. -/
theorem state_rpow_one_div_psdTracePower_eq_one_psd
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : State a)
    {alpha : ℝ} (halpha_pos : 0 < alpha) :
    psdTracePower (CFC.rpow rho.matrix (1 / alpha))
        (rho.rpowMatrix_posSemidef (1 / alpha)) alpha = 1 := by
  have hrho_nonneg : 0 ≤ rho.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr rho.pos
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hone_div_nonneg : 0 ≤ 1 / alpha := by positivity
  have halpha_ne_zero : alpha ≠ 0 := ne_of_gt halpha_pos
  have hpow :
      CFC.rpow (CFC.rpow rho.matrix (1 / alpha)) alpha =
        CFC.rpow rho.matrix (1 : ℝ) := by
    calc
      CFC.rpow (CFC.rpow rho.matrix (1 / alpha)) alpha =
          CFC.rpow rho.matrix ((1 / alpha) * alpha) := by
            exact CFC.rpow_rpow_of_exponent_nonneg rho.matrix
              (1 / alpha) alpha hone_div_nonneg halpha_nonneg hrho_nonneg
      _ = CFC.rpow rho.matrix (1 : ℝ) := by
            congr 1
            field_simp [halpha_ne_zero]
  have hone : CFC.rpow rho.matrix (1 : ℝ) = rho.matrix :=
    CFC.rpow_one rho.matrix (ha := hrho_nonneg)
  rw [psdTracePower, hpow, hone, rho.trace_eq_one]
  norm_num

/-- PSD version of the normalized interpolation endpoint in Schatten-norm
form. -/
theorem state_rpow_one_div_psdSchattenPNorm_eq_one_psd
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : State a)
    {alpha : ℝ} (halpha_pos : 0 < alpha) :
    psdSchattenPNorm (CFC.rpow rho.matrix (1 / alpha))
        (rho.rpowMatrix_posSemidef (1 / alpha)) alpha = 1 := by
  rw [psdSchattenPNorm,
    state_rpow_one_div_psdTracePower_eq_one_psd rho halpha_pos]
  exact Real.one_rpow (1 / alpha)

/-- State-level lower-bound half of KW `EA_capacity.tex:1193-1217`.

This is the support-convention version of the product-state argument: purify
both states canonically, restrict the post-Sion `tau_C` optimization to product
states, and use the `AC` trace-matrix product factorization.  No full-rank
hypothesis is imposed on the bipartite states or their marginals. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProduct_ge_add
    {a1 b1 a2 b2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    xi.sandwichedRenyiMutualInformationE alpha +
        omega.sandwichedRenyiMutualInformationE alpha ≤
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha := by
  haveI : Nonempty (Prod a1 b1) := xi.nonempty
  haveI : Nonempty a1 := ⟨(Classical.choice (xi.nonempty)).1⟩
  haveI : Nonempty b1 := ⟨(Classical.choice (xi.nonempty)).2⟩
  haveI : Nonempty (Prod a2 b2) := omega.nonempty
  haveI : Nonempty a2 := ⟨(Classical.choice (omega.nonempty)).1⟩
  haveI : Nonempty b2 := ⟨(Classical.choice (omega.nonempty)).2⟩
  let psi : PureVector (Prod (Prod a1 b1) (Prod a1 b1)) :=
    xi.canonicalPurification.reindex (Equiv.prodComm (Prod a1 b1) (Prod a1 b1))
  let phi : PureVector (Prod (Prod a2 b2) (Prod a2 b2)) :=
    omega.canonicalPurification.reindex (Equiv.prodComm (Prod a2 b2) (Prod a2 b2))
  have hpsiAB : psi.state.marginalAB = xi := by
    simpa [psi] using State.canonicalPurification_swap_marginalAB xi
  have hphiAB : phi.state.marginalAB = omega := by
    simpa [phi] using State.canonicalPurification_swap_marginalAB omega
  have h :=
    PureVector.sandwichedRenyiMutualInformationE_bipartiteProductPurification_ge_add
      psi phi halpha
  have htarget :
      psi.state.marginalAB.sandwichedRenyiMutualInformationE alpha +
          phi.state.marginalAB.sandwichedRenyiMutualInformationE alpha ≤
        (psi.state.marginalAB.bipartiteProduct phi.state.marginalAB).sandwichedRenyiMutualInformationE
          alpha := by
    have hprodAB := PureVector.bipartiteProductPurification_marginalAB psi phi
    rw [← hprodAB]
    simpa [State.marginalAB_eq_marginalA] using h
  rw [hpsiAB, hphiAB] at htarget
  exact htarget

/-- State-level product additivity for sandwiched-Renyi mutual information.

This is the completed support-convention form of KW `EA_capacity.tex:1169-1217`,
combining the definition-side upper bound with the source-shaped lower branch
above. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProduct_eq_add
    {a1 b1 a2 b2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha =
      xi.sandwichedRenyiMutualInformationE alpha +
        omega.sandwichedRenyiMutualInformationE alpha := by
  haveI : Nonempty (Prod a1 b1) := xi.nonempty
  haveI : Nonempty b1 := ⟨(Classical.choice (xi.nonempty)).2⟩
  haveI : Nonempty (Prod a2 b2) := omega.nonempty
  haveI : Nonempty b2 := ⟨(Classical.choice (omega.nonempty)).2⟩
  exact le_antisymm
    (State.sandwichedRenyiMutualInformationE_bipartiteProduct_le_add
      xi omega halpha)
    (State.sandwichedRenyiMutualInformationE_bipartiteProduct_ge_add
      xi omega halpha)

end State

/-- The full-rank state domain used in the KW channel alternate expression is
nonempty, witnessed by the maximally mixed state. -/
private instance fullRankStateSubtypeNonempty
    {a : Type u1} [Fintype a] [DecidableEq a] [Nonempty a] :
    Nonempty {sigma : State a // sigma.matrix.PosDef} :=
  ⟨⟨State.maximallyMixed a, State.maximallyMixed_posDef⟩⟩

namespace MatrixMap

variable {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
variable [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
variable [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]

/-- The output-side weighting map `S_sigma^(alpha)` from the KW CB-norm
expression for sandwiched entanglement-assisted mutual information. -/
def sandwichedSideWeightMap (sigma : State b1) (alpha : ℝ) : MatrixMap b1 b1 :=
  MatrixMap.ofKraus
    (fun _ : Unit => CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)))

/-- The weighting map acts by conjugation with the sandwiched reference power. -/
theorem sandwichedSideWeightMap_apply
    (sigma : State b1) (alpha : ℝ) (X : CMatrix b1) :
    sandwichedSideWeightMap sigma alpha X =
      CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)) *
        X *
        (CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha))).conjTranspose := by
  simp [sandwichedSideWeightMap, MatrixMap.ofKraus]

/-- Source form of the KW weighting map:
`S_sigma^(alpha)(X) = sigma^s X sigma^s`.  The right-hand Kraus adjoint in
`sandwichedSideWeightMap_apply` is the same matrix because PSD functional
calculus powers are Hermitian. -/
theorem sandwichedSideWeightMap_apply_source
    (sigma : State b1) (alpha : ℝ) (X : CMatrix b1) :
    sandwichedSideWeightMap sigma alpha X =
      CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)) *
        X *
        CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)) := by
  rw [sandwichedSideWeightMap_apply]
  have hHerm :
      (CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha))).IsHermitian :=
    (cMatrix_rpow_posSemidef
      (A := sigma.matrix) (s := (1 - alpha) / (2 * alpha)) sigma.pos).isHermitian
  rw [hHerm.eq]

/-- The output-side weighting map is completely positive. -/
theorem sandwichedSideWeightMap_completelyPositive
    (sigma : State b1) (alpha : ℝ) :
    MatrixMap.IsCompletelyPositive (sandwichedSideWeightMap sigma alpha) :=
  MatrixMap.ofKraus_completelyPositive _

/-- The KW output-side weighting map preserves positive semidefinite inputs. -/
theorem sandwichedSideWeightMap_mapsPositive
    (sigma : State b1) (alpha : ℝ)
    {X : CMatrix b1} (hX : X.PosSemidef) :
    (sandwichedSideWeightMap sigma alpha X).PosSemidef :=
  MatrixMap.isCompletelyPositive_mapsPositive (sandwichedSideWeightMap sigma alpha)
    (sandwichedSideWeightMap_completelyPositive sigma alpha) X hX

/-- Full-rank KW side weighting is injective on matrices.  This is the local
nonzero-preservation fact behind the strict positivity side condition needed
when the source proof takes `log ||S_sigma^(alpha) o N||`. -/
theorem sandwichedSideWeightMap_apply_ne_zero_of_posDef
    (sigma : State b1) (hsigma : sigma.matrix.PosDef) (alpha : ℝ)
    {X : CMatrix b1} (hXne : X ≠ 0) :
    sandwichedSideWeightMap sigma alpha X ≠ 0 := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let C : CMatrix b1 := CFC.rpow sigma.matrix s
  have hC : C.PosDef := by
    simpa [C, s] using cMatrix_rpow_posDef_of_posDef hsigma s
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hleft : C⁻¹ * C = (1 : CMatrix b1) := Matrix.nonsing_inv_mul C hCdet
  have hright : C * C⁻¹ = (1 : CMatrix b1) := Matrix.mul_nonsing_inv C hCdet
  intro hzero
  have hzeroC : C * X * C = 0 := by
    have h := hzero
    rw [sandwichedSideWeightMap_apply] at h
    change C * X * C.conjTranspose = 0 at h
    rwa [hC.isHermitian.eq] at h
  have hzero' : C⁻¹ * (C * X * C) * C⁻¹ = 0 := by
    rw [hzeroC]
    simp
  have hXzero : X = 0 := by
    calc
      X = (1 : CMatrix b1) * X * (1 : CMatrix b1) := by simp
      _ = (C⁻¹ * C) * X * (C * C⁻¹) := by rw [hleft, hright]
      _ = C⁻¹ * (C * X * C) * C⁻¹ := by noncomm_ring
      _ = 0 := hzero'
  exact hXne hXzero

/-- Reference-tensored KW side weighting is conjugation by
`I_R ⊗ sigma^((1-alpha)/(2 alpha))`. -/
theorem referenceKron_sandwichedSideWeightMap_apply
    (sigma : State b1) (alpha : ℝ) (X : CMatrix (Prod a1 b1)) :
    MatrixMap.kron (Channel.idChannel a1).map (sandwichedSideWeightMap sigma alpha) X =
      Matrix.kronecker (1 : CMatrix a1)
          (CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha))) *
        X *
        (Matrix.kronecker (1 : CMatrix a1)
          (CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)))).conjTranspose := by
  change (MatrixMap.kron
      (MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix a1)))
      (MatrixMap.ofKraus
        (fun _ : Unit => CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)))) X) = _
  rw [MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
  simp [MatrixMap.ofKraus, MatrixMap.krausProduct]

/-- Full-rank reference-tensored KW side weighting preserves nonzero matrices. -/
theorem referenceKron_sandwichedSideWeightMap_apply_ne_zero_of_posDef
    (sigma : State b1) (hsigma : sigma.matrix.PosDef) (alpha : ℝ)
    {X : CMatrix (Prod a1 b1)} (hXne : X ≠ 0) :
    MatrixMap.kron (Channel.idChannel a1).map
        (sandwichedSideWeightMap sigma alpha) X ≠ 0 := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let C : CMatrix b1 := CFC.rpow sigma.matrix s
  let D : CMatrix (Prod a1 b1) := Matrix.kronecker (1 : CMatrix a1) C
  have hC : C.PosDef := by
    simpa [C, s] using cMatrix_rpow_posDef_of_posDef hsigma s
  have hD : D.PosDef := by
    simpa [D] using Matrix.PosDef.one.kronecker hC
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hleft : D⁻¹ * D = (1 : CMatrix (Prod a1 b1)) :=
    Matrix.nonsing_inv_mul D hDdet
  have hright : D * D⁻¹ = (1 : CMatrix (Prod a1 b1)) :=
    Matrix.mul_nonsing_inv D hDdet
  intro hzero
  have hzeroD : D * X * D = 0 := by
    have h := hzero
    rw [referenceKron_sandwichedSideWeightMap_apply] at h
    change D * X * D.conjTranspose = 0 at h
    rwa [hD.isHermitian.eq] at h
  have hzero' : D⁻¹ * (D * X * D) * D⁻¹ = 0 := by
    rw [hzeroD]
    simp
  have hXzero : X = 0 := by
    calc
      X = (1 : CMatrix (Prod a1 b1)) * X * (1 : CMatrix (Prod a1 b1)) := by simp
      _ = (D⁻¹ * D) * X * (D * D⁻¹) := by rw [hleft, hright]
      _ = D⁻¹ * (D * X * D) * D⁻¹ := by noncomm_ring
      _ = 0 := hzero'
  exact hXne hXzero

/-- The source CB `1 -> alpha` norm is nonnegative because it is the supremum
of nonnegative admissible values. -/
theorem cbOneToAlphaNorm_nonneg
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : ℝ) :
    0 ≤ MatrixMap.cbOneToAlphaNorm Phi hPhi alpha := by
  unfold MatrixMap.cbOneToAlphaNorm MatrixMap.cbOneToAlphaOriginalValueSet
  exact Real.sSup_nonneg (by
    rintro x ⟨Y, rfl⟩
    exact MatrixMap.cbOneToAlphaOriginalValue_nonneg Phi hPhi Y alpha)

/-- Reference lifting preserves trace when the underlying matrix map does.
This is the trace-preserving half of the source `id_R ⊗ Phi` construction. -/
theorem referenceLift_isTracePreserving
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsTracePreserving Phi) :
    MatrixMap.IsTracePreserving Phi.referenceLift :=
  MatrixMap.isTracePreserving_kron (Channel.idChannel a1).map Phi
    (Channel.idChannel a1).tracePreserving hPhi

/-- A trace-preserving map cannot send a nonzero positive semidefinite input
to zero, because that would force the input trace to vanish. -/
theorem isTracePreserving_apply_ne_zero_of_posSemidef
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsTracePreserving Phi)
    {X : CMatrix a1} (hX : X.PosSemidef) (hXne : X ≠ 0) :
    Phi X ≠ 0 := by
  intro hzero
  have htrace_zero : X.trace = 0 := by
    have htrace := hPhi X
    rw [hzero] at htrace
    simpa using htrace.symm
  have hXzero : X = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hX).mp htrace_zero
  exact hXne hXzero

/-- Reference-lifted trace-preserving maps preserve nonzero PSD inputs. -/
theorem referenceLift_apply_ne_zero_of_tracePreserving
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsTracePreserving Phi)
    {X : CMatrix (Prod a1 a1)} (hX : X.PosSemidef) (hXne : X ≠ 0) :
    Phi.referenceLift X ≠ 0 :=
  isTracePreserving_apply_ne_zero_of_posSemidef Phi.referenceLift
    (referenceLift_isTracePreserving Phi hPhi) hX hXne

omit [DecidableEq a1] in
/-- A positive-definite finite matrix on a nonempty system is nonzero. -/
theorem cMatrix_ne_zero_of_posDef [Nonempty a1]
    {X : CMatrix a1} (hX : X.PosDef) :
    X ≠ 0 := by
  intro hzero
  have htrace : (0 : ℂ) < X.trace := Matrix.PosDef.trace_pos hX
  rw [hzero] at htrace
  norm_num at htrace

/-- The source Choi/Gamma CB input is nonzero for full-rank reference-side
weights. -/
theorem cbOneToAlphaOriginalInput_ne_zero_of_posDef
    [Nonempty a1] {Y : CMatrix a1} (hY : Y.PosDef)
    {alpha : ℝ} (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput Y alpha ≠ 0 := by
  intro hzero
  have hpartial_zero :
      partialTraceB (a := a1) (b := a1) (cbOneToAlphaOriginalInput Y alpha) = 0 := by
    rw [hzero]
    ext i j
    change (∑ k : a1, (0 : CMatrix (Prod a1 a1)) (i, k) (j, k)) = 0
    simp
  have hrpow_zero : CFC.rpow Y (1 / alpha) = 0 := by
    rw [← partialTraceB_cbOneToAlphaOriginalInput_eq_rpow
      (a := a1) hY.posSemidef halpha]
    exact hpartial_zero
  exact cMatrix_ne_zero_of_posDef
    (cMatrix_rpow_posDef_of_posDef hY (1 / alpha)) hrpow_zero

/-- The source Choi/Gamma CB input is nonzero for every normalized state.

This is the trace-one endpoint needed in KW `EA_capacity.tex:2090-2093` after
the `Tr[Y_R] = 1` reduction: positive definiteness of the state is not needed,
only normalization. -/
theorem cbOneToAlphaOriginalInput_ne_zero_of_state
    (tau : State a1) {alpha : ℝ} (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput tau.matrix alpha ≠ 0 := by
  intro hzero
  have hpartial_zero :
      partialTraceB (a := a1) (b := a1)
          (cbOneToAlphaOriginalInput tau.matrix alpha) = 0 := by
    rw [hzero]
    ext i j
    change (∑ k : a1, (0 : CMatrix (Prod a1 a1)) (i, k) (j, k)) = 0
    simp
  have hrpow_zero : CFC.rpow tau.matrix (1 / alpha) = 0 := by
    rw [← partialTraceB_cbOneToAlphaOriginalInput_eq_rpow
      (a := a1) tau.pos halpha]
    exact hpartial_zero
  have hnorm_zero :
      psdSchattenPNorm (CFC.rpow tau.matrix (1 / alpha))
          (tau.rpowMatrix_posSemidef (1 / alpha)) alpha = 0 := by
    calc
      psdSchattenPNorm (CFC.rpow tau.matrix (1 / alpha))
          (tau.rpowMatrix_posSemidef (1 / alpha)) alpha =
        psdSchattenPNorm (0 : CMatrix a1) Matrix.PosSemidef.zero alpha := by
          exact psdSchattenPNorm_congr hrpow_zero _ Matrix.PosSemidef.zero alpha
      _ = 0 := psdSchattenPNorm_zero alpha (ne_of_gt halpha)
  have hone :=
    State.state_rpow_one_div_psdSchattenPNorm_eq_one_psd tau halpha
  rw [hone] at hnorm_zero
  norm_num at hnorm_zero

/-- The maximally mixed reference gives a nonzero source Choi/Gamma CB input. -/
theorem cbOneToAlphaOriginalInput_maximallyMixed_ne_zero
    [Nonempty a1] {alpha : ℝ} (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput (State.maximallyMixed a1).matrix alpha ≠ 0 :=
  cbOneToAlphaOriginalInput_ne_zero_of_posDef
    (State.maximallyMixed_posDef_of_nonempty (a := a1)) halpha

/-- The maximally mixed source-side CB candidate has strictly positive value
for any trace-preserving completely positive map. -/
theorem cbOneToAlphaOriginalValue_maximallyMixed_pos_of_tracePreserving
    [Nonempty a1] (Phi : MatrixMap a1 b1)
    (hPhiCP : MatrixMap.IsCompletelyPositive Phi)
    (hPhiTP : MatrixMap.IsTracePreserving Phi)
    {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      cbOneToAlphaOriginalValue Phi hPhiCP
        { matrix := (State.maximallyMixed a1).matrix,
          pos := (State.maximallyMixed a1).pos,
          trace_le_one := by
            rw [(State.maximallyMixed a1).trace_eq_one]
            norm_num }
        alpha := by
  let Y0 : CBOneToAlphaOriginalDomain a1 :=
    { matrix := (State.maximallyMixed a1).matrix,
      pos := (State.maximallyMixed a1).pos,
      trace_le_one := by
        rw [(State.maximallyMixed a1).trace_eq_one]
        norm_num }
  let X : CMatrix (Prod a1 a1) := cbOneToAlphaOriginalInput Y0.matrix alpha
  let hX : X.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y0.pos alpha
  have hXne : X ≠ 0 := by
    simpa [X, Y0] using cbOneToAlphaOriginalInput_maximallyMixed_ne_zero
      (a1 := a1) halpha
  have hPhiXne : Phi.referenceLift X ≠ 0 :=
    referenceLift_apply_ne_zero_of_tracePreserving Phi hPhiTP hX hXne
  unfold cbOneToAlphaOriginalValue
  change 0 < psdSchattenPNorm (Phi.referenceLift X) _ alpha
  exact psdSchattenPNorm_pos_of_ne_zero (Phi.referenceLift X) _ hPhiXne

/-- A zero-trace PSD source-side input gives the zero Choi/Gamma CB input.

This is the zero-boundary branch of KW `EA_capacity.tex:2088-2093`: when the
trace-normalized source variable has zero trace, it contributes zero to the
CB `1 -> alpha` supremum before the trace-one normalization step. -/
theorem cbOneToAlphaOriginalInput_eq_zero_of_trace_zero
    {Y : CMatrix a1} (hY : Y.PosSemidef)
    {alpha : ℝ} (halpha : 0 < alpha)
    (htrace : Y.trace.re = 0) :
    cbOneToAlphaOriginalInput Y alpha = 0 := by
  have hYtrace : Y.trace = 0 := by
    apply Complex.ext
    · simpa using htrace
    · simpa using (Matrix.PosSemidef.trace_nonneg hY).2.symm
  have hYzero : Y = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hY).mp hYtrace
  have hexp_ne : 1 / (2 * alpha) ≠ 0 :=
    one_div_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt halpha))
  unfold cbOneToAlphaOriginalInput cbOneToAlphaReferenceWeight
  rw [hYzero, CFC.zero_rpow (A := CMatrix a1) hexp_ne]
  simp [Matrix.kronecker]

/-- Zero-trace source-side inputs contribute zero to the source Choi/Gamma
CB-norm value.

This is the scalar-value form of
`cbOneToAlphaOriginalInput_eq_zero_of_trace_zero`, used before replacing a
nonzero subnormalized source variable by its normalized trace-one state. -/
theorem cbOneToAlphaOriginalValue_eq_zero_of_trace_zero
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Y : CBOneToAlphaOriginalDomain a1)
    {alpha : ℝ} (halpha : 0 < alpha)
    (htrace : Y.matrix.trace.re = 0) :
    cbOneToAlphaOriginalValue Phi hPhi Y alpha = 0 := by
  let X : CMatrix (Prod a1 a1) := cbOneToAlphaOriginalInput Y.matrix alpha
  let hX : X.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  have hXzero : X = 0 := by
    simpa [X] using
      cbOneToAlphaOriginalInput_eq_zero_of_trace_zero Y.pos halpha htrace
  have hPhiXpos : (Phi.referenceLift X).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi hX
  have hPhiXzero : Phi.referenceLift X = 0 := by
    rw [hXzero]
    exact map_zero Phi.referenceLift
  unfold cbOneToAlphaOriginalValue
  change psdSchattenPNorm (Phi.referenceLift X) _ alpha = 0
  calc
    psdSchattenPNorm (Phi.referenceLift X) _ alpha =
        psdSchattenPNorm (0 : CMatrix (Prod a1 b1))
          Matrix.PosSemidef.zero alpha := by
          exact psdSchattenPNorm_congr hPhiXzero hPhiXpos
            Matrix.PosSemidef.zero alpha
    _ = 0 := psdSchattenPNorm_zero alpha (ne_of_gt halpha)

/-- A trace-one state as a source-side CB original-domain point. -/
def CBOneToAlphaOriginalDomain.ofState (tau : State a1) :
    CBOneToAlphaOriginalDomain a1 where
  matrix := tau.matrix
  pos := tau.pos
  trace_le_one := by
    rw [tau.trace_eq_one]
    norm_num

/-- A nonzero source CB original-domain point is its normalized state times
its trace.

This is the matrix normalization step in KW `EA_capacity.tex:2088-2093`,
before proving that the source CB supremum can be restricted to `Tr[Y] = 1`. -/
theorem cbOneToAlphaOriginalDomain_matrix_eq_trace_smul_normalize
    (Y : CBOneToAlphaOriginalDomain a1)
    (htrace : Y.matrix.trace.re ≠ 0) :
    let ρ : SubnormalizedState a1 :=
      { matrix := Y.matrix, pos := Y.pos, trace_le_one := Y.trace_le_one }
    Y.matrix = Y.matrix.trace.re • (ρ.normalize htrace).matrix := by
  intro ρ
  have hscale : Y.matrix.trace.re * (Y.matrix.trace.re)⁻¹ = 1 := by
    exact mul_inv_cancel₀ htrace
  rw [SubnormalizedState.normalize_matrix]
  change Y.matrix = Y.matrix.trace.re • ((Y.matrix.trace.re)⁻¹ • Y.matrix)
  rw [smul_smul, hscale, one_smul]

/-- Positive real scaling pulls through the source-side CB reference weight.

This is the homogeneous part of the KW trace-normalization step
`EA_capacity.tex:2088-2093`. -/
theorem cbOneToAlphaReferenceWeight_pos_real_smul
    {Y : CMatrix a1} (hY : Y.PosSemidef)
    {t alpha : ℝ} (ht : 0 < t) (_halpha : 0 < alpha) :
    cbOneToAlphaReferenceWeight (t • Y : CMatrix a1) alpha =
      (t ^ (1 / (2 * alpha)) : ℝ) • cbOneToAlphaReferenceWeight Y alpha := by
  unfold cbOneToAlphaReferenceWeight
  rw [cMatrix_rpow_real_smul_posSemidef_schatten hY (le_of_lt ht)]
  ext p q
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, mul_assoc]

/-- Positive real scaling of the source-side CB original input.

If `Y = t tau` with `t > 0`, then the weighted Choi/Gamma input scales by
`t^(1/alpha)`.  This is the algebraic heart of KW
`EA_capacity.tex:2088-2093`. -/
theorem cbOneToAlphaOriginalInput_pos_real_smul
    {Y : CMatrix a1} (hY : Y.PosSemidef)
    {t alpha : ℝ} (ht : 0 < t) (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput (t • Y : CMatrix a1) alpha =
      (t ^ (1 / alpha) : ℝ) • cbOneToAlphaOriginalInput Y alpha := by
  let c : ℝ := t ^ (1 / (2 * alpha))
  have hW :
      cbOneToAlphaReferenceWeight (t • Y : CMatrix a1) alpha =
        c • cbOneToAlphaReferenceWeight Y alpha := by
    simpa [c] using cbOneToAlphaReferenceWeight_pos_real_smul
      (a1 := a1) hY ht halpha
  have hc_mul : c * c = t ^ (1 / alpha) := by
    have hexp : 1 / alpha = 1 / (2 * alpha) + 1 / (2 * alpha) := by
      field_simp [ne_of_gt halpha]
      ring
    rw [hexp, Real.rpow_add ht]
  unfold cbOneToAlphaOriginalInput
  rw [hW]
  simpa [hc_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]

/-- Positive real scaling of the source-side CB original value.

This is the value-level homogeneous step in KW `EA_capacity.tex:2088-2093`:
once a subnormalized source variable is written as `t • tau`, the corresponding
CB value is multiplied by `t^(1/alpha)`. -/
theorem cbOneToAlphaOriginalValue_eq_rpow_mul_of_matrix_eq_pos_real_smul
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Y : CBOneToAlphaOriginalDomain a1) (tau : State a1)
    {t alpha : ℝ} (ht : 0 < t) (halpha : 0 < alpha)
    (hY : Y.matrix = t • tau.matrix) :
    cbOneToAlphaOriginalValue Phi hPhi Y alpha =
      t ^ (1 / alpha) *
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau) alpha := by
  let lambda : ℝ := t ^ (1 / alpha)
  let Xtau : CMatrix (Prod a1 a1) := cbOneToAlphaOriginalInput tau.matrix alpha
  let hXtau : Xtau.PosSemidef := cbOneToAlphaOriginalInput_posSemidef tau.pos alpha
  let XY : CMatrix (Prod a1 a1) := cbOneToAlphaOriginalInput Y.matrix alpha
  let hXY : XY.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  have hlambda_nonneg : 0 ≤ lambda := Real.rpow_nonneg (le_of_lt ht) (1 / alpha)
  have hinput :
      XY = lambda • Xtau := by
    dsimp [XY, Xtau, lambda]
    rw [hY]
    exact cbOneToAlphaOriginalInput_pos_real_smul tau.pos ht halpha
  have hPhiXtau :
      (Phi.referenceLift Xtau).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi hXtau
  have hPhiScaled :
      (lambda • Phi.referenceLift Xtau : CMatrix (Prod a1 b1)).PosSemidef :=
    Matrix.PosSemidef.smul hPhiXtau hlambda_nonneg
  have hPhiXY :
      Phi.referenceLift XY = lambda • Phi.referenceLift Xtau := by
    rw [hinput]
    exact LinearMap.map_smul_of_tower Phi.referenceLift lambda Xtau
  unfold cbOneToAlphaOriginalValue
  calc
    psdSchattenPNorm (Phi.referenceLift XY) _ alpha =
        psdSchattenPNorm (lambda • Phi.referenceLift Xtau) hPhiScaled alpha := by
          exact psdSchattenPNorm_congr hPhiXY _ hPhiScaled alpha
    _ =
        lambda * psdSchattenPNorm (Phi.referenceLift Xtau) hPhiXtau alpha := by
          rw [psdSchattenPNorm_real_smul hPhiXtau hlambda_nonneg halpha]
    _ =
        t ^ (1 / alpha) *
          psdSchattenPNorm
            (Phi.referenceLift
              (cbOneToAlphaOriginalInput
                (CBOneToAlphaOriginalDomain.ofState tau).matrix alpha))
            _ alpha := by
          simp [lambda, Xtau, CBOneToAlphaOriginalDomain.ofState]

/-- Source concavity for the trace-normalized induced `alpha -> alpha` value.

This is the `Y ↦ ||Phi(Y^(1/alpha))||_alpha` form of KW
`EA_capacity.tex:2080-2084`, specialized to the trace-normalized domain used
by the CB complement bridge.  The theorem is the finite-dimensional
bookkeeping wrapper around
`MatrixMap.cp_psdSchatten_rpow_value_concave`. -/
theorem alphaToAlphaTraceValue_mix_le
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (Y0 Y1 : AlphaToAlphaTraceDomain a1 alpha) :
    lambda * alphaToAlphaTraceValue (alpha := alpha) Phi hPhi Y0 +
        (1 - lambda) * alphaToAlphaTraceValue (alpha := alpha) Phi hPhi Y1 ≤
      alphaToAlphaTraceValue (alpha := alpha) Phi hPhi
        { matrix := lambda • Y0.matrix + (1 - lambda) • Y1.matrix,
          pos :=
            Matrix.PosSemidef.add
              (Matrix.PosSemidef.smul Y0.pos hlambda0)
              (Matrix.PosSemidef.smul Y1.pos (sub_nonneg.mpr hlambda1)),
          trace_le_one := by
            calc
              ((lambda • Y0.matrix + (1 - lambda) • Y1.matrix).trace).re =
                  lambda * Y0.matrix.trace.re + (1 - lambda) * Y1.matrix.trace.re := by
                    simp [Matrix.trace_add, Matrix.trace_smul, add_comm, add_left_comm,
                      add_assoc]
              _ ≤ lambda * 1 + (1 - lambda) * 1 := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left Y0.trace_le_one hlambda0)
                      (mul_le_mul_of_nonneg_left Y1.trace_le_one
                        (sub_nonneg.mpr hlambda1))
              _ = 1 := by ring } := by
  exact cp_psdSchatten_rpow_value_concave
    Phi hPhi halpha hlambda0 hlambda1 Y0.pos Y1.pos

/-- Concavity of the KW source-side CB original value in the normalized
source input.

This is the `tau_R`-side mathematical condition used in the channel Sion step
KW `EA_capacity.tex:2080-2084`: for fixed weighted channel map, the function
`tau ↦ ||(id ⊗ Phi)(Γ_tau)||_alpha` is concave on normalized source states.
The proof follows the source route already formalized locally: pass through the
complement trace-domain representation and apply
`alphaToAlphaTraceValue_mix_le`. -/
theorem cbOneToAlphaOriginalValue_ofState_mix_le
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (tau0 tau1 : State a1) :
    lambda *
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau0) alpha +
      (1 - lambda) *
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau1) alpha ≤
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState
            { matrix := lambda • tau0.matrix + (1 - lambda) • tau1.matrix,
              pos :=
                Matrix.PosSemidef.add
                  (Matrix.PosSemidef.smul tau0.pos hlambda0)
                  (Matrix.PosSemidef.smul tau1.pos (sub_nonneg.mpr hlambda1)),
              trace_eq_one := by
                rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                  tau0.trace_eq_one, tau1.trace_eq_one]
                norm_num }) alpha := by
  let tauMix : State a1 :=
    { matrix := lambda • tau0.matrix + (1 - lambda) • tau1.matrix,
      pos :=
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul tau0.pos hlambda0)
          (Matrix.PosSemidef.smul tau1.pos (sub_nonneg.mpr hlambda1)),
      trace_eq_one := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
          tau0.trace_eq_one, tau1.trace_eq_one]
        norm_num }
  let PhiC : MatrixMap a1 (Prod a1 b1) := MatrixMap.cpComplement Phi hPhi
  let hPhiC : MatrixMap.IsCompletelyPositive PhiC :=
    MatrixMap.cpComplement_isCompletelyPositive Phi hPhi
  let Y0 : AlphaToAlphaTraceDomain a1 alpha :=
    (CBOneToAlphaOriginalDomain.ofState tau0).toTransposeTraceDomain
      (alpha := alpha) (lt_trans zero_lt_one halpha)
  let Y1 : AlphaToAlphaTraceDomain a1 alpha :=
    (CBOneToAlphaOriginalDomain.ofState tau1).toTransposeTraceDomain
      (alpha := alpha) (lt_trans zero_lt_one halpha)
  have hconc := alphaToAlphaTraceValue_mix_le
    PhiC hPhiC halpha hlambda0 hlambda1 Y0 Y1
  have h0 :
      cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau0) alpha =
        alphaToAlphaTraceValue PhiC hPhiC Y0 := by
    simpa [PhiC, hPhiC, Y0] using
      cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
        Phi hPhi (lt_trans zero_lt_one halpha)
        (CBOneToAlphaOriginalDomain.ofState tau0)
  have h1 :
      cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau1) alpha =
        alphaToAlphaTraceValue PhiC hPhiC Y1 := by
    simpa [PhiC, hPhiC, Y1] using
      cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
        Phi hPhi (lt_trans zero_lt_one halpha)
        (CBOneToAlphaOriginalDomain.ofState tau1)
  have hmix :
      cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tauMix) alpha =
        alphaToAlphaTraceValue (alpha := alpha) PhiC hPhiC
          { matrix := lambda • Y0.matrix + (1 - lambda) • Y1.matrix,
            pos :=
              Matrix.PosSemidef.add
                (Matrix.PosSemidef.smul Y0.pos hlambda0)
                (Matrix.PosSemidef.smul Y1.pos (sub_nonneg.mpr hlambda1)),
            trace_le_one := by
              calc
                ((lambda • Y0.matrix + (1 - lambda) • Y1.matrix).trace).re =
                    lambda * Y0.matrix.trace.re +
                      (1 - lambda) * Y1.matrix.trace.re := by
                    simp [Matrix.trace_add, Matrix.trace_smul, add_comm,
                      add_left_comm, add_assoc]
                _ ≤ lambda * 1 + (1 - lambda) * 1 := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left Y0.trace_le_one hlambda0)
                      (mul_le_mul_of_nonneg_left Y1.trace_le_one
                        (sub_nonneg.mpr hlambda1))
                _ = 1 := by ring } := by
    simpa [PhiC, hPhiC, tauMix, Y0, Y1, CBOneToAlphaOriginalDomain.ofState,
      CBOneToAlphaOriginalDomain.toTransposeTraceDomain, Matrix.transpose_add,
      Matrix.transpose_smul] using
      cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
        Phi hPhi (lt_trans zero_lt_one halpha)
        (CBOneToAlphaOriginalDomain.ofState tauMix)
  have hgoal :
      lambda *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau0) alpha +
        (1 - lambda) *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau1) alpha ≤
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tauMix) alpha := by
    rw [h0, h1, hmix]
    exact hconc
  simpa [tauMix] using hgoal

/-- Quasiconcavity-style two-point consequence of the KW source-side
concavity theorem.

This is the scalar `min <= mixed value` form needed by Sion's
`QuasiconcaveOn` hypothesis for the source variable in
KW `EA_capacity.tex:2080-2084`. -/
theorem cbOneToAlphaOriginalValue_ofState_min_le_mix
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (tau0 tau1 : State a1) :
    min
        (cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau0) alpha)
        (cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau1) alpha) ≤
      cbOneToAlphaOriginalValue Phi hPhi
        (CBOneToAlphaOriginalDomain.ofState
          { matrix := lambda • tau0.matrix + (1 - lambda) • tau1.matrix,
            pos :=
              Matrix.PosSemidef.add
                (Matrix.PosSemidef.smul tau0.pos hlambda0)
                (Matrix.PosSemidef.smul tau1.pos (sub_nonneg.mpr hlambda1)),
            trace_eq_one := by
              rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                tau0.trace_eq_one, tau1.trace_eq_one]
              norm_num }) alpha := by
  let v0 : ℝ :=
    cbOneToAlphaOriginalValue Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState tau0) alpha
  let v1 : ℝ :=
    cbOneToAlphaOriginalValue Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState tau1) alpha
  let tauMix : State a1 :=
    { matrix := lambda • tau0.matrix + (1 - lambda) • tau1.matrix,
      pos :=
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul tau0.pos hlambda0)
          (Matrix.PosSemidef.smul tau1.pos (sub_nonneg.mpr hlambda1)),
      trace_eq_one := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
          tau0.trace_eq_one, tau1.trace_eq_one]
        norm_num }
  have hmix :=
    cbOneToAlphaOriginalValue_ofState_mix_le
      Phi hPhi halpha hlambda0 hlambda1 tau0 tau1
  have hweighted :
      min v0 v1 ≤ lambda * v0 + (1 - lambda) * v1 := by
    calc
      min v0 v1 =
          lambda * min v0 v1 + (1 - lambda) * min v0 v1 := by ring
      _ ≤ lambda * v0 + (1 - lambda) * v1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (min_le_left v0 v1) hlambda0)
            (mul_le_mul_of_nonneg_left (min_le_right v0 v1)
              (sub_nonneg.mpr hlambda1))
  exact hweighted.trans (by simpa [v0, v1, tauMix] using hmix)

/-- Every source original-domain CB candidate is bounded by a trace-one state
candidate.

This formalizes KW `EA_capacity.tex:2090`: after splitting off the trace of
`Y_R`, a nonzero subnormalized candidate is a positive scalar multiple of its
normalized state, and the scalar factor is at most one. -/
theorem exists_state_cbOneToAlphaOriginalValue_ge
    [Nonempty a1]
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 0 < alpha) (Y : CBOneToAlphaOriginalDomain a1) :
    ∃ tau : State a1,
      cbOneToAlphaOriginalValue Phi hPhi Y alpha ≤
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau) alpha := by
  by_cases htrace : Y.matrix.trace.re = 0
  · refine ⟨State.maximallyMixed a1, ?_⟩
    rw [cbOneToAlphaOriginalValue_eq_zero_of_trace_zero Phi hPhi Y halpha htrace]
    exact cbOneToAlphaOriginalValue_nonneg Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState (State.maximallyMixed a1)) alpha
  · let ρ : SubnormalizedState a1 :=
      { matrix := Y.matrix, pos := Y.pos, trace_le_one := Y.trace_le_one }
    let tau : State a1 := ρ.normalize htrace
    refine ⟨tau, ?_⟩
    have ht : 0 < Y.matrix.trace.re := by
      simpa [ρ] using ρ.trace_pos_of_trace_ne_zero htrace
    have hY :
        Y.matrix = Y.matrix.trace.re • tau.matrix := by
      simpa [ρ, tau] using
        cbOneToAlphaOriginalDomain_matrix_eq_trace_smul_normalize Y htrace
    have hvalue :
        cbOneToAlphaOriginalValue Phi hPhi Y alpha =
          Y.matrix.trace.re ^ (1 / alpha) *
            cbOneToAlphaOriginalValue Phi hPhi
              (CBOneToAlphaOriginalDomain.ofState tau) alpha := by
      exact cbOneToAlphaOriginalValue_eq_rpow_mul_of_matrix_eq_pos_real_smul
        Phi hPhi Y tau ht halpha hY
    have hscale :
        Y.matrix.trace.re ^ (1 / alpha) ≤ 1 := by
      have htrace_nonneg : 0 ≤ Y.matrix.trace.re :=
        (Matrix.PosSemidef.trace_nonneg Y.pos).1
      have hinv_nonneg : 0 ≤ 1 / alpha :=
        one_div_nonneg.mpr (le_of_lt halpha)
      exact Real.rpow_le_one htrace_nonneg Y.trace_le_one hinv_nonneg
    have hstate_nonneg :
        0 ≤
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau) alpha :=
      cbOneToAlphaOriginalValue_nonneg Phi hPhi
        (CBOneToAlphaOriginalDomain.ofState tau) alpha
    rw [hvalue]
    calc
      Y.matrix.trace.re ^ (1 / alpha) *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau) alpha ≤
        1 *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau) alpha := by
          exact mul_le_mul_of_nonneg_right hscale hstate_nonneg
      _ =
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau) alpha := by
          rw [one_mul]

/-- Source CB original values restricted to trace-one state candidates. -/
def cbOneToAlphaStateOriginalValueSet
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : ℝ) : Set ℝ :=
  Set.range fun tau : State a1 =>
    cbOneToAlphaOriginalValue Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState tau) alpha

/-- The source CB norm supremum is unchanged after restricting the source
variable to trace-one state candidates.

This is the formal Lean interface for the final sentence of KW
`EA_capacity.tex:2090-2093`. -/
theorem cbOneToAlphaNorm_eq_sSup_stateOriginalValueSet_of_one_lt
    [Nonempty a1]
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    cbOneToAlphaNorm Phi hPhi alpha =
      sSup (cbOneToAlphaStateOriginalValueSet Phi hPhi alpha) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hbddState :
      BddAbove (cbOneToAlphaStateOriginalValueSet Phi hPhi alpha) := by
    refine ⟨cbOneToAlphaNorm Phi hPhi alpha, ?_⟩
    rintro y ⟨tau, rfl⟩
    exact cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      Phi hPhi halpha (CBOneToAlphaOriginalDomain.ofState tau)
  haveI : Nonempty (State a1) := ⟨State.maximallyMixed a1⟩
  haveI : Nonempty (CBOneToAlphaOriginalDomain a1) :=
    ⟨CBOneToAlphaOriginalDomain.ofState (State.maximallyMixed a1)⟩
  refine le_antisymm ?_ ?_
  · unfold cbOneToAlphaNorm cbOneToAlphaOriginalValueSet
    refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨Y, rfl⟩
    rcases exists_state_cbOneToAlphaOriginalValue_ge
        Phi hPhi halpha_pos Y with ⟨tau, hleTau⟩
    exact hleTau.trans
      (le_csSup hbddState
        ⟨tau, rfl⟩)
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨tau, rfl⟩
    exact cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      Phi hPhi halpha (CBOneToAlphaOriginalDomain.ofState tau)

/-- For full-rank product references, the KW output-side weighting map
factorizes as a tensor product.  This is the `S_{sigma_1 ⊗ sigma_2}` identity
used in `EA_capacity.tex:1242-1254`. -/
theorem sandwichedSideWeightMap_prod_posDef
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    (alpha : ℝ) :
    sandwichedSideWeightMap (sigma1.prod sigma2) alpha =
      MatrixMap.kron (sandwichedSideWeightMap sigma1 alpha)
        (sandwichedSideWeightMap sigma2 alpha) := by
  unfold sandwichedSideWeightMap
  rw [MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
  ext X bd bd'
  simp [MatrixMap.ofKraus, MatrixMap.krausProduct, State.prod]
  change
    (CFC.rpow (Matrix.kronecker sigma1.matrix sigma2.matrix)
          ((1 - alpha) / (2 * alpha)) *
        X *
        (CFC.rpow (Matrix.kronecker sigma1.matrix sigma2.matrix)
          ((1 - alpha) / (2 * alpha))).conjTranspose)
        bd bd' =
      (Matrix.kronecker
          (CFC.rpow sigma1.matrix ((1 - alpha) / (2 * alpha)))
          (CFC.rpow sigma2.matrix ((1 - alpha) / (2 * alpha))) *
        X *
        (Matrix.kronecker
          (CFC.rpow sigma1.matrix ((1 - alpha) / (2 * alpha)))
          (CFC.rpow sigma2.matrix ((1 - alpha) / (2 * alpha)))).conjTranspose)
        bd bd'
  rw [cMatrix_rpow_kronecker_posDef hsigma1 hsigma2 ((1 - alpha) / (2 * alpha))]

private theorem kron_comp_apply_general_local
    {x1 y1 z1 x2 y2 z2 : Type*}
    [Fintype x1] [DecidableEq x1] [Fintype y1] [DecidableEq y1]
    [Fintype z1] [DecidableEq z1] [Fintype x2] [DecidableEq x2]
    [Fintype y2] [DecidableEq y2] [Fintype z2] [DecidableEq z2]
    (Phi1 : MatrixMap y1 z1) (Phi2 : MatrixMap y2 z2)
    (Psi1 : MatrixMap x1 y1) (Psi2 : MatrixMap x2 y2)
    (X : CMatrix (Prod x1 x2)) :
    MatrixMap.kron Phi1 Phi2 (MatrixMap.kron Psi1 Psi2 X) =
      MatrixMap.kron (Phi1.comp Psi1) (Phi2.comp Psi2) X := by
  ext cd cd'
  rw [MatrixMap.map_eq_sum_single (MatrixMap.kron Psi1 Psi2) X]
  simp_rw [map_sum]
  simp_rw [map_smul]
  simp only [Matrix.sum_apply]
  rw [MatrixMap.map_eq_sum_single
    (MatrixMap.kron (Phi1.comp Psi1) (Phi2.comp Psi2)) X]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun ac _ => ?_
  refine Finset.sum_congr rfl fun ac' _ => ?_
  simp only [Matrix.smul_apply]
  congr 1
  cases ac with
  | mk a0 c0 =>
  cases ac' with
  | mk a1 c1 =>
  rw [single_prod_eq_kronecker_single]
  rw [MatrixMap.kron_apply_kronecker]
  rw [MatrixMap.kron_apply_kronecker]
  rw [MatrixMap.kron_apply_kronecker]
  rfl

/-- Reference lifting commutes with composition in the expected
`id_R ⊗ (Psi o Phi)` form. -/
theorem referenceLift_comp_apply
    (Psi : MatrixMap b1 b2) (Phi : MatrixMap a1 b1)
    (X : CMatrix (Prod a1 a1)) :
    MatrixMap.referenceLift (Psi.comp Phi) X =
      MatrixMap.kron (Channel.idChannel a1).map Psi (MatrixMap.referenceLift Phi X) := by
  symm
  change MatrixMap.kron (Channel.idChannel a1).map Psi
      (MatrixMap.kron (Channel.idChannel a1).map Phi X) =
    MatrixMap.kron (Channel.idChannel a1).map (Psi.comp Phi) X
  rw [kron_comp_apply_general_local
    (Channel.idChannel a1).map Psi (Channel.idChannel a1).map Phi X]
  have hid :
      ((Channel.idChannel a1).map.comp (Channel.idChannel a1).map) =
        (Channel.idChannel a1).map := by
    ext Y i j
    simp [LinearMap.comp_apply, Channel.idChannel_map]
  rw [hid]

/-- A reference lift commutes with sandwiching by a matrix acting only on the
reference register.

This is the matrix-map form of the KW polar-decomposition step where the
reference factor `tau_R^s` is absorbed into the Choi/Gamma input before the
channel acts on the second tensor factor. -/
theorem referenceLift_referenceSandwich
    (Phi : MatrixMap a1 b1) (W : CMatrix a1) (X : CMatrix (Prod a1 a1)) :
    MatrixMap.referenceLift Phi
        (Matrix.kronecker W (1 : CMatrix a1) *
          X *
          Matrix.kronecker W (1 : CMatrix a1)) =
      Matrix.kronecker W (1 : CMatrix b1) *
        MatrixMap.referenceLift Phi X *
        Matrix.kronecker W (1 : CMatrix b1) := by
  classical
  ext rb rb'
  rcases rb with ⟨r, b⟩
  rcases rb' with ⟨r', b'⟩
  simp only [MatrixMap.referenceLift, MatrixMap.kron_idChannel_left_apply_slice,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have hleft :
      (fun j j' =>
          ∑ x, ∑ y,
            (∑ u, ∑ v, (W r u * if j = v then 1 else 0) * X (u, v) (x, y)) *
              (W x r' * if j' = y then 1 else 0)) =
        (fun j j' => ∑ u, ∑ x, W r u * (W x r' * X (u, j) (x, j'))) := by
    ext j j'
    calc
      (∑ x, ∑ y,
          (∑ u, ∑ v, (W r u * if j = v then 1 else 0) * X (u, v) (x, y)) *
            (W x r' * if j' = y then 1 else 0)) =
          ∑ x, W x r' * ∑ u, W r u * X (u, j) (x, j') := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ =
          ∑ x, ∑ u, W x r' * (W r u * X (u, j) (x, j')) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
      _ = ∑ u, ∑ x, W x r' * (W r u * X (u, j) (x, j')) := by
            rw [Finset.sum_comm]
      _ = ∑ u, ∑ x, W r u * (W x r' * X (u, j) (x, j')) := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro x _
            ring
  have hright :
      (∑ x, ∑ y,
          (∑ u, ∑ v, (W r u * if b = v then 1 else 0) *
            Phi (fun j j' => X (u, j) (x, j')) v y) *
            (W x r' * if b' = y then 1 else 0)) =
        ∑ u, ∑ x, W r u * (W x r' * Phi (fun j j' => X (u, j) (x, j')) b b') := by
    calc
      (∑ x, ∑ y,
          (∑ u, ∑ v, (W r u * if b = v then 1 else 0) *
            Phi (fun j j' => X (u, j) (x, j')) v y) *
            (W x r' * if b' = y then 1 else 0)) =
          ∑ x, W x r' * ∑ u, W r u *
            Phi (fun j j' => X (u, j) (x, j')) b b' := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ =
          ∑ x, W x r' * ∑ u, W r u *
            Phi (fun j j' => X (u, j) (x, j')) b b' :=
        rfl
      _ =
          ∑ x, ∑ u, W x r' *
            (W r u * Phi (fun j j' => X (u, j) (x, j')) b b') := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
      _ = ∑ u, ∑ x, W x r' *
            (W r u * Phi (fun j j' => X (u, j) (x, j')) b b') := by
            rw [Finset.sum_comm]
      _ = ∑ u, ∑ x, W r u *
            (W x r' * Phi (fun j j' => X (u, j) (x, j')) b b') := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro x _
            ring
  rw [hleft, hright]
  have hslice :
      (fun j j' => ∑ x, ∑ y, W r x * (W y r' * X (x, j) (y, j'))) =
        ∑ x, ∑ y, (W r x * W y r') • (fun j j' => X (x, j) (y, j')) := by
    ext j j'
    simpa [mul_assoc]
  rw [hslice]
  have hmap1 :
      Phi (∑ x, ∑ y, (W r x * W y r') • (fun j j' => X (x, j) (y, j'))) =
        ∑ x, Phi (∑ y, (W r x * W y r') •
          (fun j j' => X (x, j) (y, j'))) := by
    exact (map_sum Phi (fun x =>
      ∑ y, (W r x * W y r') • (fun j j' => X (x, j) (y, j'))) Finset.univ)
  calc
    Phi (∑ x, ∑ y, (W r x * W y r') • (fun j j' => X (x, j) (y, j'))) b b' =
        (∑ x, Phi (∑ y, (W r x * W y r') •
          (fun j j' => X (x, j) (y, j')))) b b' := by
          exact congrFun (congrFun hmap1 b) b'
    _ = ∑ x, (Phi (∑ y, (W r x * W y r') •
          (fun j j' => X (x, j) (y, j')))) b b' := by
          simp [Matrix.sum_apply]
    _ = ∑ x, ∑ y, W r x *
          (W y r' * Phi (fun j j' => X (x, j) (y, j')) b b') := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have hmap2 :
              Phi (∑ y, (W r x * W y r') • (fun j j' => X (x, j) (y, j'))) =
                ∑ y, Phi ((W r x * W y r') • (fun j j' => X (x, j) (y, j'))) := by
            exact (map_sum Phi (fun y =>
              (W r x * W y r') • (fun j j' => X (x, j) (y, j')))) Finset.univ
          calc
            (Phi (∑ y, (W r x * W y r') •
                (fun j j' => X (x, j) (y, j')))) b b' =
                (∑ y, Phi ((W r x * W y r') •
                  (fun j j' => X (x, j) (y, j')))) b b' := by
                  exact congrFun (congrFun hmap2 b) b'
            _ = ∑ y, (Phi ((W r x * W y r') •
                  (fun j j' => X (x, j) (y, j')))) b b' := by
                  simp [Matrix.sum_apply]
            _ = ∑ y, W r x *
                  (W y r' * Phi (fun j j' => X (x, j) (y, j')) b b') := by
                  refine Finset.sum_congr rfl fun y _ => ?_
                  have hmap3 :
                      Phi ((W r x * W y r') • (fun j j' => X (x, j) (y, j'))) =
                        (W r x * W y r') • Phi (fun j j' => X (x, j) (y, j')) := by
                    exact map_smul Phi (W r x * W y r') (fun j j' => X (x, j) (y, j'))
                  calc
                    (Phi ((W r x * W y r') •
                        (fun j j' => X (x, j) (y, j')))) b b' =
                        ((W r x * W y r') •
                          Phi (fun j j' => X (x, j) (y, j'))) b b' := by
                          exact congrFun (congrFun hmap3 b) b'
                    _ = W r x *
                        (W y r' * Phi (fun j j' => X (x, j) (y, j')) b b') := by
                        rw [Matrix.smul_apply]
                        ring
    _ = ∑ u, ∑ x, W r u *
          (W x r' * Phi (fun j j' => X (u, j) (x, j')) b b') := by
          rfl

theorem canonicalPurification_referenceSandwich_state_eq_cbOneToAlphaOriginalInput
    (tau : State a1) {alpha : ℝ} (halpha : 1 < alpha) :
    Matrix.kronecker
        (CFC.rpow tau.matrix ((1 - alpha) / (2 * alpha))) (1 : CMatrix a1) *
          (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)).state.matrix *
        Matrix.kronecker
          (CFC.rpow tau.matrix ((1 - alpha) / (2 * alpha))) (1 : CMatrix a1) =
      MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let R : CMatrix a1 := CFC.rpow tau.matrix (1 / (2 * alpha))
  let W : CMatrix a1 := CFC.rpow tau.matrix s
  have hs_den : (1 - alpha) / (alpha * 2) = s := by
    dsimp [s]
    ring
  have hsqrt_left :
      CFC.rpow tau.matrix s * tau.sqrtMatrix = R := by
    rw [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
    change tau.matrix ^ s * tau.matrix ^ (1 / 2 : ℝ) = R
    simpa [s, R] using cMatrix_sandwiched_left_rpow_mul_sqrt tau.pos halpha
  have hsqrt_right :
      tau.sqrtMatrix * CFC.rpow tau.matrix s = R := by
    rw [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
    change tau.matrix ^ (1 / 2 : ℝ) * tau.matrix ^ s = R
    simpa [s, R] using cMatrix_sqrt_mul_sandwiched_left_rpow tau.pos halpha
  have hleftEntry (i j : a1) :
      (∑ x : a1, W i x * tau.sqrtMatrix x j) =
        R i j := by
    have happ := congrFun (congrFun hsqrt_left i) j
    simpa [Matrix.mul_apply, W, R] using happ
  have hrightEntry (i j : a1) :
      (∑ x : a1, tau.sqrtMatrix i x * W x j) =
        R i j := by
    have happ := congrFun (congrFun hsqrt_right i) j
    simpa [Matrix.mul_apply, W, R] using happ
  have hcanon :
      (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)).state.matrix =
        rankOneMatrix (fun ra : Prod a1 a1 => tau.sqrtMatrix ra.1 ra.2) := by
    ext ra ra'
    rcases ra with ⟨r, x⟩
    rcases ra' with ⟨r', x'⟩
    simp [PureVector.reindex_state, State.reindex, PureVector.state_matrix,
      rankOneMatrix_apply, State.canonicalPurification, State.canonicalPurificationAmp]
  have hrightEntryStar (i j : a1) :
      (∑ x : a1, star (tau.sqrtMatrix x i) * W x j) =
        R i j := by
    calc
      (∑ x : a1, star (tau.sqrtMatrix x i) * W x j) =
          ∑ x : a1, tau.sqrtMatrix i x * W x j := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [← tau.sqrtMatrix_isHermitian.apply i x]
      _ = R i j := hrightEntry i j
  have hinput :
      MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha =
        rankOneMatrix (fun ra : Prod a1 a1 => R ra.1 ra.2) := by
    simpa [R] using
      MatrixMap.cbOneToAlphaOriginalInput_eq_rankOne_rpow tau.pos alpha
  rw [hinput]
  rw [hcanon]
  ext ra ra'
  rcases ra with ⟨r, x⟩
  rcases ra' with ⟨r', x'⟩
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, rankOneMatrix_apply]
  calc
    (∑ y : Prod a1 a1,
        (∑ z : Prod a1 a1,
          (CFC.rpow tau.matrix ((1 - alpha) / (2 * alpha)) r z.1 *
              (if x = z.2 then 1 else 0)) *
            (tau.sqrtMatrix z.1 z.2 * star (tau.sqrtMatrix y.1 y.2))) *
          (CFC.rpow tau.matrix ((1 - alpha) / (2 * alpha)) y.1 r' *
              (if y.2 = x' then 1 else 0))) =
        (∑ u : a1, W r u * tau.sqrtMatrix u x) *
          (∑ v : a1, star (tau.sqrtMatrix v x') * W v r') := by
          simp [W, Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm,
            Finset.sum_mul, Finset.mul_sum, hs_den]
    _ = R r x * R x' r' := by
          rw [hleftEntry r x, hrightEntryStar x' r']
    _ = R r x * star (R r' x') := by
          have hRherm :
              R.IsHermitian :=
            (cMatrix_rpow_posSemidef (A := tau.matrix)
              (s := 1 / (2 * alpha)) tau.pos).isHermitian
          rw [hRherm.apply]

/-- The full-rank KW weighting map for a product reference composes with a
product channel map as the product of the individually weighted channel maps. -/
theorem sandwichedSideWeightMap_prod_comp_kron_posDef
    (sigma1 : State b1) (sigma2 : State b2)
    (Phi1 : MatrixMap a1 b1) (Phi2 : MatrixMap a2 b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    (alpha : ℝ) :
    (sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
        (MatrixMap.kron Phi1 Phi2) =
      MatrixMap.kron ((sandwichedSideWeightMap sigma1 alpha).comp Phi1)
        ((sandwichedSideWeightMap sigma2 alpha).comp Phi2) := by
  rw [sandwichedSideWeightMap_prod_posDef sigma1 sigma2 hsigma1 hsigma2 alpha]
  ext X bd bd'
  exact congrFun (congrFun
    (kron_comp_apply_general_local
      (sandwichedSideWeightMap sigma1 alpha)
      (sandwichedSideWeightMap sigma2 alpha)
      Phi1 Phi2 X) bd) bd'

private theorem cbOneToAlphaNorm_congr_map_additivity
    {Phi Psi : MatrixMap a1 b1}
    (hmap : Phi = Psi)
    (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (hPsi : MatrixMap.IsCompletelyPositive Psi)
    (alpha : ℝ) :
    MatrixMap.cbOneToAlphaNorm Phi hPhi alpha =
      MatrixMap.cbOneToAlphaNorm Psi hPsi alpha := by
  subst hmap
  rfl

/-- Full-rank product-reference instance of the KW CB-norm multiplicativity
step for the weighted channel maps. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightMap_prod_comp_kron_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (sigma1 : State b1) (sigma2 : State b2)
    (Phi1 : MatrixMap a1 b1) (hPhi1 : MatrixMap.IsCompletelyPositive Phi1)
    (Phi2 : MatrixMap a2 b2) (hPhi2 : MatrixMap.IsCompletelyPositive Phi2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm
        ((sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
          (MatrixMap.kron Phi1 Phi2))
        (MatrixMap.isCompletelyPositive_comp _ _
          (sandwichedSideWeightMap_completelyPositive (sigma1.prod sigma2) alpha)
          (MatrixMap.isCompletelyPositive_kron Phi1 Phi2 hPhi1 hPhi2))
        alpha =
      MatrixMap.cbOneToAlphaNorm
          ((sandwichedSideWeightMap sigma1 alpha).comp Phi1)
          (MatrixMap.isCompletelyPositive_comp _ _
            (sandwichedSideWeightMap_completelyPositive sigma1 alpha) hPhi1)
          alpha *
        MatrixMap.cbOneToAlphaNorm
          ((sandwichedSideWeightMap sigma2 alpha).comp Phi2)
          (MatrixMap.isCompletelyPositive_comp _ _
            (sandwichedSideWeightMap_completelyPositive sigma2 alpha) hPhi2)
          alpha := by
  let Tprod : MatrixMap (Prod a1 a2) (Prod b1 b2) :=
    (sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
      (MatrixMap.kron Phi1 Phi2)
  let T1 : MatrixMap a1 b1 := (sandwichedSideWeightMap sigma1 alpha).comp Phi1
  let T2 : MatrixMap a2 b2 := (sandwichedSideWeightMap sigma2 alpha).comp Phi2
  let hTprod : MatrixMap.IsCompletelyPositive Tprod :=
    MatrixMap.isCompletelyPositive_comp _ _
      (sandwichedSideWeightMap_completelyPositive (sigma1.prod sigma2) alpha)
      (MatrixMap.isCompletelyPositive_kron Phi1 Phi2 hPhi1 hPhi2)
  let hT1 : MatrixMap.IsCompletelyPositive T1 :=
    MatrixMap.isCompletelyPositive_comp _ _
      (sandwichedSideWeightMap_completelyPositive sigma1 alpha) hPhi1
  let hT2 : MatrixMap.IsCompletelyPositive T2 :=
    MatrixMap.isCompletelyPositive_comp _ _
      (sandwichedSideWeightMap_completelyPositive sigma2 alpha) hPhi2
  have hTprod_eq : Tprod = MatrixMap.kron T1 T2 := by
    dsimp [Tprod, T1, T2]
    exact sandwichedSideWeightMap_prod_comp_kron_posDef
      sigma1 sigma2 Phi1 Phi2 hsigma1 hsigma2 alpha
  change MatrixMap.cbOneToAlphaNorm Tprod hTprod alpha =
    MatrixMap.cbOneToAlphaNorm T1 hT1 alpha *
      MatrixMap.cbOneToAlphaNorm T2 hT2 alpha
  calc
    MatrixMap.cbOneToAlphaNorm Tprod hTprod alpha =
      MatrixMap.cbOneToAlphaNorm (MatrixMap.kron T1 T2)
        (MatrixMap.isCompletelyPositive_kron T1 T2 hT1 hT2) alpha := by
          exact cbOneToAlphaNorm_congr_map_additivity hTprod_eq hTprod
            (MatrixMap.isCompletelyPositive_kron T1 T2 hT1 hT2) alpha
    _ = MatrixMap.cbOneToAlphaNorm T1 hT1 alpha *
        MatrixMap.cbOneToAlphaNorm T2 hT2 alpha := by
          exact MatrixMap.cbOneToAlphaNorm_kron_eq_mul T1 hT1 T2 hT2 halpha

end MatrixMap

namespace Channel

variable {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
variable [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
variable [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]

/-- Matrix form of a pure input-reference output, matching the `referenceLift`
input used by the KW CB-norm quotient. -/
theorem hypothesisTestingOutputState_matrix_referenceLift
    (N : Channel a1 b1) (ψ : PureVector (Prod a1 a1)) :
    (N.hypothesisTestingOutputState ψ).matrix =
      MatrixMap.referenceLift N.map ψ.state.matrix := by
  rfl

/-- The reference marginal is untouched by the channel output state
`(id_R ⊗ N)(|ψ⟩⟨ψ|)`. -/
theorem hypothesisTestingOutputState_marginalA
    (N : Channel a1 b1) (ψ : PureVector (Prod a1 a1)) :
    (N.hypothesisTestingOutputState ψ).marginalA = ψ.state.marginalA := by
  unfold Channel.hypothesisTestingOutputState
  exact State.marginalA_applyState_id_prod ψ.state N

/-- Sandwiched mutual information of a channel output is monotone under
reference-side isometries.

This is the channel-output form of the KW purification-equivalence step:
`N` commutes with the reference isometry, and the resulting reference-side
post-processing is handled by the optimized state sandwiched-Renyi DPI. -/
theorem hypothesisTestingOutputState_applyReferenceIsometry_sandwichedRenyiMutualInformationE_le
    {r1 : Type u1} {r2 : Type u2}
    [Fintype r1] [DecidableEq r1] [Fintype r2] [DecidableEq r2]
    (N : Channel a1 b1) (V : ReferenceIsometry r1 r2)
    (ψ : PureVector (Prod r1 a1)) {alpha : Real} (halpha : 1 < alpha) :
    (N.hypothesisTestingOutputState (V.applyPureVector ψ)).sandwichedRenyiMutualInformationE
        alpha ≤
      (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha := by
  rw [N.hypothesisTestingOutputState_applyReferenceIsometry V ψ]
  exact State.sandwichedRenyiMutualInformationE_dataProcessing_left
    (N.hypothesisTestingOutputState ψ) (Channel.ofReferenceIsometry V) halpha

/-- Arbitrary-reference pure inputs whose reference system contains an
input-copy reference are bounded by the optimized channel sandwiched-Renyi
mutual information.

This is the sandwiched-Renyi analogue of the hypothesis-testing purification
bridge: replace an arbitrary purification by the canonical purification of its
input marginal, then use reference-side data processing. -/
theorem hypothesisTestingOutputState_sandwichedRenyiMutualInformationE_le_channel_of_card_le
    (N : Channel a1 b1) {r : Type u2} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a1)) {alpha : Real} (halpha : 1 < alpha)
    (hcard : Fintype.card a1 ≤ Fintype.card r) :
    (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  let φ : PureVector (Prod a1 a1) := ψ.state.marginalB.canonicalPurification
  have hφ : φ.Purifies ψ.state.marginalB := by
    exact ψ.state.marginalB.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.marginalB :=
    ψ.purifies_marginalB_forHypothesisTestingDPI
  rcases PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.hypothesisTestingOutputState ψ =
        ((Channel.ofReferenceIsometry V).prod (Channel.idChannel b1)).applyState
          (N.hypothesisTestingOutputState φ) := by
    rw [hV]
    exact N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  rw [hout]
  exact (State.sandwichedRenyiMutualInformationE_dataProcessing_left
      (N.hypothesisTestingOutputState φ) (Channel.ofReferenceIsometry V) halpha).trans
    (N.inputSandwichedRenyiMutualInformationE_le_channel φ alpha)

omit [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2] in
/-- Pure inputs with an input-copy reference are bounded by the canonical
purification of their input marginal.

This is the KW purification-equivalence step before the support/full-rank
analysis of the input marginal: every input-copy purification is a
reference-side isometric image of the canonical purification of the same input
state, and optimized sandwiched mutual information is monotone under that
reference-side post-processing. -/
theorem hypothesisTestingOutputState_sandwichedRenyiMutualInformationE_le_canonical_marginalB
    (N : Channel a1 b1) (ψ : PureVector (Prod a1 a1))
    {alpha : Real} (halpha : 1 < alpha) :
    (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha ≤
      (N.hypothesisTestingOutputState
        ψ.state.marginalB.canonicalPurification).sandwichedRenyiMutualInformationE
          alpha := by
  let φ : PureVector (Prod a1 a1) := ψ.state.marginalB.canonicalPurification
  change (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha ≤
    (N.hypothesisTestingOutputState φ).sandwichedRenyiMutualInformationE alpha
  have hφ : φ.Purifies ψ.state.marginalB := by
    exact ψ.state.marginalB.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.marginalB :=
    ψ.purifies_marginalB_forHypothesisTestingDPI
  rcases PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hφ hψ (Nat.le_refl (Fintype.card a1)) with ⟨V, hV⟩
  rw [hV]
  exact
    N.hypothesisTestingOutputState_applyReferenceIsometry_sandwichedRenyiMutualInformationE_le
      V φ halpha

/-- The KW weighted channel map `S_sigma^(alpha) ∘ N` from
`EA_capacity.tex:1242-1254`. -/
def sandwichedSideWeightedMap (N : Channel a1 b1) (sigma : State b1) (alpha : ℝ) :
    MatrixMap a1 b1 :=
  (MatrixMap.sandwichedSideWeightMap sigma alpha).comp N.map

/-- Source form of the KW weighted channel map:
`(S_sigma^(alpha) o N)(X) = sigma^s N(X) sigma^s`. -/
theorem sandwichedSideWeightedMap_apply_source
    (N : Channel a1 b1) (sigma : State b1) (alpha : ℝ) (X : CMatrix a1) :
    sandwichedSideWeightedMap N sigma alpha X =
      CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)) *
        (N.map X) *
        CFC.rpow sigma.matrix ((1 - alpha) / (2 * alpha)) := by
  rw [sandwichedSideWeightedMap]
  change MatrixMap.sandwichedSideWeightMap sigma alpha (N.map X) = _
  exact MatrixMap.sandwichedSideWeightMap_apply_source sigma alpha (N.map X)

/-- Complete positivity of the KW weighted channel map. -/
theorem sandwichedSideWeightedMap_completelyPositive
    (N : Channel a1 b1) (sigma : State b1) (alpha : ℝ) :
    MatrixMap.IsCompletelyPositive (sandwichedSideWeightedMap N sigma alpha) :=
  MatrixMap.isCompletelyPositive_comp _ _
    (MatrixMap.sandwichedSideWeightMap_completelyPositive sigma alpha)
    N.completelyPositive

/-- The KW weighted channel map preserves positive semidefinite inputs. -/
theorem sandwichedSideWeightedMap_mapsPositive
    (N : Channel a1 b1) (sigma : State b1) (alpha : ℝ)
    {X : CMatrix a1} (hX : X.PosSemidef) :
    (sandwichedSideWeightedMap N sigma alpha X).PosSemidef :=
  MatrixMap.isCompletelyPositive_mapsPositive (sandwichedSideWeightedMap N sigma alpha)
    (sandwichedSideWeightedMap_completelyPositive N sigma alpha) X hX

theorem swappedCanonical_referenceInner_eq_referenceLift_cbOneToAlphaOriginalInput
    (N : Channel a1 b1) (sigma : State b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    let psi := tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
    State.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix alpha =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha) := by
  intro psi
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let Wtau : CMatrix a1 := CFC.rpow tau.matrix s
  let Wsigma : CMatrix b1 := CFC.rpow sigma.matrix s
  have hmarg : (N.hypothesisTestingOutputState psi).marginalA = tau := by
    calc
      (N.hypothesisTestingOutputState psi).marginalA = psi.state.marginalA :=
        Channel.hypothesisTestingOutputState_marginalA N psi
      _ = tau := by
        simpa [psi] using State.canonicalPurification_reindex_prodComm_marginalA tau
  have hstateSandwich :
      Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.matrix *
          Matrix.kronecker Wtau (1 : CMatrix a1) =
        MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha := by
    simpa [psi, Wtau, s] using
      MatrixMap.canonicalPurification_referenceSandwich_state_eq_cbOneToAlphaOriginalInput
        tau halpha
  have hreferenceSandwich :
      MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.matrix *
            Matrix.kronecker Wtau (1 : CMatrix a1)) =
        Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.matrix *
          Matrix.kronecker Wtau (1 : CMatrix b1) := by
    exact MatrixMap.referenceLift_referenceSandwich N.map Wtau psi.state.matrix
  have hBA :
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker ((1 : CMatrix a1) * Wtau)
          (Wsigma * (1 : CMatrix b1)) := by
            exact (Matrix.mul_kronecker_mul
              (1 : CMatrix a1) Wtau Wsigma (1 : CMatrix b1)).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hAB :
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker (Wtau * (1 : CMatrix a1))
          ((1 : CMatrix b1) * Wsigma) := by
            exact (Matrix.mul_kronecker_mul
              Wtau (1 : CMatrix a1) (1 : CMatrix b1) Wsigma).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hpow :
      CFC.rpow (Matrix.kronecker tau.matrix sigma.matrix) s =
        Matrix.kronecker Wtau Wsigma := by
    simpa [Wtau, Wsigma] using
      State.cMatrix_rpow_kronecker_posSemidef_support tau.pos sigma.pos s
  calc
    State.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix alpha
        =
      Matrix.kronecker Wtau Wsigma *
        MatrixMap.referenceLift N.map psi.state.matrix *
        Matrix.kronecker Wtau Wsigma := by
          unfold State.sandwichedRenyiReferenceInner
          change
            CFC.rpow ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix s *
                (N.hypothesisTestingOutputState psi).matrix *
              CFC.rpow ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix s =
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.matrix *
              Matrix.kronecker Wtau Wsigma
          rw [hmarg, State.prod_matrix_kronecker, hpow]
          rw [Channel.hypothesisTestingOutputState_matrix_referenceLift]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        (Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.matrix *
          Matrix.kronecker Wtau (1 : CMatrix b1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          calc
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.matrix *
              Matrix.kronecker Wtau Wsigma =
              (Matrix.kronecker (1 : CMatrix a1) Wsigma *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                MatrixMap.referenceLift N.map psi.state.matrix *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  Matrix.kronecker (1 : CMatrix a1) Wsigma) := by
                  rw [hBA, hAB]
            _ =
              Matrix.kronecker (1 : CMatrix a1) Wsigma *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  MatrixMap.referenceLift N.map psi.state.matrix *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
                  noncomm_ring
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.matrix *
            Matrix.kronecker Wtau (1 : CMatrix a1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hreferenceSandwich]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map
          (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hstateSandwich]
    _ =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha) := by
          rw [sandwichedSideWeightedMap]
          rw [MatrixMap.referenceLift_comp_apply]
          rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
          have hWherm : Wsigma.conjTranspose = Wsigma := by
            exact (cMatrix_rpow_posSemidef (A := sigma.matrix) (s := s) sigma.pos).isHermitian.eq
          have hDherm :
              (Matrix.kronecker (1 : CMatrix a1) Wsigma).conjTranspose =
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
            exact (Matrix.PosSemidef.one.kronecker
              (cMatrix_rpow_posSemidef (A := sigma.matrix) (s := s) sigma.pos)).isHermitian.eq
          rw [hDherm]

/-- Local support-convention Kronecker rule for matrix real powers.

The public theorem `cMatrix_rpow_kronecker_nonneg` covers PSD matrices with
nonnegative exponents, while the KW weighted input route needs the negative
exponent `s = (1 - alpha) / (2 * alpha)`.  This proof follows the existing
finite-dimensional diagonal/unitary route from `QIT.States.Schatten`, where
zero eigenvalues are handled by the repository's `0^s = 0` support convention. -/
private theorem cMatrix_rpow_kronecker_posSemidef_support
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    {A : CMatrix x} {B : CMatrix y} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : ℝ) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) := by
  let UA := hA.isHermitian.eigenvectorUnitary
  let UB := hB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod x y) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix x) (UB : CMatrix y),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let da : x → ℝ := hA.isHermitian.eigenvalues
  let db : y → ℝ := hB.isHermitian.eigenvalues
  let dprod : Prod x y → ℝ := fun i => da i.1 * db i.2
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
    simp [U, dprod, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  have hA_rpow :
      CFC.rpow A s =
        Unitary.conjStarAlgAut ℂ _ UA
          (Matrix.diagonal (fun i => ((da i ^ s : ℝ) : ℂ))) := by
    rw [hA_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal UA da hda s
  have hB_rpow :
      CFC.rpow B s =
        Unitary.conjStarAlgAut ℂ _ UB
          (Matrix.diagonal (fun i => ((db i ^ s : ℝ) : ℂ))) := by
    rw [hB_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal UB db hdb s
  have hleft :
      CFC.rpow (Matrix.kronecker A B) s =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => ((dprod i ^ s : ℝ) : ℂ))) := by
    rw [hAB_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U dprod hdprod s
  have hdiag :
      Matrix.diagonal (fun i : Prod x y => ((dprod i ^ s : ℝ) : ℂ)) =
        Matrix.diagonal
          (fun i : Prod x y => (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [dprod, Real.mul_rpow (hda i.1) (hdb i.2)]
    · simp [Matrix.diagonal, hij]
  have hright :
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal
            (fun i : Prod x y => (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ))) := by
    rw [hA_rpow, hB_rpow]
    simp [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  rw [hleft, hdiag, hright]

/-- Support-convention product rule for the sandwiched `Q` functional.

This is the PSD/high-`alpha` algebra hidden in KW
`EA_capacity.tex:1183-1186`: even when the references are singular, the
repository support convention for `CFC.rpow` makes the tensor-product
Schatten trace factorize. -/
private theorem sandwichedRenyiQ_kronecker_posSemidef_support
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    {rho1 sigma1 : CMatrix x} {rho2 sigma2 : CMatrix y}
    (hrho1 : rho1.PosSemidef) (hsigma1 : sigma1.PosSemidef)
    (hrho2 : rho2.PosSemidef) (hsigma2 : sigma2.PosSemidef)
    (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha) :
    State.sandwichedRenyiQ
        (Matrix.kronecker rho1 rho2)
        (Matrix.kronecker sigma1 sigma2)
        (hrho1.kronecker hrho2) (hsigma1.kronecker hsigma2) alpha =
      State.sandwichedRenyiQ rho1 sigma1 hrho1 hsigma1 alpha *
        State.sandwichedRenyiQ rho2 sigma2 hrho2 hsigma2 alpha := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let C1 : CMatrix x := CFC.rpow sigma1 s
  let C2 : CMatrix y := CFC.rpow sigma2 s
  let inner1 : CMatrix x := C1 * rho1 * C1
  let inner2 : CMatrix y := C2 * rho2 * C2
  have hC :
      CFC.rpow (Matrix.kronecker sigma1 sigma2) s =
        Matrix.kronecker C1 C2 := by
    simpa [C1, C2, s] using
      cMatrix_rpow_kronecker_posSemidef_support hsigma1 hsigma2 s
  have hinner :
      CFC.rpow (Matrix.kronecker sigma1 sigma2) s *
          Matrix.kronecker rho1 rho2 *
          CFC.rpow (Matrix.kronecker sigma1 sigma2) s =
        Matrix.kronecker inner1 inner2 := by
    rw [hC]
    simp [inner1, inner2, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  have hC1_hm : C1.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := sigma1) (s := s) hsigma1).isHermitian
  have hC2_hm : C2.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := sigma2) (s := s) hsigma2).isHermitian
  have hinner1_psd : inner1.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hrho1 C1
    rwa [hC1_hm.eq] at h
  have hinner2_psd : inner2.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hrho2 C2
    rwa [hC2_hm.eq] at h
  have htraceC :
      (CFC.rpow
        (CFC.rpow (Matrix.kronecker sigma1 sigma2) s * Matrix.kronecker rho1 rho2 *
          CFC.rpow (Matrix.kronecker sigma1 sigma2) s) alpha).trace =
        (CFC.rpow inner1 alpha).trace * (CFC.rpow inner2 alpha).trace := by
    rw [hinner]
    rw [cMatrix_rpow_kronecker_nonneg hinner1_psd hinner2_psd halpha_nonneg]
    change
      (Matrix.kroneckerMap (fun x y => x * y)
        (CFC.rpow inner1 alpha) (CFC.rpow inner2 alpha)).trace =
        (CFC.rpow inner1 alpha).trace * (CFC.rpow inner2 alpha).trace
    rw [Matrix.trace_kronecker]
  have him1 : ((CFC.rpow inner1 alpha).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner1 alpha).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner1) (y := alpha)))
    exact htrace_nonneg.2.symm
  have him2 : ((CFC.rpow inner2 alpha).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner2 alpha).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner2) (y := alpha)))
    exact htrace_nonneg.2.symm
  unfold State.sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.kronecker sigma1 sigma2) s * Matrix.kronecker rho1 rho2 *
        CFC.rpow (Matrix.kronecker sigma1 sigma2) s) alpha).trace.re =
      (CFC.rpow inner1 alpha).trace.re * (CFC.rpow inner2 alpha).trace.re
  rw [htraceC, Complex.mul_re, him1, him2]
  ring

/-- Product rule for the supported high-`alpha` finite PSD-reference branch.

This is the finite-branch form of the KW step
`EA_capacity.tex:1183-1186`, where the sandwiched Renyi divergence of product
states against product references splits into the sum of the two divergences.
The hypotheses are exactly support-convention hypotheses, not full-rank
assumptions. -/
private theorem sandwichedRenyiPSDReferenceHighAlphaFinite_prod_of_supports
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    (rho1 : State x) (rho2 : State y)
    {sigma1 : CMatrix x} {sigma2 : CMatrix y}
    (hsigma1 : sigma1.PosSemidef) (hsigma2 : sigma2.PosSemidef)
    (hsupport1 : Matrix.Supports rho1.matrix sigma1)
    (hsupport2 : Matrix.Supports rho2.matrix sigma2)
    {alpha : ℝ} (halpha : 1 < alpha) :
    QIT.State.sandwichedRenyiPSDReferenceHighAlphaFinite (rho1.prod rho2)
        (Matrix.kronecker sigma1 sigma2) (hsigma1.kronecker hsigma2) alpha =
      QIT.State.sandwichedRenyiPSDReferenceHighAlphaFinite rho1 sigma1 hsigma1 alpha +
        QIT.State.sandwichedRenyiPSDReferenceHighAlphaFinite rho2 sigma2 hsigma2 alpha := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hq :=
    sandwichedRenyiQ_kronecker_posSemidef_support
      (rho1 := rho1.matrix) (sigma1 := sigma1)
      (rho2 := rho2.matrix) (sigma2 := sigma2)
      rho1.pos hsigma1 rho2.pos hsigma2 alpha (le_of_lt halpha_pos)
  have htrace :
      psdTracePower
          (QIT.State.sandwichedRenyiReferenceInner (rho1.prod rho2)
            (Matrix.kronecker sigma1 sigma2) alpha)
          (QIT.State.sandwichedRenyiReferenceInner_posSemidef (rho1.prod rho2)
            (hsigma1.kronecker hsigma2) alpha)
          alpha =
        psdTracePower (QIT.State.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
            (QIT.State.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha)
            alpha *
          psdTracePower (QIT.State.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
            (QIT.State.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha)
            alpha := by
    simpa [QIT.State.sandwichedRenyiQ, QIT.State.sandwichedRenyiReferenceInner,
      State.prod_matrix_kronecker, psdTracePower] using hq
  have hq1_pos :
      0 < psdTracePower (QIT.State.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
          (QIT.State.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha)
          alpha :=
    QIT.State.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
      rho1 hsigma1 hsupport1 alpha
  have hq2_pos :
      0 < psdTracePower (QIT.State.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
          (QIT.State.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha)
          alpha :=
    QIT.State.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
      rho2 hsigma2 hsupport2 alpha
  unfold QIT.State.sandwichedRenyiPSDReferenceHighAlphaFinite
  rw [htrace]
  rw [log2_mul (ne_of_gt hq1_pos) (ne_of_gt hq2_pos)]
  ring

/-- KW weighted rank-one alternate expression for an arbitrary pure input.

This is the channel-side version of the polar-decomposition step in
`EA_capacity.tex:2054-2093`: sandwiching the channel output by
`rho_R^s \otimes sigma_B^s` is the same as first sandwiching the pure input on
the reference register by `rho_R^s`, then applying the weighted channel map
`S_sigma^(alpha) o N`. -/
theorem referenceInner_eq_referenceLift_weightedRankOne
    (N : Channel a1 b1) (sigma : State b1) (psi : PureVector (Prod a1 a1))
    (hsigma : sigma.matrix.PosDef)
    {alpha : ℝ} (_halpha : 1 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    let weighted : Prod a1 a1 → ℂ :=
      Matrix.mulVec
        (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix s) (1 : CMatrix a1))
        psi.amp
    State.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix alpha =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (rankOneMatrix weighted) := by
  intro s weighted
  let Wtau : CMatrix a1 := CFC.rpow psi.state.marginalA.matrix s
  let Wsigma : CMatrix b1 := CFC.rpow sigma.matrix s
  let M : CMatrix (Prod a1 a1) := Matrix.kronecker Wtau (1 : CMatrix a1)
  have hmarg :
      (N.hypothesisTestingOutputState psi).marginalA = psi.state.marginalA :=
    Channel.hypothesisTestingOutputState_marginalA N psi
  have hMherm : M.conjTranspose = M := by
    exact (Matrix.PosSemidef.kronecker
      (cMatrix_rpow_posSemidef (A := psi.state.marginalA.matrix) (s := s)
        psi.state.marginalA.pos)
      Matrix.PosSemidef.one).isHermitian.eq
  have hrank :
      rankOneMatrix (M.mulVec psi.amp) =
        M * rankOneMatrix psi.amp * Matrix.conjTranspose M := by
    rw [rankOneMatrix, rankOneMatrix]
    rw [Matrix.mul_vecMulVec]
    rw [Matrix.vecMulVec_mul]
    congr
    ext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]
  have hstateSandwich :
      Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.matrix *
          Matrix.kronecker Wtau (1 : CMatrix a1) =
        rankOneMatrix weighted := by
    calc
      Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.matrix *
          Matrix.kronecker Wtau (1 : CMatrix a1) =
        M * rankOneMatrix psi.amp * Matrix.conjTranspose M := by
          rw [PureVector.state_matrix]
          change M * rankOneMatrix psi.amp * M =
            M * rankOneMatrix psi.amp * Matrix.conjTranspose M
          rw [hMherm]
      _ = rankOneMatrix (M.mulVec psi.amp) := hrank.symm
      _ = rankOneMatrix weighted := by
          rfl
  have hreferenceSandwich :
      MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.matrix *
            Matrix.kronecker Wtau (1 : CMatrix a1)) =
        Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.matrix *
          Matrix.kronecker Wtau (1 : CMatrix b1) := by
    exact MatrixMap.referenceLift_referenceSandwich N.map Wtau psi.state.matrix
  have hBA :
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker ((1 : CMatrix a1) * Wtau)
          (Wsigma * (1 : CMatrix b1)) := by
            exact (Matrix.mul_kronecker_mul
              (1 : CMatrix a1) Wtau Wsigma (1 : CMatrix b1)).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hAB :
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker (Wtau * (1 : CMatrix a1))
          ((1 : CMatrix b1) * Wsigma) := by
            exact (Matrix.mul_kronecker_mul
              Wtau (1 : CMatrix a1) (1 : CMatrix b1) Wsigma).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hpow :
      CFC.rpow (Matrix.kronecker psi.state.marginalA.matrix sigma.matrix) s =
        Matrix.kronecker Wtau Wsigma := by
    simpa [Wtau, Wsigma] using
      cMatrix_rpow_kronecker_posSemidef_support
        psi.state.marginalA.pos hsigma.posSemidef s
  calc
    State.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix alpha
        =
      Matrix.kronecker Wtau Wsigma *
        MatrixMap.referenceLift N.map psi.state.matrix *
        Matrix.kronecker Wtau Wsigma := by
          unfold State.sandwichedRenyiReferenceInner
          change
            CFC.rpow ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix s *
                (N.hypothesisTestingOutputState psi).matrix *
              CFC.rpow ((N.hypothesisTestingOutputState psi).marginalA.prod sigma).matrix s =
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.matrix *
              Matrix.kronecker Wtau Wsigma
          rw [hmarg, State.prod_matrix_kronecker, hpow]
          rw [Channel.hypothesisTestingOutputState_matrix_referenceLift]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        (Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.matrix *
          Matrix.kronecker Wtau (1 : CMatrix b1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          calc
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.matrix *
              Matrix.kronecker Wtau Wsigma =
              (Matrix.kronecker (1 : CMatrix a1) Wsigma *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                MatrixMap.referenceLift N.map psi.state.matrix *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  Matrix.kronecker (1 : CMatrix a1) Wsigma) := by
                  rw [hBA, hAB]
            _ =
              Matrix.kronecker (1 : CMatrix a1) Wsigma *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  MatrixMap.referenceLift N.map psi.state.matrix *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
                  noncomm_ring
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.matrix *
            Matrix.kronecker Wtau (1 : CMatrix a1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hreferenceSandwich]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map (rankOneMatrix weighted) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hstateSandwich]
    _ =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (rankOneMatrix weighted) := by
          rw [sandwichedSideWeightedMap]
          rw [MatrixMap.referenceLift_comp_apply]
          rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
          have hDherm :
              (Matrix.kronecker (1 : CMatrix a1) Wsigma).conjTranspose =
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
            exact (Matrix.PosSemidef.one.kronecker
              (cMatrix_rpow_posSemidef (A := sigma.matrix) (s := s) sigma.pos)).isHermitian.eq
          rw [hDherm]

/-- The KW weighted rank-one input has normalized Schatten-`alpha`
denominator.

For `tau_R = psi_R`, applying the reference weight
`tau_R^((1-alpha)/(2 alpha))` to `|psi><psi|` leaves reference marginal
`tau_R^(1/alpha)`, whose Schatten-`alpha` norm is one.  This is exactly the
normalization step used in `EA_capacity.tex:2052-2058`. -/
theorem weightedRankOne_denominator_eq_one
    (psi : PureVector (Prod a1 a1)) (hA : psi.state.marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 0 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    let weighted : Prod a1 a1 → ℂ :=
      Matrix.mulVec
        (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix s) (1 : CMatrix a1))
        psi.amp
    psdSchattenPNorm
        (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
        (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
        alpha =
      1 := by
  intro s weighted
  let tau : State a1 := psi.state.marginalA
  let W : CMatrix a1 := CFC.rpow tau.matrix s
  have hWherm : Matrix.conjTranspose W = W :=
    (cMatrix_rpow_posSemidef (A := tau.matrix) (s := s) tau.pos).isHermitian.eq
  have hnonneg : 0 ≤ tau.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr tau.pos
  have hpow_one : CFC.rpow tau.matrix (1 : ℝ) = tau.matrix :=
    CFC.rpow_one tau.matrix (ha := hnonneg)
  have hs_left :
      CFC.rpow tau.matrix s * tau.matrix = CFC.rpow tau.matrix (s + 1) := by
    calc
      CFC.rpow tau.matrix s * tau.matrix =
          CFC.rpow tau.matrix s * CFC.rpow tau.matrix (1 : ℝ) := by
            rw [hpow_one]
      _ = CFC.rpow tau.matrix (s + 1) := by
            exact (CFC.rpow_add (a := tau.matrix) (x := s) (y := 1) hA.isUnit).symm
  have hs_total :
      CFC.rpow tau.matrix (s + 1) * CFC.rpow tau.matrix s =
        CFC.rpow tau.matrix ((s + 1) + s) := by
    exact (CFC.rpow_add (a := tau.matrix) (x := s + 1) (y := s) hA.isUnit).symm
  have hexp : (s + 1) + s = 1 / alpha := by
    dsimp [s]
    field_simp [ne_of_gt halpha]
    ring
  have hsand :
      W * tau.matrix * Matrix.conjTranspose W = CFC.rpow tau.matrix (1 / alpha) := by
    calc
      W * tau.matrix * Matrix.conjTranspose W =
          CFC.rpow tau.matrix s * tau.matrix * CFC.rpow tau.matrix s := by
            rw [hWherm]
      _ = (CFC.rpow tau.matrix s * tau.matrix) * CFC.rpow tau.matrix s := by
            rw [Matrix.mul_assoc]
      _ = CFC.rpow tau.matrix (s + 1) * CFC.rpow tau.matrix s := by
            rw [hs_left]
      _ = CFC.rpow tau.matrix ((s + 1) + s) := hs_total
      _ = CFC.rpow tau.matrix (1 / alpha) := by rw [hexp]
  have hmatrix :
      partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted) =
        CFC.rpow tau.matrix (1 / alpha) := by
    calc
      partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted) =
          W * partialTraceB (a := a1) (b := a1) (rankOneMatrix psi.amp) *
            Matrix.conjTranspose W := by
            simpa [weighted, W, tau] using
              PureVector.partialTraceB_rankOne_kron_left_mulVec_eq
                (d := a1) (c := a1) W psi.amp
      _ = W * tau.matrix * Matrix.conjTranspose W := by
            simp [tau, State.marginalA_matrix, PureVector.state_matrix]
      _ = CFC.rpow tau.matrix (1 / alpha) := hsand
  calc
    psdSchattenPNorm
        (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
        (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
        alpha =
      psdSchattenPNorm
        (CFC.rpow tau.matrix (1 / alpha))
        (tau.rpowMatrix_posSemidef (1 / alpha))
        alpha := by
          exact psdSchattenPNorm_congr hmatrix _ _ alpha
    _ = 1 := State.state_rpow_one_div_psdSchattenPNorm_eq_one tau hA alpha halpha

/-- Support-convention version of
`weightedRankOne_denominator_eq_one`.

For `alpha > 1`, the same KW weighted rank-one input is normalized without
assuming that the input/reference marginal is full rank.  The only new
ingredient is the PSD support algebra
`State.rpow_sandwich_self_eq_rpow_one_div`. -/
theorem weightedRankOne_denominator_eq_one_psd
    (psi : PureVector (Prod a1 a1)) {alpha : ℝ} (halpha : 1 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    let weighted : Prod a1 a1 → ℂ :=
      Matrix.mulVec
        (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix s) (1 : CMatrix a1))
        psi.amp
    psdSchattenPNorm
        (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
        (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
        alpha =
      1 := by
  intro s weighted
  let tau : State a1 := psi.state.marginalA
  let W : CMatrix a1 := CFC.rpow tau.matrix s
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hWherm : Matrix.conjTranspose W = W :=
    (cMatrix_rpow_posSemidef (A := tau.matrix) (s := s) tau.pos).isHermitian.eq
  have hsand :
      W * tau.matrix * Matrix.conjTranspose W = CFC.rpow tau.matrix (1 / alpha) := by
    calc
      W * tau.matrix * Matrix.conjTranspose W = W * tau.matrix * W := by
        rw [hWherm]
      _ = CFC.rpow tau.matrix (1 / alpha) := by
        simpa [s, W] using
          (State.rpow_sandwich_self_eq_rpow_one_div tau halpha)
  have hmatrix :
      partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted) =
        CFC.rpow tau.matrix (1 / alpha) := by
    calc
      partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted) =
          W * partialTraceB (a := a1) (b := a1) (rankOneMatrix psi.amp) *
            Matrix.conjTranspose W := by
            simpa [weighted, W, tau] using
              PureVector.partialTraceB_rankOne_kron_left_mulVec_eq
                (d := a1) (c := a1) W psi.amp
      _ = W * tau.matrix * Matrix.conjTranspose W := by
            simp [tau, State.marginalA_matrix, PureVector.state_matrix]
      _ = CFC.rpow tau.matrix (1 / alpha) := hsand
  calc
    psdSchattenPNorm
        (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
        (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
        alpha =
      psdSchattenPNorm
        (CFC.rpow tau.matrix (1 / alpha))
        (tau.rpowMatrix_posSemidef (1 / alpha))
        alpha := by
          exact psdSchattenPNorm_congr hmatrix _ _ alpha
    _ = 1 := State.state_rpow_one_div_psdSchattenPNorm_eq_one_psd tau halpha_pos

/-- The reference lift of a full-rank KW weighted channel map preserves
nonzero PSD inputs. -/
theorem sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
    (N : Channel a1 b1) (sigma : State b1) (hsigma : sigma.matrix.PosDef)
    (alpha : ℝ) {X : CMatrix (Prod a1 a1)}
    (hX : X.PosSemidef) (hXne : X ≠ 0) :
    MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 := by
  rw [sandwichedSideWeightedMap]
  rw [MatrixMap.referenceLift_comp_apply]
  have hNXne : MatrixMap.referenceLift N.map X ≠ 0 :=
    MatrixMap.referenceLift_apply_ne_zero_of_tracePreserving
      N.map N.tracePreserving hX hXne
  exact MatrixMap.referenceKron_sandwichedSideWeightMap_apply_ne_zero_of_posDef
    sigma hsigma alpha hNXne

/-- Real-valued CB-norm expression from the KW alternate expression before
identifying it with optimized sandwiched EA mutual information. -/
def sandwichedRenyiCBNormExpression
    (N : Channel a1 b1) (sigma : State b1) (alpha : ℝ) : ℝ :=
  alpha / (alpha - 1) *
    log2 (MatrixMap.cbOneToAlphaNorm
      (sandwichedSideWeightedMap N sigma alpha)
      (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
      alpha)

/-- KW alternate-expression form of the weighted-channel logarithmic integrand.

This is the direct specialization of
`MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression` to the
side-weighted channel map used in the EA sandwiched mutual information proof. -/
theorem sandwichedRenyiCBNormExpression_eq_cbAlternateExpression
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedRenyiCBNormExpression N sigma alpha =
      alpha / (alpha - 1) *
        log2 (MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          alpha) := by
  unfold sandwichedRenyiCBNormExpression
  rw [MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N sigma alpha)
    (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
    halpha]

/-- Order bridge from a pointwise fixed-input CB upper bound to the optimized
channel alternate-expression upper bound.

This is the `sup_psi`/`inf_sigma` bookkeeping in KW
`EA_capacity.tex:2039-2093`.  The hypothesis is the remaining pointwise
matrix-analytic step: for every pure input and every full-rank side state, the
input sandwiched-Renyi objective is bounded by the corresponding weighted
CB expression. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_of_input_le
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) (alpha : ℝ)
    (hBelow :
      BddBelow (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha))
    (hinput :
      ∀ psi : PureVector (Prod a1 a1),
        ∀ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          N.inputSandwichedRenyiMutualInformationE psi alpha ≤
            ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  let S := {sigma : State b1 // sigma.matrix.PosDef}
  haveI : Nonempty S := ⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩
  let f : S → ℝ := fun sigma =>
    sandwichedRenyiCBNormExpression N sigma.1 alpha
  have hInf :
      sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) =
        ((sInf (Set.range f) : ℝ) : EReal) :=
    ereal_sInf_range_coe_eq_coe_real_sInf f (by simpa [S, f] using hBelow)
  rw [N.sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le (N.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  have hleInf :
      N.inputSandwichedRenyiMutualInformationE psi alpha ≤
        sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro z ⟨sigma, rfl⟩
    simpa [S, f] using hinput psi sigma
  simpa [S, f, hInf] using hleInf

/-- Logarithmic CB-norm bound for a fixed rank-one input.

This is the scalar/logarithmic form of the pure-rank-one quotient bound from
the CB-norm alternate-expression proof.  It supplies the final `log` step used
after KW rewrites a fixed channel input into a weighted `|Γ⟩⟨Γ|` candidate in
`EA_capacity.tex:2054-2093`. -/
theorem sandwichedPureRankOneLogQuotient_le_CBNormExpression
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    {alpha : ℝ} (halpha : 1 < alpha) (psi : Prod a1 a1 → ℂ)
    (hden :
      0 <
        psdSchattenPNorm
          (partialTraceB (a := a1) (b := a1) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha)
    (hnum :
      0 <
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos psi))
          alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
              (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                (rankOneMatrix psi))
              (MatrixMap.referenceLift_mapsPositive
                (sandwichedSideWeightedMap N sigma alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                (rankOneMatrix_pos psi))
              alpha /
            psdSchattenPNorm
              (partialTraceB (a := a1) (b := a1) (rankOneMatrix psi))
              (partialTraceB_posSemidef (rankOneMatrix_pos psi))
              alpha) ≤
      sandwichedRenyiCBNormExpression N sigma alpha := by
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let num : ℝ :=
    psdSchattenPNorm
      (MatrixMap.referenceLift Phi (rankOneMatrix psi))
      (MatrixMap.referenceLift_mapsPositive Phi hPhi (rankOneMatrix_pos psi))
      alpha
  let den : ℝ :=
    psdSchattenPNorm
      (partialTraceB (a := a1) (b := a1) (rankOneMatrix psi))
      (partialTraceB_posSemidef (rankOneMatrix_pos psi))
      alpha
  have hquot_le :
      num / den ≤ MatrixMap.cbOneToAlphaNorm Phi hPhi alpha := by
    simpa [Phi, hPhi, num, den] using
      MatrixMap.cbOneToAlphaPureRankOneValue_le_cbOneToAlphaNorm
        Phi hPhi halpha psi hden
  have hnum' : 0 < num := by
    simpa [Phi, hPhi, num] using hnum
  have hquot_pos : 0 < num / den := div_pos hnum' hden
  have hlog_le :
      log2 (num / den) ≤ log2 (MatrixMap.cbOneToAlphaNorm Phi hPhi alpha) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hquot_pos hquot_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt (sandwichedCoeff_pos halpha))

/-- The denominator of the source CB original input is normalized to one for a
state reference.

This is the Lean form of the normalization used in KW
`EA_capacity.tex:2052-2058` and before `eq-operator_CB_alpha_norm`: for a
state `tau_R`, the reference marginal of
`tau_R^(1/(2 alpha)) |Γ⟩⟨Γ| tau_R^(1/(2 alpha))` is `tau_R^(1/alpha)`,
whose Schatten-`alpha` norm is one. -/
theorem cbOneToAlphaOriginalInput_state_denominator_eq_one
    (tau : State a1) {alpha : ℝ} (halpha : 0 < alpha) :
    psdSchattenPNorm
        (partialTraceB (a := a1) (b := a1)
          (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha))
        (partialTraceB_posSemidef
          (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.pos alpha))
        alpha =
      1 := by
  have htrace :
      partialTraceB (a := a1) (b := a1)
          (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha) =
        CFC.rpow tau.matrix (1 / alpha) :=
    MatrixMap.partialTraceB_cbOneToAlphaOriginalInput_eq_rpow tau.pos halpha
  calc
    psdSchattenPNorm
        (partialTraceB (a := a1) (b := a1)
          (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha))
        (partialTraceB_posSemidef
          (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.pos alpha))
        alpha =
      psdSchattenPNorm
        (CFC.rpow tau.matrix (1 / alpha))
        (tau.rpowMatrix_posSemidef (1 / alpha))
        alpha := by
          exact psdSchattenPNorm_congr htrace _ _ alpha
    _ = 1 := State.state_rpow_one_div_psdSchattenPNorm_eq_one_psd tau halpha

/-- Full-rank original CB candidates have strictly positive weighted-channel
value under a full-rank side reference.

This is the positivity side condition needed before taking logarithms of the
rank-one candidates that arise from the KW polar-decomposition route. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) (Y : MatrixMap.CBOneToAlphaOriginalDomain a1)
    (hY : Y.matrix.PosDef) {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        Y
        alpha := by
  let X : CMatrix (Prod a1 a1) := MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  have hXne : X ≠ 0 := by
    simpa [X] using MatrixMap.cbOneToAlphaOriginalInput_ne_zero_of_posDef
      (a1 := a1) hY halpha
  have hPhiXne :
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 :=
    sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
      N sigma hsigma alpha hX hXne
  unfold MatrixMap.cbOneToAlphaOriginalValue
  change 0 <
    psdSchattenPNorm
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ alpha
  exact psdSchattenPNorm_pos_of_ne_zero
    (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ hPhiXne

/-- Trace-one state candidates have strictly positive weighted-channel CB
value under a full-rank side reference.

This removes the unnecessary full-rank hypothesis from the source-side
candidate in the `Tr[Y_R] = 1` branch of KW `EA_capacity.tex:2090-2093`. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) (tau : State a1)
    {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
        alpha := by
  let X : CMatrix (Prod a1 a1) := MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.pos alpha
  have hXne : X ≠ 0 := by
    simpa [X] using MatrixMap.cbOneToAlphaOriginalInput_ne_zero_of_state
      (a1 := a1) tau halpha
  have hPhiXne :
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 :=
    sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
      N sigma hsigma alpha hX hXne
  unfold MatrixMap.cbOneToAlphaOriginalValue
  change 0 <
    psdSchattenPNorm
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ alpha
  exact psdSchattenPNorm_pos_of_ne_zero
    (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ hPhiXne

/-- Logarithmic two-point quasiconcavity input for the channel Sion exchange.

This is the `tau_R`-side Sion hypothesis from KW
`EA_capacity.tex:2080-2084`, in the exact scalar form used by the channel
alternate-expression surface: for a fixed full-rank `sigma_B`, the
weighted-channel CB objective at a convex mixture of normalized source states
dominates the smaller endpoint value after applying `log2` and the positive
Renyi prefactor. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_mix_min_le
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (tau0 tau1 : State a1) :
    min
        (alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau0)
              alpha))
        (alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau1)
              alpha)) ≤
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState
              { matrix := lambda • tau0.matrix + (1 - lambda) • tau1.matrix,
                pos :=
                  Matrix.PosSemidef.add
                    (Matrix.PosSemidef.smul tau0.pos hlambda0)
                    (Matrix.PosSemidef.smul tau1.pos (sub_nonneg.mpr hlambda1)),
                trace_eq_one := by
                  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    tau0.trace_eq_one, tau1.trace_eq_one]
                  norm_num })
            alpha) := by
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let tauMix : State a1 :=
    { matrix := lambda • tau0.matrix + (1 - lambda) • tau1.matrix,
      pos :=
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul tau0.pos hlambda0)
          (Matrix.PosSemidef.smul tau1.pos (sub_nonneg.mpr hlambda1)),
      trace_eq_one := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
          tau0.trace_eq_one, tau1.trace_eq_one]
        norm_num }
  let v0 : ℝ :=
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau0) alpha
  let v1 : ℝ :=
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau1) alpha
  let vmix : ℝ :=
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tauMix) alpha
  have hraw : min v0 v1 ≤ vmix := by
    simpa [Phi, hPhi, tauMix, v0, v1, vmix] using
      MatrixMap.cbOneToAlphaOriginalValue_ofState_min_le_mix
        Phi hPhi halpha hlambda0 hlambda1 tau0 tau1
  have hv0_pos : 0 < v0 := by
    simpa [Phi, hPhi, v0] using
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N sigma hsigma tau0 (lt_trans zero_lt_one halpha)
  have hv1_pos : 0 < v1 := by
    simpa [Phi, hPhi, v1] using
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N sigma hsigma tau1 (lt_trans zero_lt_one halpha)
  have hvmix_pos : 0 < vmix := by
    simpa [Phi, hPhi, tauMix, vmix] using
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N sigma hsigma tauMix (lt_trans zero_lt_one halpha)
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using sandwichedCoeff_pos halpha)
  by_cases h01 : v0 ≤ v1
  · have hlog01 : log2 v0 ≤ log2 v1 := log2_mono_of_pos hv0_pos h01
    have hv0_le_mix : v0 ≤ vmix := by
      simpa [min_eq_left h01] using hraw
    have hlog0_mix : log2 v0 ≤ log2 vmix :=
      log2_mono_of_pos hv0_pos hv0_le_mix
    calc
      min (coeff * log2 v0) (coeff * log2 v1) =
          coeff * log2 v0 := by
            rw [min_eq_left (mul_le_mul_of_nonneg_left hlog01 hcoeff_nonneg)]
      _ ≤ coeff * log2 vmix := by
            exact mul_le_mul_of_nonneg_left hlog0_mix hcoeff_nonneg
  · have h10 : v1 ≤ v0 := le_of_lt (lt_of_not_ge h01)
    have hlog10 : log2 v1 ≤ log2 v0 := log2_mono_of_pos hv1_pos h10
    have hv1_le_mix : v1 ≤ vmix := by
      simpa [min_eq_right h10] using hraw
    have hlog1_mix : log2 v1 ≤ log2 vmix :=
      log2_mono_of_pos hv1_pos hv1_le_mix
    calc
      min (coeff * log2 v0) (coeff * log2 v1) =
          coeff * log2 v1 := by
            rw [min_eq_right (mul_le_mul_of_nonneg_left hlog10 hcoeff_nonneg)]
      _ ≤ coeff * log2 vmix := by
            exact mul_le_mul_of_nonneg_left hlog1_mix hcoeff_nonneg

/-- Matrix-domain wrapper for the source-side logarithmic objective in the KW
channel Sion step.

The surrounding channel API optimizes over `State a`, while mathlib's Sion
theorem works over compact convex matrix domains.  This wrapper is equal to
the state expression on `State.densityMatrixSet a`; outside that domain its
value is irrelevant. -/
def sandwichedChannelOriginalValueLogDensity
    (N : Channel a1 b1) (sigma : State b1) (alpha : ℝ)
    (M : CMatrix a1) : ℝ := by
  classical
  exact
    if hM : M ∈ State.densityMatrixSet a1 then
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState
              (State.densityMatrixSetState M hM))
            alpha)
    else
      0

@[simp]
theorem sandwichedChannelOriginalValueLogDensity_of_mem
    (N : Channel a1 b1) (sigma : State b1) (alpha : ℝ)
    {M : CMatrix a1} (hM : M ∈ State.densityMatrixSet a1) :
    sandwichedChannelOriginalValueLogDensity N sigma alpha M =
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState
              (State.densityMatrixSetState M hM))
            alpha) := by
  classical
  simp [sandwichedChannelOriginalValueLogDensity, hM]

private theorem cbOneToAlphaReferenceWeight_continuousOn_posSemidef
    {alpha : ℝ} (halpha : 0 < alpha) :
    ContinuousOn
      (fun M : CMatrix a1 => MatrixMap.cbOneToAlphaReferenceWeight M alpha)
      ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) := by
  have hexp : 0 < (1 / (2 * alpha) : ℝ) := by
    positivity
  have hpow := State.cMatrix_rpow_continuousOn_posSemidef_of_pos (a := a1) hexp
  have hkr :
      Continuous fun T : CMatrix a1 => Matrix.kronecker T (1 : CMatrix a1) := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        (continuous_id.matrix_elem x.1 y.1).mul continuous_const
  simpa [MatrixMap.cbOneToAlphaReferenceWeight, Function.comp_def] using
    hkr.comp_continuousOn hpow

private theorem cbOneToAlphaOriginalInput_continuousOn_posSemidef
    {alpha : ℝ} (halpha : 0 < alpha) :
    ContinuousOn
      (fun M : CMatrix a1 => MatrixMap.cbOneToAlphaOriginalInput M alpha)
      ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) := by
  let W : CMatrix a1 → CMatrix (Prod a1 a1) := fun M =>
    MatrixMap.cbOneToAlphaReferenceWeight M alpha
  have hW : ContinuousOn W ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) :=
    cbOneToAlphaReferenceWeight_continuousOn_posSemidef (a1 := a1) halpha
  have hleft :
      ContinuousOn
        (fun M : CMatrix a1 =>
          W M * MatrixMap.maximallyEntangledProjector a1)
        ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) :=
    hW.mul continuousOn_const
  have hall :
      ContinuousOn
        (fun M : CMatrix a1 =>
          (W M * MatrixMap.maximallyEntangledProjector a1) * W M)
        ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) :=
    hleft.mul hW
  simpa [MatrixMap.cbOneToAlphaOriginalInput, W, Matrix.mul_assoc] using hall

private theorem matrixMap_continuous (Phi : MatrixMap a1 b1) :
    Continuous fun X : CMatrix a1 => Phi X := by
  simpa [LinearMap.coe_toContinuousLinearMap] using
    (LinearMap.toContinuousLinearMap Phi).continuous

private theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_continuousOn_density
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ContinuousOn
      (sandwichedChannelOriginalValueLogDensity N sigma alpha)
      (State.densityMatrixSet a1) := by
  rw [continuousOn_iff_continuous_restrict]
  let S := {M : CMatrix a1 // M ∈ State.densityMatrixSet a1}
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let X : S → CMatrix (Prod a1 a1) := fun M =>
    MatrixMap.cbOneToAlphaOriginalInput M.1 alpha
  have hXcont : Continuous X := by
    have hcontOn :
        ContinuousOn
          (fun M : CMatrix a1 => MatrixMap.cbOneToAlphaOriginalInput M alpha)
          (State.densityMatrixSet a1) :=
      (cbOneToAlphaOriginalInput_continuousOn_posSemidef (a1 := a1)
        (lt_trans zero_lt_one halpha)).mono
          (fun M hM => (State.mem_densityMatrixSet_iff.mp hM).1)
    simpa [S, X] using continuousOn_iff_continuous_restrict.mp hcontOn
  let Y : S → CMatrix (Prod a1 b1) := fun M => Phi.referenceLift (X M)
  have hYcont : Continuous Y := by
    exact (matrixMap_continuous (a1 := Prod a1 a1) (b1 := Prod a1 b1)
      Phi.referenceLift).comp hXcont
  have hYpsd : ∀ M : S, (Y M).PosSemidef := by
    intro M
    exact Phi.referenceLift_mapsPositive hPhi
      (MatrixMap.cbOneToAlphaOriginalInput_posSemidef
        ((State.mem_densityMatrixSet_iff.mp M.2).1) alpha)
  let normValue : S → ℝ := fun M => psdSchattenPNorm (Y M) (hYpsd M) alpha
  have hnorm_cont : Continuous normValue := by
    rw [continuous_iff_continuousAt]
    intro M
    exact psdSchattenPNorm_tendsto_of_tendsto_posSemidef
      (a := Prod a1 b1) (lt_trans zero_lt_one halpha) hYcont.continuousAt hYpsd
      (hYpsd M)
  have hnorm_pos : ∀ M : S, 0 < normValue M := by
    intro M
    have hpos :=
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N sigma hsigma (State.densityMatrixSetState M.1 M.2)
        (lt_trans zero_lt_one halpha)
    simpa [Phi, hPhi, X, Y, normValue, MatrixMap.cbOneToAlphaOriginalValue,
      State.densityMatrixSetState_matrix] using hpos
  have hlog_cont : Continuous fun M : S => log2 (normValue M) := by
    rw [continuous_iff_continuousAt]
    intro M
    unfold log2
    exact ((Real.continuousAt_log (ne_of_gt (hnorm_pos M))).div_const _).comp
      hnorm_cont.continuousAt
  have hscaled :
      Continuous fun M : S =>
        alpha / (alpha - 1) * log2 (normValue M) :=
    continuous_const.mul hlog_cont
  have hfun :
      (fun M : S => sandwichedChannelOriginalValueLogDensity N sigma alpha M.1) =
        fun M : S => alpha / (alpha - 1) * log2 (normValue M) := by
    funext M
    rw [sandwichedChannelOriginalValueLogDensity_of_mem N sigma alpha M.2]
    unfold normValue Y X Phi MatrixMap.cbOneToAlphaOriginalValue
      MatrixMap.CBOneToAlphaOriginalDomain.ofState
    simp [State.densityMatrixSetState_matrix]
  change Continuous fun M : S => sandwichedChannelOriginalValueLogDensity N sigma alpha M.1
  rw [hfun]
  exact hscaled

/-- Upper semicontinuity of the KW channel Sion objective in the source/input
density variable.

This is the topological half of the Sion hypothesis attached to
Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`, after the channel objective is
rewritten as the finite-dimensional CB-norm source function over normalized
input densities. -/
private theorem sandwichedChannelOriginalValueLogDensity_upperSemicontinuousOn_density
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    UpperSemicontinuousOn
      (sandwichedChannelOriginalValueLogDensity N sigma alpha)
      (State.densityMatrixSet a1) :=
  ContinuousOn.upperSemicontinuousOn
    (cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_continuousOn_density
      N sigma hsigma halpha)

/-- Matrix-domain quasiconcavity of the KW source-side channel objective.

This discharges the source-variable quasiconcavity part of Sion's hypotheses
for KW `EA_capacity.tex:2080-2084`, after translating the normalized-state
objective to the matrix density domain. -/
theorem sandwichedChannelOriginalValueLogDensity_quasiconcaveOn
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    QuasiconcaveOn ℝ (State.densityMatrixSet a1)
      (sandwichedChannelOriginalValueLogDensity N sigma alpha) := by
  rw [quasiconcaveOn_iff_min_le]
  refine ⟨State.densityMatrixSet_convex, ?_⟩
  intro X hX Y hY s t hs ht hst
  have ht_eq : t = 1 - s := by linarith
  subst t
  have hmix :
      s • X + (1 - s) • Y ∈ State.densityMatrixSet a1 :=
    State.densityMatrixSet_convex hX hY hs ht hst
  let tauX : State a1 := State.densityMatrixSetState X hX
  let tauY : State a1 := State.densityMatrixSetState Y hY
  have hmain :=
    cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_mix_min_le
      N sigma hsigma halpha hs (by linarith) tauX tauY
  simpa [sandwichedChannelOriginalValueLogDensity, hX, hY, hmix, tauX, tauY,
    State.densityMatrixSetState] using hmain

/-- Matrix-domain wrapper for the reference-side logarithmic objective in the
KW channel Sion step.

The source proof optimizes over full-rank side states `sigma_B`.  This wrapper
keeps that variable as a matrix so Sion can be applied on the matrix domain;
outside the full-rank density domain its value is irrelevant. -/
def sandwichedChannelOriginalValueLogReferenceDensity
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ)
    (M : CMatrix b1) : ℝ := by
  classical
  exact
    if hM : M ∈ State.fullRankDensityMatrixSet b1 then
      let sigma : State b1 :=
        State.densityMatrixSetState M (State.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha)
    else
      0

@[simp]
theorem sandwichedChannelOriginalValueLogReferenceDensity_of_mem
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ)
    {M : CMatrix b1} (hM : M ∈ State.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueLogReferenceDensity N tau alpha M =
      let sigma : State b1 :=
        State.densityMatrixSetState M (State.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha) := by
  classical
  simp [sandwichedChannelOriginalValueLogReferenceDensity, hM]

/-- Raw reference-side objective underlying
`sandwichedChannelOriginalValueLogReferenceDensity`.

Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`, proves convexity on the
unlogged CB-norm expression before applying the positive logarithmic Renyi
prefactor.  This wrapper isolates that raw value on the same full-rank matrix
domain used in the Sion step. -/
def sandwichedChannelOriginalValueReferenceDensity
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ)
    (M : CMatrix b1) : ℝ := by
  classical
  exact
    if hM : M ∈ State.fullRankDensityMatrixSet b1 then
      let sigma : State b1 :=
        State.densityMatrixSetState M (State.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
        alpha
    else
      0

/-- Fixed source-side Choi input appearing in the KW channel alternate
expression proof. -/
private def sandwichedChannelReferenceBase
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ) : CMatrix (Prod a1 b1) :=
  MatrixMap.referenceLift N.map
    (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha)

private theorem sandwichedChannelReferenceBase_posSemidef
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ) :
    (sandwichedChannelReferenceBase N tau alpha).PosSemidef :=
  MatrixMap.referenceLift_mapsPositive N.map N.completelyPositive
    (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.pos alpha)

/-- KW source-shaped matrix after the polar-decomposition/unitary-invariance
rewrite in `EA_capacity.tex:2071-2079`. -/
private def sandwichedChannelReferenceKWMatrix
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ) (M : CMatrix b1) :
    CMatrix (Prod a1 b1) :=
  let base : CMatrix (Prod a1 b1) := sandwichedChannelReferenceBase N tau alpha
  CFC.sqrt base *
    Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) *
      CFC.sqrt base

private theorem sandwichedChannelReferenceKWMatrix_posSemidef
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ)
    {M : CMatrix b1} (hM : M.PosSemidef) :
    (sandwichedChannelReferenceKWMatrix N tau alpha M).PosSemidef := by
  let base : CMatrix (Prod a1 b1) := sandwichedChannelReferenceBase N tau alpha
  let W : CMatrix (Prod a1 b1) :=
    Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha))
  have hbase : base.PosSemidef := sandwichedChannelReferenceBase_posSemidef N tau alpha
  have hW : W.PosSemidef :=
    Matrix.PosSemidef.one.kronecker
      (cMatrix_rpow_posSemidef (A := M) (s := (1 - alpha) / alpha) hM)
  have hsqrtHerm : (CFC.sqrt base).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg base)).isHermitian
  have h := hW.mul_mul_conjTranspose_same (CFC.sqrt base)
  simpa [sandwichedChannelReferenceKWMatrix, base, W, hsqrtHerm.eq] using h

private theorem real_reference_half_rpow_mul_self
    {x alpha : ℝ} (hx : 0 ≤ x) (halpha : 1 < alpha) :
    x ^ ((1 - alpha) / (2 * alpha)) * x ^ ((1 - alpha) / (2 * alpha)) =
      x ^ ((1 - alpha) / alpha) := by
  by_cases hx0 : x = 0
  · subst x
    have hhalf_ne : (1 - alpha) / (2 * alpha) ≠ 0 := by
      have hnum : 1 - alpha ≠ 0 := by linarith
      have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
      exact div_ne_zero hnum hden
    have hfull_ne : (1 - alpha) / alpha ≠ 0 := by
      have hnum : 1 - alpha ≠ 0 := by linarith
      have hden : alpha ≠ 0 := by linarith [lt_trans zero_lt_one halpha]
      exact div_ne_zero hnum hden
    simp [Real.zero_rpow hhalf_ne, Real.zero_rpow hfull_ne]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [← Real.rpow_add hxpos]
    congr 1
    field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
    ring

private theorem cMatrix_reference_half_rpow_mul_self
    {M : CMatrix b1} (hM : M.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
    CFC.rpow M ((1 - alpha) / (2 * alpha)) *
        CFC.rpow M ((1 - alpha) / (2 * alpha)) =
      CFC.rpow M ((1 - alpha) / alpha) :=
  cMatrix_rpow_mul_rpow_of_posSemidef_scalar hM
    (fun _ hx => real_reference_half_rpow_mul_self hx halpha)

private theorem referenceWeight_mul_self_eq_referencePower
    {M : CMatrix b1} (hM : M.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
    let D : CMatrix (Prod a1 b1) :=
      Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / (2 * alpha)))
    D * D =
      Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) := by
  intro D
  calc
    D * D =
        Matrix.kronecker ((1 : CMatrix a1) * (1 : CMatrix a1))
          (CFC.rpow M ((1 - alpha) / (2 * alpha)) *
            CFC.rpow M ((1 - alpha) / (2 * alpha))) := by
          simpa [D] using
            (Matrix.mul_kronecker_mul (1 : CMatrix a1) (1 : CMatrix a1)
              (CFC.rpow M ((1 - alpha) / (2 * alpha)))
              (CFC.rpow M ((1 - alpha) / (2 * alpha)))).symm
    _ = Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) := by
          rw [cMatrix_reference_half_rpow_mul_self hM halpha]
          simp

@[simp]
theorem sandwichedChannelOriginalValueReferenceDensity_of_mem
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ)
    {M : CMatrix b1} (hM : M ∈ State.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueReferenceDensity N tau alpha M =
      let sigma : State b1 :=
        State.densityMatrixSetState M (State.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
        alpha := by
  classical
  simp [sandwichedChannelOriginalValueReferenceDensity, hM]

private theorem sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm
    [Nonempty a1] (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix b1} (hM : M ∈ State.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueReferenceDensity N tau alpha M =
      psdSchattenPNorm (sandwichedChannelReferenceKWMatrix N tau alpha M)
        (sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef)
        alpha := by
  let sigma : State b1 :=
    State.densityMatrixSetState M (State.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
  let X : CMatrix (Prod a1 a1) := MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let base : CMatrix (Prod a1 b1) := sandwichedChannelReferenceBase N tau alpha
  let D : CMatrix (Prod a1 b1) :=
    Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / (2 * alpha)))
  let S : CMatrix (Prod a1 b1) := CFC.sqrt base
  let A : CMatrix (Prod a1 b1) := D * S
  let B : CMatrix (Prod a1 b1) := S * D
  have hbase : base.PosSemidef := sandwichedChannelReferenceBase_posSemidef N tau alpha
  have hDherm : D.conjTranspose = D := by
    have hpow :
        (CFC.rpow M ((1 - alpha) / (2 * alpha))).PosSemidef :=
      cMatrix_rpow_posSemidef (A := M) (s := (1 - alpha) / (2 * alpha))
        hM.1.posSemidef
    have hD : D.PosSemidef := Matrix.PosSemidef.one.kronecker hpow
    exact hD.isHermitian.eq
  have hsqrt : S * S = base := by
    simpa [S] using CFC.sqrt_mul_sqrt_self base hbase.nonneg
  have hDsq :
      D * D =
        Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) := by
    simpa [D] using referenceWeight_mul_self_eq_referencePower (a1 := a1)
      hM.1.posSemidef halpha
  have hYeq :
      Phi.referenceLift X = D * base * D := by
    dsimp [Phi, X, sigma]
    rw [sandwichedSideWeightedMap]
    rw [MatrixMap.referenceLift_comp_apply]
    rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
    simp only [State.densityMatrixSetState_matrix]
    change D * base * D.conjTranspose = D * base * D
    rw [hDherm]
  have hAB :
      A * B = Phi.referenceLift X := by
    calc
      A * B = D * S * (S * D) := by simp [A, B, Matrix.mul_assoc]
      _ = D * (S * S) * D := by noncomm_ring
      _ = D * base * D := by rw [hsqrt]
      _ = Phi.referenceLift X := hYeq.symm
  have hBA :
      B * A = sandwichedChannelReferenceKWMatrix N tau alpha M := by
    calc
      B * A = S * D * (D * S) := by simp [A, B, Matrix.mul_assoc]
      _ = S * (D * D) * S := by noncomm_ring
      _ = S * Matrix.kronecker (1 : CMatrix a1)
            (CFC.rpow M ((1 - alpha) / alpha)) * S := by rw [hDsq]
      _ = sandwichedChannelReferenceKWMatrix N tau alpha M := by
            simp [S, base, sandwichedChannelReferenceKWMatrix, Matrix.mul_assoc]
  have hABpsd :
      (A * B).PosSemidef := by
    rw [hAB]
    exact Phi.referenceLift_mapsPositive hPhi
      (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.pos alpha)
  have hBApsd :
      (B * A).PosSemidef := by
    rw [hBA]
    exact sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef
  have hPhiXpos :
      (Phi.referenceLift X).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi
      (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.pos alpha)
  rw [sandwichedChannelOriginalValueReferenceDensity_of_mem N tau alpha hM]
  unfold MatrixMap.cbOneToAlphaOriginalValue MatrixMap.CBOneToAlphaOriginalDomain.ofState
  calc
    psdSchattenPNorm (Phi.referenceLift X) hPhiXpos alpha =
        psdSchattenPNorm (A * B) hABpsd alpha := by
          exact psdSchattenPNorm_congr hAB.symm hPhiXpos hABpsd alpha
    _ = psdSchattenPNorm (B * A) hBApsd alpha :=
          psdSchattenPNorm_mul_comm hABpsd hBApsd (lt_trans zero_lt_one halpha)
    _ =
        psdSchattenPNorm (sandwichedChannelReferenceKWMatrix N tau alpha M)
          (sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef)
          alpha := by
          exact psdSchattenPNorm_congr hBA hBApsd
            (sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef)
            alpha

private theorem cMatrix_conj_le_conj
    {A B S : CMatrix (Prod a1 b1)} (hAB : A ≤ B) :
    S * A * S.conjTranspose ≤ S * B * S.conjTranspose := by
  rw [Matrix.le_iff]
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hconj : (S * (B - A) * S.conjTranspose).PosSemidef :=
    hdiff.mul_mul_conjTranspose_same S
  have heq :
      S * B * S.conjTranspose - S * A * S.conjTranspose =
        S * (B - A) * S.conjTranspose := by
    noncomm_ring
  simpa [heq]

private theorem kronecker_one_left_le_of_le
    {A B : CMatrix b1} (hAB : A ≤ B) :
    Matrix.kronecker (1 : CMatrix a1) A ≤ Matrix.kronecker (1 : CMatrix a1) B := by
  rw [Matrix.le_iff]
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hdiffK :
      (Matrix.kronecker (1 : CMatrix a1) (B - A)).PosSemidef :=
    Matrix.PosSemidef.one.kronecker hdiff
  have heq :
      Matrix.kronecker (1 : CMatrix a1) B -
          Matrix.kronecker (1 : CMatrix a1) A =
        Matrix.kronecker (1 : CMatrix a1) (B - A) := by
    ext i j
    by_cases hij : i.1 = j.1
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, hij,
        sub_eq_add_neg, mul_add]
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, hij,
        sub_eq_add_neg]
  rw [heq]
  exact hdiffK

private theorem sandwichedChannelReferenceKWMatrix_le_convex_combo
    (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    {X Y : CMatrix b1} (hX : X ∈ State.fullRankDensityMatrixSet b1)
    (hY : Y ∈ State.fullRankDensityMatrixSet b1)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    sandwichedChannelReferenceKWMatrix N tau alpha (s • X + t • Y) ≤
      s • sandwichedChannelReferenceKWMatrix N tau alpha X +
        t • sandwichedChannelReferenceKWMatrix N tau alpha Y := by
  let p : ℝ := (1 - alpha) / alpha
  let base : CMatrix (Prod a1 b1) := sandwichedChannelReferenceBase N tau alpha
  let S : CMatrix (Prod a1 b1) := CFC.sqrt base
  let PX : CMatrix b1 := CFC.rpow X p
  let PY : CMatrix b1 := CFC.rpow Y p
  let Pmix : CMatrix b1 := CFC.rpow (s • X + t • Y) p
  let WX : CMatrix (Prod a1 b1) := Matrix.kronecker (1 : CMatrix a1) PX
  let WY : CMatrix (Prod a1 b1) := Matrix.kronecker (1 : CMatrix a1) PY
  let Wmix : CMatrix (Prod a1 b1) := Matrix.kronecker (1 : CMatrix a1) Pmix
  have hp : p ∈ Set.Icc (-1 : ℝ) 0 := by
    constructor
    · dsimp [p]
      have hapos : 0 < alpha := lt_trans zero_lt_one halpha
      rw [le_div_iff₀ hapos]
      linarith
    · dsimp [p]
      have hapos : 0 < alpha := lt_trans zero_lt_one halpha
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hapos)
  have hpow :
      Pmix ≤ s • PX + t • PY := by
    simpa [Pmix, PX, PY, p] using
      (State.cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero (a := b1) hp).2
        hX.1 hY.1 hs ht hst
  have hW :
      Wmix ≤ s • WX + t • WY := by
    have hK := kronecker_one_left_le_of_le (a1 := a1) hpow
    have hlin :
        Matrix.kronecker (1 : CMatrix a1) (s • PX + t • PY) =
      s • WX + t • WY := by
      dsimp [WX, WY]
      rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
        (by intro x y z; exact mul_add x y z)
        (1 : CMatrix a1) (s • PX) (t • PY)]
      rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) s
        (by intro x y; exact mul_smul_comm s x y) (1 : CMatrix a1) PX]
      rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) t
        (by intro x y; exact mul_smul_comm t x y) (1 : CMatrix a1) PY]
    rw [hlin] at hK
    simpa [Wmix] using hK
  have hS : S.conjTranspose = S := by
    have hbase : base.PosSemidef := sandwichedChannelReferenceBase_posSemidef N tau alpha
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg base)).isHermitian.eq
  have hconj := cMatrix_conj_le_conj (a1 := a1) (b1 := b1) (S := S) hW
  have hleft :
      S * Wmix * S =
        sandwichedChannelReferenceKWMatrix N tau alpha (s • X + t • Y) := by
    simp [S, Wmix, Pmix, base, p, sandwichedChannelReferenceKWMatrix, Matrix.mul_assoc]
  have hright :
      S * (s • WX + t • WY) * S =
        s • sandwichedChannelReferenceKWMatrix N tau alpha X +
          t • sandwichedChannelReferenceKWMatrix N tau alpha Y := by
    simp [S, WX, WY, PX, PY, base, p, sandwichedChannelReferenceKWMatrix,
      Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc]
  simpa [hS, hleft, hright] using hconj

private theorem real_convex_combo_le_max
    {x y s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    s * x + t * y ≤ max x y := by
  by_cases hxy : x ≤ y
  · have hsx : s * x ≤ s * y := mul_le_mul_of_nonneg_left hxy hs
    calc
      s * x + t * y ≤ s * y + t * y := add_le_add hsx le_rfl
      _ = (s + t) * y := by ring
      _ = y := by rw [hst, one_mul]
      _ ≤ max x y := le_max_right _ _
  · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
    have hty : t * y ≤ t * x := mul_le_mul_of_nonneg_left hyx ht
    calc
      s * x + t * y ≤ s * x + t * x := add_le_add le_rfl hty
      _ = (s + t) * x := by ring
      _ = x := by rw [hst, one_mul]
      _ ≤ max x y := le_max_left _ _

private theorem sandwichedChannelOriginalValueReferenceDensity_quasiconvexOn
    [Nonempty a1] (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    QuasiconvexOn ℝ (State.fullRankDensityMatrixSet b1)
      (sandwichedChannelOriginalValueReferenceDensity N tau alpha) := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨State.fullRankDensityMatrixSet_convex, ?_⟩
  intro X hX Y hY s t hs ht hst
  have hmix : s • X + t • Y ∈ State.fullRankDensityMatrixSet b1 :=
    State.fullRankDensityMatrixSet_convex hX hY hs ht hst
  let MX : CMatrix (Prod a1 b1) := sandwichedChannelReferenceKWMatrix N tau alpha X
  let MY : CMatrix (Prod a1 b1) := sandwichedChannelReferenceKWMatrix N tau alpha Y
  let MM : CMatrix (Prod a1 b1) :=
    sandwichedChannelReferenceKWMatrix N tau alpha (s • X + t • Y)
  have hMX : MX.PosSemidef :=
    sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hX.1.posSemidef
  have hMY : MY.PosSemidef :=
    sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hY.1.posSemidef
  have hMM : MM.PosSemidef :=
    sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hmix.1.posSemidef
  have hcombo : (s • MX + t • MY).PosSemidef :=
    Matrix.PosSemidef.add (Matrix.PosSemidef.smul hMX hs)
      (Matrix.PosSemidef.smul hMY ht)
  have hle :
      MM ≤ s • MX + t • MY := by
    simpa [MM, MX, MY] using
      sandwichedChannelReferenceKWMatrix_le_convex_combo
        N tau halpha hX hY hs ht hst
  have hnorm :
      psdSchattenPNorm MM hMM alpha ≤
        s * psdSchattenPNorm MX hMX alpha + t * psdSchattenPNorm MY hMY alpha := by
    exact (psdSchattenPNorm_mono_of_le hMM hcombo halpha hle).trans
      (psdSchattenPNorm_convex_combo_le hMX hMY halpha hs ht hst)
  have hmax :
      s * psdSchattenPNorm MX hMX alpha + t * psdSchattenPNorm MY hMY alpha ≤
        max (psdSchattenPNorm MX hMX alpha) (psdSchattenPNorm MY hMY alpha) :=
    real_convex_combo_le_max hs ht hst
  rw [sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm N tau halpha hmix,
    sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm N tau halpha hX,
    sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm N tau halpha hY]
  exact hnorm.trans hmax

private theorem sandwichedChannelOriginalValueReferenceDensity_pos_of_mem
    [Nonempty a1] (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix b1} (hM : M ∈ State.fullRankDensityMatrixSet b1) :
    0 < sandwichedChannelOriginalValueReferenceDensity N tau alpha M := by
  let sigma : State b1 :=
    State.densityMatrixSetState M (State.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
  have hsigma : sigma.matrix.PosDef := by
    simpa [sigma, State.densityMatrixSetState_matrix] using hM.1
  rw [sandwichedChannelOriginalValueReferenceDensity_of_mem N tau alpha hM]
  exact cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
    N sigma hsigma tau (lt_trans zero_lt_one halpha)

private theorem sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
    (N : Channel a1 b1) (tau : State a1) (alpha : ℝ)
    {M : CMatrix b1} (hM : M ∈ State.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueLogReferenceDensity N tau alpha M =
      alpha / (alpha - 1) *
        log2 (sandwichedChannelOriginalValueReferenceDensity N tau alpha M) := by
  rw [sandwichedChannelOriginalValueLogReferenceDensity_of_mem N tau alpha hM,
    sandwichedChannelOriginalValueReferenceDensity_of_mem N tau alpha hM]

private theorem sandwichedChannelOriginalValueLogReferenceDensity_quasiconvexOn_of_raw
    [Nonempty a1] (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hRawQ :
      QuasiconvexOn ℝ (State.fullRankDensityMatrixSet b1)
        (sandwichedChannelOriginalValueReferenceDensity N tau alpha)) :
    QuasiconvexOn ℝ (State.fullRankDensityMatrixSet b1)
      (sandwichedChannelOriginalValueLogReferenceDensity N tau alpha) := by
  rw [quasiconvexOn_iff_le_max] at hRawQ ⊢
  refine ⟨hRawQ.1, ?_⟩
  intro X hX Y hY s t hs ht hst
  have hmix : s • X + t • Y ∈ State.fullRankDensityMatrixSet b1 :=
    hRawQ.1 hX hY hs ht hst
  let raw : CMatrix b1 → ℝ := sandwichedChannelOriginalValueReferenceDensity N tau alpha
  let logged : CMatrix b1 → ℝ :=
    sandwichedChannelOriginalValueLogReferenceDensity N tau alpha
  have hraw :
      raw (s • X + t • Y) ≤ max (raw X) (raw Y) := by
    simpa [raw] using hRawQ.2 hX hY hs ht hst
  have hxpos : 0 < raw X := by
    simpa [raw] using
      sandwichedChannelOriginalValueReferenceDensity_pos_of_mem N tau halpha hX
  have hypos : 0 < raw Y := by
    simpa [raw] using
      sandwichedChannelOriginalValueReferenceDensity_pos_of_mem N tau halpha hY
  have hmixpos : 0 < raw (s • X + t • Y) := by
    simpa [raw] using
      sandwichedChannelOriginalValueReferenceDensity_pos_of_mem N tau halpha hmix
  have hlog :
      log2 (raw (s • X + t • Y)) ≤ log2 (max (raw X) (raw Y)) :=
    log2_mono_of_pos hmixpos hraw
  have hlog_max :
      log2 (max (raw X) (raw Y)) =
        max (log2 (raw X)) (log2 (raw Y)) := by
    by_cases hxy : raw X ≤ raw Y
    · have hlogxy : log2 (raw X) ≤ log2 (raw Y) :=
        log2_mono_of_pos hxpos hxy
      rw [max_eq_right hxy, max_eq_right hlogxy]
    · have hyx : raw Y ≤ raw X := le_of_lt (lt_of_not_ge hxy)
      have hlogyx : log2 (raw Y) ≤ log2 (raw X) :=
        log2_mono_of_pos hypos hyx
      rw [max_eq_left hyx, max_eq_left hlogyx]
  have hlog' :
      log2 (raw (s • X + t • Y)) ≤ max (log2 (raw X)) (log2 (raw Y)) := by
    simpa [hlog_max] using hlog
  let coeff : ℝ := alpha / (alpha - 1)
  have hcoeff : 0 ≤ coeff := le_of_lt (by simpa [coeff] using sandwichedCoeff_pos halpha)
  have hscaled :
      coeff * log2 (raw (s • X + t • Y)) ≤
        max (coeff * log2 (raw X)) (coeff * log2 (raw Y)) := by
    by_cases hxy : log2 (raw X) ≤ log2 (raw Y)
    · have hlog_le_y : log2 (raw (s • X + t • Y)) ≤ log2 (raw Y) := by
        simpa [max_eq_right hxy] using hlog'
      have hscaled_xy : coeff * log2 (raw X) ≤ coeff * log2 (raw Y) :=
        mul_le_mul_of_nonneg_left hxy hcoeff
      rw [max_eq_right hscaled_xy]
      exact mul_le_mul_of_nonneg_left hlog_le_y hcoeff
    · have hyx : log2 (raw Y) ≤ log2 (raw X) := le_of_lt (lt_of_not_ge hxy)
      have hlog_le_x : log2 (raw (s • X + t • Y)) ≤ log2 (raw X) := by
        simpa [max_eq_left hyx] using hlog'
      have hscaled_yx : coeff * log2 (raw Y) ≤ coeff * log2 (raw X) :=
        mul_le_mul_of_nonneg_left hyx hcoeff
      rw [max_eq_left hscaled_yx]
      exact mul_le_mul_of_nonneg_left hlog_le_x hcoeff
  have hmix_log :
      logged (s • X + t • Y) = coeff * log2 (raw (s • X + t • Y)) := by
    simpa [logged, raw, coeff] using
      sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
        N tau alpha hmix
  have hx_log : logged X = coeff * log2 (raw X) := by
    simpa [logged, raw, coeff] using
      sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
        N tau alpha hX
  have hy_log : logged Y = coeff * log2 (raw Y) := by
    simpa [logged, raw, coeff] using
      sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
        N tau alpha hY
  simpa [logged, hmix_log, hx_log, hy_log] using hscaled

/-- Continuity of the KW channel Sion objective in the full-rank reference
density variable.

This is the topological half of the `sigma_B` side of
Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`: the map
`sigma_B ↦ ||(S_sigma^(alpha) ∘ N)(Y_tau)||_alpha` is continuous on the
full-rank density domain, hence its positive logarithmic rescaling is
continuous there. -/
private theorem sandwichedChannelOriginalValueLogReferenceDensity_continuousOn_fullRank
    [Nonempty a1] (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ContinuousOn
      (sandwichedChannelOriginalValueLogReferenceDensity N tau alpha)
      (State.fullRankDensityMatrixSet b1) := by
  rw [continuousOn_iff_continuous_restrict]
  let S := {M : CMatrix b1 // M ∈ State.fullRankDensityMatrixSet b1}
  let X : CMatrix (Prod a1 a1) := MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.pos alpha
  let W : S → CMatrix b1 := fun M =>
    CFC.rpow M.1 ((1 - alpha) / (2 * alpha))
  have hWcont : Continuous W := by
    have hcontOn :
        ContinuousOn
          (fun M : CMatrix b1 => CFC.rpow M ((1 - alpha) / (2 * alpha)))
          (State.fullRankDensityMatrixSet b1) :=
      (State.cMatrix_rpow_continuousOn_posDef
        (a := b1) ((1 - alpha) / (2 * alpha))).mono (fun M hM => hM.1)
    simpa [S, W] using continuousOn_iff_continuous_restrict.mp hcontOn
  let base : CMatrix (Prod a1 b1) := MatrixMap.referenceLift N.map X
  let Y : S → CMatrix (Prod a1 b1) := fun M =>
    MatrixMap.referenceLift
      (sandwichedSideWeightedMap N
        (State.densityMatrixSetState M.1
          (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        alpha) X
  let Yexplicit : S → CMatrix (Prod a1 b1) := fun M =>
    Matrix.kronecker (1 : CMatrix a1) (W M) * base *
      Matrix.kronecker (1 : CMatrix a1) (W M)
  have hY_eq : Y = Yexplicit := by
    funext M
    dsimp [Y, Yexplicit, base, W]
    rw [sandwichedSideWeightedMap]
    rw [MatrixMap.referenceLift_comp_apply]
    rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
    have hDherm :
        (Matrix.kronecker (1 : CMatrix a1)
            (CFC.rpow
              (State.densityMatrixSetState M.1
                (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).matrix
              ((1 - alpha) / (2 * alpha)))).conjTranspose =
          Matrix.kronecker (1 : CMatrix a1)
            (CFC.rpow
              (State.densityMatrixSetState M.1
                (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).matrix
              ((1 - alpha) / (2 * alpha))) :=
      (Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef
          (A := (State.densityMatrixSetState M.1
            (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).matrix)
          (s := (1 - alpha) / (2 * alpha))
          (State.densityMatrixSetState M.1
            (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).pos)).isHermitian.eq
    rw [hDherm]
    simp [State.densityMatrixSetState_matrix, W]
  have hYexplicit_cont : Continuous Yexplicit := by
    have hkr :
        Continuous fun M : S => Matrix.kronecker (1 : CMatrix a1) (W M) := by
      unfold Matrix.kronecker
      exact _root_.continuous_matrix fun x y => by
        simpa [Matrix.kroneckerMap_apply] using
          continuous_const.mul ((hWcont.matrix_elem x.2 y.2))
    exact (hkr.matrix_mul continuous_const).matrix_mul hkr
  have hYcont : Continuous Y := by
    rw [hY_eq]
    exact hYexplicit_cont
  have hYpsd : ∀ M : S, (Y M).PosSemidef := by
    intro M
    exact MatrixMap.referenceLift_mapsPositive
      (sandwichedSideWeightedMap N
        (State.densityMatrixSetState M.1
          (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        alpha)
      (sandwichedSideWeightedMap_completelyPositive N
        (State.densityMatrixSetState M.1
          (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        alpha)
      hX
  let normValue : S → ℝ := fun M => psdSchattenPNorm (Y M) (hYpsd M) alpha
  have hnorm_cont : Continuous normValue := by
    rw [continuous_iff_continuousAt]
    intro M
    exact psdSchattenPNorm_tendsto_of_tendsto_posSemidef
      (a := Prod a1 b1) (lt_trans zero_lt_one halpha) hYcont.continuousAt hYpsd
      (hYpsd M)
  have hnorm_pos : ∀ M : S, 0 < normValue M := by
    intro M
    have hpos :=
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N
        (State.densityMatrixSetState M.1
          (State.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        M.2.1 tau (lt_trans zero_lt_one halpha)
    simpa [Y, normValue, MatrixMap.cbOneToAlphaOriginalValue,
      MatrixMap.CBOneToAlphaOriginalDomain.ofState] using hpos
  have hlog_cont : Continuous fun M : S => log2 (normValue M) := by
    rw [continuous_iff_continuousAt]
    intro M
    unfold log2
    exact ((Real.continuousAt_log (ne_of_gt (hnorm_pos M))).div_const _).comp
      hnorm_cont.continuousAt
  have hscaled :
      Continuous fun M : S =>
        alpha / (alpha - 1) * log2 (normValue M) :=
    continuous_const.mul hlog_cont
  have hfun :
      (fun M : S =>
        sandwichedChannelOriginalValueLogReferenceDensity N tau alpha M.1) =
        fun M : S => alpha / (alpha - 1) * log2 (normValue M) := by
    funext M
    rw [sandwichedChannelOriginalValueLogReferenceDensity_of_mem N tau alpha M.2]
    unfold normValue Y X
    simp [MatrixMap.cbOneToAlphaOriginalValue,
      MatrixMap.CBOneToAlphaOriginalDomain.ofState]
  change Continuous fun M : S =>
    sandwichedChannelOriginalValueLogReferenceDensity N tau alpha M.1
  rw [hfun]
  exact hscaled

/-- Lower semicontinuity of the KW channel Sion objective in the full-rank
reference density variable. -/
private theorem sandwichedChannelOriginalValueLogReferenceDensity_lowerSemicontinuousOn_fullRank
    [Nonempty a1] (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    LowerSemicontinuousOn
      (sandwichedChannelOriginalValueLogReferenceDensity N tau alpha)
      (State.fullRankDensityMatrixSet b1) :=
  ContinuousOn.lowerSemicontinuousOn
    (sandwichedChannelOriginalValueLogReferenceDensity_continuousOn_fullRank
      N tau halpha)

/-- Two-matrix wrapper for the KW channel Sion objective.

The source proof in Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`, applies
Sion to the full-rank reference density `sigma_B` and the input density
`tau_A`.  This wrapper makes both variables matrix-valued so the local Sion API
can be applied directly.  Outside the Sion domains its value is irrelevant. -/
def sandwichedChannelOriginalValueLogMatrix
    (N : Channel a1 b1) (alpha : ℝ) (sigmaM : CMatrix b1) (tauM : CMatrix a1) :
    ℝ := by
  classical
  exact
    if hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1 then
      if hTau : tauM ∈ State.densityMatrixSet a1 then
        let sigma : State b1 :=
          State.densityMatrixSetState sigmaM
            (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
        let tau : State a1 := State.densityMatrixSetState tauM hTau
        alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              alpha)
      else
        0
    else
      0

@[simp]
theorem sandwichedChannelOriginalValueLogMatrix_of_mem
    (N : Channel a1 b1) (alpha : ℝ)
    {sigmaM : CMatrix b1} (hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1)
    {tauM : CMatrix a1} (hTau : tauM ∈ State.densityMatrixSet a1) :
    sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM =
      let sigma : State b1 :=
        State.densityMatrixSetState sigmaM
          (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
      let tau : State a1 := State.densityMatrixSetState tauM hTau
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha) := by
  classical
  simp [sandwichedChannelOriginalValueLogMatrix, hSigma, hTau]

private theorem quasiconvexOn_congr_on
    {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [SMul 𝕜 E] [LE β] {s : Set E} {f g : E → β}
    (hfg : ∀ x ∈ s, f x = g x) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s g := by
  intro r
  have hset : {x | x ∈ s ∧ g x ≤ r} = {x | x ∈ s ∧ f x ≤ r} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
  simpa [hset] using hf r

private theorem quasiconcaveOn_congr_on
    {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [SMul 𝕜 E] [LE β] {s : Set E} {f g : E → β}
    (hfg : ∀ x ∈ s, f x = g x) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s g := by
  intro r
  have hset : {x | x ∈ s ∧ r ≤ g x} = {x | x ∈ s ∧ r ≤ f x} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
  simpa [hset] using hf r

/-- Matrix-domain form of the KW channel Sion exchange, isolated to the
reference-density quasiconvexity input on the full-rank side.

The hypothesis records the convexity consequence of the Khatri--Wilde
polar-decomposition/CB-norm argument in `EA_capacity.tex:2080-2084`, separating
that analytic input from the finite-dimensional Sion bookkeeping. -/
private theorem sandwichedChannelOriginalValueLogMatrix_sion_of_reference_quasiconvexOn
    [Nonempty a1] [Nonempty b1] (N : Channel a1 b1)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hRefQ :
      ∀ tau : State a1,
        QuasiconvexOn ℝ (State.fullRankDensityMatrixSet b1)
          (sandwichedChannelOriginalValueLogReferenceDensity N tau alpha)) :
    (⨅ sigmaM : CMatrix b1,
      ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
        ⨆ tauM : CMatrix a1,
          ⨆ _hTau : tauM ∈ State.densityMatrixSet a1,
            ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
              EReal)) =
      ⨆ tauM : CMatrix a1,
        ⨆ _hTau : tauM ∈ State.densityMatrixSet a1,
          ⨅ sigmaM : CMatrix b1,
            ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                EReal) := by
  let F : {sigmaM : CMatrix b1 // sigmaM ∈ State.fullRankDensityMatrixSet b1} →
      {tauM : CMatrix a1 // tauM ∈ State.densityMatrixSet a1} → EReal :=
    fun sigma tau =>
      ((sandwichedChannelOriginalValueLogMatrix N alpha sigma.1 tau.1 : ℝ) : EReal)
  have hnegMem :
      (⨅ tauM : CMatrix a1,
        ⨅ _hTau : tauM ∈ State.densityMatrixSet a1,
          ⨆ sigmaM : CMatrix b1,
            ⨆ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
              -((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                EReal)) =
        ⨆ sigmaM : CMatrix b1,
          ⨆ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
            ⨅ tauM : CMatrix a1,
              ⨅ _hTau : tauM ∈ State.densityMatrixSet a1,
                -((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                  EReal) := by
    exact State.sion_iInf_iSup_eq_iSup_iInf
      (State.densityMatrixSet_nonempty (a := a1))
      (State.densityMatrixSet_convex (a := a1))
      (State.densityMatrixSet_isCompact (a := a1))
      (fun sigmaM hSigma => by
        let sigma : State b1 :=
          State.densityMatrixSetState sigmaM
            (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
        have hcontE : ContinuousOn
            (fun tauM : CMatrix a1 =>
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                EReal))
            (State.densityMatrixSet a1) := by
          have hcontReal :
              ContinuousOn
                (sandwichedChannelOriginalValueLogDensity N sigma alpha)
                (State.densityMatrixSet a1) :=
            cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_continuousOn_density
              N sigma hSigma.1 halpha
          refine continuous_coe_real_ereal.comp_continuousOn ?_
          refine hcontReal.congr ?_
          intro tauM hTau
          simp [sandwichedChannelOriginalValueLogDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, sigma]
        exact ContinuousOn.lowerSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun sigmaM hSigma => by
        let sigma : State b1 :=
          State.densityMatrixSetState sigmaM
            (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
        have hq :
            QuasiconcaveOn ℝ (State.densityMatrixSet a1)
              (sandwichedChannelOriginalValueLogDensity N sigma alpha) :=
          sandwichedChannelOriginalValueLogDensity_quasiconcaveOn N sigma hSigma.1 halpha
        have hqReal :
            QuasiconcaveOn ℝ (State.densityMatrixSet a1)
              (fun tauM : CMatrix a1 =>
                sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM) := by
          refine quasiconcaveOn_congr_on ?_ hq
          intro tauM hTau
          simp [sandwichedChannelOriginalValueLogDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, sigma]
        have hfinal := hqReal.antitone_comp antitone_ereal_neg_coe
        simpa [Function.comp_def] using hfinal)
      (State.fullRankDensityMatrixSet_convex (a := b1))
      (fun tauM hTau => by
        let tau : State a1 := State.densityMatrixSetState tauM hTau
        have hcontE : ContinuousOn
            (fun sigmaM : CMatrix b1 =>
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                EReal))
            (State.fullRankDensityMatrixSet b1) := by
          have hcontReal :
              ContinuousOn
                (sandwichedChannelOriginalValueLogReferenceDensity N tau alpha)
                (State.fullRankDensityMatrixSet b1) :=
            sandwichedChannelOriginalValueLogReferenceDensity_continuousOn_fullRank
              N tau halpha
          refine continuous_coe_real_ereal.comp_continuousOn ?_
          refine hcontReal.congr ?_
          intro sigmaM hSigma
          simp [sandwichedChannelOriginalValueLogReferenceDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, tau]
        exact ContinuousOn.upperSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun tauM hTau => by
        let tau : State a1 := State.densityMatrixSetState tauM hTau
        have hq :
            QuasiconvexOn ℝ (State.fullRankDensityMatrixSet b1)
              (sandwichedChannelOriginalValueLogReferenceDensity N tau alpha) :=
          hRefQ tau
        have hqReal :
            QuasiconvexOn ℝ (State.fullRankDensityMatrixSet b1)
              (fun sigmaM : CMatrix b1 =>
                sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM) := by
          refine quasiconvexOn_congr_on ?_ hq
          intro sigmaM hSigma
          simp [sandwichedChannelOriginalValueLogReferenceDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, tau]
        have hfinal := hqReal.antitone_comp antitone_ereal_neg_coe
        simpa [Function.comp_def] using hfinal)
  have hnegSub :
      (⨅ tau : {tauM : CMatrix a1 // tauM ∈ State.densityMatrixSet a1},
        ⨆ sigma : {sigmaM : CMatrix b1 // sigmaM ∈ State.fullRankDensityMatrixSet b1},
          -F sigma tau) =
        ⨆ sigma : {sigmaM : CMatrix b1 // sigmaM ∈ State.fullRankDensityMatrixSet b1},
          ⨅ tau : {tauM : CMatrix a1 // tauM ∈ State.densityMatrixSet a1},
            -F sigma tau := by
    simpa [F, iInf_subtype', iSup_subtype'] using hnegMem
  have hsub := ereal_sion_from_neg F hnegSub
  simpa [F, iInf_subtype', iSup_subtype'] using hsub

/-- Logarithmic CB upper bound for the original weighted-`Γ` candidate
associated with a state reference.

This combines the pure rank-one quotient bound with the state denominator
normalization above.  It is the `U = 1` normalized branch of the polar
decomposition route in KW `EA_capacity.tex:2054-2093`. -/
theorem cbOneToAlphaOriginalValue_state_log_le_CBNormExpression
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1) (tau : State a1)
    (hsigma : sigma.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            { matrix := tau.matrix,
              pos := tau.pos,
              trace_le_one := by
                rw [tau.trace_eq_one]
                norm_num }
            alpha) ≤
      sandwichedRenyiCBNormExpression N sigma alpha := by
  let Y : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := tau.matrix,
      pos := tau.pos,
      trace_le_one := by
        rw [tau.trace_eq_one]
        norm_num }
  let psi : Prod a1 a1 → ℂ :=
    fun ra => CFC.rpow tau.matrix (1 / (2 * alpha)) ra.1 ra.2
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hinput :
      MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha = rankOneMatrix psi := by
    simpa [Y, psi] using
      MatrixMap.cbOneToAlphaOriginalInput_eq_rankOne_rpow tau.pos alpha
  have hden_matrix :
      partialTraceB (a := a1) (b := a1) (rankOneMatrix psi) =
        partialTraceB (a := a1) (b := a1)
          (MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha) := by
    rw [← hinput]
  have hden_one :
      psdSchattenPNorm
          (partialTraceB (a := a1) (b := a1) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha =
        1 := by
    calc
      psdSchattenPNorm
          (partialTraceB (a := a1) (b := a1) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (partialTraceB (a := a1) (b := a1)
            (MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha))
          (partialTraceB_posSemidef
            (MatrixMap.cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
          alpha := by
            exact psdSchattenPNorm_congr hden_matrix _ _ alpha
      _ = 1 := by
            simpa [Y] using
              cbOneToAlphaOriginalInput_state_denominator_eq_one tau halpha_pos
  have hden_pos :
      0 <
        psdSchattenPNorm
          (partialTraceB (a := a1) (b := a1) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha := by
    rw [hden_one]
    norm_num
  have hnum_eq :
      psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos psi))
          alpha =
        MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y
          alpha := by
    unfold MatrixMap.cbOneToAlphaOriginalValue
    have hnum_matrix :
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi) =
          MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha) := by
      rw [← hinput]
    exact psdSchattenPNorm_congr hnum_matrix _ _ alpha
  have hnum_pos :
      0 <
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos psi))
          alpha := by
    rw [hnum_eq]
    simpa [Y, MatrixMap.CBOneToAlphaOriginalDomain.ofState] using
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N sigma hsigma tau halpha_pos
  have hmain :=
    sandwichedPureRankOneLogQuotient_le_CBNormExpression
      N sigma halpha psi hden_pos hnum_pos
  rw [hden_one, div_one] at hmain
  rw [hnum_eq] at hmain
  simpa [Y] using hmain

/-- Fixed-side-reference form of KW `EA_capacity.tex:2090-2093`.

After the CB original-domain supremum is restricted to `Tr[Y_R] = 1`, the
weighted-channel CB expression is the supremum over normalized input states
`tau_R`.  This is the logarithmic scalar shell needed before the channel-level
Sion exchange. -/
theorem sandwichedRenyiCBNormExpression_eq_sSup_stateOriginalValue_log
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedRenyiCBNormExpression N sigma alpha =
      sSup (Set.range fun tau : State a1 =>
        alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              alpha)) := by
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let v : State a1 → ℝ := fun tau =>
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau) alpha
  haveI : Nonempty (State a1) := ⟨State.maximallyMixed a1⟩
  have hnorm :
      MatrixMap.cbOneToAlphaNorm Phi hPhi alpha =
        sSup (Set.range v) := by
    simpa [v] using
      MatrixMap.cbOneToAlphaNorm_eq_sSup_stateOriginalValueSet_of_one_lt
        (a1 := a1) Phi hPhi halpha
  have hbdd : BddAbove (Set.range v) := by
    refine ⟨MatrixMap.cbOneToAlphaNorm Phi hPhi alpha, ?_⟩
    rintro y ⟨tau, rfl⟩
    exact MatrixMap.cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      Phi hPhi halpha (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
  have hpos : ∀ x ∈ Set.range v, 0 < x := by
    rintro x ⟨tau, rfl⟩
    simpa [Phi, hPhi, v] using
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N sigma hsigma tau (lt_trans zero_lt_one halpha)
  have hlogSup :
      sSup (log2 '' Set.range v) = log2 (sSup (Set.range v)) :=
    real_log2_sSup_image_eq (Set.range_nonempty v) hbdd hpos
  have hlogImage :
      log2 '' Set.range v = Set.range fun tau : State a1 => log2 (v tau) := by
    ext x
    constructor
    · rintro ⟨y, ⟨tau, rfl⟩, rfl⟩
      exact ⟨tau, rfl⟩
    · rintro ⟨tau, rfl⟩
      exact ⟨v tau, ⟨tau, rfl⟩, rfl⟩
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using sandwichedCoeff_pos halpha)
  have hmulSup :
      coeff * sSup (Set.range fun tau : State a1 => log2 (v tau)) =
        sSup (Set.range fun tau : State a1 => coeff * log2 (v tau)) := by
    rw [sSup_range, sSup_range]
    exact Real.mul_iSup_of_nonneg hcoeff_nonneg
      (fun tau : State a1 => log2 (v tau))
  unfold sandwichedRenyiCBNormExpression
  change coeff * log2 (MatrixMap.cbOneToAlphaNorm Phi hPhi alpha) =
    sSup (Set.range fun tau : State a1 => coeff * log2 (v tau))
  rw [hnorm]
  calc
    coeff * log2 (sSup (Set.range v)) =
        coeff * sSup (Set.range fun tau : State a1 => log2 (v tau)) := by
          rw [← hlogSup, hlogImage]
    _ = sSup (Set.range fun tau : State a1 => coeff * log2 (v tau)) := hmulSup

/-- Full-rank side-reference form of the last KW channel rewrite before Sion.

This is the `inf_{sigma_B} log sup_{rho_R}` surface in
`EA_capacity.tex:2087-2092`, with the fixed-`sigma_B` endpoint supplied by
`sandwichedRenyiCBNormExpression_eq_sSup_stateOriginalValue_log`.  The actual
KW Sion exchange proving equality with the optimized channel mutual
information remains a separate theorem. -/
theorem fullRankCB_sInf_EReal_eq_iInf_stateOriginalValue_log_iSup
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) =
      ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
        ((sSup (Set.range fun tau : State a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha)) : ℝ) : EReal) := by
  rw [sInf_range]
  apply iInf_congr
  intro sigma
  rw [sandwichedRenyiCBNormExpression_eq_sSup_stateOriginalValue_log
    N sigma.1 sigma.2 halpha]

/-- Fixed pure-input KW CB upper bound.

This is the arbitrary-input version of the channel alternate-expression
direction in `EA_capacity.tex:2054-2093`: once a full-rank side reference
`sigma_B` is fixed, the sandwiched mutual information of any full-support
channel output is bounded by the logarithmic CB norm of the weighted channel
map. -/
theorem inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (psi : PureVector (Prod a1 a1))
    (hsigma : sigma.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE psi alpha ≤
      ((sandwichedRenyiCBNormExpression N sigma alpha : ℝ) : EReal) := by
  let rho : State (Prod a1 b1) := N.hypothesisTestingOutputState psi
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let weighted : Prod a1 a1 → ℂ :=
    Matrix.mulVec
      (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix s) (1 : CMatrix a1))
      psi.amp
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hmarg : rho.marginalA = psi.state.marginalA := by
    simpa [rho] using Channel.hypothesisTestingOutputState_marginalA N psi
  have hProdSupport :
      Matrix.Supports (rho.marginalA.prod rho.marginalB).matrix
        (rho.marginalA.prod sigma).matrix := by
    simpa [State.prod_matrix_kronecker] using
      Matrix.Supports.kronecker_right_of_posDef
        rho.marginalA.matrix rho.marginalB.matrix sigma.matrix hsigma
  have hSupport :
      Matrix.Supports rho.matrix (rho.marginalA.prod sigma).matrix :=
    rho.matrix_supports_prod_marginals.trans hProdSupport
  let inner : CMatrix (Prod a1 b1) :=
    State.sandwichedRenyiReferenceInner rho (rho.marginalA.prod sigma).matrix alpha
  let hinner : inner.PosSemidef :=
    State.sandwichedRenyiReferenceInner_posSemidef rho
      (rho.marginalA.prod sigma).pos alpha
  have hinner_eq :
      inner =
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
          (rankOneMatrix weighted) := by
    simpa [inner, rho, s, weighted] using
      referenceInner_eq_referenceLift_weightedRankOne
        N sigma psi hsigma halpha
  have hnorm_eq :
      psdSchattenPNorm inner hinner alpha =
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix weighted))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos weighted))
          alpha := by
    exact psdSchattenPNorm_congr hinner_eq hinner _ alpha
  have hcandidate_eq :
      rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
        ((alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                (rankOneMatrix weighted))
              (MatrixMap.referenceLift_mapsPositive
                (sandwichedSideWeightedMap N sigma alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                (rankOneMatrix_pos weighted))
              alpha) : ℝ) : EReal) := by
    calc
      rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
          ((alpha / (alpha - 1) * log2 (psdSchattenPNorm inner hinner alpha) : ℝ) :
            EReal) := by
            simpa [inner, hinner] using
              State.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
                rho sigma hSupport halpha
      _ =
          ((alpha / (alpha - 1) *
            log2
              (psdSchattenPNorm
                (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                  (rankOneMatrix weighted))
                (MatrixMap.referenceLift_mapsPositive
                  (sandwichedSideWeightedMap N sigma alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                  (rankOneMatrix_pos weighted))
                alpha) : ℝ) : EReal) := by
            rw [hnorm_eq]
  have hden_one :
      psdSchattenPNorm
          (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
          (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
          alpha =
        1 := by
    simpa [s, weighted] using
      weightedRankOne_denominator_eq_one_psd psi halpha
  have hden_pos :
      0 <
        psdSchattenPNorm
          (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
          (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
          alpha := by
    rw [hden_one]
    norm_num
  have hweighted_ne : rankOneMatrix weighted ≠ 0 := by
    intro hzero
    have hpartial_zero :
        partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted) = 0 := by
      rw [hzero]
      ext i j
      simp [partialTraceB]
    have hden_zero :
        psdSchattenPNorm
            (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
            (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
            alpha =
          0 := by
      calc
        psdSchattenPNorm
            (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
            (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
            alpha =
          psdSchattenPNorm (0 : CMatrix a1) Matrix.PosSemidef.zero alpha := by
            exact psdSchattenPNorm_congr hpartial_zero _ _ alpha
        _ = 0 := psdSchattenPNorm_zero alpha (ne_of_gt halpha_pos)
    have hcontr : (0 : ℝ) = 1 := by
      rw [← hden_one, hden_zero]
    norm_num at hcontr
  have hnum_pos :
      0 <
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix weighted))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos weighted))
          alpha := by
    have hPhi_ne :
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
          (rankOneMatrix weighted) ≠ 0 :=
      sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
        N sigma hsigma alpha (rankOneMatrix_pos weighted) hweighted_ne
    exact psdSchattenPNorm_pos_of_ne_zero
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (rankOneMatrix weighted))
      _ hPhi_ne
  have hmain :
      alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
                (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                  (rankOneMatrix weighted))
                (MatrixMap.referenceLift_mapsPositive
                  (sandwichedSideWeightedMap N sigma alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                  (rankOneMatrix_pos weighted))
                alpha /
              psdSchattenPNorm
                (partialTraceB (a := a1) (b := a1) (rankOneMatrix weighted))
                (partialTraceB_posSemidef (rankOneMatrix_pos weighted))
                alpha) ≤
        sandwichedRenyiCBNormExpression N sigma alpha :=
    sandwichedPureRankOneLogQuotient_le_CBNormExpression
      N sigma halpha weighted hden_pos hnum_pos
  rw [hden_one, div_one] at hmain
  calc
    N.inputSandwichedRenyiMutualInformationE psi alpha =
        rho.sandwichedRenyiMutualInformationE alpha := by
          rfl
    _ ≤ rho.sandwichedRenyiMutualInformationCandidateE sigma alpha :=
        State.sandwichedRenyiMutualInformationE_le_candidate rho sigma alpha
    _ =
        ((alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                (rankOneMatrix weighted))
              (MatrixMap.referenceLift_mapsPositive
                (sandwichedSideWeightedMap N sigma alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                (rankOneMatrix_pos weighted))
              alpha) : ℝ) : EReal) := hcandidate_eq
    _ ≤ ((sandwichedRenyiCBNormExpression N sigma alpha : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hmain

/-- Full-rank input-marginal canonical branch of the KW CB upper bound.

This is the same weighted-channel estimate as
`inputSandwichedRenyiMutualInformationE_le_CBNormExpression`, specialized to
the canonical purification of a full-rank input state.  The reference marginal
of this purification is the transpose of the input state, hence full rank. -/
theorem inputSandwichedRenyiMutualInformationE_canonical_marginalB_le_CBNormExpression
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1) (tau : State a1)
    (hsigma : sigma.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE tau.canonicalPurification alpha ≤
      ((sandwichedRenyiCBNormExpression N sigma alpha : ℝ) : EReal) := by
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma tau.canonicalPurification hsigma halpha

/-- KW CB upper bound for pure inputs whose channel-input marginal is full
rank.

The proof follows the source purification step: replace the input by the
canonical purification of its input marginal using a reference isometry, then
apply the full-rank canonical CB estimate. -/
theorem inputSandwichedRenyiMutualInformationE_le_CBNormExpression_of_marginalB_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (psi : PureVector (Prod a1 a1))
    (hsigma : sigma.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE psi alpha ≤
      ((sandwichedRenyiCBNormExpression N sigma alpha : ℝ) : EReal) := by
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma psi hsigma halpha

/-- KW canonical-input equality before taking the CB supremum.

This isolates the exact bridge in `EA_capacity.tex:2054-2079`: after replacing
the pure channel input by the swapped canonical purification of a full-rank
input state, the sandwiched candidate against a full-rank side reference is
the logarithm of the corresponding CB `1 -> alpha` original-domain value. -/
theorem swappedCanonical_sandwichedRenyiMutualInformationCandidateE_eq_cbOriginalValue
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1) (tau : State a1)
    (hsigma : sigma.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    let psi : PureVector (Prod a1 a1) :=
      tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
    let rho : State (Prod a1 b1) := N.hypothesisTestingOutputState psi
    rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
      ((alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            { matrix := tau.matrix,
              pos := tau.pos,
              trace_le_one := by
                rw [tau.trace_eq_one]
                norm_num }
            alpha) : ℝ) : EReal) := by
  let psi : PureVector (Prod a1 a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  let rho : State (Prod a1 b1) := N.hypothesisTestingOutputState psi
  let Y : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := tau.matrix,
      pos := tau.pos,
      trace_le_one := by
        rw [tau.trace_eq_one]
        norm_num }
  change rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
    ((alpha / (alpha - 1) *
      log2
        (MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y
          alpha) : ℝ) : EReal)
  have hmarg : rho.marginalA = tau := by
    calc
      rho.marginalA = psi.state.marginalA := by
        simpa [rho] using Channel.hypothesisTestingOutputState_marginalA N psi
      _ = tau := by
        simpa [psi] using State.canonicalPurification_reindex_prodComm_marginalA tau
  have hSupport :
      Matrix.Supports rho.matrix (rho.marginalA.prod sigma).matrix :=
    State.supports_marginalA_prod_of_side_posDef rho sigma hsigma
  let inner : CMatrix (Prod a1 b1) :=
    State.sandwichedRenyiReferenceInner rho (rho.marginalA.prod sigma).matrix alpha
  let hinner : inner.PosSemidef :=
    State.sandwichedRenyiReferenceInner_posSemidef rho
      (rho.marginalA.prod sigma).pos alpha
  have hinner_eq :
      inner =
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
          (MatrixMap.cbOneToAlphaOriginalInput tau.matrix alpha) := by
    simpa [inner, rho, psi] using
      swappedCanonical_referenceInner_eq_referenceLift_cbOneToAlphaOriginalInput
        N sigma tau halpha
  have hnorm_eq :
      psdSchattenPNorm inner hinner alpha =
        MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y
          alpha := by
    unfold MatrixMap.cbOneToAlphaOriginalValue
    exact psdSchattenPNorm_congr hinner_eq hinner _ alpha
  calc
    rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
        ((alpha / (alpha - 1) * log2 (psdSchattenPNorm inner hinner alpha) : ℝ) :
          EReal) := by
          simpa [inner, hinner] using
            State.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
              rho sigma hSupport halpha
    _ =
        ((alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              Y
              alpha) : ℝ) : EReal) := by
          rw [hnorm_eq]

theorem inputSandwichedRenyiMutualInformationE_swappedCanonical_le_CBNormExpression
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1) (tau : State a1)
    (hsigma : sigma.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha ≤
      ((sandwichedRenyiCBNormExpression N sigma alpha : ℝ) : EReal) := by
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) hsigma halpha

/-- Full-rank channel outputs make a fixed-input sandwiched objective a real
full-rank side-reference infimum.

This is the bookkeeping needed to turn the KW pointwise estimate
`input <= CB(sigma)` into a real lower bound for the whole full-rank
CB-expression family. -/
theorem inputSandwichedRenyiMutualInformationE_eq_coe_fullRankCandidateReal_sInf
    [Nonempty b1] (N : Channel a1 b1) (psi : PureVector (Prod a1 a1))
    (hOut : (N.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOutA : (N.hypothesisTestingOutputState psi).marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE psi alpha =
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        State.sandwichedRenyiMutualInformationCandidateRealPosDef
          (N.hypothesisTestingOutputState psi) sigma.1 hOut hOutA sigma.2
          alpha halpha) : ℝ) : EReal) := by
  haveI : Nonempty {sigma : State b1 // sigma.matrix.PosDef} :=
    ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  let rho : State (Prod a1 b1) := N.hypothesisTestingOutputState psi
  have hraw :
      rho.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
          (State.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOut hOutA sigma.2 alpha halpha : EReal)) := by
    simpa [rho] using
      State.sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
        rho hOut hOutA halpha
  have hbdd :
      BddBelow (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        State.sandwichedRenyiMutualInformationCandidateRealPosDef
          rho sigma.1 hOut hOutA sigma.2 alpha halpha) := by
    exact State.sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
      rho hOut hOutA halpha
  calc
    N.inputSandwichedRenyiMutualInformationE psi alpha =
        rho.sandwichedRenyiMutualInformationE alpha := by
          rfl
    _ =
        sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
          (State.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOut hOutA sigma.2 alpha halpha : EReal)) := hraw
    _ =
        ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
          State.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOut hOutA sigma.2 alpha halpha) : ℝ) : EReal) := by
          exact ereal_sInf_range_coe_eq_coe_real_sInf
            (fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
              State.sandwichedRenyiMutualInformationCandidateRealPosDef
                rho sigma.1 hOut hOutA sigma.2 alpha halpha)
            hbdd
    _ =
        ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
          State.sandwichedRenyiMutualInformationCandidateRealPosDef
            (N.hypothesisTestingOutputState psi) sigma.1 hOut hOutA sigma.2
            alpha halpha) : ℝ) : EReal) := by
          rfl

/-- Fixed full-rank input form of the KW channel alternate expression.

This is the `inf_sigma` identification used after the source Sion step in
`EA_capacity.tex:2054-2093`: for the swapped canonical purification of a
full-rank input state, the full-rank side-reference optimization is exactly the
corresponding CB original-domain value optimization. -/
theorem inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_coe_fullRankCBOriginalValue_sInf
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) (tau : State a1) (htau : tau.matrix.PosDef)
    (hOut : (N.hypothesisTestingOutputState
      (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1))).matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma.1 alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              alpha)) : ℝ) : EReal) := by
  let psi : PureVector (Prod a1 a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  let rho : State (Prod a1 b1) := N.hypothesisTestingOutputState psi
  have hOutRho : rho.matrix.PosDef := by
    simpa [rho, psi] using hOut
  have hmarg : rho.marginalA = tau := by
    calc
      rho.marginalA = psi.state.marginalA := by
        simpa [rho] using Channel.hypothesisTestingOutputState_marginalA N psi
      _ = tau := by
        simpa [psi] using State.canonicalPurification_reindex_prodComm_marginalA tau
  have hOutARho : rho.marginalA.matrix.PosDef := by
    rw [hmarg]
    exact htau
  have hinput :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
          State.sandwichedRenyiMutualInformationCandidateRealPosDef
            (N.hypothesisTestingOutputState psi) sigma.1
            (by simpa [psi] using hOut) (by simpa [rho] using hOutARho)
            sigma.2 alpha halpha) : ℝ) : EReal) := by
    exact inputSandwichedRenyiMutualInformationE_eq_coe_fullRankCandidateReal_sInf
      N psi (by simpa [psi] using hOut) (by simpa [rho] using hOutARho) halpha
  let f : {sigma : State b1 // sigma.matrix.PosDef} → ℝ := fun sigma =>
    State.sandwichedRenyiMutualInformationCandidateRealPosDef
      (N.hypothesisTestingOutputState psi) sigma.1
      (by simpa [psi] using hOut) (by simpa [rho] using hOutARho)
      sigma.2 alpha halpha
  let g : {sigma : State b1 // sigma.matrix.PosDef} → ℝ := fun sigma =>
    alpha / (alpha - 1) *
      log2
        (MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma.1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
          (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
          alpha)
  have hfg : f = g := by
    funext sigma
    have hcandidate :
        rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha =
          (State.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOutRho hOutARho sigma.2 alpha halpha : EReal) :=
      State.sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
        rho sigma.1 hOutRho hOutARho sigma.2 halpha
    have hcb :
        rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha =
          ((g sigma : ℝ) : EReal) := by
      simpa [rho, psi, g, MatrixMap.CBOneToAlphaOriginalDomain.ofState] using
        swappedCanonical_sandwichedRenyiMutualInformationCandidateE_eq_cbOriginalValue
          N sigma.1 tau sigma.2 halpha
    have hE :
        ((State.sandwichedRenyiMutualInformationCandidateRealPosDef
          rho sigma.1 hOutRho hOutARho sigma.2 alpha halpha : ℝ) : EReal) =
          ((g sigma : ℝ) : EReal) :=
      hcandidate.symm.trans hcb
    have hreal : State.sandwichedRenyiMutualInformationCandidateRealPosDef
        rho sigma.1 hOutRho hOutARho sigma.2 alpha halpha = g sigma :=
      EReal.coe_eq_coe_iff.mp hE
    simpa [f, rho] using hreal
  calc
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
        N.inputSandwichedRenyiMutualInformationE psi alpha := by
          rfl
    _ = ((sInf (Set.range f) : ℝ) : EReal) := by
          simpa [f] using hinput
    _ = ((sInf (Set.range g) : ℝ) : EReal) := by
          rw [hfg]
    _ =
        ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha)) : ℝ) : EReal) := by
          rfl

/-- Fixed full-rank input form of the KW channel alternate expression using the
high-`alpha` full-rank side-reference reduction.

Unlike
`inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_coe_fullRankCBOriginalValue_sInf`,
this form does not assume the channel output on the canonical input is
positive definite.  It is the support-closure version of the fixed-input
`inf_sigma` identity needed before the KW Sion exchange in
`EA_capacity.tex:2039-2093`. -/
theorem inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_iInf_fullRankCBOriginalValue
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
      ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma.1 alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              alpha) : ℝ) : EReal) := by
  let psi : PureVector (Prod a1 a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  let rho : State (Prod a1 b1) := N.hypothesisTestingOutputState psi
  have hraw :
      rho.sandwichedRenyiMutualInformationE alpha =
        ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha := by
    exact State.sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha
      rho halpha
  calc
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
        rho.sandwichedRenyiMutualInformationE alpha := by
          rfl
    _ =
        ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha := hraw
    _ =
        ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ((alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha) : ℝ) : EReal) := by
          apply iInf_congr
          intro sigma
          simpa [rho, psi, MatrixMap.CBOneToAlphaOriginalDomain.ofState] using
            swappedCanonical_sandwichedRenyiMutualInformationCandidateE_eq_cbOriginalValue
              N sigma.1 tau sigma.2 halpha

/-- Fixed full-rank input branch after the KW Sion exchange, without assuming
the corresponding channel output is full rank. -/
theorem fullRankCBOriginalValue_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) (tau : State a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
      ((alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha) : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  let psi : PureVector (Prod a1 a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  have heq :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ((alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha) : ℝ) : EReal) := by
    simpa [psi] using
      inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_iInf_fullRankCBOriginalValue
        N tau halpha
  rw [← heq]
  exact N.inputSandwichedRenyiMutualInformationE_le_channel psi alpha

/-- Post-Sion channel branch for KW `EA_capacity.tex:2084-2093`.

Once the source minimax step has exchanged
`inf_sigma sup_tau` with `sup_tau inf_sigma`, each fixed `tau_R` branch is the
swapped-canonical channel input already identified above, hence is bounded by
the optimized channel sandwiched-Renyi mutual information.  This theorem does
not perform the Sion exchange; it is the exact no-extra-hypothesis endpoint
needed immediately after that exchange. -/
theorem fullRankCBOriginalValue_iSup_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    (⨆ tau : State a1, ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
      ((alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha) : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  refine iSup_le ?_
  intro tau
  exact fullRankCBOriginalValue_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    N tau halpha

/-- The exact KW channel alternate-expression Sion exchange.

This is the minimax step in Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`.
It is a transparent predicate used only to keep downstream staging lemmas
readable; proving this predicate, rather than assuming it, is one of the
remaining mathematical obligations for the unconditional channel additivity
theorem. -/
def sandwichedChannelAlternateSionExchange
    (N : Channel a1 b1) (alpha : ℝ) : Prop :=
  (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
    ((sSup (Set.range fun tau : State a1 =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha)) : ℝ) : EReal)) =
    (⨆ tau : State a1,
      ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma.1 alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              alpha) : ℝ) : EReal))

/-- The fixed full-rank `sigma_B` source-side logarithmic channel objective is
bounded above by the corresponding CB-norm expression.

This is the scalar boundedness bridge needed to identify the real `sSup`
surface in `sandwichedChannelAlternateSionExchange` with the `EReal` supremum
surface used by the matrix-domain Sion theorem. -/
private theorem sandwichedChannelOriginalValueLogDensity_bddAbove
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun tau : State a1 =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha)) := by
  refine ⟨sandwichedRenyiCBNormExpression N sigma alpha, ?_⟩
  rintro y ⟨tau, rfl⟩
  exact cbOneToAlphaOriginalValue_state_log_le_CBNormExpression
    N sigma tau hsigma halpha

/-- Predicate-form KW channel Sion exchange from the remaining reference-side
quasiconvexity input.

This theorem removes the bookkeeping gap between the matrix-domain Sion
surface and the channel alternate-expression predicate.  The only remaining
mathematical hypothesis is exactly the reference-density quasiconvexity in
Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`, before the
polar-decomposition/CB-norm argument is applied. -/
theorem sandwichedChannelAlternateSionExchange_of_reference_quasiconvexOn
    [Nonempty a1] [Nonempty b1] (N : Channel a1 b1)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hRefQ :
      ∀ tau : State a1,
        QuasiconvexOn ℝ (State.fullRankDensityMatrixSet b1)
          (sandwichedChannelOriginalValueLogReferenceDensity N tau alpha)) :
    N.sandwichedChannelAlternateSionExchange alpha := by
  haveI : Nonempty (State a1) := ⟨State.maximallyMixed a1⟩
  let stateLog : {sigma : State b1 // sigma.matrix.PosDef} → State a1 → ℝ :=
    fun sigma tau =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha)
  have hleftSup :
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
        ((sSup (Set.range fun tau : State a1 => stateLog sigma tau) : ℝ) :
          EReal)) =
        (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ⨆ tau : State a1, ((stateLog sigma tau : ℝ) : EReal)) := by
    apply iInf_congr
    intro sigma
    have hbdd :
        BddAbove (Set.range fun tau : State a1 => stateLog sigma tau) := by
      simpa [stateLog] using
        sandwichedChannelOriginalValueLogDensity_bddAbove
          N sigma.1 sigma.2 halpha
    exact (ereal_sSup_range_coe_eq_coe_real_sSup
      (fun tau : State a1 => stateLog sigma tau) hbdd).symm
  have hmatrix :=
    sandwichedChannelOriginalValueLogMatrix_sion_of_reference_quasiconvexOn
      N halpha hRefQ
  have hleftToMatrix :
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ⨆ tau : State a1, ((stateLog sigma tau : ℝ) : EReal)) =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
            ⨆ tau : State a1,
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix :
                ℝ) : EReal)) := by
    calc
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ⨆ tau : State a1, ((stateLog sigma tau : ℝ) : EReal))
          =
        (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ⨆ tau : State a1,
            ((sandwichedChannelOriginalValueLogMatrix N alpha sigma.1.matrix tau.matrix :
              ℝ) : EReal)) := by
          apply iInf_congr
          intro sigma
          apply iSup_congr
          intro tau
          have hSigma : sigma.1.matrix ∈ State.fullRankDensityMatrixSet b1 :=
            ⟨sigma.2, sigma.1.trace_eq_one⟩
          have hTau : tau.matrix ∈ State.densityMatrixSet a1 :=
            State.state_matrix_mem_densityMatrixSet tau
          have hSigmaState :
              State.densityMatrixSetState sigma.1.matrix
                  (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma) =
                sigma.1 := by
            apply State.ext
            exact State.densityMatrixSetState_matrix sigma.1.matrix
              (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
          have hTauState :
              State.densityMatrixSetState tau.matrix hTau = tau := by
            apply State.ext
            exact State.densityMatrixSetState_matrix tau.matrix hTau
          simp [stateLog, sandwichedChannelOriginalValueLogMatrix, hSigma, hTau,
            hSigmaState, hTauState]
      _ =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
            ⨆ tau : State a1,
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix :
                ℝ) : EReal)) := by
          exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
            (fun sigmaM : CMatrix b1 =>
              ⨆ tau : State a1,
                ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix :
                  ℝ) : EReal))
  have hrightFromMatrix :
      (⨆ tau : State a1,
          ⨅ sigmaM : CMatrix b1,
            ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix : ℝ) :
                EReal)) =
        (⨆ tau : State a1,
          ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
            ((stateLog sigma tau : ℝ) : EReal)) := by
    apply iSup_congr
    intro tau
    calc
      (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
            ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix : ℝ) :
              EReal))
          =
        (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ((sandwichedChannelOriginalValueLogMatrix N alpha sigma.1.matrix tau.matrix :
            ℝ) : EReal)) := by
          exact (fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
            (fun sigmaM : CMatrix b1 =>
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix :
                ℝ) : EReal))).symm
      _ =
        (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ((stateLog sigma tau : ℝ) : EReal)) := by
          apply iInf_congr
          intro sigma
          have hSigma : sigma.1.matrix ∈ State.fullRankDensityMatrixSet b1 :=
            ⟨sigma.2, sigma.1.trace_eq_one⟩
          have hTau : tau.matrix ∈ State.densityMatrixSet a1 :=
            State.state_matrix_mem_densityMatrixSet tau
          have hSigmaState :
              State.densityMatrixSetState sigma.1.matrix
                  (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma) =
                sigma.1 := by
            apply State.ext
            exact State.densityMatrixSetState_matrix sigma.1.matrix
              (State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
          have hTauState :
              State.densityMatrixSetState tau.matrix hTau = tau := by
            apply State.ext
            exact State.densityMatrixSetState_matrix tau.matrix hTau
          simp [stateLog, sandwichedChannelOriginalValueLogMatrix, hSigma, hTau,
            hSigmaState, hTauState]
  have hmatrixState :
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ⨆ tau : State a1, ((stateLog sigma tau : ℝ) : EReal)) =
        (⨆ tau : State a1,
          ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
            ((stateLog sigma tau : ℝ) : EReal)) := by
    calc
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
          ⨆ tau : State a1, ((stateLog sigma tau : ℝ) : EReal))
          =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
            ⨆ tau : State a1,
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix :
                ℝ) : EReal)) := hleftToMatrix
      _ =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
            ⨆ tauM : CMatrix a1,
              ⨆ _hTau : tauM ∈ State.densityMatrixSet a1,
                ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                  EReal)) := by
          apply iInf_congr
          intro sigmaM
          apply iInf_congr
          intro hSigma
          exact state_iSup_matrix_eq_densityMatrixSet_iSup
            (fun tauM : CMatrix a1 =>
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                EReal))
      _ =
        (⨆ tauM : CMatrix a1,
          ⨆ _hTau : tauM ∈ State.densityMatrixSet a1,
            ⨅ sigmaM : CMatrix b1,
              ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
                ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                  EReal)) := hmatrix
      _ =
        (⨆ tau : State a1,
          ⨅ sigmaM : CMatrix b1,
            ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
              ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tau.matrix : ℝ) :
                EReal)) := by
          exact (state_iSup_matrix_eq_densityMatrixSet_iSup
            (fun tauM : CMatrix a1 =>
              ⨅ sigmaM : CMatrix b1,
                ⨅ _hSigma : sigmaM ∈ State.fullRankDensityMatrixSet b1,
                  ((sandwichedChannelOriginalValueLogMatrix N alpha sigmaM tauM : ℝ) :
                    EReal))).symm
      _ =
        (⨆ tau : State a1,
          ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
            ((stateLog sigma tau : ℝ) : EReal)) := hrightFromMatrix
  unfold sandwichedChannelAlternateSionExchange
  simpa [stateLog] using hleftSup.trans hmatrixState

/-- The KW channel alternate-expression Sion exchange with no remaining
reference-side quasiconvexity hypothesis.

This closes the local minimax gap from Khatri--Wilde 2024,
`EA_capacity.tex:2080-2084`: the full-rank reference density objective is
quasiconvex by the polar-decomposition/CB-norm rewrite above, and the existing
matrix-domain Sion wrapper then gives the channel predicate used by the
alternate expression. -/
theorem sandwichedChannelAlternateSionExchange_proved
    [Nonempty a1] [Nonempty b1] (N : Channel a1 b1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedChannelAlternateSionExchange alpha := by
  refine sandwichedChannelAlternateSionExchange_of_reference_quasiconvexOn
    N halpha ?_
  intro tau
  exact sandwichedChannelOriginalValueLogReferenceDensity_quasiconvexOn_of_raw
    N tau halpha
    (sandwichedChannelOriginalValueReferenceDensity_quasiconvexOn N tau halpha)

/-- Channel alternate-expression lower branch after the KW Sion exchange.

This theorem does not prove Sion's minimax hypothesis.  It records the exact
handoff after the source exchange in
KhatriWilde2024Principles, `EA_capacity.tex:2080-2093`: the already-proved
`inf_sigma sup_tau` CB surface is rewritten to the post-Sion
`sup_tau inf_sigma` surface, and every fixed `tau` branch is the swapped
canonical input branch bounded by the channel mutual information. -/
theorem fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion :
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
        ((sSup (Set.range fun tau : State a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha)) : ℝ) : EReal)) =
        (⨆ tau : State a1,
          ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
            ((alpha / (alpha - 1) *
              log2
                (MatrixMap.cbOneToAlphaOriginalValue
                  (sandwichedSideWeightedMap N sigma.1 alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                  (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                  alpha) : ℝ) : EReal))) :
    sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  rw [fullRankCB_sInf_EReal_eq_iInf_stateOriginalValue_log_iSup N halpha]
  rw [hSion]
  exact fullRankCBOriginalValue_iSup_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    N halpha

/-- Predicate-form version of
`fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion`. -/
theorem fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sionExchange
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion : N.sandwichedChannelAlternateSionExchange alpha) :
    sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  exact fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion
    N halpha (by simpa [sandwichedChannelAlternateSionExchange] using hSion)

/-- KW channel alternate-expression lower branch with the Sion exchange proved.

This is the `>=` half of `EA_capacity.tex:2039-2093`, after discharging the
minimax step in `sandwichedChannelAlternateSionExchange_proved`. -/
theorem fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  exact fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sionExchange
    N halpha (sandwichedChannelAlternateSionExchange_proved N halpha)

/-- Fixed full-rank input branch after the KW Sion exchange.

Once the inner `inf_sigma` has been identified with the swapped canonical
input sandwiched mutual information, optimizing over channel inputs bounds it
by the channel sandwiched-Renyi mutual information. -/
theorem fullRankCBOriginalValue_sInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) (tau : State a1) (htau : tau.matrix.PosDef)
    (hOut : (N.hypothesisTestingOutputState
      (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1))).matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha)) : ℝ) : EReal) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  let psi : PureVector (Prod a1 a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  have heq :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha)) : ℝ) : EReal) := by
    simpa [psi] using
      inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_coe_fullRankCBOriginalValue_sInf
        N tau htau hOut halpha
  rw [← heq]
  exact N.inputSandwichedRenyiMutualInformationE_le_channel psi alpha

/-- A single full-rank channel output gives a real lower bound for the KW
full-rank weighted-channel CB-expression family.

The proof follows KW's channel alternate-expression route in the already
formalized direction: the fixed input objective is a finite real quantity, and
the pointwise weighted-rank-one estimate bounds it by every full-rank
`sigma_B` CB expression. -/
theorem sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_input_output_posDef
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) (psi : PureVector (Prod a1 a1))
    (hOut : (N.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOutA : (N.hypothesisTestingOutputState psi).marginalA.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    BddBelow (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      sandwichedRenyiCBNormExpression N sigma.1 alpha) := by
  haveI : Nonempty {sigma : State b1 // sigma.matrix.PosDef} :=
    ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  let lower : ℝ :=
    sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      State.sandwichedRenyiMutualInformationCandidateRealPosDef
        (N.hypothesisTestingOutputState psi) sigma.1 hOut hOutA sigma.2 alpha
        halpha)
  refine ⟨lower, ?_⟩
  rintro y ⟨sigma, rfl⟩
  have hinput_eq :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ((lower : ℝ) : EReal) := by
    simpa [lower] using
      inputSandwichedRenyiMutualInformationE_eq_coe_fullRankCandidateReal_sInf
        N psi hOut hOutA halpha
  have hpoint :
      N.inputSandwichedRenyiMutualInformationE psi alpha ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal) :=
    inputSandwichedRenyiMutualInformationE_le_CBNormExpression
      N sigma.1 psi sigma.2 halpha
  have hreal :
      ((lower : ℝ) : EReal) ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal) := by
    simpa [hinput_eq] using hpoint
  exact EReal.coe_le_coe_iff.mp hreal

/-- Full-support output hypotheses supply the `BddBelow` side condition needed
by the KW full-rank CB `sInf` bookkeeping. -/
theorem sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : PureVector (Prod a1 a1),
      (N.hypothesisTestingOutputState psi).matrix.PosDef) :
    BddBelow (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      sandwichedRenyiCBNormExpression N sigma.1 alpha) := by
  let psi0 : PureVector (Prod a1 a1) := PureVector.basisPureVector
  have hpsi0 : (N.hypothesisTestingOutputState psi0).matrix.PosDef := hOut psi0
  have hpsi0A : (N.hypothesisTestingOutputState psi0).marginalA.matrix.PosDef :=
    State.marginalA_posDef_of_posDef (N.hypothesisTestingOutputState psi0) hpsi0
  exact sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_input_output_posDef
    N psi0 hpsi0 hpsi0A halpha

/-- Boundedness below of the full-rank weighted-channel CB-expression family.

This removes the historical full-support output hypothesis from
`sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef`.  The
fixed-input lower bound is a real number because the support-convention state
alternate expression realizes the corresponding input mutual information as a
coerced real value. -/
theorem sandwichedRenyiCBNormExpression_fullRank_bddBelow
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    BddBelow (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
      sandwichedRenyiCBNormExpression N sigma.1 alpha) := by
  let psi0 : PureVector (Prod a1 a1) := PureVector.basisPureVector
  let rho : State (Prod a1 b1) := N.hypothesisTestingOutputState psi0
  let chi : PureVector (Prod (Prod a1 b1) (Prod a1 b1)) :=
    rho.canonicalPurification.reindex (Equiv.prodComm (Prod a1 b1) (Prod a1 b1))
  let lower : ℝ :=
    alpha / (alpha - 1) *
      log2
        (sSup (Set.range fun τC : State (Prod a1 b1) =>
          psdSchattenPNorm
            (PureVector.sandwichedMutualInformationACTraceMatrix
              chi.state.marginalAB.marginalA chi τC alpha)
            (PureVector.sandwichedMutualInformationACTraceMatrix_posSemidef
              chi.state.marginalAB.marginalA chi τC alpha)
            (alpha / (2 * alpha - 1))))
  refine ⟨lower, ?_⟩
  rintro y ⟨sigma, rfl⟩
  have hchiAB : chi.state.marginalAB = rho := by
    simpa [chi] using State.canonicalPurification_swap_marginalAB rho
  have hinput_eq :
      N.inputSandwichedRenyiMutualInformationE psi0 alpha = (lower : EReal) := by
    change rho.sandwichedRenyiMutualInformationE alpha = (lower : EReal)
    rw [← hchiAB]
    simpa [lower] using
      PureVector.sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        chi halpha
  have hpoint :
      N.inputSandwichedRenyiMutualInformationE psi0 alpha ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal) :=
    inputSandwichedRenyiMutualInformationE_le_CBNormExpression
      N sigma.1 psi0 sigma.2 halpha
  have hreal :
      (lower : EReal) ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal) := by
    simpa [hinput_eq] using hpoint
  exact EReal.coe_le_coe_iff.mp hreal

/-- KW channel alternate-expression upper bound.

This combines the source-shaped weighted-rank-one step with the
`sup_psi`/`inf_sigma` order bridge.  The proof follows
`EA_capacity.tex:2039-2093`, using the supported PSD-reference branch for
possibly singular input marginals. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hBelow :
      BddBelow (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha)) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  refine sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_of_input_le
    N alpha hBelow ?_
  intro psi sigma
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma.1 psi sigma.2 halpha

/-- KW channel alternate-expression upper bound in extended-real `inf` form.

This is the same `sup_psi`/`inf_sigma` order step as
`sandwichedRenyiMutualInformationE_le_fullRankCB_sInf`, but it keeps the
infimum in `EReal`.  Consequently it does not need a separate bounded-below or
full-support hypothesis; those scalar side conditions only enter when one
identifies this `EReal` infimum with a coerced real infimum. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_EReal
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) := by
  rw [N.sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le (N.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro z ⟨sigma, rfl⟩
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma.1 psi sigma.2 halpha

/-- Channel alternate-expression equality assuming exactly the source Sion
exchange from KW `EA_capacity.tex:2080-2084`.

The forward inequality is the already-proved weighted-rank-one/CB upper bound;
the reverse inequality is
`fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion`.  Thus the
only remaining mathematical obligation for the unconditional channel alternate
expression is the displayed Sion exchange itself. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion :
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
        ((sSup (Set.range fun tau : State a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha)) : ℝ) : EReal)) =
        (⨆ tau : State a1,
          ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
            ((alpha / (alpha - 1) *
              log2
                (MatrixMap.cbOneToAlphaOriginalValue
                  (sandwichedSideWeightedMap N sigma.1 alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                  (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                  alpha) : ℝ) : EReal))) :
    N.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) := by
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_EReal N halpha)
    (fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion
      N halpha hSion)

/-- Predicate-form version of
`sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion`. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sionExchange
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion : N.sandwichedChannelAlternateSionExchange alpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion
    N halpha (by simpa [sandwichedChannelAlternateSionExchange] using hSion)

/-- KW channel alternate expression in `EReal` form, with the Sion step proved.

This is the source statement `EA_capacity.tex:2090-2093` at the full-rank
side-reference surface.  The real-valued `sInf` version below still needs the
separate scalar boundedness/full-support bridge. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sionExchange
    N halpha (sandwichedChannelAlternateSionExchange_proved N halpha)

/-- KW channel alternate expression in real `sInf` form, without full-support
output hypotheses.

The boundedness side condition is supplied by
`sandwichedRenyiCBNormExpression_fullRank_bddBelow`, whose lower bound uses the
support-convention state alternate expression. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  let S := {sigma : State b1 // sigma.matrix.PosDef}
  let f : S → ℝ := fun sigma =>
    sandwichedRenyiCBNormExpression N sigma.1 alpha
  have hBelow : BddBelow (Set.range f) := by
    simpa [S, f] using sandwichedRenyiCBNormExpression_fullRank_bddBelow N halpha
  rw [sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal N halpha]
  simpa [S, f] using ereal_sInf_range_coe_eq_coe_real_sInf f hBelow

/-- Real-valued full-rank CB alternate expression after the KW Sion exchange,
under the full-support output condition that supplies the real `sInf`
boundedness side condition.

This packages two already separated source obligations:
* KW `EA_capacity.tex:2080-2084`, the Sion exchange, supplied as `hSion`;
* the scalar full-rank closure from `EReal` to real `sInf`, supplied here by
  full-support channel outputs.

It is intentionally not the unconditional channel alternate-expression theorem:
the Sion exchange is still an explicit hypothesis. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sion
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : PureVector (Prod a1 a1),
      (N.hypothesisTestingOutputState psi).matrix.PosDef)
    (hSion :
      (⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
        ((sSup (Set.range fun tau : State a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                alpha)) : ℝ) : EReal)) =
        (⨆ tau : State a1,
          ⨅ sigma : {sigma : State b1 // sigma.matrix.PosDef},
            ((alpha / (alpha - 1) *
              log2
                (MatrixMap.cbOneToAlphaOriginalValue
                  (sandwichedSideWeightedMap N sigma.1 alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                  (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                  alpha) : ℝ) : EReal))) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  let S := {sigma : State b1 // sigma.matrix.PosDef}
  let f : S → ℝ := fun sigma => sandwichedRenyiCBNormExpression N sigma.1 alpha
  have hBelow : BddBelow (Set.range f) := by
    simpa [S, f] using
      sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef N halpha hOut
  have hE :
      N.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) := by
    simpa [S, f] using
      sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion
        N halpha hSion
  have hInf :
      sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) =
        ((sInf (Set.range f) : ℝ) : EReal) :=
    ereal_sInf_range_coe_eq_coe_real_sInf f hBelow
  simpa [S, f] using hE.trans hInf

/-- Predicate-form version of
`sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sion`. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : PureVector (Prod a1 a1),
      (N.hypothesisTestingOutputState psi).matrix.PosDef)
    (hSion : N.sandwichedChannelAlternateSionExchange alpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sion
    N halpha hOut (by simpa [sandwichedChannelAlternateSionExchange] using hSion)

/-- Real-valued full-rank CB alternate expression with Sion proved, under the
existing full-support output condition that supplies scalar boundedness. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : PureVector (Prod a1 a1),
      (N.hypothesisTestingOutputState psi).matrix.PosDef) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
    N halpha hOut (sandwichedChannelAlternateSionExchange_proved N halpha)

/-- Full-support channel outputs supply the boundedness side condition in the
KW channel alternate-expression upper bound. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_of_outputs_posDef
    [Nonempty a1] [Nonempty b1]
    (N : Channel a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : PureVector (Prod a1 a1),
      (N.hypothesisTestingOutputState psi).matrix.PosDef) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun sigma : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  exact sandwichedRenyiMutualInformationE_le_fullRankCB_sInf N halpha
    (sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N halpha hOut)

/-- Product-reference version of the KW channel alternate-expression
upper bound.

This is the order step used by the channel subadditivity proof after
restricting the side-reference infimum to product states, matching
`EA_capacity.tex:1247-1252`. -/
theorem sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hBelow :
      BddBelow (Set.range fun
          p : {sigma : State b1 // sigma.matrix.PosDef} ×
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun
          p : {sigma : State b1 // sigma.matrix.PosDef} ×
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha) :
          ℝ) : EReal) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : S1 × S2 → ℝ := fun p =>
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha
  have hInf :
      sInf (Set.range fun p : S1 × S2 => ((f p : ℝ) : EReal)) =
        ((sInf (Set.range f) : ℝ) : EReal) :=
    ereal_sInf_range_coe_eq_coe_real_sInf f (by simpa [S1, S2, f] using hBelow)
  rw [(N1.prod N2).sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le ((N1.prod N2).sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  have hleInf :
      (N1.prod N2).inputSandwichedRenyiMutualInformationE psi alpha ≤
        sInf (Set.range fun p : S1 × S2 => ((f p : ℝ) : EReal)) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro z ⟨p, rfl⟩
    have hsigma : (p.1.1.prod p.2.1).matrix.PosDef :=
      State.prod_posDef p.1.2 p.2.2
    simpa [S1, S2, f] using
      inputSandwichedRenyiMutualInformationE_le_CBNormExpression
        (N1.prod N2) (p.1.1.prod p.2.1) psi hsigma halpha
  simpa [S1, S2, f, hInf] using hleInf

/-- Product-reference KW upper bound in extended-real `inf` form.

This is the product-channel analogue of
`sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_EReal`.  It proves the
source order step after restricting the product channel side reference to
full-rank product states, without importing the real bounded-below hypotheses
used by the scalar split theorem. -/
theorem sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf_EReal
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      sInf (Set.range fun
          p : Prod {sigma : State b1 // sigma.matrix.PosDef}
              {sigma : State b2 // sigma.matrix.PosDef} =>
        ((sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
          alpha : ℝ) : EReal)) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : Prod S1 S2 → ℝ := fun p =>
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha
  rw [(N1.prod N2).sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le ((N1.prod N2).sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro z ⟨p, rfl⟩
  have hsigma : (p.1.1.prod p.2.1).matrix.PosDef :=
    State.prod_posDef p.1.2 p.2.2
  simpa [S1, S2, f] using
    inputSandwichedRenyiMutualInformationE_le_CBNormExpression
      (N1.prod N2) (p.1.1.prod p.2.1) psi hsigma halpha

/-- For full-rank side information, the maximally mixed source-side CB
candidate has strictly positive value under the KW weighted channel map. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_maximallyMixed_pos_of_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        { matrix := (State.maximallyMixed a1).matrix,
          pos := (State.maximallyMixed a1).pos,
          trace_le_one := by
            rw [(State.maximallyMixed a1).trace_eq_one]
            norm_num }
        alpha := by
  let Y0 : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := (State.maximallyMixed a1).matrix,
      pos := (State.maximallyMixed a1).pos,
      trace_le_one := by
        rw [(State.maximallyMixed a1).trace_eq_one]
        norm_num }
  let X : CMatrix (Prod a1 a1) := MatrixMap.cbOneToAlphaOriginalInput Y0.matrix alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef Y0.pos alpha
  have hXne : X ≠ 0 := by
    simpa [X, Y0] using MatrixMap.cbOneToAlphaOriginalInput_maximallyMixed_ne_zero
      (a1 := a1) halpha
  have hPhiXne :
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 :=
    sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
      N sigma hsigma alpha hX hXne
  unfold MatrixMap.cbOneToAlphaOriginalValue
  change 0 <
    psdSchattenPNorm
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ alpha
  exact psdSchattenPNorm_pos_of_ne_zero
    (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ hPhiXne

/-- Full-rank side information makes the KW weighted-channel CB norm strictly
positive, so the source logarithm is on the nonzero branch. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaNorm
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        alpha := by
  let Y0 : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := (State.maximallyMixed a1).matrix,
      pos := (State.maximallyMixed a1).pos,
      trace_le_one := by
        rw [(State.maximallyMixed a1).trace_eq_one]
        norm_num }
  have hval_pos :
      0 <
        MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y0
          alpha := by
    simpa [Y0] using
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_maximallyMixed_pos_of_posDef
        N sigma hsigma (lt_trans zero_lt_one halpha)
  have hval_le :
      MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y0
          alpha ≤
        MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          alpha := by
    exact MatrixMap.cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      (sandwichedSideWeightedMap N sigma alpha)
      (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
      halpha
      Y0
  exact lt_of_lt_of_le hval_pos hval_le

/-- Full-rank side information also makes the KW alternate CB expression
strictly positive after substituting the proved CB alternate-expression theorem. -/
theorem cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_pos_of_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        alpha := by
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N sigma alpha)
    (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
    halpha]
  exact cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
    N sigma hsigma halpha

/-- Product pure input for the sandwiched entanglement-assisted objective of a
product channel, repartitioned from `(A1 x A1) x (A2 x A2)` to
`(A1 x A2) x (A1 x A2)`. -/
def sandwichedRenyiProductInput
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2)) :
    PureVector (Prod (Prod a1 a2) (Prod a1 a2)) :=
  (psi.prod phi).reindex
    (State.bipartiteProductEquiv (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2))

/-- Applying a product channel to a repartitioned product input yields the
repartitioned product of the two individual output states. -/
private theorem applyState_prod_reindex_sandwichedRenyiProductInput
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (rho : State (Prod a1 a1)) (sigma : State (Prod a2 a2)) :
    (((Channel.idChannel (Prod a1 a2)).prod (N1.prod N2)).applyState
        ((rho.prod sigma).reindex
          (State.bipartiteProductEquiv
            (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2)))) =
      ((((Channel.idChannel a1).prod N1).applyState rho).prod
          (((Channel.idChannel a2).prod N2).applyState sigma)).reindex
        (State.bipartiteProductEquiv
          (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2)) := by
  apply State.ext
  ext x y
  rcases x with ⟨xR, xB⟩
  rcases y with ⟨yR, yB⟩
  rcases xR with ⟨xR1, xR2⟩
  rcases xB with ⟨xB1, xB2⟩
  rcases yR with ⟨yR1, yR2⟩
  rcases yB with ⟨yB1, yB2⟩
  simp only [Channel.applyState, Channel.prod, State.reindex_matrix,
    State.prod_matrix_kronecker, Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' =>
          (Matrix.kronecker rho.matrix sigma.matrix).submatrix
            (State.bipartiteProductEquiv
              (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2)).symm
            (State.bipartiteProductEquiv
              (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2)).symm
            (((xR1, xR2), (xB1, xB2)).1, j)
            (((yR1, yR2), (yB1, yB2)).1, j')) =
        Matrix.kronecker
          (fun i i' => rho.matrix (xR1, i) (yR1, i'))
          (fun k k' => sigma.matrix (xR2, k) (yR2, k')) := by
    ext z z'
    rcases z with ⟨z1, z2⟩
    rcases z' with ⟨z1', z2'⟩
    simp [State.bipartiteProductEquiv, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [hslice]
  change MatrixMap.kron N1.map N2.map
      (Matrix.kronecker
        (fun i i' => rho.matrix (xR1, i) (yR1, i'))
        (fun k k' => sigma.matrix (xR2, k) (yR2, k')))
      (xB1, xB2) (yB1, yB2) = _
  rw [MatrixMap.kron_apply_kronecker]
  simp [State.bipartiteProductEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]

/-- Product-channel output states factor on the product pure inputs used by the
sandwiched entanglement-assisted objective. -/
theorem hypothesisTestingOutputState_prod
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2)) :
    (N1.prod N2).hypothesisTestingOutputState
        (sandwichedRenyiProductInput psi phi) =
      (N1.hypothesisTestingOutputState psi).bipartiteProduct
        (N2.hypothesisTestingOutputState phi) := by
  unfold Channel.hypothesisTestingOutputState sandwichedRenyiProductInput
  rw [PureVector.reindex_state, PureVector.prod_state]
  exact applyState_prod_reindex_sandwichedRenyiProductInput
    N1 N2 psi.state phi.state

/-- Product pure inputs reduce the channel sandwiched-Renyi objective to the
bipartite product output state.  This is the first source step in the
superadditivity half of Khatri--Wilde, `EA_capacity.tex:1224-1234`. -/
theorem inputSandwichedRenyiMutualInformationE_prodProductInput
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2))
    (alpha : ℝ) :
    (N1.prod N2).inputSandwichedRenyiMutualInformationE
        (sandwichedRenyiProductInput psi phi) alpha =
      ((N1.hypothesisTestingOutputState psi).bipartiteProduct
        (N2.hypothesisTestingOutputState phi)).sandwichedRenyiMutualInformationE alpha := by
  unfold Channel.inputSandwichedRenyiMutualInformationE
  rw [hypothesisTestingOutputState_prod]

/-- The product-output state value obtained from product pure inputs is below
the optimized product-channel sandwiched-Renyi mutual information.  This is the
order-theoretic supremum step in the superadditivity half of
Khatri--Wilde, `EA_capacity.tex:1224-1234`. -/
theorem bipartiteProduct_output_sandwichedRenyiMutualInformationE_le_prodChannel
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2))
    (alpha : ℝ) :
    ((N1.hypothesisTestingOutputState psi).bipartiteProduct
        (N2.hypothesisTestingOutputState phi)).sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  rw [← inputSandwichedRenyiMutualInformationE_prodProductInput N1 N2 psi phi alpha]
  exact (N1.prod N2).inputSandwichedRenyiMutualInformationE_le_channel
    (sandwichedRenyiProductInput psi phi) alpha

/-- KW superadditivity order bridge for product channels.

This is the supremum step in `EA_capacity.tex:1229-1238`: once the product
output states satisfy the state-level product lower bound, restricting the
channel optimization to product pure inputs gives the corresponding
channel-level lower bound. -/
theorem sandwichedRenyiMutualInformationE_prod_ge_add_of_state_product_ge
    [Nonempty a1] [Nonempty a2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) (alpha : ℝ)
    (hstate :
      ∀ psi : PureVector (Prod a1 a1), ∀ phi : PureVector (Prod a2 a2),
        N1.inputSandwichedRenyiMutualInformationE psi alpha +
            N2.inputSandwichedRenyiMutualInformationE phi alpha ≤
          ((N1.hypothesisTestingOutputState psi).bipartiteProduct
            (N2.hypothesisTestingOutputState phi)).sandwichedRenyiMutualInformationE alpha) :
    N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  haveI : Nonempty (PureVector (Prod a1 a1)) := ⟨PureVector.basisPureVector⟩
  haveI : Nonempty (PureVector (Prod a2 a2)) := ⟨PureVector.basisPureVector⟩
  rw [N1.sandwichedRenyiMutualInformationE_eq_sSup,
    N2.sandwichedRenyiMutualInformationE_eq_sSup]
  refine EReal.add_le_of_forall_lt ?_
  intro x hx y hy
  obtain ⟨value1, hvalue1, hxvalue1⟩ :=
    exists_lt_of_lt_csSup
      (Set.range_nonempty
        (fun psi : PureVector (Prod a1 a1) =>
          N1.inputSandwichedRenyiMutualInformationE psi alpha))
      hx
  obtain ⟨value2, hvalue2, hyvalue2⟩ :=
    exists_lt_of_lt_csSup
      (Set.range_nonempty
        (fun phi : PureVector (Prod a2 a2) =>
          N2.inputSandwichedRenyiMutualInformationE phi alpha))
      hy
  rcases hvalue1 with ⟨psi, rfl⟩
  rcases hvalue2 with ⟨phi, rfl⟩
  exact (EReal.add_lt_add hxvalue1 hyvalue2).le.trans
    ((hstate psi phi).trans
      (bipartiteProduct_output_sandwichedRenyiMutualInformationE_le_prodChannel
        N1 N2 psi phi alpha))

/-- KW superadditivity bridge stated with the eventual state product theorem.

The hypothesis is exactly the state-level lower-bound half of
`EA_capacity.tex:1193-1214`; the conclusion is the channel superadditivity
step used in `EA_capacity.tex:1229-1238`. -/
theorem sandwichedRenyiMutualInformationE_prod_ge_add_of_bipartiteProduct_ge
    [Nonempty a1] [Nonempty a2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) (alpha : ℝ)
    (hstate :
      ∀ xi : State (Prod a1 b1), ∀ omega : State (Prod a2 b2),
        xi.sandwichedRenyiMutualInformationE alpha +
            omega.sandwichedRenyiMutualInformationE alpha ≤
          (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha) :
    N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  refine sandwichedRenyiMutualInformationE_prod_ge_add_of_state_product_ge
    N1 N2 alpha ?_
  intro psi phi
  exact hstate (N1.hypothesisTestingOutputState psi) (N2.hypothesisTestingOutputState phi)

/-- KW channel superadditivity from the completed state-product lower branch.

This is the unconditional version of the `>=` half in
`EA_capacity.tex:1224-1238`: restrict the product-channel optimization to
product pure inputs, then apply state-level product additivity to the two
output states. -/
theorem sandwichedRenyiMutualInformationE_prod_ge_add
    [Nonempty a1] [Nonempty a2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha) :
    N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  refine sandwichedRenyiMutualInformationE_prod_ge_add_of_bipartiteProduct_ge
    N1 N2 alpha ?_
  intro xi omega
  exact State.sandwichedRenyiMutualInformationE_bipartiteProduct_ge_add
    xi omega halpha

/-- The CB `1 -> alpha` norm is multiplicative on the maps underlying product
channels.  This is the channel-level instance of the Khatri--Wilde
subadditivity step, `EA_capacity.tex:1242-1254`, using the source-backed
MatrixMap theorem from the CB-norm module. -/
theorem cbOneToAlphaNorm_prod_map_eq_mul
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm (N1.prod N2).map (N1.prod N2).completelyPositive alpha =
      MatrixMap.cbOneToAlphaNorm N1.map N1.completelyPositive alpha *
        MatrixMap.cbOneToAlphaNorm N2.map N2.completelyPositive alpha := by
  simpa [Channel.prod] using
    (MatrixMap.cbOneToAlphaNorm_kron_eq_mul
      N1.map N1.completelyPositive N2.map N2.completelyPositive halpha)

/-- Channel-level form of the KW weighting-map product identity. -/
theorem sandwichedSideWeightMap_prod_comp_prod_map_posDef
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    (alpha : ℝ) :
    (MatrixMap.sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
        (N1.prod N2).map =
      MatrixMap.kron
        ((MatrixMap.sandwichedSideWeightMap sigma1 alpha).comp N1.map)
        ((MatrixMap.sandwichedSideWeightMap sigma2 alpha).comp N2.map) := by
  simpa [Channel.prod] using
    MatrixMap.sandwichedSideWeightMap_prod_comp_kron_posDef
      sigma1 sigma2 N1.map N2.map hsigma1 hsigma2 alpha

/-- Weighted product-channel maps factor as products of the weighted component
maps on full-rank product references. -/
theorem sandwichedSideWeightedMap_prod_posDef
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    (alpha : ℝ) :
    sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha =
      MatrixMap.kron (sandwichedSideWeightedMap N1 sigma1 alpha)
        (sandwichedSideWeightedMap N2 sigma2 alpha) := by
  simpa [sandwichedSideWeightedMap] using
    sandwichedSideWeightMap_prod_comp_prod_map_posDef
      N1 N2 sigma1 sigma2 hsigma1 hsigma2 alpha

/-- Channel-level weighted-map CB-norm multiplicativity for full-rank product
references, the map-norm step in KW `EA_capacity.tex:1242-1254`. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightMap_prod_map_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm
        ((MatrixMap.sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
          (N1.prod N2).map)
        (MatrixMap.isCompletelyPositive_comp _ _
          (MatrixMap.sandwichedSideWeightMap_completelyPositive
            (sigma1.prod sigma2) alpha)
          (N1.prod N2).completelyPositive)
        alpha =
      MatrixMap.cbOneToAlphaNorm
          ((MatrixMap.sandwichedSideWeightMap sigma1 alpha).comp N1.map)
          (MatrixMap.isCompletelyPositive_comp _ _
            (MatrixMap.sandwichedSideWeightMap_completelyPositive sigma1 alpha)
            N1.completelyPositive)
          alpha *
        MatrixMap.cbOneToAlphaNorm
          ((MatrixMap.sandwichedSideWeightMap sigma2 alpha).comp N2.map)
          (MatrixMap.isCompletelyPositive_comp _ _
            (MatrixMap.sandwichedSideWeightMap_completelyPositive sigma2 alpha)
            N2.completelyPositive)
          alpha := by
  simpa [Channel.prod] using
    MatrixMap.cbOneToAlphaNorm_sandwichedSideWeightMap_prod_comp_kron_eq_mul_posDef
      sigma1 sigma2 N1.map N1.completelyPositive N2.map N2.completelyPositive
      hsigma1 hsigma2 halpha

/-- Weighted-map CB-norm multiplicativity, stated using the local weighted-map
abbreviation. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightedMap_prod_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm
        (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
        (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
          (sigma1.prod sigma2) alpha)
        alpha =
      MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N1 sigma1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
          alpha *
        MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N2 sigma2 alpha)
          (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
          alpha := by
  simpa [sandwichedSideWeightedMap, sandwichedSideWeightedMap_completelyPositive] using
    cbOneToAlphaNorm_sandwichedSideWeightMap_prod_map_eq_mul_posDef
      N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha

/-- Multiplicativity of the KW alternate CB expression for full-rank product
side references, obtained by substituting the proved CB alternate-expression
theorem into the CB-norm multiplicativity step. -/
theorem cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_prod_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
        (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
          (sigma1.prod sigma2) alpha)
        alpha =
      MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap N1 sigma1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
          alpha *
        MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap N2 sigma2 alpha)
          (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
          alpha := by
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
    (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
      (sigma1.prod sigma2) alpha)
    halpha]
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N1 sigma1 alpha)
    (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
    halpha]
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N2 sigma2 alpha)
    (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
    halpha]
  exact cbOneToAlphaNorm_sandwichedSideWeightedMap_prod_eq_mul_posDef
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha

/-- Log-additivity of the KW alternate CB expression on full-rank product
references.  This is the alternate-expression version of the scalar step used
in KW `EA_capacity.tex:1265-1267`. -/
theorem sandwichedRenyiCBAlternateExpression_prod_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2 (MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
          (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
            (sigma1.prod sigma2) alpha)
          alpha) =
      alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N1 sigma1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
            alpha) +
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N2 sigma2 alpha)
            (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
            alpha) := by
  rw [cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_prod_eq_mul_posDef
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha]
  rw [log2_mul
    (ne_of_gt (cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_pos_of_posDef
      N1 sigma1 hsigma1 halpha))
    (ne_of_gt (cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_pos_of_posDef
      N2 sigma2 hsigma2 halpha))]
  ring

/-- Full-rank product-reference infimum split written directly in the KW
alternate CB expression.

This is the source scalar optimization step after the CB alternate-expression
substitution.  The theorem is intentionally restricted to the full-rank domain;
the later channel alternate-expression theorem must still prove the singular
reference closure before this can close the optimized additivity theorem. -/
theorem sandwichedRenyiCBAlternateExpression_fullRankProduct_sInf_eq_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N1 sigma1.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N1 sigma1.1 alpha)
            alpha)))
    (hN2 :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N2 sigma2.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N2 sigma2.1 alpha)
            alpha))) :
    sInf (Set.range fun
        p : {sigma : State b1 // sigma.matrix.PosDef} ×
            {sigma : State b2 // sigma.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2 (MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap (N1.prod N2) (p.1.1.prod p.2.1) alpha)
          (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
            (p.1.1.prod p.2.1) alpha)
          alpha)) =
      sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N1 sigma1.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N1 sigma1.1 alpha)
            alpha)) +
      sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N2 sigma2.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N2 sigma2.1 alpha)
            alpha)) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : S1 → ℝ := fun sigma1 =>
    alpha / (alpha - 1) *
      log2 (MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap N1 sigma1.1 alpha)
        (sandwichedSideWeightedMap_completelyPositive N1 sigma1.1 alpha)
        alpha)
  let g : S2 → ℝ := fun sigma2 =>
    alpha / (alpha - 1) *
      log2 (MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap N2 sigma2.1 alpha)
        (sandwichedSideWeightedMap_completelyPositive N2 sigma2.1 alpha)
        alpha)
  have hpoint :
      (fun p : S1 × S2 =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap (N1.prod N2) (p.1.1.prod p.2.1) alpha)
            (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
              (p.1.1.prod p.2.1) alpha)
            alpha)) =
        (fun p : S1 × S2 => f p.1 + g p.2) := by
    funext p
    exact sandwichedRenyiCBAlternateExpression_prod_posDef
      N1 N2 p.1.1 p.2.1 p.1.2 p.2.2 halpha
  rw [hpoint]
  exact real_sInf_range_prod_add_eq_add_sInf_range f g hN1 hN2

/-- Log-additivity of the KW CB-norm expression on full-rank product
references.  The nonzero hypotheses are only the scalar side conditions needed
for `log2_mul`; they are not a replacement for the missing source alternate
expression equating this candidate with optimized channel mutual information. -/
theorem sandwichedRenyiCBNormExpression_prod_posDef_of_ne
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N1 sigma1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
          alpha ≠ 0)
    (hN2 :
      MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N2 sigma2 alpha)
          (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
          alpha ≠ 0) :
    sandwichedRenyiCBNormExpression (N1.prod N2) (sigma1.prod sigma2) alpha =
      sandwichedRenyiCBNormExpression N1 sigma1 alpha +
        sandwichedRenyiCBNormExpression N2 sigma2 alpha := by
  unfold sandwichedRenyiCBNormExpression
  rw [cbOneToAlphaNorm_sandwichedSideWeightedMap_prod_eq_mul_posDef
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha]
  rw [log2_mul hN1 hN2]
  ring

/-- Log-additivity of the KW CB-norm expression on full-rank product
references, with the logarithm side conditions discharged from positivity of
the weighted-channel CB norms. -/
theorem sandwichedRenyiCBNormExpression_prod_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedRenyiCBNormExpression (N1.prod N2) (sigma1.prod sigma2) alpha =
      sandwichedRenyiCBNormExpression N1 sigma1 alpha +
        sandwichedRenyiCBNormExpression N2 sigma2 alpha := by
  exact sandwichedRenyiCBNormExpression_prod_posDef_of_ne
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha
    (ne_of_gt (cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
      N1 sigma1 hsigma1 halpha))
    (ne_of_gt (cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
      N2 sigma2 hsigma2 halpha))

/-- Full-rank product-reference infimum split for the KW CB expression.

This is the source scalar optimization step in `EA_capacity.tex:1265-1267`,
after the weighted-map product identity and CB-norm multiplicativity have
turned the product-channel integrand into a sum of two independent integrands.
It is deliberately stated on the full-rank reference domain used by the
currently proved logarithmic CB-expression lemmas; the singular-reference
closure still belongs to the missing channel alternate-expression layer. -/
theorem sandwichedRenyiCBNormExpression_fullRankProduct_sInf_eq_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha))
    (hN2 :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha)) :
    sInf (Set.range fun
        p : {sigma : State b1 // sigma.matrix.PosDef} ×
            {sigma : State b2 // sigma.matrix.PosDef} =>
      sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha) =
      sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) +
      sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : S1 → ℝ := fun sigma1 => sandwichedRenyiCBNormExpression N1 sigma1.1 alpha
  let g : S2 → ℝ := fun sigma2 => sandwichedRenyiCBNormExpression N2 sigma2.1 alpha
  have hpoint :
      (fun p : S1 × S2 =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha) =
        (fun p : S1 × S2 => f p.1 + g p.2) := by
    funext p
    exact sandwichedRenyiCBNormExpression_prod_posDef
      N1 N2 p.1.1 p.2.1 p.1.2 p.2.2 halpha
  rw [hpoint]
  exact real_sInf_range_prod_add_eq_add_sInf_range f g hN1 hN2

/-- Boundedness of the full-rank product-reference CB expression follows from
the two one-channel boundedness hypotheses.

This is the order side condition needed before converting the product
full-rank `inf` into the real-valued expression used in the KW
`EA_capacity.tex:1247-1267` subadditivity chain. -/
theorem sandwichedRenyiCBNormExpression_fullRankProduct_bddBelow
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha))
    (hN2 :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha)) :
    BddBelow (Set.range fun
        p : Prod {sigma : State b1 // sigma.matrix.PosDef}
            {sigma : State b2 // sigma.matrix.PosDef} =>
      sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha) := by
  rcases hN1 with ⟨l1, hl1⟩
  rcases hN2 with ⟨l2, hl2⟩
  refine ⟨l1 + l2, ?_⟩
  rintro y ⟨p, rfl⟩
  change l1 + l2 ≤
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha
  rw [sandwichedRenyiCBNormExpression_prod_posDef N1 N2
    p.1.1 p.2.1 p.1.2 p.2.2 halpha]
  exact add_le_add (hl1 ⟨p.1, rfl⟩) (hl2 ⟨p.2, rfl⟩)

/-- Component full-support output hypotheses supply the boundedness side
condition for the product-reference KW channel alternate-expression upper
bound. -/
theorem sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf_of_outputs_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun
          p : {sigma : State b1 // sigma.matrix.PosDef} ×
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha) :
          ℝ) : EReal) := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N1 halpha hOut1
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N2 halpha hOut2
  exact sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf
    N1 N2 halpha
    (sandwichedRenyiCBNormExpression_fullRankProduct_bddBelow
      N1 N2 halpha hN1Below hN2Below)

/-- KW subadditivity assembly bridge for product channels.

This is the order/scalar part of `EA_capacity.tex:1247-1267`: if the pending
channel alternate-expression theorem identifies each optimized channel
quantity with the full-rank CB expression, then restricting the product
channel's side-state infimum to product references and applying CB-norm
multiplicativity gives the `≤` half of channel additivity.

The hypotheses are intentionally explicit: this theorem is not the missing
alternate-expression theorem itself, and it is not a completion claim for
the unconditional channel additivity result. -/
theorem sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha))
    (hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha))
    (hprodAltLe :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range fun
            p : Prod {sigma : State b1 // sigma.matrix.PosDef}
                {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
            alpha) : ℝ) : EReal))
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  let f : S1 → ℝ := fun sigma1 =>
    sandwichedRenyiCBNormExpression N1 sigma1.1 alpha
  let g : S2 → ℝ := fun sigma2 =>
    sandwichedRenyiCBNormExpression N2 sigma2.1 alpha
  let prodF : Prod S1 S2 → ℝ := fun p =>
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) alpha
  have hsplit :
      sInf (Set.range prodF) = sInf (Set.range f) + sInf (Set.range g) := by
    simpa [S1, S2, f, g, prodF] using
      sandwichedRenyiCBNormExpression_fullRankProduct_sInf_eq_add
        N1 N2 halpha hN1Below hN2Below
  have hprodAltLe' :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range prodF) : ℝ) : EReal) := by
    simpa [S1, S2, prodF] using hprodAltLe
  have hN1Alt' :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range f) : ℝ) : EReal) := by
    simpa [S1, f] using hN1Alt
  have hN2Alt' :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range g) : ℝ) : EReal) := by
    simpa [S2, g] using hN2Alt
  calc
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha
        ≤ ((sInf (Set.range prodF) : ℝ) : EReal) := hprodAltLe'
    _ = (((sInf (Set.range f) + sInf (Set.range g) : ℝ)) : EReal) := by
      rw [hsplit]
    _ = ((sInf (Set.range f) : ℝ) : EReal) +
          ((sInf (Set.range g) : ℝ) : EReal) := by
      rw [EReal.coe_add]
    _ = N1.sandwichedRenyiMutualInformationE alpha +
          N2.sandwichedRenyiMutualInformationE alpha := by
      rw [← hN1Alt', ← hN2Alt']

/-- KW subadditivity assembly bridge with the product-channel CB upper bound
generated internally from the two single-channel CB alternate expressions.

Compared with `sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate`,
this removes the separate product boundedness/upper-bound input: it follows
from the weighted-map product identity and the pointwise CB expression
additivity already proved above.  The remaining hypotheses are the genuinely
missing one-channel alternate-expression equalities. -/
theorem sandwichedRenyiMutualInformationE_prod_le_add_of_single_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha))
    (hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha))
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hProdBelow :
      BddBelow (Set.range fun
          p : Prod {sigma : State b1 // sigma.matrix.PosDef}
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
          alpha) :=
    sandwichedRenyiCBNormExpression_fullRankProduct_bddBelow
      N1 N2 halpha hN1Below hN2Below
  have hprodAltLe :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range fun
            p : Prod {sigma : State b1 // sigma.matrix.PosDef}
                {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
            alpha) : ℝ) : EReal) :=
    sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf
      N1 N2 halpha hProdBelow
  exact sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate
    N1 N2 halpha hN1Below hN2Below hprodAltLe hN1Alt hN2Alt

/-- KW channel subadditivity after the channel alternate expression has been
proved in real `sInf` form.

This is the unconditional `<=` half of `EA_capacity.tex:1242-1267`: restrict
the product side-reference optimization to full-rank product references, use
CB-norm multiplicativity, and split the independent real infima. -/
theorem sandwichedRenyiMutualInformationE_prod_le_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) := by
    simpa using sandwichedRenyiCBNormExpression_fullRank_bddBelow N1 halpha
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) := by
    simpa using sandwichedRenyiCBNormExpression_fullRank_bddBelow N2 halpha
  exact sandwichedRenyiMutualInformationE_prod_le_add_of_single_cb_fullRankAlternate
    N1 N2 halpha hN1Below hN2Below
    (sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf N1 halpha)
    (sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf N2 halpha)

/-- Full-support assembly theorem for the KW channel-additivity route.

This combines the already proved product-input superadditivity branch with the
CB alternate-expression subadditivity bridge above.  It is deliberately not the
unconditional channel additivity theorem: the explicit hypotheses record the
real-valued full-rank CB bookkeeping used by this auxiliary assembly and the
channel alternate-expression equality.  The state-product lower branch is
already support-convention/unconditional. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_output_posDef_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef)
    (hprodAltLe :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range fun
            p : Prod {sigma : State b1 // sigma.matrix.PosDef}
                {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
            alpha) : ℝ) : EReal))
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N1 halpha hOut1
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N2 halpha hOut2
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate
      N1 N2 halpha hN1Below hN2Below hprodAltLe hN1Alt hN2Alt)
    (sandwichedRenyiMutualInformationE_prod_ge_add N1 N2 halpha)

/-- Full-support assembly with the product-channel CB upper bound generated
from the source weighted-rank-one route.

Compared with
`sandwichedRenyiMutualInformationE_prod_eq_add_of_output_posDef_cb_fullRankAlternate`,
this removes the bare `hprodAltLe` parameter by proving it from the
product-channel alternate-expression upper-bound branch.  The remaining
hypotheses are exactly the still-missing KW closure/equality pieces for this
auxiliary real-valued full-rank CB assembly: component boundedness supplied by
full-support outputs and the one-channel CB alternate expression identities. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef)
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N1 halpha hOut1
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N2 halpha hOut2
  exact le_antisymm
      (sandwichedRenyiMutualInformationE_prod_le_add_of_single_cb_fullRankAlternate
        N1 N2 halpha hN1Below hN2Below hN1Alt hN2Alt)
      (sandwichedRenyiMutualInformationE_prod_ge_add N1 N2 halpha)

/-- Full-support channel-additivity assembly after the KW Sion exchange.

This replaces the abstract one-channel alternate-expression hypotheses in
`sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_cb_fullRankAlternate`
by the exact Sion exchange from KW `EA_capacity.tex:2080-2084`, combined with
the already formalized full-support scalar closure from `EReal` to real `sInf`.

This remains a full-support auxiliary theorem; the unconditional theorem below
uses the proved Sion exchange and the support-convention product and CB-norm
branches, so the final product-channel theorem carries no full-support output
assumptions. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_sionExchange
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef)
    (hSion1 : N1.sandwichedChannelAlternateSionExchange alpha)
    (hSion2 : N2.sandwichedChannelAlternateSionExchange alpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 alpha) : ℝ) : EReal) :=
    sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
      N1 halpha hOut1 hSion1
  have hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 alpha) : ℝ) : EReal) :=
    sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
      N2 halpha hOut2 hSion2
  exact sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_cb_fullRankAlternate
    N1 N2 halpha hOut1 hOut2 hN1Alt hN2Alt

/-- Full-support channel-additivity assembly with the KW Sion exchange proved. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  exact sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_sionExchange
    N1 N2 halpha hOut1 hOut2
    (sandwichedChannelAlternateSionExchange_proved N1 halpha)
    (sandwichedChannelAlternateSionExchange_proved N2 halpha)

/-- Khatri--Wilde sandwiched entanglement-assisted mutual information is
additive under product channels for `alpha > 1`.

This corresponds to KhatriWilde2024Principles, `EA_capacity.tex:1220-1277`:
the lower bound comes from the state-product theorem over product pure inputs,
and the upper bound comes from the channel CB-norm alternate expression and
multiplicativity. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    {alpha : Real} (halpha : 1 < alpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_prod_le_add N1 N2 halpha)
    (sandwichedRenyiMutualInformationE_prod_ge_add N1 N2 halpha)

end Channel

end

end QIT
