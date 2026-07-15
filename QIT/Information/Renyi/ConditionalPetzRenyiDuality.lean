/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyiSource

/-!
# Downward Petz Renyi duality trace preparation

Source-shaped trace lemmas for Tomamichel2015FiniteResources, `cond.tex`,
Proposition `pr:dual-old`, lines 317--336.

This module formalizes the normalized non-endpoint part currently expressible
by the local API.  The trace route starts with the source rewrite
`Tr(ρ_AB^α ρ_B^(1-α)) =
  Tr(ρ_AB^(α-1) |ρ⟩⟨ρ|_ABC ρ_B^(1-α))`
for a pure tripartite state, then proves the Schmidt/intertwiner bridge from
the `AB|C` side to the `AC|B` side before closing the scalar entropy identity.
Endpoint conventions at `alpha = 0` or `alpha = 1`, and subnormalized-state
variants, are intentionally not claimed here.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

omit [DecidableEq a] in
private theorem trace_mul_kronecker_one_right_eq_partialTraceB_forPetz
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    (X * Matrix.kronecker U (1 : CMatrix b)).trace =
      (partialTraceB (a := a) (b := b) X * U).trace := by
  have hpartial :
      partialTraceB (a := a) (b := b) (X * Matrix.kronecker U (1 : CMatrix b)) =
        partialTraceB (a := a) (b := b) X * U :=
    partialTraceB_mul_leftKroneckerOne X U
  rw [← hpartial, partialTraceB_trace]

private theorem cMatrix_rpow_add_psd_forPetz
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) {p q : Real} (hpq : p + q ≠ 0) :
    CFC.rpow A p * CFC.rpow A q = CFC.rpow A (p + q) := by
  let U : Matrix.unitaryGroup d Complex := hA.isHermitian.eigenvectorUnitary
  let eigen : d → Real := hA.isHermitian.eigenvalues
  have heigen_nonneg : ∀ i, 0 ≤ eigen i := fun i => hA.eigenvalues_nonneg i
  have hA_spec :
      A = (U : CMatrix d) *
        (Matrix.diagonal fun i => (eigen i : Complex)) *
        star (U : CMatrix d) := by
    simpa [U, eigen, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hp :
      CFC.rpow A p =
        (U : CMatrix d) *
          (Matrix.diagonal fun i => ((eigen i ^ p : Real) : Complex)) *
          star (U : CMatrix d) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U eigen heigen_nonneg p
  have hq :
      CFC.rpow A q =
        (U : CMatrix d) *
          (Matrix.diagonal fun i => ((eigen i ^ q : Real) : Complex)) *
          star (U : CMatrix d) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U eigen heigen_nonneg q
  have hpq_pow :
      CFC.rpow A (p + q) =
        (U : CMatrix d) *
          (Matrix.diagonal fun i => ((eigen i ^ (p + q) : Real) : Complex)) *
          star (U : CMatrix d) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U eigen heigen_nonneg (p + q)
  have hconj (M : CMatrix d) :
      (U : CMatrix d) * M * star (U : CMatrix d) =
        (Unitary.conjStarAlgAut Complex (CMatrix d) U) M := by
    simp [Unitary.conjStarAlgAut_apply]
  have hdiag :
      (Matrix.diagonal fun i => ((eigen i ^ p : Real) : Complex) : CMatrix d) *
        (Matrix.diagonal fun i => ((eigen i ^ q : Real) : Complex)) =
        Matrix.diagonal (fun i => ((eigen i ^ (p + q) : Real) : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Real.rpow_add' (heigen_nonneg i) hpq]
    · simp [hij]
  rw [hp, hq, hpq_pow, hconj, hconj, hconj, ← map_mul, hdiag]

private theorem cMatrix_rpow_mulVec_of_posSemidef_eigen_forPetz
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) {v : d -> Complex} {lambda : Real}
    (_hlambda : 0 <= lambda)
    (hev : A.mulVec v = (lambda : Complex) • v) (p : Real) :
    (CFC.rpow A p).mulVec v = ((lambda ^ p : Real) : Complex) • v := by
  let U : Matrix.unitaryGroup d Complex := hA.isHermitian.eigenvectorUnitary
  let eigen : d -> Real := hA.isHermitian.eigenvalues
  let D : CMatrix d := Matrix.diagonal fun i => ((eigen i : Real) : Complex)
  let Dp : CMatrix d := Matrix.diagonal fun i => ((eigen i ^ p : Real) : Complex)
  let w : d -> Complex := (star (U : CMatrix d)).mulVec v
  have hA_spec :
      A = (U : CMatrix d) * D * star (U : CMatrix d) := by
    simpa [U, eigen, D, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hpow :
      CFC.rpow A p = (U : CMatrix d) * Dp * star (U : CMatrix d) := by
    simpa [U, eigen, Dp] using cMatrix_rpow_eq_eigenbasis_diagonal hA p
  have hcoord_left :
      (star (U : CMatrix d)).mulVec (A.mulVec v) = D.mulVec w := by
    rw [hA_spec]
    have hUU : star (U : CMatrix d) * (U : CMatrix d) = 1 :=
      Unitary.coe_star_mul_self U
    have hmat :
        star (U : CMatrix d) * ((U : CMatrix d) * (D * star (U : CMatrix d))) =
          D * star (U : CMatrix d) := by
      calc
        star (U : CMatrix d) * ((U : CMatrix d) * (D * star (U : CMatrix d))) =
            (star (U : CMatrix d) * (U : CMatrix d)) * (D * star (U : CMatrix d)) := by
              noncomm_ring
        _ = 1 * (D * star (U : CMatrix d)) := by rw [hUU]
        _ = D * star (U : CMatrix d) := by simp
    simpa [w, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
      congrArg (fun M : CMatrix d => M.mulVec v) hmat
  have hcoord : D.mulVec w = (lambda : Complex) • w := by
    calc
      D.mulVec w = (star (U : CMatrix d)).mulVec (A.mulVec v) := hcoord_left.symm
      _ = (star (U : CMatrix d)).mulVec ((lambda : Complex) • v) := by rw [hev]
      _ = (lambda : Complex) • w := by
            rw [Matrix.mulVec_smul]
  have hDp_coord : Dp.mulVec w = ((lambda ^ p : Real) : Complex) • w := by
    ext i
    have hi := congrFun hcoord i
    by_cases hwi : w i = 0
    · simp [Dp, Matrix.mulVec, dotProduct, Matrix.diagonal, hwi]
    · have heq_complex : (eigen i : Complex) = (lambda : Complex) := by
        have hi' : (eigen i : Complex) * w i = (lambda : Complex) * w i := by
          simpa [D, Matrix.mulVec, dotProduct, Matrix.diagonal] using hi
        exact mul_right_cancel₀ hwi hi'
      have heq : eigen i = lambda := Complex.ofReal_injective heq_complex
      simp [Dp, Matrix.mulVec, dotProduct, Matrix.diagonal, heq]
  have hv : (U : CMatrix d).mulVec w = v := by
    calc
      (U : CMatrix d).mulVec w =
          ((U : CMatrix d) * star (U : CMatrix d)).mulVec v := by
            simp [w, Matrix.mulVec_mulVec]
      _ = (1 : CMatrix d).mulVec v := by
            have hUU : (U : CMatrix d) * star (U : CMatrix d) = 1 :=
              Unitary.coe_mul_star_self U
            rw [hUU]
      _ = v := by simp
  calc
    (CFC.rpow A p).mulVec v =
        ((U : CMatrix d) * Dp * star (U : CMatrix d)).mulVec v := by rw [hpow]
    _ = (U : CMatrix d).mulVec (Dp.mulVec w) := by
          simp [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (U : CMatrix d).mulVec (((lambda ^ p : Real) : Complex) • w) := by
          rw [hDp_coord]
    _ = ((lambda ^ p : Real) : Complex) • (U : CMatrix d).mulVec w := by
          rw [Matrix.mulVec_smul]
    _ = ((lambda ^ p : Real) : Complex) • v := by rw [hv]

private theorem cMatrix_rpow_mulVec_eigenvectorUnitary_forPetz
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) (k : d) (p : Real) :
    (CFC.rpow A p).mulVec
        (fun x => (hA.isHermitian.eigenvectorUnitary : CMatrix d) x k) =
      ((hA.isHermitian.eigenvalues k ^ p : Real) : Complex) •
        fun x => (hA.isHermitian.eigenvectorUnitary : CMatrix d) x k := by
  apply cMatrix_rpow_mulVec_of_posSemidef_eigen_forPetz
    hA (hA.eigenvalues_nonneg k) ?_ p
  simpa [Matrix.IsHermitian.eigenvectorUnitary_apply] using
    hA.isHermitian.mulVec_eigenvectorBasis k

omit [DecidableEq a] in
/-- Two-sided trace lifting through `Tr_C`.

This is the trace bookkeeping used in Tomamichel2015FiniteResources,
`cond.tex:329-331`, when a trace over `AB` is rewritten as a trace over a
purifying `ABC` system with an identity on `C`. -/
theorem trace_left_right_kronecker_one_eq_partialTraceB
    (R : CMatrix (Prod a b)) (L M : CMatrix a) :
    ((Matrix.kronecker L (1 : CMatrix b) * R *
      Matrix.kronecker M (1 : CMatrix b)).trace).re =
      ((L * partialTraceB (a := a) (b := b) R * M).trace).re := by
  calc
    ((Matrix.kronecker L (1 : CMatrix b) * R *
        Matrix.kronecker M (1 : CMatrix b)).trace).re =
        (((R * Matrix.kronecker M (1 : CMatrix b)) *
          Matrix.kronecker L (1 : CMatrix b)).trace).re := by
          rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    _ = ((partialTraceB (a := a) (b := b)
          (R * Matrix.kronecker M (1 : CMatrix b)) * L).trace).re := by
          rw [trace_mul_kronecker_one_right_eq_partialTraceB_forPetz]
    _ = (((partialTraceB (a := a) (b := b) R * M) * L).trace).re := by
          rw [partialTraceB_mul_leftKroneckerOne]
    _ = ((L * partialTraceB (a := a) (b := b) R * M).trace).re := by
          exact congrArg Complex.re
            (Matrix.trace_mul_cycle (partialTraceB (a := a) (b := b) R) M L)

private theorem trace_mul_rankOneMatrix_mul_eq_dotProduct
    {d : Type*} [Fintype d] [DecidableEq d]
    (L R : CMatrix d) (v : d -> Complex) :
    (L * rankOneMatrix v * R).trace =
      dotProduct (star ((Matrix.conjTranspose R).mulVec v)) (L.mulVec v) := by
  simp [Matrix.trace, Matrix.mul_apply, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm,
    mul_comm]
  apply Finset.sum_congr rfl
  intro _ _
  rw [Finset.sum_comm]

private theorem trace_mul_rankOneMatrix_mul_re_eq_of_mulVec_eq
    {d : Type*} [Fintype d] [DecidableEq d]
    {L R L' R' : CMatrix d} {v : d -> Complex}
    (hL : L.mulVec v = L'.mulVec v)
    (hR : (Matrix.conjTranspose R).mulVec v = (Matrix.conjTranspose R').mulVec v) :
    ((L * rankOneMatrix v * R).trace).re =
      ((L' * rankOneMatrix v * R').trace).re := by
  rw [trace_mul_rankOneMatrix_mul_eq_dotProduct L R v]
  rw [trace_mul_rankOneMatrix_mul_eq_dotProduct L' R' v]
  rw [hL, hR]

private theorem trace_mul_rankOneMatrix_mul_re_eq_of_hermitian_mulVec_eq
    {d : Type*} [Fintype d] [DecidableEq d]
    {L R L' R' : CMatrix d} {v : d -> Complex}
    (hL : L.mulVec v = L'.mulVec v)
    (hR : R.mulVec v = R'.mulVec v)
    (hRherm : Matrix.conjTranspose R = R)
    (hR'herm : Matrix.conjTranspose R' = R') :
    ((L * rankOneMatrix v * R).trace).re =
      ((L' * rankOneMatrix v * R').trace).re := by
  exact trace_mul_rankOneMatrix_mul_re_eq_of_mulVec_eq
    (L := L) (R := R) (L' := L') (R' := R') (v := v) hL
    (by simpa [hRherm, hR'herm] using hR)

private theorem trace_rankOneMatrix_hermitian_swap_re
    {d : Type*} [Fintype d] [DecidableEq d]
    (L R : CMatrix d) (v : d -> Complex)
    (hL : Matrix.conjTranspose L = L) (hR : Matrix.conjTranspose R = R) :
    ((L * rankOneMatrix v * R).trace).re =
      ((R * rankOneMatrix v * L).trace).re := by
  have hct :
      Matrix.conjTranspose (L * rankOneMatrix v * R) =
        R * rankOneMatrix v * L := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp [hL, hR, rankOneMatrix_conjTranspose, Matrix.mul_assoc]
  calc
    ((L * rankOneMatrix v * R).trace).re =
        (star ((L * rankOneMatrix v * R).trace)).re := by simp
    _ = ((Matrix.conjTranspose (L * rankOneMatrix v * R)).trace).re := by
          rw [Matrix.trace_conjTranspose]
    _ = ((R * rankOneMatrix v * L).trace).re := by rw [hct]

private theorem kronecker_left_mulVec_apply_forPetz
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (W : CMatrix d) (v : Prod d e -> Complex) (i : d) (k : e) :
    (Matrix.kronecker W (1 : CMatrix e)).mulVec v (i, k) =
      W.mulVec (fun j => v (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

private theorem kronecker_right_mulVec_apply_forPetz
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (W : CMatrix e) (v : Prod d e -> Complex) (i : d) (k : e) :
    (Matrix.kronecker (1 : CMatrix d) W).mulVec v (i, k) =
      W.mulVec (fun l => v (i, l)) k := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Parameter bookkeeping for the old Petz downward-duality conjugacy
`alpha + beta = 2`. -/
private theorem petzRenyiDualParam_beta_eq_two_sub
    {alpha beta : Real} (hdual : alpha + beta = 2) :
    beta = 2 - alpha := by
  linarith

/-- Under `alpha + beta = 2`, the state exponent on the `AC` side is
`beta - 1 = 1 - alpha`. -/
private theorem petzRenyiDualParam_beta_sub_one_eq_one_sub
    {alpha beta : Real} (hdual : alpha + beta = 2) :
    beta - 1 = 1 - alpha := by
  linarith

/-- Under `alpha + beta = 2`, the reference exponent on the `C` side is
`1 - beta = alpha - 1`. -/
private theorem petzRenyiDualParam_one_sub_beta_eq_sub_one
    {alpha beta : Real} (hdual : alpha + beta = 2) :
    1 - beta = alpha - 1 := by
  linarith

namespace State

/-- Entropy-level Petz duality algebra from equality of the two trace terms.

This lemma is deliberately only the final scalar algebra shell of
Tomamichel2015FiniteResources, `cond.tex:335-336`.  The mathematical content
needed upstream is the source trace bridge equating the two Petz trace terms;
once that equality is available, `alpha + beta = 2` makes the two prefactors
`1/(1-alpha)` and `1/(1-beta)` cancel. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_add_eq_zero_of_traceTerm_eq
    (rhoAB : State (Prod a b)) (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    (rhoAC : State (Prod a c)) (tauC : State c) (htauC : tauC.matrix.PosDef)
    {alpha beta : Real} (halpha_pos : 0 < alpha) (hbeta_pos : 0 < beta)
    (halpha_ne_one : alpha ≠ 1) (hbeta_ne_one : beta ≠ 1)
    (hdual : alpha + beta = 2)
    (htrace :
      rhoAB.conditionalPetzRenyiTraceTerm sigmaB alpha =
        rhoAC.conditionalPetzRenyiTraceTerm tauC beta) :
    rhoAB.conditionalPetzRenyiEntropyCandidateFullReference sigmaB hsigmaB
        alpha halpha_pos halpha_ne_one +
      rhoAC.conditionalPetzRenyiEntropyCandidateFullReference tauC htauC
        beta hbeta_pos hbeta_ne_one =
      0 := by
  let L : Real := log2 (rhoAC.conditionalPetzRenyiTraceTerm tauC beta)
  have halpha_den : 1 - alpha ≠ 0 := by
    intro h
    apply halpha_ne_one
    linarith
  have hbeta_den : 1 - beta ≠ 0 := by
    intro h
    apply hbeta_ne_one
    linarith
  have hcoeff : 1 / (1 - alpha) + 1 / (1 - beta) = 0 := by
    field_simp [halpha_den, hbeta_den]
    linarith
  dsimp [conditionalPetzRenyiEntropyCandidateFullReference]
  rw [htrace]
  change 1 / (1 - alpha) * L + 1 / (1 - beta) * L = 0
  calc
    1 / (1 - alpha) * L + 1 / (1 - beta) * L =
        (1 / (1 - alpha) + 1 / (1 - beta)) * L := by
          ring
    _ = 0 := by
          rw [hcoeff]
          ring

end State

namespace PureVector

def conditionalPetzRenyiABCToACBEquiv :
    Prod (Prod a b) c ≃ Prod (Prod a c) b where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl

private theorem conditionalPetzRenyiABCToACB_marginalAB
    (psi : PureVector (Prod (Prod a b) c)) :
    ((psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state).marginalAB =
      psi.state.marginalAC := by
  apply State.ext
  ext x y
  rcases x with ⟨i, k⟩
  rcases y with ⟨i', k'⟩
  simp [State.marginalAC_matrix, State.marginalAB, State.marginalA,
    partialTraceB, PureVector.reindex_state, State.reindex,
    conditionalPetzRenyiABCToACBEquiv]

private theorem conditionalPetzRenyiABCToACB_marginalBOfABC
    (psi : PureVector (Prod (Prod a b) c)) :
    ((psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state).marginalBOfABC =
      psi.state.marginalAC.marginalB := by
  apply State.ext
  ext k k'
  simp [State.marginalBOfABC, State.marginalAB, State.marginalA,
    State.marginalB, State.marginalAC_matrix, partialTraceA, partialTraceB,
    PureVector.reindex_state, State.reindex, conditionalPetzRenyiABCToACBEquiv]

private theorem conditionalPetzRenyiABCToACB_marginalB
    (psi : PureVector (Prod (Prod a b) c)) :
    ((psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state).marginalB =
      psi.state.marginalBOfABC := by
  apply State.ext
  ext k k'
  simp [State.marginalBOfABC, State.marginalAB, State.marginalA, State.marginalB,
    partialTraceA, partialTraceB, PureVector.reindex_state, State.reindex,
    conditionalPetzRenyiABCToACBEquiv, Fintype.sum_prod_type]

private theorem marginalAC_marginalB_eq_marginalB
    (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAC.marginalB = psi.state.marginalB := by
  apply State.ext
  ext k k'
  simp [State.marginalAC, State.marginalB, partialTraceA, Fintype.sum_prod_type]

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq c] in
private theorem conditionalPetzRenyiABCToACB_submatrix_refC
    (T : CMatrix c) :
    (Matrix.kronecker (1 : CMatrix (Prod a b)) T).submatrix
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm =
      Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) (1 : CMatrix b) := by
  ext x y
  rcases x with ⟨⟨i, k⟩, j⟩
  rcases y with ⟨⟨i', k'⟩, j'⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hj : j = j'
    · subst j'
      simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv]
    · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hj]
  · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hi]

omit [Fintype a] [Fintype b] [DecidableEq b] [Fintype c] in
private theorem conditionalPetzRenyiABCToACB_submatrix_refB
    (T : CMatrix b) :
    (Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) (1 : CMatrix c)).submatrix
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm =
      Matrix.kronecker (1 : CMatrix (Prod a c)) T := by
  ext x y
  rcases x with ⟨⟨i, k⟩, j⟩
  rcases y with ⟨⟨i', k'⟩, j'⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hk : k = k'
    · subst k'
      simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv]
    · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hk]
  · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hi]

private theorem conditionalPetzRenyiABCToACB_projectorTrace_reindex
    (psi : PureVector (Prod (Prod a b) c)) (TC : CMatrix c) (SB : CMatrix b) :
    ((Matrix.kronecker (1 : CMatrix (Prod a b)) TC *
      psi.state.matrix *
      Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) SB) (1 : CMatrix c)).trace).re =
      ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker (1 : CMatrix (Prod a c)) SB).trace).re := by
  let e := conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)
  let A : CMatrix (Prod (Prod a b) c) := Matrix.kronecker (1 : CMatrix (Prod a b)) TC
  let B : CMatrix (Prod (Prod a b) c) := psi.state.matrix
  let C : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) SB) (1 : CMatrix c)
  let phi : PureVector (Prod (Prod a c) b) := psi.reindex e
  have hA :
      A.submatrix e.symm e.symm =
        Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) := by
    simpa [A, e] using conditionalPetzRenyiABCToACB_submatrix_refC
      (a := a) (b := b) (c := c) TC
  have hB : B.submatrix e.symm e.symm = phi.state.matrix := by
    simp [B, phi, PureVector.reindex_state, State.reindex]
  have hC :
      C.submatrix e.symm e.symm =
        Matrix.kronecker (1 : CMatrix (Prod a c)) SB := by
    simpa [C, e] using conditionalPetzRenyiABCToACB_submatrix_refB
      (a := a) (b := b) (c := c) SB
  change ((A * B * C).trace).re =
    ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) *
      phi.state.matrix *
      Matrix.kronecker (1 : CMatrix (Prod a c)) SB).trace).re
  calc
    ((A * B * C).trace).re =
        (((A * B * C).submatrix e.symm e.symm).trace).re := by
          exact congrArg Complex.re
            (State.trace_submatrix_equiv e.symm (A * B * C)).symm
    _ =
        ((A.submatrix e.symm e.symm * B.submatrix e.symm e.symm *
          C.submatrix e.symm e.symm).trace).re := by
          congr 1
          rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    _ =
        ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) *
          phi.state.matrix *
          Matrix.kronecker (1 : CMatrix (Prod a c)) SB).trace).re := by
          rw [hA, hB, hC]

private theorem sum_r_s_s_reorder
    {r s : Type*} [Fintype r] [Fintype s]
    (f : r -> s -> s -> Complex) :
    (∑ x : r, ∑ y : s, ∑ z : s, f x y z) =
      ∑ z : s, ∑ y : s, ∑ x : r, f x y z := by
  calc
    (∑ x : r, ∑ y : s, ∑ z : s, f x y z) =
        ∑ x : r, ∑ z : s, ∑ y : s, f x y z := by
          apply Finset.sum_congr rfl
          intro _ _
          rw [Finset.sum_comm]
    _ = ∑ z : s, ∑ x : r, ∑ y : s, f x y z := by
          rw [Finset.sum_comm]
    _ = ∑ z : s, ∑ y : s, ∑ x : r, f x y z := by
          apply Finset.sum_congr rfl
          intro _ _
          rw [Finset.sum_comm]

private def rightSchmidtSlice
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k : s) : r -> Complex :=
  fun i => ∑ x : s,
    star ((psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) x k) *
      psi.amp (i, x)

private theorem rightSchmidtSlice_marginalB_left_eigen_sum
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k x : s) :
    (∑ y : s,
      star ((psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) y k) *
        psi.state.marginalB.matrix y x) =
      (psi.state.marginalB.pos.isHermitian.eigenvalues k : Complex) *
        star ((psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) x k) := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  let lambda : Real := psi.state.marginalB.pos.isHermitian.eigenvalues k
  have hentry : ∀ i j : s,
      star (psi.state.marginalB.matrix i j) = psi.state.marginalB.matrix j i := by
    intro i j
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun psi.state.marginalB.pos.isHermitian.eq j) i
  have hentry_partial : ∀ i j : s,
      star (partialTraceA (a := r) (b := s) (rankOneMatrix psi.amp) i j) =
        partialTraceA (a := r) (b := s) (rankOneMatrix psi.amp) j i := by
    intro i j
    simpa [State.marginalB] using hentry i j
  have hright := psi.state.marginalB.pos.isHermitian.mulVec_eigenvectorBasis k
  have hcomp :
      (∑ y : s, psi.state.marginalB.matrix x y * (U : CMatrix s) y k) =
        (lambda : Complex) * (U : CMatrix s) x k := by
    have h := congrFun hright x
    simpa [U, lambda, Matrix.mulVec, dotProduct,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  have hstar := congrArg star hcomp
  simpa [U, lambda, State.marginalB, hentry_partial, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm] using hstar

private theorem rightSchmidtSlice_marginalA_eigen
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k : s) :
    psi.state.marginalA.matrix.mulVec (rightSchmidtSlice psi k) =
      (psi.state.marginalB.pos.isHermitian.eigenvalues k : Complex) •
        rightSchmidtSlice psi k := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  let lambda : Real := psi.state.marginalB.pos.isHermitian.eigenvalues k
  ext i
  have hrewrite :
      (psi.state.marginalA.matrix.mulVec (rightSchmidtSlice psi k)) i =
        ∑ x : s, psi.amp (i, x) *
          (∑ y : s, star ((U : CMatrix s) y k) * psi.state.marginalB.matrix y x) := by
    simpa [U, rightSchmidtSlice, State.marginalA, State.marginalB, partialTraceA,
      partialTraceB, Matrix.mulVec, dotProduct, rankOneMatrix_apply, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] using
      (sum_r_s_s_reorder
        (f := fun x y z =>
          psi.amp (i, z) *
            (psi.amp (x, y) *
              (star (psi.amp (x, z)) * star ((U : CMatrix s) y k)))))
  calc
    (psi.state.marginalA.matrix.mulVec (rightSchmidtSlice psi k)) i =
        ∑ x : s, psi.amp (i, x) *
          (∑ y : s, star ((U : CMatrix s) y k) * psi.state.marginalB.matrix y x) := hrewrite
    _ = ∑ x : s, psi.amp (i, x) *
          ((lambda : Complex) * star ((U : CMatrix s) x k)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [rightSchmidtSlice_marginalB_left_eigen_sum (psi := psi) k x]
    _ = ((lambda : Complex) • rightSchmidtSlice psi k) i := by
          simp [U, lambda, rightSchmidtSlice, Finset.mul_sum, mul_assoc, mul_comm]

private theorem rightSchmidtSlice_marginalA_rpow
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k : s) (p : Real) :
    (CFC.rpow psi.state.marginalA.matrix p).mulVec (rightSchmidtSlice psi k) =
      ((psi.state.marginalB.pos.isHermitian.eigenvalues k ^ p : Real) : Complex) •
        rightSchmidtSlice psi k := by
  exact cMatrix_rpow_mulVec_of_posSemidef_eigen_forPetz
    psi.state.marginalA.pos (psi.state.marginalB.pos.eigenvalues_nonneg k)
    (rightSchmidtSlice_marginalA_eigen psi k) p

private theorem rightSchmidtSlice_reconstruct
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (i : r) (x : s) :
    (∑ k : s,
      rightSchmidtSlice psi k i *
        (psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) x k) =
      psi.amp (i, x) := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  have hunit : (U : CMatrix s) * star (U : CMatrix s) = 1 :=
    Unitary.coe_mul_star_self U
  calc
    (∑ k : s, rightSchmidtSlice psi k i * (U : CMatrix s) x k) =
        ∑ y : s, psi.amp (i, y) * ((U : CMatrix s) * star (U : CMatrix s)) x y := by
          simp [U, rightSchmidtSlice, Matrix.mul_apply, Finset.mul_sum, mul_left_comm,
            mul_comm]
          rw [Finset.sum_comm]
    _ = psi.amp (i, x) := by
          rw [hunit]
          simp [Matrix.one_apply]

private theorem pureVector_rpow_marginalA_tensor_one_mulVec_eq_one_tensor_marginalB_rpow_mulVec
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (p : Real) :
    (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)).mulVec
        psi.amp =
      (Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)).mulVec
        psi.amp := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  let lambda : s -> Real := psi.state.marginalB.pos.isHermitian.eigenvalues
  ext z
  rcases z with ⟨i, x⟩
  have hleft :
      (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)).mulVec
          psi.amp (i, x) =
        ∑ k : s, ((lambda k ^ p : Real) : Complex) *
          rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
    rw [kronecker_left_mulVec_apply_forPetz]
    have hvec :
        (fun j : r => psi.amp (j, x)) =
          fun j : r => ∑ k : s, rightSchmidtSlice psi k j * (U : CMatrix s) x k := by
      ext j
      exact (rightSchmidtSlice_reconstruct psi j x).symm
    rw [hvec]
    calc
      (CFC.rpow psi.state.marginalA.matrix p).mulVec
          (fun j : r => ∑ k : s, rightSchmidtSlice psi k j * (U : CMatrix s) x k) i =
          ∑ k : s,
            (CFC.rpow psi.state.marginalA.matrix p).mulVec
              (rightSchmidtSlice psi k) i * (U : CMatrix s) x k := by
            simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm]
            rw [Finset.sum_comm]
      _ = ∑ k : s, ((lambda k ^ p : Real) : Complex) *
            rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
            apply Finset.sum_congr rfl
            intro k _
            have hk := congrFun (rightSchmidtSlice_marginalA_rpow psi k p) i
            simpa [U, lambda, Pi.smul_apply, mul_assoc] using
              congrArg (fun z => z * (U : CMatrix s) x k) hk
  have hright :
      (Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)).mulVec
          psi.amp (i, x) =
        ∑ k : s, ((lambda k ^ p : Real) : Complex) *
          rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
    rw [kronecker_right_mulVec_apply_forPetz]
    have hvec :
        (fun y : s => psi.amp (i, y)) =
          fun y : s => ∑ k : s, rightSchmidtSlice psi k i * (U : CMatrix s) y k := by
      ext y
      exact (rightSchmidtSlice_reconstruct psi i y).symm
    rw [hvec]
    calc
      (CFC.rpow psi.state.marginalB.matrix p).mulVec
          (fun y : s => ∑ k : s, rightSchmidtSlice psi k i * (U : CMatrix s) y k) x =
          ∑ k : s, rightSchmidtSlice psi k i *
            (CFC.rpow psi.state.marginalB.matrix p).mulVec
              (fun y : s => (U : CMatrix s) y k) x := by
            simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
            rw [Finset.sum_comm]
      _ = ∑ k : s, rightSchmidtSlice psi k i *
            (((lambda k ^ p : Real) : Complex) * (U : CMatrix s) x k) := by
            apply Finset.sum_congr rfl
            intro k _
            have hk := congrFun
              (cMatrix_rpow_mulVec_eigenvectorUnitary_forPetz
                psi.state.marginalB.pos k p) x
            simpa [U, lambda, Pi.smul_apply] using
              congrArg (fun z => rightSchmidtSlice psi k i * z) hk
      _ = ∑ k : s, ((lambda k ^ p : Real) : Complex) *
            rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
            apply Finset.sum_congr rfl
            intro k _
            ring
  rw [hleft, hright]

private theorem pureVector_projectorTrace_move_left_rpow
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (K : CMatrix (Prod r s)) (p : Real) :
    ((Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s) *
      psi.state.matrix * K).trace).re =
      ((Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p) *
        psi.state.matrix * K).trace).re := by
  simpa [PureVector.state_matrix] using
    trace_mul_rankOneMatrix_mul_re_eq_of_mulVec_eq
      (L := Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s))
      (R := K)
      (L' := Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p))
      (R' := K)
      (v := psi.amp)
      (pureVector_rpow_marginalA_tensor_one_mulVec_eq_one_tensor_marginalB_rpow_mulVec
        psi p)
      rfl

private theorem pureVector_projectorTrace_move_right_rpow
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (K : CMatrix (Prod r s)) (p : Real) :
    ((K * psi.state.matrix *
      Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)).trace).re =
      ((K * psi.state.matrix *
        Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)).trace).re := by
  let R : CMatrix (Prod r s) :=
    Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)
  let R' : CMatrix (Prod r s) :=
    Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)
  have hR : R.mulVec psi.amp = R'.mulVec psi.amp :=
    (pureVector_rpow_marginalA_tensor_one_mulVec_eq_one_tensor_marginalB_rpow_mulVec
      psi p).symm
  have hRherm : Matrix.conjTranspose R = R := by
    have hpsd : R.PosSemidef := by
      dsimp [R]
      exact Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef (A := psi.state.marginalB.matrix) (s := p)
          psi.state.marginalB.pos)
    exact hpsd.isHermitian.eq
  have hR'herm : Matrix.conjTranspose R' = R' := by
    have hpsd : R'.PosSemidef := by
      dsimp [R']
      exact
        (cMatrix_rpow_posSemidef (A := psi.state.marginalA.matrix) (s := p)
          psi.state.marginalA.pos).kronecker Matrix.PosSemidef.one
    exact hpsd.isHermitian.eq
  simpa [PureVector.state_matrix, R, R'] using
    trace_mul_rankOneMatrix_mul_re_eq_of_hermitian_mulVec_eq
      (L := K) (R := R) (L' := K) (R' := R') (v := psi.amp)
      rfl hR hRherm hR'herm

/-- Middle source trace bridge for downward Petz duality.

This is the formal version of the nontrivial middle equality in
Tomamichel2015FiniteResources, `cond.tex:331-334`:
`Tr(rho_AB^(alpha-1) |psi><psi| rho_B^(1-alpha)) =
  Tr(rho_AC^(1-alpha) |psi><psi| rho_C^(alpha-1))`, with the right-hand side
written in the `ACB` ordering used by the `A|C` Petz trace term.

The proof follows the source route: Schmidt/intertwiner movement across the
pure projector, finite basis relabeling from `ABC` to `ACB`, the corresponding
movement on the `AC|B` split, and a Hermitian trace swap to align with the
existing AC-side projector trace convention. -/
theorem conditionalPetzRenyi_projectorTrace_marginalAB_eq_acbProjectorTrace_dualParam
    (psi : PureVector (Prod (Prod a b) c)) {alpha : Real} :
    ((Matrix.kronecker
        (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
        (1 : CMatrix c) *
      psi.state.matrix *
      Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix a)
          (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
        (1 : CMatrix c)).trace).re =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := by
  let e := conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)
  let phi : PureVector (Prod (Prod a c) b) := psi.reindex e
  let p : Real := alpha - 1
  let q : Real := 1 - alpha
  let KBABC : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a)
        (CFC.rpow psi.state.marginalBOfABC.matrix q))
      (1 : CMatrix c)
  let KCABC₀ : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker (1 : CMatrix (Prod a b))
      (CFC.rpow psi.state.marginalB.matrix p)
  let KACB₀ : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a)
        (CFC.rpow psi.state.marginalB.matrix p))
      (1 : CMatrix b)
  let KACB : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a)
        (CFC.rpow psi.state.marginalAC.marginalB.matrix p))
      (1 : CMatrix b)
  let RBACB : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker (1 : CMatrix (Prod a c))
      (CFC.rpow psi.state.marginalBOfABC.matrix q)
  let RACACB : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker (CFC.rpow psi.state.marginalAC.matrix q) (1 : CMatrix b)
  have hC : psi.state.marginalAC.marginalB = psi.state.marginalB :=
    marginalAC_marginalB_eq_marginalB psi
  have hKACB : KACB₀ = KACB := by
    simpa [KACB₀, KACB] using
      congrArg
        (fun τ : State c =>
          Matrix.kronecker
            (Matrix.kronecker (1 : CMatrix a) (CFC.rpow τ.matrix p))
            (1 : CMatrix b))
        hC.symm
  have hleft :
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix p)
          (1 : CMatrix c) *
        psi.state.matrix * KBABC).trace).re =
        ((KCABC₀ * psi.state.matrix * KBABC).trace).re := by
    have h :=
      pureVector_projectorTrace_move_left_rpow
        (r := Prod a b) (s := c) psi KBABC p
    simpa [KCABC₀, State.marginalAB, State.marginalA] using h
  have hreindex :
      ((KCABC₀ * psi.state.matrix * KBABC).trace).re =
        ((KACB₀ * phi.state.matrix * RBACB).trace).re := by
    have h :=
      conditionalPetzRenyiABCToACB_projectorTrace_reindex
        (a := a) (b := b) (c := c) psi
        (CFC.rpow psi.state.marginalB.matrix p)
        (CFC.rpow psi.state.marginalBOfABC.matrix q)
    simpa [KCABC₀, KBABC, KACB₀, RBACB, phi, e] using h
  have hphiA : phi.state.marginalA = psi.state.marginalAC := by
    simpa [phi, e, State.marginalAB, State.marginalA] using
      conditionalPetzRenyiABCToACB_marginalAB (a := a) (b := b) (c := c) psi
  have hphiB : phi.state.marginalB = psi.state.marginalBOfABC := by
    simpa [phi, e] using
      conditionalPetzRenyiABCToACB_marginalB (a := a) (b := b) (c := c) psi
  have hright :
      ((KACB₀ * phi.state.matrix * RBACB).trace).re =
        ((KACB₀ * phi.state.matrix * RACACB).trace).re := by
    have h :=
      pureVector_projectorTrace_move_right_rpow
        (r := Prod a c) (s := b) phi KACB₀ q
    simpa [RBACB, RACACB, hphiA, hphiB] using h
  have hKherm : Matrix.conjTranspose KACB = KACB := by
    have hpsd : KACB.PosSemidef := by
      dsimp [KACB]
      exact
        (Matrix.PosSemidef.one.kronecker
          (cMatrix_rpow_posSemidef
            (A := psi.state.marginalAC.marginalB.matrix) (s := p)
            psi.state.marginalAC.marginalB.pos)).kronecker
          Matrix.PosSemidef.one
    exact hpsd.isHermitian.eq
  have hRherm : Matrix.conjTranspose RACACB = RACACB := by
    have hpsd : RACACB.PosSemidef := by
      dsimp [RACACB]
      exact
        (cMatrix_rpow_posSemidef
          (A := psi.state.marginalAC.matrix) (s := q)
          psi.state.marginalAC.pos).kronecker Matrix.PosSemidef.one
    exact hpsd.isHermitian.eq
  have hswap :
      ((KACB * phi.state.matrix * RACACB).trace).re =
        ((RACACB * phi.state.matrix * KACB).trace).re := by
    simpa [PureVector.state_matrix] using
      trace_rankOneMatrix_hermitian_swap_re KACB RACACB phi.amp hKherm hRherm
  calc
    ((Matrix.kronecker
        (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
        (1 : CMatrix c) *
      psi.state.matrix *
      Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix a)
          (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
        (1 : CMatrix c)).trace).re =
        ((KCABC₀ * psi.state.matrix * KBABC).trace).re := by
          simpa [p, q, KBABC] using hleft
    _ = ((KACB₀ * phi.state.matrix * RBACB).trace).re := hreindex
    _ = ((KACB₀ * phi.state.matrix * RACACB).trace).re := hright
    _ = ((KACB * phi.state.matrix * RACACB).trace).re := by rw [hKACB]
    _ = ((RACACB * phi.state.matrix * KACB).trace).re := hswap
    _ =
        ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := by
          simp [phi, e, p, q, KACB, RACACB]

/-- First source trace rewrite for downward Petz duality.

For a normalized pure state `ψ_ABC`, this is the formal version of the first
line in Tomamichel2015FiniteResources, `cond.tex:329-331`:
`Tr(ρ_AB^α ρ_B^(1-α)) =
  Tr(ρ_AB^(α-1) |ψ⟩⟨ψ|_ABC ρ_B^(1-α))`.

The assumption `α ≠ 0` is exactly the nonzero-exponent side condition needed
by the current singular-PSD exponent law when combining
`ρ_AB^(α-1) ρ_AB = ρ_AB^α`. -/
theorem conditionalPetzRenyiTraceTerm_marginalAB_eq_projectorTrace
    (psi : PureVector (Prod (Prod a b) c)) {alpha : Real}
    (halpha_ne_zero : alpha ≠ 0) :
    psi.state.marginalAB.conditionalPetzRenyiTraceTerm
        psi.state.marginalBOfABC alpha =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
          (1 : CMatrix c) *
        psi.state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
          (1 : CMatrix c)).trace).re := by
  let rhoAB : State (Prod a b) := psi.state.marginalAB
  let rhoB : State b := psi.state.marginalBOfABC
  let L : CMatrix (Prod a b) := CFC.rpow rhoAB.matrix (alpha - 1)
  let M : CMatrix (Prod a b) :=
    Matrix.kronecker (1 : CMatrix a) (CFC.rpow rhoB.matrix (1 - alpha))
  have hpow_one : CFC.rpow rhoAB.matrix (1 : Real) = rhoAB.matrix :=
    CFC.rpow_one rhoAB.matrix (ha := Matrix.nonneg_iff_posSemidef.mpr rhoAB.pos)
  have hpq : (alpha - 1) + 1 ≠ 0 := by
    intro hzero
    apply halpha_ne_zero
    linarith
  have hpow : L * rhoAB.matrix = CFC.rpow rhoAB.matrix alpha := by
    calc
      L * rhoAB.matrix =
          CFC.rpow rhoAB.matrix (alpha - 1) * CFC.rpow rhoAB.matrix (1 : Real) := by
            rw [hpow_one]
      _ = CFC.rpow rhoAB.matrix ((alpha - 1) + 1) := by
            exact cMatrix_rpow_add_psd_forPetz rhoAB.pos hpq
      _ = CFC.rpow rhoAB.matrix alpha := by
            congr 1
            ring
  have hside :
      CFC.rpow (State.identityTensorStateMatrix (a := a) rhoB) (1 - alpha) = M := by
    simpa [M, State.identityTensorStateMatrix] using
      State.cMatrix_rpow_identity_kronecker (a := a) rhoB.matrix rhoB.pos (1 - alpha)
  dsimp [State.conditionalPetzRenyiTraceTerm]
  change
    ((CFC.rpow rhoAB.matrix alpha *
      CFC.rpow (State.identityTensorStateMatrix (a := a) rhoB) (1 - alpha)).trace).re =
      ((Matrix.kronecker L (1 : CMatrix c) * psi.state.matrix *
        Matrix.kronecker M (1 : CMatrix c)).trace).re
  rw [hside]
  calc
    ((CFC.rpow rhoAB.matrix alpha * M).trace).re =
        ((L * rhoAB.matrix * M).trace).re := by
          rw [← hpow]
    _ =
        ((Matrix.kronecker L (1 : CMatrix c) * psi.state.matrix *
          Matrix.kronecker M (1 : CMatrix c)).trace).re := by
          have htrace :=
            trace_left_right_kronecker_one_eq_partialTraceB
              (a := Prod a b) (b := c) psi.state.matrix L M
          simpa [rhoAB, State.marginalAB, State.marginalA] using htrace.symm

/-- AC-side source trace rewrite for downward Petz duality.

For the reindexed `AC:B` presentation of the same pure vector, this is the
formal version of the final source trace contraction in
Tomamichel2015FiniteResources, `cond.tex:334-335`, read from the Petz trace
term side:
`Tr(ρ_AC^(β-1) |ψ⟩⟨ψ|_ACB ρ_C^(1-β)) =
  Tr(ρ_AC^β ρ_C^(1-β))`.

The theorem is stated with the left side as the Petz trace term so it can be
used directly when closing the `H_β(A|C)` half of Proposition `pr:dual-old`.
The ACB ordering is only a basis relabeling of the original `ABC` pure state;
the declaration names keep the original namespaces unchanged. -/
theorem conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace
    (psi : PureVector (Prod (Prod a b) c)) {beta : Real}
    (hbeta_ne_zero : beta ≠ 0) :
    psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB beta =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (beta - 1))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (1 - beta)))
          (1 : CMatrix b)).trace).re := by
  let e := conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)
  let phi : PureVector (Prod (Prod a c) b) := psi.reindex e
  have hsource :=
    conditionalPetzRenyiTraceTerm_marginalAB_eq_projectorTrace
      (a := a) (b := c) (c := b) phi hbeta_ne_zero
  have hAB : phi.state.marginalAB = psi.state.marginalAC := by
    simpa [phi, e] using conditionalPetzRenyiABCToACB_marginalAB (a := a) (b := b)
      (c := c) psi
  have hB : phi.state.marginalBOfABC = psi.state.marginalAC.marginalB := by
    simpa [phi, e] using
      conditionalPetzRenyiABCToACB_marginalBOfABC (a := a) (b := b) (c := c) psi
  simpa [phi, hAB, hB] using hsource

/-- AC-side projector trace rewrite with the source dual parameter
`alpha + beta = 2` already substituted.

This is the same trace contraction as
`conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace`, but the
exponents are displayed in the form used in Tomamichel2015FiniteResources,
`cond.tex:332-335`: `rho_AC^(1-alpha)` and `rho_C^(alpha-1)`. -/
theorem conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace_dualParam
    (psi : PureVector (Prod (Prod a b) c)) {alpha beta : Real}
    (hbeta_ne_zero : beta ≠ 0) (hdual : alpha + beta = 2) :
    psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB beta =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := by
  have hbase :=
    conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace
      (a := a) (b := b) (c := c) psi hbeta_ne_zero
  have hstate := petzRenyiDualParam_beta_sub_one_eq_one_sub hdual
  have href := petzRenyiDualParam_one_sub_beta_eq_sub_one hdual
  simpa [hstate, href] using hbase

/-- Equality of the two old-Petz trace terms in Proposition `pr:dual-old`.

This combines the first source trace contraction, the Schmidt/intertwiner
middle bridge, and the AC-side final contraction.  The hypotheses `alpha ≠ 0`
and `beta ≠ 0` are the singular-PSD exponent side conditions required by the
current finite-dimensional CFC power API when contracting a projector trace
back to `Tr(rho^alpha sigma^(1-alpha))`. -/
theorem conditionalPetzRenyiTraceTerm_marginalAB_eq_marginalAC_dualParam
    (psi : PureVector (Prod (Prod a b) c)) {alpha beta : Real}
    (halpha_ne_zero : alpha ≠ 0) (hbeta_ne_zero : beta ≠ 0)
    (hdual : alpha + beta = 2) :
    psi.state.marginalAB.conditionalPetzRenyiTraceTerm
        psi.state.marginalBOfABC alpha =
      psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB beta := by
  have hAB :=
    conditionalPetzRenyiTraceTerm_marginalAB_eq_projectorTrace
      (a := a) (b := b) (c := c) psi halpha_ne_zero
  have hbridge :=
    conditionalPetzRenyi_projectorTrace_marginalAB_eq_acbProjectorTrace_dualParam
      (a := a) (b := b) (c := c) (alpha := alpha) psi
  have hAC :=
    conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace_dualParam
      (a := a) (b := b) (c := c) psi hbeta_ne_zero hdual
  calc
    psi.state.marginalAB.conditionalPetzRenyiTraceTerm
        psi.state.marginalBOfABC alpha =
        ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
          (1 : CMatrix c) *
        psi.state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
          (1 : CMatrix c)).trace).re := hAB
    _ =
        ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := hbridge
    _ =
        psi.state.marginalAC.conditionalPetzRenyiTraceTerm
          psi.state.marginalAC.marginalB beta := hAC.symm

/-- Normalized non-endpoint old-Petz downward duality.

This is the current Lean realization of Tomamichel2015FiniteResources,
`cond.tex`, Proposition `pr:dual-old`, lines 317--336, under the local API's
non-endpoint hypotheses.  The theorem assumes full-rank side marginals because
`conditionalPetzRenyiDown` is currently defined through the full-reference
candidate.  It does not claim endpoint conventions at `alpha = 0` or
`alpha = 1`, nor any subnormalized-state extension. -/
theorem conditionalPetzRenyiDown_duality_source
    (psi : PureVector (Prod (Prod a b) c))
    (hB : psi.state.marginalBOfABC.matrix.PosDef)
    (hC : psi.state.marginalAC.marginalB.matrix.PosDef)
    {alpha beta : Real}
    (halpha_pos : 0 < alpha) (hbeta_pos : 0 < beta)
    (_halpha_le_two : alpha ≤ 2) (_hbeta_le_two : beta ≤ 2)
    (halpha_ne_one : alpha ≠ 1) (hbeta_ne_one : beta ≠ 1)
    (hdual : alpha + beta = 2) :
    psi.state.marginalAB.conditionalPetzRenyiDown
        hB alpha halpha_pos halpha_ne_one +
      psi.state.marginalAC.conditionalPetzRenyiDown
        hC beta hbeta_pos hbeta_ne_one =
      0 := by
  have htrace :=
    conditionalPetzRenyiTraceTerm_marginalAB_eq_marginalAC_dualParam
      (a := a) (b := b) (c := c) psi
      (ne_of_gt halpha_pos) (ne_of_gt hbeta_pos) hdual
  have hscalar :=
    State.conditionalPetzRenyiEntropyCandidateFullReference_add_eq_zero_of_traceTerm_eq
      (a := a) (b := b) (c := c)
      psi.state.marginalAB psi.state.marginalBOfABC hB
      psi.state.marginalAC psi.state.marginalAC.marginalB hC
      halpha_pos hbeta_pos halpha_ne_one hbeta_ne_one hdual htrace
  simpa [State.conditionalPetzRenyiDown] using hscalar

end PureVector

end

end QIT
