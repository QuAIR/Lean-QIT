/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Lower.Petz
public import QIT.Coding.EntanglementAssisted.Basic
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.Renyi.RenyiLimit

/-!
# Petz--Renyi alpha-to-one limit for entanglement-assisted information

This module proves the source-shaped `alpha -> 1^-` bridge for the PSD-domain
barred Petz--Renyi mutual information used in the asymptotic
entanglement-assisted achievability step
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:894-982] and the channel
mutual-information definition
[KhatriWilde2024Principles, Chapters/entropies.tex:8132-8144].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace BinaryHypothesisTest

/-- Product eigenbasis unitary for the product of the two marginals of a
bipartite state. -/
def productMarginalEigenvectorUnitary
    (rhoAB : State (Prod a b)) : Matrix.unitaryGroup (Prod a b) ℂ :=
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
    Matrix.kronecker_mem_unitary UA.2 UB.2⟩

/-- Transition from the eigenbasis of `rhoAB` to the product eigenbasis of its
marginals. -/
def productMarginalNussbaumSzkolaTransitionUnitary
    (rhoAB : State (Prod a b)) : Matrix.unitaryGroup (Prod a b) ℂ :=
  rhoAB.pos.isHermitian.eigenvectorUnitary⁻¹ *
    productMarginalEigenvectorUnitary rhoAB

/-- Product-marginal Nussbaum--Szkola overlap
`|<rhoAB_x|rhoA_i tensor rhoB_j>|^2`. -/
def productMarginalNussbaumSzkolaOverlap
    (rhoAB : State (Prod a b)) (x y : Prod a b) : NNReal :=
  ⟨Complex.normSq
    ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB : CMatrix (Prod a b)) x y),
    Complex.normSq_nonneg _⟩

theorem productMarginalNussbaumSzkolaOverlap_row_sum
    (rhoAB : State (Prod a b)) (x : Prod a b) :
    ∑ y : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y = 1 := by
  apply NNReal.eq
  simpa [productMarginalNussbaumSzkolaOverlap] using
    unitary_row_normSq_sum
      (productMarginalNussbaumSzkolaTransitionUnitary rhoAB) x

theorem productMarginalNussbaumSzkolaOverlap_col_sum
    (rhoAB : State (Prod a b)) (y : Prod a b) :
    ∑ x : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y = 1 := by
  apply NNReal.eq
  simpa [productMarginalNussbaumSzkolaOverlap] using
    unitary_col_normSq_sum
      (productMarginalNussbaumSzkolaTransitionUnitary rhoAB) y

/-- Spectral weights of a product of the two marginals, expressed in the
explicit product marginal eigenbasis. -/
def productMarginalSpectralWeight
    (rhoAB : State (Prod a b)) (y : Prod a b) : NNReal :=
  stateSpectralWeight rhoAB.marginalA y.1 *
    stateSpectralWeight rhoAB.marginalB y.2

theorem productMarginalSpectralWeight_sum
    (rhoAB : State (Prod a b)) :
    ∑ y : Prod a b, productMarginalSpectralWeight rhoAB y = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : a, ∑ y : b,
        stateSpectralWeight rhoAB.marginalA x *
          stateSpectralWeight rhoAB.marginalB y)
        =
      ∑ x : a, stateSpectralWeight rhoAB.marginalA x *
        (∑ y : b, stateSpectralWeight rhoAB.marginalB y) := by
        simp [Finset.mul_sum]
    _ = ∑ x : a, stateSpectralWeight rhoAB.marginalA x := by
        simp [stateSpectralWeight_sum]
    _ = 1 := stateSpectralWeight_sum rhoAB.marginalA

/-- The product of the two marginals is diagonalized by the explicit tensor
product of the marginal eigenbases. -/
theorem productMarginal_matrix_eq_productEigenbasis_diagonal
    (rhoAB : State (Prod a b)) :
    (rhoAB.marginalA.prod rhoAB.marginalB).matrix =
      (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) *
        Matrix.diagonal
          (fun y : Prod a b =>
            (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
        star (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  have hA :
      rhoAB.marginalA.matrix =
        (UA : CMatrix a) *
          Matrix.diagonal
            (fun x : a => (((stateSpectralWeight rhoAB.marginalA x : NNReal) : ℝ) : ℂ)) *
          star (UA : CMatrix a) := by
    simpa [UA, stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.marginalA.pos.isHermitian.spectral_theorem
  have hB :
      rhoAB.marginalB.matrix =
        (UB : CMatrix b) *
          Matrix.diagonal
            (fun y : b => (((stateSpectralWeight rhoAB.marginalB y : NNReal) : ℝ) : ℂ)) *
          star (UB : CMatrix b) := by
    simpa [UB, stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.marginalB.pos.isHermitian.spectral_theorem
  change Matrix.kronecker rhoAB.marginalA.matrix rhoAB.marginalB.matrix =
    (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) *
      Matrix.diagonal
        (fun y : Prod a b =>
          (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
      star (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b))
  rw [hA, hB]
  simp [productMarginalEigenvectorUnitary, productMarginalSpectralWeight, UA, UB,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.mul_assoc]

/-- Product-marginal Nussbaum--Szkola model.  Its second spectral basis is the
explicit tensor-product eigenbasis of `rhoAB.marginalA.prod rhoAB.marginalB`,
so the endpoint KL can be identified directly with entropy-form mutual
information. -/
def productMarginalNussbaumSzkolaModel
    (rhoAB : State (Prod a b)) :
    ClassicalBinaryModel ((Prod a b) × (Prod a b)) where
  p xy :=
    stateSpectralWeight rhoAB xy.1 *
      productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2
  q xy :=
    productMarginalSpectralWeight rhoAB xy.2 *
      productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2
  p_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : Prod a b, ∑ y : Prod a b,
          stateSpectralWeight rhoAB x *
            productMarginalNussbaumSzkolaOverlap rhoAB x y)
          =
        ∑ x : Prod a b, stateSpectralWeight rhoAB x *
          (∑ y : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y) := by
          simp [Finset.mul_sum]
      _ = ∑ x : Prod a b, stateSpectralWeight rhoAB x := by
          simp [productMarginalNussbaumSzkolaOverlap_row_sum]
      _ = 1 := stateSpectralWeight_sum rhoAB
  q_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : Prod a b, ∑ y : Prod a b,
          productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y)
          =
        ∑ y : Prod a b, ∑ x : Prod a b,
          productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y := by
          rw [Finset.sum_comm]
      _ =
        ∑ y : Prod a b, productMarginalSpectralWeight rhoAB y *
          (∑ x : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y) := by
          simp [Finset.mul_sum]
      _ = ∑ y : Prod a b, productMarginalSpectralWeight rhoAB y := by
          simp [productMarginalNussbaumSzkolaOverlap_col_sum]
      _ = 1 := productMarginalSpectralWeight_sum rhoAB

/-- The product-marginal Nussbaum--Szkola `p` distribution is supported by
its `q` distribution. -/
theorem productMarginalNussbaumSzkolaModel_p_supportedBy_q
    (rhoAB : State (Prod a b)) :
    (productMarginalNussbaumSzkolaModel rhoAB).pDistribution.SupportedBy
      (productMarginalNussbaumSzkolaModel rhoAB).q := by
  classical
  intro xy hp
  rcases xy with ⟨x, y⟩
  by_contra hq
  have hq_zero :
      (productMarginalNussbaumSzkolaModel rhoAB).q (x, y) = 0 := hq
  have hp_nonzero :
      (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) ≠ 0 := hp
  have hweight_or_overlap :
      productMarginalSpectralWeight rhoAB y = 0 ∨
        productMarginalNussbaumSzkolaOverlap rhoAB x y = 0 := by
    simpa [productMarginalNussbaumSzkolaModel, mul_eq_zero] using hq_zero
  rcases hweight_or_overlap with hweight_zero | hoverlap_zero
  · let Urho : Matrix.unitaryGroup (Prod a b) ℂ :=
      rhoAB.pos.isHermitian.eigenvectorUnitary
    let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
      productMarginalEigenvectorUnitary rhoAB
    let sigma : State (Prod a b) := rhoAB.marginalA.prod rhoAB.marginalB
    let Dprod : CMatrix (Prod a b) :=
      Matrix.diagonal
        (fun i : Prod a b =>
          (((productMarginalSpectralWeight rhoAB i : NNReal) : ℝ) : ℂ))
    have hsigma_spec :
        sigma.matrix = (Uprod : CMatrix (Prod a b)) * Dprod *
          star (Uprod : CMatrix (Prod a b)) := by
      simpa [sigma, Uprod, Dprod] using
        productMarginal_matrix_eq_productEigenbasis_diagonal rhoAB
    have hsigma_mul :
        sigma.matrix * (Uprod : CMatrix (Prod a b)) =
          (Uprod : CMatrix (Prod a b)) * Dprod := by
      rw [hsigma_spec]
      calc
        ((Uprod : CMatrix (Prod a b)) * Dprod *
            star (Uprod : CMatrix (Prod a b))) *
            (Uprod : CMatrix (Prod a b))
            =
          (Uprod : CMatrix (Prod a b)) * Dprod *
            (star (Uprod : CMatrix (Prod a b)) *
              (Uprod : CMatrix (Prod a b))) := by
            noncomm_ring
        _ = (Uprod : CMatrix (Prod a b)) * Dprod := by
            rw [Unitary.coe_star_mul_self]
            simp
    have hsigma_col :
        ∀ k, (sigma.matrix * (Uprod : CMatrix (Prod a b))) k y = 0 := by
      intro k
      rw [hsigma_mul]
      simp [Dprod, Matrix.mul_apply, Matrix.diagonal, hweight_zero]
    let v : Prod a b → ℂ := fun i => (Uprod : CMatrix (Prod a b)) i y
    have hsigma_v : sigma.matrix.mulVec v = 0 := by
      ext k
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hsigma_col k
    have hrho_v : rhoAB.matrix.mulVec v = 0 :=
      rhoAB.matrix_supports_prod_marginals v (by simpa [sigma] using hsigma_v)
    have hrho_col :
        ∀ k, (rhoAB.matrix * (Uprod : CMatrix (Prod a b))) k y = 0 := by
      intro k
      have hk := congrFun hrho_v k
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hk
    have hleft :
        (star (Urho : CMatrix (Prod a b)) * rhoAB.matrix *
          (Uprod : CMatrix (Prod a b))) x y = 0 := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, hrho_col]
    let T : CMatrix (Prod a b) :=
      star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))
    let Drho : CMatrix (Prod a b) :=
      Matrix.diagonal
        (fun i : Prod a b =>
          (((stateSpectralWeight rhoAB i : NNReal) : ℝ) : ℂ))
    have hrho_diag :
        rhoAB.matrix = (Urho : CMatrix (Prod a b)) * Drho *
          star (Urho : CMatrix (Prod a b)) := by
      simpa [Urho, Drho, Function.comp_def, stateSpectralWeight,
        Unitary.conjStarAlgAut_apply]
        using rhoAB.pos.isHermitian.spectral_theorem
    have hleft_diag :
        (star (Urho : CMatrix (Prod a b)) * rhoAB.matrix *
          (Uprod : CMatrix (Prod a b))) x y =
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ) * T x y := by
      have hmatrix :
          star (Urho : CMatrix (Prod a b)) * rhoAB.matrix *
            (Uprod : CMatrix (Prod a b)) =
              Drho * T := by
        rw [hrho_diag]
        dsimp [Drho, T]
        calc
          star (Urho : CMatrix (Prod a b)) *
              ((Urho : CMatrix (Prod a b)) * Drho *
                star (Urho : CMatrix (Prod a b))) *
                (Uprod : CMatrix (Prod a b))
              =
                (star (Urho : CMatrix (Prod a b)) *
                  (Urho : CMatrix (Prod a b))) *
                  (Drho * (star (Urho : CMatrix (Prod a b)) *
                    (Uprod : CMatrix (Prod a b)))) := by
                noncomm_ring
          _ = Drho *
                (star (Urho : CMatrix (Prod a b)) *
                  (Uprod : CMatrix (Prod a b)) ) := by
                rw [Unitary.coe_star_mul_self]
                simp
      have hentry := congrFun (congrFun hmatrix x) y
      simpa [Drho, T, Matrix.mul_apply, Matrix.diagonal] using hentry
    have hprod_zero :
        (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ) * T x y = 0 := by
      rw [← hleft_diag]
      exact hleft
    have hp_zero :
        (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) = 0 := by
      rcases mul_eq_zero.mp hprod_zero with hstate | htransition
      · have hstate_real : ((stateSpectralWeight rhoAB x : NNReal) : ℝ) = 0 :=
          Complex.ofReal_eq_zero.mp hstate
        have hstate_nn : stateSpectralWeight rhoAB x = 0 := by
          apply NNReal.eq
          simpa using hstate_real
        simp [productMarginalNussbaumSzkolaModel, hstate_nn]
      · have hoverlap_nn :
          productMarginalNussbaumSzkolaOverlap rhoAB x y = 0 := by
          have hT_entry :
              ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB :
                CMatrix (Prod a b)) x y) = T x y := by
            simp [productMarginalNussbaumSzkolaTransitionUnitary, T, Urho, Uprod,
              Matrix.star_eq_conjTranspose]
          apply NNReal.eq
          change Complex.normSq
              ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB :
                CMatrix (Prod a b)) x y) = 0
          rw [hT_entry, htransition]
          simp [Complex.normSq]
        simp [productMarginalNussbaumSzkolaModel, hoverlap_nn]
    exact hp_nonzero hp_zero
  · have hp_zero :
        (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) = 0 := by
      simp [productMarginalNussbaumSzkolaModel, hoverlap_zero]
    exact hp_nonzero hp_zero

/-- The `p`-weighted transition probabilities, summed over the global
eigenbasis of `rhoAB`, give the diagonal of `rhoAB` in the product marginal
eigenbasis. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
    (rhoAB : State (Prod a b)) (y : Prod a b) :
    ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
      ((star (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) *
        rhoAB.matrix * (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)))
          y y).re := by
  classical
  let Urho : Matrix.unitaryGroup (Prod a b) ℂ :=
    rhoAB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let D : CMatrix (Prod a b) :=
    Matrix.diagonal
      (fun x : Prod a b => (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ))
  let T : CMatrix (Prod a b) :=
    star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))
  have hrho :
      rhoAB.matrix = (Urho : CMatrix (Prod a b)) * D * star (Urho : CMatrix (Prod a b)) := by
    simpa [Urho, D, stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.pos.isHermitian.spectral_theorem
  have hmatrix :
      star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix *
          (Uprod : CMatrix (Prod a b)) =
        star T * D * T := by
    rw [hrho]
    dsimp [T]
    calc
      star (Uprod : CMatrix (Prod a b)) *
          ((Urho : CMatrix (Prod a b)) * D * star (Urho : CMatrix (Prod a b))) *
          (Uprod : CMatrix (Prod a b))
          =
        (star (Uprod : CMatrix (Prod a b)) * (Urho : CMatrix (Prod a b))) *
          D * (star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))) := by
            noncomm_ring
      _ = star (star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))) *
          D * (star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))) := by
            simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hentry := congrFun (congrFun hmatrix y) y
  have hre := congrArg Complex.re hentry
  have hdiag :
      ((star T * D * T) y y).re =
        ∑ x : Prod a b,
          ((stateSpectralWeight rhoAB x : NNReal) : ℝ) * Complex.normSq (T x y) := by
    simp [D, Matrix.mul_apply, Matrix.diagonal,
      Matrix.star_eq_conjTranspose, Complex.normSq_apply,
      mul_left_comm, mul_comm]
  change
    ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
      ((star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix *
        (Uprod : CMatrix (Prod a b))) y y).re
  rw [hre]
  rw [hdiag]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  have hoverlap :
      ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
        Complex.normSq (T x y) := by
    change Complex.normSq
        ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB : CMatrix (Prod a b)) x y) =
      Complex.normSq (T x y)
    congr 1
  rw [hoverlap]

/-- The first marginal of the product-marginal Nussbaum--Szkola `p`
distribution is the spectral distribution of `rhoAB.marginalA`. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_fst_sum
    (rhoAB : State (Prod a b)) (i : a) :
    ∑ x : Prod a b, ∑ j : b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) =
      ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let M : CMatrix (Prod a b) :=
    star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix * (Uprod : CMatrix (Prod a b))
  have hdiag_sum :
      ∑ j : b, (M (i, j) (i, j)).re =
        ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) := by
    have hpt :=
      partialTraceB_local_unitary_conj (a := a) (b := b)
        rhoAB.matrix UA UB
    have hUprod :
        (Uprod : CMatrix (Prod a b)) =
          Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := by
      rfl
    have hptM :
        partialTraceB (a := a) (b := b) M =
          star (UA : CMatrix a) * rhoAB.marginalA.matrix * (UA : CMatrix a) := by
      simpa [M, Uprod, hUprod, State.marginalA_matrix] using hpt
    have hdiag :
        star (UA : CMatrix a) * rhoAB.marginalA.matrix * (UA : CMatrix a) =
          Matrix.diagonal
            (fun k : a => (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) := by
      have hspec := rhoAB.marginalA.pos.isHermitian.spectral_theorem
      have hρA :
          rhoAB.marginalA.matrix =
            (UA : CMatrix a) *
              Matrix.diagonal
                (fun k : a =>
                  (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) *
              star (UA : CMatrix a) := by
        simpa [UA, stateSpectralWeight, Function.comp_def,
          Unitary.conjStarAlgAut_apply] using hspec
      calc
        star (UA : CMatrix a) * rhoAB.marginalA.matrix * (UA : CMatrix a)
            = star (UA : CMatrix a) *
                ((UA : CMatrix a) *
                  Matrix.diagonal
                    (fun k : a =>
                      (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) *
                  star (UA : CMatrix a)) *
                (UA : CMatrix a) := by
                  rw [hρA]
        _ = (star (UA : CMatrix a) * (UA : CMatrix a)) *
              Matrix.diagonal
                (fun k : a =>
                  (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) *
              (star (UA : CMatrix a) * (UA : CMatrix a)) := by
                noncomm_ring
        _ = Matrix.diagonal
              (fun k : a =>
                (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) := by
              rw [Unitary.coe_star_mul_self]
              simp
    have hentry :
        (partialTraceB (a := a) (b := b) M) i i =
          (Matrix.diagonal
            (fun k : a => (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ))
              : CMatrix a) i i := by
      rw [hptM, hdiag]
    have hre := congrArg Complex.re hentry
    simpa [partialTraceB, Matrix.diagonal, M] using hre
  calc
    ∑ x : Prod a b, ∑ j : b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ)
        =
      ∑ j : b, ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ j : b, (M (i, j) (i, j)).re := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
          rhoAB (i, j)
    _ = ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) := hdiag_sum

/-- The second marginal of the product-marginal Nussbaum--Szkola `p`
distribution is the spectral distribution of `rhoAB.marginalB`. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_snd_sum
    (rhoAB : State (Prod a b)) (j : b) :
    ∑ x : Prod a b, ∑ i : a,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) =
      ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let M : CMatrix (Prod a b) :=
    star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix * (Uprod : CMatrix (Prod a b))
  have hdiag_sum :
      ∑ i : a, (M (i, j) (i, j)).re =
        ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) := by
    have hpt :=
      partialTraceA_local_unitary_conj (a := a) (b := b)
        rhoAB.matrix UA UB
    have hUprod :
        (Uprod : CMatrix (Prod a b)) =
          Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := by
      rfl
    have hptM :
        partialTraceA (a := a) (b := b) M =
          star (UB : CMatrix b) * rhoAB.marginalB.matrix * (UB : CMatrix b) := by
      simpa [M, Uprod, hUprod, State.marginalB_matrix] using hpt
    have hdiag :
        star (UB : CMatrix b) * rhoAB.marginalB.matrix * (UB : CMatrix b) =
          Matrix.diagonal
            (fun k : b => (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) := by
      have hspec := rhoAB.marginalB.pos.isHermitian.spectral_theorem
      have hρB :
          rhoAB.marginalB.matrix =
            (UB : CMatrix b) *
              Matrix.diagonal
                (fun k : b =>
                  (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) *
              star (UB : CMatrix b) := by
        simpa [UB, stateSpectralWeight, Function.comp_def,
          Unitary.conjStarAlgAut_apply] using hspec
      calc
        star (UB : CMatrix b) * rhoAB.marginalB.matrix * (UB : CMatrix b)
            = star (UB : CMatrix b) *
                ((UB : CMatrix b) *
                  Matrix.diagonal
                    (fun k : b =>
                      (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) *
                  star (UB : CMatrix b)) *
                (UB : CMatrix b) := by
                  rw [hρB]
        _ = (star (UB : CMatrix b) * (UB : CMatrix b)) *
              Matrix.diagonal
                (fun k : b =>
                  (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) *
              (star (UB : CMatrix b) * (UB : CMatrix b)) := by
                noncomm_ring
        _ = Matrix.diagonal
              (fun k : b =>
                (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) := by
              rw [Unitary.coe_star_mul_self]
              simp
    have hentry :
        (partialTraceA (a := a) (b := b) M) j j =
          (Matrix.diagonal
            (fun k : b => (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ))
              : CMatrix b) j j := by
      rw [hptM, hdiag]
    have hre := congrArg Complex.re hentry
    simpa [partialTraceA, Matrix.diagonal, M] using hre
  calc
    ∑ x : Prod a b, ∑ i : a,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ)
        =
      ∑ i : a, ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ i : a, (M (i, j) (i, j)).re := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
          rhoAB (i, j)
    _ = ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) := hdiag_sum

/-- KL summand for the product-marginal Nussbaum--Szkola model, with the
overlap factor cancelling in the `p ≠ 0` branch. -/
private theorem relativeEntropySummandReal_productMarginalNussbaumSzkolaModel
    (rhoAB : State (Prod a b)) (xy : (Prod a b) × (Prod a b)) :
    relativeEntropySummandReal
        (productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (productMarginalNussbaumSzkolaModel rhoAB).qDistribution xy =
      (((stateSpectralWeight rhoAB xy.1 : NNReal) : ℝ) *
        ((productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2 : NNReal) : ℝ)) *
        (Real.log ((stateSpectralWeight rhoAB xy.1 : NNReal) : ℝ) -
          Real.log ((productMarginalSpectralWeight rhoAB xy.2 : NNReal) : ℝ)) := by
  classical
  rcases xy with ⟨x, y⟩
  let M := productMarginalNussbaumSzkolaModel rhoAB
  by_cases hp : M.p (x, y) = 0
  · have hfactor :
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 0 := by
      have hpR : ((M.p (x, y) : NNReal) : ℝ) = 0 := by
        rw [hp]
        norm_num
      simpa [M, productMarginalNussbaumSzkolaModel, NNReal.coe_mul] using hpR
    simp [relativeEntropySummandReal, ClassicalBinaryModel.pDistribution,
      productMarginalNussbaumSzkolaModel, hfactor]
  · have hq : M.q (x, y) ≠ 0 :=
      productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB (x, y) (by
        simpa [M, ClassicalBinaryModel.pDistribution] using hp)
    have hp_prod :
        stateSpectralWeight rhoAB x *
            productMarginalNussbaumSzkolaOverlap rhoAB x y ≠ 0 := by
      simpa [M, productMarginalNussbaumSzkolaModel] using hp
    have hq_prod :
        productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y ≠ 0 := by
      simpa [M, productMarginalNussbaumSzkolaModel] using hq
    have hlam_ne : stateSpectralWeight rhoAB x ≠ 0 :=
      (mul_ne_zero_iff.mp hp_prod).1
    have ho_ne : productMarginalNussbaumSzkolaOverlap rhoAB x y ≠ 0 :=
      (mul_ne_zero_iff.mp hp_prod).2
    have hmu_ne : productMarginalSpectralWeight rhoAB y ≠ 0 :=
      (mul_ne_zero_iff.mp hq_prod).1
    have hlam_pos : 0 < ((stateSpectralWeight rhoAB x : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB x :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB x from zero_le)
          (Ne.symm hlam_ne)
      exact_mod_cast hnn
    have ho_pos : 0 < ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < productMarginalNussbaumSzkolaOverlap rhoAB x y :=
        lt_of_le_of_ne
          (show (0 : NNReal) ≤ productMarginalNussbaumSzkolaOverlap rhoAB x y from zero_le)
          (Ne.symm ho_ne)
      exact_mod_cast hnn
    have hmu_pos : 0 < ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < productMarginalSpectralWeight rhoAB y :=
        lt_of_le_of_ne
          (show (0 : NNReal) ≤ productMarginalSpectralWeight rhoAB y from zero_le)
          (Ne.symm hmu_ne)
      exact_mod_cast hnn
    have hlog :
        Real.log
            ((((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
                ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) /
              (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) *
                ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ))) =
          Real.log ((stateSpectralWeight rhoAB x : NNReal) : ℝ) -
            Real.log ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) := by
      have hoR_ne :
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) ≠ 0 :=
        ne_of_gt ho_pos
      rw [show
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) /
            (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) =
            ((stateSpectralWeight rhoAB x : NNReal) : ℝ) /
              ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) by
            field_simp [hoR_ne]]
      exact Real.log_div hlam_pos.ne' hmu_pos.ne'
    rw [relativeEntropySummandReal]
    simp only [ClassicalBinaryModel.pDistribution, ClassicalBinaryModel.qDistribution]
    rw [if_neg (by simpa [M] using hp)]
    simp [productMarginalNussbaumSzkolaModel, NNReal.coe_mul, hlog]

/-- The log of the product-marginal spectral weight splits after multiplying by
the joint diagonal weight.  If one marginal eigenvalue is zero, the support
bridge makes the joint diagonal weight zero as well. -/
theorem productMarginalNussbaumSzkolaModel_weighted_log_product
    (rhoAB : State (Prod a b)) (y : Prod a b) :
    (∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) *
        Real.log ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) =
      (∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) *
        (Real.log ((stateSpectralWeight rhoAB.marginalA y.1 : NNReal) : ℝ) +
          Real.log ((stateSpectralWeight rhoAB.marginalB y.2 : NNReal) : ℝ)) := by
  classical
  by_cases hmu : productMarginalSpectralWeight rhoAB y = 0
  · have hcoeff_zero :
        ∑ x : Prod a b,
          ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
            ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _hx
      have hq :
          (productMarginalNussbaumSzkolaModel rhoAB).q (x, y) = 0 := by
        simp [productMarginalNussbaumSzkolaModel, hmu]
      have hp :
          (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) = 0 := by
        by_contra hp_ne
        exact (productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB (x, y) hp_ne) hq
      have hfactor :
          ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
            ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 0 := by
        have hpR : (((productMarginalNussbaumSzkolaModel rhoAB).p (x, y) : NNReal) : ℝ) = 0 := by
          rw [hp]
          norm_num
        simpa [productMarginalNussbaumSzkolaModel, NNReal.coe_mul] using hpR
      exact hfactor
    simp [hcoeff_zero]
  · have hA_ne : stateSpectralWeight rhoAB.marginalA y.1 ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa [productMarginalSpectralWeight] using hmu)).1
    have hB_ne : stateSpectralWeight rhoAB.marginalB y.2 ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa [productMarginalSpectralWeight] using hmu)).2
    have hA_pos : 0 < ((stateSpectralWeight rhoAB.marginalA y.1 : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB.marginalA y.1 :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB.marginalA y.1 from zero_le)
          (Ne.symm hA_ne)
      exact_mod_cast hnn
    have hB_pos : 0 < ((stateSpectralWeight rhoAB.marginalB y.2 : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB.marginalB y.2 :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB.marginalB y.2 from zero_le)
          (Ne.symm hB_ne)
      exact_mod_cast hnn
    rw [productMarginalSpectralWeight, NNReal.coe_mul]
    rw [Real.log_mul hA_pos.ne' hB_pos.ne']

/-- Product-marginal Nussbaum--Szkola classical relative entropy is the
entropy-form mutual-information log numerator. -/
private theorem productMarginalNussbaumSzkolaModel_relativeEntropyReal_eq_log_sums
    (rhoAB : State (Prod a b)) :
    relativeEntropyReal
        (productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (productMarginalNussbaumSzkolaModel rhoAB).qDistribution =
      (∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          Real.log ((stateSpectralWeight rhoAB x : NNReal) : ℝ)) -
        ((∑ i : a,
          ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) *
            Real.log ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ)) +
          (∑ j : b,
            ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) *
              Real.log ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ))) := by
  classical
  let lam : Prod a b → ℝ := fun x =>
    ((stateSpectralWeight rhoAB x : NNReal) : ℝ)
  let ov : Prod a b → Prod a b → ℝ := fun x y =>
    ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)
  let mu : Prod a b → ℝ := fun y =>
    ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ)
  let muA : a → ℝ := fun i =>
    ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ)
  let muB : b → ℝ := fun j =>
    ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ)
  have hrow : ∀ x : Prod a b, ∑ y : Prod a b, ov x y = 1 := by
    intro x
    have h :
        ∑ y : Prod a b,
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 1 := by
      exact_mod_cast productMarginalNussbaumSzkolaOverlap_row_sum rhoAB x
    simpa [ov] using h
  have hfst : ∀ i : a, ∑ j : b, ∑ x : Prod a b, lam x * ov x (i, j) = muA i := by
    intro i
    rw [Finset.sum_comm]
    simpa [lam, ov, muA] using
      productMarginalNussbaumSzkolaOverlap_weighted_fst_sum rhoAB i
  have hsnd : ∀ j : b, ∑ i : a, ∑ x : Prod a b, lam x * ov x (i, j) = muB j := by
    intro j
    rw [Finset.sum_comm]
    simpa [lam, ov, muB] using
      productMarginalNussbaumSzkolaOverlap_weighted_snd_sum rhoAB j
  have hfirst :
      ∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (lam xy.1) =
        ∑ x : Prod a b, lam x * Real.log (lam x) := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : Prod a b, ∑ y : Prod a b,
          (lam x * ov x y) * Real.log (lam x)
          =
        ∑ x : Prod a b, ∑ y : Prod a b,
          ov x y * (lam x * Real.log (lam x)) := by
          simp [mul_assoc, mul_comm]
      _ = ∑ x : Prod a b,
          (∑ y : Prod a b, ov x y) * (lam x * Real.log (lam x)) := by
          simp [Finset.sum_mul]
      _ = ∑ x : Prod a b, lam x * Real.log (lam x) := by
          simp [hrow]
  have hsecond :
      ∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (mu xy.2) =
        (∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j)) := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : Prod a b, ∑ y : Prod a b,
          (lam x * ov x y) * Real.log (mu y)
          =
        ∑ y : Prod a b, (∑ x : Prod a b, lam x * ov x y) * Real.log (mu y) := by
          rw [Finset.sum_comm]
          simp [Finset.sum_mul]
      _ =
        ∑ y : Prod a b, (∑ x : Prod a b, lam x * ov x y) *
          (Real.log (muA y.1) + Real.log (muB y.2)) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          simpa [lam, ov, mu, muA, muB] using
            productMarginalNussbaumSzkolaModel_weighted_log_product rhoAB y
      _ =
        (∑ i : a, ∑ j : b,
          (∑ x : Prod a b, lam x * ov x (i, j)) * Real.log (muA i)) +
          (∑ i : a, ∑ j : b,
            (∑ x : Prod a b, lam x * ov x (i, j)) * Real.log (muB j)) := by
          rw [Fintype.sum_prod_type]
          simp [mul_add, Finset.sum_add_distrib]
      _ =
        (∑ i : a, (∑ j : b, ∑ x : Prod a b, lam x * ov x (i, j)) *
          Real.log (muA i)) +
          (∑ j : b, (∑ i : a, ∑ x : Prod a b, lam x * ov x (i, j)) *
            Real.log (muB j)) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [Finset.sum_mul]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simp [Finset.sum_mul]
      _ =
        (∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j)) := by
          simp [hfst, hsnd]
  calc
    relativeEntropyReal
        (productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (productMarginalNussbaumSzkolaModel rhoAB).qDistribution
        =
      ∑ xy : (Prod a b) × (Prod a b),
        (lam xy.1 * ov xy.1 xy.2) *
          (Real.log (lam xy.1) - Real.log (mu xy.2)) := by
        unfold relativeEntropyReal
        refine Finset.sum_congr rfl ?_
        intro xy _hxy
        simpa [lam, ov, mu] using
          relativeEntropySummandReal_productMarginalNussbaumSzkolaModel rhoAB xy
    _ =
      (∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (lam xy.1)) -
        (∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (mu xy.2)) := by
        simp [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ x : Prod a b, lam x * Real.log (lam x)) -
        ((∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j))) := by
        rw [hfirst, hsecond]

private theorem productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_term
    (p q r : NNReal) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
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

/-- The product-marginal classical Chernoff coefficient is the Petz
coefficient for the barred product-marginal pair. -/
theorem productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_eq
    (rhoAB : State (Prod a b)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (productMarginalNussbaumSzkolaModel rhoAB).petzChernoffCoefficient s =
      rhoAB.petzRenyiCoefficient
        (rhoAB.marginalA.prod rhoAB.marginalB) s := by
  classical
  let Urho : Matrix.unitaryGroup (Prod a b) ℂ :=
    rhoAB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let sigma : State (Prod a b) := rhoAB.marginalA.prod rhoAB.marginalB
  have hrho :
      CFC.rpow rhoAB.matrix s =
        (Urho : CMatrix (Prod a b)) *
          Matrix.diagonal
            (fun x : Prod a b =>
              (((((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s : ℝ) : ℂ))) *
          star (Urho : CMatrix (Prod a b)) := by
    simpa [Urho, stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal rhoAB.pos s
  have hw_nonneg :
      ∀ y : Prod a b, 0 ≤ ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) := by
    intro y
    positivity
  have hsigma_spec :
      sigma.matrix =
        (Uprod : CMatrix (Prod a b)) *
          Matrix.diagonal
            (fun y : Prod a b =>
              (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
          star (Uprod : CMatrix (Prod a b)) := by
    simpa [sigma, Uprod] using
      productMarginal_matrix_eq_productEigenbasis_diagonal rhoAB
  have hsigma :
      CFC.rpow sigma.matrix (1 - s) =
        (Uprod : CMatrix (Prod a b)) *
          Matrix.diagonal
            (fun y : Prod a b =>
              ((((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s) : ℝ) : ℂ)) *
          star (Uprod : CMatrix (Prod a b)) := by
    rw [hsigma_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal
      Uprod (fun y : Prod a b => ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ))
      hw_nonneg (1 - s)
  have htrace :
      (rhoAB.petzRenyiCoefficient sigma s : ℝ) =
        ∑ x : Prod a b, ∑ y : Prod a b,
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s) *
            ((((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s)) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) := by
    change ((CFC.rpow rhoAB.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re = _
    rw [hrho, hsigma]
    simpa [Urho, Uprod, productMarginalNussbaumSzkolaOverlap,
      productMarginalNussbaumSzkolaTransitionUnitary, Matrix.star_eq_conjTranspose,
      mul_assoc, mul_left_comm, mul_comm] using
      trace_mul_two_unitary_conj_diagonal_ofReal_re
        Urho Uprod
        (fun x : Prod a b => (((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s : ℝ))
        (fun y : Prod a b =>
          (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s) : ℝ))
  apply NNReal.eq
  calc
    ((productMarginalNussbaumSzkolaModel rhoAB).petzChernoffCoefficient s : ℝ) =
        ∑ xy : (Prod a b) × (Prod a b),
          (((stateSpectralWeight rhoAB xy.1) ^ s *
            (productMarginalSpectralWeight rhoAB xy.2) ^ (1 - s) *
              productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2 : NNReal) : ℝ) := by
          simp [ClassicalBinaryModel.petzChernoffCoefficient,
            productMarginalNussbaumSzkolaModel,
            productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_term _ _ _ hs0 hs1,
            mul_assoc]
    _ = ∑ x : Prod a b, ∑ y : Prod a b,
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s) *
            ((((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s)) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) := by
          rw [Fintype.sum_prod_type]
          simp [NNReal.coe_rpow, mul_assoc]
    _ = (rhoAB.petzRenyiCoefficient sigma s : ℝ) := htrace.symm

end BinaryHypothesisTest

namespace State

/-- Entropy as the spectral-weight sum used by the Nussbaum--Szkola models. -/
theorem vonNeumann_eq_neg_sum_stateSpectralWeight (ρ : State a) :
    ρ.vonNeumann =
      -∑ x : a, xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
  unfold State.vonNeumann BinaryHypothesisTest.stateSpectralWeight
  congr 1

/-- Change-of-base bridge for the entropy summand used in spectral sums. -/
private lemma xlog2_mul_log_two {x : ℝ} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [xlog2, if_neg (ne_of_gt hxp), log2]
    field_simp

/-- Spectral log sums are the negative von Neumann entropy after dividing by
`log 2`. -/
theorem spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann
    (ρ : State a) :
    (∑ x : a,
        ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
          Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) /
      Real.log 2 =
        -ρ.vonNeumann := by
  classical
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hmul :
      (∑ x : a,
          xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) *
        Real.log 2 =
      ∑ x : a,
        ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
          Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    exact xlog2_mul_log_two (NNReal.coe_nonneg _)
  have hdiv :
      (∑ x : a,
          ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
            Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) /
        Real.log 2 =
      ∑ x : a,
        xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
    calc
      ((∑ x : a,
          ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
            Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) /
          Real.log 2) =
        ((∑ x : a,
          xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) *
          Real.log 2) / Real.log 2 := by
          rw [hmul]
      _ = ∑ x : a,
          xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
          field_simp [hlog_ne]
  rw [hdiv, vonNeumann_eq_neg_sum_stateSpectralWeight]
  ring

/-- The product-marginal Nussbaum--Szkola endpoint is the entropy-form mutual
information, not the full-rank relative-entropy API. -/
theorem productMarginalNussbaumSzkolaModel_relativeEntropyReal_div_log_two_eq_mutualInformation
    (rhoAB : State (Prod a b)) :
    BinaryHypothesisTest.relativeEntropyReal
        (BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).qDistribution /
      Real.log 2 =
        mutualInformation rhoAB := by
  classical
  let sAB : ℝ := ∑ x : Prod a b,
    ((BinaryHypothesisTest.stateSpectralWeight rhoAB x : NNReal) : ℝ) *
      Real.log ((BinaryHypothesisTest.stateSpectralWeight rhoAB x : NNReal) : ℝ)
  let sA : ℝ := ∑ i : a,
    ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) *
      Real.log ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ)
  let sB : ℝ := ∑ j : b,
    ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) *
      Real.log ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ)
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hAB : sAB / Real.log 2 = -rhoAB.vonNeumann := by
    simpa [sAB] using
      spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann rhoAB
  have hA : sA / Real.log 2 = -rhoAB.marginalA.vonNeumann := by
    simpa [sA] using
      spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann rhoAB.marginalA
  have hB : sB / Real.log 2 = -rhoAB.marginalB.vonNeumann := by
    simpa [sB] using
      spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann rhoAB.marginalB
  rw [BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_relativeEntropyReal_eq_log_sums]
  change (sAB - (sA + sB)) / Real.log 2 = mutualInformation rhoAB
  calc
    (sAB - (sA + sB)) / Real.log 2 =
        sAB / Real.log 2 - (sA / Real.log 2 + sB / Real.log 2) := by
          field_simp [hlog_ne]
    _ = mutualInformation rhoAB := by
          rw [hAB, hA, hB]
          unfold mutualInformation
          ring

/-- In the PSD source branch, barred Petz--Renyi mutual information is the
base-2 Chernoff log partition of the product-marginal Nussbaum--Szkola model. -/
theorem barPetzRenyiMutualInformationPSD_eq_productMarginal_chernoffLog2
    (rhoAB : State (Prod a b)) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    rhoAB.barPetzRenyiMutualInformationPSD alpha halpha0 (ne_of_lt halpha1) =
      (1 / (alpha - 1)) *
        log2 ((BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).chernoffPartition alpha) := by
  classical
  let sigma : State (Prod a b) := rhoAB.marginalA.prod rhoAB.marginalB
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB
  have htrace :
      ((CFC.rpow rhoAB.matrix alpha *
        CFC.rpow sigma.matrix (1 - alpha)).trace).re =
        (rhoAB.petzRenyiCoefficient sigma alpha : ℝ) := by
    have h := State.petzRenyiCoefficient_trace_eq rhoAB sigma alpha
    have hre := congrArg Complex.re h
    simpa using hre.symm
  have hpart :
      M.chernoffPartition alpha =
        (rhoAB.petzRenyiCoefficient sigma alpha : ℝ) := by
    have hnn :
        M.chernoffPartitionNNReal alpha = M.petzChernoffCoefficient alpha :=
      BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
        (M := M) halpha0 halpha1
    have hns :
        M.petzChernoffCoefficient alpha =
          rhoAB.petzRenyiCoefficient sigma alpha := by
      simpa [sigma, M] using
        BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_eq
          rhoAB (le_of_lt halpha0) (le_of_lt halpha1)
    calc
      M.chernoffPartition alpha =
          (M.chernoffPartitionNNReal alpha : ℝ) := by
            exact (BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_coe
              M alpha).symm
      _ = (M.petzChernoffCoefficient alpha : ℝ) := by rw [hnn]
      _ = (rhoAB.petzRenyiCoefficient sigma alpha : ℝ) := by rw [hns]
  have hpart' :
      (BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).chernoffPartition alpha =
        (rhoAB.petzRenyiCoefficient (rhoAB.marginalA.prod rhoAB.marginalB) alpha : ℝ) := by
    simpa [M, sigma] using hpart
  unfold State.barPetzRenyiMutualInformationPSD State.petzRenyiPSD
  change
    (1 / (alpha - 1)) *
        log2 ((CFC.rpow rhoAB.matrix alpha *
          CFC.rpow (rhoAB.marginalA.prod rhoAB.marginalB).matrix (1 - alpha)).trace).re =
      (1 / (alpha - 1)) *
        log2 ((BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).chernoffPartition alpha)
  rw [htrace, ← hpart']

/-- State-level barred PSD Petz--Renyi mutual information converges to the
entropy-form mutual information as `alpha -> 1^-`. -/
theorem barPetzRenyiMutualInformationPSD_tendsto_mutualInformation_left
    (rhoAB : State (Prod a b)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        rhoAB.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds (mutualInformation rhoAB)) := by
  classical
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB
  have hendpoint :
      BinaryHypothesisTest.relativeEntropyReal M.pDistribution M.qDistribution /
        Real.log 2 = mutualInformation rhoAB := by
    simpa [M] using
      productMarginalNussbaumSzkolaModel_relativeEntropyReal_div_log_two_eq_mutualInformation rhoAB
  have hclassical :
      Tendsto
        (fun alpha : PetzRenyiAlpha =>
          (1 / (alpha.1 - 1)) * log2 (M.chernoffPartition alpha.1))
        PetzRenyiAlpha.leftToOne
        (nhds (mutualInformation rhoAB)) := by
    simpa [hendpoint] using
      BinaryHypothesisTest.ClassicalBinaryModel.petzChernoffLog2_tendsto_relativeEntropyReal_subtype_left
        (M := M) hpq
  refine hclassical.congr' ?_
  filter_upwards with alpha
  exact (barPetzRenyiMutualInformationPSD_eq_productMarginal_chernoffLog2
    (rhoAB := rhoAB) (alpha := alpha.1) alpha.2.1 alpha.2.2).symm

/-- Source-range comparison needed for the channel-level `sSup` upper bound:
barred PSD Petz--Renyi mutual information is bounded by entropy-form mutual
information. -/
theorem barPetzRenyiMutualInformationPSD_le_mutualInformation
    (rhoAB : State (Prod a b)) (alpha : PetzRenyiAlpha) :
    rhoAB.barPetzRenyiMutualInformationPSD
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      mutualInformation rhoAB := by
  classical
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB
  have hendpoint :
      BinaryHypothesisTest.relativeEntropyReal M.pDistribution M.qDistribution /
        Real.log 2 = mutualInformation rhoAB := by
    simpa [M] using
      productMarginalNussbaumSzkolaModel_relativeEntropyReal_div_log_two_eq_mutualInformation rhoAB
  calc
    rhoAB.barPetzRenyiMutualInformationPSD
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) =
      (1 / (alpha.1 - 1)) * log2 (M.chernoffPartition alpha.1) := by
        simpa [M] using
          barPetzRenyiMutualInformationPSD_eq_productMarginal_chernoffLog2
            (rhoAB := rhoAB) (alpha := alpha.1) alpha.2.1 alpha.2.2
    _ ≤ BinaryHypothesisTest.relativeEntropyReal M.pDistribution M.qDistribution /
        Real.log 2 :=
        BinaryHypothesisTest.ClassicalBinaryModel.petzChernoffLog2_le_relativeEntropyReal
          (M := M) hpq alpha.2.1 alpha.2.2
    _ = mutualInformation rhoAB := hendpoint

/-- State-level barred PSD Petz--Renyi mutual information converges to the
Nussbaum--Szkola classical relative entropy for the product-marginal pair. -/
theorem barPetzRenyiMutualInformationPSD_tendsto_nussbaumSzkola_relativeEntropyReal_left
    (rhoAB : State (Prod a b)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        rhoAB.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds
        (BinaryHypothesisTest.relativeEntropyReal
          (BinaryHypothesisTest.nussbaumSzkolaModel rhoAB
            (rhoAB.marginalA.prod rhoAB.marginalB)).pDistribution
          (BinaryHypothesisTest.nussbaumSzkolaModel rhoAB
            (rhoAB.marginalA.prod rhoAB.marginalB)).qDistribution /
            Real.log 2)) := by
  simpa [State.barPetzRenyiMutualInformationPSD] using
    State.petzRenyiPSD_tendsto_nussbaumSzkola_relativeEntropyReal_left
      rhoAB (rhoAB.marginalA.prod rhoAB.marginalB)
      rhoAB.matrix_supports_prod_marginals

end State

namespace Channel

variable (N : Channel a b)

/-- The hypothesis-testing and entanglement-assisted output-state APIs use the
same channel-output state. -/
theorem hypothesisTestingOutputState_eq_entanglementAssistedOutputState
    (psi : PureVector (Prod a a)) :
    N.hypothesisTestingOutputState psi = N.entanglementAssistedOutputState psi := by
  rfl

/-- Fixed-input channel bridge for the PSD barred Petz--Renyi endpoint, with
the endpoint still expressed as the Nussbaum--Szkola classical relative
entropy of the output/product-marginal pair. -/
theorem inputBarPetzRenyiMutualInformationPSD_tendsto_nussbaumSzkola_relativeEntropyReal_left
    (psi : PureVector (Prod a a)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.inputBarPetzRenyiMutualInformationPSD
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds
        (BinaryHypothesisTest.relativeEntropyReal
          (BinaryHypothesisTest.nussbaumSzkolaModel
            (N.hypothesisTestingOutputState psi)
            ((N.hypothesisTestingOutputState psi).marginalA.prod
              (N.hypothesisTestingOutputState psi).marginalB)).pDistribution
          (BinaryHypothesisTest.nussbaumSzkolaModel
            (N.hypothesisTestingOutputState psi)
            ((N.hypothesisTestingOutputState psi).marginalA.prod
              (N.hypothesisTestingOutputState psi).marginalB)).qDistribution /
            Real.log 2)) := by
  simpa [Channel.inputBarPetzRenyiMutualInformationPSD] using
    State.barPetzRenyiMutualInformationPSD_tendsto_nussbaumSzkola_relativeEntropyReal_left
      (N.hypothesisTestingOutputState psi)

/-- Fixed-input channel bridge for the PSD barred Petz--Renyi endpoint, with
the endpoint expressed as entropy-form entanglement-assisted mutual
information. -/
theorem inputBarPetzRenyiMutualInformationPSD_tendsto_entanglementAssistedMutualInformation_left
    (psi : PureVector (Prod a a)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.inputBarPetzRenyiMutualInformationPSD
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds (N.entanglementAssistedMutualInformation psi)) := by
  simpa [Channel.inputBarPetzRenyiMutualInformationPSD,
    Channel.entanglementAssistedMutualInformation,
    N.hypothesisTestingOutputState_eq_entanglementAssistedOutputState psi] using
    State.barPetzRenyiMutualInformationPSD_tendsto_mutualInformation_left
      (N.hypothesisTestingOutputState psi)

/-- Fixed-input source-range comparison against the channel's ordinary
entanglement-assisted information. -/
theorem inputBarPetzRenyiMutualInformationPSD_le_entanglementAssistedInformation
    [Nonempty a] (psi : PureVector (Prod a a)) (alpha : PetzRenyiAlpha) :
    N.inputBarPetzRenyiMutualInformationPSD
        psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      N.entanglementAssistedInformation := by
  calc
    N.inputBarPetzRenyiMutualInformationPSD
        psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) =
      (N.hypothesisTestingOutputState psi).barPetzRenyiMutualInformationPSD
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := rfl
    _ ≤ mutualInformation (N.hypothesisTestingOutputState psi) :=
        State.barPetzRenyiMutualInformationPSD_le_mutualInformation
          (N.hypothesisTestingOutputState psi) alpha
    _ = N.entanglementAssistedMutualInformation psi := by
        simp [Channel.entanglementAssistedMutualInformation,
          N.hypothesisTestingOutputState_eq_entanglementAssistedOutputState psi]
    _ ≤ N.entanglementAssistedInformation :=
        N.entanglementAssistedMutualInformation_le_information psi

/-- The PSD barred channel Petz value set is bounded above by `I(N)` in the
source range. -/
theorem barPetzRenyiMutualInformationPSDValueSet_bddAbove
    [Nonempty a] (alpha : PetzRenyiAlpha) :
    BddAbove
      (N.barPetzRenyiMutualInformationPSDValueSet
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) := by
  refine ⟨N.entanglementAssistedInformation, ?_⟩
  intro value hvalue
  rcases hvalue with ⟨psi, rfl⟩
  exact N.inputBarPetzRenyiMutualInformationPSD_le_entanglementAssistedInformation
    psi alpha

/-- Channel-level source-range upper bound for PSD barred Petz--Renyi mutual
information. -/
theorem barPetzRenyiMutualInformationPSD_le_entanglementAssistedInformation
    [Nonempty a] (alpha : PetzRenyiAlpha) :
    N.barPetzRenyiMutualInformationPSD
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      N.entanglementAssistedInformation := by
  classical
  rw [N.barPetzRenyiMutualInformationPSD_eq_sSup
    alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)]
  have hne :
      (N.barPetzRenyiMutualInformationPSDValueSet
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)).Nonempty := by
    let psi0 : PureVector (Prod a a) := PureVector.basisPureVector
    refine ⟨N.inputBarPetzRenyiMutualInformationPSD
      psi0 alpha.1 alpha.2.1 (ne_of_lt alpha.2.2), ?_⟩
    exact ⟨psi0, rfl⟩
  refine csSup_le hne ?_
  intro value hvalue
  rcases hvalue with ⟨psi, rfl⟩
  exact N.inputBarPetzRenyiMutualInformationPSD_le_entanglementAssistedInformation
    psi alpha

/-- Source-shaped alpha-to-one theorem for the PSD-domain barred
Petz--Renyi channel mutual information:
`lim_{alpha -> 1^-} \bar I_alpha^{Petz,PSD}(N) = I(N)`. -/
theorem barPetzRenyiMutualInformationPSD_tendsto_entanglementAssistedInformation_left
    [Nonempty a] :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds N.entanglementAssistedInformation) := by
  classical
  obtain ⟨psi, hpsi⟩ := N.exists_entanglementAssistedInformation_maximizer
  have hfixed :
      Tendsto
        (fun alpha : PetzRenyiAlpha =>
          N.inputBarPetzRenyiMutualInformationPSD
            psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
        PetzRenyiAlpha.leftToOne
        (nhds N.entanglementAssistedInformation) := by
    simpa [hpsi] using
      N.inputBarPetzRenyiMutualInformationPSD_tendsto_entanglementAssistedMutualInformation_left
        psi
  have hconst :
      Tendsto
        (fun _alpha : PetzRenyiAlpha => N.entanglementAssistedInformation)
        PetzRenyiAlpha.leftToOne
        (nhds N.entanglementAssistedInformation) := tendsto_const_nhds
  have hlower :
      (fun alpha : PetzRenyiAlpha =>
        N.inputBarPetzRenyiMutualInformationPSD
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) ≤
      (fun alpha : PetzRenyiAlpha =>
        N.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) := by
    intro alpha
    change
      N.inputBarPetzRenyiMutualInformationPSD
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
        N.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
    rw [N.barPetzRenyiMutualInformationPSD_eq_sSup
      alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)]
    exact le_csSup
      (N.barPetzRenyiMutualInformationPSDValueSet_bddAbove alpha)
      ⟨psi, rfl⟩
  have hupper :
      (fun alpha : PetzRenyiAlpha =>
        N.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) ≤
      (fun _alpha : PetzRenyiAlpha => N.entanglementAssistedInformation) := by
    intro alpha
    exact N.barPetzRenyiMutualInformationPSD_le_entanglementAssistedInformation alpha
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hfixed hconst hlower hupper

end Channel

end

end QIT
