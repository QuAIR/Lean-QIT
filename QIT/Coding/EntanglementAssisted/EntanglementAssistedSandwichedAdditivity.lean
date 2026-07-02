/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwiched
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedPetzAdditivity

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

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u1 v1 u2 v2

noncomputable section

namespace State

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

/-- Fixed product side-information candidates are additive on the full-rank
branch.  This is only the restricted-candidate ingredient in
`EA_capacity.tex:1177-1191`; the optimized equality for
`sandwichedRenyiMutualInformationE` still needs the alternate-expression route
from `lem-sand_rel_mut_inf_alt`. -/
theorem sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_posDef
    (xi : State (Prod a1 b1)) (omega : State (Prod a2 b2))
    (sigma1 : State b1) (sigma2 : State b2)
    (hxi : xi.matrix.PosDef) (homega : omega.matrix.PosDef)
    (hxiA : xi.marginalA.matrix.PosDef) (homegaA : omega.marginalA.matrix.PosDef)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
        (sigma1.prod sigma2) alphaR =
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR +
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR := by
  let ref1 : State (Prod a1 b1) := xi.marginalA.prod sigma1
  let ref2 : State (Prod a2 b2) := omega.marginalA.prod sigma2
  have hprodState : (xi.bipartiteProduct omega).matrix.PosDef :=
    bipartiteProduct_posDef hxi homega
  have hprodMarginal :
      (xi.bipartiteProduct omega).marginalA.matrix.PosDef := by
    rw [bipartiteProduct_marginalA]
    exact State.prod_posDef hxiA homegaA
  have hsigmaProd : (sigma1.prod sigma2).matrix.PosDef :=
    State.prod_posDef hsigma1 hsigma2
  have href1 : ref1.matrix.PosDef := State.prod_posDef hxiA hsigma1
  have href2 : ref2.matrix.PosDef := State.prod_posDef homegaA hsigma2
  have hrefProd : (ref1.prod ref2).matrix.PosDef := State.prod_posDef href1 href2
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB := xi.bipartiteProduct omega) (sigmaB := sigma1.prod sigma2)
    hprodState hprodMarginal hsigmaProd halpha]
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB := xi) (sigmaB := sigma1) hxi hxiA hsigma1 halpha]
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB := omega) (sigmaB := sigma2) homega homegaA hsigma2 halpha]
  have hleft :
      sandwichedRenyiReference (xi.bipartiteProduct omega)
          ((xi.bipartiteProduct omega).marginalA.prod (sigma1.prod sigma2)).matrix
          hprodState (State.prod_posDef hprodMarginal hsigmaProd)
          alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha) =
        sandwichedRenyiReference (xi.prod omega) (ref1.prod ref2).matrix
          (State.prod_posDef hxi homega) hrefProd
          alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha) := by
    unfold sandwichedRenyiReference
    have href :=
      congrArg State.matrix (bipartiteProduct_candidateReference xi omega sigma1 sigma2)
    rw [href]
    have hre :=
      sandwichedRenyiReference_reindex (rho := xi.prod omega)
        (sigma := (ref1.prod ref2).matrix)
        (e := bipartiteProductEquiv (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2))
        (State.prod_posDef hxi homega) hrefProd
        alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)
    unfold sandwichedRenyiReference at hre
    simpa [bipartiteProduct, State.reindex_matrix, ref1, ref2] using hre
  rw [hleft]
  rw [sandwichedRenyiReference_state (xi.prod omega) (ref1.prod ref2)
    (State.prod_posDef hxi homega) hrefProd
    alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)]
  rw [State.sandwichedRenyi_prod xi ref1 omega ref2
    hxi href1 homega href2 alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)]
  rw [← sandwichedRenyiReference_state xi ref1 hxi href1
    alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)]
  rw [← sandwichedRenyiReference_state omega ref2 homega href2
    alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)]
  simp [ref1, ref2]

end State

end

end QIT
