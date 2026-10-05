/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix.MarginalOrder
public import QIT.Util.Matrix.PosSqrt
public import QIT.Util.Wires

/-!
# Filtered marginal bounds

The marginal bound for a positive filter and an arbitrary positive input
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374].
The input carrier is `(B × R) × E`; reassociation followed by tracing out `B`
leaves `R × E`. Identity factors and register permutations are explicit.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

universe u v w

/-- A filter with a scalar upper bound on its receiver Gram marginal bounds
the remaining marginal of every rank-one input. This rectangular-Gram form
of the argument avoids inverses on spectral supports
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem partialTraceA_reassoc_conjugation_rankOne_le
    {b : Type u} {r : Type v} {e : Type w}
    [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e]
    (K : CMatrix (b × r)) (v : (b × r) × e → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hK : partialTraceB (K * Kᴴ) ≤ (c : ℂ) • (1 : CMatrix b)) :
    partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
      (Matrix.kronecker K (1 : CMatrix e) * rankOneMatrix v *
        Matrix.kronecker Kᴴ (1 : CMatrix e))) ≤
      (c : ℂ) • Matrix.kronecker (1 : CMatrix r) (partialTraceA (rankOneMatrix v)) := by
  let A : Matrix e (b × r) ℂ := fun i j => v (j, i)
  let W : Matrix (r × (b × r)) b ℂ := fun i j => K (j, i.1) i.2
  let T := Matrix.kronecker (1 : CMatrix r) A
  have hW : Wᴴ * W = (partialTraceB (K * Kᴴ))ᵀ := by
    ext i j
    change (∑ k : r × (b × r), star (K (i, k.1) k.2) * K (j, k.1) k.2) =
      ∑ k : r, ∑ l : b × r, K (j, k) l * star (K (i, k) l)
    simp only [Fintype.sum_prod_type, mul_comm]
  have hWt : Wᴴ * W ≤ (c : ℂ) • (1 : CMatrix b) := by
    rw [hW, Matrix.le_iff]
    simpa only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one] using
      (Matrix.le_iff.mp hK).transpose
  have hWW := (conjTranspose_mul_le_smul_one_iff W c hc).mp hWt
  have hbound : T * (W * Wᴴ) * Tᴴ ≤ T * ((c : ℂ) • (1 : CMatrix (r × (b × r)))) * Tᴴ := by
    rw [Matrix.le_iff, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact (Matrix.le_iff.mp hWW).mul_mul_conjTranspose_same T
  have hA : A * Aᴴ = partialTraceA (rankOneMatrix v) := by
    ext i j
    rfl
  have hright : T * ((c : ℂ) • (1 : CMatrix (r × (b × r)))) * Tᴴ =
      (c : ℂ) • Matrix.kronecker (1 : CMatrix r) (partialTraceA (rankOneMatrix v)) := by
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, T,
      Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, hA]
  have hTW (i : r × e) (j : b) :
      (T * W) i j = ∑ k, K (j, i.1) k * v (k, i.2) := by
    change (∑ k : r × (b × r),
      ((1 : CMatrix r) i.1 k.1 * v (k.2, i.2)) * K (j, k.1) k.2) = _
    simp [Fintype.sum_prod_type, Matrix.one_apply, mul_comm]
  have hleft : partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
      (Matrix.kronecker K (1 : CMatrix e) * rankOneMatrix v *
        Matrix.kronecker Kᴴ (1 : CMatrix e))) = T * (W * Wᴴ) * Tᴴ := by
    have hL : Matrix.kronecker Kᴴ (1 : CMatrix e) =
        (Matrix.kronecker K (1 : CMatrix e))ᴴ := by
      simp [Matrix.kronecker, Matrix.conjTranspose_kronecker]
    rw [hL, ← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    have hassoc : T * (W * Wᴴ) * Tᴴ = (T * W) * (T * W)ᴴ := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hassoc]
    ext i j
    simp only [partialTraceA, WireFam.matReindex_apply, Equiv.prodAssoc_symm_apply,
      rankOneMatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hTW]
    apply Finset.sum_congr rfl
    intro k _
    congr 1 <;>
      simp [Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Matrix.one_apply]
  rw [hleft, ← hright]
  exact hbound

/-- A receiver Gram marginal bound controls a filtered marginal for every
positive input, without normalization
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem partialTraceA_reassoc_conjugation_le
    {b : Type u} {r : Type v} {e : Type w}
    [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e]
    (K : CMatrix (b × r)) (X : CMatrix ((b × r) × e))
    (hX : X.PosSemidef) (c : ℝ) (hc : 0 ≤ c)
    (hK : partialTraceB (K * Kᴴ) ≤ (c : ℂ) • (1 : CMatrix b)) :
    partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
      (Matrix.kronecker K (1 : CMatrix e) * X *
        Matrix.kronecker Kᴴ (1 : CMatrix e))) ≤
      (c : ℂ) • Matrix.kronecker (1 : CMatrix r) (partialTraceA X) := by
  let v (j : (b × r) × e) : (b × r) × e → ℂ := fun i => psdSqrt X i j
  have hsum : X = ∑ j, rankOneMatrix (v j) := by
    have hs : psdSqrt X * (psdSqrt X)ᴴ = X := by
      rw [(psdSqrt_isHermitian X).eq, psdSqrt_mul_self_of_posSemidef hX]
    rw [← hs]
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, rankOneMatrix_apply, v]
  rw [hsum]
  have hleft : partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
      (Matrix.kronecker K (1 : CMatrix e) * (∑ j, rankOneMatrix (v j)) *
        Matrix.kronecker Kᴴ (1 : CMatrix e))) =
      ∑ j, partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
        (Matrix.kronecker K (1 : CMatrix e) * rankOneMatrix (v j) *
          Matrix.kronecker Kᴴ (1 : CMatrix e))) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    ext i j
    simp only [partialTraceA, WireFam.matReindex_apply, Matrix.sum_apply]
    exact Finset.sum_comm
  have hright : (c : ℂ) • Matrix.kronecker (1 : CMatrix r)
      (partialTraceA (∑ j, rankOneMatrix (v j))) =
      ∑ j, (c : ℂ) • Matrix.kronecker (1 : CMatrix r)
        (partialTraceA (rankOneMatrix (v j))) := by
    ext i j
    rcases i with ⟨i, k⟩
    rcases j with ⟨j, l⟩
    simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kronecker_apply, partialTraceA,
      Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hleft, hright]
  exact Finset.sum_le_sum fun j _ =>
    partialTraceA_reassoc_conjugation_rankOne_le K (v j) c hc hK

/-- The filtered marginal bound with any explicit scalar bound on `Tr_R Q`.
This form lets a downstream test normalization supply its constant directly
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem partialTraceA_reassoc_filtered_le_of_marginal_le
    {b : Type u} {r : Type v} {e : Type w}
    [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e]
    (Q : CMatrix (b × r)) (ρ : CMatrix ((b × r) × e))
    (hQ : Q.PosSemidef) (hρ : ρ.PosSemidef) (c : ℝ) (hc : 0 ≤ c)
    (hmarginal : partialTraceB Q ≤ (c : ℂ) • (1 : CMatrix b)) :
    partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
      (Matrix.kronecker Q (1 : CMatrix e) * ρ * Matrix.kronecker Q (1 : CMatrix e))) ≤
      (c : ℂ) • Matrix.kronecker (1 : CMatrix r)
        (partialTraceA (Matrix.kronecker (psdSqrt Q) (1 : CMatrix e) * ρ *
          Matrix.kronecker (psdSqrt Q) (1 : CMatrix e))) := by
  let S := Matrix.kronecker (psdSqrt Q) (1 : CMatrix e)
  have hS : Sᴴ = S := by
    simp [S, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      (psdSqrt_isHermitian Q).eq]
  have hSS : S * S = Matrix.kronecker Q (1 : CMatrix e) := by
    simp only [S, Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      psdSqrt_mul_self_of_posSemidef hQ]
  have hK : partialTraceB (psdSqrt Q * (psdSqrt Q)ᴴ) ≤
      (c : ℂ) • (1 : CMatrix b) := by
    rwa [(psdSqrt_isHermitian Q).eq, psdSqrt_mul_self_of_posSemidef hQ]
  have hX : (S * ρ * S).PosSemidef := by
    simpa only [hS] using hρ.mul_mul_conjTranspose_same S
  have h := partialTraceA_reassoc_conjugation_le (psdSqrt Q) (S * ρ * S) hX c hc hK
  rw [(psdSqrt_isHermitian Q).eq] at h
  change partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
    (S * (S * ρ * S) * S)) ≤ _ at h
  have heq : S * (S * ρ * S) * S = (S * S) * ρ * (S * S) := by
    simp only [Matrix.mul_assoc]
  simpa only [heq, hSS] using h

/-- Lemma 1(ii): the filtered marginal is bounded by the operator norm of
`Tr_R Q` times the square-root-filtered environment marginal. Neither input
is normalized, and no spectral identity is assumed. The carrier `R × E`
is the explicit swap of the source's `E × R`
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem partialTraceA_reassoc_filtered_le
    {b : Type u} {r : Type v} {e : Type w}
    [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e]
    (Q : CMatrix (b × r)) (ρ : CMatrix ((b × r) × e))
    (hQ : Q.PosSemidef) (hρ : ρ.PosSemidef) :
    partialTraceA (WireFam.matReindex (Equiv.prodAssoc b r e)
      (Matrix.kronecker Q (1 : CMatrix e) * ρ * Matrix.kronecker Q (1 : CMatrix e))) ≤
      (‖partialTraceB Q‖ : ℂ) • Matrix.kronecker (1 : CMatrix r)
        (partialTraceA (Matrix.kronecker (psdSqrt Q) (1 : CMatrix e) * ρ *
          Matrix.kronecker (psdSqrt Q) (1 : CMatrix e))) :=
  partialTraceA_reassoc_filtered_le_of_marginal_le Q ρ hQ hρ _ (norm_nonneg _)
    (cMatrix_le_norm_smul_one _ (partialTraceB_posSemidef hQ))

end

end QIT
