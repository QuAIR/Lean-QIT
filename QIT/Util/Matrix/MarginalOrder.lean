/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Pure
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matrix marginal order

Partial-trace contraction, convexity of rank-one kernels, and the scalar-order
bridge between complementary pure marginals
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374].
All matrices and vectors may be unnormalized. Matrix norms in this module are
the L2 operator norm.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

universe u v w

/-- A rectangular contraction on the discarded system cannot increase the
remaining marginal in Loewner order
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem partialTraceA_contraction_le
    {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (S : CMatrix (a × b)) (K : Matrix c a ℂ)
    (hS : S.PosSemidef) (hK : Kᴴ * K ≤ 1) :
    partialTraceA (Matrix.kronecker K (1 : CMatrix b) * S *
      Matrix.kronecker Kᴴ (1 : CMatrix b)) ≤ partialTraceA S := by
  let L := Matrix.kronecker K (1 : CMatrix b)
  have hL : Lᴴ = Matrix.kronecker Kᴴ (1 : CMatrix b) := by
    simp [L, Matrix.kronecker, Matrix.conjTranspose_kronecker]
  have hF : (L * S * Lᴴ).PosSemidef := hS.mul_mul_conjTranspose_same L
  rw [← hL, Matrix.le_iff]
  apply (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg
    ((partialTraceA_posSemidef hS).isHermitian.sub
      (partialTraceA_posSemidef hF).isHermitian)).2
  intro Z hZ
  have hpair : ((partialTraceA (L * S * Lᴴ)) * Z).trace =
      (S * Matrix.kronecker (Kᴴ * K) Z).trace := by
    rw [partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right,
      Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm L, Matrix.mul_assoc]
    congr 1
    simp only [L, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one]
  have htrace : (((partialTraceA S - partialTraceA (L * S * Lᴴ)) * Z).trace) =
      (S * Matrix.kronecker (1 - Kᴴ * K) Z).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub, hpair,
      partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right]
    have hd : Matrix.kronecker (1 - Kᴴ * K) Z =
        Matrix.kronecker (1 : CMatrix a) Z - Matrix.kronecker (Kᴴ * K) Z := by
      ext i j
      exact sub_mul _ _ _
    rw [hd, Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace]
  exact cMatrix_trace_mul_posSemidef_re_nonneg hS ((Matrix.le_iff.mp hK).kronecker hZ)

/-- Taking the rank-one kernel is convex in an arbitrary complex amplitude
vector; the amplitudes need not be unit vectors
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem rankOneMatrix_convex_sum_le
    {ι : Type u} {a : Type v} [Fintype ι] [Fintype a]
    (p : ι → ℝ) (v : ι → a → ℂ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    rankOneMatrix (∑ j, (p j : ℂ) • v j) ≤
      ∑ j, (p j : ℂ) • rankOneMatrix (v j) := by
  classical
  let μ : a → ℂ := ∑ j, (p j : ℂ) • v j
  have hμ (x : a) : ∑ j, (p j : ℂ) * v j x = μ x := by
    simp [μ]
  have hpc : ∑ j, (p j : ℂ) = 1 := by exact_mod_cast hs
  have hvariance : (∑ j, (p j : ℂ) • rankOneMatrix (v j - μ)) =
      (∑ j, (p j : ℂ) • rankOneMatrix (v j)) - rankOneMatrix μ := by
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
      rankOneMatrix_apply, Pi.sub_apply, smul_eq_mul]
    calc
      _ = (∑ j, (p j : ℂ) * (v j x * star (v j y))) -
          (∑ j, (p j : ℂ) * v j x) * star (μ y) -
          μ x * star (∑ j, (p j : ℂ) * v j y) +
          (∑ j, (p j : ℂ)) * (μ x * star (μ y)) := by
        simp only [Finset.sum_mul, Finset.mul_sum, star_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_sub, star_mul, Complex.star_def, Complex.conj_ofReal]
        ring
      _ = _ := by rw [hμ x, hμ y, hpc]; ring
  rw [Matrix.le_iff, ← hvariance]
  exact Matrix.posSemidef_sum Finset.univ fun j _ =>
    (rankOneMatrix_pos (v j - μ)).smul (by exact_mod_cast hp j)

/-- A PSD matrix has operator norm at most a nonnegative scalar exactly when
it is bounded by that scalar times the identity. -/
theorem cMatrix_norm_le_iff_le_smul_one
    {a : Type u} [Fintype a] [DecidableEq a]
    (A : CMatrix a) (hA : A.PosSemidef) (c : ℝ) (hc : 0 ≤ c) :
    ‖A‖ ≤ c ↔ A ≤ (c : ℂ) • (1 : CMatrix a) := by
  let : CStarAlgebra (CMatrix a) := {}
  have hs : algebraMap ℝ (CMatrix a) c = (c : ℂ) • (1 : CMatrix a) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]
  simpa only [hs] using CStarAlgebra.norm_le_iff_le_algebraMap A hc hA.nonneg

/-- A PSD matrix is bounded by its operator norm times the identity. -/
theorem cMatrix_le_norm_smul_one
    {a : Type u} [Fintype a] [DecidableEq a]
    (A : CMatrix a) (hA : A.PosSemidef) : A ≤ (‖A‖ : ℂ) • (1 : CMatrix a) :=
  (cMatrix_norm_le_iff_le_smul_one A hA ‖A‖ (norm_nonneg A)).mp le_rfl

/-- The two rectangular Gram matrices have the same nonnegative scalar
identity bounds. This is the operator-order consequence of their common
nonzero spectrum. -/
theorem conjTranspose_mul_le_smul_one_iff
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : Matrix a b ℂ) (c : ℝ) (hc : 0 ≤ c) :
    Aᴴ * A ≤ (c : ℂ) • (1 : CMatrix b) ↔ A * Aᴴ ≤ (c : ℂ) • (1 : CMatrix a) := by
  have hn : ‖Aᴴ * A‖ = ‖A * Aᴴ‖ := by
    calc
      _ = ‖A‖ * ‖A‖ := Matrix.l2_opNorm_conjTranspose_mul_self A
      _ = ‖Aᴴ‖ * ‖Aᴴ‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ = _ := by simpa using (Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ).symm
  rw [← cMatrix_norm_le_iff_le_smul_one _ (Matrix.posSemidef_conjTranspose_mul_self A) c hc,
    ← cMatrix_norm_le_iff_le_smul_one _ (Matrix.posSemidef_self_mul_conjTranspose A) c hc, hn]

/-- Scalar upper bounds transfer between the two marginals of an arbitrary
rank-one operator, including the zero vector and unequal system dimensions
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem partialTraceA_rankOneMatrix_le_smul_one_iff
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (v : a × b → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    partialTraceA (rankOneMatrix v) ≤ (c : ℂ) • (1 : CMatrix b) ↔
    partialTraceB (rankOneMatrix v) ≤ (c : ℂ) • (1 : CMatrix a) := by
  let A : Matrix a b ℂ := fun i j => v (i, j)
  have hA : partialTraceA (rankOneMatrix v) = (Aᴴ * A)ᵀ := by
    ext i j
    change (∑ x : a, v (x, i) * star (v (x, j))) =
      ∑ x : a, star (v (x, j)) * v (x, i)
    simp only [mul_comm]
  have hB : partialTraceB (rankOneMatrix v) = A * Aᴴ := by
    ext i j
    rfl
  have ht : (Aᴴ * A)ᵀ ≤ (c : ℂ) • (1 : CMatrix b) ↔
      Aᴴ * A ≤ (c : ℂ) • (1 : CMatrix b) := by
    simp only [Matrix.le_iff]
    have heq : (c : ℂ) • (1 : CMatrix b) - (Aᴴ * A)ᵀ =
        ((c : ℂ) • (1 : CMatrix b) - Aᴴ * A)ᵀ := by
      simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    rw [heq, Matrix.posSemidef_transpose_iff]
  rw [hA, hB, ht]
  exact conjTranspose_mul_le_smul_one_iff A c hc

/-- Complementary rank-one marginals have equal operator norms. This is the
part of pure-state spectral equality needed for marginal order bounds
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:292-374]. -/
theorem norm_partialTraceA_rankOneMatrix_eq_partialTraceB
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (v : a × b → ℂ) :
    ‖partialTraceA (rankOneMatrix v)‖ = ‖partialTraceB (rankOneMatrix v)‖ := by
  have hA := partialTraceA_posSemidef (rankOneMatrix_pos v)
  have hB := partialTraceB_posSemidef (rankOneMatrix_pos v)
  apply le_antisymm
  · apply (cMatrix_norm_le_iff_le_smul_one _ hA _ (norm_nonneg _)).mpr
    exact (partialTraceA_rankOneMatrix_le_smul_one_iff v _ (norm_nonneg _)).mpr
      (cMatrix_le_norm_smul_one _ hB)
  · apply (cMatrix_norm_le_iff_le_smul_one _ hB _ (norm_nonneg _)).mpr
    exact (partialTraceA_rankOneMatrix_le_smul_one_iff v _ (norm_nonneg _)).mp
      (cMatrix_le_norm_smul_one _ hA)

end

end QIT
