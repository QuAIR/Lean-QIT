/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Geometry.PurifiedDistance
public import QIT.States.Geometry.PureTargetFidelity
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Geometry of an approximate projector filter

Normalized filter geometry for
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419].
Matrix norms are L2 operator norms.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

variable {x : Type*} [Fintype x] [DecidableEq x]

omit [DecidableEq x] in
/-- The rank-one trace is the squared Euclidean norm of the amplitude. -/
theorem rankOneMatrix_trace_re_eq_norm_sq (v : x → ℂ) :
    (rankOneMatrix v).trace.re = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ x) _ _ _ (WithLp.toLp 2 v)]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [rankOneMatrix_trace, dotProduct]

omit [DecidableEq x] in
/-- Moving a Hermitian matrix between the slots of a quadratic form. -/
theorem hermitian_mulVec_dotProduct (P : CMatrix x) (hP : P.IsHermitian)
    (v w : x → ℂ) : star (P.mulVec v) ⬝ᵥ w = star v ⬝ᵥ P.mulVec w := by
  rw [Matrix.star_mulVec, hP.eq, Matrix.dotProduct_mulVec]

/-- A supported unit eigenvector evaluates the uncompressed test to its eigenvalue. -/
theorem blowingUp_test_expectation
    (P Q : CMatrix x) (hP : P.IsHermitian) (ψ : PureVector x)
    (hψ : P.mulVec ψ.amp = ψ.amp) (lam : ℝ)
    (heig : (P * Q).mulVec ψ.amp = (lam : ℂ) • ψ.amp) :
    star ψ.amp ⬝ᵥ Q.mulVec ψ.amp = (lam : ℂ) := by
  calc
    _ = star (P.mulVec ψ.amp) ⬝ᵥ Q.mulVec ψ.amp := by rw [hψ]
    _ = star ψ.amp ⬝ᵥ (P * Q).mulVec ψ.amp := by
      rw [hermitian_mulVec_dotProduct P hP, Matrix.mulVec_mulVec]
    _ = (lam : ℂ) := by
      rw [heig, dotProduct_smul]
      have hu : star ψ.amp ⬝ᵥ ψ.amp = 1 := by
        rw [dotProduct_comm]
        exact ψ.trace_rankOne_eq_one
      simp [hu]

/-- The test expectation as a trace against the input pure state. -/
theorem blowingUp_test_state_trace
    (P Q : CMatrix x) (hP : P.IsHermitian) (ψ : PureVector x)
    (hψ : P.mulVec ψ.amp = ψ.amp) (lam : ℝ)
    (heig : (P * Q).mulVec ψ.amp = (lam : ℂ) • ψ.amp) :
    (Q * ψ.state.matrix).trace = (lam : ℂ) := by
  rw [PureVector.state_matrix, rankOneMatrix, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm]
  exact blowingUp_test_expectation P Q hP ψ hψ lam heig

/-- A positive contraction has square bounded by itself. -/
theorem posSemidef_mul_self_le (Q : CMatrix x) (hQ : Q.PosSemidef)
    (hQ1 : Q ≤ 1) : Q * Q ≤ Q := by
  let : CStarAlgebra (CMatrix x) := {}
  have hc : Commute Q (1 - Q) := by
    show Q * (1 - Q) = (1 - Q) * Q
    noncomm_ring
  have hh := hc.mul_nonneg hQ.nonneg (sub_nonneg.mpr hQ1)
  rw [mul_sub, mul_one] at hh
  exact sub_nonneg.mp hh

/-- The squared test-vector norm is at most the supported eigenvalue. -/
theorem blowingUp_test_vector_norm_sq_le
    (P Q : CMatrix x) (hP : P.IsHermitian) (hQ : Q.PosSemidef)
    (hQ1 : Q ≤ 1) (ψ : PureVector x) (hψ : P.mulVec ψ.amp = ψ.amp)
    (lam : ℝ) (heig : (P * Q).mulVec ψ.amp = (lam : ℂ) • ψ.amp) :
    (rankOneMatrix (Q.mulVec ψ.amp)).trace.re ≤ lam := by
  have hb := (Matrix.le_iff.mp (posSemidef_mul_self_le Q hQ hQ1)).re_dotProduct_nonneg ψ.amp
  have hnorm : star ψ.amp ⬝ᵥ (Q * Q).mulVec ψ.amp =
      (rankOneMatrix (Q.mulVec ψ.amp)).trace := by
    rw [← Matrix.mulVec_mulVec, ← hermitian_mulVec_dotProduct Q hQ.isHermitian,
      rankOneMatrix_trace, dotProduct_comm]
    rfl
  change 0 ≤ (star ψ.amp ⬝ᵥ (Q - Q * Q).mulVec ψ.amp).re at hb
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    blowingUp_test_expectation P Q hP ψ hψ lam heig, hnorm] at hb
  change 0 ≤ lam - _ at hb
  linarith

omit [DecidableEq x] in
/-- Rank-one traces add for orthogonal amplitudes. -/
theorem rankOneMatrix_trace_add_of_orthogonal (v w : x → ℂ)
    (h : star v ⬝ᵥ w = 0) :
    (rankOneMatrix (v + w)).trace = (rankOneMatrix v).trace + (rankOneMatrix w).trace := by
  have h' : star w ⬝ᵥ v = 0 := by
    rw [Matrix.star_dotProduct, h, star_zero]
  change (v + w) ⬝ᵥ star (v + w) = v ⬝ᵥ star v + w ⬝ᵥ star w
  simp only [star_add, dotProduct_add, add_dotProduct]
  have hvw : v ⬝ᵥ star w = 0 := by rwa [dotProduct_comm]
  have hwv : w ⬝ᵥ star v = 0 := by rwa [dotProduct_comm]
  rw [hvw, hwv]
  simp

/-- Multiplication by a matrix bounds the rank-one trace by its squared operator norm. -/
theorem rankOneMatrix_mulVec_trace_re_le (A : CMatrix x) (v : x → ℂ) :
    (rankOneMatrix (A.mulVec v)).trace.re ≤ ‖A‖ ^ 2 * (rankOneMatrix v).trace.re := by
  rw [rankOneMatrix_trace_re_eq_norm_sq, rankOneMatrix_trace_re_eq_norm_sq]
  have hh := A.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have hh' : ‖WithLp.toLp 2 (A.mulVec v)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 v‖ := hh
  calc
    _ ≤ (‖A‖ * ‖WithLp.toLp 2 v‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hh'
    _ = _ := by ring

/-- The component created outside the projector image is orthogonal to the input. -/
theorem blowingUp_filter_error_orthogonal
    (P T Q : CMatrix x) (hP : P.IsHermitian) (hPid : P * P = P)
    (hPT : P * T = P) (ψ : PureVector x) (hψ : P.mulVec ψ.amp = ψ.amp) :
    star ψ.amp ⬝ᵥ ((T - P) * Q).mulVec ψ.amp = 0 := by
  calc
    _ = star (P.mulVec ψ.amp) ⬝ᵥ ((T - P) * Q).mulVec ψ.amp := by rw [hψ]
    _ = star ψ.amp ⬝ᵥ (P * ((T - P) * Q)).mulVec ψ.amp := by
      rw [hermitian_mulVec_dotProduct P hP, Matrix.mulVec_mulVec]
    _ = 0 := by simp [← Matrix.mul_assoc, Matrix.mul_sub, hPT, hPid]

/-- The filtered vector has overlap equal to the supported eigenvalue. -/
theorem blowingUp_filter_overlap
    (P T Q : CMatrix x) (hP : P.IsHermitian) (hPT : P * T = P)
    (ψ : PureVector x) (hψ : P.mulVec ψ.amp = ψ.amp) (lam : ℝ)
    (heig : (P * Q).mulVec ψ.amp = (lam : ℂ) • ψ.amp) :
    star ψ.amp ⬝ᵥ (T * Q).mulVec ψ.amp = (lam : ℂ) := by
  calc
    _ = star (P.mulVec ψ.amp) ⬝ᵥ (T * Q).mulVec ψ.amp := by rw [hψ]
    _ = star ψ.amp ⬝ᵥ (P * Q).mulVec ψ.amp := by
      rw [hermitian_mulVec_dotProduct P hP, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPT]
    _ = (lam : ℂ) := by
      rw [heig, dotProduct_smul]
      have hu : star ψ.amp ⬝ᵥ ψ.amp = 1 := by
        rw [dotProduct_comm]
        exact ψ.trace_rankOne_eq_one
      simp [hu]

/-- Orthogonal splitting of the filtered vector into the supported and error parts. -/
theorem blowingUp_filter_trace_split
    (P T Q : CMatrix x) (hP : P.IsHermitian) (hPid : P * P = P)
    (hPT : P * T = P) (ψ : PureVector x) (hψ : P.mulVec ψ.amp = ψ.amp)
    (lam : ℝ) (heig : (P * Q).mulVec ψ.amp = (lam : ℂ) • ψ.amp) :
    (rankOneMatrix ((T * Q).mulVec ψ.amp)).trace.re = lam ^ 2 +
      (rankOneMatrix (((T - P) * Q).mulVec ψ.amp)).trace.re := by
  have hsplit : (T * Q).mulVec ψ.amp =
      (lam : ℂ) • ψ.amp + ((T - P) * Q).mulVec ψ.amp := by
    rw [Matrix.sub_mul, Matrix.sub_mulVec, heig]
    abel
  have hort : star ((lam : ℂ) • ψ.amp) ⬝ᵥ ((T - P) * Q).mulVec ψ.amp = 0 := by
    rw [star_smul, smul_dotProduct, blowingUp_filter_error_orthogonal P T Q hP hPid hPT ψ hψ]
    simp
  have htr : (rankOneMatrix ((lam : ℂ) • ψ.amp)).trace = (lam : ℂ) ^ 2 := by
    change ((lam : ℂ) • ψ.amp) ⬝ᵥ star ((lam : ℂ) • ψ.amp) = _
    rw [star_smul, smul_dotProduct, dotProduct_smul]
    have hu : ψ.amp ⬝ᵥ star ψ.amp = 1 := ψ.trace_rankOne_eq_one
    simp [hu, pow_two]
  rw [hsplit, rankOneMatrix_trace_add_of_orthogonal _ _ hort, Complex.add_re, htr]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Normalizing a vector with real overlap gives the corresponding overlap ratio. -/
theorem PureVector.overlap_normalize_of_real
    (ψ : PureVector x) (v : x → ℂ) (hd : 0 < (rankOneMatrix v).trace.re)
    (lam : ℝ) (hover : star ψ.amp ⬝ᵥ v = (lam : ℂ)) :
    ψ.overlap (PureVector.normalize v hd) =
      ((lam / Real.sqrt (rankOneMatrix v).trace.re : ℝ) : ℂ) := by
  change star ψ.amp ⬝ᵥ ((((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) • v) = _
  rw [dotProduct_smul, hover]
  simp [div_eq_mul_inv, mul_comm]

/-- Squared fidelity after normalization is the squared overlap divided by mass. -/
theorem PureVector.squaredFidelity_normalize_of_real
    (ψ : PureVector x) (v : x → ℂ) (hd : 0 < (rankOneMatrix v).trace.re)
    (lam : ℝ) (hover : star ψ.amp ⬝ᵥ v = (lam : ℂ)) :
    ψ.state.squaredFidelity (PureVector.normalize v hd).state =
      lam ^ 2 / (rankOneMatrix v).trace.re := by
  rw [State.squaredFidelity_pure_right_eq_trace]
  change (rankOneMatrix ψ.amp * rankOneMatrix (PureVector.normalize v hd).amp).trace.re = _
  rw [PureVector.rankOneMatrix_mul_trace_re_eq_overlapSq, PureVector.overlapSq_eq_normSq,
    ψ.overlap_normalize_of_real v hd lam hover, Complex.normSq_ofReal]
  rw [← pow_two, div_pow, Real.sq_sqrt hd.le]

/-- An approximate projector filter produces a normalized pure vector nearby.
This is the filter geometry used in
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:408-419]. -/
theorem blowingUp_filter_geometry
    (P T Q : CMatrix x) (hP : P.IsHermitian) (hPid : P * P = P)
    (hPT : P * T = P) (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1)
    (ψ : PureVector x) (hψ : P.mulVec ψ.amp = ψ.amp)
    {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε)
    (heig : (P * Q).mulVec ψ.amp = (lam : ℂ) • ψ.amp)
    (happrox : ‖T - P‖ ^ 2 ≤ ε ^ 2 * lam / 4) :
    let v := (T * Q).mulVec ψ.amp
    let d := (rankOneMatrix v).trace.re
    0 < d ∧ lam ^ 2 ≤ d ∧ d ≤ lam ^ 2 + lam * ‖T - P‖ ^ 2 ∧
      ∃ φ : PureVector x, φ.state.matrix = ((d⁻¹ : ℝ) : ℂ) • rankOneMatrix v ∧
        ψ.state.purifiedDistance φ.state ≤ ε / 2 := by
  dsimp only
  let v := (T * Q).mulVec ψ.amp
  let d := (rankOneMatrix v).trace.re
  have hsplit := blowingUp_filter_trace_split P T Q hP hPid hPT ψ hψ lam heig
  have herr0 : 0 ≤ (rankOneMatrix (((T - P) * Q).mulVec ψ.amp)).trace.re :=
    (rankOneMatrix_pos _).trace_nonneg.1
  have hlower : lam ^ 2 ≤ d := by dsimp [d, v]; linarith
  have hd : 0 < d := lt_of_lt_of_le (sq_pos_of_pos hlam) hlower
  have herr := rankOneMatrix_mulVec_trace_re_le (T - P) (Q.mulVec ψ.amp)
  rw [Matrix.mulVec_mulVec] at herr
  have hq := blowingUp_test_vector_norm_sq_le P Q hP hQ hQ1 ψ hψ lam heig
  have hupper : d ≤ lam ^ 2 + lam * ‖T - P‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hq (sq_nonneg ‖T - P‖)
    dsimp [d, v]
    nlinarith
  refine ⟨hd, hlower, hupper, PureVector.normalize v hd,
    PureVector.normalize_state_matrix v hd, ?_⟩
  rw [State.purifiedDistance_eq,
    ψ.squaredFidelity_normalize_of_real v hd lam
      (blowingUp_filter_overlap P T Q hP hPT ψ hψ lam heig)]
  apply (Real.sqrt_le_left (by linarith : 0 ≤ ε / 2)).2
  have hmass : d - lam ^ 2 ≤ ε ^ 2 * lam ^ 2 / 4 := by
    have hmul := mul_le_mul_of_nonneg_left happrox hlam.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlower (sq_nonneg ε)
  change 1 - lam ^ 2 / d ≤ (ε / 2) ^ 2
  rw [show 1 - lam ^ 2 / d = (d - lam ^ 2) / d by
    rw [sub_div, div_self (ne_of_gt hd)]]
  apply (div_le_iff₀ hd).2
  nlinarith

end

end QIT
