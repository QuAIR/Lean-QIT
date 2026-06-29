/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import QIT.Core.SDP.HermitianPSDTraceDuality
public import QIT.Core.SDP.PSDCone
public import QIT.Core.SDP.StrongDuality
public import QIT.Information.Smooth
public import QIT.Information.Renyi
public import QIT.Information.ConditionalRenyiTraceBridge
public import QIT.Util.BlockMatrix
import QIT.States.TraceNorm.Spectral
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Endpoint min/max entropy scales

This module separates the raw endpoint optimization values underneath the
definition-level conditional min/max entropies in `QIT.Information.Smooth`.

The declarations here are intentionally exponent/scale level.  The final
smooth min/max duality proof will need to connect these raw optimization values
to endpoint SDP duality before translating back through `log₂`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise
open scoped Topology

open Matrix
open Set Filter

namespace QIT

universe u v w x

noncomputable section

/-! ## Order-theoretic logarithm transport -/

/-- On a nonempty positive bounded-above set, `log₂` sends the supremum to the
supremum of the image. -/
theorem log2_sSup_image_eq {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddAbove s) (hpos : ∀ x ∈ s, 0 < x) :
    sSup (log2 '' s) = log2 (sSup s) := by
  unfold log2
  have hsup_pos : 0 < sSup s := by
    rcases hne with ⟨x, hx⟩
    exact lt_of_lt_of_le (hpos x hx) (le_csSup hbdd hx)
  have hcont : ContinuousWithinAt (fun x : ℝ => Real.log x / Real.log 2) s (sSup s) := by
    exact (Real.continuousAt_log hsup_pos.ne').div_const _ |>.continuousWithinAt
  have hmono : MonotoneOn (fun x : ℝ => Real.log x / Real.log 2) s := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_right (Real.log_le_log (hpos x hx) hxy)
      (le_of_lt (Real.log_pos one_lt_two))
  have hmap := MonotoneOn.map_csSup_of_continuousWithinAt
    (f := fun x : ℝ => Real.log x / Real.log 2) (A := s) hcont hmono hne hbdd
  simpa using hmap.symm

/-- On a nonempty bounded-below set whose infimum is strictly positive,
`-log₂` sends the infimum to the supremum of the image. -/
theorem neg_log2_sInf_image_eq {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddBelow s) (hinf_pos : 0 < sInf s) :
    sSup ((fun x : ℝ => -log2 x) '' s) = -log2 (sInf s) := by
  unfold log2
  have hcont : ContinuousWithinAt
      (fun x : ℝ => -(Real.log x / Real.log 2)) s (sInf s) := by
    exact (Real.continuousAt_log hinf_pos.ne').div_const _ |>.neg |>.continuousWithinAt
  have hanti : AntitoneOn (fun x : ℝ => -(Real.log x / Real.log 2)) s := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le hinf_pos (csInf_le hbdd hx)
    exact neg_le_neg (div_le_div_of_nonneg_right (Real.log_le_log hxpos hxy)
      (le_of_lt (Real.log_pos one_lt_two)))
  have hmap := AntitoneOn.map_csInf_of_continuousWithinAt
    (f := fun x : ℝ => -(Real.log x / Real.log 2)) (A := s) hcont hanti hne hbdd
  simpa using hmap.symm

theorem neg_log2_rpow_two_neg (lam : ℝ) :
    -log2 (Real.rpow 2 (-lam)) = lam := by
  unfold log2
  rw [show Real.log (Real.rpow 2 (-lam)) = -lam * Real.log 2 by
    exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lam)]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

theorem rpow_two_log2_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hx
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  unfold log2
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

theorem mul_sSup_image_eq {s : Set ℝ} {c : ℝ}
    (hne : s.Nonempty) (hbdd : BddAbove s) (hc : 0 < c) :
    sSup ((fun x : ℝ => c * x) '' s) = c * sSup s := by
  have hcont : ContinuousWithinAt (fun x : ℝ => c * x) s (sSup s) :=
    (continuous_const.mul continuous_id).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun x : ℝ => c * x) s := by
    intro x _ y _ hxy
    exact mul_le_mul_of_nonneg_left hxy (le_of_lt hc)
  have hmap := MonotoneOn.map_csSup_of_continuousWithinAt
    (f := fun x : ℝ => c * x) (A := s) hcont hmono hne hbdd
  simpa using hmap.symm

theorem trace_abs_le_traceNorm {a : Type u} [Fintype a] [DecidableEq a]
    (M : CMatrix a) :
    Complex.abs M.trace ≤ traceNorm M := by
  simpa using traceNorm_variational_unitary_abs_trace_le M (1 : Matrix.unitaryGroup a ℂ)

/-- Trace norm is invariant under conjugate transpose. -/
theorem traceNorm_conjTranspose {a : Type u} [Fintype a] [DecidableEq a]
    (A : CMatrix a) :
    traceNorm (Matrix.conjTranspose A) = traceNorm A := by
  apply le_antisymm
  · obtain ⟨U, hU⟩ :=
      traceNorm_variational_exists_unitary_abs_trace (Matrix.conjTranspose A)
    let V : Matrix.unitaryGroup a ℂ := U⁻¹
    have hcoe : (V : CMatrix a) = star (U : CMatrix a) := by rfl
    have hstar : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
      rw [← Matrix.star_eq_conjTranspose, star_star]
    have htrace :
        ((Matrix.conjTranspose A * (U : CMatrix a)).trace) =
          star ((A * (V : CMatrix a)).trace) := by
      rw [hcoe]
      calc
        (Matrix.conjTranspose A * (U : CMatrix a)).trace =
            ((U : CMatrix a) * Matrix.conjTranspose A).trace := by
              rw [Matrix.trace_mul_comm]
        _ = (Matrix.conjTranspose (A * star (U : CMatrix a))).trace := by
            rw [Matrix.conjTranspose_mul, hstar]
        _ = star ((A * star (U : CMatrix a)).trace) :=
            Matrix.trace_conjTranspose _
    calc
      traceNorm (Matrix.conjTranspose A) =
          Complex.abs ((Matrix.conjTranspose A * (U : CMatrix a)).trace) := hU.symm
      _ = Complex.abs ((A * (V : CMatrix a)).trace) := by simp [htrace]
      _ ≤ traceNorm A := traceNorm_variational_unitary_abs_trace_le A V
  · obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace A
    let V : Matrix.unitaryGroup a ℂ := U⁻¹
    have hcoe : (V : CMatrix a) = star (U : CMatrix a) := by rfl
    have hstar : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
      rw [← Matrix.star_eq_conjTranspose, star_star]
    have htrace :
        ((A * (U : CMatrix a)).trace) =
          star ((Matrix.conjTranspose A * (V : CMatrix a)).trace) := by
      rw [hcoe]
      calc
        (A * (U : CMatrix a)).trace =
            ((U : CMatrix a) * A).trace := by rw [Matrix.trace_mul_comm]
        _ = (Matrix.conjTranspose (Matrix.conjTranspose A * star (U : CMatrix a))).trace := by
            rw [Matrix.conjTranspose_mul, hstar, Matrix.conjTranspose_conjTranspose]
        _ = star ((Matrix.conjTranspose A * star (U : CMatrix a)).trace) :=
            Matrix.trace_conjTranspose _
    calc
      traceNorm A = Complex.abs ((A * (U : CMatrix a)).trace) := hU.symm
      _ = Complex.abs ((Matrix.conjTranspose A * (V : CMatrix a)).trace) := by
            simp [htrace]
      _ ≤ traceNorm (Matrix.conjTranspose A) :=
          traceNorm_variational_unitary_abs_trace_le (Matrix.conjTranspose A) V

theorem State.squaredFidelity_comm {a : Type u} [Fintype a] [DecidableEq a]
    (ρ σ : State a) :
    ρ.squaredFidelity σ = σ.squaredFidelity ρ := by
  rw [State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq,
    State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  congr 1
  have hconj :
      Matrix.conjTranspose (ρ.sqrtMatrix * σ.sqrtMatrix) =
        σ.sqrtMatrix * ρ.sqrtMatrix := by
    rw [Matrix.conjTranspose_mul, ρ.sqrtMatrix_isHermitian.eq,
      σ.sqrtMatrix_isHermitian.eq]
  rw [← hconj, traceNorm_conjTranspose]

theorem PureVector.overlapSq_comm_endpoint {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) :
    Ψ.overlapSq Φ = Φ.overlapSq Ψ := by
  rw [PureVector.overlapSq_eq_normSq, PureVector.overlapSq_eq_normSq]
  have hconj : Ψ.overlap Φ = star (Φ.overlap Ψ) := by
    simp [PureVector.overlap, map_sum, map_mul, mul_comm]
  rw [hconj]
  simp [Complex.normSq]

theorem PureVector.normSq_sum_star_mul_le_rankOne_trace
    {a : Type u} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (η : PureVector a) :
    Complex.normSq (∑ i, star (v i) * η.amp i) ≤
      (rankOneMatrix v).trace.re := by
  classical
  let x : EuclideanSpace ℂ a := WithLp.toLp 2 v
  let y : EuclideanSpace ℂ a := WithLp.toLp 2 η.amp
  have hcs := norm_inner_le_norm (𝕜 := ℂ) x y
  have hinner :
      inner ℂ x y = ∑ i, star (v i) * η.amp i := by
    dsimp [x, y]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  have hxnorm : ‖x‖ ^ 2 = (rankOneMatrix v).trace.re := by
    rw [@norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ a) _ _ _ x]
    dsimp [x]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [rankOneMatrix_trace, dotProduct, mul_comm]
  have hynorm : ‖y‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ a) _ _ _ y]
    dsimp [y]
    rw [EuclideanSpace.inner_toLp_toLp]
    simpa [rankOneMatrix_trace, dotProduct, mul_comm] using
      congrArg Complex.re η.trace_rankOne_eq_one
  have hsq : Complex.normSq (inner ℂ x y) ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖inner ℂ x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by ring
  rw [hinner] at hsq
  rwa [hxnorm, hynorm, mul_one] at hsq

/-- A scalar phase can rotate any complex number so that its real part is its
absolute value. -/
theorem exists_complex_phase_mul_re_eq_abs (z : ℂ) :
    ∃ c : ℂ, c * star c = 1 ∧ (c * z).re = Complex.abs z := by
  by_cases hz : z = 0
  · refine ⟨1, ?_, ?_⟩
    · simp
    · simp [hz]
  · refine ⟨(Complex.abs z : ℂ) / z, ?_, ?_⟩
    · rw [div_eq_mul_inv]
      rw [star_mul]
      rw [show star ((Complex.abs z : ℂ)) = (Complex.abs z : ℂ) by
        apply Complex.ext <;> simp]
      have hzstar : star z ≠ 0 := by
        intro h
        apply hz
        simpa using congrArg star h
      have habs_ne : (Complex.abs z : ℂ) ≠ 0 := by
        exact_mod_cast (norm_ne_zero_iff.mpr hz : Complex.abs z ≠ 0)
      field_simp [hz, hzstar, habs_ne]
      rw [show star (1 / z) = (star z)⁻¹ by simp [div_eq_mul_inv]]
      field_simp [hzstar]
      have hnorm : (Complex.normSq z : ℂ) = star z * z := by
        simpa using (Complex.normSq_eq_conj_mul_self (z := z))
      rw [← hnorm]
      rw [Complex.normSq_eq_norm_sq]
      change ((‖z‖ : ℝ) : ℂ) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ)
      norm_num
    · have hmul : (((Complex.abs z : ℂ) / z) * z) = (Complex.abs z : ℂ) := by
        field_simp [hz]
      rw [hmul]
      simp

theorem psdSqrt_real_smul_one {a : Type u} [Fintype a] [DecidableEq a]
    {r : ℝ} (hr : 0 ≤ r) :
    psdSqrt (((r : ℂ) • (1 : CMatrix a))) =
      ((Real.sqrt r : ℝ) : ℂ) • (1 : CMatrix a) := by
  let rr : NNReal := ⟨r, hr⟩
  have hscalar : ((r : ℂ) • (1 : CMatrix a)) = algebraMap NNReal (CMatrix a) rr := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.algebraMap_matrix_apply, rr]
      rfl
    · simp [Matrix.algebraMap_matrix_apply, rr, hij]
  have hsqrt := (CFC.sqrt_algebraMap (A := CMatrix a) (r := rr))
  rw [hscalar]
  rw [show ((Real.sqrt r : ℝ) : ℂ) • (1 : CMatrix a) =
      algebraMap NNReal (CMatrix a) (NNReal.sqrt rr) by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.algebraMap_matrix_apply, rr]
      rw [Real.sqrt, Real.toNNReal_of_nonneg hr]
      rfl
    · simp [Matrix.algebraMap_matrix_apply, hij]]
  simp [psdSqrt] at hsqrt ⊢

theorem psdSqrt_real_smul {a : Type u} [Fintype a] [DecidableEq a]
    {r : ℝ} (hr : 0 ≤ r) {M : CMatrix a} (hM : M.PosSemidef) :
    psdSqrt (((r : ℂ) • M)) =
      ((Real.sqrt r : ℝ) : ℂ) • psdSqrt M := by
  let S : CMatrix a := ((Real.sqrt r : ℝ) : ℂ) • psdSqrt M
  have hSsq : S * S = ((r : ℂ) • M) := by
    dsimp [S]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hr,
      psdSqrt_mul_self_of_posSemidef hM]
  have hSpos : S.PosSemidef := by
    have hscalar : (0 : ℂ) ≤ ((Real.sqrt r : ℝ) : ℂ) := by
      exact_mod_cast Real.sqrt_nonneg r
    exact Matrix.PosSemidef.smul (psdSqrt_pos M) hscalar
  change psdSqrt (((r : ℂ) • M)) = S
  simpa [psdSqrt, S] using
    (CFC.sqrt_unique (a := ((r : ℂ) • M)) (b := S) hSsq hSpos.nonneg)

theorem psdSqrt_kronecker {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    psdSqrt (Matrix.kronecker A B) =
      Matrix.kronecker (psdSqrt A) (psdSqrt B) := by
  simp only [psdSqrt, CFC.sqrt_eq_rpow]
  exact cMatrix_rpow_kronecker_nonneg hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem traceNorm_real_smul_eq {a : Type u} [Fintype a] [DecidableEq a]
    {c : ℝ} (hc : 0 ≤ c) (M : CMatrix a) :
    traceNorm (((c : ℂ) • M)) = c * traceNorm M := by
  by_cases hcz : c = 0
  · simp [hcz]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    apply le_antisymm
    · exact traceNorm_real_smul_le hc M
    · have hInvNonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr hc
      have hle := traceNorm_real_smul_le hInvNonneg (((c : ℂ) • M))
      have hscale : (((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • M)) = M := by
        rw [smul_smul]
        have hcC : ((c : ℂ) ≠ 0) := by exact_mod_cast hcz
        simp [hcC]
      rw [hscale] at hle
      have hmul := mul_le_mul_of_nonneg_left hle hc
      have htrace_nonneg : 0 ≤ traceNorm (((c : ℂ) • M)) :=
        traceNorm_nonneg _
      have hc_inv : c * c⁻¹ = 1 := mul_inv_cancel₀ hcz
      nlinarith

theorem traceNorm_sq_le_card_mul_hilbertSchmidt {a : Type u}
    [Fintype a] [DecidableEq a] (M : CMatrix a) :
    traceNorm M ^ 2 ≤
      (Fintype.card a : ℝ) * ((star M * M).trace).re := by
  have hmain := traceNorm_sq_le_finrank_range_mul_hilbertSchmidt M
  have hrank : (Module.finrank ℂ (LinearMap.range M.toEuclideanLin) : ℝ) ≤
      (Fintype.card a : ℝ) := by
    have hnat : Module.finrank ℂ (LinearMap.range M.toEuclideanLin) ≤ Fintype.card a := by
      simpa [finrank_euclideanSpace] using
        (Submodule.finrank_le (LinearMap.range M.toEuclideanLin))
    exact_mod_cast hnat
  have hhs_nonneg : 0 ≤ ((star M * M).trace).re :=
    (Matrix.PosSemidef.trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self M)).1
  exact hmain.trans (mul_le_mul_of_nonneg_right hrank hhs_nonneg)

/-- A block-diagonal matrix with positive semidefinite diagonal blocks is
positive semidefinite.  This small local bridge is the block-cone constructor
needed for endpoint SDP feasibility. -/
theorem cMatrix_fromBlocks_diagonal_posSemidef {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {D : CMatrix b}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D : CMatrix (Sum a b)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.IsHermitian.ext_iff.mp hA.isHermitian,
        Matrix.IsHermitian.ext_iff.mp hD.isHermitian]
  · intro x
    let xl : a → ℂ := fun i => x (Sum.inl i)
    let xr : b → ℂ := fun i => x (Sum.inr i)
    have hleft : 0 ≤ star xl ⬝ᵥ A.mulVec xl :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 xl
    have hright : 0 ≤ star xr ⬝ᵥ D.mulVec xr :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hD).2 xr
    have hsum : 0 ≤ star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr :=
      add_nonneg hleft hright
    have hquad :
        star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D).mulVec x =
          star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_fromBlocks, Matrix.dotProduct_block]
      simp [Matrix.dotProduct_mulVec, xl, xr]
      change
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr =
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr
      rfl
    simpa [hquad] using hsum

/-- The elementary unitary block matrix `[[I,U],[U†,I]]` is positive
semidefinite.  It factors as `T†T`, with `T = [[I,U],[0,0]]`. -/
theorem cMatrix_fromBlocks_unitary_posSemidef {a : Type u}
    [Fintype a] [DecidableEq a] (U : Matrix.unitaryGroup a ℂ) :
    (Matrix.fromBlocks (1 : CMatrix a) (U : CMatrix a) (star (U : CMatrix a)) 1 :
      CMatrix (Sum a a)).PosSemidef := by
  classical
  let T : CMatrix (Sum a a) :=
    Matrix.fromBlocks (1 : CMatrix a) (U : CMatrix a) 0 0
  have hpsd : (star T * T).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self T
  have hfactor :
      star T * T =
        (Matrix.fromBlocks (1 : CMatrix a) (U : CMatrix a) (star (U : CMatrix a)) 1 :
          CMatrix (Sum a a)) := by
    have hUconj : ((U : CMatrix a)ᴴ) * (U : CMatrix a) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        Matrix.UnitaryGroup.star_mul_self U
    dsimp [T]
    rw [Matrix.star_eq_conjTranspose]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [hUconj, Matrix.star_eq_conjTranspose]
  simpa [hfactor.symm] using hpsd

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem traceNorm_eq_trace_psdSqrt_mul_conjTranspose (A : CMatrix a) :
    traceNorm A = (psdSqrt (A * Matrix.conjTranspose A)).trace.re := by
  rw [← traceNorm_conjTranspose A]
  simp [traceNorm, Matrix.conjTranspose_conjTranspose]

theorem traceNorm_eq_of_mul_conjTranspose_eq {A B : CMatrix a}
    (h : A * Matrix.conjTranspose A = B * Matrix.conjTranspose B) :
    traceNorm A = traceNorm B := by
  rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose A,
    traceNorm_eq_trace_psdSqrt_mul_conjTranspose B, h]

theorem traceNorm_eq_of_conjTranspose_mul_eq {A B : CMatrix a}
    (h : Matrix.conjTranspose A * A = Matrix.conjTranspose B * B) :
    traceNorm A = traceNorm B := by
  rw [← traceNorm_conjTranspose A, ← traceNorm_conjTranspose B]
  apply traceNorm_eq_of_mul_conjTranspose_eq
  simpa [Matrix.conjTranspose_conjTranspose] using h

namespace ReferenceIsometry

variable {r₁ : Type w} {r₂ : Type x}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

private theorem matrix_mul_conjTranspose_mul_matrix_smoothEndpoint (V : ReferenceIsometry r₁ r₂)
    (B C : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
  calc
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * B * (Matrix.conjTranspose V.matrix * V.matrix) *
        C * Matrix.conjTranspose V.matrix := by
        simp only [Matrix.mul_assoc]
    _ = V.matrix * B * (1 : CMatrix r₁) * C * Matrix.conjTranspose V.matrix := by
        rw [V.isometry]
    _ = V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]

omit [DecidableEq a] [DecidableEq r₁] in
theorem rightBlock_mul (X Y : CMatrix (Prod a r₁)) (i j : a) :
    rightBlock (X * Y) i j =
      ∑ k : a, rightBlock X i k * rightBlock Y k j := by
  ext x y
  change (X * Y) (i, x) (j, y) =
    (∑ k : a, rightBlock X i k * rightBlock Y k j) x y
  rw [Matrix.mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Matrix.sum_apply]
  simp [rightBlock, Matrix.mul_apply]

omit [DecidableEq a] in
theorem applyMatrixRight_mul (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod a r₁)) :
    V.applyMatrixRight X * V.applyMatrixRight Y = V.applyMatrixRight (X * Y) := by
  ext p q
  calc
    (V.applyMatrixRight X * V.applyMatrixRight Y) p q =
        (∑ k : a,
          ((V.matrix * rightBlock X p.1 k * Matrix.conjTranspose V.matrix) *
            (V.matrix * rightBlock Y k q.1 * Matrix.conjTranspose V.matrix)) p.2 q.2) := by
      change (∑ j : Prod a r₂, V.applyMatrixRight X p j * V.applyMatrixRight Y j q) = _
      rw [← Finset.univ_product_univ, Finset.sum_product]
      simp [applyMatrixRight, Matrix.mul_apply]
    _ = (∑ k : a,
          (V.matrix * (rightBlock X p.1 k * rightBlock Y k q.1) *
            Matrix.conjTranspose V.matrix) p.2 q.2) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := V.matrix_mul_conjTranspose_mul_matrix_smoothEndpoint
        (rightBlock X p.1 k) (rightBlock Y k q.1)
      exact congrFun (congrFun h p.2) q.2
    _ = (V.matrix * (∑ k : a, rightBlock X p.1 k * rightBlock Y k q.1) *
            Matrix.conjTranspose V.matrix) p.2 q.2 := by
      have hsum :
          V.matrix * (∑ k : a, rightBlock X p.1 k * rightBlock Y k q.1) *
              Matrix.conjTranspose V.matrix =
            ∑ k : a, V.matrix * (rightBlock X p.1 k * rightBlock Y k q.1) *
              Matrix.conjTranspose V.matrix := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
      have hentry := congrFun (congrFun hsum p.2) q.2
      simpa [Matrix.sum_apply] using hentry.symm
    _ = V.applyMatrixRight (X * Y) p q := by
      rw [← rightBlock_mul X Y p.1 q.1]
      rfl

theorem applyMatrixRight_posSemidef (V : ReferenceIsometry r₁ r₂)
    {X : CMatrix (Prod a r₁)} (hX : X.PosSemidef) :
    (V.applyMatrixRight X).PosSemidef := by
  rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]
  exact MatrixMap.isCompletelyPositive_mapsPositive
    (MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V))
    (MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
      (MatrixMap.ofReferenceIsometry V)
      (Channel.idChannel a).completelyPositive
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V))
    X hX

theorem psdSqrt_applyMatrixRight (V : ReferenceIsometry r₁ r₂)
    {X : CMatrix (Prod a r₁)} (hX : X.PosSemidef) :
    psdSqrt (V.applyMatrixRight X) = V.applyMatrixRight (psdSqrt X) := by
  let S : CMatrix (Prod a r₂) := V.applyMatrixRight (psdSqrt X)
  have hSpos : S.PosSemidef := by
    simpa [S] using V.applyMatrixRight_posSemidef (a := a) (psdSqrt_pos X)
  have hSsq : S * S = V.applyMatrixRight X := by
    dsimp [S]
    rw [applyMatrixRight_mul, psdSqrt_mul_self_of_posSemidef hX]
  simpa [psdSqrt, S] using
    (CFC.sqrt_unique (a := V.applyMatrixRight X) (b := S) hSsq hSpos.nonneg)

private def prodSumRightEquiv
    (a : Type u) (extra : Type w) (b : Type v) :
    Sum (Prod a extra) (Prod a b) ≃ Prod a (Sum extra b) where
  toFun x := match x with
    | Sum.inl ae => (ae.1, Sum.inl ae.2)
    | Sum.inr ab => (ab.1, Sum.inr ab.2)
  invFun x := match x.2 with
    | Sum.inl e => Sum.inl (x.1, e)
    | Sum.inr y => Sum.inr (x.1, y)
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x with | mk i s => cases s <;> rfl

private theorem submatrix_equiv_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B : CMatrix κ) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_equiv e
    (fun x => A (e i) (e x) * B (e x) (e j))
    (fun y => A (e i) y * B y (e j))
    (by simp)).symm

private theorem eq_of_submatrix_equiv_eq {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    {A B : CMatrix κ} (h : A.submatrix e e = B.submatrix e e) :
    A = B := by
  ext i j
  have hij := congrFun (congrFun h (e.symm i)) (e.symm j)
  simpa using hij

omit [Fintype a] [DecidableEq a] in
private theorem applyMatrixRight_sumInr_submatrix_prodSumRightEquiv
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (X : CMatrix (Prod a b)) :
    ((ReferenceIsometry.sumInr extra b).applyMatrixRight X).submatrix
      (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b) =
        (Matrix.fromBlocks (0 : CMatrix (Prod a extra)) 0 0 X :
          CMatrix (Sum (Prod a extra) (Prod a b))) := by
  ext x y
  cases x <;> cases y <;>
    simp [prodSumRightEquiv, ReferenceIsometry.applyMatrixRight,
      ReferenceIsometry.rightBlock, ReferenceIsometry.sumInr, Matrix.mul_apply]

private theorem applyMatrixRight_sumInr_sandwich_submatrix_prodSumRightEquiv
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (A : CMatrix (Prod a b)) (Y : CMatrix (Prod a (Sum extra b))) :
    (((ReferenceIsometry.sumInr extra b).applyMatrixRight A) * Y *
        ((ReferenceIsometry.sumInr extra b).applyMatrixRight A)).submatrix
        (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b) =
      Matrix.fromBlocks (0 : CMatrix (Prod a extra)) 0 0
        (A * Matrix.sumBlock22 (Y.submatrix
          (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b)) * A) := by
  rw [submatrix_equiv_mul, submatrix_equiv_mul]
  rw [applyMatrixRight_sumInr_submatrix_prodSumRightEquiv]
  rw [← Matrix.fromBlocks_sumBlocks
    (Y.submatrix (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b))]
  rw [Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_multiply]
  ext x y
  cases x <;> cases y
  all_goals
    simp [Matrix.sumBlock11, Matrix.sumBlock12, Matrix.sumBlock21, Matrix.sumBlock22,
      Matrix.fromBlocks, Matrix.submatrix]

private theorem applyMatrixRight_sumInr_sandwich
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (A : CMatrix (Prod a b)) (Y : CMatrix (Prod a (Sum extra b))) :
    ((ReferenceIsometry.sumInr extra b).applyMatrixRight A) * Y *
        ((ReferenceIsometry.sumInr extra b).applyMatrixRight A) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight
        (A * Matrix.sumBlock22 (Y.submatrix
          (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b)) * A) := by
  apply eq_of_submatrix_equiv_eq (prodSumRightEquiv a extra b)
  rw [applyMatrixRight_sumInr_sandwich_submatrix_prodSumRightEquiv]
  rw [applyMatrixRight_sumInr_submatrix_prodSumRightEquiv]

/-- Concrete right-summand reference padding preserves trace norm. -/
theorem traceNorm_applyMatrixRight_sumInr
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (X : CMatrix (Prod a b)) :
    traceNorm ((ReferenceIsometry.sumInr extra b).applyMatrixRight X) =
      traceNorm X := by
  let e := prodSumRightEquiv a extra b
  have htn := traceNorm_submatrix_equiv e
    ((ReferenceIsometry.sumInr extra b).applyMatrixRight X)
  rw [applyMatrixRight_sumInr_submatrix_prodSumRightEquiv (a := a)
    (b := b) (extra := extra) X] at htn
  rw [← htn]
  rw [Matrix.traceNorm_fromBlocks_diagonal]
  simp

/-- Concrete right-summand reference padding commutes with the positive square root. -/
theorem psdSqrt_applyMatrixRight_sumInr
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    {X : CMatrix (Prod a b)} (hX : X.PosSemidef) :
    psdSqrt ((ReferenceIsometry.sumInr extra b).applyMatrixRight X) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight (psdSqrt X) :=
  (ReferenceIsometry.sumInr extra b).psdSqrt_applyMatrixRight hX

end ReferenceIsometry

namespace MatrixMap

variable {κ : Type x} [Fintype κ]

def smoothEndpointKrausAdjoint (K : κ → Matrix b a ℂ)
    (E : CMatrix b) : CMatrix a :=
  ∑ k : κ, Matrix.conjTranspose (K k) * E * K k

theorem smoothEndpoint_ofKraus_trace_duality
    (K : κ → Matrix b a ℂ) (X : CMatrix a) (E : CMatrix b) :
    (((ofKraus K) X) * E).trace =
      (X * smoothEndpointKrausAdjoint K E).trace := by
  simp [ofKraus, smoothEndpointKrausAdjoint, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  let Kk : Matrix b a ℂ := K k
  let KkH : Matrix a b ℂ := Matrix.conjTranspose Kk
  calc
    ((K k * X * Matrix.conjTranspose (K k)) * E).trace =
        ((Kk * X * KkH) * E).trace := by rfl
    _ = (E * (Kk * X * KkH)).trace := by rw [Matrix.trace_mul_comm]
    _ = ((E * Kk) * (X * KkH)).trace := by
          simp only [Matrix.mul_assoc]
    _ = ((X * KkH) * (E * Kk)).trace := by rw [Matrix.trace_mul_comm]
    _ = (X * (KkH * E * Kk)).trace := by
          simp only [Matrix.mul_assoc]
    _ = (X * (Matrix.conjTranspose (K k) * E * K k)).trace := by rfl

theorem smoothEndpointKrausAdjoint_posSemidef
    (K : κ → Matrix b a ℂ) {E : CMatrix b} (hE : E.PosSemidef) :
    (smoothEndpointKrausAdjoint K E).PosSemidef := by
  unfold smoothEndpointKrausAdjoint
  exact Matrix.posSemidef_sum Finset.univ fun k _ => by
    simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using hE.mul_mul_conjTranspose_same (Matrix.conjTranspose (K k))

theorem smoothEndpointKrausAdjoint_one_le_of_traceNonincreasing
    (K : κ → Matrix b a ℂ)
    (hTNI : IsTraceNonincreasing (ofKraus K)) :
    smoothEndpointKrausAdjoint K (1 : CMatrix b) ≤ 1 := by
  rw [Matrix.le_iff]
  refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg ?_).2 ?_
  · exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      (smoothEndpointKrausAdjoint_posSemidef K Matrix.PosSemidef.one).isHermitian
  · intro A hA
    have hle := hTNI A hA
    have hdual :
        (((ofKraus K) A) * (1 : CMatrix b)).trace =
          (A * smoothEndpointKrausAdjoint K (1 : CMatrix b)).trace :=
      smoothEndpoint_ofKraus_trace_duality K A (1 : CMatrix b)
    rw [Matrix.mul_one] at hdual
    have htrace :
        ((A * ((1 : CMatrix a) -
          smoothEndpointKrausAdjoint K (1 : CMatrix b))).trace).re =
          A.trace.re -
            ((A * smoothEndpointKrausAdjoint K (1 : CMatrix b)).trace).re := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm]
    rw [htrace]
    rw [← hdual]
    exact sub_nonneg.mpr hle

def smoothEndpointKrausStack (K : κ → Matrix b a ℂ) :
    Matrix (Prod κ b) a ℂ :=
  fun x i => K x.1 x.2 i

theorem smoothEndpointKrausStack_conjTranspose_mul
    (K : κ → Matrix b a ℂ) :
    Matrix.conjTranspose (smoothEndpointKrausStack K) *
        smoothEndpointKrausStack K =
      smoothEndpointKrausAdjoint K (1 : CMatrix b) := by
  classical
  ext i j
  calc
    (Matrix.conjTranspose (smoothEndpointKrausStack K) *
        smoothEndpointKrausStack K) i j =
        ∑ x : κ, ∑ y : b, star (K x y i) * K x y j := by
          simp [smoothEndpointKrausStack, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    _ = (∑ x : κ, Matrix.conjTranspose (K x) * K x) i j := by
          rw [Matrix.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = (smoothEndpointKrausAdjoint K (1 : CMatrix b)) i j := by
          simp [smoothEndpointKrausAdjoint, Matrix.mul_apply,
            Matrix.conjTranspose_apply]

theorem smoothEndpointKrausStack_contraction_of_traceNonincreasing
    (K : κ → Matrix b a ℂ)
    (hTNI : IsTraceNonincreasing (ofKraus K)) :
    Matrix.conjTranspose (smoothEndpointKrausStack K) *
        smoothEndpointKrausStack K ≤ (1 : CMatrix a) := by
  rw [smoothEndpointKrausStack_conjTranspose_mul]
  exact smoothEndpointKrausAdjoint_one_le_of_traceNonincreasing K hTNI

end MatrixMap

namespace State

variable {c : Type*} [Fintype c] [DecidableEq c]

noncomputable local instance cMatrixCStarAlgebra : CStarAlgebra (CMatrix a) := {}

local instance cMatrixNormedSpaceReal : NormedSpace ℝ (CMatrix b) :=
  inferInstance

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule
attribute [local instance 1001] PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-! ## Elementary state bounds and maximally mixed side states -/

/-- Every normalized finite-dimensional state is bounded above by the identity
operator. -/
theorem matrix_le_one (ρ : State a) :
    ρ.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := ρ.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : ρ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.1.spectral_theorem
  have heig_sum : ∑ i, ρ.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact ρ.pos.1.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, ρ.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ ρ.pos.1.eigenvalues j :=
      ρ.pos.eigenvalues_nonneg j
    calc ρ.pos.1.eigenvalues i
        ≤ ρ.pos.1.eigenvalues i +
            ∑ j ∈ Finset.univ.erase i, ρ.pos.1.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, ρ.pos.1.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - ρ.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - ρ.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - ρ.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

theorem sqrtMatrix_trace_re_pos [Nonempty a] (ρ : State a) :
    0 < ρ.sqrtMatrix.trace.re := by
  have hnon : 0 ≤ ρ.sqrtMatrix.trace.re :=
    (Matrix.PosSemidef.trace_nonneg ρ.sqrtMatrix_pos).1
  by_contra hnot
  have hle : ρ.sqrtMatrix.trace.re ≤ 0 := le_of_not_gt hnot
  have hre : ρ.sqrtMatrix.trace.re = 0 := le_antisymm hle hnon
  have htr : ρ.sqrtMatrix.trace = 0 := by
    apply Complex.ext
    · exact hre
    · exact (Matrix.PosSemidef.trace_nonneg ρ.sqrtMatrix_pos).2.symm
  have hsqrt_zero : ρ.sqrtMatrix = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff ρ.sqrtMatrix_pos).mp htr
  have hrho_zero : ρ.matrix = 0 := by
    rw [← ρ.sqrtMatrix_mul_self, hsqrt_zero]
    simp
  have htrace : (ρ.matrix.trace : ℂ) = 0 := by simp [hrho_zero]
  rw [ρ.trace_eq_one] at htrace
  norm_num at htrace

omit [DecidableEq a] in theorem trace_re_le_of_le {X Y : CMatrix a} (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have hnon : 0 ≤ (Y - X).trace.re := (Matrix.PosSemidef.trace_nonneg hXY).1
  have htrace : (Y - X).trace.re = Y.trace.re - X.trace.re := by
    simp [Matrix.trace_sub]
  linarith

/-- A positive semidefinite finite matrix is bounded above by its trace times the
identity. -/
theorem posSemidef_le_trace_re_smul_one {A : CMatrix a} (hA : A.PosSemidef) :
    A ≤ (((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := hA.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : A = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hA.1.spectral_theorem
  have heig_sum : ∑ i, hA.1.eigenvalues i = A.trace.re := by
    have hc : A.trace = ∑ i, ((hA.1.eigenvalues i : ℝ) : ℂ) := by
      exact hA.1.trace_eq_sum_eigenvalues
    have hre := congrArg Complex.re hc
    simpa using hre.symm
  have heig_le_trace : ∀ i, hA.1.eigenvalues i ≤ A.trace.re := by
    intro i
    have hnonneg (j : a) : 0 ≤ hA.1.eigenvalues j := hA.eigenvalues_nonneg j
    calc hA.1.eigenvalues i
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
      c • (1 : CMatrix a) - A =
        (U : CMatrix a) * (c • (1 : CMatrix a) - D) * star (U : CMatrix a) := by
    have hunit_scalar :
        (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) =
          c • (1 : CMatrix a) := by
      have hunit : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
        simp
      calc
        (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) =
            c • ((U : CMatrix a) * (1 : CMatrix a) * star (U : CMatrix a)) := by
          simp
        _ = c • (1 : CMatrix a) := by
          simp [hunit]
    calc
      c • (1 : CMatrix a) - A =
          c • (1 : CMatrix a) - (U : CMatrix a) * D * star (U : CMatrix a) := by
        rw [hdiag]
      _ = (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
        rw [hunit_scalar]
      _ = (U : CMatrix a) * (c • (1 : CMatrix a) - D) * star (U : CMatrix a) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
  have hdiag_sub :
      c • (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((A.trace.re - hA.1.eigenvalues i : ℝ) : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D, c]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast sub_nonneg.mpr (heig_le_trace i)

/-- The operator norm of a PSD matrix is controlled by its trace. -/
theorem norm_le_trace_re_mul_norm_one_of_posSemidef {A : CMatrix a} (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace.re * ‖(1 : CMatrix a)‖ := by
  have hA0 : (0 : CMatrix a) ≤ A := by
    simpa [Matrix.le_iff] using hA
  have hle := posSemidef_le_trace_re_smul_one (a := a) hA
  have hnorm :
      ‖A‖ ≤ ‖(((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a))‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (A := CMatrix a) (a := A)
      (b := (((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a))) hA0 hle
  calc
    ‖A‖ ≤ ‖(((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a))‖ := hnorm
    _ = A.trace.re * ‖(1 : CMatrix a)‖ := by
      rw [norm_smul]
      have htr_nonneg : 0 ≤ A.trace.re := (Matrix.PosSemidef.trace_nonneg hA).1
      rw [Complex.norm_of_nonneg htr_nonneg]

/-- The maximally mixed state on a nonempty finite system. -/
def maximallyMixed (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a] : State a where
  matrix := (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix a)
  pos := by
    have hscalar : (0 : ℂ) ≤ (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card a : ℕ))
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one hscalar
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    have hcard : (Fintype.card a : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    norm_num [hcard]

@[simp]
theorem maximallyMixed_matrix [Nonempty a] :
    (maximallyMixed a).matrix =
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix a) :=
  rfl

omit [Fintype a] in theorem identityTensorStateMatrix_maximallyMixed [Nonempty b] :
    identityTensorStateMatrix (a := a) (maximallyMixed b) =
      ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix (Prod a b))) := by
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [identityTensorStateMatrix, maximallyMixed, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, h1, h2]

theorem identityTensorStateMatrix_trace_re (σ : State b) :
    (identityTensorStateMatrix (a := a) σ).trace.re = (Fintype.card a : ℝ) := by
  change (Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) σ.matrix).trace.re =
    (Fintype.card a : ℝ)
  rw [Matrix.trace_kronecker, σ.trace_eq_one, Matrix.trace_one]
  norm_num

omit [DecidableEq b] in theorem rpow_two_log2_card [Nonempty b] :
    Real.rpow 2 (log2 (Fintype.card b : ℝ)) = (Fintype.card b : ℝ) := by
  have hcard_pos : 0 < (Fintype.card b : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold log2
  have harg : Real.log 2 * (Real.log (Fintype.card b : ℝ) / Real.log 2) =
      Real.log (Fintype.card b : ℝ) := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog2]
  calc
    Real.rpow 2 (Real.log (Fintype.card b : ℝ) / Real.log 2)
        = Real.exp (Real.log 2 * (Real.log (Fintype.card b : ℝ) / Real.log 2)) := by
          exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _
    _ = Real.exp (Real.log (Fintype.card b : ℝ)) := by rw [harg]
    _ = (Fintype.card b : ℝ) := Real.exp_log hcard_pos

/-! ## Conditional max-entropy exponent -/

/-- The raw squared-fidelity expression optimized by conditional max-entropy,
before applying `log₂`. -/
def conditionalMaxEntropyExponentCandidate (ρ : State (Prod a b)) (σ : State b) :
    ℝ :=
  (traceNorm (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2

@[simp]
theorem conditionalMaxEntropyExponentCandidate_eq
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate σ =
      (traceNorm (ρ.sqrtMatrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 :=
  rfl

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²`. -/
def conditionalMaxEntropyExponentValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : State b,
    x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²`. -/
def conditionalMaxEntropyExponent (ρ : State (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyExponentValueSet (a := a))

@[simp]
theorem conditionalMaxEntropyExponent_eq (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponent =
      sSup (ρ.conditionalMaxEntropyExponentValueSet (a := a)) :=
  rfl

/-- The existing conditional max-entropy candidate is the logarithm of the raw
endpoint candidate. -/
theorem conditionalMaxEntropyCandidate_eq_log2_exponentCandidate
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyCandidate σ =
      log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) :=
  rfl

theorem conditionalMaxEntropyExponentCandidate_nonneg
    (ρ : State (Prod a b)) (σ : State b) :
    0 ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  exact sq_nonneg _

theorem conditionalMaxEntropyExponentCandidate_maximallyMixed_pos
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) (maximallyMixed b) := by
  let c : ℝ := (Fintype.card b : ℝ)⁻¹
  have hc_nonneg : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hc_pos : 0 < Real.sqrt c := by
    have hcard_pos : 0 < (Fintype.card b : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact Real.sqrt_pos.mpr (inv_pos.mpr hcard_pos)
  have hsqrt_id :
      psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b)) =
        (((Real.sqrt c : ℝ) : ℂ) • (1 : CMatrix (Prod a b))) := by
    rw [identityTensorStateMatrix_maximallyMixed (a := a) (b := b)]
    exact psdSqrt_real_smul_one (a := Prod a b) hc_nonneg
  have htrace_eq :
      (ρ.sqrtMatrix *
          psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b))).trace =
        ((Real.sqrt c : ℝ) : ℂ) * ρ.sqrtMatrix.trace := by
    rw [hsqrt_id]
    simp [Matrix.trace_smul]
  have htrace_abs_pos :
      0 < Complex.abs ((ρ.sqrtMatrix *
          psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b))).trace) := by
    rw [htrace_eq]
    change 0 < ‖((Real.sqrt c : ℝ) : ℂ) * ρ.sqrtMatrix.trace‖
    rw [norm_mul]
    have htr_ne : ρ.sqrtMatrix.trace ≠ 0 := by
      intro hzero
      have hre : ρ.sqrtMatrix.trace.re = 0 := by rw [hzero]; rfl
      have hpos : 0 < ρ.sqrtMatrix.trace.re := ρ.sqrtMatrix_trace_re_pos
      linarith
    have hc_ne : (((Real.sqrt c : ℝ) : ℂ) : ℂ) ≠ 0 := by
      exact_mod_cast hc_pos.ne'
    exact mul_pos (norm_pos_iff.mpr hc_ne) (norm_pos_iff.mpr htr_ne)
  have htn_pos :
      0 < traceNorm (ρ.sqrtMatrix *
        psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b))) :=
    lt_of_lt_of_le htrace_abs_pos (trace_abs_le_traceNorm _)
  unfold conditionalMaxEntropyExponentCandidate
  exact sq_pos_of_pos htn_pos

theorem identityTensorStateMatrix_posSemidef (σ : State b) :
    (identityTensorStateMatrix (a := a) σ).PosSemidef := by
  change (Matrix.kronecker (1 : CMatrix a) σ.matrix).PosSemidef
  exact Matrix.PosSemidef.one.kronecker σ.pos

theorem psdSqrt_identityTensorStateMatrix (σ : State b) :
    psdSqrt (identityTensorStateMatrix (a := a) σ) =
      Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix := by
  change psdSqrt (Matrix.kronecker (1 : CMatrix a) σ.matrix) =
    Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix
  rw [psdSqrt_kronecker Matrix.PosSemidef.one σ.pos]
  have hone : psdSqrt (1 : CMatrix a) = (1 : CMatrix a) := by
    simpa using (psdSqrt_real_smul_one (a := a) (r := 1) (by norm_num))
  rw [hone]
  simp [State.sqrtMatrix]

theorem maximallyMixed_sqrtMatrix [Nonempty a] :
    (maximallyMixed a).sqrtMatrix =
      (((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
        (1 : CMatrix a)) := by
  rw [State.sqrtMatrix, maximallyMixed_matrix]
  exact psdSqrt_real_smul_one (a := a)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem maximallyMixed_prod_sqrtMatrix [Nonempty a] (σ : State b) :
    ((maximallyMixed a).prod σ).sqrtMatrix =
      ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
        Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix := by
  rw [State.sqrtMatrix, State.prod]
  rw [psdSqrt_kronecker (maximallyMixed a).pos σ.pos]
  change Matrix.kronecker ((maximallyMixed a).sqrtMatrix) (σ.sqrtMatrix) =
    ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
      Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix
  rw [maximallyMixed_sqrtMatrix (a := a)]
  ext x y
  simp [Matrix.kroneckerMap_apply, mul_assoc]

theorem sqrt_identityTensorStateMatrix_eq_sqrt_card_smul_maximallyMixed_prod_sqrtMatrix
    [Nonempty a] (σ : State b) :
    Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ) •
        ((maximallyMixed a).prod σ).sqrtMatrix) := by
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hreal :
      Real.sqrt (Fintype.card a : ℝ) *
          Real.sqrt ((Fintype.card a : ℝ)⁻¹) = 1 := by
    rw [← Real.sqrt_mul (le_of_lt hcard_pos)]
    rw [mul_inv_cancel₀ hcard_pos.ne', Real.sqrt_one]
  rw [maximallyMixed_prod_sqrtMatrix (a := a) σ]
  ext x y
  simp [Matrix.kroneckerMap_apply]

theorem identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod
    [Nonempty a] (σ : State b) :
    identityTensorStateMatrix (a := a) σ =
      ((Fintype.card a : ℂ) • ((maximallyMixed a).prod σ).matrix) := by
  have hcard_ne : (Fintype.card a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  ext x y
  simp [identityTensorStateMatrix, State.prod, maximallyMixed_matrix, hcard_ne,
    Matrix.kroneckerMap_apply, mul_assoc]

theorem conditionalMaxEntropyExponentCandidate_eq_sqrt_identity
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ =
      (traceNorm (ρ.sqrtMatrix *
        Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix)) ^ 2 := by
  rw [conditionalMaxEntropyExponentCandidate_eq,
    psdSqrt_identityTensorStateMatrix (a := a) σ]

theorem conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
    [Nonempty a] (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ =
      (Fintype.card a : ℝ) *
        ρ.squaredFidelity ((maximallyMixed a).prod σ) := by
  let d : ℝ := Fintype.card a
  let M : CMatrix (Prod a b) :=
    ρ.sqrtMatrix * ((maximallyMixed a).prod σ).sqrtMatrix
  have hd_nonneg : 0 ≤ d := Nat.cast_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsqrt_sq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd_nonneg
  have hrewrite :
      ρ.sqrtMatrix * Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
        (((Real.sqrt d : ℝ) : ℂ) • M) := by
    have hsqrt :
        Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
          (((Real.sqrt d : ℝ) : ℂ) • ((maximallyMixed a).prod σ).sqrtMatrix) := by
      dsimp [d]
      exact sqrt_identityTensorStateMatrix_eq_sqrt_card_smul_maximallyMixed_prod_sqrtMatrix
        (a := a) σ
    calc
      ρ.sqrtMatrix * Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
          ρ.sqrtMatrix *
            (((Real.sqrt d : ℝ) : ℂ) • ((maximallyMixed a).prod σ).sqrtMatrix) := by
            rw [hsqrt]
      _ = (((Real.sqrt d : ℝ) : ℂ) • M) := by
            dsimp [M]
            rw [Matrix.mul_smul]
  rw [conditionalMaxEntropyExponentCandidate_eq_sqrt_identity]
  rw [hrewrite]
  rw [traceNorm_real_smul_eq hsqrt_nonneg M]
  rw [State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  dsimp [M, d]
  let t : ℝ := traceNorm (ρ.sqrtMatrix * ((maximallyMixed a).prod σ).sqrtMatrix)
  change (Real.sqrt (Fintype.card a : ℝ) * t) ^ 2 =
    (Fintype.card a : ℝ) * t ^ 2
  nlinarith [hsqrt_sq]

theorem conditionalMaxEntropy_hilbertSchmidt_trace_le
    (ρ : State (Prod a b)) (σ : State b) :
    ((star (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ)) *
        (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ))).trace).re ≤
      (Fintype.card a : ℝ) := by
  let S : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let T : CMatrix (Prod a b) := psdSqrt S
  have hSpos : S.PosSemidef := identityTensorStateMatrix_posSemidef (a := a) σ
  have hTstar : star T = T := (psdSqrt_isHermitian S).eq
  have hle : star T * ρ.matrix * T ≤ star T * (1 : CMatrix (Prod a b)) * T :=
    star_left_conjugate_le_conjugate (ρ.matrix_le_one) T
  have hleft_eq :
      star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T) = star T * ρ.matrix * T := by
    calc
      star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T)
          = Tᴴ * (ρ.sqrtMatrix * (ρ.sqrtMatrix * T)) := by
              simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
                ρ.sqrtMatrix_isHermitian.eq, Matrix.mul_assoc]
      _ = Tᴴ * ((ρ.sqrtMatrix * ρ.sqrtMatrix) * T) := by rw [Matrix.mul_assoc]
      _ = Tᴴ * (ρ.matrix * T) := by rw [ρ.sqrtMatrix_mul_self]
      _ = star T * ρ.matrix * T := by
          simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hright_eq : star T * (1 : CMatrix (Prod a b)) * T = S := by
    rw [hTstar]
    simp [T, psdSqrt_mul_self_of_posSemidef hSpos]
  have htrace_le := trace_re_le_of_le hle
  rw [hright_eq] at htrace_le
  change (star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T)).trace.re ≤
    (Fintype.card a : ℝ)
  rw [hleft_eq]
  exact htrace_le.trans_eq (identityTensorStateMatrix_trace_re (a := a) σ)

theorem conditionalMaxEntropyExponentCandidate_le_card
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤
      (Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ) := by
  let M : CMatrix (Prod a b) :=
    ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ)
  have hhs : ((star M * M).trace).re ≤ (Fintype.card a : ℝ) :=
    conditionalMaxEntropy_hilbertSchmidt_trace_le (a := a) ρ σ
  have htn := traceNorm_sq_le_card_mul_hilbertSchmidt M
  unfold conditionalMaxEntropyExponentCandidate
  change traceNorm M ^ 2 ≤ (Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ)
  exact htn.trans (mul_le_mul_of_nonneg_left hhs (Nat.cast_nonneg _))

/-- The definition-level conditional max-entropy candidate set.

It filters out zero endpoint exponents before applying `log₂`, matching the
finite-real-valued convention used by `State.conditionalMaxEntropy`: this is the
real-valued replacement for the usual extended-real convention `log 0 = -∞`. -/
def conditionalMaxEntropyValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {h : ℝ | ∃ σ : State b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = conditionalMaxEntropyCandidate (a := a) ρ σ}

@[simp]
theorem conditionalMaxEntropyValueSet_eq (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyValueSet (a := a) =
      {h : ℝ | ∃ σ : State b,
        0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
          h = conditionalMaxEntropyCandidate (a := a) ρ σ} :=
  rfl

theorem conditionalMaxEntropy_eq_sSup_valueSet (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropy =
      sSup (ρ.conditionalMaxEntropyValueSet (a := a)) := by
  rfl

theorem conditionalMaxEntropyValueSet_nonempty [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyCandidate (a := a) (maximallyMixed b),
    maximallyMixed b, ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos
      (a := a), rfl⟩

theorem conditionalMaxEntropyCandidate_le_log2_card_bound
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyCandidate (a := a) σ ≤
      max 0 (log2 ((Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ))) := by
  by_cases hpos : 0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ
  · have hle := ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ
    have hbound_pos :
        0 < (Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ) := by
      have hprod : 0 < (Fintype.card (Prod a b) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨Classical.arbitrary (Prod a b)⟩
      have ha : 0 < (Fintype.card a : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨Classical.arbitrary a⟩
      exact mul_pos hprod ha
    have hlog :
        log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) ≤
          log2 ((Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ)) := by
      unfold log2
      exact div_le_div_of_nonneg_right (Real.log_le_log hpos hle)
        (le_of_lt (Real.log_pos one_lt_two))
    rw [conditionalMaxEntropyCandidate_eq_log2_exponentCandidate]
    exact hlog.trans (le_max_right _ _)
  · have hzero : ρ.conditionalMaxEntropyExponentCandidate (a := a) σ = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        (ρ.conditionalMaxEntropyExponentCandidate_nonneg (a := a) σ)
    rw [conditionalMaxEntropyCandidate_eq_log2_exponentCandidate, hzero]
    simp [log2]

theorem conditionalMaxEntropyValueSet_bddAbove [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyValueSet (a := a)) := by
  refine ⟨max 0 (log2 ((Fintype.card (Prod a b) : ℝ) *
    (Fintype.card a : ℝ))), ?_⟩
  intro h hh
  rcases hh with ⟨σ, _hpos, rfl⟩
  exact ρ.conditionalMaxEntropyCandidate_le_log2_card_bound (a := a) σ

/-- The normalized fidelity form of the conditional max-entropy endpoint
optimization:
`{F(ρ_AB, π_A ⊗ σ_B)^2 | σ_B}`. -/
def conditionalMaxEntropyFidelityValueSet [Nonempty a]
    (ρ : State (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : State b,
    x = ρ.squaredFidelity ((maximallyMixed a).prod σ)}

theorem conditionalMaxEntropyFidelityValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyFidelityValueSet (a := a)).Nonempty :=
  ⟨ρ.squaredFidelity ((maximallyMixed a).prod (maximallyMixed b)),
    maximallyMixed b, rfl⟩

theorem conditionalMaxEntropyFidelityValueSet_bddAbove
    [Nonempty a] (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  refine ⟨(Fintype.card (Prod a b) : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hle := conditionalMaxEntropyExponentCandidate_le_card
    (a := a) ρ σ
  rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
    (a := a) ρ σ] at hle
  nlinarith

/-! ### Block-SDP surface for the fidelity endpoint -/

/-- Block-matrix feasibility for the finite-dimensional fidelity SDP:
`[[ρ_AB, X], [X†, π_A ⊗ σ_B]] ≥ 0`.

This is the primal block-cone side that will later be dualized against the
conditional-min scale. -/
def ConditionalMaxFidelityBlockFeasible [Nonempty a]
    (ρ : State (Prod a b)) (σ : State b) (X : CMatrix (Prod a b)) : Prop :=
  (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
      CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef

@[simp]
theorem ConditionalMaxFidelityBlockFeasible_eq [Nonempty a]
    (ρ : State (Prod a b)) (σ : State b) (X : CMatrix (Prod a b)) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ↔
      (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
        CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef :=
  Iff.rfl

/-- The linear objective in the fidelity block SDP.  The squared endpoint value
uses this quantity squared. -/
def conditionalMaxFidelityBlockValue (X : CMatrix (Prod a b)) : ℝ :=
  X.trace.re

omit [DecidableEq a] [DecidableEq b] in
@[simp]
theorem conditionalMaxFidelityBlockValue_eq (X : CMatrix (Prod a b)) :
    conditionalMaxFidelityBlockValue X = X.trace.re :=
  rfl

/-- The max-entropy endpoint value represented through a feasible block SDP
candidate. -/
def conditionalMaxFidelityBlockExponentValue [Nonempty a]
    (X : CMatrix (Prod a b)) : ℝ :=
  (Fintype.card a : ℝ) * (conditionalMaxFidelityBlockValue X) ^ 2

omit [DecidableEq a] [DecidableEq b] in
@[simp]
theorem conditionalMaxFidelityBlockExponentValue_eq [Nonempty a]
    (X : CMatrix (Prod a b)) :
    conditionalMaxFidelityBlockExponentValue (a := a) X =
      (Fintype.card a : ℝ) * X.trace.re ^ 2 :=
  rfl

/-- Zero off-diagonal block feasibility.  This proves the block SDP surface is
nonempty without using any fidelity or duality theorem. -/
theorem ConditionalMaxFidelityBlockFeasible_zero [Nonempty a]
    (ρ : State (Prod a b)) (σ : State b) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ 0 := by
  simpa [ConditionalMaxFidelityBlockFeasible] using
    cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) ρ.pos
      (((maximallyMixed a).prod σ).pos)

private def scaledBlockEmbeddingMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (t : ℝ) : Matrix (Sum α α) α ℂ :=
  fun x y =>
    match x with
    | Sum.inl i => if i = y then (Real.sqrt t : ℂ) else 0
    | Sum.inr i => if i = y then 1 else 0

private theorem scaledBlockEmbeddingMatrix_mul_pos_mul_conjTranspose
    {α : Type*} [Fintype α] [DecidableEq α]
    {τ : CMatrix α} (hτ : τ.PosSemidef) (t : ℝ) :
    (scaledBlockEmbeddingMatrix (α := α) t * τ *
      (scaledBlockEmbeddingMatrix (α := α) t)ᴴ).PosSemidef := by
  exact hτ.mul_mul_conjTranspose_same (scaledBlockEmbeddingMatrix (α := α) t)

private theorem scaledBlockEmbeddingMatrix_block_eq {α : Type*}
    [Fintype α] [DecidableEq α] {τ : CMatrix α} {t : ℝ} (ht : 0 ≤ t) :
    scaledBlockEmbeddingMatrix (α := α) t * τ *
      (scaledBlockEmbeddingMatrix (α := α) t)ᴴ =
        (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ : CMatrix (Sum α α)) := by
  classical
  ext x y
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]
          rw [Finset.sum_eq_single j]
          · simp
            ring_nf
            rw [← Complex.ofReal_pow]
            rw [Real.sq_sqrt ht]
            ring
          · intro x _ hx
            have hx' : ¬ j = x := by intro h; exact hx h.symm
            simp [hx']
          · intro hnot
            simp at hnot
      | inr j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]
  | inr i =>
      cases y with
      | inl j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]
          rw [Finset.sum_eq_single j]
          · simp
            ring
          · intro x _ hx
            have hx' : ¬ j = x := by intro h; exact hx h.symm
            simp [hx']
          · intro hnot
            simp at hnot
      | inr j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]

theorem ConditionalMaxFidelityBlockFeasible.of_scaled_le [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {t : ℝ} (ht : 0 ≤ t)
    (hle : (((t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix) ≤ ρ.matrix) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ
      ((((Real.sqrt t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix)) := by
  classical
  let τ : CMatrix (Prod a b) := ((maximallyMixed a).prod σ).matrix
  have hdiff : (ρ.matrix - (((t : ℝ) : ℂ) • τ)).PosSemidef := by
    simpa [τ, Matrix.le_iff] using hle
  have hdiag :
      (Matrix.fromBlocks (ρ.matrix - (((t : ℝ) : ℂ) • τ)) 0 0
        (0 : CMatrix (Prod a b)) :
        CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef := by
    exact cMatrix_fromBlocks_diagonal_posSemidef hdiff Matrix.PosSemidef.zero
  have hrank :
      (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ :
          CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef := by
    rw [← scaledBlockEmbeddingMatrix_block_eq (α := Prod a b) (τ := τ) ht]
    exact scaledBlockEmbeddingMatrix_mul_pos_mul_conjTranspose
      ((maximallyMixed a).prod σ).pos t
  have hsum :
      (Matrix.fromBlocks ρ.matrix
          ((((Real.sqrt t : ℝ) : ℂ) • τ))
          (Matrix.conjTranspose ((((Real.sqrt t : ℝ) : ℂ) • τ)))
          τ :
          CMatrix (Sum (Prod a b) (Prod a b))) =
        (Matrix.fromBlocks (ρ.matrix - (((t : ℝ) : ℂ) • τ)) 0 0
          (0 : CMatrix (Prod a b)) :
          CMatrix (Sum (Prod a b) (Prod a b))) +
        (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ :
          CMatrix (Sum (Prod a b) (Prod a b))) := by
    ext x y
    cases x <;> cases y <;>
      simp [τ, Matrix.fromBlocks, Matrix.of_apply,
        Matrix.conjTranspose_smul, ((maximallyMixed a).prod σ).pos.isHermitian.eq]
  rw [ConditionalMaxFidelityBlockFeasible]
  change (Matrix.fromBlocks ρ.matrix
    ((((Real.sqrt t : ℝ) : ℂ) • τ))
    (Matrix.conjTranspose ((((Real.sqrt t : ℝ) : ℂ) • τ)))
    τ : CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef
  rw [hsum]
  exact hdiag.add hrank

theorem ConditionalMaxFidelityBlockFeasible.of_scaled_le_blockExponentValue [Nonempty a]
    {σ : State b} {t : ℝ} (ht : 0 ≤ t) :
    conditionalMaxFidelityBlockExponentValue (a := a)
        ((((Real.sqrt t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix)) =
      (Fintype.card a : ℝ) * t := by
  have htrace :
      (((((Real.sqrt t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix)).trace).re =
        Real.sqrt t := by
    rw [Matrix.trace_smul, ((maximallyMixed a).prod σ).trace_eq_one]
    simp
  rw [conditionalMaxFidelityBlockExponentValue_eq, htrace]
  rw [Real.sq_sqrt ht]

/-! ### Block-SDP feasible points are fidelity-bounded -/

private def pureVectorOfAmplitudeMatrix {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Aᴴ).trace = 1) :
    PureVector (Prod r α) where
  amp := fun x => A x.2 x.1
  trace_rankOne_eq_one := by
    classical
    calc
      (rankOneMatrix (fun x : Prod r α => A x.2 x.1)).trace =
          ∑ x : Prod r α, A x.2 x.1 * star (A x.2 x.1) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ i : α, ∑ j : r, A i j * star (A i j) := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
      _ = (A * Aᴴ).trace := by
            simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = 1 := htrace

@[simp]
private theorem pureVectorOfAmplitudeMatrix_amplitudeMatrix {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Aᴴ).trace = 1) :
    (pureVectorOfAmplitudeMatrix A htrace).amplitudeMatrix = A := by
  rfl

private theorem pureVectorOfAmplitudeMatrix_purifies {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {A : Matrix α r ℂ} {ρ : State α}
    (hgram : A * Aᴴ = ρ.matrix) (htrace : (A * Aᴴ).trace = 1) :
    (pureVectorOfAmplitudeMatrix A htrace).Purifies ρ := by
  rw [PureVector.purifies_iff]
  rw [PureVector.state_matrix]
  rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  simpa [pureVectorOfAmplitudeMatrix_amplitudeMatrix] using hgram

private def pureVectorNormalize {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) : PureVector α where
  amp := fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x
  trace_rankOne_eq_one := by
    classical
    let t : ℝ := (rankOneMatrix v).trace.re
    have htpos : 0 < t := hpos
    have ht_nonneg : 0 ≤ t := le_of_lt htpos
    have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
    have htrace_im : (rankOneMatrix v).trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).2.symm
    have htrace_complex : (rankOneMatrix v).trace = (t : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using htrace_im
    have hcoeff :
        (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    calc
      (rankOneMatrix
          (fun x => ((((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x))).trace =
          (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (rankOneMatrix v).trace) := by
            simp [rankOneMatrix_trace, dotProduct, t, Finset.mul_sum, mul_assoc,
              mul_left_comm, mul_comm]
      _ = (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) := by
            rw [htrace_complex]
      _ = 1 := hcoeff

@[simp]
private theorem pureVectorNormalize_amp {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) :
    (pureVectorNormalize v hpos).amp =
      fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x :=
  rfl

private def maxEntangledSideAmplitude {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a]
    (η : PureVector (Prod r b)) : Matrix (Prod a b) (Prod r a) ℂ :=
  fun x y =>
    (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
      (if y.2 = x.1 then η.amp (y.1, x.2) else 0)

private theorem maxEntangledSideAmplitude_gram {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : PureVector (Prod r b)) :
    maxEntangledSideAmplitude (a := a) η *
        (maxEntangledSideAmplitude (a := a) η)ᴴ =
      ((State.maximallyMixed a).prod η.state.marginalB).matrix := by
  classical
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  let s : ℂ := ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ)
  have hcoeff : s * s = (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← sq, Real.sq_sqrt]
    exact inv_nonneg.mpr (le_of_lt hcard_pos)
  have hcoeff' :
      (((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) *
          ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa [s] using hcoeff
  have hcoeff_inv_sqrt :
      (((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℝ) : ℂ) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hcard_pos)]
    rw [Real.sq_sqrt (le_of_lt hcard_pos)]
  have hcoeff_complex_inv :
      (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) *
          ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa [Complex.ofReal_inv] using hcoeff_inv_sqrt
  by_cases hxy : xa = ya
  · subst ya
    simp [maxEntangledSideAmplitude, Matrix.mul_apply, Matrix.conjTranspose_apply,
      State.prod, State.maximallyMixed, State.marginalB, partialTraceA,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum,
      Fintype.sum_prod_type,
      mul_assoc, mul_left_comm, mul_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, hcoeff_complex_inv]
    rw [Complex.ofReal_inv]
    norm_num
  · simp [maxEntangledSideAmplitude, Matrix.mul_apply, Matrix.conjTranspose_apply,
      State.prod, State.maximallyMixed, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, hxy]

private def maxEntangledSidePureVector {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : PureVector (Prod r b)) :
    PureVector (Prod (Prod r a) (Prod a b)) :=
  pureVectorOfAmplitudeMatrix (maxEntangledSideAmplitude (a := a) η) (by
    rw [maxEntangledSideAmplitude_gram]
    exact ((State.maximallyMixed a).prod η.state.marginalB).trace_eq_one)

private theorem maxEntangledSidePureVector_purifies {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : PureVector (Prod r b)) :
    (maxEntangledSidePureVector (a := a) η).Purifies
      ((State.maximallyMixed a).prod η.state.marginalB) := by
  exact pureVectorOfAmplitudeMatrix_purifies
    (maxEntangledSideAmplitude_gram (a := a) η)
    (by
      rw [maxEntangledSideAmplitude_gram]
      exact ((State.maximallyMixed a).prod η.state.marginalB).trace_eq_one)

private def blockSqrtTopRow {α : Type*} [Fintype α] [DecidableEq α]
    (S : CMatrix (Sum α α)) : Matrix α (Sum α α) ℂ :=
  fun i j => S (Sum.inl i) j

private def blockSqrtBottomRow {α : Type*} [Fintype α] [DecidableEq α]
    (S : CMatrix (Sum α α)) : Matrix α (Sum α α) ℂ :=
  fun i j => S (Sum.inr i) j

private theorem blockSqrtTopRow_mul_conjTranspose {α : Type*}
    [Fintype α] [DecidableEq α] (S : CMatrix (Sum α α)) (hS : S.IsHermitian) :
    blockSqrtTopRow S * (blockSqrtTopRow S)ᴴ = Matrix.sumBlock11 (S * S) := by
  classical
  ext i j
  simp only [blockSqrtTopRow, Matrix.sumBlock11_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : star (S (Sum.inl j) k) = S k (Sum.inl j) := by
    have h := congrFun (congrFun hS.eq k) (Sum.inl j)
    simpa [Matrix.conjTranspose_apply] using h
  rw [hk]

private theorem blockSqrtBottomRow_mul_conjTranspose {α : Type*}
    [Fintype α] [DecidableEq α] (S : CMatrix (Sum α α)) (hS : S.IsHermitian) :
    blockSqrtBottomRow S * (blockSqrtBottomRow S)ᴴ = Matrix.sumBlock22 (S * S) := by
  classical
  ext i j
  simp only [blockSqrtBottomRow, Matrix.sumBlock22_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : star (S (Sum.inr j) k) = S k (Sum.inr j) := by
    have h := congrFun (congrFun hS.eq k) (Sum.inr j)
    simpa [Matrix.conjTranspose_apply] using h
  rw [hk]

private theorem blockSqrtTopRow_mul_bottomRow_conjTranspose {α : Type*}
    [Fintype α] [DecidableEq α] (S : CMatrix (Sum α α)) (hS : S.IsHermitian) :
    blockSqrtTopRow S * (blockSqrtBottomRow S)ᴴ = Matrix.sumBlock12 (S * S) := by
  classical
  ext i j
  simp only [blockSqrtTopRow, blockSqrtBottomRow, Matrix.sumBlock12_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : star (S (Sum.inr j) k) = S k (Sum.inr j) := by
    have h := congrFun (congrFun hS.eq k) (Sum.inr j)
    simpa [Matrix.conjTranspose_apply] using h
  rw [hk]

private theorem pureVector_abs_overlap_le_fidelity {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {Ψ Φ : PureVector (Prod r α)} {ρ σ : State α}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies σ) :
    Complex.abs (Ψ.overlap Φ) ≤ ρ.fidelity σ := by
  have hsq := PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ
  rw [PureVector.overlapSq_eq_normSq, State.squaredFidelity_eq_fidelity_sq] at hsq
  have hleft_nonneg : 0 ≤ Complex.abs (Ψ.overlap Φ) := norm_nonneg _
  have hfid_nonneg : 0 ≤ ρ.fidelity σ := traceNorm_nonneg _
  rw [Complex.normSq_eq_norm_sq] at hsq
  exact (sq_le_sq₀ hleft_nonneg hfid_nonneg).mp hsq

private theorem abs_trace_eq_abs_overlap_of_amplitude_gram {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {A B : Matrix α r ℂ} {X : CMatrix α}
    (hX : A * Bᴴ = X) {hAtrace : (A * Aᴴ).trace = 1}
    {hBtrace : (B * Bᴴ).trace = 1} :
    Complex.abs X.trace =
      Complex.abs ((pureVectorOfAmplitudeMatrix A hAtrace).overlap
        (pureVectorOfAmplitudeMatrix B hBtrace)) := by
  let Ψ := pureVectorOfAmplitudeMatrix A hAtrace
  let Φ := pureVectorOfAmplitudeMatrix B hBtrace
  have hoverlap :
      Ψ.overlap Φ = (Aᴴ * B).trace := by
    rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
    rfl
  have htrace_conj :
      X.trace = star ((Aᴴ * B).trace) := by
    calc
      X.trace = (A * Bᴴ).trace := by rw [← hX]
      _ = (Bᴴ * A).trace := by rw [Matrix.trace_mul_comm]
      _ = (Matrix.conjTranspose (Aᴴ * B)).trace := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = star ((Aᴴ * B).trace) := Matrix.trace_conjTranspose _
  rw [htrace_conj, hoverlap]
  simp

theorem ConditionalMaxFidelityBlockFeasible.abs_trace_le_fidelity [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    Complex.abs X.trace ≤ ρ.fidelity ((maximallyMixed a).prod σ) := by
  classical
  let α := Prod a b
  let τ : State α := (maximallyMixed a).prod σ
  let H : CMatrix (Sum α α) := Matrix.fromBlocks ρ.matrix X (star X) τ.matrix
  let S : CMatrix (Sum α α) := psdSqrt H
  let A : Matrix α (Sum α α) ℂ := blockSqrtTopRow S
  let B : Matrix α (Sum α α) ℂ := blockSqrtBottomRow S
  have hH : H.PosSemidef := hX
  have hS : S.IsHermitian := psdSqrt_isHermitian H
  have hSsq : S * S = H := psdSqrt_mul_self_of_posSemidef hH
  have hAgram : A * Aᴴ = ρ.matrix := by
    calc
      A * Aᴴ = Matrix.sumBlock11 (S * S) :=
        blockSqrtTopRow_mul_conjTranspose S hS
      _ = Matrix.sumBlock11 H := by rw [hSsq]
      _ = ρ.matrix := by rfl
  have hBgram : B * Bᴴ = τ.matrix := by
    calc
      B * Bᴴ = Matrix.sumBlock22 (S * S) :=
        blockSqrtBottomRow_mul_conjTranspose S hS
      _ = Matrix.sumBlock22 H := by rw [hSsq]
      _ = τ.matrix := by rfl
  have hAB : A * Bᴴ = X := by
    calc
      A * Bᴴ = Matrix.sumBlock12 (S * S) :=
        blockSqrtTopRow_mul_bottomRow_conjTranspose S hS
      _ = Matrix.sumBlock12 H := by rw [hSsq]
      _ = X := by rfl
  have hAtrace : (A * Aᴴ).trace = 1 := by
    rw [hAgram, ρ.trace_eq_one]
  have hBtrace : (B * Bᴴ).trace = 1 := by
    rw [hBgram, τ.trace_eq_one]
  let Ψ : PureVector (Prod (Sum α α) α) := pureVectorOfAmplitudeMatrix A hAtrace
  let Φ : PureVector (Prod (Sum α α) α) := pureVectorOfAmplitudeMatrix B hBtrace
  have hΨ : Ψ.Purifies ρ := pureVectorOfAmplitudeMatrix_purifies hAgram hAtrace
  have hΦ : Φ.Purifies τ := pureVectorOfAmplitudeMatrix_purifies hBgram hBtrace
  have habs :
      Complex.abs X.trace = Complex.abs (Ψ.overlap Φ) :=
    abs_trace_eq_abs_overlap_of_amplitude_gram hAB
  rw [habs]
  exact pureVector_abs_overlap_le_fidelity hΨ hΦ

theorem ConditionalMaxFidelityBlockFeasible.trace_re_le_fidelity [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    X.trace.re ≤ ρ.fidelity ((maximallyMixed a).prod σ) :=
  (Complex.re_le_norm X.trace).trans hX.abs_trace_le_fidelity

theorem ConditionalMaxFidelityBlockFeasible.blockValue_le_fidelity [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockValue X ≤
      ρ.fidelity ((maximallyMixed a).prod σ) := by
  simpa [conditionalMaxFidelityBlockValue] using hX.trace_re_le_fidelity

theorem ConditionalMaxFidelityBlockFeasible.blockExponentValue_le_exponentCandidate
    [Nonempty a] {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockExponentValue (a := a) X ≤
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  rw [conditionalMaxFidelityBlockExponentValue_eq,
    conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
    State.squaredFidelity_eq_fidelity_sq]
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by exact_mod_cast Nat.zero_le _
  have habs_sq :
      X.trace.re ^ 2 ≤ ρ.fidelity ((maximallyMixed a).prod σ) ^ 2 := by
    have hre_abs : |X.trace.re| ≤ Complex.abs X.trace :=
      Complex.abs_re_le_norm X.trace
    have hle_abs : |X.trace.re| ≤ ρ.fidelity ((maximallyMixed a).prod σ) :=
      hre_abs.trans hX.abs_trace_le_fidelity
    have hleft : 0 ≤ |X.trace.re| := abs_nonneg _
    have hright : 0 ≤ ρ.fidelity ((maximallyMixed a).prod σ) :=
      traceNorm_nonneg _
    have hsquare := (sq_le_sq₀ hleft hright).mpr hle_abs
    simpa [sq_abs] using hsquare
  exact mul_le_mul_of_nonneg_left habs_sq hcard_nonneg

/-- Unitary polar factors produce feasible points of the fidelity block SDP:
`X = √ρ U √(π_A ⊗ σ_B)`. -/
theorem ConditionalMaxFidelityBlockFeasible.of_unitary_sqrt [Nonempty a]
    (ρ : State (Prod a b)) (σ : State b)
    (U : Matrix.unitaryGroup (Prod a b) ℂ) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ
      (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) *
        ((maximallyMixed a).prod σ).sqrtMatrix) := by
  let τ : State (Prod a b) := (maximallyMixed a).prod σ
  let H : CMatrix (Sum (Prod a b) (Prod a b)) :=
    Matrix.fromBlocks (1 : CMatrix (Prod a b)) (U : CMatrix (Prod a b))
      (star (U : CMatrix (Prod a b))) 1
  let S : CMatrix (Sum (Prod a b) (Prod a b)) :=
    Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix
  have hH : H.PosSemidef := by
    simpa [H] using cMatrix_fromBlocks_unitary_posSemidef U
  have hconj : (S * H * star S).PosSemidef := by
    simpa [Matrix.mul_assoc] using hH.mul_mul_conjTranspose_same S
  have hEq :
      S * H * star S =
        (Matrix.fromBlocks ρ.matrix
          (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix)
          (star (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix))
          τ.matrix : CMatrix (Sum (Prod a b) (Prod a b))) := by
    have hρH : ρ.sqrtMatrixᴴ = ρ.sqrtMatrix := ρ.sqrtMatrix_isHermitian.eq
    have hτH : τ.sqrtMatrixᴴ = τ.sqrtMatrix := τ.sqrtMatrix_isHermitian.eq
    have hρsq : ρ.sqrtMatrix * ρ.sqrtMatrix = ρ.matrix := ρ.sqrtMatrix_mul_self
    have hτsq : τ.sqrtMatrix * τ.sqrtMatrix = τ.matrix := τ.sqrtMatrix_mul_self
    dsimp [S, H]
    change
      Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix *
          Matrix.fromBlocks (1 : CMatrix (Prod a b)) (U : CMatrix (Prod a b))
            (star (U : CMatrix (Prod a b))) 1 *
            (Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix)ᴴ =
        (Matrix.fromBlocks ρ.matrix
          (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix)
          (star (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix))
          τ.matrix :
          CMatrix (Sum (Prod a b) (Prod a b)))
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;>
      simp [hρH, hτH, hρsq, hτsq, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simpa [ConditionalMaxFidelityBlockFeasible, τ, hEq] using hconj

/-- The fidelity block constraint is invariant under a scalar phase rotation of
the off-diagonal block. -/
theorem ConditionalMaxFidelityBlockFeasible.smul_phase [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    {c : ℂ} (hc : c * star c = 1)
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ (c • X) := by
  let D : CMatrix (Sum (Prod a b) (Prod a b)) :=
    Matrix.fromBlocks (1 : CMatrix (Prod a b)) 0 0
      ((star c) • (1 : CMatrix (Prod a b)))
  have hc'' : c * (starRingEnd ℂ) c = 1 := by
    simpa using hc
  have hconj :
      (D *
          (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
            CMatrix (Sum (Prod a b) (Prod a b))) *
            star D).PosSemidef :=
    hX.mul_mul_conjTranspose_same D
  have hEq :
      D *
          (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
            CMatrix (Sum (Prod a b) (Prod a b))) *
            star D =
        (Matrix.fromBlocks ρ.matrix (c • X) (star (c • X))
          ((maximallyMixed a).prod σ).matrix :
          CMatrix (Sum (Prod a b) (Prod a b))) := by
    dsimp [D]
    simp_rw [Matrix.star_eq_conjTranspose]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [← mul_assoc, hc'']
  simpa [ConditionalMaxFidelityBlockFeasible, hEq] using hconj

/-- For each side state `σ_B`, the fidelity block SDP has a feasible point
whose absolute trace objective attains the root fidelity
`F(ρ_AB, π_A ⊗ σ_B)`. -/
theorem exists_ConditionalMaxFidelityBlockFeasible_abs_trace_eq_fidelity
    [Nonempty a] (ρ : State (Prod a b)) (σ : State b) :
    ∃ X : CMatrix (Prod a b),
      ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
        Complex.abs X.trace =
          ρ.fidelity ((maximallyMixed a).prod σ) := by
  let τ : State (Prod a b) := (maximallyMixed a).prod σ
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_unitary_abs_trace (τ.sqrtMatrix * ρ.sqrtMatrix)
  let X : CMatrix (Prod a b) := ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix
  refine ⟨X, ?_, ?_⟩
  · exact ConditionalMaxFidelityBlockFeasible.of_unitary_sqrt (a := a) ρ σ U
  · have htrace :
        X.trace = ((τ.sqrtMatrix * ρ.sqrtMatrix) * (U : CMatrix (Prod a b))).trace := by
      calc
        X.trace = ((ρ.sqrtMatrix * (U : CMatrix (Prod a b))) * τ.sqrtMatrix).trace := by
          simp [X, Matrix.mul_assoc]
        _ = (τ.sqrtMatrix * (ρ.sqrtMatrix * (U : CMatrix (Prod a b)))).trace := by
          rw [Matrix.trace_mul_comm]
        _ = ((τ.sqrtMatrix * ρ.sqrtMatrix) * (U : CMatrix (Prod a b))).trace := by
          rw [Matrix.mul_assoc]
    have hconj :
        τ.sqrtMatrix * ρ.sqrtMatrix =
          Matrix.conjTranspose (ρ.sqrtMatrix * τ.sqrtMatrix) := by
      rw [Matrix.conjTranspose_mul, ρ.sqrtMatrix_isHermitian.eq,
        τ.sqrtMatrix_isHermitian.eq]
    calc
      Complex.abs X.trace =
          Complex.abs (((τ.sqrtMatrix * ρ.sqrtMatrix) *
            (U : CMatrix (Prod a b))).trace) := by rw [htrace]
      _ = traceNorm (τ.sqrtMatrix * ρ.sqrtMatrix) := hU
      _ = traceNorm (ρ.sqrtMatrix * τ.sqrtMatrix) := by
        rw [hconj, traceNorm_conjTranspose]
      _ = ρ.fidelity τ := by rfl

/-- For each side state `σ_B`, the fidelity block SDP has a feasible point
whose real trace objective attains the root fidelity. -/
theorem exists_ConditionalMaxFidelityBlockFeasible_trace_re_eq_fidelity
    [Nonempty a] (ρ : State (Prod a b)) (σ : State b) :
    ∃ X : CMatrix (Prod a b),
      ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
        conditionalMaxFidelityBlockValue X =
          ρ.fidelity ((maximallyMixed a).prod σ) := by
  rcases exists_ConditionalMaxFidelityBlockFeasible_abs_trace_eq_fidelity
      (a := a) ρ σ with ⟨X, hX, hXtrace⟩
  rcases exists_complex_phase_mul_re_eq_abs X.trace with ⟨c, hc, hcTrace⟩
  refine ⟨c • X, ?_, ?_⟩
  · exact ConditionalMaxFidelityBlockFeasible.smul_phase (a := a) hc hX
  · have htrace : (c • X).trace = c * X.trace := by
      simp [Matrix.trace, Finset.mul_sum]
    calc
      conditionalMaxFidelityBlockValue (c • X) = (c * X.trace).re := by
        simp [conditionalMaxFidelityBlockValue, htrace]
      _ = Complex.abs X.trace := hcTrace
      _ = ρ.fidelity ((maximallyMixed a).prod σ) := hXtrace

/-- Feasible objective values for the block-SDP representation of the
conditional max-fidelity endpoint. -/
def conditionalMaxFidelityBlockValueSet [Nonempty a]
    (ρ : State (Prod a b)) : Set ℝ :=
  {v : ℝ | ∃ σ : State b, ∃ X : CMatrix (Prod a b),
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
      v = conditionalMaxFidelityBlockValue X}

/-- Squared and dimension-scaled feasible endpoint values for the block-SDP
representation. -/
def conditionalMaxFidelityBlockExponentValueSet [Nonempty a]
    (ρ : State (Prod a b)) : Set ℝ :=
  {v : ℝ | ∃ σ : State b, ∃ X : CMatrix (Prod a b),
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
      v = conditionalMaxFidelityBlockExponentValue (a := a) X}

/-- Every definition-level max-entropy exponent candidate is realized by the
block-SDP endpoint surface. -/
theorem conditionalMaxEntropyExponentValueSet_subset_conditionalMaxFidelityBlockExponentValueSet
    [Nonempty a] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponentValueSet (a := a) ⊆
      ρ.conditionalMaxFidelityBlockExponentValueSet (a := a) := by
  intro v hv
  rcases hv with ⟨σ, rfl⟩
  rcases ρ.exists_ConditionalMaxFidelityBlockFeasible_trace_re_eq_fidelity
      (a := a) σ with ⟨X, hX, hval⟩
  refine ⟨σ, X, hX, ?_⟩
  rw [conditionalMaxFidelityBlockExponentValue, hval]
  rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
    (a := a) ρ σ]
  rw [State.squaredFidelity_eq_fidelity_sq]

theorem conditionalMaxFidelityBlockValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxFidelityBlockValueSet (a := a)).Nonempty := by
  refine ⟨0, maximallyMixed b, 0, ?_, ?_⟩
  · exact ρ.ConditionalMaxFidelityBlockFeasible_zero (a := a) (maximallyMixed b)
  · simp [conditionalMaxFidelityBlockValue]

theorem conditionalMaxFidelityBlockExponentValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)).Nonempty := by
  refine ⟨0, maximallyMixed b, 0, ?_, ?_⟩
  · exact ρ.ConditionalMaxFidelityBlockFeasible_zero (a := a) (maximallyMixed b)
  · simp [conditionalMaxFidelityBlockExponentValue, conditionalMaxFidelityBlockValue]

theorem conditionalMaxEntropyExponentValueSet_eq_card_mul_fidelityValueSet
    [Nonempty a] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponentValueSet (a := a) =
      (fun x : ℝ => (Fintype.card a : ℝ) * x) ''
        ρ.conditionalMaxEntropyFidelityValueSet (a := a) := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨ρ.squaredFidelity ((maximallyMixed a).prod σ), ?_, ?_⟩
    · exact ⟨σ, rfl⟩
    · exact (conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
        (a := a) ρ σ
      ).symm
  · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    exact (conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
      (a := a) ρ σ).symm

theorem conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponent (a := a) =
      (Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  rw [conditionalMaxEntropyExponent, conditionalMaxEntropyExponentValueSet_eq_card_mul_fidelityValueSet
    (a := a) ρ]
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  exact mul_sSup_image_eq
    (ρ.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
    (ρ.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos

/-- Positive raw max-entropy exponent candidate values.

The positivity filter is mathematically necessary for transporting `log₂`
through `sSup`: with the repository convention `log 0 = 0`, zero candidates
cannot be kept in the logarithmic candidate set without changing the supremum. -/
def conditionalMaxEntropyPositiveExponentValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : State b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

/-- Definition-level max-entropy candidates whose raw exponent is strictly
positive. -/
def conditionalMaxEntropyPositiveValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {h : ℝ | ∃ σ : State b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = ρ.conditionalMaxEntropyCandidate σ}

/-- Compatibility name for the positive-candidate conditional max-entropy.

After the real-valued convention correction, this agrees with
`conditionalMaxEntropy`; the separate name remains useful for endpoint-duality
proofs that explicitly expose the positive raw exponent. -/
def conditionalMaxEntropyPositive (ρ : State (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a))

/-- The positive-candidate raw endpoint exponent. -/
def conditionalMaxEntropyPositiveExponent (ρ : State (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))

theorem conditionalMaxEntropyPositiveExponentValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) (maximallyMixed b),
    maximallyMixed b, ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos (a := a), rfl⟩

theorem conditionalMaxEntropyPositiveExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
  refine ⟨(Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, _hpos, rfl⟩
  exact ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ

theorem conditionalMaxEntropyExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyExponentValueSet (a := a)) := by
  refine ⟨(Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  exact ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ

theorem conditionalMaxEntropyExponentValueSet_nonempty
    [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) (maximallyMixed b),
    maximallyMixed b, rfl⟩

theorem ConditionalMaxFidelityBlockFeasible.blockExponentValue_le_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] {ρ : State (Prod a b)} {σ : State b}
    {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockExponentValue (a := a) X ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  calc
    conditionalMaxFidelityBlockExponentValue (a := a) X
        ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a) σ :=
          hX.blockExponentValue_le_exponentCandidate
    _ ≤ ρ.conditionalMaxEntropyExponent (a := a) := by
          rw [conditionalMaxEntropyExponent]
          exact le_csSup (ρ.conditionalMaxEntropyExponentValueSet_bddAbove (a := a))
            ⟨σ, rfl⟩

theorem conditionalMaxFidelityBlockExponentValueSet_sSup_le_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  refine csSup_le (ρ.conditionalMaxFidelityBlockExponentValueSet_nonempty (a := a)) ?_
  intro v hv
  rcases hv with ⟨σ, X, hX, rfl⟩
  exact hX.blockExponentValue_le_conditionalMaxEntropyExponent

/-- The block-SDP endpoint surface is bounded above by the definition-level
conditional max-entropy exponent. -/
theorem conditionalMaxFidelityBlockExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) := by
  refine ⟨ρ.conditionalMaxEntropyExponent (a := a), ?_⟩
  intro x hx
  rcases hx with ⟨σ, X, hX, rfl⟩
  exact hX.blockExponentValue_le_conditionalMaxEntropyExponent

/-- The fidelity block-SDP endpoint has the same optimum as the
definition-level conditional max-entropy exponent. -/
theorem sSup_conditionalMaxFidelityBlockExponentValueSet_eq_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
      ρ.conditionalMaxEntropyExponent (a := a) := by
  refine le_antisymm
    (ρ.conditionalMaxFidelityBlockExponentValueSet_sSup_le_conditionalMaxEntropyExponent
      (a := a)) ?_
  rw [conditionalMaxEntropyExponent]
  refine csSup_le (ρ.conditionalMaxEntropyExponentValueSet_nonempty (a := a)) ?_
  intro x hx
  exact le_csSup (ρ.conditionalMaxFidelityBlockExponentValueSet_bddAbove (a := a))
    (ρ.conditionalMaxEntropyExponentValueSet_subset_conditionalMaxFidelityBlockExponentValueSet
      (a := a) hx)

/-- The raw fidelity endpoint and the block-SDP endpoint have the same
dimension-scaled optimum. -/
theorem card_mul_sSup_fidelityValueSet_eq_sSup_conditionalMaxFidelityBlockExponentValueSet
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
      sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) := by
  rw [sSup_conditionalMaxFidelityBlockExponentValueSet_eq_conditionalMaxEntropyExponent
    (a := a) ρ]
  exact (conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
    (a := a) ρ).symm

theorem conditionalMaxEntropyPositiveExponent_le_exponent
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveExponent (a := a) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [conditionalMaxEntropyPositiveExponent, conditionalMaxEntropyExponent]
  refine csSup_le (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨σ, _hpos, rfl⟩
  exact le_csSup (ρ.conditionalMaxEntropyExponentValueSet_bddAbove (a := a))
    ⟨σ, rfl⟩

theorem conditionalMaxEntropyExponent_le_positiveExponent
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponent (a := a) ≤
      ρ.conditionalMaxEntropyPositiveExponent (a := a) := by
  rw [conditionalMaxEntropyExponent, conditionalMaxEntropyPositiveExponent]
  have hne :
      (ρ.conditionalMaxEntropyExponentValueSet (a := a)).Nonempty := by
    rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a) with
      ⟨_, σ, _hpos, rfl⟩
    exact ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) σ, σ, rfl⟩
  refine csSup_le hne ?_
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  by_cases hpos : 0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ
  · exact le_csSup (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))
      ⟨σ, hpos, rfl⟩
  · have hzero : ρ.conditionalMaxEntropyExponentCandidate (a := a) σ = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        (conditionalMaxEntropyExponentCandidate_nonneg (a := a) ρ σ)
    rw [hzero]
    rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a) with ⟨y, hy⟩
    rcases hy with ⟨τ, hτpos, rfl⟩
    exact le_trans (le_of_lt hτpos)
      (le_csSup (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))
        ⟨τ, hτpos, rfl⟩)

theorem conditionalMaxEntropyExponent_eq_positiveExponent
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponent (a := a) =
      ρ.conditionalMaxEntropyPositiveExponent (a := a) :=
  le_antisymm
    (ρ.conditionalMaxEntropyExponent_le_positiveExponent (a := a))
    (ρ.conditionalMaxEntropyPositiveExponent_le_exponent (a := a))

theorem conditionalMaxEntropyExponent_pos
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    0 < ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a)]
  rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a) with ⟨x, hx⟩
  rcases hx with ⟨σ, hσpos, rfl⟩
  exact lt_of_lt_of_le hσpos
    (le_csSup (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))
      ⟨σ, hσpos, rfl⟩)

theorem conditionalMaxEntropyPositiveValueSet_eq_log2_image
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) =
      log2 '' ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
  ext h
  constructor
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) σ, ?_, ?_⟩
    · exact ⟨σ, hpos, rfl⟩
    · exact (ρ.conditionalMaxEntropyCandidate_eq_log2_exponentCandidate σ).symm
  · rintro ⟨x, ⟨σ, hpos, rfl⟩, rfl⟩
    exact ⟨σ, hpos, ρ.conditionalMaxEntropyCandidate_eq_log2_exponentCandidate σ⟩

/-- Positive endpoint candidates are definition-level conditional max-entropy
candidates. After the convention correction this is essentially an identity
of candidate sets, kept as a monotonicity helper for existing proofs. -/
theorem conditionalMaxEntropyPositiveValueSet_subset_conditionalMaxEntropyValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) ⊆
      ρ.conditionalMaxEntropyValueSet (a := a) := by
  intro h hh
  rcases hh with ⟨σ, _hpos, rfl⟩
  exact ⟨σ, _hpos, rfl⟩

theorem conditionalMaxEntropyValueSet_eq_positiveValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyValueSet (a := a) =
      ρ.conditionalMaxEntropyPositiveValueSet (a := a) := rfl

theorem conditionalMaxEntropy_eq_positive [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropy = ρ.conditionalMaxEntropyPositive := by
  rw [conditionalMaxEntropy_eq_sSup_valueSet, conditionalMaxEntropyPositive,
    conditionalMaxEntropyValueSet_eq_positiveValueSet]

/-- The positive-endpoint conditional max-entropy is bounded by the
definition-level value; after the real-valued convention correction these are
definitionally the same candidate set. -/
theorem conditionalMaxEntropyPositive_le_conditionalMaxEntropy
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositive ≤ ρ.conditionalMaxEntropy := by
  rw [conditionalMaxEntropyPositive, conditionalMaxEntropy_eq_sSup_valueSet]
  refine csSup_le ?_ ?_
  · rw [conditionalMaxEntropyPositiveValueSet_eq_log2_image]
    exact Set.Nonempty.image _ (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty
      (a := a))
  · intro h hh
    exact le_csSup (ρ.conditionalMaxEntropyValueSet_bddAbove (a := a))
      (ρ.conditionalMaxEntropyPositiveValueSet_subset_conditionalMaxEntropyValueSet
        (a := a) hh)

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent
    (ρ : State (Prod a b))
    (hne : (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty)
    (hbdd : BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) := by
  have hpos : ∀ x ∈ ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a), 0 < x := by
    intro x hx
    rcases hx with ⟨σ, hσpos, rfl⟩
    exact hσpos
  rw [conditionalMaxEntropyPositive, conditionalMaxEntropyPositiveExponent,
    conditionalMaxEntropyPositiveValueSet_eq_log2_image]
  exact log2_sSup_image_eq hne hbdd hpos

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_bddAbove
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hbdd : BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) :=
  ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent
    (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a)) hbdd

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) :=
  ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_bddAbove
    (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))

theorem conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyExponent (a := a)) := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_nonempty (a := a),
    ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a)]

/-! ## Conditional min-entropy scale -/

/-- Feasibility for the unnormalized side-operator form of conditional
min-entropy:
`ρ_AB ≤ I_A ⊗ T_B`, with `T_B ≥ 0`. -/
def ConditionalMinEntropyScaleFeasible (ρ : State (Prod a b)) (T : CMatrix b) :
    Prop :=
  T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T

@[simp]
theorem ConditionalMinEntropyScaleFeasible_eq
    (ρ : State (Prod a b)) (T : CMatrix b) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ↔
      T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T :=
  Iff.rfl

/-- Conditioning-register isometries transport unnormalized conditional-min
feasible side operators.  If `ρ_AB ≤ I_A ⊗ T_B`, then after applying an
isometry `V : B → B⁺` to the conditioning register, the pushed side operator
`V T_B V†` remains feasible. -/
theorem ConditionalMinEntropyScaleFeasible.apply_conditioningIsometry
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ : State (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (V : ReferenceIsometry b bPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρ.conditioningIsometryApply V)
      (MatrixMap.ofReferenceIsometry V T) := by
  constructor
  · exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V) T hT.1
  · let Φ : MatrixMap (Prod a b) (Prod a bPlus) :=
      MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V)
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
    have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) hdiff
    change ((Matrix.kronecker (1 : CMatrix a)
        (MatrixMap.ofReferenceIsometry V T)) -
        (ρ.conditioningIsometryApply V).matrix).PosSemidef
    rw [conditioningIsometryApply_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    rw [MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]
    simp [Channel.idChannel, MatrixMap.ofKraus]

theorem trace_ofReferenceIsometry_apply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) (T : CMatrix b) :
    (MatrixMap.ofReferenceIsometry V T).trace.re = T.trace.re := by
  have h := MatrixMap.ofReferenceIsometry_isTracePreserving V T
  rw [h]

omit [DecidableEq b] in
/-- The lower-right principal block of a PSD `Sum`-indexed matrix has trace no
larger than the full matrix. -/
theorem sumBlock22_trace_re_le_of_posSemidef
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (T : CMatrix (Sum extra b)) (hT : T.PosSemidef) :
    (Matrix.sumBlock22 T).trace.re ≤ T.trace.re := by
  have hsplit :
      T.trace.re =
        (Matrix.sumBlock11 T).trace.re + (Matrix.sumBlock22 T).trace.re := by
    simp [Matrix.trace, Matrix.sumBlock11, Matrix.sumBlock22,
      Fintype.sum_sum_type, Complex.add_re, add_comm]
  have h11_nonneg :
      0 ≤ (Matrix.sumBlock11 T).trace.re :=
    (Matrix.PosSemidef.trace_nonneg (Matrix.sumBlock11_posSemidef hT)).1
  linarith

/-- For the concrete right-summand embedding used by the purification transport
layer, feasible enlarged side operators compress back to feasible old side
operators by taking the lower-right principal block. -/
theorem ConditionalMinEntropyScaleFeasible.compress_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ : State (Prod a b)} {TPlus : CMatrix (Sum extra b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ (Matrix.sumBlock22 TPlus) := by
  constructor
  · exact Matrix.sumBlock22_posSemidef hT.1
  · have hsub := hT.2.submatrix (fun x : Prod a b => (x.1, Sum.inr x.2))
    change (Matrix.kronecker (1 : CMatrix a) (Matrix.sumBlock22 TPlus) -
      ρ.matrix).PosSemidef
    convert hsub using 1
    ext x y
    simp [Matrix.kronecker, Matrix.sumBlock22, conditioningIsometryApply_matrix,
      ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      ReferenceIsometry.sumInr, Matrix.mul_apply]

/-- The raw endpoint scale
`inf {Tr T_B | T_B ≥ 0, ρ_AB ≤ I_A ⊗ T_B}`. -/
def conditionalMinEntropyScale (ρ : State (Prod a b)) : ℝ :=
  sInf {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScale_eq (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- The unnormalized side-operator scale values
`Tr T_B` with `T_B ≥ 0` and `ρ_AB ≤ I_A ⊗ T_B`. -/
def conditionalMinEntropyScaleValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScaleValueSet_eq (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) =
      {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- Dual-effect feasibility for the endpoint conditional-min SDP:
`M_AC ≥ 0` and `Tr_A M_AC ≤ I_C`. -/
def ConditionalMinEntropyDualEffectFeasible (M : CMatrix (Prod a b)) : Prop :=
  M.PosSemidef ∧ partialTraceA (a := a) (b := b) M ≤ 1

/-- The linear dual-effect value set for the endpoint conditional-min SDP:
`{Tr(ρ_AB M_AB) | M_AB ≥ 0, Tr_A M_AB ≤ I_B}`. -/
def conditionalMinEntropyDualEffectValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {v : ℝ | ∃ M : CMatrix (Prod a b),
    ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
      v = ((ρ.matrix * M).trace).re}

/-- Reindex an `A ⊗ B` dual effect as the Choi matrix of a map `B → A`. -/
def conditionalMinEntropyDualEffectChoiMatrix (M : CMatrix (Prod a b)) :
    CMatrix (Prod b a) :=
  fun x y => M (x.2, x.1) (y.2, y.1)

/-- The matrix map `B → A` represented by a conditional-min dual effect
`M_AC`. -/
def conditionalMinEntropyDualEffectMatrixMap (M : CMatrix (Prod a b)) :
    MatrixMap b a :=
  MatrixMap.ofChoiMatrix (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M)

/-- Transpose-Choi orientation of an `A ⊗ B` dual effect as a map `B → A`.

This is the orientation that pairs directly with the repository's
`MatrixMap.choi` convention and the `AA'` maximally-entangled projector in the
endpoint link-map proof. -/
def conditionalMinEntropyDualEffectTransposeChoiMatrix (M : CMatrix (Prod a b)) :
    CMatrix (Prod b a) :=
  Matrix.transpose (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M)

/-- The transpose-Choi matrix map `B → A` induced by a conditional-min dual
effect. -/
def conditionalMinEntropyDualEffectTransposeMatrixMap (M : CMatrix (Prod a b)) :
    MatrixMap b a :=
  MatrixMap.ofChoiMatrix
    (conditionalMinEntropyDualEffectTransposeChoiMatrix (a := a) (b := b) M)

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem conditionalMinEntropyDualEffectChoiMatrix_posSemidef
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M).PosSemidef := by
  simpa [conditionalMinEntropyDualEffectChoiMatrix] using
    hM.submatrix (fun x : Prod b a => (x.2, x.1))

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem conditionalMinEntropyDualEffectTransposeChoiMatrix_posSemidef
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    (conditionalMinEntropyDualEffectTransposeChoiMatrix (a := a) (b := b) M).PosSemidef := by
  exact (conditionalMinEntropyDualEffectChoiMatrix_posSemidef
    (a := a) (b := b) hM).transpose

/-- Positive dual effects define Choi-positive, hence completely positive,
finite matrix maps. -/
theorem conditionalMinEntropyDualEffectMatrixMap_isCompletelyPositive
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    MatrixMap.IsCompletelyPositive
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) := by
  exact MatrixMap.ofChoiMatrix_isCompletelyPositive
    (conditionalMinEntropyDualEffectChoiMatrix_posSemidef (a := a) (b := b) hM)

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_isCompletelyPositive
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    MatrixMap.IsCompletelyPositive
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) := by
  exact MatrixMap.ofChoiMatrix_isCompletelyPositive
    (conditionalMinEntropyDualEffectTransposeChoiMatrix_posSemidef
      (a := a) (b := b) hM)

theorem conditionalMinEntropyDualEffectMatrixMap_trace
    (M : CMatrix (Prod a b)) (X : CMatrix b) :
    ((conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) X).trace =
      (X * Matrix.transpose (partialTraceA (a := a) (b := b) M)).trace := by
  classical
  simp [conditionalMinEntropyDualEffectMatrixMap,
    conditionalMinEntropyDualEffectChoiMatrix, Matrix.trace, Matrix.mul_apply,
    partialTraceA]
  calc
    (∑ x : a, ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * M (x, x_1) (x, x_2)) =
        ∑ x_1 : b, ∑ x : a, ∑ x_2 : b, X x_1 x_2 * M (x, x_1) (x, x_2) := by
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, ∑ x : a, X x_1 x_2 * M (x, x_1) (x, x_2) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * ∑ x : a, M (x, x_1) (x, x_2) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      apply Finset.sum_congr rfl
      intro x_2 _
      rw [Finset.mul_sum]

/-- Dual-effect feasible matrices define trace-nonincreasing CP maps under the
Choi interpretation `B → A`. -/
theorem conditionalMinEntropyDualEffectMatrixMap_traceNonincreasing
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.IsTraceNonincreasing
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) := by
  intro X hX
  rw [conditionalMinEntropyDualEffectMatrixMap_trace (a := a) (b := b) M X]
  have hcomp : ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hcompT :
      ((1 : CMatrix b) - Matrix.transpose (partialTraceA (a := a) (b := b) M)).PosSemidef := by
    simpa [Matrix.transpose_sub, Matrix.transpose_one] using hcomp.transpose
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcompT
  have htrace :
      ((X * ((1 : CMatrix b) -
          Matrix.transpose (partialTraceA (a := a) (b := b) M))).trace).re =
        X.trace.re -
          ((X * Matrix.transpose (partialTraceA (a := a) (b := b) M)).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace] at hnonneg
  linarith

theorem conditionalMinEntropyDualEffectMatrixMap_traceNonincreasingCP
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.TraceNonincreasingCP
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) where
  completelyPositive :=
    conditionalMinEntropyDualEffectMatrixMap_isCompletelyPositive (a := a) (b := b) hM.1
  traceNonincreasing :=
    conditionalMinEntropyDualEffectMatrixMap_traceNonincreasing (a := a) (b := b) hM

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_trace
    (M : CMatrix (Prod a b)) (X : CMatrix b) :
    ((conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) X).trace =
      (X * partialTraceA (a := a) (b := b) M).trace := by
  classical
  simp [conditionalMinEntropyDualEffectTransposeMatrixMap,
    conditionalMinEntropyDualEffectTransposeChoiMatrix,
    conditionalMinEntropyDualEffectChoiMatrix, Matrix.trace, Matrix.mul_apply,
    partialTraceA, Matrix.transpose]
  calc
    (∑ x : a, ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * M (x, x_2) (x, x_1)) =
        ∑ x_1 : b, ∑ x : a, ∑ x_2 : b, X x_1 x_2 * M (x, x_2) (x, x_1) := by
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, ∑ x : a, X x_1 x_2 * M (x, x_2) (x, x_1) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * ∑ x : a, M (x, x_2) (x, x_1) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      apply Finset.sum_congr rfl
      intro x_2 _
      rw [Finset.mul_sum]

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasing
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.IsTraceNonincreasing
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) := by
  intro X hX
  rw [conditionalMinEntropyDualEffectTransposeMatrixMap_trace (a := a) (b := b) M X]
  have hcomp : ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcomp
  have htrace :
      ((X * ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M)).trace).re =
        X.trace.re - ((X * partialTraceA (a := a) (b := b) M).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace] at hnonneg
  linarith

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasingCP
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.TraceNonincreasingCP
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) where
  completelyPositive :=
    conditionalMinEntropyDualEffectTransposeMatrixMap_isCompletelyPositive
      (a := a) (b := b) hM.1
  traceNonincreasing :=
    conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasing
      (a := a) (b := b) hM

/-- The `AC` dual effect generated by a Kraus stack `K : C → A`.

The orientation is chosen so that
`conditionalMinEntropyDualEffectTransposeMatrixMap` has exactly the Kraus
representation `MatrixMap.ofKraus K`. -/
def conditionalMinEntropyDualEffectOfKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) : CMatrix (Prod a b) :=
  fun x y => ∑ l : κ, K l y.1 y.2 * star (K l x.1 x.2)

theorem conditionalMinEntropyDualEffectOfKraus_transposeMatrixMap_eq_ofKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) :
    conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b)
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K) =
      MatrixMap.ofKraus K := by
  apply MatrixMap.choi_inj
  rw [conditionalMinEntropyDualEffectTransposeMatrixMap, MatrixMap.choi_ofChoiMatrix,
    MatrixMap.choi_ofKraus]
  ext x y
  rcases x with ⟨z, i⟩
  rcases y with ⟨z', i'⟩
  simp [conditionalMinEntropyDualEffectTransposeChoiMatrix,
    conditionalMinEntropyDualEffectChoiMatrix,
    conditionalMinEntropyDualEffectOfKraus, Matrix.transpose, Matrix.sum_apply,
    Matrix.vecMulVec_apply]

theorem conditionalMinEntropyDualEffectOfKraus_posSemidef
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) :
    (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K).PosSemidef := by
  have hCPK : MatrixMap.IsCompletelyPositive (MatrixMap.ofKraus K) := by
    rw [MatrixMap.IsCompletelyPositive, MatrixMap.choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ fun l _ =>
      Matrix.posSemidef_vecMulVec_self_star _
  have hCP :
      MatrixMap.IsCompletelyPositive
        (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b)
          (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K)) := by
    simpa [conditionalMinEntropyDualEffectOfKraus_transposeMatrixMap_eq_ofKraus
      (a := a) (b := b) K] using hCPK
  rw [MatrixMap.IsCompletelyPositive, conditionalMinEntropyDualEffectTransposeMatrixMap,
    MatrixMap.choi_ofChoiMatrix] at hCP
  have hchoi :
      (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b)
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K)).PosSemidef := by
    simpa [conditionalMinEntropyDualEffectTransposeChoiMatrix] using hCP.transpose
  simpa [conditionalMinEntropyDualEffectChoiMatrix] using
    hchoi.submatrix (fun x : Prod a b => (x.2, x.1))

theorem partialTraceA_conditionalMinEntropyDualEffectOfKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) :
    partialTraceA (a := a) (b := b)
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K) =
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K := by
  classical
  ext z z'
  simp [partialTraceA, conditionalMinEntropyDualEffectOfKraus,
    MatrixMap.smoothEndpointKrausStack, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, mul_comm]
  rw [Finset.sum_comm]

theorem conditionalMinEntropyDualEffectOfKraus_feasible
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ)
    (hK :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
          MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix b)) :
    ConditionalMinEntropyDualEffectFeasible (a := a)
      (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K) := by
  constructor
  · exact conditionalMinEntropyDualEffectOfKraus_posSemidef (a := a) (b := b) K
  · rw [partialTraceA_conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K]
    exact hK

theorem exists_krausStack_contraction_conditionalMinEntropyDualEffectTransposeMatrixMap
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    ∃ K : (b × a) → Matrix a b ℂ,
      conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M =
        MatrixMap.ofKraus K ∧
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
          MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix b) := by
  classical
  let T : MatrixMap b a :=
    conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M
  have hCP : MatrixMap.IsCompletelyPositive T :=
    conditionalMinEntropyDualEffectTransposeMatrixMap_isCompletelyPositive
      (a := a) (b := b) hM.1
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd T hCP
  refine ⟨K, hK, ?_⟩
  have hTNI : MatrixMap.IsTraceNonincreasing (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasing
      (a := a) (b := b) hM
  exact MatrixMap.smoothEndpointKrausStack_contraction_of_traceNonincreasing K hTNI

/-- The maximally-entangled projector on the outer `A` registers, tensored
with the identity on the middle `B` register.

On `(A × B) × A`, this is
`|Ω⟩⟨Ω|_{AA'} ⊗ I_B`, where
`|Ω⟩ = |A|^{-1/2} ∑ᵢ |i⟩|i⟩`.  The concrete matrix form avoids introducing a
separate maximally-entangled-vector API just for the endpoint SDP bridge. -/
def maximallyEntangledProjectorWithMiddle [Nonempty a] (b : Type v) [Fintype b]
    [DecidableEq b] :
    CMatrix (Prod (Prod a b) a) :=
  fun x y =>
    if x.1.2 = y.1.2 ∧ x.1.1 = x.2 ∧ y.1.1 = y.2 then
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ)
    else
      0

@[simp]
theorem maximallyEntangledProjectorWithMiddle_apply [Nonempty a]
    {b : Type v} [Fintype b] [DecidableEq b] (x y : Prod (Prod a b) a) :
    maximallyEntangledProjectorWithMiddle (a := a) b x y =
      if x.1.2 = y.1.2 ∧ x.1.1 = x.2 ∧ y.1.1 = y.2 then
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ)
      else
        0 :=
  rfl

private def maximallyEntangledMiddleVector [Nonempty a] (b0 : b) :
    Prod (Prod a b) a → ℂ :=
  fun x => if x.1.2 = b0 ∧ x.1.1 = x.2 then
    (Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℂ) else 0

private theorem maximallyEntangledProjectorWithMiddle_eq_sum_rankOne [Nonempty a] :
    maximallyEntangledProjectorWithMiddle (a := a) b =
      ∑ b0 : b, rankOneMatrix (maximallyEntangledMiddleVector (a := a) b0) := by
  classical
  ext x y
  simp only [Matrix.sum_apply]
  by_cases hb : x.1.2 = y.1.2
  · have hsum :
        (∑ b0 : b, rankOneMatrix (maximallyEntangledMiddleVector (a := a) b0) x y) =
          rankOneMatrix (maximallyEntangledMiddleVector (a := a) x.1.2) x y := by
      rw [Finset.sum_eq_single x.1.2]
      · intro b0 _ hb0
        have hx0 : x.1.2 ≠ b0 := by
          intro h
          exact hb0 (h.symm)
        simp [maximallyEntangledMiddleVector, rankOneMatrix_apply, hx0]
      · intro hnot
        simp at hnot
    rw [hsum]
    by_cases hx : x.1.1 = x.2
    · by_cases hy : y.1.1 = y.2
      · have hcard_pos : 0 < (Fintype.card a : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
        have hsqrt_ne : Real.sqrt (Fintype.card a : ℝ) ≠ 0 := by
          exact ne_of_gt (Real.sqrt_pos.mpr hcard_pos)
        have hcoeff_real :
            (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) =
              (((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℝ) : ℂ) *
                (((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]
          congr 1
          field_simp [hsqrt_ne]
          rw [Real.sq_sqrt (le_of_lt hcard_pos)]
        have hcoeff :
            ((Fintype.card a : ℂ)⁻¹) =
              ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) *
                ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) := by
          simpa [Complex.ofReal_inv] using hcoeff_real
        simp [maximallyEntangledProjectorWithMiddle, maximallyEntangledMiddleVector,
          rankOneMatrix_apply, hb, hx, hy]
        exact hcoeff
      · simp [maximallyEntangledProjectorWithMiddle, maximallyEntangledMiddleVector,
          rankOneMatrix_apply, hb, hx, hy]
    · simp [maximallyEntangledProjectorWithMiddle, maximallyEntangledMiddleVector,
        rankOneMatrix_apply, hb, hx]
  · have hsum :
        (∑ b0 : b, rankOneMatrix (maximallyEntangledMiddleVector (a := a) b0) x y) = 0 := by
      apply Finset.sum_eq_zero
      intro b0 _
      by_cases hx0 : x.1.2 = b0
      · have hy0 : ¬ y.1.2 = b0 := by
          intro hy0
          exact hb (hx0.trans hy0.symm)
        simp [maximallyEntangledMiddleVector, rankOneMatrix_apply, hx0, hy0]
      · simp [maximallyEntangledMiddleVector, rankOneMatrix_apply, hx0]
    simp [maximallyEntangledProjectorWithMiddle, hb]
    exact hsum.symm

theorem maximallyEntangledProjectorWithMiddle_posSemidef [Nonempty a] :
    (maximallyEntangledProjectorWithMiddle (a := a) b).PosSemidef := by
  classical
  rw [maximallyEntangledProjectorWithMiddle_eq_sum_rankOne]
  exact Matrix.posSemidef_sum Finset.univ fun b0 _ =>
    rankOneMatrix_pos (maximallyEntangledMiddleVector (a := a) b0)

private theorem sum_abab_delta_state {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [AddCommMonoid γ] (p r : α) (q s : β) (f : α → β → α → β → γ) :
    (∑ x₁ : α, ∑ y₁ : β, ∑ x₂ : α, ∑ y₂ : β,
      if x₁ = p ∧ x₂ = r ∧ y₁ = q ∧ y₂ = s then f x₁ y₁ x₂ y₂ else 0) =
      f p q r s := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single s]
        · simp
        · intro y _ hy
          simp [hy]
        · intro hnot
          simp at hnot
      · intro x _ hx
        simp [hx]
      · intro hnot
        simp at hnot
    · intro y _ hy
      simp [hy]
    · intro hnot
      simp at hnot
  · intro x _ hx
    simp [hx]
  · intro hnot
    simp at hnot

private theorem sum_projector_delta_state {α : Type*} {β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (r : ℂ) (f : α → β → α → ℂ) :
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if x = u ∧ y = v ∧ z = w then r * f x y z else 0) =
      r * (∑ x : α, ∑ z : α, ∑ y : β, f x y z) := by
  calc
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if x = u ∧ y = v ∧ z = w then r * f x y z else 0) =
        ∑ x : α, ∑ y : β, ∑ z : α, r * f x y z := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
          if x = u ∧ y = v ∧ z = w then r * f x y z else 0) =
            ∑ z : α, ∑ u : α, ∑ v : β, ∑ w : α,
              if x = u ∧ y = v ∧ z = w then r * f x y z else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ z : α, r * f x y z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · rw [Finset.sum_eq_single z]
              · simp
              · intro w _ hw
                have hzw : z ≠ w := hw.symm
                simp [hzw]
              · intro hnot
                simp at hnot
            · intro v _ hv
              have hyv : y ≠ v := hv.symm
              simp [hyv]
            · intro hnot
              simp at hnot
          · intro u _ hu
            have hxu : x ≠ u := hu.symm
            simp [hxu]
          · intro hnot
            simp at hnot
    _ = ∑ x : α, ∑ z : α, ∑ y : β, r * f x y z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = r * (∑ x : α, ∑ z : α, ∑ y : β, f x y z) := by
      simp [Finset.mul_sum]

private theorem sum_projector_delta_state_full {α : Type*} {β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (r : ℂ) (f : α → β → α → α → β → α → ℂ) :
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0) =
      r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
  calc
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0) =
        ∑ x : α, ∑ y : β, ∑ z : α, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
          if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0) =
            ∑ z : α, ∑ u : α, ∑ v : β, ∑ w : α,
              if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ z : α, r * f x y x z y z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · rw [Finset.sum_eq_single z]
              · simp
              · intro w _ hw
                have hzw : z ≠ w := hw.symm
                simp [hzw]
              · intro hnot
                simp at hnot
            · intro v _ hv
              have hyv : y ≠ v := hv.symm
              simp [hyv]
            · intro hnot
              simp at hnot
          · intro u _ hu
            have hxu : x ≠ u := hu.symm
            simp [hxu]
          · intro hnot
            simp at hnot
    _ = ∑ x : α, ∑ z : α, ∑ y : β, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
      simp [Finset.mul_sum]

private theorem sum_projector_delta_state_full_right {α : Type*} {β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (r : ℂ) (f : α → β → α → α → β → α → ℂ) :
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0) =
      r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
  calc
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0) =
        ∑ x : α, ∑ y : β, ∑ z : α, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
          if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0) =
            ∑ z : α, ∑ u : α, ∑ v : β, ∑ w : α,
              if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ z : α, r * f x y x z y z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · rw [Finset.sum_eq_single z]
              · simp
              · intro w _ hw
                have hzw : z ≠ w := hw.symm
                simp [hzw]
              · intro hnot
                simp at hnot
            · intro v _ hv
              simp [hv]
            · intro hnot
              simp at hnot
          · intro u _ hu
            have hxu : x ≠ u := hu.symm
            simp [hxu]
          · intro hnot
            simp at hnot
    _ = ∑ x : α, ∑ z : α, ∑ y : β, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
      simp [Finset.mul_sum]

theorem trace_maximallyEntangledProjectorWithMiddle_mul [Nonempty a]
    (O : CMatrix (Prod (Prod a b) a)) :
    (((maximallyEntangledProjectorWithMiddle (a := a) b) * O).trace) =
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) *
        (∑ i : a, ∑ i' : a, ∑ j : b, O ((i', j), i') ((i, j), i)) := by
  classical
  simpa [maximallyEntangledProjectorWithMiddle, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type] using
      sum_projector_delta_state_full
        (α := a) (β := b)
        ((((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ))
        (fun x y u z v w => O ((z, v), w) ((x, y), u))

theorem trace_mul_maximallyEntangledProjectorWithMiddle [Nonempty a]
    (O : CMatrix (Prod (Prod a b) a)) :
    ((O * (maximallyEntangledProjectorWithMiddle (a := a) b)).trace) =
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) *
        (∑ i : a, ∑ i' : a, ∑ j : b, O ((i, j), i) ((i', j), i')) := by
  classical
  simpa [maximallyEntangledProjectorWithMiddle, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, mul_comm, and_assoc, and_left_comm, and_comm] using
      sum_projector_delta_state_full_right
        (α := a) (β := b)
        ((((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ))
        (fun x y u z v w => O ((x, y), u) ((z, v), w))

theorem conditionalMinEntropyDualEffectValueSet_nonempty
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectValueSet (a := a)).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · constructor
    · exact Matrix.PosSemidef.zero
    · have hzero :
          partialTraceA (a := a) (b := b) (0 : CMatrix (Prod a b)) = 0 := by
        ext i j
        simp [partialTraceA]
      rw [Matrix.le_iff, hzero]
      simpa using (Matrix.PosSemidef.one : (1 : CMatrix b).PosSemidef)
  · simp

omit [DecidableEq b] in
private theorem partialTraceA_mul_kronecker_one_right
    (X : CMatrix (Prod a b)) (U : CMatrix b) :
    partialTraceA (a := a) (b := b) (X * Matrix.kronecker (1 : CMatrix a) U) =
      partialTraceA (a := a) (b := b) X * U := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq b] in
private theorem partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right
    (X : CMatrix (Prod a b)) (U : CMatrix b) :
    ((partialTraceA (a := a) (b := b) X) * U).trace =
      (X * Matrix.kronecker (1 : CMatrix a) U).trace := by
  rw [← partialTraceA_mul_kronecker_one_right X U]
  exact partialTraceA_trace (a := a) (b := b)
    (X * Matrix.kronecker (1 : CMatrix a) U)

omit [DecidableEq b] in
private theorem trace_kronecker_one_mul_eq_trace_mul_partialTraceA
    (M : CMatrix (Prod a b)) (T : CMatrix b) :
    ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re =
      ((T * partialTraceA (a := a) (b := b) M).trace).re := by
  have h₁ :
      (Matrix.kronecker (1 : CMatrix a) T * M).trace =
        (M * Matrix.kronecker (1 : CMatrix a) T).trace := by
    rw [Matrix.trace_mul_comm]
  have h₂ :
      (M * Matrix.kronecker (1 : CMatrix a) T).trace =
        ((partialTraceA (a := a) (b := b) M) * T).trace := by
    exact (partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right
      (a := a) (b := b) M T).symm
  calc
    ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re =
        ((M * Matrix.kronecker (1 : CMatrix a) T).trace).re := by rw [h₁]
    _ = (((partialTraceA (a := a) (b := b) M) * T).trace).re := by rw [h₂]
    _ = ((T * partialTraceA (a := a) (b := b) M).trace).re := by
      rw [Matrix.trace_mul_comm]

/-- Weak duality between the endpoint conditional-min scale side and the
dual-effect SDP side. -/
theorem conditionalMinEntropyDualEffectValue_le_scaleValue
    {ρ : State (Prod a b)} {M : CMatrix (Prod a b)} {T : CMatrix b}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M)
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    ((ρ.matrix * M).trace).re ≤ T.trace.re := by
  have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
  have hnonneg₁ := cMatrix_trace_mul_posSemidef_re_nonneg hdiff hM.1
  have hle₁ :
      ((ρ.matrix * M).trace).re ≤
        ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re := by
    have htrace :
        (((Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) * M).trace).re =
          ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re -
            ((ρ.matrix * M).trace).re := by
      simp [Matrix.sub_mul, Matrix.trace_sub]
    linarith
  have hptr_psd : (partialTraceA (a := a) (b := b) M).PosSemidef :=
    partialTraceA_posSemidef hM.1
  have hslack : ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hnonneg₂ := cMatrix_trace_mul_posSemidef_re_nonneg hT.1 hslack
  have hle₂ :
      ((T * partialTraceA (a := a) (b := b) M).trace).re ≤ T.trace.re := by
    have htrace :
        ((T * ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M)).trace).re =
          T.trace.re -
            ((T * partialTraceA (a := a) (b := b) M).trace).re := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    linarith
  calc
    ((ρ.matrix * M).trace).re ≤
        ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re := hle₁
    _ = ((T * partialTraceA (a := a) (b := b) M).trace).re :=
        trace_kronecker_one_mul_eq_trace_mul_partialTraceA (a := a) (b := b) M T
    _ ≤ T.trace.re := hle₂

theorem conditionalMinEntropyScale_eq_sInf_scaleValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
  rfl

/-- Normalize a positive semidefinite matrix with strictly positive trace into
a finite-dimensional state. -/
def ofPosSemidefTracePos (T : CMatrix b) (hT : T.PosSemidef)
    (htr : 0 < T.trace.re) : State b where
  matrix := (((T.trace.re)⁻¹ : ℝ) : ℂ) • T
  pos := by
    have hscale : (0 : ℂ) ≤ (((T.trace.re)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_nonneg.mpr (le_of_lt htr)
    exact Matrix.PosSemidef.smul hT hscale
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrace_real : T.trace = ((T.trace.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using (Matrix.PosSemidef.trace_nonneg hT).2.symm
    rw [htrace_real]
    simp [htr.ne']

@[simp]
theorem ofPosSemidefTracePos_matrix (T : CMatrix b) (hT : T.PosSemidef)
    (htr : 0 < T.trace.re) :
    (ofPosSemidefTracePos T hT htr).matrix =
      (((T.trace.re)⁻¹ : ℝ) : ℂ) • T :=
  rfl

theorem smul_ofPosSemidefTracePos_matrix
    (T : CMatrix b) (hT : T.PosSemidef) (htr : 0 < T.trace.re) :
    ((T.trace.re : ℂ) • (ofPosSemidefTracePos T hT htr).matrix) = T := by
  simp [ofPosSemidefTracePos, smul_smul, htr.ne']

/-- A normalized conditional-min feasible pair gives an unnormalized scale
feasible side operator. -/
theorem conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ
      ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) := by
  constructor
  · have hscale : (0 : ℂ) ≤ ((Real.rpow 2 (-lam) : ℝ) : ℂ) := by
      exact_mod_cast (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam))
    exact Matrix.PosSemidef.smul σ.pos hscale
  · simpa [ConditionalMinEntropyFeasible, ConditionalMinEntropyScaleFeasible,
      identityTensorStateMatrix, Matrix.kronecker_smul] using h

/-- The trace of the unnormalized side operator induced by a normalized
conditional-min feasible pair is exactly `2^{-λ}`. -/
theorem trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (_h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (((Real.rpow 2 (-lam) : ℂ) • σ.matrix).trace).re = Real.rpow 2 (-lam) := by
  rw [Matrix.trace_smul, σ.trace_eq_one]
  simp

theorem conditionalMinEntropyFeasible_maximallyMixed [Nonempty b]
    (ρ : State (Prod a b)) :
    ConditionalMinEntropyFeasible (a := a) ρ (maximallyMixed b)
      (-log2 (Fintype.card b : ℝ)) := by
  rw [ConditionalMinEntropyFeasible]
  rw [identityTensorStateMatrix_maximallyMixed (a := a) (b := b)]
  have hrpow : Real.rpow 2 (-(-log2 (Fintype.card b : ℝ))) =
      (Fintype.card b : ℝ) := by
    simpa using (rpow_two_log2_card (b := b))
  rw [hrpow]
  have hcardC : ((Fintype.card b : ℂ) *
      (((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ)) = 1 := by
    have hcard_ne : (Fintype.card b : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    norm_num [hcard_ne]
  simpa [smul_smul, hcardC] using ρ.matrix_le_one

theorem conditionalMinEntropyScaleValueSet_nonempty [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyScaleValueSet (a := a)).Nonempty := by
  let σ : State b := maximallyMixed b
  let lam : ℝ := -log2 (Fintype.card b : ℝ)
  let T : CMatrix b := (Real.rpow 2 (-lam) : ℂ) • σ.matrix
  have hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam :=
    ρ.conditionalMinEntropyFeasible_maximallyMixed (a := a)
  refine ⟨T.trace.re, T, ?_, rfl⟩
  exact conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas

/-- Weak-duality value-set form:
the dual-effect supremum is bounded by the min-entropy scale infimum. -/
theorem sSup_conditionalMinEntropyDualEffectValueSet_le_conditionalMinEntropyScale
    [Nonempty b] (ρ : State (Prod a b)) :
    sSup (ρ.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine csSup_le (ρ.conditionalMinEntropyDualEffectValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨M, hM, rfl⟩
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro y hy
  rcases hy with ⟨T, hT, rfl⟩
  exact conditionalMinEntropyDualEffectValue_le_scaleValue (a := a) hM hT

/-- A concrete scale-feasible point bounds the endpoint dual-effect value set
above.  This is the boundedness half needed for `sSup` arguments on the
dual-effect side. -/
theorem conditionalMinEntropyDualEffectValueSet_bddAbove [Nonempty b]
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMinEntropyDualEffectValueSet (a := a)) := by
  rcases ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨y, hy⟩
  rcases hy with ⟨T, hT, rfl⟩
  refine ⟨T.trace.re, ?_⟩
  intro x hx
  rcases hx with ⟨M, hM, rfl⟩
  exact conditionalMinEntropyDualEffectValue_le_scaleValue (a := a) hM hT

/-! ### Linear SDP surface for the endpoint min-entropy scale -/

/-- The block SDP equality map
`Z ↦ Tr_A Z₁₁ + Z₂₂`, where `Z₁₁` is the `AC` block and `Z₂₂`
is the slack block on `C`. -/
noncomputable def conditionalMinEntropyDualEffectConstraintCLM :
    CMatrix (Sum (Prod a b) b) →L[ℝ] CMatrix b :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun Z =>
        partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z) + Matrix.sumBlock22 Z
       map_add' := by
        intro X Y
        ext i j
        simp [partialTraceA, Matrix.sumBlock11, Matrix.sumBlock22, Finset.sum_add_distrib,
          add_assoc, add_left_comm, add_comm]
       map_smul' := by
        intro c X
        ext i j
        simp [partialTraceA, Matrix.sumBlock11, Matrix.sumBlock22, Finset.mul_sum] } :
      CMatrix (Sum (Prod a b) b) →ₗ[ℝ] CMatrix b)

/-- The block SDP objective `Z ↦ Re Tr(ρ_AC Z₁₁)`. -/
noncomputable def conditionalMinEntropyDualEffectObjectiveCLM
    (ρ : State (Prod a b)) :
    CMatrix (Sum (Prod a b) b) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun Z => (ρ.matrix * Matrix.sumBlock11 Z).trace
         map_add' := by
          intro X Y
          have hblock :
              Matrix.sumBlock11 (X + Y) =
                Matrix.sumBlock11 X + Matrix.sumBlock11 Y := by
            ext i j
            simp [Matrix.sumBlock11]
          rw [hblock, Matrix.mul_add, Matrix.trace_add]
         map_smul' := by
          intro c X
          have hblock :
              Matrix.sumBlock11 (c • X) = c • Matrix.sumBlock11 X := by
            ext i j
            simp [Matrix.sumBlock11]
          rw [hblock]
          simp [Matrix.trace_smul, Complex.real_smul] } :
        CMatrix (Sum (Prod a b) b) →ₗ[ℝ] ℂ))

@[simp]
theorem conditionalMinEntropyDualEffectObjectiveCLM_apply
    (ρ : State (Prod a b)) (Z : CMatrix (Sum (Prod a b) b)) :
    conditionalMinEntropyDualEffectObjectiveCLM (a := a) ρ Z =
      ((ρ.matrix * Matrix.sumBlock11 Z).trace).re :=
  rfl

/-- Real trace pairing against a fixed side-register matrix.  This local copy
keeps the endpoint SDP layer independent from the cq-guessing module. -/
noncomputable def conditionalMinEntropyTracePairingCLM (T : CMatrix b) :
    CMatrix b →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun A => (T * A).trace
         map_add' := by
          intro A B
          simp [Matrix.mul_add, Matrix.trace_add]
         map_smul' := by
          intro c A
          simp [Matrix.trace_smul, Complex.real_smul] } :
        CMatrix b →ₗ[ℝ] ℂ))

@[simp]
theorem conditionalMinEntropyTracePairingCLM_apply (T A : CMatrix b) :
    conditionalMinEntropyTracePairingCLM T A = ((T * A).trace).re :=
  rfl

/-- The finite-dimensional conic SDP whose primal is the dual-effect endpoint:
maximize `Tr(ρ_AC M)` over `M ≥ 0`, `Tr_A M ≤ I_C`, represented with a PSD
slack block. -/
noncomputable def conditionalMinEntropyDualEffectProgram
    (ρ : State (Prod a b)) :
    SDP.ContinuousConeProgram (CMatrix (Sum (Prod a b) b)) (CMatrix b) where
  K := psdCone (Sum (Prod a b) b)
  A := conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b)
  b := 1
  c := conditionalMinEntropyDualEffectObjectiveCLM (a := a) ρ

/-- The conic primal value set is exactly the dual-effect endpoint value set. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_eq
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet =
      ρ.conditionalMinEntropyDualEffectValueSet (a := a) := by
  classical
  ext v
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    let M : CMatrix (Prod a b) := Matrix.sumBlock11 Z
    have hZpsd : Z.PosSemidef := by
      simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZ.1
    refine ⟨M, ?_, ?_⟩
    · constructor
      · exact Matrix.sumBlock11_posSemidef hZpsd
      · have hSpsd : (Matrix.sumBlock22 Z).PosSemidef :=
          Matrix.sumBlock22_posSemidef hZpsd
        have hconstraint :
            partialTraceA (a := a) (b := b) M + Matrix.sumBlock22 Z =
              (1 : CMatrix b) := by
          simpa [conditionalMinEntropyDualEffectProgram,
            conditionalMinEntropyDualEffectConstraintCLM, M] using hZ.2
        rw [Matrix.le_iff]
        have hEq :
            (1 : CMatrix b) - partialTraceA (a := a) (b := b) M =
              Matrix.sumBlock22 Z := by
          rw [← hconstraint]
          abel
        simpa [hEq] using hSpsd
    · exact (conditionalMinEntropyDualEffectObjectiveCLM_apply (a := a) ρ Z).symm
  · rintro ⟨M, hM, rfl⟩
    let S : CMatrix b := (1 : CMatrix b) - partialTraceA (a := a) (b := b) M
    let Z : CMatrix (Sum (Prod a b) b) := Matrix.fromBlocks M 0 0 S
    refine ⟨Z, ?_, ?_⟩
    · constructor
      · have hS : S.PosSemidef := by
          simpa [S, Matrix.le_iff] using hM.2
        simpa [conditionalMinEntropyDualEffectProgram, Z, psdCone_mem] using
          (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
            hM.1 hS)
      · have h11 : Matrix.sumBlock11 Z = M := by
          ext i j
          simp [Z, Matrix.sumBlock11]
        have h22 : Matrix.sumBlock22 Z = S := by
          ext i j
          simp [Z, S, Matrix.sumBlock22]
        change partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z) +
            Matrix.sumBlock22 Z = (1 : CMatrix b)
        rw [h11, h22]
        ext i j
        simp [S]
    · change (ρ.matrix * M).trace.re = ρ.conditionalMinEntropyDualEffectObjectiveCLM Z
      rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
      have h11 : Matrix.sumBlock11 Z = M := by
        ext i j
        simp [Z, Matrix.sumBlock11]
      rw [h11]

/-- A feasible min-entropy scale matrix induces a feasible conic dual
functional for the dual-effect SDP. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible
    {ρ : State (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible
      (conditionalMinEntropyTracePairingCLM T) := by
  classical
  intro Z hZ
  let M : CMatrix (Prod a b) := Matrix.sumBlock11 Z
  let S : CMatrix b := Matrix.sumBlock22 Z
  have hZpsd : Z.PosSemidef := by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZ
  have hM : M.PosSemidef := Matrix.sumBlock11_posSemidef hZpsd
  have hS : S.PosSemidef := Matrix.sumBlock22_posSemidef hZpsd
  have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
  have hmain_nonneg := cMatrix_trace_mul_posSemidef_re_nonneg hdiff hM
  have hmain_trace :
      (((Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) * M).trace).re =
        ((T * partialTraceA (a := a) (b := b) M).trace).re -
          ((ρ.matrix * M).trace).re := by
    calc
      (((Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) * M).trace).re =
          (((Matrix.kronecker (1 : CMatrix a) T * M -
              ρ.matrix * M)).trace).re := by
        simp [Matrix.sub_mul]
      _ = ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re -
            ((ρ.matrix * M).trace).re := by
        simp [Matrix.trace_sub]
      _ = ((T * partialTraceA (a := a) (b := b) M).trace).re -
            ((ρ.matrix * M).trace).re := by
        rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
  have hmain :
      ((ρ.matrix * M).trace).re ≤
        ((T * partialTraceA (a := a) (b := b) M).trace).re := by
    linarith
  have hslack_nonneg := cMatrix_trace_mul_posSemidef_re_nonneg hT.1 hS
  calc
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z =
        ((ρ.matrix * M).trace).re := by
      change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z =
        ((ρ.matrix * M).trace).re
      rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    _ ≤ ((T * partialTraceA (a := a) (b := b) M).trace).re +
          ((T * S).trace).re := by
      linarith
    _ = conditionalMinEntropyTracePairingCLM T
          ((ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z) := by
      have hA :
          (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z =
            partialTraceA (a := a) (b := b) M + S := by
        change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
          partialTraceA (a := a) (b := b) M + S
        rfl
      rw [hA]
      simp [Matrix.mul_add, Matrix.trace_add]

/-- Matrix-order scale values are conic dual values of the dual-effect SDP. -/
theorem conditionalMinEntropyScaleValueSet_subset_dualValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) ⊆
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet := by
  rintro value ⟨T, hT, rfl⟩
  refine ⟨conditionalMinEntropyTracePairingCLM T,
    conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible (a := a) hT, ?_⟩
  change T.trace.re = conditionalMinEntropyTracePairingCLM T (1 : CMatrix b)
  rw [conditionalMinEntropyTracePairingCLM_apply]
  simp

/-- Testing a conic dual functional on a slack-only block gives positivity. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_slack_nonneg
    (ρ : State (Prod a b)) {y : CMatrix b →L[ℝ] ℝ}
    (hy : (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible y)
    {A : CMatrix b} (hA : A.PosSemidef) :
    0 ≤ y A := by
  let Z : CMatrix (Sum (Prod a b) b) := Matrix.fromBlocks 0 0 0 A
  have hZpsd : Z.PosSemidef := by
    simpa [Z] using
      (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
        (Matrix.PosSemidef.zero : (0 : CMatrix (Prod a b)).PosSemidef) hA)
  have hdual := hy Z (by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd)
  have hobj :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z = 0 := by
    change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z = 0
    rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    have h11 : Matrix.sumBlock11 Z = (0 : CMatrix (Prod a b)) := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    rw [h11]
    simp
  have hAmap :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z = A := by
    change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z = A
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, Matrix.sumBlock11,
      Matrix.sumBlock22, partialTraceA]
  simpa [hobj, hAmap] using hdual

/-- Testing a conic dual functional on an effect-only block gives the
pointwise domination inequality. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_effect_le
    (ρ : State (Prod a b)) {y : CMatrix b →L[ℝ] ℝ}
    (hy : (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible y)
    {A : CMatrix (Prod a b)} (hA : A.PosSemidef) :
    ((ρ.matrix * A).trace).re ≤ y (partialTraceA (a := a) (b := b) A) := by
  let Z : CMatrix (Sum (Prod a b) b) := Matrix.fromBlocks A 0 0 0
  have hZpsd : Z.PosSemidef := by
    simpa [Z] using
      (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
        hA (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef))
  have hdual := hy Z (by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd)
  have hobj :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z =
        ((ρ.matrix * A).trace).re := by
    change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z =
      ((ρ.matrix * A).trace).re
    rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    have h11 : Matrix.sumBlock11 Z = A := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    rw [h11]
  have hAmap :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z =
        partialTraceA (a := a) (b := b) A := by
    change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
      partialTraceA (a := a) (b := b) A
    have h11 : Matrix.sumBlock11 Z = A := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, h11, Matrix.sumBlock22]
  simpa [hobj, hAmap] using hdual

/-- Every conic dual value is represented by a matrix-order min-entropy scale
feasible point. -/
theorem conditionalMinEntropyDualEffectProgram_dualValueSet_subset_scaleValueSet
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet ⊆
      ρ.conditionalMinEntropyScaleValueSet (a := a) := by
  classical
  rintro value ⟨y, hy, rfl⟩
  let yH : HermitianDual b :=
    y.comp (hermitianInclusion : HermitianMatrix b →L[ℝ] CMatrix b)
  rcases exists_hermitian_tracePairing_representation (n := b) yH with ⟨T, hTrep⟩
  have hrep_psd (A : CMatrix b) (hA : A.PosSemidef) :
      y A = ((T.val * A).trace).re := by
    let X : HermitianMatrix b := ⟨A, hA.1⟩
    have h := hTrep X
    simpa [yH, X, tracePairing] using h
  refine ⟨T.val, ?_, ?_⟩
  · constructor
    · refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg T.isHermitian).2 ?_
      intro A hA
      have hyA := conditionalMinEntropyDualEffectProgram_dualFeasible_slack_nonneg
        (a := a) ρ hy hA
      have hrep := hrep_psd A hA
      calc
        0 ≤ y A := hyA
        _ = ((T.val * A).trace).re := hrep
    · rw [Matrix.le_iff]
      have hK : (Matrix.kronecker (1 : CMatrix a) T.val).IsHermitian := by
        rw [Matrix.IsHermitian]
        calc
          (Matrix.kronecker (1 : CMatrix a) T.val)ᴴ =
              Matrix.kronecker ((1 : CMatrix a)ᴴ) (T.valᴴ) := by
            simpa [Matrix.kronecker] using
              (Matrix.conjTranspose_kronecker (1 : CMatrix a) T.val)
          _ = Matrix.kronecker (1 : CMatrix a) T.val := by
            rw [Matrix.conjTranspose_one, T.isHermitian.eq]
      have hHerm : (Matrix.kronecker (1 : CMatrix a) T.val - ρ.matrix).IsHermitian :=
        hK.sub ρ.pos.1
      refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hHerm).2 ?_
      intro A hA
      have heffect := conditionalMinEntropyDualEffectProgram_dualFeasible_effect_le
        (a := a) ρ hy hA
      have hrep := hrep_psd (partialTraceA (a := a) (b := b) A)
        (partialTraceA_posSemidef hA)
      have htrace :
          (((Matrix.kronecker (1 : CMatrix a) T.val - ρ.matrix) * A).trace).re =
            ((T.val * partialTraceA (a := a) (b := b) A).trace).re -
              ((ρ.matrix * A).trace).re := by
        calc
          (((Matrix.kronecker (1 : CMatrix a) T.val - ρ.matrix) * A).trace).re =
              (((Matrix.kronecker (1 : CMatrix a) T.val * A -
                  ρ.matrix * A)).trace).re := by
            simp [Matrix.sub_mul]
          _ = ((Matrix.kronecker (1 : CMatrix a) T.val * A).trace).re -
                ((ρ.matrix * A).trace).re := by
            simp [Matrix.trace_sub]
          _ = ((T.val * partialTraceA (a := a) (b := b) A).trace).re -
                ((ρ.matrix * A).trace).re := by
            rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
      have heffect' :
          ((ρ.matrix * A).trace).re ≤
            ((T.val * partialTraceA (a := a) (b := b) A).trace).re := by
        calc
          ((ρ.matrix * A).trace).re ≤
              y (partialTraceA (a := a) (b := b) A) := heffect
          _ = ((T.val * partialTraceA (a := a) (b := b) A).trace).re := hrep
      linarith
  · have hrep_one : y (1 : CMatrix b) = T.val.trace.re := by
      let X : HermitianMatrix b := ⟨1, Matrix.PosSemidef.one.1⟩
      have h := hTrep X
      simpa [yH, X, tracePairing] using h
    change y (1 : CMatrix b) = T.val.trace.re
    exact hrep_one

/-- The conic and matrix-order dual value sets coincide. -/
theorem conditionalMinEntropyDualEffectProgram_dualValueSet_eq_scaleValueSet
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet =
      ρ.conditionalMinEntropyScaleValueSet (a := a) :=
  Set.Subset.antisymm
    (conditionalMinEntropyDualEffectProgram_dualValueSet_subset_scaleValueSet (a := a) ρ)
    (conditionalMinEntropyScaleValueSet_subset_dualValueSet (a := a) ρ)

/-- The endpoint dual-effect conic primal is feasible. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_nonempty
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet.Nonempty := by
  classical
  let Z : CMatrix (Sum (Prod a b) b) :=
    Matrix.fromBlocks 0 0 0 (1 : CMatrix b)
  refine ⟨(ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z, Z, ?_, rfl⟩
  constructor
  · have hZpsd : Z.PosSemidef := by
      simpa [Z] using
        (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
          (Matrix.PosSemidef.zero : (0 : CMatrix (Prod a b)).PosSemidef)
          (Matrix.PosSemidef.one : (1 : CMatrix b).PosSemidef))
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd
  · change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
      (1 : CMatrix b)
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, Matrix.sumBlock11,
      Matrix.sumBlock22, partialTraceA]

/-- A concrete scale-feasible point bounds the dual-effect primal value set
above. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_bddAbove
    [Nonempty b] (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet := by
  rcases ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨v, hv⟩
  rcases hv with ⟨T, hT, rfl⟩
  exact (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet_bddAbove_of_dualFeasible
    (conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible (a := a) hT)

/-- The block SDP constraint preserves trace: `Tr(Tr_A Z₁₁ + Z₂₂) = Tr Z`. -/
theorem conditionalMinEntropyDualEffectConstraint_trace_re
    (Z : CMatrix (Sum (Prod a b) b)) :
    ((conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z).trace).re =
      Z.trace.re := by
  have hptr :
      (partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z)).trace =
        (Matrix.sumBlock11 Z).trace :=
    partialTraceA_trace (a := a) (b := b) (Matrix.sumBlock11 Z)
  have hsplit :
      Z.trace = (Matrix.sumBlock11 Z).trace + (Matrix.sumBlock22 Z).trace := by
    simp [Matrix.trace, Matrix.sumBlock11, Matrix.sumBlock22,
      Fintype.sum_sum_type, add_comm]
  calc
    ((conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z).trace).re =
        ((partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z) +
            Matrix.sumBlock22 Z).trace).re := rfl
    _ = ((partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z)).trace +
          (Matrix.sumBlock22 Z).trace).re := by
      rw [Matrix.trace_add]
    _ = ((Matrix.sumBlock11 Z).trace + (Matrix.sumBlock22 Z).trace).re := by
      rw [hptr]
    _ = Z.trace.re := by rw [hsplit]

set_option maxHeartbeats 900000 in
/-- The dual-effect primal hypograph is closed.  The key finite-dimensional
estimate is that PSD block variables are norm-bounded by the trace of their
constraint value. -/
theorem conditionalMinEntropyDualEffectProgram_hasClosedPrimalHypograph
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).HasClosedPrimalHypograph := by
  classical
  let P := ρ.conditionalMinEntropyDualEffectProgram (a := a)
  refine IsSeqClosed.isClosed ?_
  intro ztSeq zt hztSeq hztLim
  choose Z hZK hA ht using hztSeq
  have hYLim : Tendsto (fun n => (ztSeq n).1) atTop (𝓝 zt.1) :=
    continuous_fst.tendsto zt |>.comp hztLim
  have hYBounded : Bornology.IsBounded (Set.range fun n => (ztSeq n).1) :=
    Metric.isBounded_range_of_tendsto _ hYLim
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le hYBounded
  have hC_nonneg : 0 ≤ C := by
    exact (norm_nonneg ((ztSeq 0).1)).trans (hC ((ztSeq 0).1) (Set.mem_range_self 0))
  let trCLM : CMatrix b →L[ℝ] ℝ :=
    conditionalMinEntropyTracePairingCLM (1 : CMatrix b)
  let oneZ : CMatrix (Sum (Prod a b) b) := 1
  have hZ_norm_le (n : ℕ) :
      ‖Z n‖ ≤ ((‖trCLM‖ * C) * ‖oneZ‖) := by
    have hZpsd : (Z n).PosSemidef := by
      simpa [P, conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZK n
    have hnormZ :=
      norm_le_trace_re_mul_norm_one_of_posSemidef (a := Sum (Prod a b) b) hZpsd
    have htrace_eq :
        (Z n).trace.re = ((ztSeq n).1).trace.re := by
      have hconstraint :
          (ztSeq n).1 = conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) (Z n) := by
        simpa [P, conditionalMinEntropyDualEffectProgram] using hA n
      rw [hconstraint]
      exact (conditionalMinEntropyDualEffectConstraint_trace_re (a := a) (b := b) (Z n)).symm
    have htrace_abs :
        ((ztSeq n).1).trace.re ≤ ‖trCLM ((ztSeq n).1)‖ := by
      change ((ztSeq n).1).trace.re ≤ ‖conditionalMinEntropyTracePairingCLM
        (1 : CMatrix b) ((ztSeq n).1)‖
      rw [conditionalMinEntropyTracePairingCLM_apply]
      simp
      exact le_abs_self _
    have hop :
        ‖trCLM ((ztSeq n).1)‖ ≤ ‖trCLM‖ * ‖(ztSeq n).1‖ :=
      trCLM.le_opNorm ((ztSeq n).1)
    have hYnorm : ‖(ztSeq n).1‖ ≤ C :=
      hC ((ztSeq n).1) (Set.mem_range_self n)
    have htrace_le :
        ((ztSeq n).1).trace.re ≤ ‖trCLM‖ * C := by
      calc
        ((ztSeq n).1).trace.re ≤ ‖trCLM ((ztSeq n).1)‖ := htrace_abs
        _ ≤ ‖trCLM‖ * ‖(ztSeq n).1‖ := hop
        _ ≤ ‖trCLM‖ * C := by
          exact mul_le_mul_of_nonneg_left hYnorm (norm_nonneg trCLM)
    calc
      ‖Z n‖ ≤ (Z n).trace.re * ‖(1 : CMatrix (Sum (Prod a b) b))‖ := hnormZ
      _ = ((ztSeq n).1).trace.re * ‖oneZ‖ := by
        rw [htrace_eq]
      _ ≤ (‖trCLM‖ * C) * ‖oneZ‖ := by
        exact mul_le_mul_of_nonneg_right htrace_le (norm_nonneg oneZ)
  have hZ_bounded : Bornology.IsBounded (Set.range Z) :=
    (isBounded_iff_forall_norm_le).2
      ⟨((‖trCLM‖ * C) * ‖oneZ‖), by
        rintro _ ⟨n, rfl⟩
        exact hZ_norm_le n⟩
  obtain ⟨Zlim, -, φ, hφ, hZtend⟩ :=
    tendsto_subseq_of_bounded hZ_bounded (x := Z) (fun n => Set.mem_range_self n)
  have hZlimK : Zlim ∈ P.K :=
    P.K.isClosed.mem_of_tendsto hZtend
      (Eventually.of_forall fun n => hZK (φ n))
  have hYLimSub : Tendsto (fun n => (ztSeq (φ n)).1) atTop (𝓝 zt.1) :=
    hYLim.comp hφ.tendsto_atTop
  have hAZlim :
      Tendsto (fun n => (ztSeq (φ n)).1) atTop (𝓝 (P.A Zlim)) := by
    have hcont :
        Tendsto (fun n => P.A (Z (φ n))) atTop (𝓝 (P.A Zlim)) :=
      P.A.continuous.continuousAt.tendsto.comp hZtend
    have hfun :
        (fun n => (ztSeq (φ n)).1) = fun n => P.A (Z (φ n)) := by
      funext n
      exact hA (φ n)
    simpa [hfun] using hcont
  have hAeq : zt.1 = P.A Zlim :=
    tendsto_nhds_unique hYLimSub hAZlim
  have htLimSub : Tendsto (fun n => (ztSeq (φ n)).2) atTop (𝓝 zt.2) :=
    (continuous_snd.tendsto zt |>.comp hztLim).comp hφ.tendsto_atTop
  have hValueLim :
      Tendsto (fun n => P.primalValue (Z (φ n))) atTop
        (𝓝 (P.primalValue Zlim)) :=
    P.c.continuous.continuousAt.tendsto.comp hZtend
  have htle : zt.2 ≤ P.primalValue Zlim :=
    le_of_tendsto_of_tendsto' htLimSub hValueLim fun n => ht (φ n)
  exact ⟨Zlim, hZlimK, hAeq, htle⟩

/-- Endpoint min-entropy scale strong duality in value-set form.

The unnormalized side-operator infimum equals the supremum over dual effects
`M ≥ 0` satisfying `Tr_A M ≤ I`. -/
theorem conditionalMinEntropyScale_eq_sSup_dualEffectValueSet [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale (a := a) =
      sSup (ρ.conditionalMinEntropyDualEffectValueSet (a := a)) := by
  classical
  let P := ρ.conditionalMinEntropyDualEffectProgram (a := a)
  have hsd :
      sSup P.primalValueSet = sInf P.dualValueSet :=
    P.sSup_primalValueSet_eq_sInf_dualValueSet_of_hasClosedPrimalHypograph
      (conditionalMinEntropyDualEffectProgram_hasClosedPrimalHypograph (a := a) ρ)
      (conditionalMinEntropyDualEffectProgram_primalValueSet_nonempty (a := a) ρ)
      (conditionalMinEntropyDualEffectProgram_primalValueSet_bddAbove (a := a) ρ)
  have hpr :
      P.primalValueSet = ρ.conditionalMinEntropyDualEffectValueSet (a := a) :=
    conditionalMinEntropyDualEffectProgram_primalValueSet_eq (a := a) ρ
  have hdu :
      P.dualValueSet = ρ.conditionalMinEntropyScaleValueSet (a := a) :=
    conditionalMinEntropyDualEffectProgram_dualValueSet_eq_scaleValueSet (a := a) ρ
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  rw [← hdu, ← hsd, hpr]

theorem conditionalMinEntropyFeasible_scale_lower_bound [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (Fintype.card a : ℝ)⁻¹ ≤ Real.rpow 2 (-lam) := by
  have htrace := trace_re_le_of_le h
  have hleft : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hright :
      (((Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ).trace).re =
        Real.rpow 2 (-lam) * (Fintype.card a : ℝ) := by
    rw [Matrix.trace_smul]
    simp [identityTensorStateMatrix_trace_re (a := a) σ]
  rw [hleft, hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  rw [inv_le_iff_one_le_mul₀ hcard_pos]
  simpa [mul_comm] using htrace

theorem conditionalMinEntropyScaleFeasible_trace_lower_bound [Nonempty a]
    {ρ : State (Prod a b)} {T : CMatrix b}
    (h : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    (Fintype.card a : ℝ)⁻¹ ≤ T.trace.re := by
  have htrace := trace_re_le_of_le h.2
  have hleft : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hright :
      (Matrix.kronecker (1 : CMatrix a) T).trace.re =
        (Fintype.card a : ℝ) * T.trace.re := by
    rw [show Matrix.kronecker (1 : CMatrix a) T =
        Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T by rfl]
    rw [Matrix.trace_kronecker, Matrix.trace_one]
    simp [Complex.mul_re]
  rw [hleft, hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  rw [inv_le_iff_one_le_mul₀ hcard_pos]
  simpa [mul_comm] using htrace

/-- Feasible conditional-min exponents. -/
def conditionalMinEntropyFeasibleExponentValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {lam : ℝ | ∃ σ : State b, ConditionalMinEntropyFeasible (a := a) ρ σ lam}

/-- The normalized scale values `2^{-λ}` coming from normalized
conditional-min feasible pairs. -/
def conditionalMinEntropyNormalizedScaleValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {t : ℝ | ∃ σ : State b, ∃ lam : ℝ,
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ∧ t = Real.rpow 2 (-lam)}

/-- The infimum of normalized conditional-min scale values. -/
def conditionalMinEntropyNormalizedScale (ρ : State (Prod a b)) : ℝ :=
  sInf (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a))

theorem conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet
    [Nonempty a] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) =
      ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a) := by
  ext t
  constructor
  · rintro ⟨T, hTfeas, rfl⟩
    have htr_lower :
        (Fintype.card a : ℝ)⁻¹ ≤ T.trace.re :=
      conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hTfeas
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have htr_pos : 0 < T.trace.re := lt_of_lt_of_le (inv_pos.mpr hcard_pos) htr_lower
    let σ : State b := ofPosSemidefTracePos T hTfeas.1 htr_pos
    let lam : ℝ := -log2 T.trace.re
    refine ⟨σ, lam, ?_, ?_⟩
    · rw [ConditionalMinEntropyFeasible]
      have hrpow : Real.rpow 2 (-lam) = T.trace.re := by
        dsimp [lam]
        rw [neg_neg]
        change Real.rpow 2 (log2 T.trace.re) = T.trace.re
        exact rpow_two_log2_pos htr_pos
      have hside :
          ((T.trace.re : ℂ) • identityTensorStateMatrix (a := a) σ) =
            Matrix.kronecker (1 : CMatrix a) T := by
        rw [identityTensorStateMatrix]
        rw [show Matrix.kronecker (1 : CMatrix a) T =
            Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T by rfl]
        change ((T.trace.re : ℂ) •
            Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) σ.matrix) =
          Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T
        rw [← Matrix.kronecker_smul]
        rw [show ((T.trace.re : ℂ) • σ.matrix) = T by
          exact smul_ofPosSemidefTracePos_matrix T hTfeas.1 htr_pos]
      rw [hrpow, hside]
      exact hTfeas.2
    · dsimp [lam]
      rw [neg_neg]
      change T.trace.re = Real.rpow 2 (log2 T.trace.re)
      exact (rpow_two_log2_pos htr_pos).symm
  · rintro ⟨σ, lam, hfeas, rfl⟩
    refine ⟨((Real.rpow 2 (-lam) : ℂ) • σ.matrix), ?_, ?_⟩
    · exact conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas
    · exact (trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas).symm

theorem conditionalMinEntropyScale_eq_normalizedScale
    [Nonempty a] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale (a := a) =
      ρ.conditionalMinEntropyNormalizedScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet, conditionalMinEntropyNormalizedScale,
    conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]

theorem conditionalMinEntropyFeasibleExponentValueSet_nonempty [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)).Nonempty := by
  exact ⟨-log2 (Fintype.card b : ℝ), maximallyMixed b,
    ρ.conditionalMinEntropyFeasible_maximallyMixed (a := a)⟩

theorem conditionalMinEntropyNormalizedScaleValueSet_nonempty [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty := by
  refine ⟨Real.rpow 2 (-(-log2 (Fintype.card b : ℝ))), maximallyMixed b,
    -log2 (Fintype.card b : ℝ), ?_, rfl⟩
  exact ρ.conditionalMinEntropyFeasible_maximallyMixed (a := a)

theorem conditionalMinEntropyNormalizedScaleValueSet_pos
    {ρ : State (Prod a b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) :
    0 < t := by
  rcases ht with ⟨σ, lam, hfeas, rfl⟩
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lam)

theorem conditionalMinEntropyNormalizedScaleValueSet_bddBelow
    (ρ : State (Prod a b)) :
    BddBelow (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) := by
  refine ⟨0, ?_⟩
  intro t ht
  exact le_of_lt (conditionalMinEntropyNormalizedScaleValueSet_pos (a := a) ht)

/-- Enlarging the conditioning register by an isometry cannot increase the
unnormalized conditional-min endpoint scale.  This is the easy direction of
isometric invariance: every old side operator `T_B` pushes forward to a feasible
side operator `V T_B V†` with the same trace. -/
theorem conditionalMinEntropyScale_conditioningIsometryApply_le
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddNew :
      BddBelow ((ρ.conditioningIsometryApply V).conditionalMinEntropyScaleValueSet
        (a := a)) := by
    rw [conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
    exact (ρ.conditioningIsometryApply V).conditionalMinEntropyNormalizedScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbddNew
    ⟨MatrixMap.ofReferenceIsometry V T,
      hT.apply_conditioningIsometry V,
      (trace_ofReferenceIsometry_apply V T).symm⟩

/-- For the concrete `B ↪ extra ⊕ B` padding used by embedded purification
transport, the conditional-min endpoint scale also cannot increase when
compressing back to the original summand. -/
theorem conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScale
        (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf
    ((ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScaleValueSet_nonempty
      (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddOld : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) := by
    rw [conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
  exact le_trans
    (csInf_le hbddOld
      ⟨Matrix.sumBlock22 TPlus, hTPlus.compress_sumInr, rfl⟩)
    (sumBlock22_trace_re_le_of_posSemidef TPlus hTPlus.1)

theorem conditionalMinEntropyNormalizedScaleValueSet_lower_bound [Nonempty a]
    {ρ : State (Prod a b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) :
    (Fintype.card a : ℝ)⁻¹ ≤ t := by
  rcases ht with ⟨σ, lam, hfeas, rfl⟩
  exact conditionalMinEntropyFeasible_scale_lower_bound (a := a) hfeas

theorem conditionalMinEntropyNormalizedScale_inf_pos [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    0 < ρ.conditionalMinEntropyNormalizedScale (a := a) := by
  have hne := ρ.conditionalMinEntropyNormalizedScaleValueSet_nonempty (a := a)
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hbound :
      ∀ t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a),
        (Fintype.card a : ℝ)⁻¹ ≤ t := by
    intro t ht
    exact conditionalMinEntropyNormalizedScaleValueSet_lower_bound (a := a) ht
  exact lt_of_lt_of_le (inv_pos.mpr hcard_pos) (le_csInf hne hbound)

theorem negLog2_image_conditionalMinEntropyNormalizedScaleValueSet_eq
    (ρ : State (Prod a b)) :
    (fun t : ℝ => -log2 t) ''
        ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a) =
      ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a) := by
  ext lam
  constructor
  · rintro ⟨t, ⟨σ, mu, hfeas, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    convert hfeas using 1
    exact neg_log2_rpow_two_neg mu
  · rintro ⟨σ, hfeas⟩
    refine ⟨Real.rpow 2 (-lam), ?_, ?_⟩
    · exact ⟨σ, lam, hfeas, rfl⟩
    · exact neg_log2_rpow_two_neg lam

theorem conditionalMinEntropy_eq_neg_log2_normalizedScale
    (ρ : State (Prod a b))
    (hne : (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty)
    (hbdd : BddBelow (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)))
    (hinf_pos : 0 < ρ.conditionalMinEntropyNormalizedScale (a := a)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) := by
  rw [conditionalMinEntropy, conditionalMinEntropyNormalizedScale]
  change sSup (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) =
    -log2 (sInf (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)))
  rw [← negLog2_image_conditionalMinEntropyNormalizedScaleValueSet_eq]
  exact neg_log2_sInf_image_eq hne hbdd hinf_pos

theorem conditionalMinEntropy_eq_neg_log2_normalizedScale_of_inf_pos
    (ρ : State (Prod a b))
    (hne : (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty)
    (hinf_pos : 0 < ρ.conditionalMinEntropyNormalizedScale (a := a)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) :=
  ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale hne
    (ρ.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)) hinf_pos

theorem conditionalMinEntropy_eq_neg_log2_normalizedScale_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) :=
  ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale_of_inf_pos
    (ρ.conditionalMinEntropyNormalizedScaleValueSet_nonempty (a := a))
    (ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a))

theorem conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyScale (a := a)) := by
  rw [ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale_of_nonempty (a := a),
    ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]

/-- A normalized finite-dimensional conditional min-entropy is bounded above by
the logarithm of the conditioned register dimension. -/
theorem conditionalMinEntropy_le_log2_card_left
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) := by
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hscale_lb :
      (Fintype.card a : ℝ)⁻¹ ≤ ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a),
      conditionalMinEntropyNormalizedScale]
    exact le_csInf
      (ρ.conditionalMinEntropyNormalizedScaleValueSet_nonempty (a := a))
      (fun t ht => conditionalMinEntropyNormalizedScaleValueSet_lower_bound (a := a) ht)
  rw [ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  unfold log2
  have hlog := Real.log_le_log (inv_pos.mpr hcard_pos) hscale_lb
  have hlog_inv :
      Real.log ((Fintype.card a : ℝ)⁻¹) = -Real.log (Fintype.card a : ℝ) := by
    rw [Real.log_inv]
  rw [hlog_inv] at hlog
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdiv :=
    div_le_div_of_nonneg_right hlog (le_of_lt hlog2_pos)
  simpa [neg_div] using neg_le_neg hdiv

/-- One entropy-level consequence of the scale pushforward: applying an
isometry to the conditioning register cannot decrease the conditional
min-entropy.  The reverse inequality requires compressing side operators back
to the isometry range, and is left as the remaining equality direction. -/
theorem conditionalMinEntropy_le_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    ρ.conditionalMinEntropy ≤
      (ρ.conditioningIsometryApply V).conditionalMinEntropy := by
  rw [ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    (ρ.conditioningIsometryApply V).conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
      (a := a)]
  have hle := ρ.conditionalMinEntropyScale_conditioningIsometryApply_le (a := a) V
  have hnew_pos : 0 < (ρ.conditioningIsometryApply V).conditionalMinEntropyScale
      (a := a) := by
    rw [(ρ.conditioningIsometryApply V).conditionalMinEntropyScale_eq_normalizedScale
      (a := a)]
    exact (ρ.conditioningIsometryApply V).conditionalMinEntropyNormalizedScale_inf_pos
      (a := a)
  unfold log2
  have hlog :
      Real.log ((ρ.conditioningIsometryApply V).conditionalMinEntropyScale (a := a)) /
          Real.log 2 ≤
        Real.log (ρ.conditionalMinEntropyScale (a := a)) / Real.log 2 := by
    exact div_le_div_of_nonneg_right (Real.log_le_log hnew_pos hle)
      (le_of_lt (Real.log_pos one_lt_two))
  simpa using (neg_le_neg hlog)

/-- For the concrete right-summand padding `B ↪ extra ⊕ B`, conditional
min-entropy also cannot increase. -/
theorem conditionalMinEntropy_conditioningIsometryApply_sumInr_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy ≤
      ρ.conditionalMinEntropy := by
  rw [(ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
      (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hle := ρ.conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    (a := a) (extra := extra)
  have hold_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  have hlog :
      Real.log (ρ.conditionalMinEntropyScale (a := a)) / Real.log 2 ≤
        Real.log
          ((ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScale
            (a := a)) / Real.log 2 := by
    exact div_le_div_of_nonneg_right (Real.log_le_log hold_pos hle)
      (le_of_lt (Real.log_pos one_lt_two))
  simpa using (neg_le_neg hlog)

/-- Conditional min-entropy is invariant under the concrete right-summand
reference padding used by embedded purification-ball transport. -/
theorem conditionalMinEntropy_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy =
      ρ.conditionalMinEntropy := by
  exact le_antisymm
    (ρ.conditionalMinEntropy_conditioningIsometryApply_sumInr_le (a := a) (extra := extra))
    (ρ.conditionalMinEntropy_le_conditioningIsometryApply (a := a)
      (ReferenceIsometry.sumInr extra b))

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_exponent_eq_scale
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hscale :
      ρ.conditionalMaxEntropyExponent (a := a) =
        ρ.conditionalMinEntropyScale (a := a)) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    hscale]
  simp

/-- Order-theoretic endpoint weak-duality bridge.

It remains to prove the source-shaped pointwise matrix inequality. Once every
max-entropy exponent candidate is bounded by every feasible min-entropy side
operator trace, this theorem packages the `sSup ≤ sInf` step. -/
theorem conditionalMaxEntropyExponent_le_minEntropyScale_of_pointwise_le
    [Nonempty b] (ρ : State (Prod a b))
    (hpoint : ∀ σ : State b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤ T.trace.re) :
    ρ.conditionalMaxEntropyExponent (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMaxEntropyExponent, conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine csSup_le (ρ.conditionalMaxEntropyExponentValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro y hy
  rcases hy with ⟨T, hTfeas, rfl⟩
  exact hpoint σ T hTfeas

theorem conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_pointwise_le
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hpoint : ∀ σ : State b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤ T.trace.re) :
    ρ.conditionalMaxEntropyPositive ≤ -ρ.conditionalMinEntropy := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hpos := ρ.conditionalMaxEntropyExponent_pos (a := a)
  have hle := ρ.conditionalMaxEntropyExponent_le_minEntropyScale_of_pointwise_le
    (a := a) hpoint
  have hscale_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hpos hle)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Reverse endpoint order bridge: if every feasible unnormalized
conditional-min side operator has trace bounded by the max-entropy exponent,
then the min-entropy scale is bounded by that exponent.

This is deliberately only an order-theoretic assembly lemma.  The source-shaped
pure-state proof must still provide the pointwise matrix/SDP inequality used as
`hpoint`. -/
theorem conditionalMinEntropyScale_le_conditionalMaxEntropyExponent_of_feasible_le
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hpoint : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤ ρ.conditionalMaxEntropyExponent (a := a)) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  have hbdd : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) := by
    rw [ρ.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
  rcases ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨y, hy⟩
  calc
    sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)) ≤ y := csInf_le hbdd hy
    _ ≤ ρ.conditionalMaxEntropyExponent (a := a) := by
      rcases hy with ⟨T, hTfeas, rfl⟩
      exact hpoint T hTfeas

theorem neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_feasible_le
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hpoint : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤ ρ.conditionalMaxEntropyExponent (a := a)) :
    -ρ.conditionalMinEntropy ≤ ρ.conditionalMaxEntropyPositive := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hscale_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  have hle := ρ.conditionalMinEntropyScale_le_conditionalMaxEntropyExponent_of_feasible_le
    (a := a) hpoint
  have hexp_pos := ρ.conditionalMaxEntropyExponent_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hscale_pos hle)
    (le_of_lt (Real.log_pos one_lt_two))

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_endpoint_bounds
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hforward : ∀ σ : State b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤ ρ.conditionalMaxEntropyExponent (a := a)) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy :=
  le_antisymm
    (ρ.conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_pointwise_le
      (a := a) hforward)
    (ρ.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_feasible_le
      (a := a) hreverse)

theorem conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 ((Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a))) := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet (a := a)]

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρ.conditionalMinEntropyScale (a := a)) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy := by
  refine ρ.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_exponent_eq_scale
    (a := a) ?_
  rw [ρ.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet (a := a),
    hscale]

theorem conditionalMaxEntropy_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρ.conditionalMinEntropyScale (a := a)) :
    ρ.conditionalMaxEntropy = -ρ.conditionalMinEntropy := by
  rw [ρ.conditionalMaxEntropy_eq_positive (a := a)]
  exact ρ.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    (a := a) hscale

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_fidelity_endpoint_bounds
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hforward : ∀ σ : State b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        (Fintype.card a : ℝ) *
          ρ.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy := by
  refine ρ.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_endpoint_bounds
    (a := a) ?_ ?_
  · intro σ T hT
    rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
      (a := a) ρ σ]
    exact hforward σ T hT
  · intro T hT
    rw [ρ.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet (a := a)]
    exact hreverse T hT

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρAC.conditionalMinEntropyScale (a := a)) :
    ρAB.conditionalMaxEntropyPositive = -ρAC.conditionalMinEntropy := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    hscale]
  simp

theorem conditionalMaxEntropy_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρAC.conditionalMinEntropyScale (a := a)) :
    ρAB.conditionalMaxEntropy = -ρAC.conditionalMinEntropy := by
  rw [ρAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ρAB.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
    (a := a) ρAC hscale

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_endpoint_bounds
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ρAB.conditionalMaxEntropyPositive = -ρAC.conditionalMinEntropy := by
  have hle :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        ρAC.conditionalMinEntropyScale (a := a) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    rw [← mul_sSup_image_eq
      (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
      (ρAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos]
    refine csSup_le ?_ ?_
    · exact Set.Nonempty.image _ (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
    · intro x hx
      rcases hx with ⟨y, ⟨σ, rfl⟩, rfl⟩
      refine le_csInf (ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
      intro z hz
      rcases hz with ⟨T, hT, rfl⟩
      exact hforward σ T hT
  have hge :
      ρAC.conditionalMinEntropyScale (a := a) ≤
        (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hbdd : BddBelow (ρAC.conditionalMinEntropyScaleValueSet (a := a)) := by
      rw [ρAC.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
      exact ρAC.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
    rcases ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨z, hz⟩
    calc
      sInf (ρAC.conditionalMinEntropyScaleValueSet (a := a)) ≤ z := csInf_le hbdd hz
      _ ≤ (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
          rcases hz with ⟨T, hT, rfl⟩
          exact hreverse T hT
  exact
    ρAB.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
      (a := a) ρAC (le_antisymm hle hge)

/-- Cross-register endpoint weak-duality direction.

For complementary pure marginals, the missing SDP/fidelity proof is expected to
provide `hforward`.  This theorem packages only the order-theoretic
`sSup ≤ sInf` and logarithm transport, keeping the exact remaining proof
obligation visible. -/
theorem conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re) :
    ρAB.conditionalMaxEntropyPositive ≤ -ρAC.conditionalMinEntropy := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hle :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        ρAC.conditionalMinEntropyScale (a := a) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    rw [← mul_sSup_image_eq
      (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
      (ρAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos]
    refine csSup_le ?_ ?_
    · exact Set.Nonempty.image _ (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty
        (a := a))
    · intro x hx
      rcases hx with ⟨y, ⟨σ, rfl⟩, rfl⟩
      refine le_csInf (ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
      intro z hz
      rcases hz with ⟨T, hT, rfl⟩
      exact hforward σ T hT
  have hleft_pos :
      0 < (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ρAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ρAB.conditionalMaxEntropyExponent_pos (a := a)
  have hscale_pos : 0 < ρAC.conditionalMinEntropyScale (a := a) := by
    rw [ρAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hleft_pos hle)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Cross-register endpoint reverse-duality direction under a strong pointwise
side-operator hypothesis.

This wrapper is retained for local order-theoretic reuse, but its hypothesis is
stronger than the source endpoint SDP: feasible side operators can be scaled, so
the source-faithful reverse direction should usually use
`neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound`
instead. -/
theorem neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_fidelity_reverse_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hreverse : ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ρAC.conditionalMinEntropy ≤ ρAB.conditionalMaxEntropyPositive := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hge :
      ρAC.conditionalMinEntropyScale (a := a) ≤
        (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hbdd : BddBelow (ρAC.conditionalMinEntropyScaleValueSet (a := a)) := by
      rw [ρAC.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
      exact ρAC.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
    rcases ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨z, hz⟩
    calc
      sInf (ρAC.conditionalMinEntropyScaleValueSet (a := a)) ≤ z := csInf_le hbdd hz
      _ ≤ (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
          rcases hz with ⟨T, hT, rfl⟩
          exact hreverse T hT
  have hscale_pos : 0 < ρAC.conditionalMinEntropyScale (a := a) := by
    rw [ρAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  have hright_pos :
      0 < (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ρAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ρAB.conditionalMaxEntropyExponent_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hscale_pos hge)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Correct reverse endpoint order bridge through the dual-effect SDP.

Unlike a pointwise bound on every feasible side operator `T`, this hypothesis
is stable under scaling: it bounds the linear dual-effect objective
`Tr(ρ_AC M)` for every effect `M ≥ 0`, `Tr_A M ≤ I`.  The already-proved
endpoint strong duality
`conditionalMinEntropyScale_eq_sSup_dualEffectValueSet` then converts this
into the required scale bound. -/
theorem neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hdual : ∀ M : CMatrix (Prod a c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ρAC.conditionalMinEntropy ≤ ρAB.conditionalMaxEntropyPositive := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hne :
      (ρAC.conditionalMinEntropyDualEffectValueSet (a := a)).Nonempty :=
    ρAC.conditionalMinEntropyDualEffectValueSet_nonempty (a := a)
  have hscale_le :
      ρAC.conditionalMinEntropyScale (a := a) ≤
        (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [ρAC.conditionalMinEntropyScale_eq_sSup_dualEffectValueSet (a := a)]
    refine csSup_le hne ?_
    intro y hy
    rcases hy with ⟨M, hM, rfl⟩
    exact hdual M hM
  have hscale_pos : 0 < ρAC.conditionalMinEntropyScale (a := a) := by
    rw [ρAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  have hright_pos :
      0 < (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ρAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ρAB.conditionalMaxEntropyExponent_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hscale_pos hscale_le)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Value-set version of the reverse endpoint bound through dual effects. -/
theorem sSup_conditionalMinEntropyDualEffectValueSet_le_card_mul_sSup_fidelityValueSet_of_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hdual : ∀ M : CMatrix (Prod a c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    sSup (ρAC.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  refine csSup_le (ρAC.conditionalMinEntropyDualEffectValueSet_nonempty (a := a)) ?_
  intro y hy
  rcases hy with ⟨M, hM, rfl⟩
  exact hdual M hM

/-- Endpoint equality from the correct pair of one-sided bounds:
the forward side is the usual fidelity-vs-scale weak duality, while the
reverse side is stated through the dual-effect objective rather than through
arbitrarily scalable feasible side operators. -/
theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_forward_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re)
    (hdual : ∀ M : CMatrix (Prod a c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ρAB.conditionalMaxEntropyPositive = -ρAC.conditionalMinEntropy :=
  le_antisymm
    (ρAB.conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
      (a := a) ρAC hforward)
    (ρAB.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
      (a := a) ρAC hdual)

end State

namespace SubnormalizedState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Every subnormalized finite-dimensional state is bounded above by the
identity operator. -/
theorem matrix_le_one (ρ : SubnormalizedState a) :
    ρ.matrix ≤ 1 := by
  have htrace :
      ρ.matrix ≤ (((ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) :=
    State.posSemidef_le_trace_re_smul_one ρ.pos
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

/-! ## Subnormalized conditional min-entropy scale -/

/-- Feasibility for the raw side-operator form of subnormalized conditional
min-entropy:
`ρ_AB ≤ I_A ⊗ T_B`, with `T_B ≥ 0`. -/
def ConditionalMinEntropyScaleFeasible
    (ρ : SubnormalizedState (Prod a b)) (T : CMatrix b) : Prop :=
  T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T

@[simp]
theorem ConditionalMinEntropyScaleFeasible_eq
    (ρ : SubnormalizedState (Prod a b)) (T : CMatrix b) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ↔
      T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T :=
  Iff.rfl

/-- Conditioning-register isometries transport raw subnormalized
conditional-min feasible side operators. -/
theorem ConditionalMinEntropyScaleFeasible.apply_conditioningIsometry
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (V : ReferenceIsometry b bPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρ.conditioningIsometryApply V)
      (MatrixMap.ofReferenceIsometry V T) := by
  constructor
  · exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V) T hT.1
  · let Φ : MatrixMap (Prod a b) (Prod a bPlus) :=
      MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V)
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
    have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) hdiff
    change ((Matrix.kronecker (1 : CMatrix a)
        (MatrixMap.ofReferenceIsometry V T)) -
        (ρ.conditioningIsometryApply V).matrix).PosSemidef
    rw [conditioningIsometryApply_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    rw [MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]
    simp [Channel.idChannel, MatrixMap.ofKraus]

/-- For concrete right-summand padding, feasible enlarged side operators
compress back to feasible old side operators by taking the lower-right block. -/
theorem ConditionalMinEntropyScaleFeasible.compress_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ : SubnormalizedState (Prod a b)} {TPlus : CMatrix (Sum extra b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ (Matrix.sumBlock22 TPlus) := by
  constructor
  · exact Matrix.sumBlock22_posSemidef hT.1
  · have hsub := hT.2.submatrix (fun x : Prod a b => (x.1, Sum.inr x.2))
    change (Matrix.kronecker (1 : CMatrix a) (Matrix.sumBlock22 TPlus) -
      ρ.matrix).PosSemidef
    convert hsub using 1
    ext x y
    simp [Matrix.kronecker, Matrix.sumBlock22, conditioningIsometryApply_matrix,
      ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      ReferenceIsometry.sumInr, Matrix.mul_apply]

/-- Compressing an arbitrary concrete right-summand conditioning register
preserves raw subnormalized conditional-min feasibility. -/
theorem ConditionalMinEntropyScaleFeasible.conditioningSumInrCompressed
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρPlus : SubnormalizedState (Prod a (Sum extra b))}
    {TPlus : CMatrix (Sum extra b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρPlus TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρPlus.conditioningSumInrCompressed
      (MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus) := by
  constructor
  · exact (MatrixMap.sumInrBlockCompression_traceNonincreasingCP
      (extra := extra) (α := b)).mapsPositive TPlus hT.1
  · let Φ : MatrixMap (Prod a (Sum extra b)) (Prod a b) :=
      MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b))
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b))
        (Channel.idChannel a).completelyPositive
        (MatrixMap.sumInrBlockCompression_traceNonincreasingCP
          (extra := extra) (α := b)).completelyPositive
    have hdiff : (Matrix.kronecker (1 : CMatrix a) TPlus - ρPlus.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) TPlus - ρPlus.matrix) hdiff
    change (Matrix.kronecker (1 : CMatrix a)
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus) -
        ρPlus.conditioningSumInrCompressed.matrix).PosSemidef
    rw [conditioningSumInrCompressed_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    simp [Channel.idChannel, MatrixMap.ofKraus]

/-- The raw endpoint scale
`inf {Tr T_B | T_B ≥ 0, ρ_AB ≤ I_A ⊗ T_B}` for subnormalized states. -/
def conditionalMinEntropyScale (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sInf {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScale_eq (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- The raw side-operator scale values
`Tr T_B` with `T_B ≥ 0` and `ρ_AB ≤ I_A ⊗ T_B`. -/
def conditionalMinEntropyScaleValueSet (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScaleValueSet_eq (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) =
      {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

theorem conditionalMinEntropyScale_eq_sInf_scaleValueSet
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
  rfl

theorem conditionalMinEntropyScaleFeasible_trace_nonneg
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    0 ≤ T.trace.re :=
  (Matrix.PosSemidef.trace_nonneg hT.1).1

theorem conditionalMinEntropyScaleValueSet_nonempty
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditionalMinEntropyScaleValueSet (a := a)).Nonempty := by
  let T : CMatrix b := 1
  refine ⟨T.trace.re, T, ?_, rfl⟩
  constructor
  · exact Matrix.PosSemidef.one
  · simpa [T, Matrix.one_kronecker_one] using ρ.matrix_le_one

theorem conditionalMinEntropyScaleValueSet_nonneg
    {ρ : SubnormalizedState (Prod a b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyScaleValueSet (a := a)) :
    0 ≤ t := by
  rcases ht with ⟨T, hT, rfl⟩
  exact conditionalMinEntropyScaleFeasible_trace_nonneg (a := a) hT

theorem conditionalMinEntropyScaleValueSet_bddBelow
    (ρ : SubnormalizedState (Prod a b)) :
    BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) := by
  refine ⟨0, ?_⟩
  intro t ht
  exact conditionalMinEntropyScaleValueSet_nonneg (a := a) ht

theorem conditionalMinEntropyScale_nonneg
    (ρ : SubnormalizedState (Prod a b)) :
    0 ≤ ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  exact le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a))
    (fun t ht => conditionalMinEntropyScaleValueSet_nonneg (a := a) ht)

/-- Enlarging the conditioning register by an isometry cannot increase the raw
subnormalized conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_conditioningIsometryApply_le
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddNew :
      BddBelow ((ρ.conditioningIsometryApply V).conditionalMinEntropyScaleValueSet
        (a := a)) :=
    (ρ.conditioningIsometryApply V).conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbddNew
    ⟨MatrixMap.ofReferenceIsometry V T,
      hT.apply_conditioningIsometry V,
      (State.trace_ofReferenceIsometry_apply V T).symm⟩

/-- For concrete right-summand padding, the raw subnormalized conditional-min
endpoint scale also cannot decrease. -/
theorem conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScale
        (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf
    ((ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScaleValueSet_nonempty
      (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddOld : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
    ρ.conditionalMinEntropyScaleValueSet_bddBelow (a := a)
  exact le_trans
    (csInf_le hbddOld
      ⟨Matrix.sumBlock22 TPlus, hTPlus.compress_sumInr, rfl⟩)
    (State.sumBlock22_trace_re_le_of_posSemidef TPlus hTPlus.1)

/-- Compressing an arbitrary right-summand conditioning register cannot raise
the raw subnormalized conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_conditioningSumInrCompressed_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) :
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale (a := a) ≤
      ρPlus.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρPlus.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddCompressed :
      BddBelow
        (ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScaleValueSet
          (a := a)) :=
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  have htrace_le :
      ((MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus).trace.re) ≤
        TPlus.trace.re :=
    (MatrixMap.sumInrBlockCompression_traceNonincreasingCP
      (extra := extra) (α := b)).traceNonincreasing TPlus hTPlus.1
  exact le_trans
    (csInf_le hbddCompressed
      ⟨MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus,
        hTPlus.conditioningSumInrCompressed (a := a), rfl⟩)
    htrace_le

theorem conditionalMinEntropyScaleFeasible_trace_lower_bound [Nonempty a]
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    ρ.matrix.trace.re / (Fintype.card a : ℝ) ≤ T.trace.re := by
  have htrace := State.trace_re_le_of_le hT.2
  have hright :
      (Matrix.kronecker (1 : CMatrix a) T).trace.re =
        (Fintype.card a : ℝ) * T.trace.re := by
    rw [show Matrix.kronecker (1 : CMatrix a) T =
        Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T by rfl]
    rw [Matrix.trace_kronecker, Matrix.trace_one]
    simp [Complex.mul_re]
  rw [hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  exact (div_le_iff₀ hcard_pos).mpr (by simpa [mul_comm] using htrace)

theorem conditionalMinEntropyScale_pos_of_trace_pos [Nonempty a]
    {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    0 < ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  have hne := ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hbound :
      ∀ x ∈ ρ.conditionalMinEntropyScaleValueSet (a := a),
        ρ.matrix.trace.re / (Fintype.card a : ℝ) ≤ x := by
    intro x hx
    rcases hx with ⟨T, hT, rfl⟩
    exact conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hT
  exact lt_of_lt_of_le (div_pos hρ hcard_pos) (le_csInf hne hbound)

/-- Feasible conditional-min exponents for subnormalized states. -/
def conditionalMinEntropyFeasibleExponentValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {lam : ℝ | ∃ σ : SubnormalizedState b,
    ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropyFeasibleExponentValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a) =
      {lam : ℝ | ∃ σ : SubnormalizedState b,
        ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- A subnormalized conditional-min feasible pair gives a raw scale-feasible
side operator. Its trace may be smaller than `2^{-λ}` because the side state is
only subnormalized. -/
theorem conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ
      ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) := by
  constructor
  · have hscale : (0 : ℂ) ≤ ((Real.rpow 2 (-lam) : ℝ) : ℂ) := by
      exact_mod_cast (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam))
    exact Matrix.PosSemidef.smul σ.pos hscale
  · simpa [ConditionalMinEntropyFeasible, ConditionalMinEntropyScaleFeasible,
      identityTensorStateMatrix, Matrix.kronecker_smul] using h

theorem trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ}
    (_h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (((Real.rpow 2 (-lam) : ℂ) • σ.matrix).trace).re =
      Real.rpow 2 (-lam) * σ.matrix.trace.re := by
  rw [Matrix.trace_smul]
  simp [Complex.mul_re, σ.trace_im_zero]

theorem conditionalMinEntropyScaleValue_le_exponentScale_of_conditionalMinEntropyFeasible
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ} :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam →
      (((Real.rpow 2 (-lam) : ℂ) • σ.matrix).trace).re ≤ Real.rpow 2 (-lam) := by
  intro h
  rw [trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    (a := a) h]
  have hscale_nonneg : 0 ≤ Real.rpow 2 (-lam) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam)
  nlinarith [σ.trace_nonneg, σ.trace_le_one, hscale_nonneg]

theorem identityTensorStateMatrix_posSemidef (σ : SubnormalizedState b) :
    (identityTensorStateMatrix (a := a) σ).PosSemidef := by
  change (Matrix.kronecker (1 : CMatrix a) σ.matrix).PosSemidef
  exact Matrix.PosSemidef.one.kronecker σ.pos

/-- A positive-trace raw scale feasible side operator gives a subnormalized
conditional-min feasible exponent at `-log₂ Tr T`. -/
theorem ConditionalMinEntropyFeasible.of_scaleFeasible_trace_pos
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (htr : 0 < T.trace.re) :
    ConditionalMinEntropyFeasible (a := a) ρ
      (State.ofPosSemidefTracePos T hT.1 htr).toSubnormalized
      (-log2 T.trace.re) := by
  rw [ConditionalMinEntropyFeasible]
  have hrpow : Real.rpow 2 (-(-log2 T.trace.re)) = T.trace.re := by
    simpa using rpow_two_log2_pos htr
  have hside :
      ((T.trace.re : ℂ) •
          identityTensorStateMatrix (a := a)
            (State.ofPosSemidefTracePos T hT.1 htr).toSubnormalized) =
        Matrix.kronecker (1 : CMatrix a) T := by
    ext x y
    have htrC : ((T.trace.re : ℂ) ≠ 0) := by
      exact_mod_cast htr.ne'
    simp [identityTensorStateMatrix, State.toSubnormalized,
      State.ofPosSemidefTracePos, Matrix.kronecker, Matrix.kroneckerMap_apply]
    field_simp [htrC]
  rw [hrpow, hside]
  exact hT.2

theorem negLog2_image_conditionalMinEntropyScaleValueSet_eq_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b))
    (hρ : 0 < ρ.matrix.trace.re) :
    (fun t : ℝ => -log2 t) ''
        ρ.conditionalMinEntropyScaleValueSet (a := a) =
      ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a) := by
  ext lam
  constructor
  · rintro ⟨t, ⟨T, hT, rfl⟩, rfl⟩
    have htr_pos : 0 < T.trace.re := by
      have hcard_pos : 0 < (Fintype.card a : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
      exact lt_of_lt_of_le (div_pos hρ hcard_pos)
        (conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hT)
    exact ⟨(State.ofPosSemidefTracePos T hT.1 htr_pos).toSubnormalized,
      ConditionalMinEntropyFeasible.of_scaleFeasible_trace_pos (a := a) hT htr_pos⟩
  · rintro ⟨σ, hfeas⟩
    let c : ℝ := Real.rpow 2 (-lam)
    let m : State b := State.maximallyMixed b
    let pad : ℝ := c * (1 - σ.matrix.trace.re)
    let T : CMatrix b := (c : ℂ) • σ.matrix + (pad : ℂ) • m.matrix
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam)
    have hc_pos : 0 < c := by
      dsimp [c]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lam)
    have hpad_nonneg : 0 ≤ pad := by
      dsimp [pad]
      nlinarith [hc_nonneg, σ.trace_le_one]
    have hTpos : T.PosSemidef := by
      dsimp [T]
      exact Matrix.PosSemidef.add (Matrix.PosSemidef.smul σ.pos hc_nonneg)
        (Matrix.PosSemidef.smul m.pos hpad_nonneg)
    have hpad_id_pos :
        ((pad : ℂ) • identityTensorStateMatrix (a := a) m.toSubnormalized).PosSemidef := by
      have hpadC : (0 : ℂ) ≤ (pad : ℂ) := by exact_mod_cast hpad_nonneg
      exact Matrix.PosSemidef.smul
        (identityTensorStateMatrix_posSemidef (a := a) m.toSubnormalized) hpadC
    have hkr :
        Matrix.kronecker (1 : CMatrix a) T =
          (c : ℂ) • identityTensorStateMatrix (a := a) σ +
            (pad : ℂ) • identityTensorStateMatrix (a := a) m.toSubnormalized := by
      ext x y
      simp [T, identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
        State.toSubnormalized, mul_add]
      ring
    have hle :
        ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T := by
      refine le_trans hfeas ?_
      rw [hkr]
      exact le_add_of_nonneg_right (by simpa [Matrix.le_iff] using hpad_id_pos)
    have htr : T.trace.re = c := by
      dsimp [T, pad]
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, m.trace_eq_one]
      simp [Complex.real_smul, σ.trace_im_zero]
      ring
    refine ⟨T.trace.re, ?_, ?_⟩
    · exact ⟨T, ⟨hTpos, hle⟩, rfl⟩
    · rw [htr]
      exact neg_log2_rpow_two_neg lam

theorem conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b))
    (hρ : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyScale (a := a)) := by
  rw [conditionalMinEntropy, conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  change sSup (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) =
    -log2 (sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)))
  rw [← negLog2_image_conditionalMinEntropyScaleValueSet_eq_of_trace_pos (a := a) ρ hρ]
  exact neg_log2_sInf_image_eq
    (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a))
    (ρ.conditionalMinEntropyScaleValueSet_bddBelow (a := a))
    (ρ.conditionalMinEntropyScale_pos_of_trace_pos (a := a) hρ)

/-- Compressing an arbitrary right-summand conditioning register can only
increase subnormalized conditional min-entropy, when both traces are positive. -/
theorem conditionalMinEntropy_le_conditioningSumInrCompressed
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b)))
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < ρPlus.conditioningSumInrCompressed.matrix.trace.re) :
    ρPlus.conditionalMinEntropy ≤
      ρPlus.conditioningSumInrCompressed.conditionalMinEntropy := by
  rw [ρPlus.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hPlus,
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hCompressed]
  have hscale_le :=
    ρPlus.conditionalMinEntropyScale_conditioningSumInrCompressed_le
      (a := a) (extra := extra)
  have hcompressed_pos :
      0 <
        ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale
          (a := a) :=
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) hCompressed
  have hlog :
      log2
          (ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale
            (a := a)) ≤
        log2 (ρPlus.conditionalMinEntropyScale (a := a)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hcompressed_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

/-- Subnormalized conditional min-entropy is invariant under the concrete
right-summand reference padding used by embedded purification-ball transport,
for positive-trace states. -/
theorem conditionalMinEntropy_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy =
      ρ.conditionalMinEntropy := by
  rw [(ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) (by
        rw [conditioningIsometryApply_trace_re]
        exact hρ),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hρ]
  have hle₁ := ρ.conditionalMinEntropyScale_conditioningIsometryApply_le
    (a := a) (V := ReferenceIsometry.sumInr extra b)
  have hle₂ := ρ.conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    (a := a) (extra := extra)
  rw [le_antisymm hle₁ hle₂]

/-- Exact concrete right-summand padding transports subnormalized
purified-distance balls. -/
theorem purifiedBall_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε σ) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).purifiedBall ε
      (σ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) := by
  simpa [conditioningIsometryApply] using
    (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ) (σ := σ) (ε := ε)
      (MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry (ReferenceIsometry.sumInr extra b)))
      (MatrixMap.traceNonincreasingCP_id_kron (a := a)
        (hΦ := MatrixMap.ofReferenceIsometry_traceNonincreasingCP
          (ReferenceIsometry.sumInr extra b)))
      hball)

/-- Compressing the concrete right-summand padding transports a purified ball
back to the source conditioning register. -/
theorem purifiedBall_conditioningSumInrCompressed_of_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ : SubnormalizedState (Prod a b)}
    {ρPlus : SubnormalizedState (Prod a (Sum extra b))} {ε : ℝ}
    (hball :
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).purifiedBall ε ρPlus) :
    ρ.purifiedBall ε ρPlus.conditioningSumInrCompressed := by
  have hcompressed :=
    SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b))
      (σ := ρPlus) (ε := ε)
      (MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b)))
      (MatrixMap.traceNonincreasingCP_id_kron (a := a)
        (hΦ := MatrixMap.sumInrBlockCompression_traceNonincreasingCP
          (extra := extra) (α := b)))
      hball
  change ((ρ.conditioningIsometryApply
      (ReferenceIsometry.sumInr extra b)).conditioningSumInrCompressed).purifiedBall ε
    ρPlus.conditioningSumInrCompressed at hcompressed
  simpa [conditioningSumInrCompressed_conditioningIsometryApply_sumInr] using hcompressed

/-! ## Subnormalized conditional max-entropy exponent -/

theorem psdSqrt_trace_re_pos_of_trace_pos [Nonempty a]
    {ρ : SubnormalizedState a} (hρ : 0 < ρ.matrix.trace.re) :
    0 < (psdSqrt ρ.matrix).trace.re := by
  have hnon : 0 ≤ (psdSqrt ρ.matrix).trace.re :=
    (Matrix.PosSemidef.trace_nonneg (psdSqrt_pos ρ.matrix)).1
  by_contra hnot
  have hle : (psdSqrt ρ.matrix).trace.re ≤ 0 := le_of_not_gt hnot
  have hre : (psdSqrt ρ.matrix).trace.re = 0 := le_antisymm hle hnon
  have htr : (psdSqrt ρ.matrix).trace = 0 := by
    apply Complex.ext
    · exact hre
    · exact (Matrix.PosSemidef.trace_nonneg (psdSqrt_pos ρ.matrix)).2.symm
  have hsqrt_zero : psdSqrt ρ.matrix = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (psdSqrt_pos ρ.matrix)).mp htr
  have hrho_zero : ρ.matrix = 0 := by
    rw [← psdSqrt_mul_self_of_posSemidef ρ.pos, hsqrt_zero]
    simp
  have htrace : ρ.matrix.trace.re = 0 := by simp [hrho_zero]
  linarith

/-- The raw squared-fidelity expression optimized by subnormalized
conditional max-entropy, before applying `log₂`. -/
def conditionalMaxEntropyExponentCandidate
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) : ℝ :=
  (traceNorm (psdSqrt ρ.matrix *
    psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2

@[simp]
theorem conditionalMaxEntropyExponentCandidate_eq
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    ρ.conditionalMaxEntropyExponentCandidate σ =
      (traceNorm (psdSqrt ρ.matrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 :=
  rfl

/-- The existing subnormalized conditional max-entropy candidate is the
logarithm of the raw endpoint candidate. -/
theorem conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    ρ.conditionalMaxEntropyFidelityCandidate σ =
      log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) :=
  rfl

omit [Fintype a] in
private theorem rightBlock_identityTensorStateMatrix
    (σ : SubnormalizedState b) (i j : a) :
    ReferenceIsometry.rightBlock (identityTensorStateMatrix (a := a) σ) i j =
      (((1 : CMatrix a) i j) • σ.matrix) := by
  ext x y
  simp [identityTensorStateMatrix, ReferenceIsometry.rightBlock,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

omit [Fintype a] in
@[simp]
theorem identityTensorStateMatrix_referenceIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (σ : SubnormalizedState b) (V : ReferenceIsometry b bPlus) :
    identityTensorStateMatrix (a := a) (σ.referenceIsometryApply V) =
      V.applyMatrixRight (identityTensorStateMatrix (a := a) σ) := by
  ext x y
  rw [ReferenceIsometry.applyMatrixRight]
  rw [rightBlock_identityTensorStateMatrix]
  simp [identityTensorStateMatrix, MatrixMap.ofReferenceIsometry_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

@[simp]
theorem identityTensorStateMatrix_sumInrCompressedSide
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (σPlus : SubnormalizedState (Sum extra b)) :
    identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide =
      MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b))
        (identityTensorStateMatrix (a := a) σPlus) := by
  ext x y
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [identityTensorStateMatrix, sumInrCompressedSide, MatrixMap.sumInrBlockCompression,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

omit [Fintype a] in
private theorem sumBlock22_identityTensorStateMatrix_submatrix_prodSumRightEquiv
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (σPlus : SubnormalizedState (Sum extra b)) :
    Matrix.sumBlock22 ((identityTensorStateMatrix (a := a) σPlus).submatrix
      (ReferenceIsometry.prodSumRightEquiv a extra b)
      (ReferenceIsometry.prodSumRightEquiv a extra b)) =
      identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide := by
  ext x y
  simp [Matrix.sumBlock22, ReferenceIsometry.prodSumRightEquiv,
    identityTensorStateMatrix, sumInrCompressedSide, MatrixMap.sumInrBlockCompression,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

private theorem sumBlock22_conditioning_matrix_submatrix_prodSumRightEquiv
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) :
    Matrix.sumBlock22 (ρPlus.matrix.submatrix
      (ReferenceIsometry.prodSumRightEquiv a extra b)
      (ReferenceIsometry.prodSumRightEquiv a extra b)) =
      ρPlus.conditioningSumInrCompressed.matrix := by
  ext x y
  rw [conditioningSumInrCompressed_matrix]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [Matrix.sumBlock22, ReferenceIsometry.prodSumRightEquiv,
    MatrixMap.sumInrBlockCompression]

/-- The raw trace-norm factor in subnormalized max entropy is unchanged when
the joint state is padded by `sumInr` and an arbitrary padded side candidate is
compressed back to the success block. -/
theorem traceNorm_conditioningIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState (Sum extra b)) :
    traceNorm
        (psdSqrt (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σPlus)) =
      traceNorm
        (psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide)) := by
  let V : ReferenceIsometry b (Sum extra b) := ReferenceIsometry.sumInr extra b
  let A : CMatrix (Prod a b) := psdSqrt ρ.matrix
  let Y : CMatrix (Prod a (Sum extra b)) := identityTensorStateMatrix (a := a) σPlus
  let Yc : CMatrix (Prod a b) :=
    identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide
  let VA : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight A
  let VYc : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight Yc
  let VsqrtYc : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight (psdSqrt Yc)
  have hleft_sqrt :
      psdSqrt (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix = VA := by
    dsimp [VA, V, A]
    rw [conditioningIsometryApply_matrix]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a) ρ.pos
  have hVA_h : Matrix.conjTranspose VA = VA := by
    rw [← hleft_sqrt]
    exact (psdSqrt_isHermitian
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix).eq
  have hsY_h : Matrix.conjTranspose (psdSqrt Y) = psdSqrt Y := by
    exact (psdSqrt_isHermitian Y).eq
  have hVsYc_h : Matrix.conjTranspose VsqrtYc = VsqrtYc := by
    dsimp [VsqrtYc, V]
    rw [← ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σPlus.sumInrCompressedSide)]
    exact (psdSqrt_isHermitian
      ((ReferenceIsometry.sumInr extra b).applyMatrixRight Yc)).eq
  have hYc_block :
      Matrix.sumBlock22 (Y.submatrix
        (ReferenceIsometry.prodSumRightEquiv a extra b)
        (ReferenceIsometry.prodSumRightEquiv a extra b)) = Yc := by
    dsimp [Y, Yc]
    exact sumBlock22_identityTensorStateMatrix_submatrix_prodSumRightEquiv
      (a := a) σPlus
  have hM :
      (VA * psdSqrt Y) * Matrix.conjTranspose (VA * psdSqrt Y) =
        VA * Y * VA := by
    rw [Matrix.conjTranspose_mul, hsY_h, hVA_h]
    have hsqY : psdSqrt Y * psdSqrt Y = Y := by
      dsimp [Y]
      exact psdSqrt_mul_self_of_posSemidef
        (identityTensorStateMatrix_posSemidef (a := a) σPlus)
    calc
      (VA * psdSqrt Y) * (psdSqrt Y * VA) =
          VA * (psdSqrt Y * psdSqrt Y) * VA := by
            simp [Matrix.mul_assoc]
      _ = VA * Y * VA := by rw [hsqY]
  have hN :
      (VA * VsqrtYc) * Matrix.conjTranspose (VA * VsqrtYc) =
        VA * VYc * VA := by
    rw [Matrix.conjTranspose_mul, hVsYc_h, hVA_h]
    have hsq : VsqrtYc * VsqrtYc = VYc := by
      dsimp [VsqrtYc, VYc, V, Yc]
      rw [ReferenceIsometry.applyMatrixRight_mul]
      rw [psdSqrt_mul_self_of_posSemidef
        (identityTensorStateMatrix_posSemidef (a := a) σPlus.sumInrCompressedSide)]
    calc
      (VA * VsqrtYc) * (VsqrtYc * VA) =
          VA * (VsqrtYc * VsqrtYc) * VA := by
            simp [Matrix.mul_assoc]
      _ = VA * VYc * VA := by rw [hsq]
  have hMN :
      (VA * psdSqrt Y) * Matrix.conjTranspose (VA * psdSqrt Y) =
        (VA * VsqrtYc) * Matrix.conjTranspose (VA * VsqrtYc) := by
    rw [hM, hN]
    calc
      VA * Y * VA =
          V.applyMatrixRight (A * Yc * A) := by
            dsimp [VA, V, A, Y]
            rw [ReferenceIsometry.applyMatrixRight_sumInr_sandwich]
            rw [hYc_block]
      _ = VA * VYc * VA := by
            dsimp [VA, VYc, V]
            rw [ReferenceIsometry.applyMatrixRight_mul]
            rw [ReferenceIsometry.applyMatrixRight_mul]
  rw [hleft_sqrt]
  calc
    traceNorm (VA * psdSqrt Y) =
        traceNorm (VA * VsqrtYc) :=
          traceNorm_eq_of_mul_conjTranspose_eq hMN
    _ = traceNorm (V.applyMatrixRight (A * psdSqrt Yc)) := by
          dsimp [VA, VsqrtYc, V, A]
          rw [ReferenceIsometry.applyMatrixRight_mul]
    _ = traceNorm (A * psdSqrt Yc) := by
          dsimp [V]
          rw [ReferenceIsometry.traceNorm_applyMatrixRight_sumInr]
    _ = traceNorm (psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide)) := by
          rfl

/-- A right-summand-supported side candidate tests an arbitrary enlarged joint
state through exactly the compressed joint block. -/
theorem traceNorm_conditioningSumInrCompressed_mul_sqrt_identityTensorStateMatrix_referenceIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) (σ : SubnormalizedState b) :
    traceNorm
        (psdSqrt ρPlus.conditioningSumInrCompressed.matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σ)) =
      traceNorm
        (psdSqrt ρPlus.matrix *
          psdSqrt (identityTensorStateMatrix (a := a)
            (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)))) := by
  let V : ReferenceIsometry b (Sum extra b) := ReferenceIsometry.sumInr extra b
  let A : CMatrix (Prod a b) := psdSqrt ρPlus.conditioningSumInrCompressed.matrix
  let Y : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let VA : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight A
  let VsqrtY : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight (psdSqrt Y)
  have hside :
      psdSqrt (identityTensorStateMatrix (a := a)
          (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b))) =
        VsqrtY := by
    dsimp [VsqrtY, V, Y]
    rw [identityTensorStateMatrix_referenceIsometryApply]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σ)
  have hVA_h : Matrix.conjTranspose VA = VA := by
    dsimp [VA, V, A]
    change Matrix.conjTranspose
        ((ReferenceIsometry.sumInr extra b).applyMatrixRight
          (psdSqrt ρPlus.conditioningSumInrCompressed.matrix)) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight
        (psdSqrt ρPlus.conditioningSumInrCompressed.matrix)
    rw [← ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      ρPlus.conditioningSumInrCompressed.pos]
    exact (psdSqrt_isHermitian
      ((ReferenceIsometry.sumInr extra b).applyMatrixRight
        ρPlus.conditioningSumInrCompressed.matrix)).eq
  have hVsqrtY_h : Matrix.conjTranspose VsqrtY = VsqrtY := by
    dsimp [VsqrtY, V, Y]
    rw [← ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σ)]
    exact (psdSqrt_isHermitian
      ((ReferenceIsometry.sumInr extra b).applyMatrixRight Y)).eq
  have hVAA :
      VA * VA =
        V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix := by
    dsimp [VA, V, A]
    change (ReferenceIsometry.sumInr extra b).applyMatrixRight
        (psdSqrt ρPlus.conditioningSumInrCompressed.matrix) *
        (ReferenceIsometry.sumInr extra b).applyMatrixRight
          (psdSqrt ρPlus.conditioningSumInrCompressed.matrix) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight
        ρPlus.conditioningSumInrCompressed.matrix
    rw [ReferenceIsometry.applyMatrixRight_mul]
    rw [psdSqrt_mul_self_of_posSemidef ρPlus.conditioningSumInrCompressed.pos]
  have hsandwich :
      VsqrtY * ρPlus.matrix * VsqrtY =
        VsqrtY *
          (V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix) *
            VsqrtY := by
    calc
      VsqrtY * ρPlus.matrix * VsqrtY =
          V.applyMatrixRight
            (psdSqrt Y *
              Matrix.sumBlock22 (ρPlus.matrix.submatrix
                (ReferenceIsometry.prodSumRightEquiv a extra b)
                (ReferenceIsometry.prodSumRightEquiv a extra b)) *
              psdSqrt Y) := by
            dsimp [VsqrtY, V]
            rw [ReferenceIsometry.applyMatrixRight_sumInr_sandwich]
      _ = V.applyMatrixRight
            (psdSqrt Y * ρPlus.conditioningSumInrCompressed.matrix * psdSqrt Y) := by
            rw [sumBlock22_conditioning_matrix_submatrix_prodSumRightEquiv
              ρPlus]
      _ = VsqrtY *
          (V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix) *
            VsqrtY := by
            dsimp [VsqrtY, V]
            rw [ReferenceIsometry.applyMatrixRight_mul]
            rw [ReferenceIsometry.applyMatrixRight_mul]
  rw [← ReferenceIsometry.traceNorm_applyMatrixRight_sumInr
      (a := a) (extra := extra)
      (psdSqrt ρPlus.conditioningSumInrCompressed.matrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ))]
  rw [← ReferenceIsometry.applyMatrixRight_mul]
  change traceNorm (VA * VsqrtY) =
    traceNorm (psdSqrt ρPlus.matrix * psdSqrt (identityTensorStateMatrix (a := a)
      (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b))))
  rw [hside]
  apply traceNorm_eq_of_conjTranspose_mul_eq
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hVA_h, hVsqrtY_h]
  rw [psdSqrt_isHermitian ρPlus.matrix]
  calc
    VsqrtY * VA * (VA * VsqrtY) =
        VsqrtY * (VA * VA) * VsqrtY := by simp [Matrix.mul_assoc]
    _ = VsqrtY * (V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix) *
          VsqrtY := by rw [hVAA]
    _ = VsqrtY * ρPlus.matrix * VsqrtY := by rw [← hsandwich]
    _ = VsqrtY * psdSqrt ρPlus.matrix * (psdSqrt ρPlus.matrix * VsqrtY) := by
          have hsqrt :
              ρPlus.matrix = psdSqrt ρPlus.matrix * psdSqrt ρPlus.matrix :=
            (psdSqrt_mul_self_of_posSemidef ρPlus.pos).symm
          conv_lhs => rw [hsqrt]
          simp [Matrix.mul_assoc]

/-- Applying the same concrete right-summand padding to the joint state and the
side candidate preserves the subnormalized max-entropy exponent candidate. -/
theorem conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyExponentCandidate
        (a := a) (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)) =
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  rw [conditionalMaxEntropyExponentCandidate_eq, conditionalMaxEntropyExponentCandidate_eq]
  have hleft :
      psdSqrt (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix =
        (ReferenceIsometry.sumInr extra b).applyMatrixRight (psdSqrt ρ.matrix) := by
    rw [conditioningIsometryApply_matrix]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a) ρ.pos
  have hside :
      psdSqrt (identityTensorStateMatrix (a := a)
          (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b))) =
        (ReferenceIsometry.sumInr extra b).applyMatrixRight
          (psdSqrt (identityTensorStateMatrix (a := a) σ)) := by
    rw [identityTensorStateMatrix_referenceIsometryApply]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σ)
  rw [hleft, hside]
  rw [ReferenceIsometry.applyMatrixRight_mul]
  rw [ReferenceIsometry.traceNorm_applyMatrixRight_sumInr]

/-- A padded joint state tested against an arbitrary padded side candidate has
the same raw max-entropy exponent candidate as the source joint state tested
against the compressed side candidate. -/
theorem conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState (Sum extra b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyExponentCandidate
        (a := a) σPlus =
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σPlus.sumInrCompressedSide := by
  rw [conditionalMaxEntropyExponentCandidate_eq, conditionalMaxEntropyExponentCandidate_eq]
  rw [traceNorm_conditioningIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix]

/-- Testing an arbitrary enlarged joint state against a side candidate
supported on the right summand is exactly testing the compressed joint state. -/
theorem conditionalMaxEntropyExponentCandidate_conditioningSumInrCompressed_referenceIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) (σ : SubnormalizedState b) :
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyExponentCandidate
        (a := a) σ =
      ρPlus.conditionalMaxEntropyExponentCandidate (a := a)
        (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)) := by
  rw [conditionalMaxEntropyExponentCandidate_eq, conditionalMaxEntropyExponentCandidate_eq]
  rw [traceNorm_conditioningSumInrCompressed_mul_sqrt_identityTensorStateMatrix_referenceIsometryApply_sumInr]

/-- The logarithmic max-entropy candidate is unchanged after testing a padded
joint state against an arbitrary padded side candidate and compressing the side
candidate back to the source register. -/
theorem conditionalMaxEntropyFidelityCandidate_conditioningIsometryApply_sumInr_compressedSide
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState (Sum extra b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyFidelityCandidate
        (a := a) σPlus =
      ρ.conditionalMaxEntropyFidelityCandidate (a := a) σPlus.sumInrCompressedSide := by
  rw [conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
    conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
    conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide]

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²` for subnormalized side states. -/
def conditionalMaxEntropyExponentValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : SubnormalizedState b,
    x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

@[simp]
theorem conditionalMaxEntropyExponentValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyExponentValueSet (a := a) =
      {x : ℝ | ∃ σ : SubnormalizedState b,
        x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ} :=
  rfl

/-- Positive raw max-entropy exponent candidate values for subnormalized
states. The positivity filter is required for logarithmic endpoint bridges. -/
def conditionalMaxEntropyPositiveExponentValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : SubnormalizedState b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

@[simp]
theorem conditionalMaxEntropyPositiveExponentValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) =
      {x : ℝ | ∃ σ : SubnormalizedState b,
        0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
          x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ} :=
  rfl

/-- The positive-candidate raw endpoint exponent for subnormalized states. -/
def conditionalMaxEntropyPositiveExponent
    (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))

@[simp]
theorem conditionalMaxEntropyPositiveExponent_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveExponent =
      sSup (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) :=
  rfl

/-- Definition-level max-entropy candidates whose raw exponent is strictly
positive. -/
def conditionalMaxEntropyPositiveValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {h : ℝ | ∃ σ : SubnormalizedState b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = ρ.conditionalMaxEntropyFidelityCandidate σ}

@[simp]
theorem conditionalMaxEntropyPositiveValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) =
      {h : ℝ | ∃ σ : SubnormalizedState b,
        0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
          h = ρ.conditionalMaxEntropyFidelityCandidate σ} :=
  rfl

/-- Concrete right-summand padding preserves the positive raw endpoint exponent
candidate set for subnormalized max-entropy. -/
theorem conditionalMaxEntropyPositiveExponentValueSet_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveExponentValueSet
        (a := a) =
      ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
  ext x
  constructor
  · rintro ⟨σPlus, hpos, rfl⟩
    refine ⟨σPlus.sumInrCompressedSide, ?_, ?_⟩
    · rwa [← conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
    · rw [conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b), ?_, ?_⟩
    · rwa [conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
        (a := a) (extra := extra) ρ σ]
    · rw [conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
        (a := a) (extra := extra) ρ σ]

/-- Compatibility name for the positive-candidate subnormalized conditional
max-entropy. -/
def conditionalMaxEntropyPositive (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a))

@[simp]
theorem conditionalMaxEntropyPositive_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a)) :=
  rfl

/-- Concrete right-summand padding preserves the positive logarithmic
max-entropy candidate set. -/
theorem conditionalMaxEntropyPositiveValueSet_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveValueSet
        (a := a) =
      ρ.conditionalMaxEntropyPositiveValueSet (a := a) := by
  ext h
  constructor
  · rintro ⟨σPlus, hpos, rfl⟩
    refine ⟨σPlus.sumInrCompressedSide, ?_, ?_⟩
    · rwa [← conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
    · rw [conditionalMaxEntropyFidelityCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b), ?_, ?_⟩
    · rwa [conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
        (a := a) (extra := extra) ρ σ]
    · rw [conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
        conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
        conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr]

/-- Concrete right-summand padding preserves the positive raw endpoint exponent
for subnormalized max-entropy. -/
theorem conditionalMaxEntropyPositiveExponent_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveExponent
        (a := a) =
      ρ.conditionalMaxEntropyPositiveExponent (a := a) := by
  rw [conditionalMaxEntropyPositiveExponent_eq, conditionalMaxEntropyPositiveExponent_eq,
    conditionalMaxEntropyPositiveExponentValueSet_conditioningIsometryApply_sumInr]

/-- Concrete right-summand padding preserves subnormalized conditional
max-entropy. -/
theorem conditionalMaxEntropy_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropy =
      ρ.conditionalMaxEntropy := by
  change sSup ((ρ.conditioningIsometryApply
      (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveValueSet (a := a)) =
    sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a))
  rw [conditionalMaxEntropyPositiveValueSet_conditioningIsometryApply_sumInr]

/-- Exact-padding smooth min-entropy candidates: the smoothing witness lives in
the source register and is then padded by the concrete right-summand embedding. -/
def SumInrExactSmoothConditionalMinEntropyCandidate
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (Prod a b),
    ρ.purifiedBall ε ρ' ∧
      h = (ρ'.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy

/-- Exact-padding smooth max-entropy candidates: the smoothing witness lives in
the source register and is then padded by the concrete right-summand embedding. -/
def SumInrExactSmoothConditionalMaxEntropyCandidate
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (Prod a b),
    ρ.purifiedBall ε ρ' ∧
      h = (ρ'.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropy

/-- Any smooth min-entropy witness for the padded conditioning register
compresses to a source-register witness with at least as large endpoint value,
under the small-radius positive-trace condition. -/
theorem SmoothConditionalMinEntropyCandidate.conditioningIsometryApply_sumInr_compress
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand :
      SmoothConditionalMinEntropyCandidate (a := a)
        (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ε h) :
    ∃ h' : ℝ, SmoothConditionalMinEntropyCandidate (a := a) ρ ε h' ∧ h ≤ h' := by
  rcases hcand with ⟨ρPlus', hball, rfl⟩
  have hballCompressed :
      ρ.purifiedBall ε ρPlus'.conditioningSumInrCompressed :=
    purifiedBall_conditioningSumInrCompressed_of_conditioningIsometryApply_sumInr
      (a := a) (extra := extra) hball
  have hplus_pos :
      0 < ρPlus'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ρPlus'
      (by
        rw [conditioningIsometryApply_trace_re]
        exact hε)
      hball
  have hcompressed_pos :
      0 < ρPlus'.conditioningSumInrCompressed.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ
      ρPlus'.conditioningSumInrCompressed hε hballCompressed
  refine ⟨ρPlus'.conditioningSumInrCompressed.conditionalMinEntropy,
    ⟨ρPlus'.conditioningSumInrCompressed, hballCompressed, rfl⟩, ?_⟩
  exact conditionalMinEntropy_le_conditioningSumInrCompressed
    (a := a) (extra := extra) ρPlus' hplus_pos hcompressed_pos

/-- Under the small-radius condition used by the scaled-pure smooth-duality
surface, exact `sumInr` padding does not change smooth min-entropy candidates. -/
theorem sumInrExactSmoothConditionalMinEntropyCandidate_iff
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    SumInrExactSmoothConditionalMinEntropyCandidate (a := a) (extra := extra) ρ ε h ↔
      SmoothConditionalMinEntropyCandidate (a := a) ρ ε h := by
  constructor
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMinEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ'
      (SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball)]
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMinEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ'
      (SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball)]

/-- Exact `sumInr` padding does not change smooth max-entropy candidates. -/
theorem sumInrExactSmoothConditionalMaxEntropyCandidate_iff
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ} :
    SumInrExactSmoothConditionalMaxEntropyCandidate (a := a) (extra := extra) ρ ε h ↔
      SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h := by
  constructor
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMaxEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ']
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMaxEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ']

theorem conditionalMaxEntropyExponentCandidate_nonneg
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    0 ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  exact sq_nonneg _

omit [Fintype a] in
theorem identityTensorStateMatrix_normalize_smul
    (σ : SubnormalizedState b) (hσ : σ.matrix.trace.re ≠ 0) :
    identityTensorStateMatrix (a := a) σ =
      (σ.matrix.trace.re : ℂ) •
        State.identityTensorStateMatrix (a := a) (σ.normalize hσ) := by
  ext x y
  have hσC : ((σ.matrix.trace.re : ℂ) ≠ 0) := by
    exact_mod_cast hσ
  simp [identityTensorStateMatrix, State.identityTensorStateMatrix,
    SubnormalizedState.normalize_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply]
  field_simp [hσC]

theorem conditionalMaxEntropyExponentCandidate_eq_zero_of_side_trace_zero
    (ρ : SubnormalizedState (Prod a b)) {σ : SubnormalizedState b}
    (hσ : σ.matrix.trace.re = 0) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ = 0 := by
  have htrace : σ.matrix.trace = 0 := by
    apply Complex.ext
    · exact hσ
    · exact σ.trace_im_zero
  have hσ_zero : σ.matrix = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff σ.pos).mp htrace
  have hside : identityTensorStateMatrix (a := a) σ = 0 := by
    ext x y
    simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hσ_zero]
  unfold conditionalMaxEntropyExponentCandidate
  rw [hside]
  simp

theorem conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
    (ρ : State (Prod a b)) (σ : SubnormalizedState b)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 < σ.matrix.trace.re) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyExponentCandidate
        (a := a) σ =
      t * σ.matrix.trace.re *
        ρ.conditionalMaxEntropyExponentCandidate (a := a) (σ.normalize hσ.ne') := by
  let s : ℝ := σ.matrix.trace.re
  let M : CMatrix (Prod a b) :=
    ρ.sqrtMatrix * psdSqrt (State.identityTensorStateMatrix (a := a)
      (σ.normalize hσ.ne'))
  have hs_nonneg : 0 ≤ s := le_of_lt hσ
  have hsqrt_left :
      psdSqrt (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix =
        ((Real.sqrt t : ℝ) : ℂ) • ρ.sqrtMatrix := by
    rw [SubnormalizedState.ofStateScale_matrix]
    simpa [State.sqrtMatrix] using
      (psdSqrt_real_smul (a := Prod a b) ht.le (M := ρ.matrix) ρ.pos)
  have hside :
      identityTensorStateMatrix (a := a) σ =
        (s : ℂ) • State.identityTensorStateMatrix (a := a) (σ.normalize hσ.ne') := by
    dsimp [s]
    exact identityTensorStateMatrix_normalize_smul (a := a) σ hσ.ne'
  have hsqrt_side :
      psdSqrt (identityTensorStateMatrix (a := a) σ) =
        ((Real.sqrt s : ℝ) : ℂ) •
          psdSqrt (State.identityTensorStateMatrix (a := a) (σ.normalize hσ.ne')) := by
    rw [hside]
    exact psdSqrt_real_smul (a := Prod a b) hs_nonneg
      (M := State.identityTensorStateMatrix (a := a) (σ.normalize hσ.ne'))
      (State.identityTensorStateMatrix_posSemidef (a := a) (σ.normalize hσ.ne'))
  have hproduct :
      psdSqrt (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σ) =
        (((Real.sqrt t * Real.sqrt s : ℝ) : ℂ) • M) := by
    rw [hsqrt_left, hsqrt_side]
    dsimp [M]
    ext x y
    simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_left_comm]
  rw [conditionalMaxEntropyExponentCandidate_eq,
    State.conditionalMaxEntropyExponentCandidate_eq]
  rw [hproduct]
  rw [traceNorm_real_smul_eq (mul_nonneg (Real.sqrt_nonneg t) (Real.sqrt_nonneg s)) M]
  have hsqrt_t_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hsqrt_s_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs_nonneg
  let n : ℝ := traceNorm M
  calc
    (Real.sqrt t * Real.sqrt s * n) ^ 2 =
        (Real.sqrt t) ^ 2 * (Real.sqrt s) ^ 2 * n ^ 2 := by ring
    _ = t * s * n ^ 2 := by rw [hsqrt_t_sq, hsqrt_s_sq]

theorem conditionalMaxEntropyExponentCandidate_ofStateScale_toSubnormalized
    (ρ : State (Prod a b)) (τ : State b)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyExponentCandidate
        (a := a) τ.toSubnormalized =
      t * ρ.conditionalMaxEntropyExponentCandidate (a := a) τ := by
  have hτtr_pos : 0 < τ.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    norm_num
  have hnorm : τ.toSubnormalized.normalize hτtr_pos.ne' = τ := by
    apply State.ext
    rw [SubnormalizedState.normalize_matrix, State.toSubnormalized_matrix,
      τ.trace_eq_one]
    simp
  rw [conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
    (a := a) ρ τ.toSubnormalized ht ht1 hτtr_pos, hnorm]
  rw [State.toSubnormalized_trace]
  norm_num

theorem conditionalMaxEntropyExponentCandidate_maximallyMixed_pos_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a)
      (State.maximallyMixed b).toSubnormalized := by
  let c : ℝ := (Fintype.card b : ℝ)⁻¹
  have hc_nonneg : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hc_pos : 0 < Real.sqrt c := by
    have hcard_pos : 0 < (Fintype.card b : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact Real.sqrt_pos.mpr (inv_pos.mpr hcard_pos)
  have hsqrt_id :
      psdSqrt (identityTensorStateMatrix (a := a)
          (State.maximallyMixed b).toSubnormalized) =
        (((Real.sqrt c : ℝ) : ℂ) • (1 : CMatrix (Prod a b))) := by
    have hid :
        identityTensorStateMatrix (a := a) (State.maximallyMixed b).toSubnormalized =
          ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ) •
            (1 : CMatrix (Prod a b))) := by
      ext x y
      by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
        simp [identityTensorStateMatrix, State.maximallyMixed, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, h1, h2]
    rw [hid]
    exact psdSqrt_real_smul_one (a := Prod a b) hc_nonneg
  have htrace_eq :
      (psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a)
            (State.maximallyMixed b).toSubnormalized)).trace =
        ((Real.sqrt c : ℝ) : ℂ) * (psdSqrt ρ.matrix).trace := by
    rw [hsqrt_id]
    simp [Matrix.trace_smul]
  have htrace_abs_pos :
      0 < Complex.abs ((psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a)
            (State.maximallyMixed b).toSubnormalized)).trace) := by
    rw [htrace_eq]
    change 0 < ‖((Real.sqrt c : ℝ) : ℂ) * (psdSqrt ρ.matrix).trace‖
    rw [norm_mul]
    have htr_ne : (psdSqrt ρ.matrix).trace ≠ 0 := by
      intro hzero
      have hre : (psdSqrt ρ.matrix).trace.re = 0 := by rw [hzero]; rfl
      have hpos : 0 < (psdSqrt ρ.matrix).trace.re :=
        psdSqrt_trace_re_pos_of_trace_pos (a := Prod a b) hρ
      linarith
    have hc_ne : (((Real.sqrt c : ℝ) : ℂ) : ℂ) ≠ 0 := by
      exact_mod_cast hc_pos.ne'
    exact mul_pos (norm_pos_iff.mpr hc_ne) (norm_pos_iff.mpr htr_ne)
  have htn_pos :
      0 < traceNorm (psdSqrt ρ.matrix *
        psdSqrt (identityTensorStateMatrix (a := a)
          (State.maximallyMixed b).toSubnormalized)) :=
    lt_of_lt_of_le htrace_abs_pos (trace_abs_le_traceNorm _)
  unfold conditionalMaxEntropyExponentCandidate
  exact sq_pos_of_pos htn_pos

theorem conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a)
      (State.maximallyMixed b).toSubnormalized,
    (State.maximallyMixed b).toSubnormalized,
    ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos_of_trace_pos
      (a := a) hρ,
    rfl⟩

theorem conditionalMaxEntropyExponentValueSet_nonempty_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (_hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditionalMaxEntropyExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a)
      (State.maximallyMixed b).toSubnormalized,
    (State.maximallyMixed b).toSubnormalized,
    rfl⟩

theorem conditionalMaxEntropyPositiveValueSet_nonempty_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditionalMaxEntropyPositiveValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyFidelityCandidate
      (a := a) (State.maximallyMixed b).toSubnormalized,
    (State.maximallyMixed b).toSubnormalized,
    ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos_of_trace_pos
      (a := a) hρ,
    rfl⟩

theorem conditionalMaxEntropyPositiveValueSet_eq_log2_image
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) =
      log2 '' ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
  ext h
  constructor
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) σ, ?_, ?_⟩
    · exact ⟨σ, hpos, rfl⟩
    · exact (ρ.conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate σ).symm
  · rintro ⟨x, ⟨σ, hpos, rfl⟩, rfl⟩
    exact ⟨σ, hpos,
      ρ.conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate σ⟩

theorem conditionalMaxEntropy_eq_sSup_positiveValueSet
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropy =
      sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a)) :=
  rfl

theorem conditionalMaxEntropy_eq_positive
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropy = ρ.conditionalMaxEntropyPositive :=
  rfl

theorem conditionalMaxEntropyPositiveExponentValueSet_ofStateScale_le
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hx : x ∈
      (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyPositiveExponentValueSet
        (a := a)) :
    x ≤ t * ρ.conditionalMaxEntropyExponent (a := a) := by
  rcases hx with ⟨σ, hσpos, rfl⟩
  by_cases hσzero : σ.matrix.trace.re = 0
  · have hzero :=
      conditionalMaxEntropyExponentCandidate_eq_zero_of_side_trace_zero
        (a := a) (SubnormalizedState.ofStateScale ρ t ht.le ht1) hσzero
    linarith
  · have hσtrace_pos : 0 < σ.matrix.trace.re := by
      exact lt_of_le_of_ne σ.trace_nonneg (Ne.symm hσzero)
    rw [conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
      (a := a) ρ σ ht ht1 hσtrace_pos]
    have hstate_le :
        ρ.conditionalMaxEntropyExponentCandidate (a := a)
            (σ.normalize hσtrace_pos.ne') ≤
          ρ.conditionalMaxEntropyExponent (a := a) := by
      rw [State.conditionalMaxEntropyExponent]
      exact le_csSup (ρ.conditionalMaxEntropyExponentValueSet_bddAbove (a := a))
        ⟨σ.normalize hσtrace_pos.ne', rfl⟩
    have hstate_nonneg :
        0 ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a)
            (σ.normalize hσtrace_pos.ne') :=
      State.conditionalMaxEntropyExponentCandidate_nonneg (a := a) ρ
        (σ.normalize hσtrace_pos.ne')
    have hmul :
        σ.matrix.trace.re *
            ρ.conditionalMaxEntropyExponentCandidate (a := a)
              (σ.normalize hσtrace_pos.ne') ≤
          ρ.conditionalMaxEntropyExponent (a := a) := by
      calc
        σ.matrix.trace.re *
            ρ.conditionalMaxEntropyExponentCandidate (a := a)
              (σ.normalize hσtrace_pos.ne') ≤
            1 *
              ρ.conditionalMaxEntropyExponentCandidate (a := a)
                (σ.normalize hσtrace_pos.ne') := by
              exact mul_le_mul_of_nonneg_right σ.trace_le_one hstate_nonneg
        _ ≤ ρ.conditionalMaxEntropyExponent (a := a) := by
              simpa using hstate_le
    nlinarith [ht.le, hmul]

theorem conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    BddAbove
      ((SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyPositiveExponentValueSet
        (a := a)) := by
  exact ⟨t * ρ.conditionalMaxEntropyExponent (a := a),
    fun x hx => conditionalMaxEntropyPositiveExponentValueSet_ofStateScale_le
      (a := a) ρ ht ht1 hx⟩

theorem conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re) :
    BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
  rw [← ofStateScale_normalize_trace_eq ρ hρ]
  exact conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
    (a := a) (ρ.normalize hρ.ne') hρ ρ.trace_le_one

theorem conditionalMaxEntropyPositiveExponent_conditioningSumInrCompressed_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b)))
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < ρPlus.conditioningSumInrCompressed.matrix.trace.re) :
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponent
        (a := a) ≤
      ρPlus.conditionalMaxEntropyPositiveExponent (a := a) := by
  rw [conditionalMaxEntropyPositiveExponent_eq, conditionalMaxEntropyPositiveExponent_eq]
  have hneCompressed :
      (ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet
        (a := a)).Nonempty :=
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hCompressed
  refine csSup_le hneCompressed ?_
  intro x hx
  rcases hx with ⟨σ, hσpos, rfl⟩
  have hcand :=
    conditionalMaxEntropyExponentCandidate_conditioningSumInrCompressed_referenceIsometryApply_sumInr
      (a := a) (extra := extra) ρPlus σ
  have hmem :
      ρPlus.conditionalMaxEntropyExponentCandidate (a := a)
          (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)) ∈
        ρPlus.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
    refine ⟨σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b), ?_, rfl⟩
    rwa [← hcand]
  rw [hcand]
  exact le_csSup
    (ρPlus.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hPlus) hmem

theorem conditionalMaxEntropyPositiveExponent_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyPositiveExponent
        (a := a) =
      t * ρ.conditionalMaxEntropyExponent (a := a) := by
  let ρt : SubnormalizedState (Prod a b) :=
    SubnormalizedState.ofStateScale ρ t ht.le ht1
  have htrace_pos : 0 < ρt.matrix.trace.re := by
    dsimp [ρt]
    rw [Matrix.trace_smul, ρ.trace_eq_one]
    simpa [Complex.real_smul] using ht
  have hne :
      (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    ρt.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) htrace_pos
  have hbdd :
      BddAbove (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
    dsimp [ρt]
    exact conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
      (a := a) ρ ht ht1
  refine le_antisymm ?_ ?_
  · rw [conditionalMaxEntropyPositiveExponent]
    exact csSup_le hne (by
      intro x hx
      exact conditionalMaxEntropyPositiveExponentValueSet_ofStateScale_le
        (a := a) ρ ht ht1 hx)
  · have hlower :
        sSup ((fun x : ℝ => t * x) ''
            ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) ≤
          ρt.conditionalMaxEntropyPositiveExponent (a := a) := by
      refine csSup_le
        (Set.Nonempty.image _ (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty
          (a := a))) ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rcases hx with ⟨τ, hτpos, rfl⟩
      rw [conditionalMaxEntropyPositiveExponent]
      exact le_csSup hbdd
        ⟨τ.toSubnormalized, by
          rw [conditionalMaxEntropyExponentCandidate_ofStateScale_toSubnormalized
            (a := a) ρ τ ht ht1]
          exact mul_pos ht hτpos, by
          rw [conditionalMaxEntropyExponentCandidate_ofStateScale_toSubnormalized
            (a := a) ρ τ ht ht1]⟩
    have hsup_image :
        sSup ((fun x : ℝ => t * x) ''
            ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) =
          t * ρ.conditionalMaxEntropyPositiveExponent (a := a) := by
      rw [State.conditionalMaxEntropyPositiveExponent]
      exact mul_sSup_image_eq
        (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a))
        (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a)) ht
    rw [ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a), ← hsup_image]
    exact hlower

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent
    (ρ : SubnormalizedState (Prod a b))
    (hne : (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty)
    (hbdd : BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) := by
  have hpos : ∀ x ∈ ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a), 0 < x := by
    intro x hx
    rcases hx with ⟨σ, hσpos, rfl⟩
    exact hσpos
  rw [conditionalMaxEntropyPositive, conditionalMaxEntropyPositiveExponent,
    conditionalMaxEntropyPositiveValueSet_eq_log2_image]
  exact log2_sSup_image_eq hne hbdd hpos

/-- Compressing an arbitrary right-summand conditioning register can only
decrease subnormalized conditional max-entropy, when both traces are positive. -/
theorem conditionalMaxEntropy_conditioningSumInrCompressed_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b)))
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < ρPlus.conditioningSumInrCompressed.matrix.trace.re) :
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropy ≤
      ρPlus.conditionalMaxEntropy := by
  have hneCompressed :
      (ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet
        (a := a)).Nonempty :=
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hCompressed
  have hbddCompressed :
      BddAbove
        (ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet
          (a := a)) :=
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hCompressed
  have hnePlus :
      (ρPlus.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    ρPlus.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hPlus
  have hbddPlus :
      BddAbove (ρPlus.conditionalMaxEntropyPositiveExponentValueSet (a := a)) :=
    ρPlus.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hPlus
  rw [conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a) ρPlus.conditioningSumInrCompressed hneCompressed hbddCompressed,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a) ρPlus hnePlus hbddPlus]
  have hexp_le :=
    ρPlus.conditionalMaxEntropyPositiveExponent_conditioningSumInrCompressed_le
      (a := a) (extra := extra) hPlus hCompressed
  have hexp_pos :
      0 <
        ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponent
          (a := a) := by
    rcases hneCompressed with ⟨x, hx⟩
    have hxpos : 0 < x := by
      rcases hx with ⟨σ, hσpos, rfl⟩
      exact hσpos
    have hxle :
        x ≤
          ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponent
            (a := a) := by
      rw [conditionalMaxEntropyPositiveExponent]
      exact le_csSup hbddCompressed hx
    exact lt_of_lt_of_le hxpos hxle
  unfold log2
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hexp_pos hexp_le)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Any smooth max-entropy witness for the padded conditioning register
compresses to a source-register witness with no larger endpoint value, under
the small-radius positive-trace condition. -/
theorem SmoothConditionalMaxEntropyCandidate.conditioningIsometryApply_sumInr_compress
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand :
      SmoothConditionalMaxEntropyCandidate (a := a)
        (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ε h) :
    ∃ h' : ℝ, SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h' ∧ h' ≤ h := by
  rcases hcand with ⟨ρPlus', hball, rfl⟩
  have hballCompressed :
      ρ.purifiedBall ε ρPlus'.conditioningSumInrCompressed :=
    purifiedBall_conditioningSumInrCompressed_of_conditioningIsometryApply_sumInr
      (a := a) (extra := extra) hball
  have hplus_pos :
      0 < ρPlus'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ρPlus'
      (by
        rw [conditioningIsometryApply_trace_re]
        exact hε)
      hball
  have hcompressed_pos :
      0 < ρPlus'.conditioningSumInrCompressed.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ
      ρPlus'.conditioningSumInrCompressed hε hballCompressed
  refine ⟨ρPlus'.conditioningSumInrCompressed.conditionalMaxEntropy,
    ⟨ρPlus'.conditioningSumInrCompressed, hballCompressed, rfl⟩, ?_⟩
  exact conditionalMaxEntropy_conditioningSumInrCompressed_le
    (a := a) (extra := extra) ρPlus' hplus_pos hcompressed_pos

theorem conditionalMaxEntropy_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropy =
      ρ.conditionalMaxEntropy + log2 t := by
  let ρt : SubnormalizedState (Prod a b) :=
    SubnormalizedState.ofStateScale ρ t ht.le ht1
  have htrace_pos : 0 < ρt.matrix.trace.re := by
    dsimp [ρt]
    rw [Matrix.trace_smul, ρ.trace_eq_one]
    simpa [Complex.real_smul] using ht
  have hne :
      (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    ρt.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) htrace_pos
  have hbdd :
      BddAbove (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
    dsimp [ρt]
    exact conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
      (a := a) ρ ht ht1
  have hρexp_pos : 0 < ρ.conditionalMaxEntropyExponent (a := a) :=
    ρ.conditionalMaxEntropyExponent_pos (a := a)
  rw [conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent (a := a) ρt hne hbdd,
    conditionalMaxEntropyPositiveExponent_ofStateScale (a := a) ρ ht ht1,
    State.conditionalMaxEntropy_eq_positive (a := a),
    State.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a)]
  unfold log2
  rw [Real.log_mul ht.ne' hρexp_pos.ne']
  ring

private theorem cMatrix_real_smul_le_smul {α : Type*} [Fintype α] [DecidableEq α]
    {A B : CMatrix α} {t : ℝ} (ht : 0 ≤ t) (hAB : A ≤ B) :
    (t • A) ≤ (t • B) := by
  rw [Matrix.le_iff] at hAB ⊢
  have hdiff :
      (t • B - t • A) = t • (B - A) := by
    ext i j
    simp [sub_eq_add_neg, Complex.real_smul]
  rw [hdiff]
  exact hAB.smul ht

theorem ConditionalMinEntropyScaleFeasible.ofStateScale
    {ρ : State (Prod a b)} {T : CMatrix b} {t : ℝ}
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ConditionalMinEntropyScaleFeasible (a := a)
      (SubnormalizedState.ofStateScale ρ t ht0 ht1) (t • T) := by
  constructor
  · exact Matrix.PosSemidef.smul hT.1 ht0
  · have hscaled := cMatrix_real_smul_le_smul (A := ρ.matrix)
      (B := Matrix.kronecker (1 : CMatrix a) T) ht0 hT.2
    convert hscaled using 1
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.real_smul]
    ring

theorem ConditionalMinEntropyScaleFeasible.toStateScale
    {ρ : State (Prod a b)} {T : CMatrix b} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (SubnormalizedState.ofStateScale ρ t ht.le ht1) T) :
    State.ConditionalMinEntropyScaleFeasible (a := a) ρ (t⁻¹ • T) := by
  constructor
  · exact Matrix.PosSemidef.smul hT.1 (inv_nonneg.mpr ht.le)
  · have hscaled := cMatrix_real_smul_le_smul
      (A := (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix)
      (B := Matrix.kronecker (1 : CMatrix a) T)
      (inv_nonneg.mpr ht.le) hT.2
    convert hscaled using 1
    · simp [smul_smul, ht.ne']
    · ext i j
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.real_smul]
      ring

theorem conditionalMinEntropyScaleValueSet_ofStateScale
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMinEntropyScaleValueSet (a := a) =
      (fun r : ℝ => t * r) '' ρ.conditionalMinEntropyScaleValueSet (a := a) := by
  ext x
  constructor
  · rintro ⟨T, hT, rfl⟩
    refine ⟨(t⁻¹ • T).trace.re, ?_, ?_⟩
    · exact ⟨t⁻¹ • T,
        ConditionalMinEntropyScaleFeasible.toStateScale (a := a) ht ht1 hT, rfl⟩
    · rw [Matrix.trace_smul]
      simp [Complex.real_smul]
      field_simp [ht.ne']
  · rintro ⟨r, ⟨T, hT, rfl⟩, rfl⟩
    refine ⟨t • T,
      ConditionalMinEntropyScaleFeasible.ofStateScale (a := a) hT ht.le ht1, ?_⟩
    rw [Matrix.trace_smul]
    simp [Complex.real_smul]

theorem conditionalMinEntropyScale_ofStateScale
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMinEntropyScale (a := a) =
      t * ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    State.conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScaleValueSet_ofStateScale (a := a) ρ ht ht1]
  let s : Set ℝ := ρ.conditionalMinEntropyScaleValueSet (a := a)
  have himage : (fun r : ℝ => t * r) '' s = t • s := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact Set.mem_smul_set.mpr ⟨r, hr, by rw [smul_eq_mul]⟩
    · intro hx
      rcases Set.mem_smul_set.mp hx with ⟨r, hr, htx⟩
      exact ⟨r, hr, by simpa [smul_eq_mul] using htx⟩
  rw [himage, Real.sInf_smul_of_nonneg ht.le]
  simp [s, smul_eq_mul]

theorem conditionalMinEntropy_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMinEntropy =
      ρ.conditionalMinEntropy - log2 t := by
  have htrace_pos :
      0 < (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix.trace.re := by
    rw [ofStateScale_trace_re]
    exact ht
  rw [conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a)
      (SubnormalizedState.ofStateScale ρ t ht.le ht1) htrace_pos,
    State.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    conditionalMinEntropyScale_ofStateScale (a := a) ρ ht ht1]
  have hscale_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  rw [Real.log_mul ht.ne' hscale_pos.ne']
  ring

private theorem rpow_two_neg_sub_log2 (t lam : ℝ) (ht : 0 < t) :
    Real.rpow 2 (-(lam - log2 t)) = t * Real.rpow 2 (-lam) := by
  calc
    Real.rpow 2 (-(lam - log2 t)) =
        Real.rpow 2 (log2 t + -lam) := by ring_nf
    _ = Real.rpow 2 (log2 t) * Real.rpow 2 (-lam) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) (log2 t) (-lam)
    _ = t * Real.rpow 2 (-lam) := by rw [rpow_two_log2_pos ht]

theorem ConditionalMinEntropyFeasible.ofStateScale_shift
    {ρ : State (Prod a b)} {σ : State b} {t lam : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (h : State.ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ConditionalMinEntropyFeasible (a := a)
      (ofStateScale ρ t ht.le ht1) σ.toSubnormalized (lam - log2 t) := by
  change ρ.matrix ≤
      (Real.rpow 2 (-lam) : ℂ) • State.identityTensorStateMatrix (a := a) σ at h
  change t • ρ.matrix ≤
      (Real.rpow 2 (-(lam - log2 t)) : ℂ) •
        identityTensorStateMatrix (a := a) σ.toSubnormalized
  have hscaled := cMatrix_real_smul_le_smul (A := ρ.matrix)
    (B := (Real.rpow 2 (-lam) : ℂ) • State.identityTensorStateMatrix (a := a) σ)
    ht.le h
  convert hscaled using 1
  rw [rpow_two_neg_sub_log2 t lam ht]
  ext i j
  simp [State.toSubnormalized_identityTensorStateMatrix_eq]
  ring

theorem conditionalMinEntropyFeasibleExponentValueSet_shift_subset_ofStateScale
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (fun lam : ℝ => lam - log2 t) ''
        State.conditionalMinEntropyFeasibleExponentValueSet (a := a) ρ ⊆
      {mu : ℝ | ∃ σ : SubnormalizedState b,
        ConditionalMinEntropyFeasible (a := a)
          (ofStateScale ρ t ht.le ht1) σ mu} := by
  rintro mu ⟨lam, ⟨σ, hσ⟩, rfl⟩
  exact ⟨σ.toSubnormalized,
    ConditionalMinEntropyFeasible.ofStateScale_shift (a := a)
      (ρ := ρ) (σ := σ) ht ht1 hσ⟩

end SubnormalizedState

namespace PureVector

variable {a : Type u} {b : Type v} {c : Type*}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable {κ : Type x} [Fintype κ] [DecidableEq κ]

private theorem sum_pair_delta {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [AddCommMonoid γ] (p : α) (q : β) (f : α → β → γ) :
    (∑ x : α, ∑ y : β, if x = p ∧ y = q then f x y else 0) = f p q := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hnot
      simp at hnot
  · intro x _ hx
    have hxp : x ≠ p := hx
    simp [hxp]
  · intro hnot
    simp at hnot

private theorem sum_pair_delta_rev {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [AddCommMonoid γ] (p : α) (q : β) (f : α → β → γ) :
    (∑ x : α, ∑ y : β, if p = x ∧ q = y then f x y else 0) = f p q := by
  simpa [eq_comm] using sum_pair_delta p q f

private theorem sum_abab_delta {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [AddCommMonoid γ] (p r : α) (q s : β) (f : α → β → α → β → γ) :
    (∑ x₁ : α, ∑ y₁ : β, ∑ x₂ : α, ∑ y₂ : β,
      if x₁ = p ∧ x₂ = r ∧ y₁ = q ∧ y₂ = s then f x₁ y₁ x₂ y₂ else 0) =
      f p q r s := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single s]
        · simp
        · intro y _ hy
          simp [hy]
        · intro hnot
          simp at hnot
      · intro x _ hx
        simp [hx]
      · intro hnot
        simp at hnot
    · intro y _ hy
      simp [hy]
    · intro hnot
      simp at hnot
  · intro x _ hx
    simp [hx]
  · intro hnot
    simp at hnot

/-- The dual-effect objective on the `AC` marginal is the same tripartite
bracket obtained by lifting that `AC` operator to the pure `ABC` state.

This is only a representation bridge; it does not use or prove endpoint
duality. -/
theorem dualEffectObjective_eq_tripartiteBracket_liftAC
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    ((ψ.state.marginalAC.matrix * M).trace).re =
      (ψ.tripartiteBracket (State.liftACToABC (b := b) M)).re := by
  calc
    ((ψ.state.marginalAC.matrix * M).trace).re =
        ((M * ψ.state.marginalAC.matrix).trace).re := by
      rw [Matrix.trace_mul_comm]
    _ = (ψ.tripartiteBracket (State.liftACToABC (b := b) M)).re := by
      rw [ψ.tripartiteBracket_liftACToABC_eq_trace_marginalAC M]

/-! ### Pure endpoint link-map support -/

def dualEffectKrausSuccessVector [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (K : κ → Matrix a c ℂ) :
    Prod κ b → ℂ :=
  fun x =>
    ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) *
      ∑ i : a, ∑ z : c, K x.1 i z * ψ.amp ((i, x.2), z)

private theorem dualEffectTransposeMatrixMap_eq_ofKraus_entry
    {M : CMatrix (Prod a c)} {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K)
    (i i' : a) (z z' : c) :
    M (i', z') (i, z) =
      ∑ l : κ, K l i z * star (K l i' z') := by
  have hchoi := congrArg MatrixMap.choi hK
  have hentry := congrFun (congrFun hchoi (z, i)) (z', i')
  rw [State.conditionalMinEntropyDualEffectTransposeMatrixMap,
    MatrixMap.choi_ofChoiMatrix, MatrixMap.choi_ofKraus] at hentry
  simpa [State.conditionalMinEntropyDualEffectTransposeMatrixMap,
    State.conditionalMinEntropyDualEffectTransposeChoiMatrix,
    State.conditionalMinEntropyDualEffectChoiMatrix, Matrix.vecMulVec,
    Matrix.transpose, Matrix.sum_apply] using hentry

/-- Apply the Choi map induced by an `AC` dual effect to the purifying `C`
register of a pure `ABC` state, leaving the `AB` registers untouched.

The output lives on `(A × B) × A'`; the final endpoint proof tests the two
outer `A` registers against a maximally-entangled projector. -/
def dualEffectLinkOutputABA (ψ : PureVector (Prod (Prod a b) c))
    (M : CMatrix (Prod a c)) : CMatrix (Prod (Prod a b) a) :=
  (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b))
    (State.conditionalMinEntropyDualEffectMatrixMap (a := a) (b := c) M)) ψ.state.matrix

/-- The same link-map output, written with the adjoint input matrix.  Since
pure-state density matrices are Hermitian this is equal to
`dualEffectLinkOutputABA`, but its matrix-entry expansion has the orientation
that directly matches `Tr(ρ_AC M)`. -/
def dualEffectLinkOutputABAStarInput (ψ : PureVector (Prod (Prod a b) c))
    (M : CMatrix (Prod a c)) : CMatrix (Prod (Prod a b) a) :=
  (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b))
    (State.conditionalMinEntropyDualEffectMatrixMap (a := a) (b := c) M)) (star ψ.state.matrix)

/-- Link output using the transpose-Choi orientation of the dual effect.  This
orientation is the one whose maximally-entangled projector expectation unfolds
directly to the dual-effect objective `Tr(ρ_AC M)`. -/
def dualEffectTransposeLinkOutputABA (ψ : PureVector (Prod (Prod a b) c))
    (M : CMatrix (Prod a c)) : CMatrix (Prod (Prod a b) a) :=
  (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b))
    (State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M))
      ψ.state.matrix

theorem dualEffectLinkOutputABAStarInput_eq
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    dualEffectLinkOutputABAStarInput (a := a) (b := b) (c := c) ψ M =
      dualEffectLinkOutputABA (a := a) (b := b) (c := c) ψ M := by
  have hstar : star ψ.state.matrix = ψ.state.matrix := by
    simpa [Matrix.star_eq_conjTranspose] using ψ.state_matrix_isHermitian.eq
  rw [dualEffectLinkOutputABAStarInput, dualEffectLinkOutputABA, hstar]

@[simp]
theorem dualEffectLinkOutputABA_apply
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (ab ab' : Prod a b) (i i' : a) :
    dualEffectLinkOutputABA (a := a) (b := b) (c := c) ψ M (ab, i) (ab', i') =
      ∑ k : c, ∑ k' : c,
        ψ.state.matrix (ab, k) (ab', k') * M (i, k) (i', k') := by
  classical
  rcases ab with ⟨j, b0⟩
  rcases ab' with ⟨j', b1⟩
  simp [dualEffectLinkOutputABA, MatrixMap.kron, MatrixMap.ofChoiMatrix_apply,
    State.conditionalMinEntropyDualEffectMatrixMap,
    State.conditionalMinEntropyDualEffectChoiMatrix, PureVector.state_matrix,
    rankOneMatrix_apply, Matrix.single, Fintype.sum_prod_type,
    sum_pair_delta_rev, sum_abab_delta, and_assoc, and_left_comm]

@[simp]
theorem dualEffectLinkOutputABAStarInput_apply
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (ab ab' : Prod a b) (i i' : a) :
    dualEffectLinkOutputABAStarInput (a := a) (b := b) (c := c) ψ M (ab, i) (ab', i') =
      ∑ k : c, ∑ k' : c,
        (star ψ.state.matrix) (ab, k) (ab', k') * M (i, k) (i', k') := by
  classical
  rcases ab with ⟨j, b0⟩
  rcases ab' with ⟨j', b1⟩
  simp [dualEffectLinkOutputABAStarInput, MatrixMap.kron, MatrixMap.ofChoiMatrix_apply,
    State.conditionalMinEntropyDualEffectMatrixMap,
    State.conditionalMinEntropyDualEffectChoiMatrix, PureVector.state_matrix,
    rankOneMatrix_apply, Matrix.single, Fintype.sum_prod_type,
    sum_pair_delta_rev, sum_abab_delta, and_assoc, and_left_comm]

@[simp]
theorem dualEffectTransposeLinkOutputABA_apply
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (ab ab' : Prod a b) (i i' : a) :
    dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M (ab, i) (ab', i') =
      ∑ k : c, ∑ k' : c,
        ψ.state.matrix (ab, k) (ab', k') * M (i', k') (i, k) := by
  classical
  rcases ab with ⟨j, b0⟩
  rcases ab' with ⟨j', b1⟩
  simp [dualEffectTransposeLinkOutputABA, MatrixMap.kron, MatrixMap.ofChoiMatrix_apply,
    State.conditionalMinEntropyDualEffectTransposeMatrixMap,
    State.conditionalMinEntropyDualEffectTransposeChoiMatrix,
    State.conditionalMinEntropyDualEffectChoiMatrix, PureVector.state_matrix,
    rankOneMatrix_apply, Matrix.single, Fintype.sum_prod_type,
    sum_pair_delta_rev, sum_abab_delta, and_assoc, and_left_comm, Matrix.transpose]

private theorem sum_a_a_b_c_c_k_reorder {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → α → β → γ → γ → δ → ℂ) :
    (∑ x : α, ∑ y : α, ∑ j : β, ∑ k : γ, ∑ l : γ, ∑ m : δ,
        f x y j k l m) =
      ∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ,
        f x y j k l m := by
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
  let e : (((((α × α) × β) × γ) × γ) × δ) ≃ (((((δ × β) × α) × γ) × α) × γ) := {
    toFun := fun t =>
      (((((t.2, t.1.1.1.2), t.1.1.1.1.1), t.1.1.2), t.1.1.1.1.2), t.1.2)
    invFun := fun s =>
      (((((s.1.1.1.2, s.1.2), s.1.1.1.1.2), s.1.1.2), s.2), s.1.1.1.1.1)
    left_inv := by
      intro t
      rcases t with ⟨⟨⟨⟨⟨x, y⟩, j⟩, k⟩, l⟩, m⟩
      rfl
    right_inv := by
      intro s
      rcases s with ⟨⟨⟨⟨⟨m, j⟩, x⟩, k⟩, y⟩, l⟩
      rfl }
  simpa [e] using
    (Finset.sum_equiv e (s := Finset.univ) (t := Finset.univ)
      (fun _ => by simp)
      (fun t _ => by
        rcases t with ⟨⟨⟨⟨⟨x, y⟩, j⟩, k⟩, l⟩, m⟩
        rfl))

private theorem sum_outer_mul_inner_expand {δ : Type*} {β : Type*} {α : Type*} {γ : Type*}
    [Fintype δ] [Fintype β] [Fintype α] [Fintype γ]
    (s : ℂ) (A B : δ → β → α → γ → ℂ)
    (C : δ → β → α → γ → α → γ → ℂ) :
    (∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ,
        A m j x k * (s * (B m j x k *
          ∑ y : α, ∑ l : γ, s * C m j x k y l))) =
      ∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ,
        A m j x k * (s * (s * (B m j x k * C m j x k y l))) := by
  classical
  simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

private theorem sum_success_norm_expand {δ : Type*} {β : Type*} {α : Type*} {γ : Type*}
    [Fintype δ] [Fintype β] [Fintype α] [Fintype γ]
    (s : ℂ) (hs : star s = s) (K : δ → α → γ → ℂ)
    (A : δ → β → α → γ → ℂ) :
    (∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ,
        s * (K m x k * A m j x k) *
          star (∑ y : α, ∑ l : γ, s * (K m y l * A m j y l))) =
      ∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ,
        K m x k *
          (s * (s * (A m j x k * (star (K m y l) * star (A m j y l))))) := by
  classical
  simp [hs, Finset.mul_sum, Finset.sum_mul, map_sum, map_mul,
    mul_assoc, mul_left_comm, mul_comm]

private theorem dotProduct_single_one_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι) (f : ι → ℂ) :
    (fun j => if p = j then 1 else 0) ⬝ᵥ f = f p := by
  classical
  rw [dotProduct]
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    have hpj : p ≠ j := fun h => hj h.symm
    simp [hpj]
  · intro hnot
    simp at hnot

private theorem sum_two_delta_collapse {δ : Type*} {α : Type*} {β : Type*} {γ : Type*}
    [Fintype δ] [DecidableEq δ] [Fintype α] [DecidableEq α]
    [Fintype β] [Fintype γ]
    (F : δ → α → α → β → δ → γ → ℂ) :
    (∑ m : δ, ∑ i : α, ∑ i' : α, ∑ j : β, ∑ m' : δ,
        if m = m' ∧ i = i' then ∑ z : γ, F m i i' j m' z else 0) =
      ∑ m : δ, ∑ j : β, ∑ i : α, ∑ z : γ, F m i i j m z := by
  classical
  calc
    (∑ m : δ, ∑ i : α, ∑ i' : α, ∑ j : β, ∑ m' : δ,
        if m = m' ∧ i = i' then ∑ z : γ, F m i i' j m' z else 0) =
        ∑ m : δ, ∑ i : α, ∑ j : β, ∑ z : γ, F m i i j m z := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_eq_single i]
          · rw [Finset.sum_eq_single m]
            · simp
            · intro m' _ hm'
              have hne : m ≠ m' := fun h => hm' h.symm
              simp [hne]
            · intro hnot
              simp at hnot
          · intro i' _ hi'
            have hne : i ≠ i' := fun h => hi' h.symm
            simp [hne]
          · intro hnot
            simp at hnot
    _ = ∑ m : δ, ∑ j : β, ∑ i : α, ∑ z : γ, F m i i j m z := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm

set_option maxHeartbeats 800000 in
theorem dualEffectTransposeLink_projector_trace_eq_successVector_trace [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K) :
    ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
        State.maximallyEntangledProjectorWithMiddle (a := a) b).trace) =
      (rankOneMatrix (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace := by
  classical
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsqrt_ne : Real.sqrt (Fintype.card a : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hcard_pos)
  have hcoeff_success :
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
          (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← sq, Real.sq_sqrt]
    exact inv_nonneg.mpr (le_of_lt hcard_pos)
  rw [State.trace_mul_maximallyEntangledProjectorWithMiddle]
  rw [rankOneMatrix_trace]
  simp only [dualEffectTransposeLinkOutputABA_apply, dualEffectKrausSuccessVector,
    dotProduct, PureVector.state_matrix, rankOneMatrix_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    dualEffectTransposeMatrixMap_eq_ofKraus_entry (a := a) (c := c) hK]
  rw [hcoeff_success]
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  rw [sum_success_norm_expand
    (δ := κ) (β := b) (α := a) (γ := c)
    ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ))
    hscoeff K (fun _ j x k => ψ.amp ((x, j), k))]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    sum_a_a_b_c_c_k_reorder (α := a) (β := b) (γ := c) (δ := κ)
      (fun x y j k l m =>
        K m x k *
          ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
            ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
              (ψ.amp ((x, j), k) *
                ((starRingEnd ℂ) (K m y l) *
                  (starRingEnd ℂ) (ψ.amp ((y, j), l)))))))

private theorem sum_a_c_a_c_b_reorder {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → α → γ → ℂ) :
    (∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ, ∑ j : β,
        f x j k y l) =
      ∑ x : α, ∑ y : α, ∑ j : β, ∑ k : γ, ∑ l : γ,
        f x j k y l := by
  apply Finset.sum_congr rfl
  intro x _
  calc
    (∑ k : γ, ∑ y : α, ∑ l : γ, ∑ j : β, f x j k y l) =
        ∑ y : α, ∑ k : γ, ∑ l : γ, ∑ j : β, f x j k y l := by
      rw [Finset.sum_comm]
    _ = ∑ y : α, ∑ k : γ, ∑ j : β, ∑ l : γ, f x j k y l := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ y : α, ∑ j : β, ∑ k : γ, ∑ l : γ, f x j k y l := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]

private theorem idChannel_map_eq_linearMap_id {α : Type*} [Fintype α] [DecidableEq α] :
    (Channel.idChannel α).map = (LinearMap.id : MatrixMap α α) := by
  ext X i j
  simp [Channel.idChannel, MatrixMap.ofKraus]

private def contractionDilationReferenceIsometry {r₁ : Type*} {r₂ : Type*}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (K : Matrix r₂ r₁ ℂ) (hK : Matrix.conjTranspose K * K ≤ (1 : CMatrix r₁)) :
    ReferenceIsometry r₁ (Sum r₁ r₂) where
  matrix := fun x y =>
    match x with
    | Sum.inl i => psdSqrt ((1 : CMatrix r₁) - Matrix.conjTranspose K * K) i y
    | Sum.inr j => K j y
  isometry := by
    classical
    let S : CMatrix r₁ := (1 : CMatrix r₁) - Matrix.conjTranspose K * K
    have hSpos : S.PosSemidef := by
      simpa [S, Matrix.le_iff] using hK
    have hSH : (psdSqrt S).IsHermitian := psdSqrt_isHermitian S
    have hSsq : psdSqrt S * psdSqrt S = S :=
      psdSqrt_mul_self_of_posSemidef hSpos
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [Fintype.sum_sum_type]
    have hleft :
        (∑ x : r₁,
          star (psdSqrt S x i) * psdSqrt S x j) =
          S i j := by
      calc
        (∑ x : r₁, star (psdSqrt S x i) * psdSqrt S x j) =
            (∑ x : r₁, psdSqrt S i x * psdSqrt S x j) := by
              apply Finset.sum_congr rfl
              intro x _
              have hx := congrFun (congrFun hSH.eq i) x
              have hx' : star (psdSqrt S x i) = psdSqrt S i x := by
                simpa [Matrix.conjTranspose_apply] using hx
              rw [hx']
        _ = (psdSqrt S * psdSqrt S) i j := by
              simp [Matrix.mul_apply]
        _ = S i j := by rw [hSsq]
    rw [hleft]
    change S i j + (Matrix.conjTranspose K * K) i j = (1 : CMatrix r₁) i j
    simp [S, Matrix.sub_apply]

private def referenceIsometryRightBlockK {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (V : ReferenceIsometry c (Sum c (Prod κ a))) :
    κ → Matrix a c ℂ :=
  fun k i z => V.matrix (Sum.inr (k, i)) z

private def referenceIsometryLeftBlockMatrix {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (V : ReferenceIsometry c (Sum c (Prod κ a))) :
    CMatrix c :=
  fun z z' => V.matrix (Sum.inl z) z'

private theorem referenceIsometryRightBlockK_contraction {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (V : ReferenceIsometry c (Sum c (Prod κ a))) :
    Matrix.conjTranspose
        (MatrixMap.smoothEndpointKrausStack (referenceIsometryRightBlockK (a := a) V)) *
        MatrixMap.smoothEndpointKrausStack (referenceIsometryRightBlockK (a := a) V) ≤
      (1 : CMatrix c) := by
  classical
  let L : CMatrix c := referenceIsometryLeftBlockMatrix (a := a) V
  let Kstack : Matrix (Prod κ a) c ℂ :=
    MatrixMap.smoothEndpointKrausStack (referenceIsometryRightBlockK (a := a) V)
  have hdecomp :
      (1 : CMatrix c) - Matrix.conjTranspose Kstack * Kstack =
        Matrix.conjTranspose L * L := by
    ext z z'
    have hV := congrFun (congrFun V.isometry z) z'
    simp [L, Kstack, referenceIsometryLeftBlockMatrix, referenceIsometryRightBlockK,
      MatrixMap.smoothEndpointKrausStack, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.sub_apply] at hV ⊢
    rw [← hV]
    ring
  have hpos : ((1 : CMatrix c) - Matrix.conjTranspose Kstack * Kstack).PosSemidef := by
    rw [hdecomp]
    exact Matrix.posSemidef_conjTranspose_mul_self L
  simpa [Kstack, Matrix.le_iff] using hpos

theorem dualEffectObjective_eq_card_mul_trace_transposeLink
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    ((ψ.state.marginalAC.matrix * M).trace) =
      ((Fintype.card a : ℂ) *
        ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
          State.maximallyEntangledProjectorWithMiddle (a := a) b).trace)) := by
  classical
  rw [State.trace_mul_maximallyEntangledProjectorWithMiddle]
  simpa [dualEffectTransposeLinkOutputABA_apply, State.marginalAC, Matrix.trace,
    Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    mul_assoc] using
      sum_a_c_a_c_b_reorder (α := a) (β := b) (γ := c)
        (fun x j k y l =>
          ψ.amp ((x, j), k) * ((starRingEnd ℂ) (ψ.amp ((y, j), l)) * M (y, l) (x, k)))

theorem dualEffectTransposeLinkOutputABA_posSemidef
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    (dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M).PosSemidef := by
  classical
  let T : MatrixMap c a :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M
  have hT : MatrixMap.TraceNonincreasingCP T :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasingCP
      (a := a) (b := c) hM
  have hkron :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (Channel.idChannel (Prod a b)).map T) :=
    MatrixMap.traceNonincreasingCP_id_kron (a := Prod a b) hT
  have hkron' :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b)) T) := by
    simpa [idChannel_map_eq_linearMap_id] using hkron
  simpa [dualEffectTransposeLinkOutputABA, T] using
    hkron'.mapsPositive ψ.state.matrix ψ.state.pos

theorem dualEffectTransposeLinkOutputABA_trace_re_le_one
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    (dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M).trace.re ≤ 1 := by
  classical
  let T : MatrixMap c a :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M
  have hT : MatrixMap.TraceNonincreasingCP T :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasingCP
      (a := a) (b := c) hM
  have hkron :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (Channel.idChannel (Prod a b)).map T) :=
    MatrixMap.traceNonincreasingCP_id_kron (a := Prod a b) hT
  have hkron' :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b)) T) := by
    simpa [idChannel_map_eq_linearMap_id] using hkron
  have hle := hkron'.traceNonincreasing ψ.state.matrix ψ.state.pos
  have htrace : (ψ.amp ⬝ᵥ fun i => (starRingEnd ℂ) (ψ.amp i)).re = 1 := by
    simpa [PureVector.state_matrix, Matrix.trace, rankOneMatrix_apply, dotProduct,
      Complex.mul_re, Complex.conj_re, Complex.conj_im] using
      congrArg Complex.re ψ.trace_rankOne_eq_one
  change ((MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b)) T)
      ψ.state.matrix).trace.re ≤ 1
  simpa [htrace] using hle

theorem dualEffectTransposeLinkOutputABA_projector_trace_re_nonneg [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    0 ≤ ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
      State.maximallyEntangledProjectorWithMiddle (a := a) b).trace).re := by
  exact cMatrix_trace_mul_posSemidef_re_nonneg
    (ψ.dualEffectTransposeLinkOutputABA_posSemidef (a := a) hM)
    (State.maximallyEntangledProjectorWithMiddle_posSemidef (a := a) (b := b))

theorem dualEffectObjective_re_eq_card_mul_trace_transposeLink [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    ((ψ.state.marginalAC.matrix * M).trace).re =
      (Fintype.card a : ℝ) *
        ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
          State.maximallyEntangledProjectorWithMiddle (a := a) b).trace).re := by
  have h :=
    congrArg Complex.re
      (ψ.dualEffectObjective_eq_card_mul_trace_transposeLink (a := a) (b := b) M)
  simpa [Complex.re_ofReal_mul] using h

theorem dualEffectObjective_re_eq_card_mul_successVector_trace [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K) :
    ((ψ.state.marginalAC.matrix * M).trace).re =
      (Fintype.card a : ℝ) *
        (rankOneMatrix
          (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re := by
  have hobj :=
    ψ.dualEffectObjective_re_eq_card_mul_trace_transposeLink (a := a) (b := b) M
  have htrace :=
    congrArg Complex.re
      (ψ.dualEffectTransposeLink_projector_trace_eq_successVector_trace
        (a := a) (b := b) hK)
  rw [hobj, htrace]

theorem dualEffectKrausSuccessVector_card_mul_trace_le_scaleFeasible_trace
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {K : κ → Matrix a c ℂ}
    {T : CMatrix c}
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c))
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T) :
    (Fintype.card a : ℝ) *
        (rankOneMatrix
          (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re ≤
      T.trace.re := by
  let M : CMatrix (Prod a c) :=
    State.conditionalMinEntropyDualEffectOfKraus (a := a) (b := c) K
  have hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M := by
    exact State.conditionalMinEntropyDualEffectOfKraus_feasible
      (a := a) (b := c) K hKstack
  have hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K := by
    exact State.conditionalMinEntropyDualEffectOfKraus_transposeMatrixMap_eq_ofKraus
      (a := a) (b := c) K
  have hweak :
      ((ψ.state.marginalAC.matrix * M).trace).re ≤ T.trace.re :=
    State.conditionalMinEntropyDualEffectValue_le_scaleValue
      (a := a) hM hT
  have hobj :=
    ψ.dualEffectObjective_re_eq_card_mul_successVector_trace
      (a := a) (b := b) hK
  rwa [hobj] at hweak

theorem dualEffectObjective_le_card_mul_sSup_fidelityValueSet_of_successVector_trace_le
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K)
    (hsuccess :
      (rankOneMatrix
        (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re ≤
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ((ψ.state.marginalAC.matrix * M).trace).re ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  rw [ψ.dualEffectObjective_re_eq_card_mul_successVector_trace
    (a := a) (b := b) hK]
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card a)
  exact mul_le_mul_of_nonneg_left hsuccess hcard_nonneg

set_option maxHeartbeats 1200000 in
private theorem dualEffectKrausSuccessVector_dilation_overlap_eq_dot
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (K : κ → Matrix a c ℂ)
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c))
    (η : PureVector (Prod κ b)) :
    let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ :=
      (contractionDilationReferenceIsometry
        (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    Ψ.overlap Φ = ∑ x : Prod κ b, star (v x) * η.amp x := by
  classical
  intro v Ψ₀ Ψ Φ₀ Φ
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  simpa [PureVector.overlap, Ψ, Φ, Ψ₀, Φ₀, v,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    contractionDilationReferenceIsometry, ReferenceIsometry.sumInr,
    State.maxEntangledSidePureVector, State.pureVectorOfAmplitudeMatrix,
    State.maxEntangledSideAmplitude,
    dualEffectKrausSuccessVector, MatrixMap.smoothEndpointKrausStack,
    Matrix.mulVec, Fintype.sum_sum_type, Fintype.sum_prod_type,
    dotProduct_single_one_left,
    dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, hscoeff,
    mul_assoc, mul_left_comm, mul_comm] using
      sum_two_delta_collapse (δ := κ) (α := a) (β := b) (γ := c)
      (fun m i i' j m' z =>
            (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
            (η.amp (m', j) *
              (star (K m i z) * star (ψ.amp ((i', j), z)))))

set_option maxHeartbeats 1200000 in
private theorem referenceIsometryRightBlockK_overlap_eq_dot
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c))
    (V : ReferenceIsometry c (Sum c (Prod κ a)))
    (η : PureVector (Prod κ b)) :
    let K := referenceIsometryRightBlockK (a := a) V
    let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ := V.applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    Ψ.overlap Φ = ∑ x : Prod κ b, star (v x) * η.amp x := by
  classical
  intro K v Ψ₀ Ψ Φ₀ Φ
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  simpa [PureVector.overlap, Ψ, Φ, Ψ₀, Φ₀, v, K,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    ReferenceIsometry.sumInr, State.maxEntangledSidePureVector,
    State.pureVectorOfAmplitudeMatrix, State.maxEntangledSideAmplitude,
    referenceIsometryRightBlockK, dualEffectKrausSuccessVector,
    Matrix.mulVec, Fintype.sum_sum_type, Fintype.sum_prod_type,
    dotProduct_single_one_left, dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, hscoeff,
    mul_assoc, mul_left_comm, mul_comm] using
      sum_two_delta_collapse (δ := κ) (α := a) (β := b) (γ := c)
        (fun m i i' j m' z =>
            (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
            (η.amp (m', j) *
              (star (V.matrix (Sum.inr (m, i)) z) *
                star (ψ.amp ((i', j), z)))))

private theorem referenceIsometryRightBlockK_card_mul_overlapSq_le_scaleFeasible_trace
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c))
    (V : ReferenceIsometry c (Sum c (Prod κ a)))
    (η : PureVector (Prod κ b))
    {T : CMatrix c}
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T) :
    (Fintype.card a : ℝ) *
        ((V.applyPureVector
          (ψ.reindex (Equiv.prodComm (Prod a b) c))).overlapSq
            ((ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector
              (State.maxEntangledSidePureVector (a := a) η))) ≤
      T.trace.re := by
  classical
  let K := referenceIsometryRightBlockK (a := a) V
  let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
  have hoverlap :=
    referenceIsometryRightBlockK_overlap_eq_dot
      (a := a) (b := b) (c := c) ψ V η
  have hcauchy :
      Complex.normSq (∑ x : Prod κ b, star (v x) * η.amp x) ≤
        (rankOneMatrix v).trace.re :=
    PureVector.normSq_sum_star_mul_le_rankOne_trace v η
  have hsuccess :
      (Fintype.card a : ℝ) * (rankOneMatrix v).trace.re ≤ T.trace.re :=
    ψ.dualEffectKrausSuccessVector_card_mul_trace_le_scaleFeasible_trace
      (a := a) (b := b) (K := K)
      (referenceIsometryRightBlockK_contraction (a := a) V) hT
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card a)
  have hmul :
      (Fintype.card a : ℝ) *
          Complex.normSq (∑ x : Prod κ b, star (v x) * η.amp x) ≤
        (Fintype.card a : ℝ) * (rankOneMatrix v).trace.re :=
    mul_le_mul_of_nonneg_left hcauchy hcard_nonneg
  rw [PureVector.overlapSq_eq_normSq, hoverlap]
  exact hmul.trans hsuccess

theorem fidelity_forward_bound_by_scaleFeasible
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) (σ : State b) (T : CMatrix c)
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T) :
    (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
      T.trace.re := by
  classical
  let η : PureVector (Prod b b) := σ.canonicalPurification
  let τ : State (Prod a b) := (State.maximallyMixed a).prod σ
  let Ψ₀ : PureVector (Prod c (Prod a b)) :=
    ψ.reindex (Equiv.prodComm (Prod a b) c)
  let Φ₀ : PureVector (Prod (Prod b a) (Prod a b)) :=
    State.maxEntangledSidePureVector (a := a) η
  let Φ : PureVector (Prod (Sum c (Prod b a)) (Prod a b)) :=
    (ReferenceIsometry.sumInr c (Prod b a)).applyPureVector Φ₀
  have hη : η.state.marginalB = σ := by
    apply State.ext
    have hp : η.Purifies σ := by
      simpa [η] using σ.canonicalPurification_purifies
    simpa [η, State.marginalB_matrix] using hp
  have hΦ₀ : Φ₀.Purifies τ := by
    simpa [Φ₀, τ, hη] using State.maxEntangledSidePureVector_purifies (a := a) η
  have hΦ : Φ.Purifies τ := by
    simpa [Φ] using
      ((ReferenceIsometry.sumInr c (Prod b a)).applyPureVector_purifies hΦ₀)
  have hcardTarget :
      Fintype.card (Prod a b) ≤ Fintype.card (Sum c (Prod b a)) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod]
    calc
      Fintype.card a * Fintype.card b = Fintype.card b * Fintype.card a :=
        Nat.mul_comm _ _
      _ ≤ Fintype.card c + Fintype.card b * Fintype.card a :=
        Nat.le_add_left _ _
  obtain ⟨Ψ, hΨ, hoverlap⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := Φ) (ρ := τ) (σ := ψ.state.marginalAB) hΦ hcardTarget
  have hΨ₀ : Ψ₀.Purifies ψ.state.marginalAB := by
    simpa [Ψ₀] using ψ.reindex_prodComm_purifies_marginalA
  have hcardIso :
      Fintype.card c ≤ Fintype.card (Sum c (Prod b a)) := by
    rw [Fintype.card_sum]
    exact Nat.le_add_right _ _
  obtain ⟨V, hV⟩ :=
    PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hΨ₀ hΨ hcardIso
  have hscale :=
    referenceIsometryRightBlockK_card_mul_overlapSq_le_scaleFeasible_trace
      (a := a) (b := b) (c := c) ψ V η hT
  have hfid :
      ψ.state.marginalAB.squaredFidelity τ =
        (V.applyPureVector Ψ₀).overlapSq Φ := by
    rw [hV] at hoverlap
    calc
      ψ.state.marginalAB.squaredFidelity τ =
          τ.squaredFidelity ψ.state.marginalAB := State.squaredFidelity_comm _ _
      _ = Φ.overlapSq (V.applyPureVector Ψ₀) := hoverlap.symm
      _ = (V.applyPureVector Ψ₀).overlapSq Φ := PureVector.overlapSq_comm_endpoint _ _
  rw [hfid]
  simpa [Ψ₀, Φ, τ] using hscale

private theorem dualEffectKrausSuccessVector_dilation_overlap_eq_sqrt_trace
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (K : κ → Matrix a c ℂ)
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c))
    (hpos :
      0 < (rankOneMatrix
        (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re) :
    let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
    let η := State.pureVectorNormalize v hpos
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ :=
      (contractionDilationReferenceIsometry
        (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    Ψ.overlap Φ =
      (((Real.sqrt
        (rankOneMatrix
          (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re) : ℝ) : ℂ) := by
  classical
  intro v η Ψ₀ Ψ Φ₀ Φ
  let t : ℝ := (rankOneMatrix v).trace.re
  have htpos : 0 < t := hpos
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have htrace_im : (rankOneMatrix v).trace.im = 0 :=
    (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).2.symm
  have htrace_complex : (rankOneMatrix v).trace = (t : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using htrace_im
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  have hsqrt_inv_mul_trace :
      ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (rankOneMatrix v).trace) =
        ((Real.sqrt t : ℝ) : ℂ) := by
    rw [htrace_complex]
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt ht_nonneg]
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  have hnorm :
      (∑ x : Prod κ b, star (v x) * v x) = (rankOneMatrix v).trace := by
    simp [rankOneMatrix_trace, dotProduct, mul_comm]
  have hv_dot_re : (v ⬝ᵥ fun i => star (v i)).re = t := by
    simp [t, rankOneMatrix_trace, dotProduct, mul_comm]
  have hpsi_dot_re :
      ((dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K) ⬝ᵥ
          fun i => star (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K i)).re = t := by
    simpa [v] using hv_dot_re
  have hpsi_dot_re' :
      ((dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K) ⬝ᵥ
          fun i => (starRingEnd ℂ)
            (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K i)).re = t := by
    simpa using hpsi_dot_re
  have hsqrtdot :
      ((Real.sqrt
        (((dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K) ⬝ᵥ
          fun i => (starRingEnd ℂ)
            (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K i)).re) : ℂ)⁻¹) =
        ((Real.sqrt t : ℂ)⁻¹) := by
    exact congrArg (fun x : ℝ => ((Real.sqrt x : ℂ)⁻¹)) hpsi_dot_re'
  calc
    Ψ.overlap Φ =
        (((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
          (∑ x : Prod κ b, star (v x) * v x) := by
      rw [dualEffectKrausSuccessVector_dilation_overlap_eq_dot
        (a := a) (b := b) (c := c) ψ K hKstack η]
      simp [η, State.pureVectorNormalize_amp, v, hpsi_dot_re, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simpa [hsqrtdot, mul_assoc, mul_left_comm, mul_comm]
    _ = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (rankOneMatrix v).trace := by
      rw [hnorm]
    _ = ((Real.sqrt
          (rankOneMatrix
            (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re : ℝ) : ℂ) := by
      simpa [v, t] using hsqrt_inv_mul_trace

theorem dualEffectKrausSuccessVector_trace_le_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) {K : κ → Matrix a c ℂ}
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c)) :
    (rankOneMatrix
      (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re ≤
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  classical
  let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
  let t : ℝ := (rankOneMatrix v).trace.re
  have ht_nonneg : 0 ≤ t := by
    simpa [t] using
      (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).1
  by_cases hpos : 0 < t
  · let η : PureVector (Prod κ b) := State.pureVectorNormalize v (by simpa [t, v] using hpos)
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ :=
      (contractionDilationReferenceIsometry
        (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    have hΨ₀ : Ψ₀.Purifies ψ.state.marginalAB := by
      simpa [Ψ₀] using ψ.reindex_prodComm_purifies_marginalA
    have hΨ : Ψ.Purifies ψ.state.marginalAB := by
      simpa [Ψ] using
        ((contractionDilationReferenceIsometry
          (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector_purifies hΨ₀)
    have hΦ₀ :
        Φ₀.Purifies ((State.maximallyMixed a).prod η.state.marginalB) := by
      simpa [Φ₀] using State.maxEntangledSidePureVector_purifies (a := a) η
    have hΦ :
        Φ.Purifies ((State.maximallyMixed a).prod η.state.marginalB) := by
      simpa [Φ] using
        ((ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector_purifies hΦ₀)
    have hoverlap :
        Ψ.overlap Φ = (((Real.sqrt t : ℝ) : ℂ)) := by
      simpa [v, t, η, Ψ₀, Ψ, Φ₀, Φ] using
        (dualEffectKrausSuccessVector_dilation_overlap_eq_sqrt_trace
          (a := a) (b := b) (c := c) ψ K hKstack
          (by simpa [v, t] using hpos))
    have habs_le :
        Complex.abs (Ψ.overlap Φ) ≤
          ψ.state.marginalAB.fidelity ((State.maximallyMixed a).prod η.state.marginalB) :=
      State.pureVector_abs_overlap_le_fidelity hΨ hΦ
    have hsqrt_le :
        Real.sqrt t ≤
          ψ.state.marginalAB.fidelity ((State.maximallyMixed a).prod η.state.marginalB) := by
      simpa [hoverlap, abs_of_nonneg (Real.sqrt_nonneg t)] using habs_le
    have ht_le_sq :
        t ≤ ψ.state.marginalAB.squaredFidelity
          ((State.maximallyMixed a).prod η.state.marginalB) := by
      rw [State.squaredFidelity_eq_fidelity_sq]
      have hfid_nonneg :
          0 ≤ ψ.state.marginalAB.fidelity
            ((State.maximallyMixed a).prod η.state.marginalB) := traceNorm_nonneg _
      have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg t) hfid_nonneg).mpr hsqrt_le
      simpa [sq, Real.sq_sqrt ht_nonneg, mul_comm] using hsquare
    have hmem :
        ψ.state.marginalAB.squaredFidelity
            ((State.maximallyMixed a).prod η.state.marginalB) ∈
          ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a) := by
      exact ⟨η.state.marginalB, rfl⟩
    have hsup :
        ψ.state.marginalAB.squaredFidelity
            ((State.maximallyMixed a).prod η.state.marginalB) ≤
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
      le_csSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hmem
    exact le_trans (by simpa [t, v] using ht_le_sq) hsup
  · have ht_le_zero : t ≤ 0 := le_of_not_gt hpos
    have hzero_le_sup :
        0 ≤ sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
      let σ₀ : State b := State.maximallyMixed b
      have hmem :
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ₀) ∈
            ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a) := by
        exact ⟨σ₀, rfl⟩
      have hle_sup :
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ₀) ≤
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
        le_csSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hmem
      exact le_trans (State.squaredFidelity_nonneg _ _) hle_sup
    exact le_trans (by simpa [t, v] using ht_le_zero) hzero_le_sup

theorem dualEffectObjective_le_card_mul_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    ((ψ.state.marginalAC.matrix * M).trace).re ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  classical
  rcases State.exists_krausStack_contraction_conditionalMinEntropyDualEffectTransposeMatrixMap
      (a := a) (b := c) hM with ⟨K, hK, hKstack⟩
  exact ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet_of_successVector_trace_le
    (a := a) (b := b) hK
    (ψ.dualEffectKrausSuccessVector_trace_le_sSup_fidelityValueSet
      (a := a) (b := b) hKstack)

theorem dualEffectObjective_re_nonneg [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    0 ≤ ((ψ.state.marginalAC.matrix * M).trace).re := by
  rw [ψ.dualEffectObjective_re_eq_card_mul_trace_transposeLink (a := a) (b := b)]
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card a)
  have hproj :=
    ψ.dualEffectTransposeLinkOutputABA_projector_trace_re_nonneg
      (a := a) (b := b) hM
  exact mul_nonneg hcard_nonneg hproj

theorem dualEffectObjective_le_card_mul_sSup_fidelityValueSet_of_scaled_le
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (σ : State b) {t : ℝ} (ht : 0 ≤ t)
    (hobj :
      ((ψ.state.marginalAC.matrix * M).trace).re = (Fintype.card a : ℝ) * t)
    (hle :
      (((t : ℝ) : ℂ) • ((State.maximallyMixed a).prod σ).matrix) ≤
        ψ.state.marginalAB.matrix) :
    ((ψ.state.marginalAC.matrix * M).trace).re ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  let X : CMatrix (Prod a b) :=
    (((Real.sqrt t : ℝ) : ℂ) • ((State.maximallyMixed a).prod σ).matrix)
  have hfeas :
      State.ConditionalMaxFidelityBlockFeasible
        (a := a) ψ.state.marginalAB σ X := by
    exact State.ConditionalMaxFidelityBlockFeasible.of_scaled_le
      (a := a) (ρ := ψ.state.marginalAB) (σ := σ) ht hle
  have hval :
      State.conditionalMaxFidelityBlockExponentValue (a := a) X =
        (Fintype.card a : ℝ) * t := by
    simpa [X] using
      (State.ConditionalMaxFidelityBlockFeasible.of_scaled_le_blockExponentValue
        (a := a) (σ := σ) ht)
  have hmem :
      (Fintype.card a : ℝ) * t ∈
        ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a) := by
    refine ⟨σ, X, hfeas, ?_⟩
    exact hval.symm
  have hbdd :
      BddAbove
        (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) :=
    ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet_bddAbove (a := a)
  calc
    ((ψ.state.marginalAC.matrix * M).trace).re =
        (Fintype.card a : ℝ) * t := hobj
    _ ≤ sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet
          (a := a)) := le_csSup hbdd hmem
    _ = (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
          rw [← State.card_mul_sSup_fidelityValueSet_eq_sSup_conditionalMaxFidelityBlockExponentValueSet
            (a := a) ψ.state.marginalAB]


theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ψ.state.marginalAC.conditionalMinEntropyScale (a := a)) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
      (a := a) ψ.state.marginalAC hscale

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ψ.state.marginalAC.conditionalMinEntropyScale (a := a)) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    (a := a) hscale

/-- Pure endpoint assembly after identifying the max-fidelity endpoint with
the min-entropy dual-effect endpoint.

This packages the conic strong-duality result
`conditionalMinEntropyScale_eq_sSup_dualEffectValueSet`: the only remaining
source-shaped pure-state obligation is the equality between the dual-effect
supremum and the fidelity supremum. -/
theorem card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_dualEffect
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
      ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
  rw [hdual]
  exact (State.conditionalMinEntropyScale_eq_sSup_dualEffectValueSet
    (a := a) ψ.state.marginalAC).symm

/-- Pure endpoint assembly from the single remaining SDP equality:
the block-SDP endpoint for the `AB` marginal equals the dual-effect endpoint
for the complementary `AC` marginal. -/
theorem card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_blockDual
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
      ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
  refine ψ.card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_dualEffect
    (a := a) ?_
  rw [State.card_mul_sSup_fidelityValueSet_eq_sSup_conditionalMaxFidelityBlockExponentValueSet
    (a := a) ψ.state.marginalAB]
  exact hdual

/-- Endpoint min/max entropy duality once the pure-state dual-effect/fidelity
bridge is proved. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    (a := a)
    (ψ.card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_dualEffect
      (a := a) hdual)

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect
    (a := a) hdual

/-- Endpoint min/max entropy duality once the pure-state block/dual-effect SDP
equality is proved. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockDual
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    (a := a)
    (ψ.card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_blockDual
      (a := a) hdual)

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockDual
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockDual
    (a := a) hdual

theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_bounds
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_endpoint_bounds
      (a := a) ψ.state.marginalAC hforward hreverse

theorem conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_endpoint_forward_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤ T.trace.re) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive ≤
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
      (a := a) ψ.state.marginalAC hforward

/-- Pure-state forward endpoint order bridge through the dual-effect SDP.

This is the source-faithful form for the remaining forward weak-duality
obligation: it is enough to lower-bound the dual-effect optimum by each
max-fidelity candidate.  The conic strong-duality theorem
`conditionalMinEntropyScale_eq_sSup_dualEffectValueSet` then converts that
dual-effect optimum into the min-entropy scale. -/
theorem conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hlower : ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive ≤
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ψ.state.marginalAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hle_sup :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) := by
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    rw [← mul_sSup_image_eq
      (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
      (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos]
    refine csSup_le ?_ ?_
    · exact Set.Nonempty.image _
        (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
    · intro x hx
      rcases hx with ⟨y, ⟨σ, rfl⟩, rfl⟩
      exact hlower σ
  have hle :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
    rwa [ψ.state.marginalAC.conditionalMinEntropyScale_eq_sSup_dualEffectValueSet (a := a)]
  have hleft_pos :
      0 < (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ψ.state.marginalAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ψ.state.marginalAB.conditionalMaxEntropyExponent_pos (a := a)
  have hscale_pos : 0 < ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
    rw [ψ.state.marginalAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ψ.state.marginalAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hleft_pos hle)
    (le_of_lt (Real.log_pos one_lt_two))

/-- It suffices to exhibit a concrete feasible dual effect for every
max-fidelity side state.  This is the most useful proof obligation for the
remaining pure endpoint forward bridge. -/
theorem dualEffect_lower_bound_of_exists_feasible_objective
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hexists : ∀ σ : State b, ∃ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            ((ψ.state.marginalAC.matrix * M).trace).re) :
    ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) := by
  intro σ
  rcases hexists σ with ⟨M, hM, hleM⟩
  have hmem :
      ((ψ.state.marginalAC.matrix * M).trace).re ∈
        ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a) :=
    ⟨M, hM, rfl⟩
  have hle_sup :
      ((ψ.state.marginalAC.matrix * M).trace).re ≤
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) :=
    le_csSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet_bddAbove
      (a := a)) hmem
  exact hleM.trans hle_sup

/-- Endpoint equality from concrete feasible dual-effect witnesses for every
max-fidelity side state. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_exists_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hexists : ∀ σ : State b, ∃ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            ((ψ.state.marginalAC.matrix * M).trace).re) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  le_antisymm
    (ψ.conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
      (a := a)
      (ψ.dualEffect_lower_bound_of_exists_feasible_objective (a := a) hexists))
    (ψ.state.marginalAB
      |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
        (a := a) ψ.state.marginalAC
        (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
          (a := a) (b := b) hM))

/-- Non-positive-candidate endpoint equality from concrete feasible dual-effect
witnesses. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_exists_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hexists : ∀ σ : State b, ∃ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            ((ψ.state.marginalAC.matrix * M).trace).re) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_exists_dualEffect_lower_bound
    (a := a) hexists

/-- Pure complementary-marginal endpoint equality from the value-set forward
dual-effect lower bound and the already-proved reverse dual-effect upper
bound. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hlower : ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  le_antisymm
    (ψ.conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
      (a := a) hlower)
    (ψ.state.marginalAB
      |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
        (a := a) ψ.state.marginalAC
        (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
          (a := a) (b := b) hM))

/-- Non-positive-candidate version of
`conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound`. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hlower : ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    (a := a) hlower

/-- Pure-state version of the strong pointwise side-operator reverse wrapper.

For the source-faithful endpoint SDP bridge, prefer
`neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_dualEffect_bound`. -/
theorem neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_endpoint_reverse_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hreverse : ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ψ.state.marginalAC.conditionalMinEntropy ≤
      ψ.state.marginalAB.conditionalMaxEntropyPositive :=
  ψ.state.marginalAB
    |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_fidelity_reverse_bound
      (a := a) ψ.state.marginalAC hreverse

/-- Pure-state reverse endpoint order bridge through the correct dual-effect
objective.

This is the normalized finite-dimensional form of the remaining endpoint
link-map obligation: for every `AC` dual effect `M`, bound
`Tr(ρ_AC M)` by the max-fidelity endpoint on the complementary `AB` marginal. -/
theorem neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ψ.state.marginalAC.conditionalMinEntropy ≤
      ψ.state.marginalAB.conditionalMaxEntropyPositive :=
  ψ.state.marginalAB
    |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
      (a := a) ψ.state.marginalAC hdual

theorem neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    -ψ.state.marginalAC.conditionalMinEntropy ≤
      ψ.state.marginalAB.conditionalMaxEntropyPositive :=
  ψ.neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_dualEffect_bound
    (a := a)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Pure-state value-set form of the reverse endpoint bound through dual
effects. -/
theorem sSup_conditionalMinEntropyDualEffectValueSet_marginalAC_le_card_mul_sSup_fidelityValueSet_marginalAB_of_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
  ψ.state.marginalAB
    |>.sSup_conditionalMinEntropyDualEffectValueSet_le_card_mul_sSup_fidelityValueSet_of_dualEffect_bound
      (a := a) ψ.state.marginalAC hdual

theorem sSup_conditionalMinEntropyDualEffectValueSet_marginalAC_le_card_mul_sSup_fidelityValueSet_marginalAB
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
  ψ.sSup_conditionalMinEntropyDualEffectValueSet_marginalAC_le_card_mul_sSup_fidelityValueSet_marginalAB_of_dualEffect_bound
    (a := a)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Pure complementary-marginal endpoint equality from the two correct
one-sided source obligations: a forward fidelity/scale bound and a reverse
dual-effect bound. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re)
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_forward_dualEffect_bound
      (a := a) ψ.state.marginalAC hforward hdual

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re)
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    (a := a) hforward hdual

/-- The user-facing block-SDP weak-duality statement follows immediately from
the fidelity forward bound, because every block-feasible `X` is bounded by the
corresponding fidelity candidate. -/
theorem blockFeasible_trace_bound_by_scaleFeasible_of_fidelity_forward_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re) :
    ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re := by
  intro σ T X hX hT
  exact (hX.blockExponentValue_le_exponentCandidate (a := a)).trans (by
    rw [State.conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity]
    exact hforward σ T hT)

/-- A block-SDP trace bound implies the source-shaped fidelity forward bound.

This is the purely order-theoretic handoff from a future pointwise weak-duality
lemma for block feasible `X` to the fidelity value used in the conditional
max-entropy endpoint. -/
theorem fidelity_forward_bound_of_blockFeasible_trace_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hblock : ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re) :
    ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re := by
  intro σ T hT
  rcases ψ.state.marginalAB.exists_ConditionalMaxFidelityBlockFeasible_trace_re_eq_fidelity
      (a := a) σ with ⟨X, hX, hval⟩
  have hle := hblock σ T X hX hT
  rw [State.conditionalMaxFidelityBlockExponentValue_eq] at hle
  rw [State.squaredFidelity_eq_fidelity_sq]
  have htrace :
      X.trace.re =
        ψ.state.marginalAB.fidelity ((State.maximallyMixed a).prod σ) := by
    simpa [State.conditionalMaxFidelityBlockValue] using hval
  simpa [htrace] using hle

/-- A block-SDP trace bound plus the already-proved dual-effect reverse bound
gives the endpoint positive max/min entropy equality for pure complementary
marginals.

The remaining mathematical work is exactly the block feasible trace bound
appearing as `hblock`; all value-set, logarithm and reverse-duality assembly is
handled here. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hblock : ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    (a := a)
    (ψ.fidelity_forward_bound_of_blockFeasible_trace_bound (a := a) hblock)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Non-positive-candidate version of
`conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound`. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hblock : ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound
    (a := a) hblock

/-- Endpoint conditional min/max duality for normalized finite-dimensional
pure complementary marginals, in the positive-candidate convention for
conditional max-entropy. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    (a := a)
    (fun σ T hT => ψ.fidelity_forward_bound_by_scaleFeasible (a := a) σ T hT)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Endpoint conditional min/max duality for normalized finite-dimensional
pure complementary marginals. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    (a := a)

end PureVector

namespace SubnormalizedState

variable {c : Type x} [Fintype c] [DecidableEq c]

/-- Explicit scaled-pure subnormalized endpoint duality, obtained by shifting
the normalized complementary-marginal equality through the common scale. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_scaled_pure
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c) ψ t ht.le ht1).conditionalMaxEntropy =
      - (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c) ψ t ht.le ht1).conditionalMinEntropy := by
  rw [abMarginalFromScaledTripartitePure, acMarginalFromScaledTripartitePure,
    conditionalMaxEntropy_ofStateScale (a := a) (b := b) ψ.state.marginalAB ht ht1,
    conditionalMinEntropy_ofStateScale (a := a) (b := c) ψ.state.marginalAC ht ht1]
  rw [PureVector.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    (a := a) (b := b) (c := c) ψ]
  ring

/-- Relation-level subnormalized unsmoothed min/max entropy duality on
complementary scaled-pure marginals. -/
theorem conditionalMinMaxEntropyDualOn_complementaryPureMarginals
    {a : Type u} {b : Type v} {c : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty a] [Nonempty b] [Nonempty c] :
    ConditionalMinMaxEntropyDualOn (a := a) (b := b) (c := c)
      (ComplementaryPureMarginalRel (a := a) (b := b) (c := c)) := by
  intro ρAB ρAC hrel
  rcases hrel with ⟨ψ, t, ht, ht1, hAB, hAC⟩
  rw [hAB, hAC]
  exact conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_scaled_pure
    (a := a) (b := b) (c := c) ψ ht ht1

end SubnormalizedState

namespace State

/-- Unsmoothed conditional min/max entropy duality on complementary pure
marginals.

This is the relation-parametric `hdual` input required by the smooth
min/max-duality bridge in `QIT.Information.Smooth`. -/
theorem conditionalMinMaxEntropyDualOn_complementaryPureMarginals
    {a : Type u} {b : Type v} {c : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty a] [Nonempty b] [Nonempty c] :
    ConditionalMinMaxEntropyDualOn (a := a) (b := b) (c := c)
      (ComplementaryPureMarginalRel (a := a) (b := b) (c := c)) := by
  intro ρAB ρAC hrel
  rcases hrel with ⟨Ψ, hpur, hAC⟩
  let Ω : PureVector (Prod (Prod a b) c) :=
    Ψ.reindex (Equiv.prodComm c (Prod a b))
  have hAB : Ω.state.marginalAB = ρAB := by
    apply State.ext
    simpa [Ω, State.marginalAB_eq_marginalA, PureVector.reindex_state, State.reindex,
      State.marginalA, State.marginalB, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply] using hpur
  have hAC' : Ω.state.marginalAC = ρAC := by
    subst hAC
    apply State.ext
    ext ac ac'
    simp [Ω, acMarginalFromABPurification, State.marginalAC_matrix, State.marginalB_matrix,
      PureVector.reindex_state, State.reindex, partialTraceA,
      PureVector.state_matrix, rankOneMatrix_apply, abToACReferenceEquiv]
  rw [← hAB, ← hAC']
  exact PureVector.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    (a := a) (b := b) (c := c) Ω

/-- A normalized finite-dimensional conditional max-entropy is bounded below by
minus the logarithm of the conditioned register dimension. -/
theorem neg_log2_card_left_le_conditionalMaxEntropy
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    -log2 (Fintype.card a : ℝ) ≤ ρ.conditionalMaxEntropy := by
  obtain ⟨Ψ, hΨ⟩ :=
    State.exists_purification_on_reference_of_card_le
      (r := Prod a b) ρ (Nat.le_refl _)
  let Ω : PureVector (Prod (Prod a b) (Prod a b)) :=
    Ψ.reindex (Equiv.prodComm (Prod a b) (Prod a b))
  have hAB : Ω.state.marginalAB = ρ := by
    apply State.ext
    simpa [Ω, State.marginalAB_eq_marginalA, PureVector.reindex_state, State.reindex,
      State.marginalA, State.marginalB, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply] using hΨ
  have hdual :
      Ω.state.marginalAB.conditionalMaxEntropy =
        -Ω.state.marginalAC.conditionalMinEntropy :=
    PureVector.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
      (a := a) (b := b) (c := Prod a b) Ω
  have hmin :
      Ω.state.marginalAC.conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) :=
    Ω.state.marginalAC.conditionalMinEntropy_le_log2_card_left
      (a := a) (b := Prod a b)
  rw [← hAB, hdual]
  exact neg_le_neg hmin

end State

namespace SubnormalizedState

variable {c : Type x} [Fintype c] [DecidableEq c]

/-- A subnormalized conditional min-entropy is uniformly bounded above when the
state trace has a positive lower bound. -/
theorem conditionalMinEntropy_le_of_trace_lower_bound
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    ρ.conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) - log2 δ := by
  have hρ : 0 < ρ.matrix.trace.re := lt_of_lt_of_le hδ hδρ
  rw [← SubnormalizedState.ofStateScale_normalize_trace_eq ρ hρ]
  rw [conditionalMinEntropy_ofStateScale
    (a := a) (b := b) (ρ.normalize hρ.ne') hρ ρ.trace_le_one]
  have hnorm :
      (ρ.normalize hρ.ne').conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) :=
    (ρ.normalize hρ.ne').conditionalMinEntropy_le_log2_card_left (a := a) (b := b)
  have hlog :
      log2 δ ≤ log2 ρ.matrix.trace.re := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hδ hδρ) (le_of_lt (Real.log_pos one_lt_two))
  linarith

/-- A subnormalized conditional max-entropy is uniformly bounded below when the
state trace has a positive lower bound. -/
theorem conditionalMaxEntropy_ge_of_trace_lower_bound
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    -log2 (Fintype.card a : ℝ) + log2 δ ≤ ρ.conditionalMaxEntropy := by
  have hρ : 0 < ρ.matrix.trace.re := lt_of_lt_of_le hδ hδρ
  rw [← SubnormalizedState.ofStateScale_normalize_trace_eq ρ hρ]
  rw [conditionalMaxEntropy_ofStateScale
    (a := a) (b := b) (ρ.normalize hρ.ne') hρ ρ.trace_le_one]
  have hnorm :
      -log2 (Fintype.card a : ℝ) ≤ (ρ.normalize hρ.ne').conditionalMaxEntropy :=
    (ρ.normalize hρ.ne').neg_log2_card_left_le_conditionalMaxEntropy (a := a) (b := b)
  have hlog :
      log2 δ ≤ log2 ρ.matrix.trace.re := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hδ hδρ) (le_of_lt (Real.log_pos one_lt_two))
  linarith

/-- Smooth subnormalized min-entropy candidate sets are nonempty for
nonnegative smoothing radius. -/
theorem SmoothConditionalMinEntropyCandidate_set_nonempty_of_nonneg
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ} (hε : 0 ≤ ε) :
    ({h : ℝ | SmoothConditionalMinEntropyCandidate (a := a) ρ ε h}).Nonempty :=
  ⟨ρ.conditionalMinEntropy, ρ, ρ.purifiedBall_self_of_nonneg hε, rfl⟩

/-- Smooth subnormalized max-entropy candidate sets are nonempty for
nonnegative smoothing radius. -/
theorem SmoothConditionalMaxEntropyCandidate_set_nonempty_of_nonneg
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ} (hε : 0 ≤ ε) :
    ({h : ℝ | SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h}).Nonempty :=
  ⟨ρ.conditionalMaxEntropy, ρ, ρ.purifiedBall_self_of_nonneg hε, rfl⟩

/-- Smooth subnormalized min-entropy candidates are bounded above in any ball
whose radius is below `sqrt (Tr ρ)`. -/
theorem SmoothConditionalMinEntropyCandidate_bddAbove_of_lt_sqrt_trace
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    BddAbove {h : ℝ |
      SmoothConditionalMinEntropyCandidate (a := a) ρ ε h} := by
  let δ : ℝ := (Real.sqrt ρ.matrix.trace.re - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε)
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    dsimp [δ]
    exact ρ.purifiedBall_trace_lower_bound ρ' hε hball
  exact ρ'.conditionalMinEntropy_le_of_trace_lower_bound
    (a := a) (b := b) hδ hδρ'

/-- Smooth subnormalized max-entropy candidates are bounded below in any ball
whose radius is below `sqrt (Tr ρ)`. -/
theorem SmoothConditionalMaxEntropyCandidate_bddBelow_of_lt_sqrt_trace
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    BddBelow {h : ℝ |
      SmoothConditionalMaxEntropyCandidate (a := a) ρ ε h} := by
  let δ : ℝ := (Real.sqrt ρ.matrix.trace.re - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε)
  refine ⟨-log2 (Fintype.card a : ℝ) + log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    dsimp [δ]
    exact ρ.purifiedBall_trace_lower_bound ρ' hε hball
  exact ρ'.conditionalMaxEntropy_ge_of_trace_lower_bound
    (a := a) (b := b) hδ hδρ'

/-- Source-faithful subnormalized smooth min/max duality for a scaled pure
tripartite state.  The public surface is the scaled-pure representation:
`PureVector ψ`, `0 < t`, `t ≤ 1`, `0 ≤ ε`, and `ε < sqrt t`. -/
theorem smoothConditionalMaxEntropy_marginalAB_eq_neg_smoothConditionalMinEntropy_marginalAC_of_scaled_pure
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) {t ε : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt t) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1).smoothConditionalMaxEntropy ε =
      - (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht.le ht1).smoothConditionalMinEntropy ε := by
  classical
  let ρAB : SubnormalizedState (Prod a b) :=
    abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1
  let ρAC : SubnormalizedState (Prod a c) :=
    acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1
  have hABtrace : ρAB.matrix.trace.re = t := by
    simpa [ρAB, abMarginalFromScaledTripartitePure] using
      ofStateScale_trace_re ψ.state.marginalAB t ht.le ht1
  have hACtrace : ρAC.matrix.trace.re = t := by
    simpa [ρAC, acMarginalFromScaledTripartitePure] using
      ofStateScale_trace_re ψ.state.marginalAC t ht.le ht1
  have hεAB : ε < Real.sqrt ρAB.matrix.trace.re := by
    rwa [hABtrace]
  have hεAC : ε < Real.sqrt ρAC.matrix.trace.re := by
    rwa [hACtrace]
  have hpair :
      EmbeddedSmoothConditionalMinMaxPairing (a := a) (b := b) (c := c)
        ψ t ht.le ht1 ε :=
    embeddedSmoothConditionalMinMaxPairing_of_scaled_pure
      (a := a) (b := b) (c := c) ψ t ht.le ht1 ε
  change ρAB.smoothConditionalMaxEntropy ε =
    -ρAC.smoothConditionalMinEntropy ε
  refine smoothConditionalMaxEntropy_eq_neg_smoothConditionalMinEntropy_of_candidate_bounds
    (a := a) (b := b) (c := c)
    (ρAB := ρAB) (ρAC := ρAC) (ε := ε)
    (ρAB.SmoothConditionalMaxEntropyCandidate_set_nonempty_of_nonneg (a := a) hε0)
    (ρAC.SmoothConditionalMinEntropyCandidate_set_nonempty_of_nonneg (a := a) hε0)
    (ρAB.SmoothConditionalMaxEntropyCandidate_bddBelow_of_lt_sqrt_trace (a := a) hεAB)
    (ρAC.SmoothConditionalMinEntropyCandidate_bddAbove_of_lt_sqrt_trace (a := a) hεAC)
    ?_ ?_
  · intro h hcand
    rcases hcand with ⟨ρAB', hballAB, hh⟩
    have hemb :
        EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c)
          ψ t ht.le ht1 ε ρAB' :=
      hpair.ab_to_ac_of_purifiedBall (a := a) (b := b) (c := c)
        ρAB' (by simpa [ρAB] using hballAB)
    have hρAB' : 0 < ρAB'.matrix.trace.re :=
      SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
        ρAB ρAB' hεAB hballAB
    obtain ⟨ρACPlus', _hballPlus, hrel⟩ :=
      hemb.exists_complementaryPureMarginalRel
        (a := a) (b := b) (c := c) hρAB'
    have hdual :
        ρAB'.conditionalMaxEntropy = -ρACPlus'.conditionalMinEntropy :=
      (conditionalMinMaxEntropyDualOn_complementaryPureMarginals
        (a := a) (b := b) (c := ACPlusReference a b c))
        ρAB' ρACPlus' hrel
    have hbase :
        embeddedACPlusBaseFromScaledPure (a := a) (b := b) (c := c)
          ψ t ht.le ht1 =
          ρAC.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ABHat a b) c) := by
      simpa [ρAC] using
        embeddedACPlusBaseFromScaledPure_eq_conditioningIsometryApply_sumInr
          (a := a) (b := b) (c := c) ψ t ht.le ht1
    have hcandPlus :
        SmoothConditionalMinEntropyCandidate (a := a)
          (ρAC.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ABHat a b) c)) ε (-h) := by
      refine ⟨ρACPlus', ?_, ?_⟩
      · rwa [← hbase]
      · rw [hh, hdual]
        ring
    exact SmoothConditionalMinEntropyCandidate.conditioningIsometryApply_sumInr_compress
      (a := a) (b := c) (extra := ABHat a b) ρAC hεAC hcandPlus
  · intro m hcand
    rcases hcand with ⟨ρAC', hballAC, hm⟩
    have hemb :
        EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c)
          ψ t ht.le ht1 ε ρAC' :=
      hpair.ac_to_ab_of_purifiedBall (a := a) (b := b) (c := c)
        ρAC' (by simpa [ρAC] using hballAC)
    have hρAC' : 0 < ρAC'.matrix.trace.re :=
      SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
        ρAC ρAC' hεAC hballAC
    obtain ⟨ρABPlus', _hballPlus, hrel⟩ :=
      hemb.exists_complementaryPureMarginalRel
        (a := a) (b := b) (c := c) hρAC'
    have hdual :
        ρABPlus'.conditionalMaxEntropy = -ρAC'.conditionalMinEntropy :=
      (conditionalMinMaxEntropyDualOn_complementaryPureMarginals
        (a := a) (b := ABPlusReference a b c) (c := c))
        ρABPlus' ρAC' hrel
    have hbase :
        embeddedABPlusBaseFromScaledPure (a := a) (b := b) (c := c)
          ψ t ht.le ht1 =
          ρAB.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ACHat a c) b) := by
      simpa [ρAB] using
        embeddedABPlusBaseFromScaledPure_eq_conditioningIsometryApply_sumInr
          (a := a) (b := b) (c := c) ψ t ht.le ht1
    have hcandPlus :
        SmoothConditionalMaxEntropyCandidate (a := a)
          (ρAB.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ACHat a c) b)) ε (-m) := by
      refine ⟨ρABPlus', ?_, ?_⟩
      · rwa [← hbase]
      · rw [hm, hdual]
    exact SmoothConditionalMaxEntropyCandidate.conditioningIsometryApply_sumInr_compress
      (a := a) (b := b) (extra := ACHat a c) ρAB hεAB hcandPlus

end SubnormalizedState

end

end QIT
