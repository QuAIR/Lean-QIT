/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import QIT.Util.SDP.PSDCone
public import QIT.Util.SDP.StrongDuality
public import QIT.OneShot.Smooth
public import QIT.States.Geometry.FuchsVdG
public import QIT.Information.Renyi.Renyi
public import QIT.Information.Renyi.ConditionalRenyiTraceBridge
public import QIT.Util.BlockMatrix
import QIT.States.TraceNorm.Spectral
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Endpoint min/max entropy scales

This module separates the raw endpoint optimization values underneath the
definition-level conditional min/max entropies in `QIT.OneShot.Smooth`.

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
    simp [PureVector.overlap, mul_comm]
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
    simp [rankOneMatrix_trace, dotProduct]
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

omit [DecidableEq a] [DecidableEq b] in
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

omit [Fintype a] [DecidableEq a] in
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
          simp [smoothEndpointKrausAdjoint]

theorem smoothEndpointKrausStack_contraction_of_traceNonincreasing
    (K : κ → Matrix b a ℂ)
    (hTNI : IsTraceNonincreasing (ofKraus K)) :
    Matrix.conjTranspose (smoothEndpointKrausStack K) *
        smoothEndpointKrausStack K ≤ (1 : CMatrix a) := by
  rw [smoothEndpointKrausStack_conjTranspose_mul]
  exact smoothEndpointKrausAdjoint_one_le_of_traceNonincreasing K hTNI

end MatrixMap
end

end QIT
