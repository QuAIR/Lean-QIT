/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.SDP.HermitianPSDTraceDuality
public import QIT.Information.Renyi.Renyi
public import QIT.Information.Renyi.ConditionalRenyi
public import QIT.OneShot.SmoothEndpoint
public import QIT.Measurements.Map
public import QIT.Measurements.Projective
public import QIT.States.Purification.Uhlmann
public import QIT.States.Schatten
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Sandwiched Renyi DPI, duality, and measurement monotonicity (statement layer)

Source-shaped statement targets for the deep theorems on the proof route of the
tripartite entropic uncertainty relation: sandwiched Renyi data processing,
upward sandwiched conditional Renyi duality, and the measurement-map monotonicity
that follows from DPI.

These are statement-only (`def : Prop`); the proofs require pinching and complex
interpolation not currently available in the local stack, so no proof is claimed
and no forbidden placeholder tokens are introduced.

Source: Tomamichel2015FiniteResources, `renyi.tex` (sandwiched DPI / pinching),
`cond.tex` (upward conditional Renyi duality, `pr:dual-new`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

section ComplexInterpolation

/-- Unit-bound form of the Hadamard three-lines theorem.

This is the scalar analytic kernel needed by the sandwiched Renyi interpolation
route: once a trace-pairing family is built on the strip and bounded by `1` on
both boundary lines, its interior value is bounded by `1`. -/
theorem complex_three_lines_unit_bound
    {f : ℂ → ℂ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ 1)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f z‖ ≤ 1) :
    ‖f (θ : ℂ)‖ ≤ 1 := by
  have hz : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hθ0, hθ1]
  have h :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := f) (z := (θ : ℂ)) (a := (1 : ℝ)) (b := (1 : ℝ))
      (l := (0 : ℝ)) (u := (1 : ℝ))
      (by norm_num) hz hd hB hleft hright
  simpa using h

/-- Constant-bound form of the Hadamard three-lines theorem.

This is the version used after normalizing a trace-pairing analytic family by
the candidate Schatten bound. The constant is assumed positive; zero-norm test
operators are handled separately by the surrounding Schatten variational
interface. -/
theorem complex_three_lines_const_bound
    {f : ℂ → ℂ} {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC : 0 < C)
    (hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ C)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f z‖ ≤ C) :
    ‖f (θ : ℂ)‖ ≤ C := by
  have hz : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hθ0, hθ1]
  have h :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := f) (z := (θ : ℂ)) (a := C) (b := C)
      (l := (0 : ℝ)) (u := (1 : ℝ))
      (by norm_num) hz hd hB hleft hright
  have hmain : ‖f (θ : ℂ)‖ ≤ C ^ (1 - θ) * C ^ θ := by
    simpa using h
  have hrhs : C ^ (1 - θ) * C ^ θ = C := by
    calc
      C ^ (1 - θ) * C ^ θ = C ^ ((1 - θ) + θ) := by
        rw [← Real.rpow_add hC]
      _ = C ^ (1 : ℝ) := by ring_nf
      _ = C := by rw [Real.rpow_one]
  exact hmain.trans_eq hrhs

/-- Unit-bound three-lines theorem for the local Beigi strip convention.

The current rotated Kraus family is written as `L_z = τ^z K σ^{-z}`.  Its
`p = 1` boundary is `Re z = 0`, while its `p = ∞` boundary is
`Re z = -1/2`.  This lemma transfers the standard `0 ≤ Re w ≤ 1` strip by
`z = -w/2`, so the interpolation point is `z = -θ/2`. -/
theorem complex_three_lines_unit_bound_neg_half_strip
    {f : ℂ → ℂ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd : DiffContOnCl ℂ (fun w : ℂ => f (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ (fun w : ℂ => f (-(w / 2)))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ 1)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ), ‖f z‖ ≤ 1) :
    ‖f (-((θ : ℂ) / 2))‖ ≤ 1 := by
  have hleft' : ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f (-(w / 2))‖ ≤ 1 := by
    intro w hw
    apply hleft
    simpa [Complex.div_re, hw]
  have hright' : ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f (-(w / 2))‖ ≤ 1 := by
    intro w hw
    apply hright
    simp at hw
    norm_num [Complex.div_re, hw]
  have h := complex_three_lines_unit_bound (f := fun w : ℂ => f (-(w / 2)))
    hθ0 hθ1 hd hB hleft' hright'
  simpa using h

/-- Constant-bound three-lines theorem for the local Beigi strip convention.

This is the non-normalized companion to
`complex_three_lines_unit_bound_neg_half_strip`, used after scaling the scalar
trace-pairing family by its candidate Schatten bound. -/
theorem complex_three_lines_const_bound_neg_half_strip
    {f : ℂ → ℂ} {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC : 0 < C)
    (hd : DiffContOnCl ℂ (fun w : ℂ => f (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ (fun w : ℂ => f (-(w / 2)))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ C)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ), ‖f z‖ ≤ C) :
    ‖f (-((θ : ℂ) / 2))‖ ≤ C := by
  have hleft' : ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f (-(w / 2))‖ ≤ C := by
    intro w hw
    apply hleft
    simpa [Complex.div_re, hw]
  have hright' : ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f (-(w / 2))‖ ≤ C := by
    intro w hw
    apply hright
    simp at hw
    norm_num [Complex.div_re, hw]
  have h := complex_three_lines_const_bound (f := fun w : ℂ => f (-(w / 2)))
    hθ0 hθ1 hC hd hB hleft' hright'
  simpa using h

/-- For Holder-conjugate exponents, the interpolation parameter `θ = 1 / q`
lies in the unit interval. -/
theorem holderConjugate_inv_right_mem_unit_interval
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    0 ≤ 1 / q ∧ 1 / q ≤ 1 := by
  constructor
  · exact one_div_nonneg.mpr (le_of_lt hpq.symm.pos)
  · rw [one_div]
    exact inv_le_one_of_one_le₀ (le_of_lt hpq.symm.lt)

end ComplexInterpolation

/-- Dual Renyi parameter for the low-`α` purification/conditional-duality route.

For `1 / 2 < α < 1`, this parameter satisfies `1 < β` and
`1 / α + 1 / β = 2`, so it is the algebraic bridge from the subunit
sandwiched-Renyi range to the already-proved `β > 1` endpoint. -/
def renyiDualParameter (α : ℝ) : ℝ :=
  α / (2 * α - 1)

/-- The denominator in the dual Renyi parameter is positive for
`1 / 2 < α`. -/
theorem renyiDualParameter_den_pos {α : ℝ} (hα_half : 1 / 2 < α) :
    0 < 2 * α - 1 := by
  linarith

/-- The low-`α` dual parameter is positive. -/
theorem renyiDualParameter_pos {α : ℝ} (hα_half : 1 / 2 < α) :
    0 < renyiDualParameter α := by
  have hα_pos : 0 < α := by linarith
  have hden : 0 < 2 * α - 1 := renyiDualParameter_den_pos hα_half
  exact div_pos hα_pos hden

/-- The low-`α` dual parameter is nonzero. -/
theorem renyiDualParameter_ne_zero {α : ℝ} (hα_half : 1 / 2 < α) :
    renyiDualParameter α ≠ 0 :=
  ne_of_gt (renyiDualParameter_pos hα_half)

/-- The low-`α` dual parameter lies in the already-proved `> 1` range. -/
theorem renyiDualParameter_gt_one {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    1 < renyiDualParameter α := by
  have hden : 0 < 2 * α - 1 := renyiDualParameter_den_pos hα_half
  rw [renyiDualParameter]
  rw [lt_div_iff₀ hden]
  linarith

/-- The low-`α` dual parameter is in the conditional-Renyi admissible range. -/
theorem renyiDualParameter_half_le {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    1 / 2 ≤ renyiDualParameter α := by
  linarith [renyiDualParameter_gt_one hα_half hα_lt_one]

/-- The low-`α` dual parameter is not the singular value `1`. -/
theorem renyiDualParameter_ne_one {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    renyiDualParameter α ≠ 1 :=
  ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)

/-- The source duality relation `1 / α + 1 / β = 2` for
`β = α / (2α - 1)`. -/
theorem renyiDualParameter_inv_add_inv_eq_two {α : ℝ}
    (hα_ne_zero : α ≠ 0) :
    1 / α + 1 / renyiDualParameter α = 2 := by
  unfold renyiDualParameter
  field_simp [hα_ne_zero]
  ring

/-- The source duality relation specialized to `1 / 2 < α < 1`. -/
theorem renyiDualParameter_inv_add_inv_eq_two_of_half_lt {α : ℝ}
    (hα_half : 1 / 2 < α) (_hα_lt_one : α < 1) :
    1 / α + 1 / renyiDualParameter α = 2 := by
  have hα_pos : 0 < α := by linarith
  exact renyiDualParameter_inv_add_inv_eq_two (ne_of_gt hα_pos)

/-- Above `1`, the same algebraic dual parameter lies back in the subunit
range. This is the reverse direction needed when symmetry of the conditional
Renyi duality statement swaps the two exponents. -/
theorem renyiDualParameter_half_lt_of_one_lt {β : ℝ} (hβ_gt_one : 1 < β) :
    1 / 2 < renyiDualParameter β := by
  have hden : 0 < 2 * β - 1 := by linarith
  rw [renyiDualParameter]
  rw [lt_div_iff₀ hden]
  linarith

/-- Above `1`, the same algebraic dual parameter is strictly below `1`. -/
theorem renyiDualParameter_lt_one_of_one_lt {β : ℝ} (hβ_gt_one : 1 < β) :
    renyiDualParameter β < 1 := by
  have hden : 0 < 2 * β - 1 := by linarith
  rw [renyiDualParameter]
  rw [div_lt_one hden]
  linarith

/-- The denominator of the dual parameter after one dualization is the inverse
of the original denominator. -/
theorem renyiDualParameter_den_eq_inv_den {α : ℝ}
    (hden : 2 * α - 1 ≠ 0) :
    2 * renyiDualParameter α - 1 = 1 / (2 * α - 1) := by
  unfold renyiDualParameter
  field_simp [hden]
  ring

/-- The Renyi dual-parameter map is an involution away from its singular
denominator. -/
theorem renyiDualParameter_involutive {α : ℝ}
    (_hα_ne_zero : α ≠ 0) (hden : 2 * α - 1 ≠ 0) :
    renyiDualParameter (renyiDualParameter α) = α := by
  unfold renyiDualParameter
  have hden' : 2 * (α / (2 * α - 1)) - 1 = 1 / (2 * α - 1) := by
    field_simp [hden]
    ring_nf
  rw [hden']
  rw [div_eq_mul_inv]
  rw [one_div, inv_inv]
  rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hden, mul_one]

/-- The involution law specialized to the low-`α` source range. -/
theorem renyiDualParameter_involutive_of_half_lt_lt_one {α : ℝ}
    (hα_half : 1 / 2 < α) (_hα_lt_one : α < 1) :
    renyiDualParameter (renyiDualParameter α) = α := by
  have hα_pos : 0 < α := by linarith
  have hden_pos : 0 < 2 * α - 1 := renyiDualParameter_den_pos hα_half
  exact renyiDualParameter_involutive (ne_of_gt hα_pos) (ne_of_gt hden_pos)

/-- The involution law specialized to the `> 1` endpoint range. -/
theorem renyiDualParameter_involutive_of_one_lt {β : ℝ}
    (hβ_gt_one : 1 < β) :
    renyiDualParameter (renyiDualParameter β) = β := by
  have hβ_pos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  have hden_pos : 0 < 2 * β - 1 := by linarith
  exact renyiDualParameter_involutive (ne_of_gt hβ_pos) (ne_of_gt hden_pos)

/-- Packaged admissibility facts for the dual parameter of a strict subunit
Renyi exponent. -/
theorem renyiDualParameter_low_admissible {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    1 / 2 ≤ renyiDualParameter α ∧
      renyiDualParameter α ≠ 1 ∧
        1 < renyiDualParameter α ∧
          1 / α + 1 / renyiDualParameter α = 2 := by
  exact ⟨renyiDualParameter_half_le hα_half hα_lt_one,
    renyiDualParameter_ne_one hα_half hα_lt_one,
    renyiDualParameter_gt_one hα_half hα_lt_one,
    renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one⟩

/-- Packaged admissibility facts when starting from the already-proved
`β > 1` endpoint range and dualizing back to a subunit exponent. -/
theorem renyiDualParameter_high_admissible {β : ℝ}
    (hβ_gt_one : 1 < β) :
    1 / 2 < renyiDualParameter β ∧
      renyiDualParameter β < 1 ∧
        1 / β + 1 / renyiDualParameter β = 2 := by
  have hβ_pos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  exact ⟨renyiDualParameter_half_lt_of_one_lt hβ_gt_one,
    renyiDualParameter_lt_one_of_one_lt hβ_gt_one,
    renyiDualParameter_inv_add_inv_eq_two (ne_of_gt hβ_pos)⟩

namespace MatrixMap

section L2OperatorEndpoint

open scoped Matrix.Norms.L2Operator

local instance cMatrixNonUnitalCStarAlgebraForEndpoint (n : Type*) [Fintype n]
    [DecidableEq n] : NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance cMatrixCStarAlgebraForEndpoint (n : Type*) [Fintype n]
    [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) := ⟨⟩

/-- The L2-operator norm of the finite matrix identity is at most one.

The nonempty case has equality, but the inequality is the endpoint fact that is
valid without adding a `Nonempty` assumption on the finite index type. -/
theorem cMatrix_l2OperatorNorm_one_le :
    ‖(1 : CMatrix a)‖ ≤ (1 : ℝ) := by
  rw [Matrix.cstar_norm_def]
  simpa using
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := EuclideanSpace ℂ a))

/-- Matrix unit-ball criterion for the L2 operator norm.

This is the finite-dimensional C⋆-algebra step behind the `p = ∞` endpoint:
`Xᴴ X ≤ I` implies `‖X‖∞ ≤ 1`. -/
theorem cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one
    (X : CMatrix a) (hX : Matrix.conjTranspose X * X ≤ 1) :
    ‖X‖ ≤ (1 : ℝ) := by
  have hpos : 0 ≤ Matrix.conjTranspose X * X := by
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self X)
  have hnorm_sq_le_norm_one :
      ‖Matrix.conjTranspose X * X‖ ≤ ‖(1 : CMatrix a)‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos hX
  have hnorm_one_le : ‖(1 : CMatrix a)‖ ≤ (1 : ℝ) :=
    cMatrix_l2OperatorNorm_one_le
  have hnorm_sq_le_one : ‖Matrix.conjTranspose X * X‖ ≤ (1 : ℝ) :=
    hnorm_sq_le_norm_one.trans hnorm_one_le
  have hnorm_eq :
      ‖Matrix.conjTranspose X * X‖ = ‖X‖ * ‖X‖ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (CStarRing.norm_star_mul_self (x := X))
  have hmul : ‖X‖ * ‖X‖ ≤ (1 : ℝ) := by
    rwa [hnorm_eq] at hnorm_sq_le_one
  have hsq : ‖X‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa [pow_two] using hmul
  exact (sq_le_sq₀ (norm_nonneg X) zero_le_one).1 hsq

/-- Converse unit-ball criterion for the finite-dimensional L2 operator norm:
`‖X‖∞ ≤ 1` implies `Xᴴ X ≤ I`.

This lets Beigi endpoint contractions proved as operator-norm estimates feed
the trace-norm variational API, which represents test contractions by the
matrix-order condition `XᴴX ≤ I`. -/
theorem cMatrix_conjTranspose_mul_self_le_one_of_l2OperatorNorm_le_one
    (X : CMatrix a) (hX : ‖X‖ ≤ (1 : ℝ)) :
    Matrix.conjTranspose X * X ≤ 1 := by
  have hpos : 0 ≤ Matrix.conjTranspose X * X := by
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self X)
  have hnorm_eq :
      ‖Matrix.conjTranspose X * X‖ = ‖X‖ * ‖X‖ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (CStarRing.norm_star_mul_self (x := X))
  have hnorm_le : ‖Matrix.conjTranspose X * X‖ ≤ (1 : ℝ) := by
    rw [hnorm_eq]
    have hmul : ‖X‖ * ‖X‖ ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul hX hX (norm_nonneg X) zero_le_one
    simpa using hmul
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg
    (Matrix.conjTranspose X * X) hpos).mp hnorm_le

/-- Turning a Schrödinger-picture Kraus family into a Heisenberg adjoint of the
conjugate-transpose family recovers the original Kraus map. -/
theorem krausAdjoint_conjTranspose_family_eq_ofKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (X : CMatrix a) :
    MatrixMap.krausAdjoint (fun k => Matrix.conjTranspose (K k)) X =
      MatrixMap.ofKraus K X := by
  unfold MatrixMap.krausAdjoint MatrixMap.ofKraus
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.conjTranspose_conjTranspose]

/-- Kadison-Schwarz inequality for a unital Kraus map in Schrödinger picture.

It is obtained by applying the existing Heisenberg-adjoint Kadison-Schwarz
lemma to the conjugate-transpose Kraus family. -/
theorem ofKraus_conjTranspose_mul_self_le_of_unital
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hUnital : MatrixMap.ofKraus K (1 : CMatrix a) = (1 : CMatrix b))
    (X : CMatrix a) :
    Matrix.conjTranspose (MatrixMap.ofKraus K X) * MatrixMap.ofKraus K X ≤
      MatrixMap.ofKraus K (Matrix.conjTranspose X * X) := by
  let L : κ → Matrix a b ℂ := fun k => Matrix.conjTranspose (K k)
  have hLone : MatrixMap.krausAdjoint L (1 : CMatrix a) = (1 : CMatrix b) := by
    simpa [L, krausAdjoint_conjTranspose_family_eq_ofKraus] using hUnital
  have hKS :=
    MatrixMap.krausAdjoint_conjTranspose_mul_self_le_of_krausAdjoint_one
      L hLone X
  simpa [L, krausAdjoint_conjTranspose_family_eq_ofKraus] using hKS

/-- Unit-ball operator-norm contraction for unital finite Kraus maps.

This is the source-specific `p = ∞` endpoint needed by the Beigi interpolation
route: a unital CP Kraus map sends contractions to contractions. -/
theorem opNorm_contract_ofKraus_of_unital_on_unitBall
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hUnital : MatrixMap.ofKraus K (1 : CMatrix a) = (1 : CMatrix b))
    {X : CMatrix a} (hX : Matrix.conjTranspose X * X ≤ 1) :
    ‖MatrixMap.ofKraus K X‖ ≤ (1 : ℝ) := by
  have hKS := ofKraus_conjTranspose_mul_self_le_of_unital K hUnital X
  have hsub_pos : (1 - Matrix.conjTranspose X * X).PosSemidef := by
    simpa [Matrix.le_iff] using hX
  have hmap_sub_pos :
      (MatrixMap.ofKraus K (1 - Matrix.conjTranspose X * X)).PosSemidef :=
    MatrixMap.ofKraus_mapsPositive K (1 - Matrix.conjTranspose X * X) hsub_pos
  have hmap_le_one :
      MatrixMap.ofKraus K (Matrix.conjTranspose X * X) ≤ (1 : CMatrix b) := by
    rw [Matrix.le_iff]
    simpa [map_sub, hUnital] using hmap_sub_pos
  have hY_le_one :
      Matrix.conjTranspose (MatrixMap.ofKraus K X) * MatrixMap.ofKraus K X ≤
        (1 : CMatrix b) :=
    hKS.trans hmap_le_one
  exact cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one
    (MatrixMap.ofKraus K X) hY_le_one

/-- Squared operator-norm bound from a matrix order bound.

This is the rescaling step that turns a contraction-on-the-unit-ball statement
into an ordinary operator-norm contraction. -/
theorem cMatrix_l2OperatorNorm_sq_le_of_conjTranspose_mul_self_le_smul_one
    (Y : CMatrix b) {r : ℝ} (hr : 0 ≤ r)
    (hY : Matrix.conjTranspose Y * Y ≤ ((r : ℂ) • (1 : CMatrix b))) :
    ‖Y‖ ^ 2 ≤ r := by
  have hpos : 0 ≤ Matrix.conjTranspose Y * Y := by
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self Y)
  have hnorm_le :
      ‖Matrix.conjTranspose Y * Y‖ ≤ ‖((r : ℂ) • (1 : CMatrix b))‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos hY
  have hone : ‖(1 : CMatrix b)‖ ≤ (1 : ℝ) :=
    cMatrix_l2OperatorNorm_one_le
  have hnorm_rhs : ‖((r : ℂ) • (1 : CMatrix b))‖ ≤ r := by
    calc
      ‖((r : ℂ) • (1 : CMatrix b))‖ =
          ‖(r : ℂ)‖ * ‖(1 : CMatrix b)‖ := by
            rw [norm_smul]
      _ = r * ‖(1 : CMatrix b)‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg hr]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hone hr
      _ = r := by ring
  have hnorm_star :
      ‖Matrix.conjTranspose Y * Y‖ = ‖Y‖ * ‖Y‖ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (CStarRing.norm_star_mul_self (x := Y))
  calc
    ‖Y‖ ^ 2 = ‖Matrix.conjTranspose Y * Y‖ := by
        rw [hnorm_star, pow_two]
    _ ≤ ‖((r : ℂ) • (1 : CMatrix b))‖ := hnorm_le
    _ ≤ r := hnorm_rhs

/-- Operator-norm contraction for unital finite Kraus maps.

This is the ordinary `p = ∞` endpoint needed by the Beigi interpolation route;
it upgrades the unit-ball version by applying Kadison-Schwarz to
`XᴴX ≤ ‖X‖² I`. -/
theorem opNorm_contract_ofKraus_of_unital
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hUnital : MatrixMap.ofKraus K (1 : CMatrix a) = (1 : CMatrix b))
    (X : CMatrix a) :
    ‖MatrixMap.ofKraus K X‖ ≤ ‖X‖ := by
  have hKS := ofKraus_conjTranspose_mul_self_le_of_unital K hUnital X
  have hXbound :
      Matrix.conjTranspose X * X ≤ (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) := by
    have hXboundReal :
        Matrix.conjTranspose X * X ≤ ((‖X‖ ^ 2 : ℝ) • (1 : CMatrix a)) := by
      simpa [Matrix.star_eq_conjTranspose, Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X))
    have hsmul :
        ((‖X‖ ^ 2 : ℝ) • (1 : CMatrix a)) =
          (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) := by
      ext i j
      simp [Matrix.smul_apply]
    simpa [hsmul] using hXboundReal
  have hdiff_pos :
      ((((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) -
        Matrix.conjTranspose X * X).PosSemidef := by
    simpa [Matrix.le_iff] using hXbound
  have hmap_diff_pos :
      (MatrixMap.ofKraus K
        ((((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) -
          Matrix.conjTranspose X * X)).PosSemidef :=
    MatrixMap.ofKraus_mapsPositive K _ hdiff_pos
  have hmap_bound :
      MatrixMap.ofKraus K (Matrix.conjTranspose X * X) ≤
        (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix b)) := by
    rw [Matrix.le_iff]
    simpa [map_sub, map_smul, hUnital] using hmap_diff_pos
  have hY_bound :
      Matrix.conjTranspose (MatrixMap.ofKraus K X) * MatrixMap.ofKraus K X ≤
        (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix b)) :=
    hKS.trans hmap_bound
  have hsq :
      ‖MatrixMap.ofKraus K X‖ ^ 2 ≤ ‖X‖ ^ 2 :=
    cMatrix_l2OperatorNorm_sq_le_of_conjTranspose_mul_self_le_smul_one
      (MatrixMap.ofKraus K X) (sq_nonneg ‖X‖) hY_bound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

end L2OperatorEndpoint

/-- Right multiplication by a finite-dimensional contraction does not increase
the trace norm.

This is a local helper for the Beigi endpoint estimates: the boundary complex
powers are used only through the contraction condition `KᴴK ≤ I`. -/
theorem traceNorm_mul_contraction_le
    (M K : CMatrix a) (hK : Matrix.conjTranspose K * K ≤ 1) :
    traceNorm (M * K) ≤ traceNorm M := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (M * K)
  rw [← hU]
  let KU : CMatrix a := K * (U : CMatrix a)
  have hKU : Matrix.conjTranspose KU * KU ≤ 1 := by
    have hdiff : (1 - Matrix.conjTranspose K * K).PosSemidef := by
      simpa [Matrix.le_iff] using hK
    have hconj :
        (star (U : CMatrix a) * (1 - Matrix.conjTranspose K * K) *
          (U : CMatrix a)).PosSemidef := by
      exact hdiff.conjTranspose_mul_mul_same (U : CMatrix a)
    have hUstarU :
        Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Unitary.coe_star_mul_self U : star (U : CMatrix a) * (U : CMatrix a) = 1)
    have heq :
        1 - Matrix.conjTranspose KU * KU =
          star (U : CMatrix a) * (1 - Matrix.conjTranspose K * K) *
            (U : CMatrix a) := by
      calc
        1 - Matrix.conjTranspose KU * KU =
            Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a) -
              Matrix.conjTranspose KU * KU := by rw [hUstarU]
        _ = star (U : CMatrix a) * (1 - Matrix.conjTranspose K * K) *
            (U : CMatrix a) := by
              simp [KU, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
              noncomm_ring
    rw [Matrix.le_iff]
    rwa [heq]
  have htrace : ((M * K) * (U : CMatrix a)).trace = (M * KU).trace := by
    simp [KU, Matrix.mul_assoc]
  rw [htrace]
  exact traceNorm_variational_contraction_abs_trace_le M KU hKU

/-- Left multiplication by a square isometry does not increase the trace norm.

This companion to `traceNorm_mul_contraction_le` is the exact form needed for
the Beigi boundary reference factors. -/
theorem traceNorm_isometry_mul_le
    (K M : CMatrix a) (hK : Matrix.conjTranspose K * K = 1) :
    traceNorm (K * M) ≤ traceNorm M := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (K * M)
  rw [← hU]
  let UK : CMatrix a := (U : CMatrix a) * K
  have hUK : Matrix.conjTranspose UK * UK ≤ 1 := by
    have hUstarU :
        Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Unitary.coe_star_mul_self U : star (U : CMatrix a) * (U : CMatrix a) = 1)
    have hUKeq : Matrix.conjTranspose UK * UK = 1 := by
      calc
        Matrix.conjTranspose UK * UK =
            Matrix.conjTranspose K *
              (Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a)) * K := by
              simp [UK, Matrix.mul_assoc]
        _ = Matrix.conjTranspose K * K := by rw [hUstarU]; simp
        _ = 1 := hK
    rw [hUKeq]
  have htrace : ((K * M) * (U : CMatrix a)).trace = (M * UK).trace := by
    calc
      ((K * M) * (U : CMatrix a)).trace =
          ((U : CMatrix a) * (K * M)).trace := by rw [Matrix.trace_mul_comm]
      _ = (((U : CMatrix a) * K) * M).trace := by simp [Matrix.mul_assoc]
      _ = (M * UK).trace := by
            rw [Matrix.trace_mul_comm]
  rw [htrace]
  exact traceNorm_variational_contraction_abs_trace_le M UK hUK

/-- The product of two finite-dimensional contractions is a contraction. -/
theorem cMatrix_contraction_mul
    (A B : CMatrix a)
    (hA : Matrix.conjTranspose A * A ≤ 1)
    (hB : Matrix.conjTranspose B * B ≤ 1) :
    Matrix.conjTranspose (A * B) * (A * B) ≤ 1 := by
  have hdiffA : (1 - Matrix.conjTranspose A * A).PosSemidef := by
    simpa [Matrix.le_iff] using hA
  have hconj :
      (Matrix.conjTranspose B * (1 - Matrix.conjTranspose A * A) * B).PosSemidef := by
    simpa [Matrix.star_eq_conjTranspose] using
      hdiffA.conjTranspose_mul_mul_same B
  have hle : Matrix.conjTranspose (A * B) * (A * B) ≤
      Matrix.conjTranspose B * B := by
    rw [Matrix.le_iff]
    convert hconj using 1
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    noncomm_ring
  exact hle.trans hB

/-- Two-sided multiplication by left isometry and right contraction does not
increase the trace norm. -/
theorem traceNorm_isometry_mul_contraction_mul_le
    (L M R : CMatrix a)
    (hL : Matrix.conjTranspose L * L = 1)
    (hR : Matrix.conjTranspose R * R ≤ 1) :
    traceNorm (L * M * R) ≤ traceNorm M := by
  exact (traceNorm_mul_contraction_le (L * M) R hR).trans
    (traceNorm_isometry_mul_le L M hL)

/-- Complex scalar multiplication is bounded by the scalar norm in trace norm. -/
theorem traceNorm_complex_smul_le (c : ℂ) (M : CMatrix a) :
    traceNorm (c • M) ≤ ‖c‖ * traceNorm M := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (c • M)
  rw [← hU]
  have htrace :
      (((c • M) * (U : CMatrix a)).trace) =
        c * ((M * (U : CMatrix a)).trace) := by
    simp [Matrix.trace_smul]
  have habs :
      Complex.abs (c * ((M * (U : CMatrix a)).trace)) =
        ‖c‖ * Complex.abs ((M * (U : CMatrix a)).trace) := by
    simp [Complex.abs]
  calc
    Complex.abs (((c • M) * (U : CMatrix a)).trace) =
        ‖c‖ * Complex.abs ((M * (U : CMatrix a)).trace) := by
          rw [htrace, habs]
    _ ≤ ‖c‖ * traceNorm M :=
        mul_le_mul_of_nonneg_left
          (traceNorm_variational_unitary_abs_trace_le M U) (norm_nonneg c)

/-- Trace pairing with a contraction is bounded by the trace norm of the other
factor. -/
theorem abs_trace_mul_le_of_traceNorm_le_of_contraction
    (Y W : CMatrix a) {C : ℝ}
    (hY : traceNorm Y ≤ C)
    (hW : Matrix.conjTranspose W * W ≤ 1) :
    Complex.abs ((W * Y).trace) ≤ C := by
  have hcycle : (W * Y).trace = (Y * W).trace := by
    rw [Matrix.trace_mul_comm]
  calc
    Complex.abs ((W * Y).trace) = Complex.abs ((Y * W).trace) := by rw [hcycle]
    _ ≤ traceNorm Y := traceNorm_variational_contraction_abs_trace_le Y W hW
    _ ≤ C := hY

/-- If `W / C` is a contraction and `Y` is in the trace-norm unit ball, then
the trace pairing of `W` with `Y` is bounded by `C`. -/
theorem abs_trace_mul_le_of_traceNorm_le_one_of_scaled_contraction
    (Y W : CMatrix a) {C : ℝ} (hCpos : 0 < C)
    (hY : traceNorm Y ≤ 1)
    (hW : Matrix.conjTranspose (((C : ℂ)⁻¹) • W) *
        (((C : ℂ)⁻¹) • W) ≤ 1) :
    Complex.abs ((W * Y).trace) ≤ C := by
  let W' : CMatrix a := ((C : ℂ)⁻¹) • W
  have hW_eq : W = (C : ℂ) • W' := by
    ext i j
    have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hCpos
    simp [W', Matrix.smul_apply, hCne]
  have hpair : Complex.abs ((W' * Y).trace) ≤ 1 :=
    abs_trace_mul_le_of_traceNorm_le_of_contraction Y W' hY (by simpa [W'] using hW)
  have htrace : (W * Y).trace = (C : ℂ) * (W' * Y).trace := by
    rw [hW_eq]
    simp [Matrix.trace_smul]
  have hnormC : ‖(C : ℂ)‖ = C := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hCpos)]
  calc
    Complex.abs ((W * Y).trace) =
        ‖(C : ℂ) * (W' * Y).trace‖ := by rw [htrace]
    _ = C * Complex.abs ((W' * Y).trace) := by
          rw [norm_mul, hnormC]
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpair (le_of_lt hCpos)
    _ = C := by ring

/-- The trace norm of a positive semidefinite matrix is its real trace. -/
theorem traceNorm_posSemidef_eq_trace_re
    {P : CMatrix a} (hP : P.PosSemidef) :
    traceNorm P = P.trace.re := by
  have hstar : Matrix.conjTranspose P = P := by
    simpa [Matrix.star_eq_conjTranspose] using hP.isHermitian.eq
  have hsqrt : psdSqrt (P * P) = P := by
    simpa [psdSqrt] using
      (CFC.sqrt_unique (a := P * P) (b := P) rfl hP.nonneg)
  rw [traceNorm, hstar, hsqrt]

/-- The trace norm of a positive real power is its PSD trace power. -/
theorem traceNorm_rpow_eq_psdTracePower
    {A : CMatrix a} (hA : A.PosSemidef) (p : ℝ) :
    traceNorm (CFC.rpow A p) = psdTracePower A hA p := by
  have hp : (CFC.rpow A p).PosSemidef :=
    cMatrix_rpow_posSemidef (A := A) (s := p) hA
  simpa [psdTracePower] using traceNorm_posSemidef_eq_trace_re hp

/-- The trace norm of a positive-definite complex power depends only on the
real part of the exponent. -/
theorem traceNorm_cMatrixPosDefComplexPower_eq_psdTracePower_re
    {A : CMatrix a} (hA : A.PosDef) (z : ℂ) :
    traceNorm (cMatrixPosDefComplexPower A hA z) =
      psdTracePower A hA.posSemidef z.re := by
  have hsqrt :
      psdSqrt (CFC.rpow A (2 * z.re)) = CFC.rpow A z.re := by
    have hsq :
        CFC.rpow A z.re * CFC.rpow A z.re = CFC.rpow A (2 * z.re) := by
      calc
        CFC.rpow A z.re * CFC.rpow A z.re =
            CFC.rpow A (z.re + z.re) := by
              exact (CFC.rpow_add (a := A) (x := z.re) (y := z.re) hA.isUnit).symm
        _ = CFC.rpow A (2 * z.re) := by ring_nf
    have hpos : (CFC.rpow A z.re).PosSemidef :=
      cMatrix_rpow_posSemidef (A := A) (s := z.re) hA.posSemidef
    simpa [psdSqrt] using
      (CFC.sqrt_unique (a := CFC.rpow A (2 * z.re))
        (b := CFC.rpow A z.re) hsq hpos.nonneg)
  have hgram :
      Matrix.conjTranspose (cMatrixPosDefComplexPower A hA z) *
          cMatrixPosDefComplexPower A hA z =
        CFC.rpow A (2 * z.re) := by
    simpa [Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self hA z
  rw [traceNorm, hgram, hsqrt]
  rfl

/-- Trace-norm contraction for trace-preserving Kraus maps.

This is the finite-dimensional `p = 1` endpoint used in Beigi's weighted
Schatten interpolation route. The proof is by trace-norm variational duality:
an output unitary witness is pulled back through the Heisenberg adjoint, and
Kadison-Schwarz for unital Kraus adjoints makes the pulled-back witness a
contraction. -/
theorem traceNorm_contract_ofKraus_of_tracePreserving
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (X : CMatrix a) :
    traceNorm ((MatrixMap.ofKraus K) X) ≤ traceNorm X := by
  classical
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_unitary_abs_trace ((MatrixMap.ofKraus K) X)
  rw [← hU]
  have hdual := MatrixMap.ofKraus_trace_duality K X (U : CMatrix b)
  rw [hdual]
  refine traceNorm_variational_contraction_abs_trace_le X
    (MatrixMap.krausAdjoint K (U : CMatrix b)) ?_
  have hUstarU :
      Matrix.conjTranspose (U : CMatrix b) * (U : CMatrix b) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self U : star (U : CMatrix b) * (U : CMatrix b) = 1)
  have hKS :=
    MatrixMap.krausAdjoint_conjTranspose_mul_self_le_of_tracePreserving
      K hTP (U : CMatrix b)
  have hone : MatrixMap.krausAdjoint K (1 : CMatrix b) = (1 : CMatrix a) :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  simpa [hUstarU, hone] using hKS

end MatrixMap

section ClassicalPower

variable {ι : Type*} [Fintype ι]

/-- Scalar Jensen inequality for nonnegative weighted averages, in the form
used by the classical endpoint of Renyi DPI. -/
theorem real_rpow_weighted_sum_le_sum_weighted_rpow
    {weight value : ι → ℝ} {α : ℝ} (hα : 1 ≤ α)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1)
    (hvalue_nonneg : ∀ i, 0 ≤ value i) :
    (∑ i, weight i * value i) ^ α ≤ ∑ i, weight i * value i ^ α := by
  classical
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), value i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact hvalue_nonneg i
  have hjensen :=
    (convexOn_rpow hα).map_sum_le
      (t := (Finset.univ : Finset ι)) (w := weight) (p := value)
      (by intro i _; exact hweight_nonneg i)
      (by simpa using hweight_sum)
      hmem
  simpa [smul_eq_mul] using hjensen

/-- Concave Jensen inequality for nonnegative weighted averages, used for the
`0 ≤ α ≤ 1` classical Renyi DPI endpoint. -/
theorem real_sum_weighted_rpow_le_rpow_weighted_sum
    {weight value : ι → ℝ} {α : ℝ} (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1)
    (hvalue_nonneg : ∀ i, 0 ≤ value i) :
    (∑ i, weight i * value i ^ α) ≤ (∑ i, weight i * value i) ^ α := by
  classical
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), value i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact hvalue_nonneg i
  have hjensen :=
    (Real.concaveOn_rpow hα_nonneg hα_le_one).le_map_sum
      (t := (Finset.univ : Finset ι)) (w := weight) (p := value)
      (by intro i _; exact hweight_nonneg i)
      (by simpa using hweight_sum)
      hmem
  simpa [smul_eq_mul] using hjensen

/-- Pointwise scalar log-sum inequality behind the `α ≥ 1` classical Renyi DPI.

For one output letter of a classical stochastic map, `t i` is the transition
weight from input `i`, and the inequality controls the output power term by the
corresponding weighted input power terms. -/
theorem real_classical_renyi_weighted_power_term_le
    {p q t : ι → ℝ} {α : ℝ} (hα : 1 ≤ α)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (ht_nonneg : ∀ i, 0 ≤ t i)
    (hQ_pos : 0 < ∑ i, q i * t i) :
    (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) ≤
      ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
  classical
  let P : ℝ := ∑ i, p i * t i
  let Q : ℝ := ∑ i, q i * t i
  let weight : ι → ℝ := fun i => q i * t i / Q
  let value : ι → ℝ := fun i => p i / q i
  have hQ_ne : Q ≠ 0 := ne_of_gt (by simpa [Q] using hQ_pos)
  have hQ_nonneg : 0 ≤ Q := le_of_lt (by simpa [Q] using hQ_pos)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp_nonneg i) (ht_nonneg i)
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    exact div_nonneg (mul_nonneg (le_of_lt (hq_pos i)) (ht_nonneg i)) hQ_nonneg
  have hweight_sum : ∑ i, weight i = 1 := by
    calc
      ∑ i, weight i = (∑ i, q i * t i) / Q := by
          simp [weight, Finset.sum_div]
      _ = Q / Q := by rfl
      _ = 1 := div_self hQ_ne
  have hvalue_nonneg : ∀ i, 0 ≤ value i := by
    intro i
    exact div_nonneg (hp_nonneg i) (le_of_lt (hq_pos i))
  have hweighted_eq : ∑ i, weight i * value i = P / Q := by
    calc
      ∑ i, weight i * value i =
          ∑ i, (p i * t i) / Q := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi_ne : q i ≠ 0 := ne_of_gt (hq_pos i)
            dsimp [weight, value]
            field_simp [hqi_ne, hQ_ne]
      _ = (∑ i, p i * t i) / Q := by
            rw [Finset.sum_div]
      _ = P / Q := by rfl
  have hjensen :
      (P / Q) ^ α ≤ ∑ i, weight i * value i ^ α := by
    rw [← hweighted_eq]
    exact real_rpow_weighted_sum_le_sum_weighted_rpow hα hweight_nonneg
      hweight_sum hvalue_nonneg
  have hright_eq :
      Q * (∑ i, weight i * value i ^ α) =
        ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
    calc
      Q * (∑ i, weight i * value i ^ α) =
          ∑ i, Q * (weight i * value i ^ α) := by
            rw [Finset.mul_sum]
      _ = ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi : 0 < q i := hq_pos i
            have hqi_ne : q i ≠ 0 := ne_of_gt hqi
            have hp_i_nonneg : 0 ≤ p i := hp_nonneg i
            have hq_i_nonneg : 0 ≤ q i := le_of_lt hqi
            calc
              Q * (weight i * value i ^ α) =
                  q i * t i * (p i / q i) ^ α := by
                    dsimp [weight, value]
                    field_simp [hQ_ne]
              _ = q i * t i * (p i ^ α / q i ^ α) := by
                    rw [Real.div_rpow hp_i_nonneg hq_i_nonneg]
              _ = t i * p i ^ α * (q i ^ (1 : ℝ) / q i ^ α) := by
                    rw [Real.rpow_one]
                    ring
              _ = t i * p i ^ α * q i ^ (1 - α) := by
                    rw [← Real.rpow_sub hqi 1 α]
  have hleft_eq :
      P ^ α * Q ^ (1 - α) = Q * (P / Q) ^ α := by
    have hP_div_nonneg : 0 ≤ P / Q := div_nonneg hP_nonneg hQ_nonneg
    calc
      P ^ α * Q ^ (1 - α) =
          (Q * (P / Q)) ^ α * Q ^ (1 - α) := by
            rw [mul_div_cancel₀ P hQ_ne]
      _ = (Q ^ α * (P / Q) ^ α) * Q ^ (1 - α) := by
            rw [Real.mul_rpow hQ_nonneg hP_div_nonneg]
      _ = (P / Q) ^ α * (Q ^ α * Q ^ (1 - α)) := by
            ring
      _ = (P / Q) ^ α * Q ^ (α + (1 - α)) := by
            rw [Real.rpow_add (by simpa [Q] using hQ_pos) α (1 - α)]
      _ = (P / Q) ^ α * Q := by
            have hexp : α + (1 - α) = 1 := by ring
            rw [hexp, Real.rpow_one]
      _ = Q * (P / Q) ^ α := by
            ring
  calc
    (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) =
        P ^ α * Q ^ (1 - α) := by rfl
    _ = Q * (P / Q) ^ α := hleft_eq
    _ ≤ Q * (∑ i, weight i * value i ^ α) :=
        mul_le_mul_of_nonneg_left hjensen hQ_nonneg
    _ = ∑ i, t i * p i ^ α * q i ^ (1 - α) := hright_eq

/-- Pointwise scalar log-sum inequality in the reverse direction for
`0 ≤ α ≤ 1`, the classical Renyi DPI range with negative logarithmic
prefactor. -/
theorem real_classical_renyi_weighted_power_term_ge
    {p q t : ι → ℝ} {α : ℝ} (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (ht_nonneg : ∀ i, 0 ≤ t i)
    (hQ_pos : 0 < ∑ i, q i * t i) :
    ∑ i, t i * p i ^ α * q i ^ (1 - α) ≤
      (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) := by
  classical
  let P : ℝ := ∑ i, p i * t i
  let Q : ℝ := ∑ i, q i * t i
  let weight : ι → ℝ := fun i => q i * t i / Q
  let value : ι → ℝ := fun i => p i / q i
  have hQ_ne : Q ≠ 0 := ne_of_gt (by simpa [Q] using hQ_pos)
  have hQ_nonneg : 0 ≤ Q := le_of_lt (by simpa [Q] using hQ_pos)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp_nonneg i) (ht_nonneg i)
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    exact div_nonneg (mul_nonneg (le_of_lt (hq_pos i)) (ht_nonneg i)) hQ_nonneg
  have hweight_sum : ∑ i, weight i = 1 := by
    calc
      ∑ i, weight i = (∑ i, q i * t i) / Q := by
          simp [weight, Finset.sum_div]
      _ = Q / Q := by rfl
      _ = 1 := div_self hQ_ne
  have hvalue_nonneg : ∀ i, 0 ≤ value i := by
    intro i
    exact div_nonneg (hp_nonneg i) (le_of_lt (hq_pos i))
  have hweighted_eq : ∑ i, weight i * value i = P / Q := by
    calc
      ∑ i, weight i * value i =
          ∑ i, (p i * t i) / Q := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi_ne : q i ≠ 0 := ne_of_gt (hq_pos i)
            dsimp [weight, value]
            field_simp [hqi_ne, hQ_ne]
      _ = (∑ i, p i * t i) / Q := by
            rw [Finset.sum_div]
      _ = P / Q := by rfl
  have hjensen :
      ∑ i, weight i * value i ^ α ≤ (P / Q) ^ α := by
    rw [← hweighted_eq]
    exact real_sum_weighted_rpow_le_rpow_weighted_sum hα_nonneg hα_le_one
      hweight_nonneg hweight_sum hvalue_nonneg
  have hright_eq :
      Q * (∑ i, weight i * value i ^ α) =
        ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
    calc
      Q * (∑ i, weight i * value i ^ α) =
          ∑ i, Q * (weight i * value i ^ α) := by
            rw [Finset.mul_sum]
      _ = ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi : 0 < q i := hq_pos i
            have hqi_ne : q i ≠ 0 := ne_of_gt hqi
            have hp_i_nonneg : 0 ≤ p i := hp_nonneg i
            have hq_i_nonneg : 0 ≤ q i := le_of_lt hqi
            calc
              Q * (weight i * value i ^ α) =
                  q i * t i * (p i / q i) ^ α := by
                    dsimp [weight, value]
                    field_simp [hQ_ne]
              _ = q i * t i * (p i ^ α / q i ^ α) := by
                    rw [Real.div_rpow hp_i_nonneg hq_i_nonneg]
              _ = t i * p i ^ α * (q i ^ (1 : ℝ) / q i ^ α) := by
                    rw [Real.rpow_one]
                    ring
              _ = t i * p i ^ α * q i ^ (1 - α) := by
                    rw [← Real.rpow_sub hqi 1 α]
  have hleft_eq :
      P ^ α * Q ^ (1 - α) = Q * (P / Q) ^ α := by
    have hP_div_nonneg : 0 ≤ P / Q := div_nonneg hP_nonneg hQ_nonneg
    calc
      P ^ α * Q ^ (1 - α) =
          (Q * (P / Q)) ^ α * Q ^ (1 - α) := by
            rw [mul_div_cancel₀ P hQ_ne]
      _ = (Q ^ α * (P / Q) ^ α) * Q ^ (1 - α) := by
            rw [Real.mul_rpow hQ_nonneg hP_div_nonneg]
      _ = (P / Q) ^ α * (Q ^ α * Q ^ (1 - α)) := by
            ring
      _ = (P / Q) ^ α * Q ^ (α + (1 - α)) := by
            rw [Real.rpow_add (by simpa [Q] using hQ_pos) α (1 - α)]
      _ = (P / Q) ^ α * Q := by
            have hexp : α + (1 - α) = 1 := by ring
            rw [hexp, Real.rpow_one]
      _ = Q * (P / Q) ^ α := by
            ring
  calc
    ∑ i, t i * p i ^ α * q i ^ (1 - α) =
        Q * (∑ i, weight i * value i ^ α) := hright_eq.symm
    _ ≤ Q * (P / Q) ^ α :=
        mul_le_mul_of_nonneg_left hjensen hQ_nonneg
    _ = P ^ α * Q ^ (1 - α) := hleft_eq.symm
    _ = (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) := by rfl

/-- Finite classical stochastic-map Renyi power-sum contraction for `α ≥ 1`.

This is the classical/commuting endpoint needed by the pinching route.  The
transition kernel is represented by nonnegative real weights `T i y` whose rows
sum to one. -/
theorem real_classical_renyi_stochastic_power_sum_le
    {ο : Type*} [Fintype ο]
    {p q : ι → ℝ} {T : ι → ο → ℝ} {α : ℝ}
    (hα : 1 ≤ α)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hQout_pos : ∀ y, 0 < ∑ i, q i * T i y) :
    (∑ y, (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α)) ≤
      ∑ i, p i ^ α * q i ^ (1 - α) := by
  classical
  have hpoint :
      ∀ y,
        (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α) ≤
          ∑ i, T i y * p i ^ α * q i ^ (1 - α) := by
    intro y
    exact real_classical_renyi_weighted_power_term_le
      (ι := ι) (p := p) (q := q) (t := fun i => T i y) hα
      hp_nonneg hq_pos (fun i => hT_nonneg i y) (hQout_pos y)
  calc
    (∑ y, (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α))
        ≤ ∑ y, ∑ i, T i y * p i ^ α * q i ^ (1 - α) :=
          Finset.sum_le_sum fun y _ => hpoint y
    _ = ∑ i, ∑ y, T i y * p i ^ α * q i ^ (1 - α) := by
          rw [Finset.sum_comm]
    _ = ∑ i, (∑ y, T i y) * p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Finset.sum_mul, mul_assoc]
    _ = ∑ i, p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hT_sum i]
          ring

/-- Finite classical stochastic-map Renyi power-sum expansion for
`0 ≤ α ≤ 1`. This is the classical endpoint for the lower-α DPI range, where
the logarithmic prefactor is nonpositive. -/
theorem real_classical_renyi_stochastic_power_sum_ge
    {ο : Type*} [Fintype ο]
    {p q : ι → ℝ} {T : ι → ο → ℝ} {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hQout_pos : ∀ y, 0 < ∑ i, q i * T i y) :
    (∑ i, p i ^ α * q i ^ (1 - α)) ≤
      ∑ y, (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α) := by
  classical
  have hpoint :
      ∀ y,
        ∑ i, T i y * p i ^ α * q i ^ (1 - α) ≤
          (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α) := by
    intro y
    exact real_classical_renyi_weighted_power_term_ge
      (ι := ι) (p := p) (q := q) (t := fun i => T i y)
      hα_nonneg hα_le_one hp_nonneg hq_pos
      (fun i => hT_nonneg i y) (hQout_pos y)
  calc
    (∑ i, p i ^ α * q i ^ (1 - α)) =
        ∑ i, (∑ y, T i y) * p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hT_sum i]
          ring
    _ = ∑ i, ∑ y, T i y * p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Finset.sum_mul, mul_assoc]
    _ = ∑ y, ∑ i, T i y * p i ^ α * q i ^ (1 - α) := by
          rw [Finset.sum_comm]
    _ ≤ ∑ y, (∑ i, p i * T i y) ^ α *
          (∑ i, q i * T i y) ^ (1 - α) :=
          Finset.sum_le_sum fun y _ => hpoint y

/-- The finite classical Renyi power sum is strictly positive for full-support
probability vectors. -/
theorem nnreal_classical_renyi_power_sum_pos
    (p q : ι → ℝ≥0) (hp_sum : ∑ i, p i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (α : ℝ) :
    0 < ∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)) := by
  classical
  have hnonempty : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    have hzero : (∑ i, p i) = 0 := by simp
    rw [hzero] at hp_sum
    exact zero_ne_one hp_sum
  exact Finset.sum_pos' (fun i _ =>
      le_of_lt <| mul_pos (Real.rpow_pos_of_pos (hp_pos i) α)
        (Real.rpow_pos_of_pos (hq_pos i) (1 - α)))
    ⟨Classical.choice hnonempty, Finset.mem_univ _,
      mul_pos
        (Real.rpow_pos_of_pos (hp_pos (Classical.choice hnonempty)) α)
        (Real.rpow_pos_of_pos (hq_pos (Classical.choice hnonempty)) (1 - α))⟩

end ClassicalPower

namespace Classical

/-- Push-forward of a finite classical distribution through a row-stochastic
kernel. -/
def stochasticOutput (p : a → ℝ≥0) (T : a → b → ℝ≥0) : b → ℝ≥0 :=
  fun y => ∑ i, p i * T i y

omit [DecidableEq a] [DecidableEq b] in
/-- The push-forward through a row-stochastic kernel is normalized. -/
theorem stochasticOutput_sum
    (p : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hT_sum : ∀ i, ∑ y, T i y = 1) :
    ∑ y, stochasticOutput p T y = 1 := by
  classical
  calc
    ∑ y, stochasticOutput p T y = ∑ y, ∑ i, p i * T i y := by rfl
    _ = ∑ i, ∑ y, p i * T i y := by rw [Finset.sum_comm]
    _ = ∑ i, p i * ∑ y, T i y := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ i, p i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hT_sum i, mul_one]
    _ = 1 := hp_sum

/-- A row-stochastic classical kernel as a CPTP channel between diagonal
classical registers. -/
def stochasticChannel (T : a → b → ℝ≥0) (hT_sum : ∀ i, ∑ y, T i y = 1) :
    Channel a b :=
  Channel.prepare fun i => diagonalState (T i) (hT_sum i)

/-- The stochastic channel sends a diagonal state to the diagonal push-forward
distribution. -/
theorem stochasticChannel_applyState_diagonalState
    (p : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hT_sum : ∀ i, ∑ y, T i y = 1) :
    (stochasticChannel T hT_sum).applyState (diagonalState p hp_sum) =
      diagonalState (stochasticOutput p T) (stochasticOutput_sum p T hp_sum hT_sum) := by
  classical
  apply State.ext
  ext y y'
  by_cases hyy : y = y'
  · subst y'
    simp only [stochasticChannel, Channel.applyState, Channel.prepare, Channel.prepareMap,
      LinearMap.coe_mk, AddHom.coe_mk, diagonalState_matrix, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.diagonal_apply_eq, stochasticOutput]
    change (∑ x, ((p x : ℂ) * (T x y : ℂ))) =
      (((∑ x, p x * T x y) : ℝ≥0) : ℂ)
    simp
  · simp [stochasticChannel, Channel.applyState, Channel.prepare, Channel.prepareMap,
      diagonalState_matrix, Matrix.sum_apply, Matrix.diagonal, hyy]

end Classical

namespace State

/-- The single-outcome POVM with effect `1`, used as the terminal/discard
measurement channel in finite dimension. -/
def terminalPOVM (a : Type u) [Fintype a] [DecidableEq a] : POVM PUnit.{1} a where
  effects _ := 1
  pos _ := Matrix.PosSemidef.one
  sum_eq_one := by
    ext i j
    simp

/-- The terminal measurement channel associated with `terminalPOVM`. -/
def terminalMeasureChannel (a : Type u) [Fintype a] [DecidableEq a] : Channel a PUnit.{1} :=
  Channel.measure (terminalPOVM a)

/-- Measuring with the terminal one-outcome POVM maps every normalized state to
the unique unit-system state. -/
theorem terminalMeasureChannel_applyState (ρ : State a) :
    (terminalMeasureChannel a).applyState ρ = State.unit := by
  apply State.ext
  ext i j
  cases i
  cases j
  simp [terminalMeasureChannel, terminalPOVM, Channel.applyState, Channel.measure,
    Channel.measureMap, State.unit, ρ.trace_eq_one]

/-- Stinespring lift of a state through a trace-preserving Kraus family.

For a Kraus realization `K : a → b` and its trace-preserving proof, this is the
state on `B × κ` obtained by applying the Stinespring isometry and retaining
the environment register. The lifted state is generally not full-rank when the
environment is nontrivial; this is why the strict low-`α` route still needs a
regularized/support-aware partial-trace theorem rather than the current
`State + PosDef` API alone. -/
def stinespringLiftState {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) : State (Prod b κ) where
  matrix :=
    (MatrixMap.krausStinespringIsometry K hTP).matrix * ρ.matrix *
      Matrix.conjTranspose (MatrixMap.krausStinespringIsometry K hTP).matrix
  pos := by
    exact ρ.pos.mul_mul_conjTranspose_same
      (MatrixMap.krausStinespringIsometry K hTP).matrix
  trace_eq_one := by
    have hpt :=
      MatrixMap.partialTraceB_krausStinespringIsometry K hTP ρ.matrix
    have htrace := congrArg Matrix.trace hpt
    rw [partialTraceB_trace] at htrace
    rw [htrace, hTP ρ.matrix, ρ.trace_eq_one]

/-- The output marginal of the Stinespring lift is the Kraus-map output. -/
theorem stinespringLiftState_marginalA_matrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    ((stinespringLiftState K hTP ρ).marginalA).matrix =
      MatrixMap.ofKraus K ρ.matrix := by
  simpa [stinespringLiftState, State.marginalA] using
    MatrixMap.partialTraceB_krausStinespringIsometry K hTP ρ.matrix

/-- The output marginal of the Stinespring lift is the corresponding channel
output whenever the channel is represented by the same Kraus family. -/
theorem stinespringLiftState_marginalA_eq_applyState {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (Φ : Channel a b)
    (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    (stinespringLiftState K hTP ρ).marginalA = Φ.applyState ρ := by
  apply State.ext
  rw [stinespringLiftState_marginalA_matrix K hTP ρ]
  simp [Channel.applyState, hK]

private theorem log2_mono_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Full-support classical stochastic maps satisfy sandwiched Renyi DPI for
diagonal states in the `α > 1` range.

This is a non-circular commuting endpoint for the pinching proof route: the
proof reduces both diagonal sandwiched Renyi divergences to classical power sums
and applies the scalar log-sum/Jensen inequality for a stochastic kernel. -/
theorem sandwichedRenyi_diagonalState_stochastic_le_of_one_lt
    (p q : a → ℝ≥0) (pOut qOut : b → ℝ≥0) (T : a → b → ℝ)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_sum : ∑ y, pOut y = 1) (hqOut_sum : ∑ y, qOut y = 1)
    (hpOut_pos : ∀ y, 0 < (pOut y : ℝ)) (hqOut_pos : ∀ y, 0 < (qOut y : ℝ))
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hpOut_eq : ∀ y, (pOut y : ℝ) = ∑ i, (p i : ℝ) * T i y)
    (hqOut_eq : ∀ y, (qOut y : ℝ) = ∑ i, (q i : ℝ) * T i y)
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi (Classical.diagonalState pOut hpOut_sum)
        (Classical.diagonalState qOut hqOut_sum)
        (Classical.diagonalState_posDef pOut hpOut_sum hpOut_pos)
        (Classical.diagonalState_posDef qOut hqOut_sum hqOut_pos)
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) := by
  classical
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hα_ne_one : α ≠ 1 := ne_of_gt hα_gt_one
  have hpower_raw :
      (∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
          (∑ i, (q i : ℝ) * T i y) ^ (1 - α)) ≤
        ∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α) :=
    real_classical_renyi_stochastic_power_sum_le
      (ι := a) (ο := b) (p := fun i => (p i : ℝ))
      (q := fun i => (q i : ℝ)) (T := T) (α := α)
      (le_of_lt hα_gt_one)
      (fun i => NNReal.coe_nonneg (p i)) hq_pos hT_nonneg hT_sum
      (fun y => by
        rw [← hqOut_eq y]
        exact hqOut_pos y)
  have hpower :
      (∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α)) ≤
        ∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α) := by
    calc
      (∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α)) =
          ∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
            (∑ i, (q i : ℝ) * T i y) ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [hpOut_eq y, hqOut_eq y]
      _ ≤ ∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α) := hpower_raw
  have hout_pos :
      0 < ∑ y, ((pOut y : ℝ) ^ α) * ((qOut y : ℝ) ^ (1 - α)) :=
    nnreal_classical_renyi_power_sum_pos pOut qOut hpOut_sum
      hpOut_pos hqOut_pos α
  have hlog := log2_mono_of_pos hout_pos hpower
  have hcoef_nonneg : 0 ≤ 1 / (α - 1) := by
    exact le_of_lt (one_div_pos.2 (sub_pos.mpr hα_gt_one))
  rw [sandwichedRenyi_diagonalState_eq_classicalPowerSum pOut qOut
      hpOut_sum hqOut_sum hpOut_pos hqOut_pos α hα_pos hα_ne_one,
    sandwichedRenyi_diagonalState_eq_classicalPowerSum p q
      hp_sum hq_sum hp_pos hq_pos α hα_pos hα_ne_one]
  exact mul_le_mul_of_nonneg_left hlog hcoef_nonneg

/-- Full-support classical stochastic maps satisfy sandwiched Renyi DPI for
diagonal states in the `0 < α < 1` range.

The classical power sum moves in the reverse direction in this range; the
negative logarithmic prefactor reverses it back to the DPI inequality. -/
theorem sandwichedRenyi_diagonalState_stochastic_le_of_lt_one
    (p q : a → ℝ≥0) (pOut qOut : b → ℝ≥0) (T : a → b → ℝ)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_sum : ∑ y, pOut y = 1) (hqOut_sum : ∑ y, qOut y = 1)
    (hpOut_pos : ∀ y, 0 < (pOut y : ℝ)) (hqOut_pos : ∀ y, 0 < (qOut y : ℝ))
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hpOut_eq : ∀ y, (pOut y : ℝ) = ∑ i, (p i : ℝ) * T i y)
    (hqOut_eq : ∀ y, (qOut y : ℝ) = ∑ i, (q i : ℝ) * T i y)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyi (Classical.diagonalState pOut hpOut_sum)
        (Classical.diagonalState qOut hqOut_sum)
        (Classical.diagonalState_posDef pOut hpOut_sum hpOut_pos)
        (Classical.diagonalState_posDef qOut hqOut_sum hqOut_pos)
        α hα_pos (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α hα_pos (ne_of_lt hα_lt_one) := by
  classical
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hpower_raw :
      (∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α)) ≤
        ∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
          (∑ i, (q i : ℝ) * T i y) ^ (1 - α) :=
    real_classical_renyi_stochastic_power_sum_ge
      (ι := a) (ο := b) (p := fun i => (p i : ℝ))
      (q := fun i => (q i : ℝ)) (T := T) (α := α)
      (le_of_lt hα_pos) (le_of_lt hα_lt_one)
      (fun i => NNReal.coe_nonneg (p i)) hq_pos hT_nonneg hT_sum
      (fun y => by
        rw [← hqOut_eq y]
        exact hqOut_pos y)
  have hpower :
      (∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α)) ≤
        ∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α) := by
    calc
      (∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α))
          ≤ ∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
              (∑ i, (q i : ℝ) * T i y) ^ (1 - α) := hpower_raw
      _ = ∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [hpOut_eq y, hqOut_eq y]
  have hin_pos :
      0 < ∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)) :=
    nnreal_classical_renyi_power_sum_pos p q hp_sum hp_pos hq_pos α
  have hlog := log2_mono_of_pos hin_pos hpower
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  rw [sandwichedRenyi_diagonalState_eq_classicalPowerSum pOut qOut
      hpOut_sum hqOut_sum hpOut_pos hqOut_pos α hα_pos hα_ne_one,
    sandwichedRenyi_diagonalState_eq_classicalPowerSum p q
      hp_sum hq_sum hp_pos hq_pos α hα_pos hα_ne_one]
  exact mul_le_mul_of_nonpos_left hlog hcoef_nonpos

/-- Output-side Holder dual effect for the sandwiched Renyi variational route:
`σ^((1-α)/(2α)) B σ^((1-α)/(2α))`. -/
def sandwichedRenyiHolderDualEffect (σ : State a) (B : CMatrix a) (α : ℝ) :
    CMatrix a :=
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ.matrix s
  C * B * C

/-- The Holder dual effect remains positive semidefinite when the unit-ball
witness is positive semidefinite. -/
theorem sandwichedRenyiHolderDualEffect_posSemidef
    (σ : State a) {B : CMatrix a} (hB : B.PosSemidef) (α : ℝ) :
    (sandwichedRenyiHolderDualEffect σ B α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.matrix s
  have hC : C.PosSemidef := by
    simpa [C] using σ.rpowMatrix_posSemidef s
  have hCstar : star C = C := hC.isHermitian.eq
  have hdual : (star C * B * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hB C
  rw [hCstar] at hdual
  simpa [sandwichedRenyiHolderDualEffect, s, C] using hdual

/-- The core trace-duality identity for the `α > 1` Holder route.

For a Kraus representation of the channel, pairing the output sandwiched inner
operator with a Holder unit-ball witness is exactly the input state paired with
the Kraus-adjoint pullback of the corresponding Holder dual effect. This is the
first nontrivial channel-specific step before proving the remaining q-unit-ball
contraction. -/
theorem sandwichedRenyi_inner_trace_eq_krausAdjoint_holderDualEffect
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (B : CMatrix b) (α : ℝ) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re =
      (ρ.matrix *
        MatrixMap.krausAdjoint K
          (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace.re := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix b := CFC.rpow (Φ.applyState σ).matrix s
  let X : CMatrix b := (Φ.applyState ρ).matrix
  have hcycle :
      ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace) =
        (X * sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace := by
    change (((C * X * C) * B).trace) = (X * (C * B * C)).trace
    calc
      ((C * X * C) * B).trace = ((C * X) * (C * B)).trace := by
        congr 1
        noncomm_ring
      _ = (((C * B) * C) * X).trace := by
        exact Matrix.trace_mul_cycle C X (C * B)
      _ = (X * (C * B * C)).trace := by
        rw [Matrix.trace_mul_comm]
  have hdual :
      (X * sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace =
        (ρ.matrix *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace := by
    change ((Φ.map ρ.matrix) *
        sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace =
      (ρ.matrix *
        MatrixMap.krausAdjoint K
          (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace
    rw [hK]
    exact MatrixMap.ofKraus_trace_duality K ρ.matrix
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
  exact congrArg Complex.re (hcycle.trans hdual)

/-- The Kraus-adjoint pullback of the output Holder dual effect is positive
semidefinite. This is the positivity half of the witness transport used by the
Holder/variational proof route. -/
theorem sandwichedRenyi_krausAdjoint_holderDualEffect_posSemidef
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    (α : ℝ) :
    (MatrixMap.krausAdjoint K
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).PosSemidef := by
  exact MatrixMap.krausAdjoint_mapsPositive K
    (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
    (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α)

/-- Kadison's inequality for the pulled-back output Holder dual effect.

This is the channel-specific square inequality needed before attempting the
weighted `q`-unit-ball estimate in the α > 1 variational route. -/
theorem sandwichedRenyi_krausAdjoint_holderDualEffect_square_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (σ : State a) (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    (α : ℝ) :
    MatrixMap.krausAdjoint K (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
        MatrixMap.krausAdjoint K (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) ≤
      MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α *
          sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) := by
  exact MatrixMap.krausAdjoint_posSemidef_mul_self_le_of_tracePreserving K hTP
    (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α)

private theorem state_matrix_le_one_local (τ : State a) :
    τ.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := τ.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((τ.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : τ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using τ.pos.1.spectral_theorem
  have heig_sum : ∑ i, τ.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((τ.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact τ.pos.1.trace_eq_sum_eigenvalues.symm.trans τ.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, τ.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ τ.pos.1.eigenvalues j :=
      τ.pos.eigenvalues_nonneg j
    calc
      τ.pos.1.eigenvalues i
          ≤ τ.pos.1.eigenvalues i +
              ∑ j ∈ Finset.univ.erase i, τ.pos.1.eigenvalues j :=
            le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hnonneg j)
      _ = ∑ j, τ.pos.1.eigenvalues j := by
            rw [add_comm]
            exact Finset.sum_erase_add (s := Finset.univ)
              (f := fun j => τ.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - τ.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
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
        Matrix.diagonal fun i => (((1 : ℝ) - τ.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - τ.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

private theorem state_trace_mul_le_trace_of_posSemidef
    (τ : State a) {X : CMatrix a} (hX : X.PosSemidef) :
    ((τ.matrix * X).trace).re ≤ X.trace.re := by
  have htrace :=
    cMatrix_trace_mul_le_of_le_posSemidef_left
      (W := X) (A := τ.matrix) (B := 1) hX
      (state_matrix_le_one_local τ)
  rw [Matrix.trace_mul_comm X τ.matrix, Matrix.mul_one] at htrace
  exact htrace

private theorem cMatrix_trace_sandwich_sq_le_weighted_sq
    {S A : CMatrix a} (hS : S.PosSemidef) (hA : A.IsHermitian) :
    ((A * S * A * S).trace).re ≤ ((S * S * (A * A)).trace).re := by
  classical
  letI : NormedAddCommGroup (CMatrix a) :=
    Matrix.toMatrixNormedAddCommGroup (1 : CMatrix a) Matrix.PosDef.one
  letI : InnerProductSpace ℂ (CMatrix a) :=
    Matrix.toMatrixInnerProductSpace (1 : CMatrix a) Matrix.PosSemidef.one
  let x : CMatrix a := A * S
  let y : CMatrix a := S * A
  let R : ℝ := ((S * S * (A * A)).trace).re
  have hinner : inner ℂ x y = (A * S * A * S).trace := by
    dsimp [x, y]
    change ((S * A) * (1 : CMatrix a) * Matrix.conjTranspose (A * S)).trace =
      (A * S * A * S).trace
    rw [Matrix.conjTranspose_mul, hS.isHermitian.eq, hA.eq]
    calc
      ((S * A) * (1 : CMatrix a) * (S * A)).trace =
          (S * A * S * A).trace := by
            simp [Matrix.mul_assoc]
      _ = (A * S * A * S).trace := by
            calc
              (S * A * S * A).trace = ((S * A * S) * A).trace := by
                rw [Matrix.mul_assoc]
              _ = (A * (S * A * S)).trace := by
                rw [Matrix.trace_mul_comm]
              _ = (A * S * A * S).trace := by
                noncomm_ring
  have hxnorm : ‖x‖ ^ 2 = R := by
    rw [@norm_sq_eq_re_inner ℂ (CMatrix a) _ _ _ x]
    dsimp [x, R]
    change (((A * S) * (1 : CMatrix a) * Matrix.conjTranspose (A * S)).trace).re =
      ((S * S * (A * A)).trace).re
    rw [Matrix.conjTranspose_mul, hS.isHermitian.eq, hA.eq]
    congr 1
    calc
      ((A * S) * (1 : CMatrix a) * (S * A)).trace =
          (A * (S * S) * A).trace := by
            noncomm_ring
      _ = (A * A * (S * S)).trace := by
            exact Matrix.trace_mul_cycle A (S * S) A
      _ = ((S * S) * (A * A)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (S * S * (A * A)).trace := by
            rw [Matrix.mul_assoc]
  have hynorm : ‖y‖ ^ 2 = R := by
    rw [@norm_sq_eq_re_inner ℂ (CMatrix a) _ _ _ y]
    dsimp [y, R]
    change (((S * A) * (1 : CMatrix a) * Matrix.conjTranspose (S * A)).trace).re =
      ((S * S * (A * A)).trace).re
    rw [Matrix.conjTranspose_mul, hA.eq, hS.isHermitian.eq]
    congr 1
    calc
      ((S * A) * (1 : CMatrix a) * (A * S)).trace =
          (S * (A * A) * S).trace := by
            noncomm_ring
      _ = (S * S * (A * A)).trace := by
            exact Matrix.trace_mul_cycle S (A * A) S
  have hcs := norm_inner_le_norm (𝕜 := ℂ) x y
  have hprod_le : ‖x‖ * ‖y‖ ≤ R := by
    have hdiff : 0 ≤ (‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
    nlinarith [hxnorm, hynorm, hdiff]
  calc
    ((A * S * A * S).trace).re = (inner ℂ x y).re := by rw [hinner]
    _ ≤ ‖inner ℂ x y‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖y‖ := hcs
    _ ≤ R := hprod_le

private theorem cMatrix_quarter_sandwich_tracePower_two_le
    (σ : State a) (hσ : σ.matrix.PosDef) {A : CMatrix a} (hA : A.PosSemidef) :
    psdTracePower
        (CFC.rpow σ.matrix (1 / 4 : ℝ) * A * CFC.rpow σ.matrix (1 / 4 : ℝ))
        (by
          let C : CMatrix a := CFC.rpow σ.matrix (1 / 4 : ℝ)
          have hC : C.PosSemidef := by
            simpa [C] using σ.rpowMatrix_posSemidef (1 / 4 : ℝ)
          have hCstar : star C = C := hC.isHermitian.eq
          have hW : (star C * A * C).PosSemidef :=
            Matrix.PosSemidef.conjTranspose_mul_mul_same hA C
          rw [hCstar] at hW
          simpa [C] using hW)
        (2 : ℝ) ≤
      ((σ.matrix * (A * A)).trace).re := by
  let C : CMatrix a := CFC.rpow σ.matrix (1 / 4 : ℝ)
  let S : CMatrix a := CFC.rpow σ.matrix (1 / 2 : ℝ)
  let W : CMatrix a := C * A * C
  have hC : C.PosSemidef := by
    simpa [C] using σ.rpowMatrix_posSemidef (1 / 4 : ℝ)
  have hS : S.PosSemidef := by
    simpa [S] using σ.rpowMatrix_posSemidef (1 / 2 : ℝ)
  have hCstar : star C = C := hC.isHermitian.eq
  have hW : W.PosSemidef := by
    have hW' : (star C * A * C).PosSemidef :=
      Matrix.PosSemidef.conjTranspose_mul_mul_same hA C
    rw [hCstar] at hW'
    simpa [W] using hW'
  have hCC : C * C = S := by
    calc
      C * C =
          CFC.rpow σ.matrix (1 / 4 : ℝ) *
            CFC.rpow σ.matrix (1 / 4 : ℝ) := by rfl
      _ = CFC.rpow σ.matrix ((1 / 4 : ℝ) + (1 / 4 : ℝ)) := by
            exact (CFC.rpow_add (a := σ.matrix) (x := (1 / 4 : ℝ))
              (y := (1 / 4 : ℝ)) hσ.isUnit).symm
      _ = S := by
            norm_num [S]
  have hSS : S * S = σ.matrix := by
    calc
      S * S =
          CFC.rpow σ.matrix (1 / 2 : ℝ) *
            CFC.rpow σ.matrix (1 / 2 : ℝ) := by rfl
      _ = CFC.rpow σ.matrix ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
            exact (CFC.rpow_add (a := σ.matrix) (x := (1 / 2 : ℝ))
              (y := (1 / 2 : ℝ)) hσ.isUnit).symm
      _ = σ.matrix := by
            norm_num
            exact CFC.rpow_one σ.matrix
              (ha := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef)
  have htraceW :
      (W * W).trace.re = (A * S * A * S).trace.re := by
    congr 1
    dsimp [W]
    calc
      ((C * A * C) * (C * A * C)).trace =
          (C * A * C * C * A * C).trace := by
            noncomm_ring
      _ = (A * C * C * A * C * C).trace := by
            calc
              (C * A * C * C * A * C).trace =
                  (C * A * (C * C * A * C)).trace := by
                    noncomm_ring
              _ = ((A * C * C * A * C) * C).trace := by
                    calc
                      (C * A * (C * C * A * C)).trace =
                          (C * (A * (C * C * A * C))).trace := by
                            rw [Matrix.mul_assoc]
                      _ = ((A * (C * C * A * C)) * C).trace := by
                            rw [Matrix.trace_mul_comm]
                      _ = ((A * C * C * A * C) * C).trace := by
                            noncomm_ring
              _ = (A * C * C * A * C * C).trace := by
                    noncomm_ring
      _ = (A * S * A * S).trace := by
            calc
              (A * C * C * A * C * C).trace =
                  (A * (C * C) * A * (C * C)).trace := by
                    noncomm_ring
              _ = (A * S * A * S).trace := by
                    rw [hCC]
  have hbridge :
      ((A * S * A * S).trace).re ≤ ((S * S * (A * A)).trace).re :=
    cMatrix_trace_sandwich_sq_le_weighted_sq hS hA.isHermitian
  calc
    psdTracePower
        (CFC.rpow σ.matrix (1 / 4 : ℝ) * A * CFC.rpow σ.matrix (1 / 4 : ℝ))
        (by
          let C : CMatrix a := CFC.rpow σ.matrix (1 / 4 : ℝ)
          have hC : C.PosSemidef := by
            simpa [C] using σ.rpowMatrix_posSemidef (1 / 4 : ℝ)
          have hCstar : star C = C := hC.isHermitian.eq
          have hW : (star C * A * C).PosSemidef :=
            Matrix.PosSemidef.conjTranspose_mul_mul_same hA C
          rw [hCstar] at hW
          simpa [C] using hW)
        (2 : ℝ) =
        (W * W).trace.re := by
          rw [psdTracePower_two]
    _ = (A * S * A * S).trace.re := htraceW
    _ ≤ ((S * S * (A * A)).trace).re := hbridge
    _ = ((σ.matrix * (A * A)).trace).re := by
          rw [hSS]

/-- Weighted trace form of Kadison's inequality for a trace-preserving Kraus
channel.

For a PSD input weight `D`, the square of the pulled-back observable is bounded
after trace pairing by the output-side square. This is the `L₂` core bridge of
the α > 1 variational route. -/
theorem sandwichedRenyi_krausAdjoint_weighted_square_trace_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {D : CMatrix a} (hD : D.PosSemidef)
    {E : CMatrix b} (hE : E.IsHermitian) :
    ((D * (MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E)).trace).re ≤
      (((MatrixMap.ofKraus K) D * (E * E)).trace).re := by
  have hkadison :
      MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E ≤
        MatrixMap.krausAdjoint K (E * E) :=
    MatrixMap.krausAdjoint_mul_self_le_of_tracePreserving K hTP hE
  have htrace :=
    cMatrix_trace_mul_le_of_le_posSemidef_left (W := D)
      (A := MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E)
      (B := MatrixMap.krausAdjoint K (E * E)) hD hkadison
  have hdual := MatrixMap.ofKraus_trace_duality K D (E * E)
  rw [← hdual] at htrace
  exact htrace

/-- Weighted trace bridge specialized to the Holder dual effect generated by an
output PSD witness. -/
theorem sandwichedRenyi_holderDualEffect_weighted_square_trace_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ((σ.matrix *
        (MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α))).trace).re ≤
      (((Φ.applyState σ).matrix *
          (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α *
            sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace).re := by
  have hbase :=
    sandwichedRenyi_krausAdjoint_weighted_square_trace_le
      (K := K) hTP (D := σ.matrix) σ.pos
      (E := sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
      (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α).isHermitian
  have hmap : (MatrixMap.ofKraus K) σ.matrix = (Φ.applyState σ).matrix := by
    rw [← hK]
    rfl
  simpa [hmap] using hbase

/-- The Holder dual effect weighted square bound with the output state weight
removed using `Φσ ≤ I`. This isolates the remaining hard step: comparing the
unweighted square trace of the sandwiched dual effect to the original output
unit-ball witness. -/
theorem sandwichedRenyi_holderDualEffect_square_trace_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ((σ.matrix *
        (MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α))).trace).re ≤
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α *
        sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace.re := by
  let E : CMatrix b := sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α
  have hweighted :
      ((σ.matrix *
          (MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E)).trace).re ≤
        (((Φ.applyState σ).matrix * (E * E)).trace).re := by
    simpa [E] using
      sandwichedRenyi_holderDualEffect_weighted_square_trace_le
        K σ Φ hK hTP hB α
  have hE : E.PosSemidef := by
    simpa [E] using sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α
  have hEsq : (E * E).PosSemidef := by
    simpa [hE.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self E
  have hunweighted :
      (((Φ.applyState σ).matrix * (E * E)).trace).re ≤ (E * E).trace.re :=
    state_trace_mul_le_trace_of_posSemidef (Φ.applyState σ) hEsq
  exact hweighted.trans (by simpa [E] using hunweighted)

/-- `psdTracePower` form of `sandwichedRenyi_holderDualEffect_square_trace_le`
for the Hilbert-Schmidt/α = 2 specialization of the variational route. -/
theorem sandwichedRenyi_holderDualEffect_tracePower_two_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ((σ.matrix *
        (MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α))).trace).re ≤
      psdTracePower (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
        (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α) (2 : ℝ) := by
  have hsq :=
    sandwichedRenyi_holderDualEffect_square_trace_le
      K σ Φ hK hTP hB α
  rw [psdTracePower_two]
  exact hsq

/-- Input-side Holder witness obtained by pulling an output witness back through
the Kraus adjoint and conjugating by the inverse sandwiched reference factor.

The q-unit-ball estimate for this witness is the remaining noncommutative
operator inequality in the α > 1 Holder route. -/
def sandwichedRenyiKrausAdjointInputWitness
    (σ : State a) (Φ : Channel a b) {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (B : CMatrix b) (α : ℝ) : CMatrix a :=
  let s := (1 - α) / (2 * α)
  let D := CFC.rpow σ.matrix (-s)
  D * MatrixMap.krausAdjoint K
    (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) * D

/-- Rotated Kraus operators for the sandwiched Renyi Holder route.

For `s = (1 - α) / (2α)`, these are
`(Φσ)^s K σ^{-s}`. Their Heisenberg adjoint is exactly the input-side
Holder witness obtained by transporting an output witness through the channel.
-/
def sandwichedRenyiRotatedKraus
    (σ : State a) (τ : State b) {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (α : ℝ) : κ → Matrix b a ℂ :=
  fun k =>
    let s := (1 - α) / (2 * α)
    CFC.rpow τ.matrix s * K k * CFC.rpow σ.matrix (-s)

/-- Alignment with the weighted map in Beigi's Schatten interpolation route.

For Holder conjugates `α` and `q`, the rotated Kraus family is exactly the
Kraus representation of `Γ_τ^{-1/q} ∘ Φ ∘ Γ_σ^{1/q}`:
`τ^{-1/(2q)} K σ^{1/(2q)}`. -/
theorem sandwichedRenyiRotatedKraus_eq_beigiWeightedKraus
    (σ : State a) (τ : State b) {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (α q : ℝ) (hpq : α.HolderConjugate q) :
    sandwichedRenyiRotatedKraus σ τ K α =
      fun k => CFC.rpow τ.matrix (-(1 / q) / 2) * K k *
        CFC.rpow σ.matrix ((1 / q) / 2) := by
  funext k
  have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
  have htheta : 1 / q = 1 - 1 / α := by
    simpa [one_div] using hpq.one_sub_inv.symm
  have hs : (1 - α) / (2 * α) = -(1 / q) / 2 := by
    rw [htheta]
    field_simp [hα_ne]
    ring
  have hneg_half : - (-(1 / q) / 2) = (1 / q) / 2 := by
    ring
  simp only [sandwichedRenyiRotatedKraus]
  rw [hs, hneg_half]

/-- Complex-weighted rotated Kraus family for the interpolation proof route.

At a real exponent `s`, this is
`τ^s K σ^{-s}` and therefore specializes to the existing
`sandwichedRenyiRotatedKraus` when `s = (1 - α) / (2α)`. On imaginary boundary
lines the two reference factors are unitary by
`cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero`, providing the
matrix-power endpoint needed for the Riesz-Thorin step. -/
def sandwichedRenyiRotatedKrausComplex
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (z : ℂ) :
    κ → Matrix b a ℂ :=
  fun k =>
    cMatrixPosDefComplexPower τ.matrix hτ z * K k *
      cMatrixPosDefComplexPower σ.matrix hσ (-z)

/-- Real-axis specialization of the complex rotated Kraus family. -/
theorem sandwichedRenyiRotatedKrausComplex_ofReal
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (s : ℝ) :
    sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ) =
      fun k => CFC.rpow τ.matrix s * K k * CFC.rpow σ.matrix (-s) := by
  funext k
  have hneg : -((s : ℂ)) = ((-s : ℝ) : ℂ) := by norm_num
  unfold sandwichedRenyiRotatedKrausComplex
  rw [cMatrixPosDefComplexPower_ofReal hτ s]
  rw [hneg, cMatrixPosDefComplexPower_ofReal hσ (-s)]

/-- Analytic weighted map for the Beigi interpolation route.

For a complex strip parameter `z`, this is the source-shaped map
`X ↦ τ^z Φ(σ^{-z} X σ^{-z}) τ^z`.  On the real axis it coincides with the
Kraus map generated by `τ^z K σ^{-z}`, while avoiding the anti-holomorphic
`conjTranspose` dependence that would appear in `MatrixMap.ofKraus` away from
the real axis. -/
def sandwichedRenyiWeightedMapComplex
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (z : ℂ) :
    MatrixMap a b where
  toFun X :=
    let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
    let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
    T * MatrixMap.ofKraus K (S * X * S) * T
  map_add' X Y := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' c X := by
    simp [Matrix.mul_assoc]

/-- On real interpolation parameters, the analytic weighted map agrees with
the corresponding rotated Kraus CP map. -/
theorem sandwichedRenyiWeightedMapComplex_ofReal_eq_ofKraus
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (s : ℝ)
    (X : CMatrix a) :
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K (s : ℂ) X =
      MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ)) X := by
  let T : CMatrix b := CFC.rpow τ.matrix s
  let S : CMatrix a := CFC.rpow σ.matrix (-s)
  have hTstar : star T = T := by
    have hTpsd : T.PosSemidef := by
      simpa [T] using cMatrix_rpow_posSemidef (A := τ.matrix) (s := s) hτ.posSemidef
    exact hTpsd.isHermitian.eq
  have hSstar : star S = S := by
    have hSpsd : S.PosSemidef := by
      simpa [S] using cMatrix_rpow_posSemidef (A := σ.matrix) (s := -s) hσ.posSemidef
    exact hSpsd.isHermitian.eq
  have hneg : -((s : ℂ)) = ((-s : ℝ) : ℂ) := by norm_num
  have hconj :
      MatrixMap.ofKraus (fun k => T * K k * S) X =
        T * MatrixMap.ofKraus K (S * X * S) * T := by
    simpa [hSstar, hTstar, Matrix.mul_assoc] using
      (MatrixMap.ofKraus_conjugated_apply K T S X)
  have hfamily :
      (fun k => T * K k * S) =
        sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ) := by
    funext k
    simp [T, S, sandwichedRenyiRotatedKrausComplex_ofReal]
  calc
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K (s : ℂ) X =
        T * MatrixMap.ofKraus K (S * X * S) * T := by
          change cMatrixPosDefComplexPower τ.matrix hτ (s : ℂ) *
              MatrixMap.ofKraus K
                (cMatrixPosDefComplexPower σ.matrix hσ (-((s : ℂ))) * X *
                  cMatrixPosDefComplexPower σ.matrix hσ (-((s : ℂ)))) *
                cMatrixPosDefComplexPower τ.matrix hτ (s : ℂ) =
              T * MatrixMap.ofKraus K (S * X * S) * T
          rw [cMatrixPosDefComplexPower_ofReal hτ s]
          rw [hneg, cMatrixPosDefComplexPower_ofReal hσ (-s)]
    _ = MatrixMap.ofKraus (fun k => T * K k * S) X := hconj.symm
    _ = MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ)) X := by
          rw [hfamily]

/-- The source-shaped real rotated Kraus family is the real-axis point of the
complex interpolation family. -/
theorem sandwichedRenyiRotatedKraus_eq_complex_ofReal
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (α : ℝ) :
    sandwichedRenyiRotatedKraus σ τ K α =
      sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
        (((1 - α) / (2 * α) : ℝ) : ℂ) := by
  funext k
  rw [sandwichedRenyiRotatedKrausComplex_ofReal]
  simp [sandwichedRenyiRotatedKraus]

/-- The real interpolation point `z = -1/(2q)` of the complex rotated family is
the source-shaped rotated Kraus map for Holder-conjugate `α` and `q`. -/
theorem sandwichedRenyiRotatedKraus_eq_complex_holderTheta
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q) :
    sandwichedRenyiRotatedKraus σ τ K α =
      sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (-(((1 / q : ℝ) : ℂ) / 2)) := by
  have hpoint : -((1 / q : ℝ) / 2) = (1 - α) / (2 * α) := by
    have htheta : 1 / q = 1 - 1 / α := by
      simpa [one_div] using hpq.one_sub_inv.symm
    have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
    rw [htheta]
    field_simp [hα_ne]
    ring
  rw [sandwichedRenyiRotatedKraus_eq_complex_ofReal σ hσ τ hτ K α]
  congr 1
  exact_mod_cast hpoint.symm

/-- At the Holder interpolation point `z = -1/(2q)`, the analytic weighted map
is the source-shaped rotated Kraus map used in the sandwiched Renyi inner
operator. -/
theorem sandwichedRenyiWeightedMapComplex_holderTheta_eq_rotatedKraus
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q) (X : CMatrix a) :
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K (-(((1 / q : ℝ) : ℂ) / 2)) X =
      MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) X := by
  have hpoint : (((-(1 / q) / 2 : ℝ) : ℂ)) = -(((1 / q : ℝ) : ℂ) / 2) := by
    norm_num [one_div, div_eq_mul_inv]
  rw [← hpoint, sandwichedRenyiWeightedMapComplex_ofReal_eq_ofKraus]
  rw [hpoint]
  rw [← sandwichedRenyiRotatedKraus_eq_complex_holderTheta σ hσ τ hτ K α q hpq]

/-- Scalar trace family built from the source-faithful analytic weighted map.

The paths `Apath` and `Bpath` are the Beigi/Riesz-Thorin input and dual
witness paths.  Keeping them explicit separates the algebraic weighted-map
alignment from the later choice of analytic Schatten-normalizing paths. -/
def sandwichedRenyiWeightedTraceFamily
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b) (z : ℂ) : ℂ :=
  ((sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)) * Bpath z).trace

/-- Left-boundary endpoint estimate for the source-faithful weighted trace
family, assuming the exact boundary norm facts for the path inputs.

This is the non-circular `p = 1` Beigi endpoint: trace-norm contraction comes
only from the original trace-preserving Kraus map, while the reference and dual
paths enter through finite-dimensional contraction conditions. -/
theorem sandwichedRenyiWeightedTraceFamily_left_bound_of_traceNorm
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (C : ℝ) (z : ℂ)
    (hS : Matrix.conjTranspose (cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
        cMatrixPosDefComplexPower σ.matrix hσ (-z) = 1)
    (hT : Matrix.conjTranspose (cMatrixPosDefComplexPower τ.matrix hτ z) *
        cMatrixPosDefComplexPower τ.matrix hτ z = 1)
    (hB : Matrix.conjTranspose (Bpath z) * Bpath z ≤ 1)
    (hA : traceNorm (Apath z) ≤ C) :
    ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤ C := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  let X : CMatrix a := Apath z
  let Y : CMatrix b := Bpath z
  let M : CMatrix b := MatrixMap.ofKraus K (S * X * S)
  have hS' : Matrix.conjTranspose S * S = 1 := by simpa [S] using hS
  have hT' : Matrix.conjTranspose T * T = 1 := by simpa [T] using hT
  have hTle : Matrix.conjTranspose T * T ≤ 1 := by rw [hT']
  have hY : Matrix.conjTranspose Y * Y ≤ 1 := by simpa [Y] using hB
  have hYT : Matrix.conjTranspose (Y * T) * (Y * T) ≤ 1 :=
    MatrixMap.cMatrix_contraction_mul Y T hY hTle
  have hW : Matrix.conjTranspose (T * Y * T) * (T * Y * T) ≤ 1 := by
    simpa [Matrix.mul_assoc] using
      MatrixMap.cMatrix_contraction_mul T (Y * T) hTle hYT
  have htrace :
      sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z =
        (M * (T * Y * T)).trace := by
    unfold sandwichedRenyiWeightedTraceFamily sandwichedRenyiWeightedMapComplex
    change ((T * MatrixMap.ofKraus K (S * X * S) * T) * Y).trace =
      (M * (T * Y * T)).trace
    calc
      ((T * MatrixMap.ofKraus K (S * X * S) * T) * Y).trace =
          (T * (M * T * Y)).trace := by simp [M, Matrix.mul_assoc]
      _ = ((M * T * Y) * T).trace := by rw [Matrix.trace_mul_comm]
      _ = (M * (T * Y * T)).trace := by simp [Matrix.mul_assoc]
  have hpair :
      ‖(M * (T * Y * T)).trace‖ ≤ traceNorm M := by
    simpa using traceNorm_variational_contraction_abs_trace_le M (T * Y * T) hW
  have hkraus : traceNorm M ≤ traceNorm (S * X * S) := by
    simpa [M] using MatrixMap.traceNorm_contract_ofKraus_of_tracePreserving
      K hTP (S * X * S)
  have hSX : traceNorm (S * X * S) ≤ traceNorm X :=
    MatrixMap.traceNorm_isometry_mul_contraction_mul_le S X S hS' (by rw [hS'])
  calc
    ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ =
        ‖(M * (T * Y * T)).trace‖ := by rw [htrace]
    _ ≤ traceNorm M := hpair
    _ ≤ traceNorm (S * X * S) := hkraus
    _ ≤ traceNorm X := hSX
    _ ≤ C := by simpa [X] using hA

/-- The source-faithful weighted trace family hits the rotated-Kraus trace
pairing at the Holder interpolation point when the two analytic paths hit the
chosen input and dual witness there. -/
theorem sandwichedRenyiWeightedTraceFamily_holderTheta_target
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (A : CMatrix a) (B : CMatrix b)
    (hAθ : Apath (-(((1 / q : ℝ) : ℂ) / 2)) = A)
    (hBθ : Bpath (-(((1 / q : ℝ) : ℂ) / 2)) = B) :
    sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath
        (-(((1 / q : ℝ) : ℂ) / 2)) =
      ((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace := by
  unfold sandwichedRenyiWeightedTraceFamily
  rw [hAθ, hBθ]
  rw [sandwichedRenyiWeightedMapComplex_holderTheta_eq_rotatedKraus
    σ hσ τ hτ K α q hpq A]

private theorem matrixPath_mul_differentiable
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {M : ℂ → Matrix m n ℂ} {N : ℂ → Matrix n p ℂ}
    (hM : Differentiable ℂ M) (hN : Differentiable ℂ N) :
    Differentiable ℂ fun z : ℂ => M z * N z := by
  change Differentiable ℂ fun z : ℂ => fun i j => (M z * N z) i j
  exact differentiable_pi.2 fun i =>
    differentiable_pi.2 fun j => by
      simp only [Matrix.mul_apply]
      change Differentiable ℂ fun z : ℂ => ∑ k, M z i k * N z k j
      have hsum : Differentiable ℂ
          (∑ k, fun z : ℂ => M z i k * N z k j) :=
        Differentiable.sum (u := Finset.univ)
        (A := fun k z => M z i k * N z k j)
        (fun k _ =>
          (differentiable_pi.mp (differentiable_pi.mp hM i) k).mul
            (differentiable_pi.mp (differentiable_pi.mp hN k) j))
      convert hsum using 1
      ext z
      simp

private theorem matrixPath_smul_differentiable
    {m n : Type*} [Fintype m] [Fintype n]
    {c : ℂ → ℂ} {M : ℂ → Matrix m n ℂ}
    (hc : Differentiable ℂ c) (hM : Differentiable ℂ M) :
    Differentiable ℂ fun z : ℂ => c z • M z := by
  change Differentiable ℂ fun z : ℂ => fun i j => (c z • M z) i j
  exact differentiable_pi.2 fun i =>
    differentiable_pi.2 fun j => by
      change Differentiable ℂ fun z : ℂ => c z * M z i j
      exact hc.mul (differentiable_pi.mp (differentiable_pi.mp hM i) j)

private theorem matrixMap_ofKraus_path_differentiable
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    {Xpath : ℂ → CMatrix a} (hX : Differentiable ℂ Xpath) :
    Differentiable ℂ fun z : ℂ => MatrixMap.ofKraus K (Xpath z) := by
  change Differentiable ℂ fun z : ℂ => fun i j => (MatrixMap.ofKraus K (Xpath z)) i j
  apply differentiable_pi.2
  intro i
  apply differentiable_pi.2
  intro j
  unfold MatrixMap.ofKraus
  change Differentiable ℂ fun z : ℂ =>
    (∑ k, K k * Xpath z * Matrix.conjTranspose (K k)) i j
  simp only [Matrix.sum_apply]
  change Differentiable ℂ fun z : ℂ =>
    ∑ k, (K k * Xpath z * Matrix.conjTranspose (K k)) i j
  have hsum : Differentiable ℂ
      (∑ k, fun z : ℂ => (K k * Xpath z * Matrix.conjTranspose (K k)) i j) :=
    Differentiable.sum (u := Finset.univ)
    (A := fun k z => (K k * Xpath z * Matrix.conjTranspose (K k)) i j)
    (fun k _ => by
      have hterm : Differentiable ℂ fun z : ℂ =>
          K k * Xpath z * Matrix.conjTranspose (K k) :=
        matrixPath_mul_differentiable
          (matrixPath_mul_differentiable (differentiable_const (c := K k)) hX)
          (differentiable_const (c := Matrix.conjTranspose (K k)))
      exact differentiable_pi.mp (differentiable_pi.mp hterm i) j)
  convert hsum using 1
  ext z
  simp

private theorem matrix_trace_path_differentiable
    {n : Type*} [Fintype n] {M : ℂ → CMatrix n}
    (hM : Differentiable ℂ M) :
    Differentiable ℂ fun z : ℂ => (M z).trace := by
  unfold Matrix.trace
  change Differentiable ℂ fun z : ℂ => ∑ i, M z i i
  have hsum : Differentiable ℂ (∑ i, fun z : ℂ => M z i i) :=
    Differentiable.sum (u := Finset.univ)
    (A := fun i z => M z i i)
    (fun i _ => differentiable_pi.mp (differentiable_pi.mp hM i) i)
  convert hsum using 1
  ext z
  simp

/-- Holomorphicity of the source-faithful weighted trace family, assuming the
input and dual witness paths are holomorphic.

This is the analytic side of the Beigi/Riesz-Thorin spine after replacing the
non-holomorphic `ofKraus L_z` family by `sandwichedRenyiWeightedMapComplex`. -/
theorem sandwichedRenyiWeightedTraceFamily_differentiable
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (hApath : Differentiable ℂ Apath) (hBpath : Differentiable ℂ Bpath) :
    Differentiable ℂ
      (sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath) := by
  let Tfun : ℂ → CMatrix b := fun z => cMatrixPosDefComplexPower τ.matrix hτ z
  let Sfun : ℂ → CMatrix a := fun z => cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hT : Differentiable ℂ Tfun := by
    simpa [Tfun] using cMatrixPosDefComplexPower_differentiable hτ
  have hS : Differentiable ℂ Sfun := by
    have hraw := cMatrixPosDefComplexPower_affine_differentiable hσ (-1 : ℂ) 0
    convert hraw using 2
    ext z i
    simp [Sfun]
  have hinner : Differentiable ℂ fun z : ℂ => Sfun z * Apath z * Sfun z :=
    matrixPath_mul_differentiable (matrixPath_mul_differentiable hS hApath) hS
  have hkraus :
      Differentiable ℂ fun z : ℂ =>
        MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) :=
    matrixMap_ofKraus_path_differentiable K hinner
  have hweighted : Differentiable ℂ fun z : ℂ =>
      Tfun z * MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) * Tfun z :=
    matrixPath_mul_differentiable (matrixPath_mul_differentiable hT hkraus) hT
  have hpair : Differentiable ℂ fun z : ℂ =>
      (Tfun z * MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) * Tfun z) *
        Bpath z :=
    matrixPath_mul_differentiable hweighted hBpath
  have htrace : Differentiable ℂ fun z : ℂ =>
      ((Tfun z * MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) * Tfun z) *
        Bpath z).trace :=
    matrix_trace_path_differentiable hpair
  simpa [sandwichedRenyiWeightedTraceFamily, sandwichedRenyiWeightedMapComplex,
    Tfun, Sfun] using htrace

/-- The weighted trace family satisfies the `DiffContOnCl` analytic condition
required by the local Beigi three-lines handoff whenever its two matrix paths
are holomorphic. -/
theorem sandwichedRenyiWeightedTraceFamily_diffContOnCl_of_differentiable_paths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (hApath : Differentiable ℂ Apath) (hBpath : Differentiable ℂ Bpath) :
    DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  have hf :
      Differentiable ℂ
        (sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath) :=
    sandwichedRenyiWeightedTraceFamily_differentiable
      σ hσ τ hτ K Apath Bpath hApath hBpath
  have harg : Differentiable ℂ fun w : ℂ => -(w / 2) := by
    fun_prop
  exact (hf.comp harg).diffContOnCl

private theorem cMatrixPosDefComplexPower_one
    {A : CMatrix a} (hA : A.PosDef) :
    cMatrixPosDefComplexPower A hA (1 : ℂ) = A := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num]
  rw [cMatrixPosDefComplexPower_ofReal hA 1]
  exact CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)

private theorem cMatrixPosDefComplexPower_zero
    {A : CMatrix a} (hA : A.PosDef) :
    cMatrixPosDefComplexPower A hA (0 : ℂ) = 1 := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by norm_num]
  rw [cMatrixPosDefComplexPower_ofReal hA 0]
  exact CFC.rpow_zero A (ha := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)

/-- Beigi input path on the local strip: `A_z = A^(2αz + α)`.

With the local convention `z = -w/2`, this is the standard path
`A^(α(1-w))`; at the Holder interpolation point it is exactly `A`. -/
def sandwichedRenyiBeigiInputPath
    (A : CMatrix a) (hA : A.PosDef) (α : ℝ) (z : ℂ) : CMatrix a :=
  cMatrixPosDefComplexPower A hA ((2 * (α : ℂ)) * z + (α : ℂ))

/-- Beigi dual-witness path on the local strip: `B_z = B^(-2qz)`.

With the local convention `z = -w/2`, this is the standard path `B^(qw)`;
at the Holder interpolation point it is exactly `B`. -/
def sandwichedRenyiBeigiDualPath
    (B : CMatrix b) (hB : B.PosDef) (q : ℝ) (z : ℂ) : CMatrix b :=
  cMatrixPosDefComplexPower B hB (-(2 * (q : ℂ) * z))

theorem sandwichedRenyiBeigiInputPath_differentiable
    (A : CMatrix a) (hA : A.PosDef) (α : ℝ) :
    Differentiable ℂ (sandwichedRenyiBeigiInputPath A hA α) := by
  simpa [sandwichedRenyiBeigiInputPath] using
    cMatrixPosDefComplexPower_affine_differentiable hA ((2 * α : ℝ) : ℂ) (α : ℂ)

theorem sandwichedRenyiBeigiDualPath_differentiable
    (B : CMatrix b) (hB : B.PosDef) (q : ℝ) :
    Differentiable ℂ (sandwichedRenyiBeigiDualPath B hB q) := by
  simpa [sandwichedRenyiBeigiDualPath] using
    cMatrixPosDefComplexPower_affine_differentiable hB ((-2 * q : ℝ) : ℂ) 0

theorem sandwichedRenyiBeigiInputPath_holderTheta
    {A : CMatrix a} (hA : A.PosDef)
    {α q : ℝ} (hpq : α.HolderConjugate q) :
    sandwichedRenyiBeigiInputPath A hA α (-(((1 / q : ℝ) : ℂ) / 2)) = A := by
  have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
  have hq_ne : q ≠ 0 := ne_of_gt hpq.symm.pos
  have hexp_real : 2 * α * -(1 / q / 2) + α = 1 := by
    have hsum : 1 / α + 1 / q = 1 := by
      simpa [one_div] using hpq.inv_add_inv_eq_one
    field_simp [hα_ne, hq_ne] at hsum ⊢
    nlinarith
  have hexp :
      (2 * (α : ℂ) * (-(((1 / q : ℝ) : ℂ) / 2)) + (α : ℂ)) = 1 := by
    exact_mod_cast hexp_real
  rw [sandwichedRenyiBeigiInputPath, hexp]
  exact cMatrixPosDefComplexPower_one hA

theorem sandwichedRenyiBeigiDualPath_holderTheta
    {B : CMatrix b} (hB : B.PosDef)
    {α q : ℝ} (hpq : α.HolderConjugate q) :
    sandwichedRenyiBeigiDualPath B hB q (-(((1 / q : ℝ) : ℂ) / 2)) = B := by
  have hq_ne : q ≠ 0 := ne_of_gt hpq.symm.pos
  have hexp_real : -(2 * q * -(1 / q / 2)) = 1 := by
    field_simp [hq_ne]
  have hexp :
      (-(2 * (q : ℂ) * (-(((1 / q : ℝ) : ℂ) / 2)))) = 1 := by
    exact_mod_cast hexp_real
  rw [sandwichedRenyiBeigiDualPath, hexp]
  exact cMatrixPosDefComplexPower_one hB

theorem sandwichedRenyiBeigiInputPath_zero
    {A : CMatrix a} (hA : A.PosDef) (α : ℝ) :
    sandwichedRenyiBeigiInputPath A hA α 0 = CFC.rpow A α := by
  rw [sandwichedRenyiBeigiInputPath]
  have hexp : (2 * (α : ℂ)) * 0 + (α : ℂ) = (α : ℂ) := by ring
  rw [hexp, cMatrixPosDefComplexPower_ofReal hA α]

theorem sandwichedRenyiBeigiDualPath_zero
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) :
    sandwichedRenyiBeigiDualPath B hB q 0 = 1 := by
  rw [sandwichedRenyiBeigiDualPath]
  have hexp : -(2 * (q : ℂ) * 0) = 0 := by ring
  rw [hexp, cMatrixPosDefComplexPower_zero hB]

theorem sandwichedRenyiBeigiDualPath_star_mul_self_of_re_eq_zero
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) {z : ℂ} (hz : z.re = 0) :
    star (sandwichedRenyiBeigiDualPath B hB q z) *
        sandwichedRenyiBeigiDualPath B hB q z = 1 := by
  have hexp_re : (-(2 * (q : ℂ) * z)).re = 0 := by
    simp [hz]
  simpa [sandwichedRenyiBeigiDualPath] using
    cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hB (z := -(2 * (q : ℂ) * z))
      hexp_re

/-- On the `p = ∞` boundary of the local Beigi strip, the dual path's trace
norm is exactly its `q`-power trace. -/
theorem sandwichedRenyiBeigiDualPath_traceNorm_of_re_eq_neg_half
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) {z : ℂ}
    (hz : z.re = -(1 / 2 : ℝ)) :
    traceNorm (sandwichedRenyiBeigiDualPath B hB q z) =
      psdTracePower B hB.posSemidef q := by
  have hexp_re : (-(2 * (q : ℂ) * z)).re = q := by
    simp [hz]
    ring
  simpa [sandwichedRenyiBeigiDualPath, hexp_re] using
    MatrixMap.traceNorm_cMatrixPosDefComplexPower_eq_psdTracePower_re hB
      (-(2 * (q : ℂ) * z))

/-- A `q`-unit-ball dual witness gives trace-norm control of the Beigi dual
path on the `p = ∞` boundary. -/
theorem sandwichedRenyiBeigiDualPath_traceNorm_le_one_of_re_eq_neg_half
    {B : CMatrix b} (hB : B.PosDef) {q : ℝ}
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    traceNorm (sandwichedRenyiBeigiDualPath B hB q z) ≤ 1 := by
  rw [sandwichedRenyiBeigiDualPath_traceNorm_of_re_eq_neg_half hB q hz]
  exact hBq

theorem sandwichedRenyiBeigiInputPath_star_mul_self_of_re_eq_neg_half
    {A : CMatrix a} (hA : A.PosDef) (α : ℝ) {z : ℂ}
    (hz : z.re = -(1 / 2 : ℝ)) :
    star (sandwichedRenyiBeigiInputPath A hA α z) *
        sandwichedRenyiBeigiInputPath A hA α z = 1 := by
  have hexp_re : ((2 * (α : ℂ)) * z + (α : ℂ)).re = 0 := by
    simp [hz]
    ring
  simpa [sandwichedRenyiBeigiInputPath] using
    cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA
      (z := (2 * (α : ℂ)) * z + (α : ℂ)) hexp_re

/-- Normalized Beigi input path:
`‖A‖_α^(1-(2αz+α)) A^(2αz+α)`.

The scalar normalization is the standard Riesz-Thorin normalization: the path
still hits `A` at the Holder point, while its two boundary norms are scaled by
`‖A‖_α` rather than by `Tr A^α`. -/
def sandwichedRenyiBeigiNormalizedInputPath
    (A : CMatrix a) (hA : A.PosDef) (α : ℝ) (C : ℝ) (z : ℂ) : CMatrix a :=
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)) •
    cMatrixPosDefComplexPower A hA e

theorem sandwichedRenyiBeigiNormalizedInputPath_differentiable
    (A : CMatrix a) (hA : A.PosDef) (α C : ℝ) :
    Differentiable ℂ (sandwichedRenyiBeigiNormalizedInputPath A hA α C) := by
  let e : ℂ → ℂ := fun z => (2 * (α : ℂ)) * z + (α : ℂ)
  have he : Differentiable ℂ e := by
    fun_prop
  have hscale : Differentiable ℂ fun z : ℂ =>
      Complex.exp (((1 : ℂ) - e z) * ((Real.log C : ℝ) : ℂ)) := by
    fun_prop
  have hpow : Differentiable ℂ fun z : ℂ => cMatrixPosDefComplexPower A hA (e z) := by
    simpa [e] using
      cMatrixPosDefComplexPower_affine_differentiable hA (2 * (α : ℂ)) (α : ℂ)
  simpa [sandwichedRenyiBeigiNormalizedInputPath, e] using
    matrixPath_smul_differentiable hscale hpow

theorem sandwichedRenyiBeigiNormalizedInputPath_holderTheta
    {A : CMatrix a} (hA : A.PosDef)
    {α q : ℝ} (hpq : α.HolderConjugate q) {C : ℝ} :
    sandwichedRenyiBeigiNormalizedInputPath A hA α C
        (-(((1 / q : ℝ) : ℂ) / 2)) = A := by
  have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
  have hq_ne : q ≠ 0 := ne_of_gt hpq.symm.pos
  have hexp_real : 2 * α * -(1 / q / 2) + α = 1 := by
    have hsum : 1 / α + 1 / q = 1 := by
      simpa [one_div] using hpq.inv_add_inv_eq_one
    field_simp [hα_ne, hq_ne] at hsum ⊢
    nlinarith
  have hexp :
      (2 * (α : ℂ) * (-(((1 / q : ℝ) : ℂ) / 2)) + (α : ℂ)) = 1 := by
    exact_mod_cast hexp_real
  rw [sandwichedRenyiBeigiNormalizedInputPath, hexp]
  simp [cMatrixPosDefComplexPower_one hA]

/-- The normalized Beigi input path has trace norm at most its normalizing
Schatten value on the `Re z = 0` boundary. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_traceNorm_le_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosDef) {α C : ℝ} (hα : 0 < α)
    (hC : C = psdSchattenPNorm A hA.posSemidef α) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = 0) :
    traceNorm (sandwichedRenyiBeigiNormalizedInputPath A hA α C z) ≤ C := by
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  let scalar : ℂ := Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ))
  let Q : ℝ := psdTracePower A hA.posSemidef α
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have he_re : e.re = α := by
    simp [e, hz]
  have hscalar_norm : ‖scalar‖ = C ^ (1 - α) := by
    have hre :
        (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re =
          (1 - α) * Real.log C := by
      simp [Complex.mul_re, he_re]
    calc
      ‖scalar‖ = Real.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re := by
          simp [scalar, Complex.norm_exp]
      _ = Real.exp ((1 - α) * Real.log C) := by rw [hre]
      _ = C ^ (1 - α) := by
          rw [Real.rpow_def_of_pos hCpos]
          congr 1
          ring
  have hpower_trace :
      traceNorm (cMatrixPosDefComplexPower A hA e) = Q := by
    simpa [Q, he_re] using
      MatrixMap.traceNorm_cMatrixPosDefComplexPower_eq_psdTracePower_re hA e
  have hQ_nonneg : 0 ≤ Q := by
    simpa [Q] using psdTracePower_nonneg A hA.posSemidef α
  have hC_def : C = Q ^ (1 / α) := by
    simpa [Q, psdSchattenPNorm] using hC
  have hQ_eq_Cpow : Q = C ^ α := by
    calc
      Q = Q ^ ((1 / α) * α) := by
          have hmul : (1 / α) * α = (1 : ℝ) := by field_simp [hα_ne]
          rw [hmul, Real.rpow_one]
      _ = (Q ^ (1 / α)) ^ α := by rw [Real.rpow_mul hQ_nonneg]
      _ = C ^ α := by rw [← hC_def]
  have hscale :=
    MatrixMap.traceNorm_complex_smul_le scalar
      (cMatrixPosDefComplexPower A hA e)
  calc
    traceNorm (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)
        ≤ ‖scalar‖ * traceNorm (cMatrixPosDefComplexPower A hA e) := by
          simpa [sandwichedRenyiBeigiNormalizedInputPath, scalar, e] using hscale
    _ = C ^ (1 - α) * Q := by rw [hscalar_norm, hpower_trace]
    _ = C ^ (1 - α) * C ^ α := by rw [hQ_eq_Cpow]
    _ = C ^ ((1 - α) + α) := by rw [← Real.rpow_add hCpos]
    _ = C := by
          ring_nf
          rw [Real.rpow_one]

section BeigiInputOperatorEndpoint

open scoped Matrix.Norms.L2Operator

/-- On the `p = ∞` boundary, the normalized Beigi input path has operator norm
at most its normalizing Schatten value. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_opNorm_le_of_re_eq_neg_half
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    ‖sandwichedRenyiBeigiNormalizedInputPath A hA α C z‖ ≤ C := by
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  let scalar : ℂ := Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ))
  have he_re : e.re = 0 := by
    simp [e, hz]
    ring
  have hscalar_norm : ‖scalar‖ = C := by
    have hre :
        (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re =
          Real.log C := by
      simp [Complex.mul_re, he_re]
    calc
      ‖scalar‖ = Real.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re := by
          simp [scalar, Complex.norm_exp]
      _ = Real.exp (Real.log C) := by rw [hre]
      _ = C := Real.exp_log hCpos
  have hpow_contract :
      ‖cMatrixPosDefComplexPower A hA e‖ ≤ (1 : ℝ) := by
    have hgram :
        Matrix.conjTranspose (cMatrixPosDefComplexPower A hA e) *
            cMatrixPosDefComplexPower A hA e ≤ 1 := by
      have hunit :
          Matrix.conjTranspose (cMatrixPosDefComplexPower A hA e) *
              cMatrixPosDefComplexPower A hA e = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using
          cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA he_re
      rw [hunit]
    exact MatrixMap.cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one
      (cMatrixPosDefComplexPower A hA e) hgram
  calc
    ‖sandwichedRenyiBeigiNormalizedInputPath A hA α C z‖ =
        ‖scalar‖ * ‖cMatrixPosDefComplexPower A hA e‖ := by
          simp [sandwichedRenyiBeigiNormalizedInputPath, scalar, e, norm_smul]
    _ ≤ C * 1 := by
          rw [hscalar_norm]
          exact mul_le_mul_of_nonneg_left hpow_contract (le_of_lt hCpos)
    _ = C := by ring

/-- On the `p = ∞` boundary, the normalized Beigi input path is a matrix
contraction after dividing by its Schatten normalizing constant.

This strengthens the norm estimate above to the exact unit-ball condition used
by the trace-norm variational handoff. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_scaled_contraction_of_re_eq_neg_half
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    Matrix.conjTranspose (((C : ℂ)⁻¹) •
        sandwichedRenyiBeigiNormalizedInputPath A hA α C z) *
      (((C : ℂ)⁻¹) •
        sandwichedRenyiBeigiNormalizedInputPath A hA α C z) ≤ 1 := by
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  let scalar : ℂ := Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ))
  let c : ℂ := (C : ℂ)⁻¹ * scalar
  let P : CMatrix a := cMatrixPosDefComplexPower A hA e
  have he_re : e.re = 0 := by
    simp [e, hz]
    ring
  have hscalar_norm : ‖scalar‖ = C := by
    have hre :
        (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re =
          Real.log C := by
      simp [Complex.mul_re, he_re]
    calc
      ‖scalar‖ = Real.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re := by
          simp [scalar, Complex.norm_exp]
      _ = Real.exp (Real.log C) := by rw [hre]
      _ = C := Real.exp_log hCpos
  have hc_norm : ‖c‖ = 1 := by
    calc
      ‖c‖ = ‖(C : ℂ)⁻¹‖ * ‖scalar‖ := by simp [c]
      _ = ‖(C : ℂ)‖⁻¹ * C := by rw [norm_inv, hscalar_norm]
      _ = C⁻¹ * C := by
            have hCnorm : ‖(C : ℂ)‖ = C := by
              rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hCpos)]
            rw [hCnorm]
      _ = 1 := by field_simp [ne_of_gt hCpos]
  have hc_star_mul : star c * c = 1 := by
    have hnormSq : Complex.normSq c = 1 := by
      rw [Complex.normSq_eq_norm_sq, hc_norm]
      norm_num
    change (starRingEnd ℂ) c * c = 1
    rw [← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast hnormSq
  have hc_mul_star : c * star c = 1 := by
    rw [mul_comm]
    exact hc_star_mul
  have hc_mul_star' : c * (starRingEnd ℂ) c = 1 := by
    simpa using hc_mul_star
  have hPunit : Matrix.conjTranspose P * P = (1 : CMatrix a) := by
    simpa [P, Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA he_re
  have hpath :
      ((C : ℂ)⁻¹) • sandwichedRenyiBeigiNormalizedInputPath A hA α C z =
        c • P := by
    simp [sandwichedRenyiBeigiNormalizedInputPath, scalar, c, P, e, smul_smul,
      mul_assoc]
  rw [hpath]
  have heq :
      Matrix.conjTranspose (c • P) * (c • P) = (1 : CMatrix a) := by
    simp [Matrix.conjTranspose_smul, hPunit, smul_smul, hc_mul_star']
  rw [heq]

/-- Imaginary positive-definite complex powers are contractions in matrix
unit-ball form. -/
theorem cMatrixPosDefComplexPower_contraction_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosDef) {z : ℂ} (hz : z.re = 0) :
    Matrix.conjTranspose (cMatrixPosDefComplexPower A hA z) *
        cMatrixPosDefComplexPower A hA z ≤ 1 := by
  have hunit :
      Matrix.conjTranspose (cMatrixPosDefComplexPower A hA z) *
          cMatrixPosDefComplexPower A hA z = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA hz
  rw [hunit]

/-- Left and right multiplication by the same imaginary reference power
preserves the matrix unit ball. -/
theorem cMatrixPosDefComplexPower_mul_mul_contraction_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosDef) {z : ℂ} (hz : z.re = 0)
    {X : CMatrix a} (hX : Matrix.conjTranspose X * X ≤ 1) :
    Matrix.conjTranspose
        (cMatrixPosDefComplexPower A hA z * X *
          cMatrixPosDefComplexPower A hA z) *
      (cMatrixPosDefComplexPower A hA z * X *
          cMatrixPosDefComplexPower A hA z) ≤ 1 := by
  let U : CMatrix a := cMatrixPosDefComplexPower A hA z
  have hU : Matrix.conjTranspose U * U ≤ 1 :=
    cMatrixPosDefComplexPower_contraction_of_re_eq_zero hA hz
  have hUX : Matrix.conjTranspose (U * X) * (U * X) ≤ 1 :=
    MatrixMap.cMatrix_contraction_mul U X hU hX
  simpa [Matrix.mul_assoc, U] using
    MatrixMap.cMatrix_contraction_mul (U * X) U hUX hU

/-- Beigi right-boundary factorization for the source-faithful weighted map.

On the line `Re z = -1/2`, the analytic map
`X ↦ τ^z Φ(σ^{-z} X σ^{-z}) τ^z` factors as imaginary unitary rotations of
the real `z = -1/2` unital Kraus endpoint. -/
theorem sandwichedRenyiWeightedMapComplex_eq_imaginary_conj_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (z : ℂ) (X : CMatrix a) :
    let u : ℂ := z + ((1 / 2 : ℝ) : ℂ)
    let Uτ : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ u
    let Uσ : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-u)
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X =
      Uτ *
        MatrixMap.ofKraus
          (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
            (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (Uσ * X * Uσ) *
        Uτ := by
  let u : ℂ := z + ((1 / 2 : ℝ) : ℂ)
  let Uτ : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ u
  let Uσ : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-u)
  let T0 : CMatrix b :=
    cMatrixPosDefComplexPower τ.matrix hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let S0 : CMatrix a :=
    cMatrixPosDefComplexPower σ.matrix hσ (((1 / 2 : ℝ) : ℝ) : ℂ)
  have hT_left :
      cMatrixPosDefComplexPower τ.matrix hτ z = Uτ * T0 := by
    have h :=
      cMatrixPosDefComplexPower_add hτ u (((-(1 / 2 : ℝ)) : ℝ) : ℂ)
    have hsum : u + (((-(1 / 2 : ℝ)) : ℝ) : ℂ) = z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hT_right :
      cMatrixPosDefComplexPower τ.matrix hτ z = T0 * Uτ := by
    have h :=
      cMatrixPosDefComplexPower_add hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) u
    have hsum : (((-(1 / 2 : ℝ)) : ℝ) : ℂ) + u = z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hS_left :
      cMatrixPosDefComplexPower σ.matrix hσ (-z) = S0 * Uσ := by
    have h :=
      cMatrixPosDefComplexPower_add hσ (((1 / 2 : ℝ) : ℝ) : ℂ) (-u)
    have hsum : (((1 / 2 : ℝ) : ℝ) : ℂ) + -u = -z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hS_right :
      cMatrixPosDefComplexPower σ.matrix hσ (-z) = Uσ * S0 := by
    have h :=
      cMatrixPosDefComplexPower_add hσ (-u) (((1 / 2 : ℝ) : ℝ) : ℂ)
    have hsum : -u + (((1 / 2 : ℝ) : ℝ) : ℂ) = -z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hM :
      MatrixMap.ofKraus
          (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
            (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (Uσ * X * Uσ) =
        T0 * MatrixMap.ofKraus K (S0 * (Uσ * X * Uσ) * S0) * T0 := by
    have hreal :=
      sandwichedRenyiWeightedMapComplex_ofReal_eq_ofKraus
        σ hσ τ hτ K (-(1 / 2 : ℝ)) (Uσ * X * Uσ)
    rw [← hreal]
    unfold sandwichedRenyiWeightedMapComplex
    change
      cMatrixPosDefComplexPower τ.matrix hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          MatrixMap.ofKraus K
            (cMatrixPosDefComplexPower σ.matrix hσ
                (-((((-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
              (Uσ * X * Uσ) *
              cMatrixPosDefComplexPower σ.matrix hσ
                (-((((-(1 / 2 : ℝ)) : ℝ) : ℂ)))) *
          cMatrixPosDefComplexPower τ.matrix hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        T0 * MatrixMap.ofKraus K (S0 * (Uσ * X * Uσ) * S0) * T0
    have hneg : -((((-(1 / 2 : ℝ)) : ℝ) : ℂ)) = (((1 / 2 : ℝ) : ℝ) : ℂ) := by
      norm_num
    rw [hneg]
  unfold sandwichedRenyiWeightedMapComplex
  change
    cMatrixPosDefComplexPower τ.matrix hτ z *
        MatrixMap.ofKraus K
          (cMatrixPosDefComplexPower σ.matrix hσ (-z) * X *
            cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
        cMatrixPosDefComplexPower τ.matrix hτ z =
      Uτ *
        MatrixMap.ofKraus
          (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
            (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (Uσ * X * Uσ) *
        Uτ
  nth_rewrite 1 [hT_left]
  nth_rewrite 1 [hT_right]
  nth_rewrite 1 [hS_left]
  nth_rewrite 1 [hS_right]
  rw [hM]
  have hinside :
      (S0 * Uσ) * X * (Uσ * S0) =
        S0 * (Uσ * X * Uσ) * S0 := by
    noncomm_ring
  rw [hinside]
  noncomm_ring

end BeigiInputOperatorEndpoint

/-- The concrete Beigi input and dual paths satisfy the analytic
`DiffContOnCl` condition required by the local three-lines handoff. -/
theorem sandwichedRenyiWeightedTraceFamily_diffContOnCl_beigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q : ℝ) :
    DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiInputPath A hA α)
          (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
  sandwichedRenyiWeightedTraceFamily_diffContOnCl_of_differentiable_paths
    σ hσ τ hτ K
    (sandwichedRenyiBeigiInputPath A hA α)
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiInputPath_differentiable A hA α)
    (sandwichedRenyiBeigiDualPath_differentiable B hB q)

/-- The normalized Beigi input path and dual path satisfy the analytic
`DiffContOnCl` condition required by the local three-lines handoff. -/
theorem sandwichedRenyiWeightedTraceFamily_diffContOnCl_normalizedBeigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q C : ℝ) :
    DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
          (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
  sandwichedRenyiWeightedTraceFamily_diffContOnCl_of_differentiable_paths
    σ hσ τ hτ K
    (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiNormalizedInputPath_differentiable A hA α C)
    (sandwichedRenyiBeigiDualPath_differentiable B hB q)

section BeigiClosedStripBoundedness

open scoped Matrix.Norms.L2Operator

private theorem bddAbove_norm_mul_of_bddAbove
    {ι R : Type*} [SeminormedRing R] {s : Set ι} {f g : ι → R}
    (hf : BddAbove ((norm ∘ f) '' s))
    (hg : BddAbove ((norm ∘ g) '' s)) :
    BddAbove ((norm ∘ fun x => f x * g x) '' s) := by
  rcases hf with ⟨Cf, hCf⟩
  rcases hg with ⟨Cg, hCg⟩
  refine ⟨max (Cf * Cg) 0, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hf_le : ‖f x‖ ≤ Cf := hCf ⟨x, hx, rfl⟩
  have hg_le : ‖g x‖ ≤ Cg := hCg ⟨x, hx, rfl⟩
  have hf_nonneg : 0 ≤ Cf := (norm_nonneg (f x)).trans hf_le
  have hprod : ‖f x‖ * ‖g x‖ ≤ Cf * Cg :=
    mul_le_mul hf_le hg_le (norm_nonneg (g x)) hf_nonneg
  calc
    ‖f x * g x‖ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le _ _
    _ ≤ Cf * Cg := hprod
    _ ≤ max (Cf * Cg) 0 := le_max_left _ _

private theorem bddAbove_norm_smul_of_bddAbove
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set ι} {c : ι → ℂ} {f : ι → E}
    (hc : BddAbove ((norm ∘ c) '' s))
    (hf : BddAbove ((norm ∘ f) '' s)) :
    BddAbove ((norm ∘ fun x => c x • f x) '' s) := by
  rcases hc with ⟨Cc, hCc⟩
  rcases hf with ⟨Cf, hCf⟩
  refine ⟨max (Cc * Cf) 0, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hc_le : ‖c x‖ ≤ Cc := hCc ⟨x, hx, rfl⟩
  have hf_le : ‖f x‖ ≤ Cf := hCf ⟨x, hx, rfl⟩
  have hc_nonneg : 0 ≤ Cc := (norm_nonneg (c x)).trans hc_le
  have hprod : ‖c x‖ * ‖f x‖ ≤ Cc * Cf :=
    mul_le_mul hc_le hf_le (norm_nonneg (f x)) hc_nonneg
  calc
    ‖c x • f x‖ = ‖c x‖ * ‖f x‖ := norm_smul _ _
    _ ≤ Cc * Cf := hprod
    _ ≤ max (Cc * Cf) 0 := le_max_left _ _

private theorem bddAbove_norm_linearMap_of_bddAbove
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {s : Set ι} {f : ι → E} (L : E →ₗ[ℂ] F)
    (hf : BddAbove ((norm ∘ f) '' s)) :
    BddAbove ((norm ∘ fun x => L (f x)) '' s) := by
  rcases hf with ⟨C, hC⟩
  let C' : ℝ := max C 0
  let Lc : E →L[ℂ] F := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ * C', ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hf_le_C : ‖f x‖ ≤ C := hC ⟨x, hx, rfl⟩
  have hf_le : ‖f x‖ ≤ C' := hf_le_C.trans (le_max_left C 0)
  have hL : ‖L (f x)‖ ≤ ‖Lc‖ * ‖f x‖ := by
    simpa [Lc, LinearMap.coe_toContinuousLinearMap] using Lc.le_opNorm (f x)
  exact hL.trans (mul_le_mul_of_nonneg_left hf_le (norm_nonneg Lc))

/-- Positive-definite complex powers have operator norm depending only on the
real part of the exponent. This is the boundedness ingredient that prevents
the Beigi strip from growing in the imaginary direction. -/
theorem cMatrixPosDefComplexPower_l2OperatorNorm_eq_re
    {A : CMatrix a} (hA : A.PosDef) (z : ℂ) :
    ‖cMatrixPosDefComplexPower A hA z‖ =
      ‖cMatrixPosDefComplexPower A hA ((z.re : ℝ) : ℂ)‖ := by
  let Pz : CMatrix a := cMatrixPosDefComplexPower A hA z
  let Pr : CMatrix a := cMatrixPosDefComplexPower A hA ((z.re : ℝ) : ℂ)
  have hzstar : Matrix.conjTranspose Pz * Pz = CFC.rpow A (2 * z.re) := by
    simpa [Pz, Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self hA z
  have hr_re : (((z.re : ℝ) : ℂ)).re = z.re := by simp
  have hrstar : Matrix.conjTranspose Pr * Pr = CFC.rpow A (2 * z.re) := by
    simpa [Pr, hr_re, Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self hA (((z.re : ℝ) : ℂ))
  have hzsq : ‖Pz‖ * ‖Pz‖ = ‖CFC.rpow A (2 * z.re)‖ := by
    calc
      ‖Pz‖ * ‖Pz‖ = ‖Matrix.conjTranspose Pz * Pz‖ := by
        simpa [Matrix.star_eq_conjTranspose] using
          (CStarRing.norm_star_mul_self (x := Pz)).symm
      _ = ‖CFC.rpow A (2 * z.re)‖ := by rw [hzstar]
  have hrsq : ‖Pr‖ * ‖Pr‖ = ‖CFC.rpow A (2 * z.re)‖ := by
    calc
      ‖Pr‖ * ‖Pr‖ = ‖Matrix.conjTranspose Pr * Pr‖ := by
        simpa [Matrix.star_eq_conjTranspose] using
          (CStarRing.norm_star_mul_self (x := Pr)).symm
      _ = ‖CFC.rpow A (2 * z.re)‖ := by rw [hrstar]
  have hsq : ‖Pz‖ ^ 2 = ‖Pr‖ ^ 2 := by
    rw [pow_two, pow_two, hzsq, hrsq]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).elim id (fun hneg => by
    have hpz := norm_nonneg Pz
    have hpr := norm_nonneg Pr
    nlinarith)

private theorem cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
    {A : CMatrix a} (hA : A.PosDef) (m c l u : ℝ) :
    BddAbove ((norm ∘
      (fun z : ℂ => cMatrixPosDefComplexPower A hA (((m : ℂ) * z + (c : ℂ))))) ''
      (Complex.re ⁻¹' Set.Icc l u)) := by
  let g : ℝ → ℝ := fun t =>
    ‖cMatrixPosDefComplexPower A hA (((m * t + c : ℝ) : ℂ))‖
  have hgcont : Continuous g := by
    have hcpow : Continuous fun t : ℝ =>
        cMatrixPosDefComplexPower A hA (((m * t + c : ℝ) : ℂ)) := by
      have hd := cMatrixPosDefComplexPower_differentiable hA
      exact hd.continuous.comp (by fun_prop)
    simpa [g] using hcpow.norm
  have hbddg : BddAbove (g '' Set.Icc l u) :=
    isCompact_Icc.bddAbove_image hgcont.continuousOn
  rcases hbddg with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have harg_re : (((m : ℂ) * z + (c : ℂ))).re = m * z.re + c := by
    simp [Complex.mul_re]
  have hnorm :=
    cMatrixPosDefComplexPower_l2OperatorNorm_eq_re hA (((m : ℂ) * z + (c : ℂ)))
  calc
    ‖cMatrixPosDefComplexPower A hA (((m : ℂ) * z + (c : ℂ)))‖ =
        g z.re := by
          rw [hnorm]
          simp [g, harg_re]
    _ ≤ C := hC ⟨z.re, hz, rfl⟩

private theorem complex_exp_affine_norm_bddAbove_of_re_mem_Icc
    (m c C l u : ℝ) :
    BddAbove ((norm ∘
      (fun z : ℂ =>
        Complex.exp (((1 : ℂ) - ((m : ℂ) * z + (c : ℂ))) *
          ((Real.log C : ℝ) : ℂ)))) ''
      (Complex.re ⁻¹' Set.Icc l u)) := by
  let g : ℝ → ℝ := fun t =>
    ‖Complex.exp (((1 : ℂ) - (((m * t + c : ℝ) : ℂ))) *
      ((Real.log C : ℝ) : ℂ))‖
  have hgcont : Continuous g := by
    simpa [g] using
      ((Complex.continuous_exp.comp (by fun_prop : Continuous fun t : ℝ =>
        ((1 : ℂ) - (((m * t + c : ℝ) : ℂ))) *
          ((Real.log C : ℝ) : ℂ))).norm)
  have hbddg : BddAbove (g '' Set.Icc l u) :=
    isCompact_Icc.bddAbove_image hgcont.continuousOn
  rcases hbddg with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have harg_re : (((m : ℂ) * z + (c : ℂ))).re = m * z.re + c := by
    simp [Complex.mul_re]
  have hnorm :
      ‖Complex.exp (((1 : ℂ) - ((m : ℂ) * z + (c : ℂ))) *
          ((Real.log C : ℝ) : ℂ))‖ =
        g z.re := by
    simp [g, harg_re, Complex.norm_exp, Complex.mul_re]
  calc
    ‖Complex.exp (((1 : ℂ) - ((m : ℂ) * z + (c : ℂ))) *
        ((Real.log C : ℝ) : ℂ))‖ = g z.re := hnorm
    _ ≤ D := hD ⟨z.re, hz, rfl⟩

/-- The normalized Beigi input path is bounded on the closed interpolation
strip. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_bddAbove_closedStrip
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) :
    BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiNormalizedInputPath A hA α C (-(w / 2))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiNormalizedInputPath A hA α C (-(w / 2))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  have hscalar : BddAbove ((norm ∘ fun w : ℂ =>
      Complex.exp (((1 : ℂ) - (((-α : ℝ) : ℂ) * w + (α : ℂ))) *
        ((Real.log C : ℝ) : ℂ))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    complex_exp_affine_norm_bddAbove_of_re_mem_Icc (-α) α C 0 1
  have hpow : BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (((-α : ℝ) : ℂ) * w + (α : ℂ))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      hA (-α) α 0 1
  have h := bddAbove_norm_smul_of_bddAbove
    (s := Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) hscalar hpow
  convert h using 6
  ext w
  simp [sandwichedRenyiBeigiNormalizedInputPath]
  ring_nf

/-- The Beigi dual path is bounded on the closed interpolation strip. -/
theorem sandwichedRenyiBeigiDualPath_bddAbove_closedStrip
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) :
    BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiDualPath B hB q (-(w / 2))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiDualPath B hB q (-(w / 2))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  have hraw : BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower B hB (((q : ℂ) * w + (0 : ℂ)))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      hB q 0 0 1
  rcases hraw with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  have harg : -(2 * (q : ℂ) * (-(w / 2))) = (q : ℂ) * w + 0 := by
    ring_nf
  have hle := hD ⟨w, hw, rfl⟩
  unfold sandwichedRenyiBeigiDualPath
  change ‖cMatrixPosDefComplexPower B hB (-(2 * (q : ℂ) * (-(w / 2))))‖ ≤ D
  rw [harg]
  simpa [Function.comp_def] using hle

private theorem cMatrixPosDefComplexPower_bddAbove_neg_half_closedStrip
    {A : CMatrix a} (hA : A.PosDef) :
    BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (-(w / 2))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (-(w / 2))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  let m : ℝ := -(1 / 2)
  have hraw :
      BddAbove ((norm ∘ fun w : ℂ =>
        cMatrixPosDefComplexPower A hA (((m : ℂ) * w + (0 : ℂ)))) ''
        (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      (A := A) hA (m := m) (c := 0) (l := 0) (u := 1)
  rcases hraw with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  have harg : -(w / 2) = ((m : ℂ) * w + (0 : ℂ)) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    calc
      -(w / 2) = -((1 / 2 : ℂ) * w) := by ring
      _ = ((m : ℂ) * w + (0 : ℂ)) := by
            simp [m, hhalf, neg_mul]
  have hle := hD ⟨w, hw, rfl⟩
  simpa [Function.comp_def, harg] using hle

private theorem cMatrixPosDefComplexPower_bddAbove_pos_half_closedStrip
    {A : CMatrix a} (hA : A.PosDef) :
    BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (w / 2)) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (w / 2)) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  let m : ℝ := 1 / 2
  have hraw : BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (((m : ℂ) * w + (0 : ℂ)))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      (A := A) hA (m := m) (c := 0) (l := 0) (u := 1)
  rcases hraw with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  have harg : w / 2 = ((m : ℂ) * w + (0 : ℂ)) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    calc
      w / 2 = (1 / 2 : ℂ) * w := by ring
      _ = ((m : ℂ) * w + (0 : ℂ)) := by
            simp [m, hhalf]
  have hle := hD ⟨w, hw, rfl⟩
  simpa [Function.comp_def, harg] using hle

/-- The normalized Beigi scalar trace family is bounded on the closed strip.

This discharges the remaining analytic side condition required by
Hadamard three-lines. The proof is purely a finite-dimensional boundedness
argument: each complex-power factor has norm depending only on the real part,
and the remaining operations are continuous linear maps and matrix products. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_bddAbove_closedStrip
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q C : ℝ) :
    BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  let s : Set ℂ := Complex.HadamardThreeLines.verticalClosedStrip 0 1
  let Tpath : ℂ → CMatrix b := fun w =>
    cMatrixPosDefComplexPower τ.matrix hτ (-(w / 2))
  let Spath : ℂ → CMatrix a := fun w =>
    cMatrixPosDefComplexPower σ.matrix hσ (w / 2)
  let Apath : ℂ → CMatrix a := fun w =>
    sandwichedRenyiBeigiNormalizedInputPath A hA α C (-(w / 2))
  let Bpath : ℂ → CMatrix b := fun w =>
    sandwichedRenyiBeigiDualPath B hB q (-(w / 2))
  have hT : BddAbove ((norm ∘ Tpath) '' s) := by
    simpa [s, Tpath] using
      cMatrixPosDefComplexPower_bddAbove_neg_half_closedStrip hτ
  have hS : BddAbove ((norm ∘ Spath) '' s) := by
    simpa [s, Spath] using
      cMatrixPosDefComplexPower_bddAbove_pos_half_closedStrip hσ
  have hApath : BddAbove ((norm ∘ Apath) '' s) := by
    simpa [s, Apath] using
      sandwichedRenyiBeigiNormalizedInputPath_bddAbove_closedStrip hA α C
  have hBpath : BddAbove ((norm ∘ Bpath) '' s) := by
    simpa [s, Bpath] using
      sandwichedRenyiBeigiDualPath_bddAbove_closedStrip hB q
  have hSA : BddAbove ((norm ∘ fun w : ℂ => Spath w * Apath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hS hApath
  have hSAS : BddAbove ((norm ∘ fun w : ℂ => Spath w * Apath w * Spath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hSA hS
  have hK : BddAbove
      ((norm ∘ fun w : ℂ => MatrixMap.ofKraus K (Spath w * Apath w * Spath w)) ''
        s) :=
    bddAbove_norm_linearMap_of_bddAbove (MatrixMap.ofKraus K) hSAS
  have hTK : BddAbove
      ((norm ∘ fun w : ℂ => Tpath w *
        MatrixMap.ofKraus K (Spath w * Apath w * Spath w)) '' s) :=
    bddAbove_norm_mul_of_bddAbove hT hK
  have hTKT : BddAbove
      ((norm ∘ fun w : ℂ => Tpath w *
        MatrixMap.ofKraus K (Spath w * Apath w * Spath w) * Tpath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hTK hT
  have hPair : BddAbove
      ((norm ∘ fun w : ℂ =>
        (Tpath w * MatrixMap.ofKraus K (Spath w * Apath w * Spath w) *
          Tpath w) * Bpath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hTKT hBpath
  have hTrace : BddAbove
      ((norm ∘ fun w : ℂ =>
        (Matrix.traceLinearMap b ℂ ℂ)
          ((Tpath w * MatrixMap.ofKraus K (Spath w * Apath w * Spath w) *
            Tpath w) * Bpath w)) '' s) :=
    bddAbove_norm_linearMap_of_bddAbove (Matrix.traceLinearMap b ℂ ℂ) hPair
  simpa [s, Tpath, Spath, Apath, Bpath,
    sandwichedRenyiWeightedTraceFamily, sandwichedRenyiWeightedMapComplex,
    Matrix.mul_assoc] using hTrace

end BeigiClosedStripBoundedness

/-- Concrete left-boundary estimate for the normalized Beigi paths, reducing
the remaining endpoint work to the normalized input-path trace-norm bound.

All channel and reference-factor algebra is discharged here: the Kraus map is
used only through trace preservation, and the boundary complex powers are used
only through their contraction identities. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q C : ℝ)
    (hAtrace : ∀ z : ℂ, z.re = 0 →
      traceNorm (sandwichedRenyiBeigiNormalizedInputPath A hA α C z) ≤ C) :
    ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤ C := by
  intro z hzmem
  have hz : z.re = 0 := by simpa using hzmem
  have hS : Matrix.conjTranspose (cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
      cMatrixPosDefComplexPower σ.matrix hσ (-z) = 1 := by
    have hneg : (-z).re = 0 := by simp [hz]
    simpa using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hσ hneg
  have hT : Matrix.conjTranspose (cMatrixPosDefComplexPower τ.matrix hτ z) *
      cMatrixPosDefComplexPower τ.matrix hτ z = 1 := by
    simpa using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hτ hz
  have hBcontraction :
      Matrix.conjTranspose (sandwichedRenyiBeigiDualPath B hB q z) *
          sandwichedRenyiBeigiDualPath B hB q z ≤ 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (show star (sandwichedRenyiBeigiDualPath B hB q z) *
          sandwichedRenyiBeigiDualPath B hB q z ≤ 1 from by
        rw [sandwichedRenyiBeigiDualPath_star_mul_self_of_re_eq_zero hB q hz])
  exact sandwichedRenyiWeightedTraceFamily_left_bound_of_traceNorm
    σ hσ τ hτ K hTP
    (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
    (sandwichedRenyiBeigiDualPath B hB q) C z
    hS hT hBcontraction (hAtrace z hz)

/-- Fully discharged left-boundary estimate for the normalized Beigi paths.

This is the `p = 1` endpoint in the α > 1 Beigi interpolation spine, up to the
standard positivity of the normalizing Schatten value. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound_of_pos
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    {α q : ℝ} (hα : 0 < α)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef α) :
    ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef α))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef α := by
  exact sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound
    σ hσ τ hτ K hTP A hA B hB α q
    (psdSchattenPNorm A hA.posSemidef α)
    (fun z hz =>
      sandwichedRenyiBeigiNormalizedInputPath_traceNorm_le_of_re_eq_zero
        hA hα rfl hCpos hz)

/-- Right-boundary trace-family estimate from the weighted output
operator-contraction condition.

This isolates the remaining `p = ∞` Beigi endpoint: once the weighted output
matrix is in the operator unit ball after scaling by `C`, the dual path's
trace-norm unit-ball condition gives the scalar trace-family bound. -/
theorem sandwichedRenyiWeightedTraceFamily_right_bound_of_scaled_contraction
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    {C : ℝ} (hCpos : 0 < C) :
    (∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      Matrix.conjTranspose (((C : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)) *
        (((C : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)) ≤ 1) →
    (∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      traceNorm (Bpath z) ≤ 1) →
    ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤ C := by
  intro hW hB z hz
  let W : CMatrix b := sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)
  let Y : CMatrix b := Bpath z
  have hpair :=
    MatrixMap.abs_trace_mul_le_of_traceNorm_le_one_of_scaled_contraction
      Y W hCpos (by simpa [Y] using hB z hz) (by simpa [W] using hW z hz)
  simpa [sandwichedRenyiWeightedTraceFamily, W, Y, Complex.abs] using hpair

/-- Concrete normalized Beigi right-boundary handoff.

The theorem discharges the dual-path trace-norm endpoint from the `q`-unit-ball
hypothesis and leaves only the source-critical weighted-map operator
contraction as an assumption. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_right_bound_of_scaled_contraction
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    {α q : ℝ} (hCpos : 0 < psdSchattenPNorm A hA.posSemidef α)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    (hW : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      Matrix.conjTranspose (((psdSchattenPNorm A hA.posSemidef α : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef α) z)) *
        (((psdSchattenPNorm A hA.posSemidef α : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef α) z)) ≤ 1) :
    ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef α))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef α := by
  exact sandwichedRenyiWeightedTraceFamily_right_bound_of_scaled_contraction
    σ hσ τ hτ K
    (sandwichedRenyiBeigiNormalizedInputPath A hA α
      (psdSchattenPNorm A hA.posSemidef α))
    (sandwichedRenyiBeigiDualPath B hB q)
    hCpos hW
    (fun z hz =>
      sandwichedRenyiBeigiDualPath_traceNorm_le_one_of_re_eq_neg_half
        hB hBq (by simpa using hz))

/-- Heisenberg-adjoint boundary formula for the complex rotated Kraus family.

The adjoint of the complex-rotated family at the identity is the original
Kraus adjoint evaluated at `τ^(2 Re z)`, conjugated by the input reference
factor `σ^{-z}`. This is the algebraic core behind the interpolation endpoint
estimates. -/
theorem sandwichedRenyiRotatedKrausComplex_krausAdjoint_one
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (z : ℂ) :
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) (1 : CMatrix b) =
      star (cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
        MatrixMap.krausAdjoint K (CFC.rpow τ.matrix (2 * z.re)) *
          cMatrixPosDefComplexPower σ.matrix hσ (-z) := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hTpow : star T * T = CFC.rpow τ.matrix (2 * z.re) := by
    simpa [T] using cMatrixPosDefComplexPower_star_mul_self hτ z
  change MatrixMap.krausAdjoint (fun k => T * K k * S) (1 : CMatrix b) =
    star S * MatrixMap.krausAdjoint K (CFC.rpow τ.matrix (2 * z.re)) * S
  unfold MatrixMap.krausAdjoint
  have hterms :
      (∑ k,
        Matrix.conjTranspose (T * K k * S) * (1 : CMatrix b) *
          (T * K k * S)) =
      ∑ k,
        star S * (Matrix.conjTranspose (K k) *
          CFC.rpow τ.matrix (2 * z.re) * K k) * S := by
    apply Finset.sum_congr rfl
    intro k _
    have hTct : Matrix.conjTranspose T = star T := by
      rw [← Matrix.star_eq_conjTranspose]
    have hSct : Matrix.conjTranspose S = star S := by
      rw [← Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSct, hTct]
    calc
      (star S * (Matrix.conjTranspose (K k) * star T)) * (1 : CMatrix b) *
          (T * K k * S) =
          star S * Matrix.conjTranspose (K k) * (star T * T) * K k * S := by
            simp [Matrix.mul_assoc]
      _ = star S * Matrix.conjTranspose (K k) *
          CFC.rpow τ.matrix (2 * z.re) * K k * S := by
            rw [hTpow]
      _ = star S * (Matrix.conjTranspose (K k) *
          CFC.rpow τ.matrix (2 * z.re) * K k) * S := by
            simp [Matrix.mul_assoc]
  rw [hterms]
  simp [Matrix.mul_assoc, Finset.sum_mul, Finset.mul_sum]

/-- Schrödinger-side reference orbit for the complex rotated Kraus family.

If the original Kraus family sends the input reference state to `τ`, then the
complex-rotated family sends the reference power `σ^(1 + 2 Re z)` to
`τ^(1 + 2 Re z)`.  At the real interpolation point
`z = (1 - α)/(2α)`, this specializes to the `σ^(1/α) ↦ τ^(1/α)` endpoint.
-/
theorem sandwichedRenyiRotatedKrausComplex_apply_referencePower
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix) (z : ℂ) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
        (CFC.rpow σ.matrix (1 + 2 * z.re)) =
      CFC.rpow τ.matrix (1 + 2 * z.re) := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hSσ :
      S * CFC.rpow σ.matrix (1 + 2 * z.re) * star S = σ.matrix := by
    have h :=
      cMatrixPosDefComplexPower_mul_rpow_mul_star hσ (-z) (1 + 2 * z.re)
    have hexp : 1 + 2 * z.re + 2 * (-z).re = (1 : ℝ) := by
      simp
    rw [hexp] at h
    have hpow_one : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
      CFC.rpow_one σ.matrix
        (ha := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef)
    simpa [S] using h.trans hpow_one
  have hTτ :
      T * τ.matrix * star T = CFC.rpow τ.matrix (1 + 2 * z.re) := by
    have h := cMatrixPosDefComplexPower_mul_rpow_mul_star hτ z (1 : ℝ)
    have hpow_one : CFC.rpow τ.matrix (1 : ℝ) = τ.matrix :=
      CFC.rpow_one τ.matrix
        (ha := Matrix.nonneg_iff_posSemidef.mpr hτ.posSemidef)
    rw [hpow_one] at h
    simpa [T, add_comm] using h
  calc
    MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
        (CFC.rpow σ.matrix (1 + 2 * z.re)) =
        T * MatrixMap.ofKraus K
            (S * CFC.rpow σ.matrix (1 + 2 * z.re) * star S) * star T := by
          simpa [sandwichedRenyiRotatedKrausComplex, T, S] using
            MatrixMap.ofKraus_conjugated_apply K T S
              (CFC.rpow σ.matrix (1 + 2 * z.re))
    _ = T * MatrixMap.ofKraus K σ.matrix * star T := by rw [hSσ]
    _ = T * τ.matrix * star T := by rw [hτK]
    _ = CFC.rpow τ.matrix (1 + 2 * z.re) := hTτ

/-- On the imaginary boundary line, the complex rotated Kraus family remains
trace-preserving whenever the original Kraus family is trace-preserving.

This is one of the genuine Riesz-Thorin endpoint facts for the α > 1 route:
the reference complex powers are unitary on `Re z = 0`, so left and right
reference rotations do not change the Kraus completeness relation. -/
theorem sandwichedRenyiRotatedKrausComplex_isTracePreserving_of_re_eq_zero
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {z : ℂ} (hz : z.re = 0) :
    MatrixMap.IsTracePreserving
      (MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)) := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hTunit : star T * T = (1 : CMatrix b) := by
    simpa [T] using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hτ hz
  have hneg_re : (-z).re = 0 := by simp [hz]
  have hSunit : star S * S = (1 : CMatrix a) := by
    simpa [S] using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hσ hneg_re
  have hKone : MatrixMap.krausAdjoint K (1 : CMatrix b) = (1 : CMatrix a) :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  apply MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
  change MatrixMap.krausAdjoint (fun k => T * K k * S) (1 : CMatrix b) = 1
  calc
    MatrixMap.krausAdjoint (fun k => T * K k * S) (1 : CMatrix b) =
        star S * MatrixMap.krausAdjoint K (1 : CMatrix b) * S := by
          unfold MatrixMap.krausAdjoint
          have hterms :
              (∑ k,
                Matrix.conjTranspose (T * K k * S) * (1 : CMatrix b) *
                  (T * K k * S)) =
              ∑ k,
                star S * (Matrix.conjTranspose (K k) * (1 : CMatrix b) * K k) * S := by
            apply Finset.sum_congr rfl
            intro k _
            have hTct : Matrix.conjTranspose T = star T := by
              rw [← Matrix.star_eq_conjTranspose]
            have hSct : Matrix.conjTranspose S = star S := by
              rw [← Matrix.star_eq_conjTranspose]
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSct, hTct]
            calc
              (star S * (Matrix.conjTranspose (K k) * star T)) * (1 : CMatrix b) *
                  (T * K k * S) =
                  star S * Matrix.conjTranspose (K k) * (star T * T) * K k * S := by
                    simp [Matrix.mul_assoc]
              _ = star S * Matrix.conjTranspose (K k) * (1 : CMatrix b) * K k * S := by
                    rw [hTunit]
              _ = star S * (Matrix.conjTranspose (K k) * (1 : CMatrix b) * K k) * S := by
                    simp [Matrix.mul_assoc]
          rw [hterms]
          simp [Matrix.mul_assoc, Finset.sum_mul, Finset.mul_sum]
    _ = star S * 1 * S := by rw [hKone]
    _ = 1 := by simpa [Matrix.mul_assoc] using hSunit

/-- Trace-norm contraction on the `Re z = 0` endpoint of the Beigi weighted
interpolation family.

The previous lemma identifies this endpoint as trace-preserving; the general
finite-dimensional Kraus trace-norm contraction then gives the `p = 1`
endpoint. -/
theorem sandwichedRenyiRotatedKrausComplex_traceNorm_contract_of_re_eq_zero
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {z : ℂ} (hz : z.re = 0) (X : CMatrix a) :
    traceNorm
      (MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) X) ≤
      traceNorm X := by
  exact MatrixMap.traceNorm_contract_ofKraus_of_tracePreserving
    (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
    (sandwichedRenyiRotatedKrausComplex_isTracePreserving_of_re_eq_zero
      σ hσ τ hτ K hTP hz)
    X

/-- Unital endpoint for the local complex rotated family.

For the current convention `L_z = τ^z K σ^{-z}`, the Beigi `p = ∞` endpoint is
the vertical line `Re z = -1/2`: the reference orbit sends `σ^(1+2 Re z)` to
`τ^(1+2 Re z)`, hence sends `1` to `1` on that boundary. -/
theorem sandwichedRenyiRotatedKrausComplex_isUnital_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
      (1 : CMatrix a) = (1 : CMatrix b) := by
  have h :=
    sandwichedRenyiRotatedKrausComplex_apply_referencePower
      σ hσ τ hτ K hτK z
  have hexp : 1 + 2 * z.re = (0 : ℝ) := by
    rw [hz]
    ring
  have hσpow :
      CFC.rpow σ.matrix (1 + 2 * z.re) = (1 : CMatrix a) := by
    rw [hexp]
    exact CFC.rpow_zero σ.matrix
      (ha := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef)
  have hτpow :
      CFC.rpow τ.matrix (1 + 2 * z.re) = (1 : CMatrix b) := by
    rw [hexp]
    exact CFC.rpow_zero τ.matrix
      (ha := Matrix.nonneg_iff_posSemidef.mpr hτ.posSemidef)
  rwa [hσpow, hτpow] at h

open scoped Matrix.Norms.L2Operator in
/-- Operator-norm contraction on the `Re z = -1/2` endpoint of the local Beigi
interpolation family.

For the convention `L_z = τ^z K σ^{-z}`, this is the `p = ∞` boundary: the
previous lemma proves the endpoint map is unital, and finite-dimensional
Kadison-Schwarz gives contraction on the matrix unit ball. -/
theorem sandwichedRenyiRotatedKrausComplex_opNorm_contract_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ))
    {X : CMatrix a} (hX : Matrix.conjTranspose X * X ≤ 1) :
    ‖MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) X‖ ≤
      (1 : ℝ) := by
  exact MatrixMap.opNorm_contract_ofKraus_of_unital_on_unitBall
    (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
    (sandwichedRenyiRotatedKrausComplex_isUnital_of_re_eq_neg_half
      σ hσ τ hτ K hτK hz)
    hX

open scoped Matrix.Norms.L2Operator in
/-- Ordinary operator-norm contraction on the `Re z = -1/2` endpoint of the
local Beigi interpolation family. -/
theorem sandwichedRenyiRotatedKrausComplex_opNorm_contract_of_re_eq_neg_half'
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) (X : CMatrix a) :
    ‖MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) X‖ ≤
      ‖X‖ := by
  exact MatrixMap.opNorm_contract_ofKraus_of_unital
    (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
    (sandwichedRenyiRotatedKrausComplex_isUnital_of_re_eq_neg_half
      σ hσ τ hτ K hτK hz)
    X

open scoped Matrix.Norms.L2Operator in
/-- Beigi `p = ∞` endpoint for the normalized source-faithful weighted map,
stated as an operator-norm contraction.

The proof factors the analytic boundary map through the real `z = -1/2`
unital Kraus endpoint and imaginary reference rotations, all of which are
operator contractions. -/
theorem sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_opNorm_le_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    ‖((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)‖ ≤
      (1 : ℝ) := by
  let X0 : CMatrix a :=
    ((C : ℂ)⁻¹) • sandwichedRenyiBeigiNormalizedInputPath A hA α C z
  let u : ℂ := z + ((1 / 2 : ℝ) : ℂ)
  let Uτ : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ u
  let Uσ : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-u)
  let M : CMatrix b :=
    MatrixMap.ofKraus
      (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
        (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (Uσ * X0 * Uσ)
  have hu_re : u.re = 0 := by
    simp [u, hz]
  have hneg_u_re : (-u).re = 0 := by
    simp [hu_re]
  have hUτ : ‖Uτ‖ ≤ (1 : ℝ) :=
    MatrixMap.cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one Uτ
      (cMatrixPosDefComplexPower_contraction_of_re_eq_zero hτ hu_re)
  have hX0 :
      Matrix.conjTranspose X0 * X0 ≤ (1 : CMatrix a) := by
    simpa [X0] using
      sandwichedRenyiBeigiNormalizedInputPath_scaled_contraction_of_re_eq_neg_half
        hA α C hCpos hz
  have hV :
      Matrix.conjTranspose (Uσ * X0 * Uσ) * (Uσ * X0 * Uσ) ≤
        (1 : CMatrix a) :=
    cMatrixPosDefComplexPower_mul_mul_contraction_of_re_eq_zero
      hσ hneg_u_re hX0
  have hz0 : (((( -(1 / 2 : ℝ)) : ℝ) : ℂ)).re = -(1 / 2 : ℝ) := by
    norm_num
  have hMnorm : ‖M‖ ≤ (1 : ℝ) := by
    simpa [M] using
      sandwichedRenyiRotatedKrausComplex_opNorm_contract_of_re_eq_neg_half
        σ hσ τ hτ K hτK hz0 hV
  have hlinear :
      ((C : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
            (sandwichedRenyiBeigiNormalizedInputPath A hA α C z) =
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X0 := by
    simp [X0]
  have hfactor :
      sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X0 =
        Uτ * M * Uτ := by
    simpa [u, Uτ, Uσ, M] using
      sandwichedRenyiWeightedMapComplex_eq_imaginary_conj_of_re_eq_neg_half
        σ hσ τ hτ K z X0
  calc
    ‖((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)‖ =
        ‖sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X0‖ := by
          rw [hlinear]
    _ = ‖Uτ * M * Uτ‖ := by rw [hfactor]
    _ ≤ ‖Uτ‖ * (‖M‖ * ‖Uτ‖) := by
          calc
            ‖Uτ * M * Uτ‖ ≤ ‖Uτ * M‖ * ‖Uτ‖ := norm_mul_le _ _
            _ ≤ (‖Uτ‖ * ‖M‖) * ‖Uτ‖ := by
                  exact mul_le_mul_of_nonneg_right (norm_mul_le Uτ M) (norm_nonneg Uτ)
            _ = ‖Uτ‖ * (‖M‖ * ‖Uτ‖) := by ring
    _ ≤ (1 : ℝ) := by
          have hMU : ‖M‖ * ‖Uτ‖ ≤ (1 : ℝ) * (1 : ℝ) :=
            mul_le_mul hMnorm hUτ (norm_nonneg Uτ) zero_le_one
          have hprod : ‖Uτ‖ * (‖M‖ * ‖Uτ‖) ≤ (1 : ℝ) * (1 : ℝ) :=
            mul_le_mul hUτ (by simpa using hMU)
              (mul_nonneg (norm_nonneg M) (norm_nonneg Uτ)) zero_le_one
          simpa using hprod

/-- Beigi `p = ∞` endpoint in the matrix unit-ball form used by the local
trace-norm variational handoff. -/
theorem sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_contraction_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    Matrix.conjTranspose (((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)) *
      (((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)) ≤ 1 := by
  exact MatrixMap.cMatrix_conjTranspose_mul_self_le_one_of_l2OperatorNorm_le_one _
    (sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_opNorm_le_of_re_eq_neg_half
      σ hσ τ hτ K hτK hA α C hCpos hz)

/-- Beigi-strip three-lines handoff for the rotated Kraus trace pairing.

This is the remaining interpolation bridge after the endpoint contractions are
available.  It does not assume the target DPI or q-ball contraction: it says
that any source-faithful scalar family on the local strip, whose middle point
is the rotated-Kraus trace pairing and whose two boundary lines are bounded by
the candidate PSD Schatten norm, gives the required trace-pairing bound. -/
theorem sandwichedRenyi_tracePairingBound_of_beigiInterpolationFamily
    (σ : State a) (_hσ : σ.matrix.PosDef)
    (τ : State b) (_hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (_hB : B.PosSemidef)
    (f : ℂ → ℂ)
    (hCpos : 0 < psdSchattenPNorm A hA α)
    (hd : DiffContOnCl ℂ (fun w : ℂ => f (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hBounded : BddAbove ((norm ∘ (fun w : ℂ => f (-(w / 2)))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖f z‖ ≤ psdSchattenPNorm A hA α)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖f z‖ ≤ psdSchattenPNorm A hA α)
    (htarget :
      f (-(((1 / q : ℝ) : ℂ) / 2)) =
        ((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA α := by
  have hθ := holderConjugate_inv_right_mem_unit_interval hpq
  have hnorm :
      ‖f (-(((1 / q : ℝ) : ℂ) / 2))‖ ≤ psdSchattenPNorm A hA α :=
    complex_three_lines_const_bound_neg_half_strip
      (f := f) (θ := 1 / q) (C := psdSchattenPNorm A hA α)
      hθ.1 hθ.2 hCpos hd hBounded hleft hright
  calc
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re =
        (f (-(((1 / q : ℝ) : ℂ) / 2))).re := by
          rw [htarget]
    _ ≤ ‖f (-(((1 / q : ℝ) : ℂ) / 2))‖ := Complex.re_le_norm _
    _ ≤ psdSchattenPNorm A hA α := hnorm

/-- Source-faithful Beigi weighted-map version of the three-lines handoff.

This removes the remaining target-equality bookkeeping from the interpolation
step: once the weighted trace family has analytic control and endpoint bounds,
it yields the trace-pairing bound needed for the rotated-adjoint q-ball
contraction. -/
theorem sandwichedRenyi_tracePairingBound_of_weightedInterpolationFamily
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (hB : B.PosSemidef)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (hAθ : Apath (-(((1 / q : ℝ) : ℂ) / 2)) = A)
    (hBθ : Bpath (-(((1 / q : ℝ) : ℂ) / 2)) = B)
    (hCpos : 0 < psdSchattenPNorm A hA α)
    (hd : DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤
        psdSchattenPNorm A hA α)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤
        psdSchattenPNorm A hA α) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA α := by
  exact sandwichedRenyi_tracePairingBound_of_beigiInterpolationFamily
    σ hσ τ hτ K α q hpq hA hB
    (sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath)
    hCpos hd hBounded hleft hright
    (sandwichedRenyiWeightedTraceFamily_holderTheta_target
      σ hσ τ hτ K α q hpq Apath Bpath A B hAθ hBθ)

/-- Concrete Beigi-path handoff from endpoint estimates to the trace-pairing
bound.

This theorem fixes the source-faithful analytic paths
`A_z = A^(2αz+α)` and `B_z = B^(-2qz)`, proves their analytic condition and
target-point identities internally, and leaves only the genuine endpoint
boundedness estimates as assumptions. -/
theorem sandwichedRenyi_tracePairingBound_of_beigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef α)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiInputPath A hA α)
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiInputPath A hA α)
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef α)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiInputPath A hA α)
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef α) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef α := by
  exact sandwichedRenyi_tracePairingBound_of_weightedInterpolationFamily
    σ hσ τ hτ K α q hpq hA.posSemidef hB.posSemidef
    (sandwichedRenyiBeigiInputPath A hA α)
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiInputPath_holderTheta hA hpq)
    (sandwichedRenyiBeigiDualPath_holderTheta hB hpq)
    hCpos
    (sandwichedRenyiWeightedTraceFamily_diffContOnCl_beigiPaths
      σ hσ τ hτ K A hA B hB α q)
    hBounded hleft hright

/-- Normalized concrete Beigi-path handoff from endpoint estimates to the
trace-pairing bound.

Compared with `sandwichedRenyi_tracePairingBound_of_beigiPaths`, the input path
is scaled by the Schatten `α`-norm of `A`.  This is the source-faithful
normalization used in the Beigi weighted-`L_p` proof: the lower endpoint is
bounded by `||A||_α` rather than by `Tr(A^α)`. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef α)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef α))
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef α))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef α)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef α))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef α) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef α := by
  exact sandwichedRenyi_tracePairingBound_of_weightedInterpolationFamily
    σ hσ τ hτ K α q hpq hA.posSemidef hB.posSemidef
    (sandwichedRenyiBeigiNormalizedInputPath A hA α
      (psdSchattenPNorm A hA.posSemidef α))
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiNormalizedInputPath_holderTheta hA hpq)
    (sandwichedRenyiBeigiDualPath_holderTheta hB hpq)
    hCpos
    (sandwichedRenyiWeightedTraceFamily_diffContOnCl_normalizedBeigiPaths
      σ hσ τ hτ K A hA B hB α q (psdSchattenPNorm A hA.posSemidef α))
    hBounded hleft hright

/-- Normalized Beigi trace-pairing bound from the two endpoint estimates, with
the `p = ∞` endpoint isolated as the weighted-map scaled-contraction theorem.

This is the source-aligned bridge immediately before the final
Riesz-Thorin/Beigi contraction step: it discharges analyticity and the complete
`p = 1` boundary, and it discharges the dual-path part of the `p = ∞`
boundary from the `q`-unit-ball hypothesis. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigi_weightedEndpoint
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef α)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef α))
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hWeightedEndpoint :
      ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
        Matrix.conjTranspose (((psdSchattenPNorm A hA.posSemidef α : ℂ)⁻¹) •
            sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
              (sandwichedRenyiBeigiNormalizedInputPath A hA α
                (psdSchattenPNorm A hA.posSemidef α) z)) *
          (((psdSchattenPNorm A hA.posSemidef α : ℂ)⁻¹) •
            sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
              (sandwichedRenyiBeigiNormalizedInputPath A hA α
                (psdSchattenPNorm A hA.posSemidef α) z)) ≤ 1) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef α := by
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigiPaths
    σ hσ τ hτ K α q hpq hA hB hCpos hBounded
    (sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound_of_pos
      σ hσ τ hτ K hTP A hA B hB hpq.pos hCpos)
    (sandwichedRenyiWeightedTraceFamily_normalizedBeigi_right_bound_of_scaled_contraction
      σ hσ τ hτ K A hA B hB hCpos hBq hWeightedEndpoint)

/-- Normalized Beigi trace-pairing bound with the `p = ∞` weighted endpoint
fully discharged.

The only remaining analytic side condition is the standard closed-strip
boundedness hypothesis required by the local Hadamard three-lines theorem. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigi
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef α)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef α))
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef α := by
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigi_weightedEndpoint
    σ hσ τ hτ K hTP α q hpq hA hB hCpos hBq hBounded
    (fun z hz =>
      sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_contraction_of_re_eq_neg_half
        σ hσ τ hτ K hτK hA α
        (psdSchattenPNorm A hA.posSemidef α) hCpos
        (by simpa using hz))

/-- Normalized Beigi trace-pairing bound with all endpoint and closed-strip
analytic side conditions discharged.

This is the source-faithful α > 1 interpolation trace-pairing theorem in the
current full-rank/PosDef domain. It no longer assumes the target DPI, the
rotated-adjoint `q`-ball contraction, or an external boundedness hypothesis. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigi_closedStrip
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef α)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef α := by
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigi
    σ hσ τ hτ K hTP hτK α q hpq hA hB hCpos hBq
    (sandwichedRenyiWeightedTraceFamily_normalizedBeigi_bddAbove_closedStrip
      σ hσ τ hτ K A hA B hB α q (psdSchattenPNorm A hA.posSemidef α))

/-- Channel-specialized positive-definite Beigi trace-pairing bound.

For a Kraus realization of a channel and a full-rank input reference whose
output reference is also full-rank, the source-faithful Beigi weighted-map
interpolation proves the trace-pairing bound for positive-definite input and
output witnesses. The remaining gap to the full rotated-adjoint `q`-ball
theorem is the PSD closure/regularization from positive-definite witnesses to
all positive semidefinite witnesses. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef α := by
  haveI : Nonempty a := σ.nonempty
  have hCpos : 0 < psdSchattenPNorm A hA.posSemidef α :=
    psdSchattenPNorm_pos_of_posDef hA
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hτK : MatrixMap.ofKraus K σ.matrix = (Φ.applyState σ).matrix := by
    rw [← hK]
    rfl
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigi_closedStrip
    σ hσ (Φ.applyState σ) hσΦ K hTP hτK α q hpq
    hA hB hCpos hBq

omit [Fintype a] in
private theorem cMatrix_real_smul_one_posDef_local {r : ℝ} (hr : 0 < r) :
    (r • (1 : CMatrix a)).PosDef := by
  rw [show r • (1 : CMatrix a) = Matrix.diagonal (fun _ : a => (r : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hr

omit [Fintype a] in
private theorem cMatrix_le_add_pos_smul_one {A : CMatrix a}
    {ε : ℝ} (hε : 0 < ε) :
    A ≤ A + ε • (1 : CMatrix a) := by
  rw [Matrix.le_iff]
  have hpos : (ε • (1 : CMatrix a)).PosSemidef :=
    (cMatrix_real_smul_one_posDef_local (a := a) hε).posSemidef
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpos

omit [Fintype a] in
theorem cMatrix_posSemidef_add_pos_smul_one_posDef {A : CMatrix a}
    (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + ε • (1 : CMatrix a)).PosDef :=
  Matrix.PosDef.posSemidef_add hA
    (cMatrix_real_smul_one_posDef_local (a := a) hε)

/-- The maximally mixed state is full-rank on a nonempty finite system. -/
theorem maximallyMixed_posDef_of_nonempty [Nonempty a] :
    (maximallyMixed a).matrix.PosDef := by
  rw [maximallyMixed_matrix]
  exact cMatrix_real_smul_one_posDef_local (a := a)
    (r := (Fintype.card a : ℝ)⁻¹) (by
      exact inv_pos.mpr (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card a)))

/-- The first marginal of white noise on a product system is white noise. -/
theorem maximallyMixed_marginalA
    [Nonempty a] [Nonempty b] :
    (maximallyMixed (Prod a b)).marginalA = maximallyMixed a := by
  apply State.ext
  ext i j
  simp [State.marginalA, partialTraceB, maximallyMixed_matrix, Matrix.one_apply]

/-- The first marginal of white noise on a product system is full-rank. -/
theorem maximallyMixed_marginalA_posDef
    [Nonempty a] [Nonempty b] :
    ((maximallyMixed (Prod a b)).marginalA).matrix.PosDef := by
  simpa [maximallyMixed_marginalA] using
    maximallyMixed_posDef_of_nonempty (a := a)

/-- Affine regularization of a state matrix by a fixed noise state. -/
def regularizedStateMatrix (ρ ω : State a) (ε : ℝ) : CMatrix a :=
  (((1 - ε : ℝ) : ℂ) • ρ.matrix) + (((ε : ℝ) : ℂ) • ω.matrix)

/-- The affine regularization matrix is a normalized state when
`0 ≤ ε ≤ 1`. -/
def regularizedWithState (ρ ω : State a) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : State a where
  matrix := regularizedStateMatrix ρ ω ε
  pos := by
    unfold regularizedStateMatrix
    have hleft : (0 : ℂ) ≤ ((1 - ε : ℝ) : ℂ) := by
      exact_mod_cast sub_nonneg.mpr hε1
    have hright : (0 : ℂ) ≤ ((ε : ℝ) : ℂ) := by
      exact_mod_cast hε0
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul ρ.pos hleft)
      (Matrix.PosSemidef.smul ω.pos hright)
  trace_eq_one := by
    unfold regularizedStateMatrix
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      ρ.trace_eq_one, ω.trace_eq_one]
    norm_num

@[simp]
theorem regularizedWithState_matrix (ρ ω : State a) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (regularizedWithState ρ ω ε hε0 hε1).matrix =
      regularizedStateMatrix ρ ω ε :=
  rfl

/-- Mixing any state with positive weight of a full-rank noise state gives a
full-rank state. -/
theorem regularizedWithState_posDef_of_noise
    (ρ ω : State a) (hω : ω.matrix.PosDef) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hεpos : 0 < ε) :
    (regularizedWithState ρ ω ε hε0 hε1).matrix.PosDef := by
  unfold regularizedWithState regularizedStateMatrix
  have hleft : (0 : ℂ) ≤ ((1 - ε : ℝ) : ℂ) := by
    exact_mod_cast sub_nonneg.mpr hε1
  have hright : (0 : ℂ) < ((ε : ℝ) : ℂ) := by
    exact_mod_cast hεpos
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.pos hleft)
    (Matrix.PosDef.smul hω hright)

/-- The regularized matrix path tends back to the original state matrix as the
mixing parameter tends to zero from inside the probability interval. -/
theorem regularizedStateMatrix_tendsto_zero (ρ ω : State a) :
    Filter.Tendsto (fun ε : ℝ => regularizedStateMatrix ρ ω ε)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.matrix) := by
  have hcont : Continuous fun ε : ℝ => regularizedStateMatrix ρ ω ε := by
    unfold regularizedStateMatrix
    fun_prop
  have h0 : regularizedStateMatrix ρ ω 0 = ρ.matrix := by
    simp [regularizedStateMatrix]
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- Partial trace of an affine state regularization is the affine
regularization of the marginals. -/
theorem regularizedStateMatrix_marginalA
    (ρ ω : State (Prod a b)) (ε : ℝ) :
    partialTraceB (a := a) (b := b) (regularizedStateMatrix ρ ω ε) =
      regularizedStateMatrix ρ.marginalA ω.marginalA ε := by
  unfold regularizedStateMatrix
  rw [partialTraceB_add, partialTraceB_smul, partialTraceB_smul]
  simp [State.marginalA_matrix]

/-- The marginal of a regularized bipartite state tends to the original
marginal as the regularization weight tends to zero. -/
theorem regularizedStateMatrix_marginalA_tendsto_zero
    (ρ ω : State (Prod a b)) :
    Filter.Tendsto
      (fun ε : ℝ => partialTraceB (a := a) (b := b)
        (regularizedStateMatrix ρ ω ε))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.marginalA.matrix) := by
  have h :=
    regularizedStateMatrix_tendsto_zero ρ.marginalA ω.marginalA
  simpa [regularizedStateMatrix_marginalA] using h

/-- Positive-definite regularization of a Stinespring lift by full-rank white
noise on the enlarged output-environment system. -/
def regularizedStinespringLiftState {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    State (Prod b κ) :=
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  regularizedWithState
    (stinespringLiftState K hTP ρ)
    (maximallyMixed (Prod b κ)) ε hε0 hε1

/-- The regularized Stinespring lift is full-rank for positive regularization
weight. -/
theorem regularizedStinespringLiftState_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεpos : 0 < ε) :
    (regularizedStinespringLiftState K hTP ρ ε hε0 hε1).matrix.PosDef := by
  unfold regularizedStinespringLiftState
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  exact regularizedWithState_posDef_of_noise
    (stinespringLiftState K hTP ρ) (maximallyMixed (Prod b κ))
    maximallyMixed_posDef_of_nonempty hε0 hε1 hεpos

/-- The regularized Stinespring lift converges back to the generally singular
Stinespring lift as the regularization weight tends to zero. -/
theorem regularizedStinespringLiftState_matrix_tendsto
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    Filter.Tendsto
      (fun ε : ℝ =>
        regularizedStateMatrix
          (stinespringLiftState K hTP ρ)
          (letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
           maximallyMixed (Prod b κ)) ε)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (stinespringLiftState K hTP ρ).matrix) := by
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  exact regularizedStateMatrix_tendsto_zero
    (stinespringLiftState K hTP ρ) (maximallyMixed (Prod b κ))

/-- Matrix form of the marginal of the regularized Stinespring lift. -/
theorem regularizedStinespringLiftState_marginalA_matrix
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ((regularizedStinespringLiftState K hTP ρ ε hε0 hε1).marginalA).matrix =
      regularizedStateMatrix
        (stinespringLiftState K hTP ρ).marginalA
        ((letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
          maximallyMixed (Prod b κ)).marginalA) ε := by
  unfold regularizedStinespringLiftState
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  simpa [regularizedWithState_matrix] using
    regularizedStateMatrix_marginalA
      (stinespringLiftState K hTP ρ)
      (maximallyMixed (Prod b κ)) ε

/-- The marginal of the regularized Stinespring lift is the same affine
regularization of the channel output by the environment-noise marginal. -/
theorem regularizedStinespringLiftState_marginalA_eq_regularized_applyState
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (Φ : Channel a b)
    (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (regularizedStinespringLiftState K hTP ρ ε hε0 hε1).marginalA =
      regularizedWithState (Φ.applyState ρ)
        ((letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
          maximallyMixed (Prod b κ)).marginalA) ε hε0 hε1 := by
  apply State.ext
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  rw [regularizedStinespringLiftState_marginalA_matrix]
  have hmargin := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP ρ
  rw [hmargin]
  rfl

/-- The output marginal of the regularized Stinespring lift is full-rank for
positive regularization weight. -/
theorem regularizedStinespringLiftState_marginalA_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεpos : 0 < ε) :
    ((regularizedStinespringLiftState K hTP ρ ε hε0 hε1).marginalA).matrix.PosDef := by
  let hprod : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  letI : Nonempty (Prod b κ) := hprod
  letI : Nonempty b := ⟨(Classical.choice hprod).1⟩
  letI : Nonempty κ := ⟨(Classical.choice hprod).2⟩
  rw [regularizedStinespringLiftState_marginalA_matrix]
  have hnoise :
      ((maximallyMixed (Prod b κ)).marginalA).matrix.PosDef :=
    maximallyMixed_marginalA_posDef (a := b) (b := κ)
  have h :=
    regularizedWithState_posDef_of_noise
      (stinespringLiftState K hTP ρ).marginalA
      ((maximallyMixed (Prod b κ)).marginalA)
      hnoise hε0 hε1 hεpos
  simpa [regularizedWithState_matrix] using h

/-- The output marginal of the regularized Stinespring lift tends back to the
Kraus-channel output as the regularization weight tends to zero. -/
theorem regularizedStinespringLiftState_marginalA_matrix_tendsto
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    Filter.Tendsto
      (fun ε : ℝ =>
        partialTraceB (a := b) (b := κ)
          (regularizedStateMatrix
            (stinespringLiftState K hTP ρ)
            (letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
             maximallyMixed (Prod b κ)) ε))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (MatrixMap.ofKraus K ρ.matrix)) := by
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  have h :=
    regularizedStateMatrix_marginalA_tendsto_zero
      (stinespringLiftState K hTP ρ) (maximallyMixed (Prod b κ))
  have hpt :
      partialTraceB (a := b) (b := κ) (stinespringLiftState K hTP ρ).matrix =
        MatrixMap.ofKraus K ρ.matrix := by
    simpa [State.marginalA_matrix] using
      stinespringLiftState_marginalA_matrix K hTP ρ
  simpa [hpt] using h

/-- Positive-definite Beigi trace-pairing bound applied to a regularized PSD
input witness.

For arbitrary PSD input test `A`, the source-faithful positive-definite
interpolation theorem controls the trace pairing after replacing `A` by
`A + ε I`.  This is the concrete regularization bridge needed before the final
PSD closure/continuity step in the α > 1 rotated-adjoint `q`-ball proof. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInput
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (hB : B.PosDef)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm (A + ε • (1 : CMatrix a))
        (cMatrix_posSemidef_add_pos_smul_one_posDef hA hε).posSemidef α := by
  let L : κ → Matrix b a ℂ :=
    sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α
  let Aε : CMatrix a := A + ε • (1 : CMatrix a)
  have hAε : Aε.PosDef := by
    simpa [Aε] using cMatrix_posSemidef_add_pos_smul_one_posDef hA hε
  have hA_le : A ≤ Aε := by
    simpa [Aε] using cMatrix_le_add_pos_smul_one (a := a) (A := A) hε
  have hTA_le : MatrixMap.ofKraus L A ≤ MatrixMap.ofKraus L Aε := by
    rw [Matrix.le_iff] at hA_le ⊢
    have hpos :
        (MatrixMap.ofKraus L (Aε - A)).PosSemidef :=
      MatrixMap.ofKraus_mapsPositive L (Aε - A) hA_le
    simpa [map_sub] using hpos
  have htrace_order :
      (((MatrixMap.ofKraus L A) * B).trace).re ≤
        (((MatrixMap.ofKraus L Aε) * B).trace).re := by
    have hcomm_left :
        (((MatrixMap.ofKraus L A) * B).trace).re =
          ((B * MatrixMap.ofKraus L A).trace).re := by
      rw [Matrix.trace_mul_comm]
    have hcomm_right :
        (((MatrixMap.ofKraus L Aε) * B).trace).re =
          ((B * MatrixMap.ofKraus L Aε).trace).re := by
      rw [Matrix.trace_mul_comm]
    rw [hcomm_left, hcomm_right]
    exact cMatrix_trace_mul_le_of_le_posSemidef_left (W := B)
      (A := MatrixMap.ofKraus L A)
      (B := MatrixMap.ofKraus L Aε) hB.posSemidef hTA_le
  have hbeigi :
      (((MatrixMap.ofKraus
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) Aε) *
          B).trace).re ≤
        psdSchattenPNorm Aε hAε.posSemidef α := by
    simpa [L, Aε] using
      sandwichedRenyiRotatedKraus_tracePairingBound_of_posDef
        K σ Φ hK hσ hσΦ α q hpq hAε hB hBq
  exact htrace_order.trans (by simpa [L, Aε] using hbeigi)

/-- Beigi trace-pairing bound for regularized input and normalized regularized
output witnesses.

Starting from arbitrary PSD test matrices `A` and `B`, this theorem replaces
`A` by `A + ε I`, replaces `B` by `B + δ I`, normalizes the latter into the
positive `q`-unit sphere, and then applies the source-faithful positive-definite
Beigi interpolation theorem.  The remaining step to the full PSD handoff is the
limit as `ε, δ → 0`. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInputOutput
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef)
    {B : CMatrix b} (hB : B.PosSemidef)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    let Bδ : CMatrix b := B + δ • (1 : CMatrix b)
    let scale : ℝ := (psdTracePower Bδ
      (cMatrix_posSemidef_add_pos_smul_one_posDef hB hδ).posSemidef q) ^ (-(1 / q))
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        (scale • Bδ : CMatrix b)).trace).re ≤
      psdSchattenPNorm (A + ε • (1 : CMatrix a))
        (cMatrix_posSemidef_add_pos_smul_one_posDef hA hε).posSemidef α := by
  haveI : Nonempty b := (Φ.applyState σ).nonempty
  intro Bδ scale
  have hBδ : Bδ.PosDef := by
    simpa [Bδ] using cMatrix_posSemidef_add_pos_smul_one_posDef hB hδ
  have hSpos :
      0 < psdTracePower Bδ hBδ.posSemidef q := by
    exact psdTracePower_pos_of_ne_zero Bδ hBδ.posSemidef (by
      intro hzero
      have htr : (0 : ℂ) < Bδ.trace := Matrix.PosDef.trace_pos hBδ
      rw [hzero] at htr
      simp at htr)
  have hscale_pos : 0 < scale := by
    exact Real.rpow_pos_of_pos hSpos (-(1 / q))
  have hscale_nonneg : 0 ≤ scale := le_of_lt hscale_pos
  have hscaledB : (scale • Bδ : CMatrix b).PosDef :=
    Matrix.PosDef.smul hBδ hscale_pos
  have hscaledBq :
      psdTracePower (scale • Bδ : CMatrix b) hscaledB.posSemidef q ≤ 1 := by
    have heq :=
      psdTracePower_normalized_real_smul_eq_one_of_posDef hBδ hpq.symm.pos
    exact le_of_eq (by
      simpa [scale] using heq)
  exact
    sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInput
      K σ Φ hK hσ hσΦ α q hpq hA hscaledB hscaledBq hε

/-- PSD `q`-sphere trace-pairing bound obtained by closing the positive-definite
Beigi interpolation theorem under input/output identity regularization.

This removes the positive-definite witness assumption from
`sandwichedRenyiRotatedKraus_tracePairingBound_of_posDef` for the normalized
output `q`-sphere. It is the first nontrivial PSD closure step toward the full
rotated-adjoint `q`-ball contraction. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q = 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm A hA α := by
  let L : κ → Matrix b a ℂ :=
    sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α
  let TA : CMatrix b := MatrixMap.ofKraus L A
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hδlimit : Filter.Tendsto
      (fun δ : ℝ =>
        let Bδ : CMatrix b := B + δ • (1 : CMatrix b)
        let scale : ℝ := ((CFC.rpow Bδ q).trace.re) ^ (-(1 / q))
        ((TA * (scale • Bδ : CMatrix b)).trace).re)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((TA * B).trace.re)) := by
    have hBnorm :=
      cMatrix_normalized_regularized_tendsto_of_psdTracePower_eq_one
        hB hpq.symm.pos hBq
    have hcont : Continuous fun M : CMatrix b => ((TA * M).trace).re := by
      fun_prop
    exact hcont.tendsto B |>.comp hBnorm
  have hleft_le_regularizedInput
      {ε : ℝ} (hε : 0 < ε) :
      ((TA * B).trace).re ≤
        psdSchattenPNorm (A + ε • (1 : CMatrix a))
          (cMatrix_posSemidef_add_pos_smul_one_posDef hA hε).posSemidef α := by
    exact le_of_tendsto hδlimit (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hreg :=
        sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInputOutput
          K σ Φ hK hσ hσΦ α q hpq hA hB hε hδ
      simpa [L, TA, psdTracePower] using hreg)
  have hRtrace :=
    cMatrix_rpow_trace_re_tendsto_add_pos_smul_one hA hα_pos
  have hR : Filter.Tendsto
      (fun ε : ℝ =>
        ((CFC.rpow (A + ε • (1 : CMatrix a)) α).trace.re) ^ (1 / α))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (psdSchattenPNorm A hA α)) := by
    have hcont : ContinuousAt
        (fun x : ℝ => x ^ (1 / α))
        ((CFC.rpow A α).trace.re) :=
      Real.continuousAt_rpow_const
        ((CFC.rpow A α).trace.re) (1 / α)
        (Or.inr (le_of_lt (one_div_pos.mpr hα_pos)))
    have h := hcont.tendsto.comp hRtrace
    simpa [psdSchattenPNorm, psdTracePower] using h
  exact ge_of_tendsto hR (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h := hleft_le_regularizedInput hε
    simpa [psdSchattenPNorm, psdTracePower] using h)

/-- PSD `q`-ball trace-pairing bound for the Beigi weighted rotated Kraus map.

The `q`-sphere result gives the bound for normalized output witnesses. A
nonzero witness in the `q`-unit ball is scaled up to the `q`-sphere; PSD
monotonicity of the trace pairing then returns the original witness. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_le_one
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm A hA α := by
  classical
  let L : κ → Matrix b a ℂ :=
    sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α
  let TA : CMatrix b := MatrixMap.ofKraus L A
  by_cases hBzero : B = 0
  · have htrace_zero : ((TA * B).trace).re = 0 := by
      simp [hBzero]
    rw [htrace_zero]
    exact psdSchattenPNorm_nonneg A hA α
  · let scale : ℝ := (psdTracePower B hB q) ^ (-(1 / q))
    let Bn : CMatrix b := scale • B
    have hq_pos : 0 < q := hpq.symm.pos
    have hSpos : 0 < psdTracePower B hB q :=
      psdTracePower_pos_of_ne_zero B hB hBzero
    have hscale_nonneg : 0 ≤ scale := by
      exact Real.rpow_nonneg (le_of_lt hSpos) (-(1 / q))
    have hBn : Bn.PosSemidef := by
      simpa [Bn] using Matrix.PosSemidef.smul hB hscale_nonneg
    have hBnq : psdTracePower Bn hBn q = 1 := by
      simpa [scale, Bn] using
        psdTracePower_normalized_real_smul_eq_one_of_ne_zero hB hBzero hq_pos
    have hbound_Bn :
        ((TA * Bn).trace).re ≤ psdSchattenPNorm A hA α := by
      simpa [L, TA, Bn] using
        sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_eq_one
          K σ Φ hK hσ hσΦ α q hα_gt_one hpq hA hBn hBnq
    have hscale_ge_one : 1 ≤ scale := by
      have hSle : psdTracePower B hB q ≤ 1 := hBq
      have hnonpos : -(1 / q) ≤ 0 := by
        exact neg_nonpos.mpr (one_div_nonneg.mpr (le_of_lt hq_pos))
      simpa [scale] using
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hSpos hSle hnonpos
    have hB_le_Bn : B ≤ Bn := by
      rw [Matrix.le_iff]
      have hdiff : (Bn - B).PosSemidef := by
        have hcoeff : 0 ≤ scale - 1 := sub_nonneg.mpr hscale_ge_one
        have hscaled : ((scale - 1) • B : CMatrix b).PosSemidef :=
          Matrix.PosSemidef.smul hB hcoeff
        have hdiff_eq : Bn - B = (scale - 1) • B := by
          calc
            Bn - B = scale • B - (1 : ℝ) • B := by
              simp [Bn]
            _ = (scale - 1) • B := by
              rw [← sub_smul]
        simpa [hdiff_eq] using hscaled
      simpa [sub_eq_add_neg] using hdiff
    have hTA : TA.PosSemidef := by
      simpa [TA] using MatrixMap.ofKraus_mapsPositive L A hA
    have htrace_le :
        ((TA * B).trace).re ≤ ((TA * Bn).trace).re :=
      cMatrix_trace_mul_le_of_le_posSemidef_left (W := TA) (A := B) (B := Bn) hTA hB_le_Bn
    exact htrace_le.trans hbound_Bn

/-- The sandwiched inner operator of a state with itself is the reference
power `σ^(1/α)` in the full-rank domain.

This algebraic identity is one endpoint needed for the α > 1 interpolation
route. -/
theorem sandwichedRenyiInner_self_eq_rpow
    (σ : State a) (hσ : σ.matrix.PosDef) (α : ℝ) (hα_ne_zero : α ≠ 0) :
    sandwichedRenyiInner σ σ α = CFC.rpow σ.matrix (1 / α) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hnonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hpow_one : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
    CFC.rpow_one σ.matrix (ha := hnonneg)
  have hs_left :
      CFC.rpow σ.matrix s * σ.matrix = CFC.rpow σ.matrix (s + 1) := by
    calc
      CFC.rpow σ.matrix s * σ.matrix =
          CFC.rpow σ.matrix s * CFC.rpow σ.matrix (1 : ℝ) := by
            rw [hpow_one]
      _ = CFC.rpow σ.matrix (s + 1) := by
            exact (CFC.rpow_add (a := σ.matrix) (x := s) (y := 1) hσ.isUnit).symm
  have hs_total :
      CFC.rpow σ.matrix (s + 1) * CFC.rpow σ.matrix s =
        CFC.rpow σ.matrix ((s + 1) + s) := by
    exact (CFC.rpow_add (a := σ.matrix) (x := s + 1) (y := s) hσ.isUnit).symm
  have hexp : (s + 1) + s = 1 / α := by
    dsimp [s]
    field_simp [hα_ne_zero]
    ring
  unfold sandwichedRenyiInner
  change CFC.rpow σ.matrix s * σ.matrix * CFC.rpow σ.matrix s =
    CFC.rpow σ.matrix (1 / α)
  calc
    CFC.rpow σ.matrix s * σ.matrix * CFC.rpow σ.matrix s =
        (CFC.rpow σ.matrix s * σ.matrix) * CFC.rpow σ.matrix s := by
          rw [Matrix.mul_assoc]
    _ = CFC.rpow σ.matrix (s + 1) * CFC.rpow σ.matrix s := by
          rw [hs_left]
    _ = CFC.rpow σ.matrix ((s + 1) + s) := hs_total
    _ = CFC.rpow σ.matrix (1 / α) := by rw [hexp]

/-- The explicit input-side Holder witness is the Heisenberg adjoint of the
rotated Kraus family.

This is the algebraic normalization step for the α > 1 proof route: the
remaining hard theorem is the Schatten `q`-contraction of this rotated adjoint.
-/
theorem sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (B : CMatrix b) (α : ℝ) :
    sandwichedRenyiKrausAdjointInputWitness σ Φ K B α =
      MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix b := CFC.rpow (Φ.applyState σ).matrix s
  let D : CMatrix a := CFC.rpow σ.matrix (-s)
  have hCstar : Matrix.conjTranspose C = C := by
    exact (State.rpowMatrix_posSemidef (Φ.applyState σ) s).isHermitian.eq
  have hDstar : Matrix.conjTranspose D = D := by
    exact (State.rpowMatrix_posSemidef σ (-s)).isHermitian.eq
  have hCstar' :
      Matrix.conjTranspose (CFC.rpow (Φ.applyState σ).matrix s) =
        CFC.rpow (Φ.applyState σ).matrix s := by
    simpa [C] using hCstar
  have hDstar' :
      Matrix.conjTranspose (CFC.rpow σ.matrix (-s)) =
        CFC.rpow σ.matrix (-s) := by
    simpa [D] using hDstar
  have hCstar'' :
      Matrix.conjTranspose (CFC.rpow (Φ.applyState σ).matrix ((1 - α) / (2 * α))) =
        CFC.rpow (Φ.applyState σ).matrix ((1 - α) / (2 * α)) := by
    simpa [s] using hCstar'
  have hDstar'' :
      Matrix.conjTranspose (CFC.rpow σ.matrix (-((1 - α) / (2 * α)))) =
        CFC.rpow σ.matrix (-((1 - α) / (2 * α))) := by
    simpa [s] using hDstar'
  ext i j
  simp only [sandwichedRenyiKrausAdjointInputWitness, sandwichedRenyiRotatedKraus,
    sandwichedRenyiHolderDualEffect, MatrixMap.krausAdjoint, Matrix.conjTranspose_mul]
  rw [hCstar'', hDstar'']
  simp [Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul]

/-- The rotated Kraus adjoint sends the output dual reference endpoint
`(Φσ)^(1 - 1/α)` back to the input endpoint `σ^(1 - 1/α)`.

Together with `sandwichedRenyiRotatedKraus_apply_referencePower_eq`, this gives
the two exact endpoint normalizations required by the α > 1 interpolation
route. -/
theorem sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) =
      CFC.rpow σ.matrix (1 - 1 / α) := by
  let τ : State b := Φ.applyState σ
  let s : ℝ := (1 - α) / (2 * α)
  let r : ℝ := 1 - 1 / α
  have hα_ne_zero : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα_gt_one)
  have hτ_nonneg : 0 ≤ τ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσΦ.posSemidef
  have hσ_nonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hsrs : (s + r) + s = 0 := by
    dsimp [s, r]
    field_simp [hα_ne_zero]
    ring
  have hnegs : -s + -s = r := by
    dsimp [s, r]
    field_simp [hα_ne_zero]
    ring
  have hdual_one :
      sandwichedRenyiHolderDualEffect τ (CFC.rpow τ.matrix r) α =
        (1 : CMatrix b) := by
    have hsr :
        CFC.rpow τ.matrix s * CFC.rpow τ.matrix r =
          CFC.rpow τ.matrix (s + r) := by
      exact (CFC.rpow_add (a := τ.matrix) (x := s) (y := r) hσΦ.isUnit).symm
    have htotal :
        CFC.rpow τ.matrix (s + r) * CFC.rpow τ.matrix s =
          CFC.rpow τ.matrix ((s + r) + s) := by
      exact (CFC.rpow_add (a := τ.matrix) (x := s + r) (y := s) hσΦ.isUnit).symm
    unfold sandwichedRenyiHolderDualEffect
    change CFC.rpow τ.matrix s * CFC.rpow τ.matrix r * CFC.rpow τ.matrix s =
      (1 : CMatrix b)
    calc
      CFC.rpow τ.matrix s * CFC.rpow τ.matrix r * CFC.rpow τ.matrix s =
          (CFC.rpow τ.matrix s * CFC.rpow τ.matrix r) * CFC.rpow τ.matrix s := by
            rw [Matrix.mul_assoc]
      _ = CFC.rpow τ.matrix (s + r) * CFC.rpow τ.matrix s := by
            rw [hsr]
      _ = CFC.rpow τ.matrix ((s + r) + s) := htotal
      _ = CFC.rpow τ.matrix 0 := by rw [hsrs]
      _ = (1 : CMatrix b) := CFC.rpow_zero τ.matrix (ha := hτ_nonneg)
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) α
  rw [← hinput_eq]
  unfold sandwichedRenyiKrausAdjointInputWitness
  change CFC.rpow σ.matrix (-s) *
      MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect τ (CFC.rpow τ.matrix r) α) *
      CFC.rpow σ.matrix (-s) =
    CFC.rpow σ.matrix r
  rw [hdual_one, MatrixMap.krausAdjoint_one_of_tracePreserving K hTP]
  have hleft :
      CFC.rpow σ.matrix (-s) * (1 : CMatrix a) * CFC.rpow σ.matrix (-s) =
        CFC.rpow σ.matrix (-s) * CFC.rpow σ.matrix (-s) := by
    simp
  rw [hleft]
  calc
    CFC.rpow σ.matrix (-s) * CFC.rpow σ.matrix (-s) =
        CFC.rpow σ.matrix (-s + -s) := by
          exact (CFC.rpow_add (a := σ.matrix) (x := -s) (y := -s) hσ.isUnit).symm
    _ = CFC.rpow σ.matrix r := by rw [hnegs]

/-- The output sandwiched inner operator is obtained by applying the rotated
Kraus map to the input sandwiched inner operator.

This is the Schrödinger-picture counterpart of
`sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint`. It reduces
the α > 1 data-processing theorem to proving the correct Schatten contraction
for this specific rotated CP map. -/
theorem sandwichedRenyiInner_eq_rotatedKraus_apply
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (α : ℝ) :
    sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α =
      MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (sandwichedRenyiInner ρ σ α) := by
  let s : ℝ := (1 - α) / (2 * α)
  let Cσ : CMatrix a := CFC.rpow σ.matrix s
  let Dσ : CMatrix a := CFC.rpow σ.matrix (-s)
  let Cτ : CMatrix b := CFC.rpow (Φ.applyState σ).matrix s
  have hCτstar : Matrix.conjTranspose Cτ = Cτ := by
    exact (State.rpowMatrix_posSemidef (Φ.applyState σ) s).isHermitian.eq
  have hDσstar : Matrix.conjTranspose Dσ = Dσ := by
    exact (State.rpowMatrix_posSemidef σ (-s)).isHermitian.eq
  have hDσCσ : Dσ * Cσ = 1 := by
    simpa [Cσ, Dσ] using
      (CFC.rpow_neg_mul_rpow (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hCσDσ : Cσ * Dσ = 1 := by
    simpa [Cσ, Dσ] using
      (CFC.rpow_mul_rpow_neg (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDσCσ_mul : ∀ X : CMatrix a, Dσ * (Cσ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hDσCσ, Matrix.one_mul]
  have hCσDσ_mul : ∀ X : CMatrix a, Cσ * (Dσ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hCσDσ, Matrix.one_mul]
  have hCσDσ_mul_rect : ∀ X : Matrix a b ℂ, Cσ * (Dσ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hCσDσ, Matrix.one_mul]
  change Cτ * (Φ.applyState ρ).matrix * Cτ =
    MatrixMap.ofKraus (fun k : κ => Cτ * K k * Dσ) (Cσ * ρ.matrix * Cσ)
  rw [show (Φ.applyState ρ).matrix = Φ.map ρ.matrix by rfl, hK]
  ext i j
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.conjTranspose_mul]
  rw [hDσstar, hCτstar]
  simp [Matrix.mul_assoc, hDσCσ_mul, hCσDσ_mul_rect,
    Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]

/-- The rotated Kraus map sends the input reference endpoint `σ^(1/α)` to the
output reference endpoint `(Φσ)^(1/α)`.

This is the Schrödinger-side endpoint normalization needed before applying the
α > 1 noncommutative interpolation/Schatten-contraction theorem. -/
theorem sandwichedRenyiRotatedKraus_apply_referencePower_eq
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α)) =
      CFC.rpow (Φ.applyState σ).matrix (1 / α) := by
  have hα_ne_zero : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα_gt_one)
  have hinner :=
    sandwichedRenyiInner_eq_rotatedKraus_apply
      K σ σ Φ hK hσ α
  rw [sandwichedRenyiInner_self_eq_rpow σ hσ α hα_ne_zero,
    sandwichedRenyiInner_self_eq_rpow (Φ.applyState σ) hσΦ α hα_ne_zero] at hinner
  exact hinner.symm

/-- The interpolation reference endpoint `σ^(1/α)` has normalized
`α`-power trace. -/
theorem state_rpow_one_div_psdTracePower_eq_one
    (σ : State a) (hσ : σ.matrix.PosDef) (α : ℝ) (hα_pos : 0 < α) :
    psdTracePower (CFC.rpow σ.matrix (1 / α))
        (σ.rpowMatrix_posSemidef (1 / α)) α = 1 := by
  have hσ_nonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hone_div_nonneg : 0 ≤ 1 / α := by positivity
  have hα_ne_zero : α ≠ 0 := ne_of_gt hα_pos
  have hpow :
      CFC.rpow (CFC.rpow σ.matrix (1 / α)) α =
        CFC.rpow σ.matrix (1 : ℝ) := by
    calc
      CFC.rpow (CFC.rpow σ.matrix (1 / α)) α =
          CFC.rpow σ.matrix ((1 / α) * α) := by
            exact CFC.rpow_rpow_of_exponent_nonneg σ.matrix
              (1 / α) α hone_div_nonneg hα_nonneg hσ_nonneg
      _ = CFC.rpow σ.matrix (1 : ℝ) := by
            congr 1
            field_simp [hα_ne_zero]
  have hone : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
    CFC.rpow_one σ.matrix (ha := hσ_nonneg)
  rw [psdTracePower, hpow, hone, σ.trace_eq_one]
  norm_num

/-- The full-rank sandwiched Renyi divergence of a state from itself is zero.

This is the normalization endpoint needed for turning the already-proved
`β > 1` DPI into ordinary nonnegativity once a discard/terminal channel is
available. -/
theorem sandwichedRenyi_self_eq_zero
    (σ : State a) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi σ σ hσ hσ α hα_pos hα_ne_one = 0 := by
  have hinner :
      sandwichedRenyiInner σ σ α = CFC.rpow σ.matrix (1 / α) :=
    sandwichedRenyiInner_self_eq_rpow σ hσ α (ne_of_gt hα_pos)
  have htrace :
      psdTracePower (sandwichedRenyiInner σ σ α)
          (sandwichedRenyiInner_posSemidef σ σ α) α = 1 := by
    simpa [hinner] using state_rpow_one_div_psdTracePower_eq_one σ hσ α hα_pos
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner, htrace]
  simp [log2]

/-- The PSD-friendly low-`α` `Q` functional is normalized on equal states.

This is the `Q_α(ω,ω)=1` factor needed when local-unitary twirling produces a
common maximally mixed tensor factor. -/
theorem sandwichedRenyiQ_state_self
    (σ : State a) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) :
    sandwichedRenyiQ σ.matrix σ.matrix σ.pos σ.pos α = 1 := by
  rw [sandwichedRenyiQ_eq_psdTracePower_inner]
  simpa [sandwichedRenyiInner_self_eq_rpow σ hσ α (ne_of_gt hα_pos), psdTracePower]
    using state_rpow_one_div_psdTracePower_eq_one σ hσ α hα_pos

/-- The maximally mixed tensor factor contributes unit `Q` mass. -/
theorem sandwichedRenyiQ_maximallyMixed_self [Nonempty a]
    (α : ℝ) (hα_pos : 0 < α) :
    sandwichedRenyiQ
      (maximallyMixed a).matrix (maximallyMixed a).matrix
      (maximallyMixed a).pos (maximallyMixed a).pos α = 1 :=
  sandwichedRenyiQ_state_self (maximallyMixed a)
    (maximallyMixed_posDef_of_nonempty (a := a)) α hα_pos

/-- Tensoring both arguments with the same maximally mixed state leaves the
low-`α` `Q` functional unchanged.

This is the normalization side of the local-unitary twirling route for partial
trace monotonicity. -/
theorem sandwichedRenyiQ_kronecker_maximallyMixed_right [Nonempty b]
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.kronecker ρ (maximallyMixed b).matrix)
        (Matrix.kronecker σ (maximallyMixed b).matrix)
        (hρ.kronecker (maximallyMixed b).pos)
        (hσ.kronecker (maximallyMixed b).pos) α =
      sandwichedRenyiQ ρ σ hρ hσ α := by
  have hα_pos : 0 < α := by linarith
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hs_nonneg : 0 ≤ (1 - α) / (2 * α) := by
    have hnum : 0 ≤ 1 - α := le_of_lt (sub_pos.mpr hα_lt_one)
    have hden : 0 ≤ 2 * α := by positivity
    exact div_nonneg hnum hden
  rw [sandwichedRenyiQ_kronecker hρ hσ (maximallyMixed b).pos
    (maximallyMixed b).pos α hs_nonneg hα_nonneg]
  rw [sandwichedRenyiQ_maximallyMixed_self (a := b) α hα_pos]
  ring

/-- The unitary acting as identity on the left tensor factor and as `U` on the
right tensor factor. -/
def localRightUnitary (U : Matrix.unitaryGroup b ℂ) :
    Matrix.unitaryGroup (Prod a b) ℂ :=
  ⟨Matrix.kronecker (1 : CMatrix a) (U : CMatrix b), by
    let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
    simpa using Matrix.kronecker_mem_unitary I.2 U.2⟩

@[simp] theorem localRightUnitary_coe (U : Matrix.unitaryGroup b ℂ) :
    (localRightUnitary (a := a) U : CMatrix (Prod a b)) =
      Matrix.kronecker (1 : CMatrix a) (U : CMatrix b) := rfl

/-- The low-`α` `Q` functional is invariant under unitary conjugation on the
right tensor factor. -/
theorem sandwichedRenyiQ_localRightUnitary_conj
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (U : Matrix.unitaryGroup b ℂ) (α : ℝ)
    (hs_nonneg : 0 ≤ (1 - α) / (2 * α)) (hα_nonneg : 0 ≤ α) :
    sandwichedRenyiQ
        ((localRightUnitary (a := a) U : CMatrix (Prod a b)) * ρ *
          star (localRightUnitary (a := a) U : CMatrix (Prod a b)))
        ((localRightUnitary (a := a) U : CMatrix (Prod a b)) * σ *
          star (localRightUnitary (a := a) U : CMatrix (Prod a b)))
        (by
          simpa using
            posSemidef_unitary_conj hρ (localRightUnitary (a := a) U)⁻¹)
        (by
          simpa using
            posSemidef_unitary_conj hσ (localRightUnitary (a := a) U)⁻¹)
        α =
      sandwichedRenyiQ ρ σ hρ hσ α :=
  sandwichedRenyiQ_unitary_conj hρ hσ (localRightUnitary (a := a) U)
    α hs_nonneg hα_nonneg

/-- The interpolation reference endpoint `σ^(1/α)` has normalized
PSD Schatten `α` expression. -/
theorem state_rpow_one_div_psdSchattenPNorm_eq_one
    (σ : State a) (hσ : σ.matrix.PosDef) (α : ℝ) (hα_pos : 0 < α) :
    psdSchattenPNorm (CFC.rpow σ.matrix (1 / α))
        (σ.rpowMatrix_posSemidef (1 / α)) α = 1 := by
  rw [psdSchattenPNorm,
    state_rpow_one_div_psdTracePower_eq_one σ hσ α hα_pos]
  exact Real.one_rpow (1 / α)

/-- The Holder-dual interpolation reference endpoint `σ^(1-1/α)` has
normalized `q`-power trace when `q` is Holder-conjugate to `α`. -/
theorem state_rpow_one_sub_inv_psdTracePower_eq_one
    (σ : State a) (hσ : σ.matrix.PosDef) (α q : ℝ)
    (hpq : α.HolderConjugate q) :
    psdTracePower (CFC.rpow σ.matrix (1 - 1 / α))
        (σ.rpowMatrix_posSemidef (1 - 1 / α)) q = 1 := by
  have hσ_nonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hq_nonneg : 0 ≤ q := le_of_lt hpq.symm.pos
  have hr_eq : 1 - 1 / α = q⁻¹ := by
    simpa [one_div] using hpq.one_sub_inv
  have hr_nonneg : 0 ≤ 1 - 1 / α := by
    rw [hr_eq]
    exact inv_nonneg.mpr hq_nonneg
  have hpow :
      CFC.rpow (CFC.rpow σ.matrix (1 - 1 / α)) q =
        CFC.rpow σ.matrix (1 : ℝ) := by
    calc
      CFC.rpow (CFC.rpow σ.matrix (1 - 1 / α)) q =
          CFC.rpow σ.matrix ((1 - 1 / α) * q) := by
            exact CFC.rpow_rpow_of_exponent_nonneg σ.matrix
              (1 - 1 / α) q hr_nonneg hq_nonneg hσ_nonneg
      _ = CFC.rpow σ.matrix (1 : ℝ) := by
            congr 1
            rw [hr_eq]
            field_simp [hpq.symm.ne_zero]
  have hone : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
    CFC.rpow_one σ.matrix (ha := hσ_nonneg)
  rw [psdTracePower, hpow, hone, σ.trace_eq_one]
  norm_num

/-- The rotated Kraus map preserves the normalized `α`-power trace of the
reference interpolation endpoint.

This is the concrete boundary-norm check for the α > 1 interpolation route:
the map sends `σ^(1/α)` to `(Φσ)^(1/α)`, and both endpoints have power trace
one. -/
theorem sandwichedRenyiRotatedKraus_apply_referencePower_psdTracePower_eq_one
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    psdTracePower
        (MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α)))
        (MatrixMap.ofKraus_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α))
          (σ.rpowMatrix_posSemidef (1 / α)))
        α = 1 := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  rw [psdTracePower,
    sandwichedRenyiRotatedKraus_apply_referencePower_eq
      K σ Φ hK hσ hσΦ α hα_gt_one]
  simpa [psdTracePower] using
    state_rpow_one_div_psdTracePower_eq_one (Φ.applyState σ) hσΦ α hα_pos

/-- Order endpoint for the Schrödinger side of the α > 1 rotated-Kraus
interpolation route.

If an input positive witness is dominated by the input reference endpoint
`σ^(1/α)`, then its rotated Kraus image is dominated by the output endpoint
`(Φσ)^(1/α)`. -/
theorem sandwichedRenyiRotatedKraus_apply_le_referencePower_of_le
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) {A : CMatrix a}
    (hA_le : A ≤ CFC.rpow σ.matrix (1 / α)) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A ≤
      CFC.rpow (Φ.applyState σ).matrix (1 / α) := by
  rw [Matrix.le_iff] at hA_le ⊢
  have hpos :
      (MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α) - A)).PosSemidef :=
    MatrixMap.ofKraus_mapsPositive
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
      (CFC.rpow σ.matrix (1 / α) - A) hA_le
  rw [map_sub,
    sandwichedRenyiRotatedKraus_apply_referencePower_eq
      K σ Φ hK hσ hσΦ α hα_gt_one] at hpos
  exact hpos

/-- Schrödinger-side endpoint trace-pairing bound for the α > 1 interpolation
route.

If an input PSD test operator is dominated by the input reference endpoint
`σ^(1/α)`, then its rotated Kraus image pairs with every positive output
`q`-unit-ball witness by at most one. This is one concrete boundary estimate
needed by the eventual noncommutative interpolation proof. -/
theorem sandwichedRenyiRotatedKraus_tracePairing_le_one_of_input_le_referencePower
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (_hA : A.PosSemidef)
    (hA_le : A ≤ CFC.rpow σ.matrix (1 / α))
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) * B).trace).re ≤
      1 := by
  have hTA_le :
      MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A ≤
        CFC.rpow (Φ.applyState σ).matrix (1 / α) :=
    sandwichedRenyiRotatedKraus_apply_le_referencePower_of_le
      K σ Φ hK hσ hσΦ α hα_gt_one hA_le
  have htrace_order :
      (((MatrixMap.ofKraus
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) * B).trace).re ≤
        ((CFC.rpow (Φ.applyState σ).matrix (1 / α) * B).trace).re := by
    have hcomm_left :
        (((MatrixMap.ofKraus
            (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
              B).trace).re =
          ((B *
            MatrixMap.ofKraus
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A).trace).re := by
      rw [Matrix.trace_mul_comm]
    have hcomm_right :
        ((CFC.rpow (Φ.applyState σ).matrix (1 / α) * B).trace).re =
          ((B * CFC.rpow (Φ.applyState σ).matrix (1 / α)).trace).re := by
      rw [Matrix.trace_mul_comm]
    rw [hcomm_left, hcomm_right]
    exact cMatrix_trace_mul_le_of_le_posSemidef_left (W := B)
      (A := MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A)
      (B := CFC.rpow (Φ.applyState σ).matrix (1 / α)) hB hTA_le
  have hRpos :
      (CFC.rpow (Φ.applyState σ).matrix (1 / α)).PosSemidef :=
    (Φ.applyState σ).rpowMatrix_posSemidef (1 / α)
  have hholder :
      ((CFC.rpow (Φ.applyState σ).matrix (1 / α) * B).trace).re ≤
        psdSchattenPNorm (CFC.rpow (Φ.applyState σ).matrix (1 / α)) hRpos α :=
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      hRpos hB hpq (le_of_lt hpq.symm.lt) hBq
  have hnorm :
      psdSchattenPNorm (CFC.rpow (Φ.applyState σ).matrix (1 / α)) hRpos α = 1 := by
    simpa [hRpos] using
      state_rpow_one_div_psdSchattenPNorm_eq_one
        (Φ.applyState σ) hσΦ α (lt_trans zero_lt_one hα_gt_one)
  exact htrace_order.trans (hholder.trans_eq hnorm)

/-- The rotated Kraus adjoint preserves the normalized Holder-dual endpoint
unit ball.

For `q` Holder-conjugate to `α`, the output endpoint
`(Φσ)^(1-1/α)` has `q`-power trace one, and the rotated Kraus adjoint sends it
exactly to `σ^(1-1/α)`, which has the same normalized `q`-power trace. -/
theorem sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_psdTracePower_eq_one
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)))
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α))
          ((Φ.applyState σ).rpowMatrix_posSemidef (1 - 1 / α)))
        q = 1 := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  rw [psdTracePower,
    sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
      K σ Φ hTP hσ hσΦ α hα_gt_one]
  simpa [psdTracePower] using
    state_rpow_one_sub_inv_psdTracePower_eq_one σ hσ α q hpq

/-- Order endpoint for the α > 1 rotated-Kraus interpolation route.

If an output witness is dominated by the output dual reference endpoint
`(Φσ)^(1-1/α)`, then its rotated Kraus adjoint is dominated by the input dual
reference endpoint `σ^(1-1/α)`. This is the order-theoretic boundary condition
used by the noncommutative interpolation/Schatten-contraction step. -/
theorem sandwichedRenyiRotatedKrausAdjoint_le_referenceDualPower_of_le
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) {B : CMatrix b}
    (hB_le :
      B ≤ CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) :
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B ≤
      CFC.rpow σ.matrix (1 - 1 / α) := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  rw [Matrix.le_iff] at hB_le ⊢
  have hpos :
      (MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α) - B)).PosSemidef :=
    MatrixMap.krausAdjoint_mapsPositive
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
      (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α) - B) hB_le
  rw [MatrixMap.krausAdjoint_sub_apply,
    sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
      K σ Φ hTP hσ hσΦ α hα_gt_one] at hpos
  exact hpos

/-- Trace-pairing criterion for the rotated-adjoint `q`-unit-ball contraction.

This is the noncommutative Schatten-duality handoff for the α > 1 proof route:
to show that the rotated Heisenberg adjoint maps a positive output witness into
the input `q`-unit ball, it is enough to prove the matching trace-pairing bound
against every positive input test operator. The remaining mathematical content
is exactly that interpolation trace-pairing bound. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_of_tracePairingBound
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (τ : State b) (α q : ℝ) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hbound : ∀ A : CMatrix a, ∀ hA : A.PosSemidef,
      (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) *
          B).trace).re ≤ psdSchattenPNorm A hA α) :
    psdTracePower
        (MatrixMap.krausAdjoint (sandwichedRenyiRotatedKraus σ τ K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ τ K α) B hB) q ≤
      1 := by
  let L : κ → Matrix b a ℂ := sandwichedRenyiRotatedKraus σ τ K α
  exact
    psdTracePower_le_one_of_trace_mul_le_psdSchattenPNorm
      (MatrixMap.krausAdjoint_mapsPositive L B hB) hpq
      (fun A hA => by
        have hdual := MatrixMap.ofKraus_trace_duality L A B
        have htrace :
            ((A * MatrixMap.krausAdjoint L B).trace).re =
              (((MatrixMap.ofKraus L A) * B).trace).re :=
          (congrArg Complex.re hdual).symm
        rw [htrace]
        exact hbound A hA)

/-- Beigi weighted-map `q`-unit-ball contraction for the rotated Heisenberg
adjoint, in the full-rank reference domain.

This is the first non-circular channel-specific contraction theorem in the
α > 1 DPI route: the proof uses the normalized PSD trace-pairing theorem and
Schatten duality, not a DPI or contraction hypothesis. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_of_beigi
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB) q ≤
      1 := by
  exact
    sandwichedRenyiRotatedKrausAdjoint_qBall_of_tracePairingBound
      K σ (Φ.applyState σ) α q hpq hB
      (fun A hA =>
        sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_le_one
          K σ Φ hK hσ hσΦ α q hα_gt_one hpq hA hB hBq)

/-- Exact dual formulation of the rotated-adjoint `q`-unit-ball contraction.

For a fixed positive output witness `B`, the rotated Heisenberg adjoint lies in
the input-side PSD `q`-unit ball iff the Schrödinger rotated Kraus map satisfies
the matching trace-pairing bound against every positive input test operator.
This is the Lean-level form of the remaining noncommutative interpolation
obligation in the α > 1 DPI route. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_iff_tracePairingBound
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (τ : State b) (α q : ℝ) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef) :
    psdTracePower
        (MatrixMap.krausAdjoint (sandwichedRenyiRotatedKraus σ τ K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ τ K α) B hB) q ≤
      1 ↔
      ∀ A : CMatrix a, ∀ hA : A.PosSemidef,
        (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) *
            B).trace).re ≤ psdSchattenPNorm A hA α := by
  let L : κ → Matrix b a ℂ := sandwichedRenyiRotatedKraus σ τ K α
  have hdual_iff :=
    psdTracePower_le_one_iff_trace_mul_le_psdSchattenPNorm
      (MatrixMap.krausAdjoint_mapsPositive L B hB) hpq
  constructor
  · intro hq A hA
    have hdual := MatrixMap.ofKraus_trace_duality L A B
    have htrace :
        (((MatrixMap.ofKraus L A) * B).trace).re =
          ((A * MatrixMap.krausAdjoint L B).trace).re :=
      congrArg Complex.re hdual
    rw [htrace]
    exact hdual_iff.mp hq A hA
  · intro hbound
    exact hdual_iff.mpr (fun A hA => by
      have hdual := MatrixMap.ofKraus_trace_duality L A B
      have htrace :
          ((A * MatrixMap.krausAdjoint L B).trace).re =
            (((MatrixMap.ofKraus L A) * B).trace).re :=
        (congrArg Complex.re hdual).symm
      rw [htrace]
      exact hbound A hA)

/-- Endpoint-order subdomain of the rotated-adjoint `q`-unit-ball contraction.

Every positive output witness dominated by the dual reference endpoint
`(Φσ)^(1-1/α)` is sent by the rotated Heisenberg adjoint into the input
`q`-unit ball. This is a genuine q-ball theorem on the interpolation boundary;
the missing full contraction is the extension from this endpoint-order subdomain
to arbitrary positive output `q`-unit-ball witnesses. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_of_le_referenceDualPower
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hB_le : B ≤ CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) :
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB) q ≤
      1 := by
  let W : CMatrix a :=
    MatrixMap.krausAdjoint
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B
  have hWpos : W.PosSemidef := by
    simpa [W] using
      MatrixMap.krausAdjoint_mapsPositive
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB
  have hW_le :
      W ≤ CFC.rpow σ.matrix (1 - 1 / α) := by
    simpa [W] using
      sandwichedRenyiRotatedKrausAdjoint_le_referenceDualPower_of_le
        K σ Φ hK hσ hσΦ α hα_gt_one hB_le
  have hσ_trace : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  have hr : 1 - 1 / α = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hcriterion :=
    psdTracePower_le_one_of_trace_mul_le_psdSchattenPNorm
      hWpos hpq
      (fun A hA => by
        have htrace_le :
            ((A * W).trace).re ≤
              ((A * CFC.rpow σ.matrix (1 - 1 / α)).trace).re :=
          cMatrix_trace_mul_le_of_le_posSemidef_left hA hW_le
        have hholder :
            ((A * CFC.rpow σ.matrix (1 - 1 / α)).trace).re ≤
              psdSchattenPNorm A hA α :=
          psd_trace_rpow_holder_variational_upper
            hA σ.pos hσ_trace hpq hr
        exact htrace_le.trans hholder)
  simpa [W] using hcriterion

/-- Boundary data for the α > 1 rotated-Kraus interpolation route.

This packages the two exact endpoint identities and their normalized
trace-power unit-ball checks. The remaining theorem needed for full α > 1 DPI
is the noncommutative interpolation step that turns these boundary data into a
Schatten contraction for arbitrary positive inputs. -/
theorem sandwichedRenyiRotatedKraus_interpolationBoundaryData
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α)) =
      CFC.rpow (Φ.applyState σ).matrix (1 / α) ∧
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) =
      CFC.rpow σ.matrix (1 - 1 / α) ∧
    psdTracePower
        (MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α)))
        (MatrixMap.ofKraus_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α))
          (σ.rpowMatrix_posSemidef (1 / α)))
        α = 1 ∧
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)))
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α))
          ((Φ.applyState σ).rpowMatrix_posSemidef (1 - 1 / α)))
        q = 1 := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  exact
    ⟨sandwichedRenyiRotatedKraus_apply_referencePower_eq
        K σ Φ hK hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
        K σ Φ hTP hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKraus_apply_referencePower_psdTracePower_eq_one
        K σ Φ hK hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_psdTracePower_eq_one
        K σ Φ hK hσ hσΦ α q hα_gt_one hpq⟩

/-- Rotated Kraus endpoint normalization package for the α > 1 interpolation
route.

The pair of endpoint identities is the finite-dimensional normalization data
needed to turn the remaining analytic interpolation theorem into the desired
Schatten contraction. -/
theorem sandwichedRenyiRotatedKraus_interpolationEndpoints
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α)) =
      CFC.rpow (Φ.applyState σ).matrix (1 / α) ∧
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) =
      CFC.rpow σ.matrix (1 - 1 / α) := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  exact
    ⟨sandwichedRenyiRotatedKraus_apply_referencePower_eq
        K σ Φ hK hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
        K σ Φ hTP hσ hσΦ α hα_gt_one⟩

/-- The pulled-back input-side Holder witness is positive semidefinite whenever
the output witness is positive semidefinite. -/
theorem sandwichedRenyiKrausAdjointInputWitness_posSemidef
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    (α : ℝ) :
    (sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let D : CMatrix a := CFC.rpow σ.matrix (-s)
  have hD : D.PosSemidef := by
    simpa [D] using σ.rpowMatrix_posSemidef (-s)
  have hDstar : star D = D := hD.isHermitian.eq
  have hE :
      (MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).PosSemidef :=
    sandwichedRenyi_krausAdjoint_holderDualEffect_posSemidef K σ Φ hB α
  have hW : (star D *
      MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) * D).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hE D
  rw [hDstar] at hW
  simpa [sandwichedRenyiKrausAdjointInputWitness, s, D] using hW

/-- At the Hilbert-Schmidt endpoint `α = 2`, the explicit Kraus-adjoint input
Holder witness has no larger `2`-power trace than the output Holder dual
effect.

This is the first fully closed unit-ball transport step for the α > 1
variational route. It combines the quarter-power sandwich inequality with
Kadison's inequality for the channel Heisenberg adjoint. -/
theorem sandwichedRenyiKrausAdjointInputWitness_tracePower_two_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hσ : σ.matrix.PosDef) {B : CMatrix b} (hB : B.PosSemidef) :
    psdTracePower (sandwichedRenyiKrausAdjointInputWitness σ Φ K B (2 : ℝ))
        (sandwichedRenyiKrausAdjointInputWitness_posSemidef K σ Φ hB (2 : ℝ))
        (2 : ℝ) ≤
      psdTracePower (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B (2 : ℝ))
        (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB (2 : ℝ))
        (2 : ℝ) := by
  let E : CMatrix b := sandwichedRenyiHolderDualEffect (Φ.applyState σ) B (2 : ℝ)
  let A : CMatrix a := MatrixMap.krausAdjoint K E
  have hA : A.PosSemidef := by
    simpa [A, E] using
      sandwichedRenyi_krausAdjoint_holderDualEffect_posSemidef
        K σ Φ hB (2 : ℝ)
  have hquarter :=
    cMatrix_quarter_sandwich_tracePower_two_le σ hσ hA
  have hkadison :=
    sandwichedRenyi_holderDualEffect_tracePower_two_le
      K σ Φ hK hTP hB (2 : ℝ)
  have hleft :
      psdTracePower (sandwichedRenyiKrausAdjointInputWitness σ Φ K B (2 : ℝ))
          (sandwichedRenyiKrausAdjointInputWitness_posSemidef K σ Φ hB (2 : ℝ))
          (2 : ℝ) ≤
        ((σ.matrix * (A * A)).trace).re := by
    have hexp : -((1 - (2 : ℝ)) / (2 * (2 : ℝ))) = (1 / 4 : ℝ) := by
      norm_num
    simpa [sandwichedRenyiKrausAdjointInputWitness, E, A, hexp] using hquarter
  have hright :
      ((σ.matrix * (A * A)).trace).re ≤
        psdTracePower E
          (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB (2 : ℝ))
          (2 : ℝ) := by
    simpa [E, A] using hkadison
  exact hleft.trans hright

/-- Exact witness transport identity for the α > 1 Holder route.

The output trace pairing is rewritten as a trace pairing against the input
sandwiched inner operator with the explicit pulled-back input witness. The only
missing step for the full α > 1 theorem is proving this witness satisfies the
required `q`-unit-ball power-trace bound. -/
theorem sandwichedRenyi_inner_trace_eq_inputWitness
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (B : CMatrix b) (α : ℝ) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re =
      (sandwichedRenyiInner ρ σ α *
        sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).trace.re := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.matrix s
  let D : CMatrix a := CFC.rpow σ.matrix (-s)
  let E : CMatrix a :=
    MatrixMap.krausAdjoint K
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
  have hCD : C * D = 1 := by
    simpa [C, D] using
      (CFC.rpow_mul_rpow_neg (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDC : D * C = 1 := by
    simpa [C, D] using
      (CFC.rpow_neg_mul_rpow (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hinput :
      (sandwichedRenyiInner ρ σ α *
        sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).trace =
        (ρ.matrix * E).trace := by
    change (((C * ρ.matrix * C) * (D * E * D)).trace) =
      (ρ.matrix * E).trace
    calc
      ((C * ρ.matrix * C) * (D * E * D)).trace =
          (C * (ρ.matrix * E) * D).trace := by
          congr 1
          calc
            (C * ρ.matrix * C) * (D * E * D) =
                C * ρ.matrix * (C * D) * E * D := by
                noncomm_ring
            _ = C * ρ.matrix * 1 * E * D := by rw [hCD]
            _ = C * (ρ.matrix * E) * D := by noncomm_ring
      _ = ((D * C) * (ρ.matrix * E)).trace := by
          exact Matrix.trace_mul_cycle C (ρ.matrix * E) D
      _ = (ρ.matrix * E).trace := by
          rw [hDC, Matrix.one_mul]
  have houtput :=
    sandwichedRenyi_inner_trace_eq_krausAdjoint_holderDualEffect
      K ρ σ Φ hK B α
  simpa [E] using houtput.trans (congrArg Complex.re hinput.symm)

/-- Trace-pairing bound obtained from the rotated-Kraus adjoint `q`-unit-ball
contraction.

This is the exact handoff from the noncommutative interpolation theorem to the
current `psdSchattenPNorm` variational interface: once the rotated adjoint sends
every positive output `q`-unit-ball witness to a positive input `q`-unit-ball
witness, Holder's variational bound gives the trace-pairing estimate required
for α > 1 DPI. -/
theorem sandwichedRenyi_traceHolderUnitBall_le_of_rotatedKrausAdjoint_qBall
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (α q : ℝ) (hpq : α.HolderConjugate q)
    (hrotated :
      ∀ B : CMatrix b, ∀ hB : B.PosSemidef,
        psdTracePower B hB q ≤ 1 →
          psdTracePower
            (MatrixMap.krausAdjoint
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
            (MatrixMap.krausAdjoint_mapsPositive
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB)
            q ≤ 1)
    (B : CMatrix b) (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re ≤
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  have htrace :=
    sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ B α
  rw [htrace, hinput_eq]
  exact
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (MatrixMap.krausAdjoint_mapsPositive
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB)
      hpq (le_of_lt hpq.symm.lt)
      (hrotated B hB hBq)

/-- The reference dual endpoint already satisfies the trace-pairing bound
needed by the α > 1 variational route.

This is not the full interpolation theorem, because it covers the single
endpoint witness `B = (Φσ)^(1-1/α)` rather than every positive `q`-unit-ball
witness. It is the endpoint case of the missing rotated-adjoint Schatten
contraction. -/
theorem sandwichedRenyi_referenceDualEndpoint_traceHolder_le
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α *
        CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)).trace).re ≤
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  let B : CMatrix b := CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)
  have htrace :=
    sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ B α
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hendpoint :
      MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B =
        CFC.rpow σ.matrix (1 - 1 / α) := by
    simpa [B] using
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
        K σ Φ hTP hσ hσΦ α hα_gt_one
  rw [htrace, hinput_eq, hendpoint]
  exact
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (σ.rpowMatrix_posSemidef (1 - 1 / α))
      hpq (le_of_lt hpq.symm.lt)
      (le_of_eq (state_rpow_one_sub_inv_psdTracePower_eq_one σ hσ α q hpq))

/-- Trace-pairing bound for output witnesses dominated by the dual reference
endpoint.

This is an actual boundary estimate for the interpolation route: order
domination by `(Φσ)^(1-1/α)` is transported through the rotated adjoint to order
domination by `σ^(1-1/α)`, and the source-shaped Holder variational bound then
controls the input trace pairing by the input Schatten `α` expression. -/
theorem sandwichedRenyi_traceHolder_le_of_outputWitness_le_referenceDualPower
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hB_le : B ≤ CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re ≤
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  let W : CMatrix a :=
    MatrixMap.krausAdjoint
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B
  have htrace :=
    sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ B α
  have hW_pos : W.PosSemidef := by
    simpa [W] using
      MatrixMap.krausAdjoint_mapsPositive
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB
  have hW_le :
      W ≤ CFC.rpow σ.matrix (1 - 1 / α) := by
    simpa [W] using
      sandwichedRenyiRotatedKrausAdjoint_le_referenceDualPower_of_le
        K σ Φ hK hσ hσΦ α hα_gt_one hB_le
  have htrace_le :
      ((sandwichedRenyiInner ρ σ α * W).trace).re ≤
        ((sandwichedRenyiInner ρ σ α *
          CFC.rpow σ.matrix (1 - 1 / α)).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left
      (sandwichedRenyiInner_posSemidef ρ σ α) hW_le
  have hσ_trace : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  have hr : 1 - 1 / α = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hholder :
      ((sandwichedRenyiInner ρ σ α *
          CFC.rpow σ.matrix (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α :=
    psd_trace_rpow_holder_variational_upper
      (sandwichedRenyiInner_posSemidef ρ σ α) σ.pos hσ_trace hpq hr
  rw [htrace, hinput_eq]
  exact htrace_le.trans hholder

/-- Channel-level Kraus witness package for the α > 1 Holder route.

For every channel and output-side positive Holder witness, the channel's CP/TP
data supplies a Kraus representation whose Heisenberg adjoint is unital, whose
pulled-back input witness is PSD, and whose trace pairing is exactly the output
pairing. The remaining hard theorem is the q-unit-ball power-trace bound for
this witness. -/
theorem sandwichedRenyi_exists_kraus_inputWitness
    (ρ σ : State a) (Φ : Channel a b)
    (hσ : σ.matrix.PosDef) {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      (sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).PosSemidef ∧
      ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re =
        (sandwichedRenyiInner ρ σ α *
          sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).trace.re := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  refine ⟨K, hK, MatrixMap.krausAdjoint_one_of_tracePreserving K hTP, ?_, ?_⟩
  · exact sandwichedRenyiKrausAdjointInputWitness_posSemidef K σ Φ hB α
  · exact sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α

/-- A positive output-side Holder unit-ball witness is pulled back by a
trace-preserving Kraus channel to an input-side effect.

This is a non-circular CP/TP ingredient for the `α > 1` variational route: the
remaining hard step is the weighted `q`-unit-ball estimate after the additional
reference conjugations in `sandwichedRenyiKrausAdjointInputWitness`. -/
theorem sandwichedRenyi_krausAdjoint_outputWitness_effect
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q)
    (hBq : psdTracePower B hB q ≤ 1) :
    (MatrixMap.krausAdjoint K B).PosSemidef ∧ MatrixMap.krausAdjoint K B ≤ 1 :=
  MatrixMap.krausAdjoint_effect_of_tracePreserving K hTP hB
    (posSemidef_le_one_of_psdTracePower_le_one hB hq hBq)

/-- Channel-level form of `sandwichedRenyi_krausAdjoint_outputWitness_effect`
using the channel's Choi-positive Kraus representation. -/
theorem sandwichedRenyi_exists_kraus_outputWitness_effect
    (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    {q : ℝ} (hq : 0 < q) (hBq : psdTracePower B hB q ≤ 1) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      (MatrixMap.krausAdjoint K B).PosSemidef ∧
      MatrixMap.krausAdjoint K B ≤ 1 := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  refine ⟨K, hK, MatrixMap.krausAdjoint_one_of_tracePreserving K hTP, ?_, ?_⟩
  · exact (sandwichedRenyi_krausAdjoint_outputWitness_effect K hTP hB hq hBq).1
  · exact (sandwichedRenyi_krausAdjoint_outputWitness_effect K hTP hB hq hBq).2

/-- Every channel admits a Kraus representation whose Stinespring stack is an
isometry, with PSD orthogonal-complement projection.

This is the channel-level projection-positivity ingredient for the next
Kadison/variance step in the α > 1 Holder route. It uses only CP/TP channel
data and does not assume any DPI or contraction statement. -/
theorem sandwichedRenyi_exists_kraus_stinespring_projection
    (Φ : Channel a b) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      (1 - MatrixMap.krausStinespringMatrix K *
          Matrix.conjTranspose (MatrixMap.krausStinespringMatrix K)).PosSemidef := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hAdj : MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  refine ⟨K, hK, hAdj, ?_⟩
  exact MatrixMap.krausStinespringMatrix_projection_complement_posSemidef K hAdj

/-- Every channel admits a Kraus representation whose Heisenberg adjoint
satisfies Kadison's inequality.

This is the first channel-specific operator inequality on the α > 1
Holder/variational route. It uses only CP/TP channel data and the Stinespring
projection positivity, not any DPI or contraction hypothesis. -/
theorem sandwichedRenyi_exists_kraus_kadison
    (Φ : Channel a b) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      ∀ E : CMatrix b, E.IsHermitian →
        MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E ≤
          MatrixMap.krausAdjoint K (E * E) := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hAdj : MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  refine ⟨K, hK, hAdj, ?_⟩
  intro E hE
  exact MatrixMap.krausAdjoint_mul_self_le_of_krausAdjoint_one K hAdj hE

/-- At the endpoint `α = 1/2`, the sandwiched Renyi trace-power kernel is the
root fidelity `F(ρ,σ)`.

This is the definition bridge from the local sandwiched-Renyi API to the proved
Uhlmann/fidelity monotonicity theorem. -/
theorem sandwichedRenyiInner_psdTracePower_half_eq_fidelity
    (ρ σ : State a) :
    psdTracePower (sandwichedRenyiInner ρ σ (1 / 2 : ℝ))
        (sandwichedRenyiInner_posSemidef ρ σ (1 / 2 : ℝ)) (1 / 2 : ℝ) =
      ρ.fidelity σ := by
  have hinner :
      sandwichedRenyiInner ρ σ (1 / 2 : ℝ) =
        Matrix.conjTranspose (ρ.sqrtMatrix * σ.sqrtMatrix) *
          (ρ.sqrtMatrix * σ.sqrtMatrix) := by
    have hexp :
        (1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    calc
      sandwichedRenyiInner ρ σ (1 / 2 : ℝ) =
          σ.sqrtMatrix * ρ.matrix * σ.sqrtMatrix := by
            unfold sandwichedRenyiInner
            rw [hexp]
            simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
      _ = Matrix.conjTranspose (ρ.sqrtMatrix * σ.sqrtMatrix) *
            (ρ.sqrtMatrix * σ.sqrtMatrix) := by
            rw [Matrix.conjTranspose_mul, σ.sqrtMatrix_isHermitian.eq,
              ρ.sqrtMatrix_isHermitian.eq, ← ρ.sqrtMatrix_mul_self]
            noncomm_ring
  unfold psdTracePower State.fidelity traceNorm
  rw [hinner]
  simp [psdSqrt, CFC.sqrt_eq_rpow]

/-- Sandwiched Renyi data-processing inequality `D̃_α(Φρ ‖ Φσ) ≤ D̃_α(ρ ‖ σ)`
over the range `α ∈ [1/2, ∞)`, `α ≠ 1`. Statement only; the proof needs pinching
and complex interpolation. -/
def sandwichedRenyi_dataProcessing_statement (ρ σ : State a) (Φ : Channel a a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

/-- Same full-rank state-level sandwiched Renyi data-processing statement, but
with a general input-output channel `Φ : Channel a b`.

This is still weaker than the public source theorem for `m7-sandwiched-renyi-dpi`:
the source statement allows a positive semidefinite reference operator `σ`, while
this local sprint surface keeps the current full-rank `State + PosDef` domain. -/
def sandwichedRenyi_dataProcessing_channel_statement (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

/-- The `α = 1/2` endpoint of full-rank sandwiched Renyi DPI for a general
finite-dimensional channel.

This theorem is non-circular: it uses the proved Uhlmann/fidelity monotonicity
for channels, together with the endpoint bridge
`sandwichedRenyiInner_psdTracePower_half_eq_fidelity`. It is a genuine endpoint
subcase, not the full source theorem over all
`α ∈ [1/2,1) ∪ (1,∞)`. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_half
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ hρ hσ hρΦ hσΦ
      (1 / 2 : ℝ) (by norm_num) (by norm_num) := by
  have hfid_sq := State.squaredFidelity_le_applyState_squaredFidelity Φ ρ σ
  have hfid :
      ρ.fidelity σ ≤ (Φ.applyState ρ).fidelity (Φ.applyState σ) := by
    rw [State.squaredFidelity_eq_fidelity_sq,
      State.squaredFidelity_eq_fidelity_sq] at hfid_sq
    exact (sq_le_sq₀ (State.fidelity_nonneg ρ σ)
      (State.fidelity_nonneg (Φ.applyState ρ) (Φ.applyState σ))).mp hfid_sq
  have hpower :
      psdTracePower (sandwichedRenyiInner ρ σ (1 / 2 : ℝ))
          (sandwichedRenyiInner_posSemidef ρ σ (1 / 2 : ℝ)) (1 / 2 : ℝ) ≤
        psdTracePower
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) (1 / 2 : ℝ))
          (sandwichedRenyiInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    rw [sandwichedRenyiInner_psdTracePower_half_eq_fidelity ρ σ,
      sandwichedRenyiInner_psdTracePower_half_eq_fidelity
        (Φ.applyState ρ) (Φ.applyState σ)]
    exact hfid
  unfold sandwichedRenyi_dataProcessing_channel_statement
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ (1 / 2 : ℝ)
      (by norm_num) (by norm_num),
    sandwichedRenyi_eq_log2_psdTracePower_inner
      ρ σ hρ hσ (1 / 2 : ℝ) (by norm_num) (by norm_num)]
  have hin_pos :
      0 <
        psdTracePower (sandwichedRenyiInner ρ σ (1 / 2 : ℝ))
          (sandwichedRenyiInner_posSemidef ρ σ (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ (1 / 2 : ℝ)
  have hlog := log2_mono_of_pos hin_pos hpower
  have hcoef : 1 / ((1 / 2 : ℝ) - 1) = -2 := by norm_num
  rw [hcoef]
  exact mul_le_mul_of_nonpos_left hlog (by norm_num)

/-- The old same-space statement is exactly the `b = a` specialization of the
general-channel statement. This keeps the existing statement-only surface stable
while future proof work targets the source-shaped channel arity. -/
theorem sandwichedRenyi_dataProcessing_statement_iff_channel_statement
    (ρ σ : State a) (Φ : Channel a a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi_dataProcessing_statement ρ σ Φ hρ hσ hρΦ hσΦ α hα hα_ne_one ↔
      sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ hρ hσ hρΦ hσΦ
        α hα hα_ne_one :=
  Iff.rfl

/-- Classical stochastic channels satisfy the full-rank sandwiched Renyi DPI
statement for diagonal full-support inputs in the `α > 1` range.

This is a genuine channel primitive for the pinching/classical route; it uses
the CPTP `Classical.stochasticChannel` implementation and the proved classical
power-sum DPI, not a DPI hypothesis. -/
theorem sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_one_lt
    (p q : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_pos : ∀ y, 0 < (Classical.stochasticOutput p T y : ℝ))
    (hqOut_pos : ∀ y, 0 < (Classical.stochasticOutput q T y : ℝ))
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement
      (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
      (Classical.stochasticChannel T hT_sum)
      (Classical.diagonalState_posDef p hp_sum hp_pos)
      (Classical.diagonalState_posDef q hq_sum hq_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput p T)
          (Classical.stochasticOutput_sum p T hp_sum hT_sum) hpOut_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput q T)
          (Classical.stochasticOutput_sum q T hq_sum hT_sum) hqOut_pos)
      α (by linarith) (ne_of_gt hα_gt_one) := by
  classical
  simpa [sandwichedRenyi_dataProcessing_channel_statement,
    Classical.stochasticChannel_applyState_diagonalState] using
    sandwichedRenyi_diagonalState_stochastic_le_of_one_lt
    p q (Classical.stochasticOutput p T) (Classical.stochasticOutput q T)
    (fun i y => (T i y : ℝ)) hp_sum hq_sum hp_pos hq_pos
    (Classical.stochasticOutput_sum p T hp_sum hT_sum)
    (Classical.stochasticOutput_sum q T hq_sum hT_sum)
    hpOut_pos hqOut_pos
    (fun i y => NNReal.coe_nonneg (T i y))
    (fun i => by
      change ∑ y, ((T i y : ℝ≥0) : ℝ) = 1
      exact_mod_cast hT_sum i)
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    α hα_gt_one

/-- Classical stochastic channels satisfy the full-rank sandwiched Renyi DPI
statement for diagonal full-support inputs in the `0 < α < 1` range. -/
theorem sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_lt_one
    (p q : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_pos : ∀ y, 0 < (Classical.stochasticOutput p T y : ℝ))
    (hqOut_pos : ∀ y, 0 < (Classical.stochasticOutput q T y : ℝ))
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement
      (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
      (Classical.stochasticChannel T hT_sum)
      (Classical.diagonalState_posDef p hp_sum hp_pos)
      (Classical.diagonalState_posDef q hq_sum hq_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput p T)
          (Classical.stochasticOutput_sum p T hp_sum hT_sum) hpOut_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput q T)
          (Classical.stochasticOutput_sum q T hq_sum hT_sum) hqOut_pos)
      α hα_half (ne_of_lt hα_lt_one) := by
  classical
  simpa [sandwichedRenyi_dataProcessing_channel_statement,
    Classical.stochasticChannel_applyState_diagonalState] using
    sandwichedRenyi_diagonalState_stochastic_le_of_lt_one
    p q (Classical.stochasticOutput p T) (Classical.stochasticOutput q T)
    (fun i y => (T i y : ℝ)) hp_sum hq_sum hp_pos hq_pos
    (Classical.stochasticOutput_sum p T hp_sum hT_sum)
    (Classical.stochasticOutput_sum q T hq_sum hT_sum)
    hpOut_pos hqOut_pos
    (fun i y => NNReal.coe_nonneg (T i y))
    (fun i => by
      change ∑ y, ((T i y : ℝ≥0) : ℝ) = 1
      exact_mod_cast hT_sum i)
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    α (by linarith) hα_lt_one

/-- Classical stochastic channels satisfy the local full-rank sandwiched Renyi
DPI statement throughout the source range `1/2 ≤ α < 1` or `1 < α`, for
full-support diagonal inputs and full-support pushed-forward references. -/
theorem sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement
    (p q : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_pos : ∀ y, 0 < (Classical.stochasticOutput p T y : ℝ))
    (hqOut_pos : ∀ y, 0 < (Classical.stochasticOutput q T y : ℝ))
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement
      (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
      (Classical.stochasticChannel T hT_sum)
      (Classical.diagonalState_posDef p hp_sum hp_pos)
      (Classical.diagonalState_posDef q hq_sum hq_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput p T)
          (Classical.stochasticOutput_sum p T hp_sum hT_sum) hpOut_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput q T)
          (Classical.stochasticOutput_sum q T hq_sum hT_sum) hqOut_pos)
      α
      (by
        rcases hα_range with hlt | hgt
        · exact hlt.1
        · linarith)
      (by
        rcases hα_range with hlt | hgt
        · exact ne_of_lt hlt.2
        · exact ne_of_gt hgt) := by
  rcases hα_range with hlt | hgt
  · exact sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_lt_one
      p q T hp_sum hq_sum hT_sum hp_pos hq_pos hpOut_pos hqOut_pos α hlt.1 hlt.2
  · exact sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_one_lt
      p q T hp_sum hq_sum hT_sum hp_pos hq_pos hpOut_pos hqOut_pos α hgt

/-- Reference-spectral pinching commutes with the sandwiched inner operator:
pinching the state first is the same as pinching the sandwiched inner operator
in the reference eigenbasis. -/
theorem sandwichedRenyiInner_referenceSpectralPinching_eq_pinchingMap
    (ρ σ : State a) (α : ℝ) :
    sandwichedRenyiInner
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ α =
      (ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingMap
        (sandwichedRenyiInner ρ σ α) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.matrix s
  let D : CMatrix a :=
    Matrix.diagonal
      (fun i => ((σ.pos.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
  let Y : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  let Ydiag : CMatrix a := Matrix.diagonal fun i => Y i i
  let A : CMatrix a :=
    sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α
  let B : CMatrix a := P.pinchingMap (sandwichedRenyiInner ρ σ α)
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have hC : C = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [C, D, U] using cMatrix_rpow_eq_eigenbasis_diagonal σ.pos s
  have hC_conj : star (U : CMatrix a) * C * (U : CMatrix a) = D := by
    calc
      star (U : CMatrix a) * C * (U : CMatrix a) =
          star (U : CMatrix a) * ((U : CMatrix a) * D * star (U : CMatrix a)) *
            (U : CMatrix a) := by rw [hC]
      _ = (star (U : CMatrix a) * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (U : CMatrix a)) := by noncomm_ring
      _ = D := by rw [hUstarU]; simp
  have hPρ_conj :
      star (U : CMatrix a) * (P.pinchingChannel.applyState ρ).matrix *
          (U : CMatrix a) = Ydiag := by
    simpa [P, U, Y, Ydiag] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_eigenbasis ρ σ
  have hinner_conj :
      star (U : CMatrix a) * sandwichedRenyiInner ρ σ α * (U : CMatrix a) =
        D * Y * D := by
    calc
      star (U : CMatrix a) * sandwichedRenyiInner ρ σ α * (U : CMatrix a) =
          star (U : CMatrix a) * (C * ρ.matrix * C) * (U : CMatrix a) := by
            rfl
      _ = star (U : CMatrix a) *
            (((U : CMatrix a) * D * star (U : CMatrix a)) * ρ.matrix *
              ((U : CMatrix a) * D * star (U : CMatrix a))) *
            (U : CMatrix a) := by rw [hC]
      _ = (star (U : CMatrix a) * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (U : CMatrix a)) := by
            noncomm_ring
      _ = D * Y * D := by rw [hUstarU]; simp [Y, Matrix.mul_assoc]
  have hA_conj :
      star (U : CMatrix a) * A * (U : CMatrix a) = D * Ydiag * D := by
    calc
      star (U : CMatrix a) * A * (U : CMatrix a) =
          star (U : CMatrix a) *
              (C * (P.pinchingChannel.applyState ρ).matrix * C) *
            (U : CMatrix a) := by
            rfl
      _ = star (U : CMatrix a) *
            (((U : CMatrix a) * D * star (U : CMatrix a)) *
              (P.pinchingChannel.applyState ρ).matrix *
              ((U : CMatrix a) * D * star (U : CMatrix a))) *
            (U : CMatrix a) := by rw [hC]
      _ = (star (U : CMatrix a) * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (P.pinchingChannel.applyState ρ).matrix *
              (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (U : CMatrix a)) := by
            noncomm_ring
      _ = D *
            (star (U : CMatrix a) * (P.pinchingChannel.applyState ρ).matrix *
              (U : CMatrix a)) * D := by
            rw [hUstarU]
            simp [Matrix.mul_assoc]
      _ = D * Ydiag * D := by rw [hPρ_conj]
  have hB_conj :
      star (U : CMatrix a) * B * (U : CMatrix a) =
        Matrix.diagonal (fun i => (D * Y * D) i i) := by
    simpa [B, P, U, hinner_conj] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingMap_eigenbasis
        σ.matrix σ.pos.isHermitian (sandwichedRenyiInner ρ σ α)
  have hDYD_diag :
      D * Ydiag * D = Matrix.diagonal (fun i => (D * Y * D) i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Ydiag, Matrix.mul_apply, Matrix.diagonal]
    · simp [D, Ydiag, Matrix.mul_apply, Matrix.diagonal, hij]
  have hconj : star (U : CMatrix a) * A * (U : CMatrix a) =
      star (U : CMatrix a) * B * (U : CMatrix a) := by
    rw [hA_conj, hB_conj, hDYD_diag]
  have hreconstruct_A :
      (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
        star (U : CMatrix a) = A := by
    calc
      (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
          star (U : CMatrix a) =
          ((U : CMatrix a) * star (U : CMatrix a)) * A *
            ((U : CMatrix a) * star (U : CMatrix a)) := by
            noncomm_ring
      _ = A := by rw [hUUstar]; simp
  have hreconstruct_B :
      (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
        star (U : CMatrix a) =
      (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
        star (U : CMatrix a) := by
    rw [hconj]
  have hreconstruct_B_final :
      (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
        star (U : CMatrix a) = B := by
    calc
      (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
          star (U : CMatrix a) =
          ((U : CMatrix a) * star (U : CMatrix a)) * B *
            ((U : CMatrix a) * star (U : CMatrix a)) := by
            noncomm_ring
      _ = B := by rw [hUUstar]; simp
  calc
    sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α = A := rfl
    _ = (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
          star (U : CMatrix a) := hreconstruct_A.symm
    _ = (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
          star (U : CMatrix a) := hreconstruct_B
    _ = B := hreconstruct_B_final
    _ = P.pinchingMap (sandwichedRenyiInner ρ σ α) := rfl

/-- Trace-power contraction for the sandwiched inner operator under reference
spectral pinching, in the `α ≥ 1` range. -/
theorem sandwichedRenyiInner_referenceSpectralPinching_tracePower_le_of_one_le
    (ρ σ : State a) (α : ℝ) (hα : 1 ≤ α) :
    psdTracePower
        (sandwichedRenyiInner
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        (sandwichedRenyiInner_posSemidef
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        α ≤
      psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hpinch :=
    ProjectiveMeasurement.ofHermitianEigenbasis_pinchingMap_psdTracePower_le
      σ.matrix σ.pos.isHermitian
      (X := sandwichedRenyiInner ρ σ α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (q := α) hα
  simpa [P, sandwichedRenyiInner_referenceSpectralPinching_eq_pinchingMap ρ σ α]
    using hpinch

/-- Trace-power expansion for the sandwiched inner operator under reference
spectral pinching, in the `0 ≤ α ≤ 1` range. -/
theorem sandwichedRenyiInner_referenceSpectralPinching_tracePower_ge_of_le_one
    (ρ σ : State a) (α : ℝ) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
    psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
      psdTracePower
        (sandwichedRenyiInner
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        (sandwichedRenyiInner_posSemidef
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        α := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hpinch :=
    ProjectiveMeasurement.ofHermitianEigenbasis_pinchingMap_psdTracePower_ge
      σ.matrix σ.pos.isHermitian
      (X := sandwichedRenyiInner ρ σ α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (p := α) hα_nonneg hα_le_one
  simpa [P, sandwichedRenyiInner_referenceSpectralPinching_eq_pinchingMap ρ σ α]
    using hpinch

/-- For `α > 1`, a core trace-power contraction for the sandwiched inner
operator implies the full-rank channel DPI inequality.

This is the non-circular bridge from the operator-inequality part of the
sandwiched-Renyi proof route to the logarithmic public statement. It does not
assume DPI; the remaining hard obligation is the trace-power inequality in
`hpower`. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_tracePower_le_of_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α)
    (hpower :
      psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hα_ne_one : α ≠ 1 := ne_of_gt hα_gt_one
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α hα_pos hα_ne_one,
    sandwichedRenyi_eq_log2_psdTracePower_inner
      ρ σ hρ hσ α hα_pos hα_ne_one]
  have hout_pos :
      0 <
        psdTracePower
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          α :=
    sandwichedRenyiInner_psdTracePower_pos
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α
  have hlog := log2_mono_of_pos hout_pos hpower
  have hcoef_nonneg : 0 ≤ 1 / (α - 1) := by
    exact le_of_lt (one_div_pos.2 (sub_pos.mpr hα_gt_one))
  exact mul_le_mul_of_nonneg_left hlog hcoef_nonneg

/-- For `α > 1`, a Schatten-norm contraction for the sandwiched inner operator
implies the full-rank channel DPI inequality.

This is the variational-route handoff immediately after the Holder unit-ball
step: once the channel-specific argument proves contraction of the positive
inner operator's PSD Schatten expression, the Renyi DPI follows. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_le_of_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α)
    (hnorm :
      psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hpower :
      psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α :=
    psdTracePower_le_of_psdSchattenPNorm_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      hα_pos
      (sandwichedRenyiInner_psdTracePower_pos
        (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α)
      (sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α)
      hnorm
  exact sandwichedRenyi_dataProcessing_le_of_inner_tracePower_le_of_one_lt
    ρ σ Φ hρ hσ hρΦ hσΦ α hα_gt_one hpower

/-- The reference-spectral pinching channel satisfies the full-rank sandwiched
Renyi DPI in the `α > 1` range. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_one_lt
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α (by linarith) (ne_of_gt hα_gt_one) := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have hσP : (P.pinchingChannel.applyState σ).matrix.PosDef := by
    rw [hσP_eq]
    exact hσ
  have hpower :
      psdTracePower
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          α ≤
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α := by
    simpa [hσP_eq, P] using
      sandwichedRenyiInner_referenceSpectralPinching_tracePower_le_of_one_le
        ρ σ α (le_of_lt hα_gt_one)
  have hDPI :=
    sandwichedRenyi_dataProcessing_le_of_inner_tracePower_le_of_one_lt
      ρ σ P.pinchingChannel hρ hσ hρP hσP α hα_gt_one hpower
  simpa [sandwichedRenyi_dataProcessing_channel_statement, P, hσP_eq] using hDPI

/-- For `α > 1`, the Holder variational formula reduces full-rank channel DPI
to a unit-ball trace-pairing bound for every positive output-side dual witness.

The remaining channel-specific obligation is `hbound`: transport an arbitrary
PSD `q`-unit-ball witness on the output side through the Heisenberg adjoint (or
an equivalent Stinespring/pinching construction) and compare the resulting trace
pairing with the input-side sandwiched inner operator. -/
theorem sandwichedRenyi_dataProcessing_le_of_traceHolderUnitBall_le_of_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    (hbound : ∀ B : CMatrix b, ∀ hB : B.PosSemidef,
      psdTracePower B hB q ≤ 1 →
        ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re ≤
          psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
            (sandwichedRenyiInner_posSemidef ρ σ α) α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  have hnorm :
      psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α :=
    psdSchattenPNorm_le_of_traceHolderUnitBall_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      hpq
      hbound
  exact sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_le_of_one_lt
    ρ σ Φ hρ hσ hρΦ hσΦ α hα_gt_one hnorm

/-- Full-rank α > 1 channel DPI follows from the rotated-Kraus adjoint
`q`-unit-ball contraction.

This theorem is the final Lean handoff to the missing noncommutative
interpolation lemma: it proves the complete logarithmic α > 1 DPI inequality
once the rotated adjoint is known to contract positive `q`-unit balls. It does
not assume DPI itself. -/
theorem sandwichedRenyi_dataProcessing_le_of_rotatedKrausAdjoint_qBall_of_one_lt
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    (hrotated :
      ∀ B : CMatrix b, ∀ hB : B.PosSemidef,
        psdTracePower B hB q ≤ 1 →
          psdTracePower
            (MatrixMap.krausAdjoint
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
            (MatrixMap.krausAdjoint_mapsPositive
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB)
            q ≤ 1) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  exact
    sandwichedRenyi_dataProcessing_le_of_traceHolderUnitBall_le_of_one_lt
      ρ σ Φ hρ hσ hρΦ hσΦ α q hα_gt_one hpq
      (fun B hB hBq =>
        sandwichedRenyi_traceHolderUnitBall_le_of_rotatedKrausAdjoint_qBall
          K ρ σ Φ hK hσ α q hpq hrotated B hB hBq)

/-- α > 1 Beigi-route trace-power contraction for arbitrary input states and
positive-definite references.

This is the numeric core behind the logarithmic high-`α` DPI.  Unlike the
real-valued `sandwichedRenyi` wrapper below, it does not require the input
state or the output state to be positive definite; the new positivity side
conditions come only from the positive-definite references. -/
theorem sandwichedRenyiInner_tracePower_le_of_one_lt_channel
    (ρ σ : State a) (Φ : Channel a b)
    (hσ : σ.matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
        (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
      psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  let q : ℝ := Real.conjExponent α
  have hpq : α.HolderConjugate q :=
    Real.HolderConjugate.conjExponent hα_gt_one
  have hnorm :
      psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α :=
    psdSchattenPNorm_le_of_traceHolderUnitBall_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      hpq
      (fun B hB hBq =>
        sandwichedRenyi_traceHolderUnitBall_le_of_rotatedKrausAdjoint_qBall
          K ρ σ Φ hK hσ α q hpq
          (fun B hB hBq =>
            sandwichedRenyiRotatedKrausAdjoint_qBall_of_beigi
              K σ Φ hK hσ hσΦ α q hα_gt_one hpq hB hBq)
          B hB hBq)
  exact
    psdTracePower_le_of_psdSchattenPNorm_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (lt_trans zero_lt_one hα_gt_one)
      (sandwichedRenyiInner_psdTracePower_pos_of_reference_posDef
        (Φ.applyState ρ) (Φ.applyState σ) hσΦ α)
      (sandwichedRenyiInner_psdTracePower_pos_of_reference_posDef ρ σ hσ α)
      hnorm

/-- α > 1 full-rank sandwiched Renyi DPI for a general channel with an explicit
finite Kraus realization.

This theorem is the current Beigi-route completion for the full-rank
`State + PosDef` local domain: it uses the proved rotated-adjoint `q`-ball
contraction and does not assume DPI or a contraction hypothesis. It is still
not the full source statement because the source statement allows a positive
semidefinite, not necessarily full-rank, reference operator and also includes
the `1 / 2 ≤ α < 1` range. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_one_lt
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α (by linarith) (ne_of_gt hα_gt_one) := by
  unfold sandwichedRenyi_dataProcessing_channel_statement
  exact
    sandwichedRenyi_dataProcessing_le_of_rotatedKrausAdjoint_qBall_of_one_lt
      K ρ σ Φ hK hρ hσ hρΦ hσΦ α q hα_gt_one hpq
      (fun B hB hBq =>
        sandwichedRenyiRotatedKrausAdjoint_qBall_of_beigi
          K σ Φ hK hσ hσΦ α q hα_gt_one hpq hB hBq)

/-- α > 1 full-rank sandwiched Renyi DPI for an arbitrary finite-dimensional
channel.

This removes the explicit Kraus-realization parameter from
`sandwichedRenyi_dataProcessing_channel_statement_of_one_lt`: the channel's
Choi-positive complete-positivity proof supplies a finite Kraus family, and the
Beigi weighted-map contraction theorem proves the local full-rank statement. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α (by linarith) (ne_of_gt hα_gt_one) := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  exact
    sandwichedRenyi_dataProcessing_channel_statement_of_one_lt
      K ρ σ Φ hK hρ hσ hρΦ hσΦ
      α (Real.conjExponent α) hα_gt_one
      (Real.HolderConjugate.conjExponent hα_gt_one)

/-- Full-rank sandwiched Renyi divergences are nonnegative in the proved
`α > 1` range.

The proof applies the already-established general-channel DPI to the terminal
one-outcome measurement channel. Both output states are the unique unit-system
state, whose self-divergence is zero. -/
theorem sandwichedRenyi_nonneg_of_one_lt
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    0 ≤ sandwichedRenyi ρ σ hρ hσ α
      (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) := by
  let Φ : Channel a PUnit.{1} := terminalMeasureChannel a
  have hρΦ_eq : Φ.applyState ρ = State.unit := by
    simpa [Φ] using terminalMeasureChannel_applyState ρ
  have hσΦ_eq : Φ.applyState σ = State.unit := by
    simpa [Φ] using terminalMeasureChannel_applyState σ
  have hunit_pos : (State.unit.matrix : CMatrix PUnit.{1}).PosDef := by
    change (1 : CMatrix PUnit.{1}).PosDef
    exact Matrix.PosDef.one
  have hρΦ_pos : (Φ.applyState ρ).matrix.PosDef := by
    rw [hρΦ_eq]
    exact hunit_pos
  have hσΦ_pos : (Φ.applyState σ).matrix.PosDef := by
    rw [hσΦ_eq]
    exact hunit_pos
  have hDPI_stmt :
      sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
        hρ hσ hρΦ_pos hσΦ_pos α
        (by linarith) (ne_of_gt hα_gt_one) :=
    sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
      ρ σ Φ hρ hσ hρΦ_pos hσΦ_pos α hα_gt_one
  unfold sandwichedRenyi_dataProcessing_channel_statement at hDPI_stmt
  have hleft :
      sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ)
          hρΦ_pos hσΦ_pos α
          (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) = 0 := by
    simpa [hρΦ_eq, hσΦ_eq] using
      sandwichedRenyi_self_eq_zero State.unit hunit_pos α
        (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one)
  rw [hleft] at hDPI_stmt
  exact hDPI_stmt

/-- Full-rank sandwiched Renyi DPI for the proved parts of the public range:
the fidelity endpoint `α = 1/2` and the Beigi interpolation range `α > 1`.

This gives a single non-circular entry point for the subrange already proved in
this sprint. It deliberately does not cover the strict subunit interval
`1 / 2 < α < 1`, whose remaining blocker is the conditional-duality/minimax
route. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_eq_half_or_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_range : α = 1 / 2 ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ hρ hσ hρΦ hσΦ
      α
      (by
        rcases hα_range with rfl | hgt
        · norm_num
        · linarith)
      (by
        rcases hα_range with rfl | hgt
        · norm_num
        · exact ne_of_gt hgt) := by
  rcases hα_range with rfl | hgt
  · simpa using
      sandwichedRenyi_dataProcessing_channel_statement_half
        ρ σ Φ hρ hσ hρΦ hσΦ
  · exact
      sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
        ρ σ Φ hρ hσ hρΦ hσΦ α hgt

/-- For `1 / 2 ≤ α < 1`, the negative logarithmic prefactor reverses the
trace-power order: a core trace-power expansion for the sandwiched inner
operator implies the full-rank channel DPI inequality.

This packages the precise operator inequality needed for the subunit Renyi
range without assuming DPI as a hypothesis. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hpower :
      psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α hα_pos hα_ne_one,
    sandwichedRenyi_eq_log2_psdTracePower_inner
      ρ σ hρ hσ α hα_pos hα_ne_one]
  have hin_pos :
      0 <
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α :=
    sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  have hlog := log2_mono_of_pos hin_pos hpower
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  exact mul_le_mul_of_nonpos_left hlog hcoef_nonpos

/-- Low-`α` `Q`-functional form of the full-rank DPI reduction.

For `α < 1`, the logarithmic prefactor in `D̃_α` is negative, so the data
processing inequality is obtained from the reverse `Q`-functional inequality
`Q_α(ρ, σ) ≤ Q_α(Φρ, Φσ)`.  This is the bridge from the PSD-friendly
matrix-level route back to the current `State + PosDef` public theorem
surface. -/
theorem sandwichedRenyi_dataProcessing_le_of_lowAlphaQ_ge
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hQ :
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α ≤
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ).pos α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  exact
    sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      (by
        simpa [sandwichedRenyiQ_eq_psdTracePower_inner] using hQ)

/-- The reference-spectral pinching channel satisfies the full-rank sandwiched
Renyi DPI in the `1 / 2 ≤ α < 1` range. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_lt_one
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α hα_half (ne_of_lt hα_lt_one) := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have hσP : (P.pinchingChannel.applyState σ).matrix.PosDef := by
    rw [hσP_eq]
    exact hσ
  have hpower :
      psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdTracePower
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          α := by
    simpa [hσP_eq, P] using
      sandwichedRenyiInner_referenceSpectralPinching_tracePower_ge_of_le_one
        ρ σ α (by linarith) (le_of_lt hα_lt_one)
  have hDPI :=
    sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
      ρ σ P.pinchingChannel hρ hσ hρP hσP α hα_half hα_lt_one hpower
  simpa [sandwichedRenyi_dataProcessing_channel_statement, P, hσP_eq] using hDPI

/-- The reference-spectral pinching channel satisfies the local full-rank
sandwiched Renyi DPI statement throughout the source range
`1 / 2 ≤ α < 1` or `1 < α`. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α
      (by
        rcases hα_range with hlt | hgt
        · exact hlt.1
        · linarith)
      (by
        rcases hα_range with hlt | hgt
        · exact ne_of_lt hlt.2
        · exact ne_of_gt hgt) := by
  rcases hα_range with hlt | hgt
  · exact sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_lt_one
      ρ σ hρ hσ hρP α hlt.1 hlt.2
  · exact sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_one_lt
      ρ σ hρ hσ hρP α hgt

/-- For `1 / 2 ≤ α < 1`, a Schatten-norm expansion for the sandwiched inner
operator implies the full-rank channel DPI inequality.

This is the matching reverse-Holder handoff for the subunit Renyi range: once
the proof route establishes that the input inner operator's PSD Schatten
expression is bounded by the output inner operator's expression, the negative
Renyi prefactor converts it to DPI. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_ge_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hnorm :
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hpower :
      psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α :=
    psdTracePower_le_of_psdSchattenPNorm_le
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      hα_pos
      (sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α)
      (sandwichedRenyiInner_psdTracePower_pos
        (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α)
      hnorm
  exact sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
    ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one hpower

/-- Reverse-Holder witness handoff for the `1 / 2 ≤ α < 1` channel DPI route.

The remaining channel-specific task in this range is to construct a normalized
PSD side-state `N` supporting the input sandwiched inner operator and prove the
displayed trace objective is controlled by the output PSD Schatten expression.
This theorem then converts that source-shaped reverse-Holder bound into the
full-rank logarithmic DPI inequality. -/
theorem sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    {N : CMatrix a} (hN : N.PosSemidef) (hNtr : N.trace.re = 1)
    (hSupport : Matrix.Supports (sandwichedRenyiInner ρ σ α) N)
    (htrace_le :
      ((sandwichedRenyiInner ρ σ α * CFC.rpow N (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hnorm :
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          α :=
    psdSchattenPNorm_le_of_reverseHolder_trace_le
      (sandwichedRenyiInner_posSemidef ρ σ α) hN hNtr hSupport
      hα_pos hα_lt_one htrace_le
  exact
    sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_ge_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one hnorm

/-- All-side-state reverse-Holder handoff for the `1 / 2 ≤ α < 1` channel
DPI route.

Because the full-rank input sandwiched inner operator has positive
`α`-power trace, the reverse-Holder optimizer supplies a normalized supporting
side-state. Thus it is enough to prove the displayed trace bound for every
normalized PSD side-state supporting the input inner operator. -/
theorem sandwichedRenyi_dataProcessing_le_of_all_reverseHolder_sideStates_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_all :
      ∀ {N : CMatrix a}, N.PosSemidef → N.trace.re = 1 →
        Matrix.Supports (sandwichedRenyiInner ρ σ α) N →
          ((sandwichedRenyiInner ρ σ α *
              CFC.rpow N (1 - 1 / α)).trace).re ≤
            psdSchattenPNorm
              (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
              (sandwichedRenyiInner_posSemidef
                (Φ.applyState ρ) (Φ.applyState σ) α)
              α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  obtain ⟨N, hN, hNtr, hSupport, _hattain⟩ :=
    exists_psdTraceReverseHolder_sideState_attaining
      (sandwichedRenyiInner_posSemidef ρ σ α) hα_pos
      (sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α)
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      hN hNtr hSupport (htrace_all hN hNtr hSupport)

/-- Full-rank side-state handoff for the `1 / 2 ≤ α < 1` channel DPI route.

The input sandwiched inner operator is full-rank in the local `State + PosDef`
domain. Its explicit reverse-Holder optimizer is therefore also full-rank, so
the remaining channel-specific low-`α` task can be stated using only
normalized positive-definite side-states. This is the form needed before using
negative powers of the side-state in a source-faithful duality argument. -/
theorem sandwichedRenyi_dataProcessing_le_of_all_reverseHolder_fullRank_sideStates_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_all :
      ∀ {N : CMatrix a}, N.PosDef → N.trace.re = 1 →
          ((sandwichedRenyiInner ρ σ α *
              CFC.rpow N (1 - 1 / α)).trace).re ≤
            psdSchattenPNorm
              (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
              (sandwichedRenyiInner_posSemidef
                (Φ.applyState ρ) (Φ.applyState σ) α)
              α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hMdef : M.PosDef := by
    simpa [M] using sandwichedRenyiInner_posDef ρ σ hρ hσ α
  have hSpos : 0 < psdTracePower M hM α := by
    simpa [M, hM] using sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  have hNdef :
      (psdTraceReverseHolderOptimizer M hM α).PosDef :=
    _root_.QIT.psdTraceReverseHolderOptimizer_posDef_of_posDef hM hMdef hSpos
  rcases _root_.QIT.psdTraceReverseHolderOptimizer_props hM hα_pos hSpos with
    ⟨hN, hNtr, _hSupport, _hattain⟩
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      (by simpa [M, hM] using hN)
      (by simpa [M, hM] using hNtr)
      (by
        simpa [M, hM] using
          Matrix.Supports.of_right_posDef M
            (psdTraceReverseHolderOptimizer M hM α) hNdef)
      (by simpa [M, hM] using htrace_all hNdef hNtr)

/-- The reverse-Holder trace objective is strictly positive for full-rank
inputs and full-rank side-states.

This isolates the finite-dimensional positivity fact needed by the low-`α`
route before applying negative side-state powers or logarithmic conversions. -/
theorem sandwichedRenyi_reverseHolder_fullRank_sideState_trace_pos
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) {N : CMatrix a} (hN : N.PosDef) :
    0 <
      ((sandwichedRenyiInner ρ σ α *
        CFC.rpow N (1 - 1 / α)).trace).re := by
  haveI : Nonempty a := ρ.nonempty
  exact _root_.QIT.trace_mul_posDef_re_pos
    (sandwichedRenyiInner_posDef ρ σ hρ hσ α)
    (_root_.QIT.cMatrix_rpow_posDef_of_posDef hN (1 - 1 / α))

/-- The explicit reverse-Holder optimizer has exactly the input PSD Schatten
value as its trace objective.

This is the concrete equality behind the low-`α` optimizer handoff: after this
point, the only missing channel-specific inequality is to compare this exact
input-side optimizer value with the output-side PSD Schatten expression. -/
theorem sandwichedRenyi_reverseHolder_optimizer_trace_eq_schatten
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) :
    let M : CMatrix a := sandwichedRenyiInner ρ σ α
    let hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
    ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
        (1 - 1 / α)).trace).re =
      psdSchattenPNorm M hM α := by
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hSpos : 0 < psdTracePower M hM α := by
    simpa [M, hM] using sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  rcases _root_.QIT.psdTraceReverseHolderOptimizer_props hM hα_pos hSpos with
    ⟨_hN, _hNtr, _hSupport, hattain⟩
  simpa [M, hM] using hattain.symm

/-- Source-shaped form of the explicit low-`α` reverse-Holder optimizer for a
sandwiched Renyi inner operator: it is the normalized positive `α`-power of the
inner operator.

This is the concrete power-state form needed by the conditional-duality/minimax
route for the strict subunit interval. -/
theorem sandwichedRenyi_reverseHolder_optimizer_eq_normalized_inner_power
    (ρ σ : State a) (α : ℝ) :
    let M : CMatrix a := sandwichedRenyiInner ρ σ α
    let hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
    psdTraceReverseHolderOptimizer M hM α =
      (((psdTracePower M hM α)⁻¹ : ℝ) : ℂ) • CFC.rpow M α := by
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  simpa [M, hM] using
    (_root_.QIT.psdTraceReverseHolderOptimizer_eq_inv_tracePower_smul_rpow
      (M := M) hM (p := α))

/-- The low-`α` reverse-Holder optimizer trace bound is fully proved for the
reference spectral pinching channel.

This is the first nontrivial closed instance of the strict-subunit optimizer
obligation: it combines the already-proved pinching trace-power expansion with
the explicit reverse-Holder optimizer equality. The general-channel case still
requires the conditional-duality/minimax route. -/
theorem sandwichedRenyi_referenceSpectralPinching_reverseHolder_optimizer_trace_le_of_lt_one
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    let P : ProjectiveMeasurement a a :=
      ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
    let M : CMatrix a := sandwichedRenyiInner ρ σ α
    let hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
    ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
        (1 - 1 / α)).trace).re ≤
      psdSchattenPNorm
        (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
          (P.pinchingChannel.applyState σ) α)
        (sandwichedRenyiInner_posSemidef
          (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
        α := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hα_pos : 0 < α := by linarith
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have htrace_eq :
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re =
        psdSchattenPNorm M hM α := by
    simpa [M, hM] using
      sandwichedRenyi_reverseHolder_optimizer_trace_eq_schatten
        ρ σ hρ hσ α hα_pos
  have hpower :
      psdTracePower M hM α ≤
        psdTracePower
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) σ α)
          α := by
    simpa [M, hM, P] using
      sandwichedRenyiInner_referenceSpectralPinching_tracePower_ge_of_le_one
        ρ σ α (by linarith) (le_of_lt hα_lt_one)
  have hnorm :
      psdSchattenPNorm M hM α ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) σ α)
          α :=
    _root_.QIT.psdSchattenPNorm_le_of_psdTracePower_le
      hM
      (sandwichedRenyiInner_posSemidef
        (P.pinchingChannel.applyState ρ) σ α)
      hα_pos hpower
  calc
    ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
        (1 - 1 / α)).trace).re =
        psdSchattenPNorm M hM α := htrace_eq
    _ ≤ psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) σ α)
          α := hnorm
    _ = psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          α := by
          rw [hσP_eq]

/-- Single-obligation optimizer handoff for the `1 / 2 ≤ α < 1` channel DPI
route.

The previous all-side-state form is equivalent to a source-shaped variational
argument, but the actual remaining proof obligation can be concentrated on the
explicit full-rank reverse-Holder optimizer for the input sandwiched inner
operator. Proving the displayed trace bound for that optimizer is now enough
to obtain the full-rank logarithmic DPI inequality in the subunit range. -/
theorem sandwichedRenyi_dataProcessing_le_of_reverseHolder_optimizer_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_le :
      let M : CMatrix a := sandwichedRenyiInner ρ σ α
      let hM : M.PosSemidef := by
        simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ) α)
          α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hSpos : 0 < psdTracePower M hM α := by
    simpa [M, hM] using sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  rcases _root_.QIT.psdTraceReverseHolderOptimizer_props hM hα_pos hSpos with
    ⟨hN, hNtr, hSupport, _hattain⟩
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      (by simpa [M, hM] using hN)
      (by simpa [M, hM] using hNtr)
      (by simpa [M, hM] using hSupport)
      (by simpa [M, hM] using htrace_le)

/-- Statement-form strict-subunit handoff for the remaining low-`α` proof
obligation.

This theorem does not prove the missing reverse-Holder optimizer inequality.
It records the exact final shape needed to turn that future inequality into the
general-channel full-rank DPI statement for `1 / 2 ≤ α < 1`. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_reverseHolder_optimizer_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_le :
      let M : CMatrix a := sandwichedRenyiInner ρ σ α
      let hM : M.PosSemidef := by
        simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ) α)
          α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ hρ hσ hρΦ hσΦ
      α hα_half (ne_of_lt hα_lt_one) := by
  unfold sandwichedRenyi_dataProcessing_channel_statement
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_optimizer_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one htrace_le

/-- The reference-spectral pinching channel satisfies the strict-subunit
full-rank DPI through the reverse-Holder optimizer route.

This is a proof-route check rather than a new public endpoint: it shows that
the optimizer trace bound above is strong enough to feed the general
`reverseHolder_optimizer_trace_le` handoff. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_lt_one_via_optimizer
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α hα_half (ne_of_lt hα_lt_one) := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have hσP : (P.pinchingChannel.applyState σ).matrix.PosDef := by
    rw [hσP_eq]
    exact hσ
  have htrace_le :
      let M : CMatrix a := sandwichedRenyiInner ρ σ α
      let hM : M.PosSemidef := by
        simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          α := by
    simpa [P] using
      sandwichedRenyi_referenceSpectralPinching_reverseHolder_optimizer_trace_le_of_lt_one
        ρ σ hρ hσ α hα_half hα_lt_one
  have hDPI :=
    sandwichedRenyi_dataProcessing_channel_statement_of_reverseHolder_optimizer_trace_le_of_lt_one
      ρ σ P.pinchingChannel hρ hσ hρP hσP α hα_half hα_lt_one htrace_le
  simpa [sandwichedRenyi_dataProcessing_channel_statement, P, hσP_eq] using hDPI

/-- Applying the identity channel does not change the sandwiched Renyi
divergence. This small API lemma keeps later DPI sanity checks independent from
the concrete Kraus implementation of `Channel.idChannel`. -/
@[simp]
theorem sandwichedRenyi_idChannel_applyState
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρid : ((Channel.idChannel a).applyState ρ).matrix.PosDef)
    (hσid : ((Channel.idChannel a).applyState σ).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi ((Channel.idChannel a).applyState ρ)
        ((Channel.idChannel a).applyState σ) hρid hσid α hα_pos hα_ne_one =
      sandwichedRenyi ρ σ hρ hσ α hα_pos hα_ne_one := by
  unfold sandwichedRenyi
  simp [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus]

/-- Identity-channel sanity check for the generalized statement surface.

This is a genuine proved specialization and an API check for the `Channel a b`
statement shape; it is not the sandwiched Renyi DPI proof required to close
`m7-sandwiched-renyi-dpi`. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_idChannel
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ (Channel.idChannel a) hρ hσ
      (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ)
      (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ)
      α hα hα_ne_one := by
  unfold sandwichedRenyi_dataProcessing_channel_statement
  exact le_of_eq (sandwichedRenyi_idChannel_applyState ρ σ hρ hσ _ _ α (by linarith) hα_ne_one)

/-- A proved state-level DPI instance remains true after tensoring both inputs
with the same untouched full-rank side-information pair.

This is a reusable lifting step for later tensor-power/asymptotic DPI work: it
uses the already-proved product additivity of `sandwichedRenyi`, not the deep DPI
theorem itself. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_prod_idChannel
    (ρ₁ σ₁ : State a) (ρ₂ σ₂ : State c) (Φ : Channel a b)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ₁).matrix.PosDef) (hσΦ : (Φ.applyState σ₁).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hΦ : sandwichedRenyi_dataProcessing_channel_statement ρ₁ σ₁ Φ
      hρ₁ hσ₁ hρΦ hσΦ α hα hα_ne_one) :
    sandwichedRenyi_dataProcessing_channel_statement (ρ₁.prod ρ₂) (σ₁.prod σ₂)
      (Φ.prod (Channel.idChannel c))
      (State.prod_posDef hρ₁ hρ₂) (State.prod_posDef hσ₁ hσ₂)
      (by
        rw [Channel.applyState_prod]
        exact State.prod_posDef hρΦ
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ₂))
      (by
        rw [Channel.applyState_prod]
        exact State.prod_posDef hσΦ
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ₂))
      α hα hα_ne_one := by
  have hα_pos : 0 < α := by linarith
  unfold sandwichedRenyi_dataProcessing_channel_statement at hΦ ⊢
  calc
    sandwichedRenyi ((Φ.prod (Channel.idChannel c)).applyState (ρ₁.prod ρ₂))
        ((Φ.prod (Channel.idChannel c)).applyState (σ₁.prod σ₂)) _ _
        α _ hα_ne_one =
      sandwichedRenyi ((Φ.applyState ρ₁).prod ((Channel.idChannel c).applyState ρ₂))
        ((Φ.applyState σ₁).prod ((Channel.idChannel c).applyState σ₂)) _ _
        α hα_pos hα_ne_one := by
          unfold sandwichedRenyi
          simp [Channel.applyState_prod]
    _ =
      sandwichedRenyi (Φ.applyState ρ₁) (Φ.applyState σ₁) hρΦ hσΦ
          α hα_pos hα_ne_one +
        sandwichedRenyi ((Channel.idChannel c).applyState ρ₂)
          ((Channel.idChannel c).applyState σ₂)
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ₂)
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ₂)
          α hα_pos hα_ne_one := by
          rw [State.sandwichedRenyi_prod (Φ.applyState ρ₁) (Φ.applyState σ₁)
            ((Channel.idChannel c).applyState ρ₂) ((Channel.idChannel c).applyState σ₂)
            hρΦ hσΦ
            (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ₂)
            (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ₂)
            α hα_pos hα_ne_one]
    _ =
      sandwichedRenyi (Φ.applyState ρ₁) (Φ.applyState σ₁) hρΦ hσΦ
          α hα_pos hα_ne_one +
        sandwichedRenyi ρ₂ σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
          rw [sandwichedRenyi_idChannel_applyState ρ₂ σ₂ hρ₂ hσ₂ _ _
            α hα_pos hα_ne_one]
    _ ≤ sandwichedRenyi ρ₁ σ₁ hρ₁ hσ₁ α hα_pos hα_ne_one +
        sandwichedRenyi ρ₂ σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
          exact add_le_add hΦ (le_refl _)
    _ = sandwichedRenyi (ρ₁.prod ρ₂) (σ₁.prod σ₂)
        (State.prod_posDef hρ₁ hρ₂) (State.prod_posDef hσ₁ hσ₂)
        α hα_pos hα_ne_one := by
          rw [State.sandwichedRenyi_prod ρ₁ σ₁ ρ₂ σ₂
            hρ₁ hσ₁ hρ₂ hσ₂ α hα_pos hα_ne_one]

/-- The class of channels satisfying the local full-rank sandwiched Renyi DPI
statement is closed under channel composition.

This does not prove DPI for every channel by itself. It is the composition step
needed by reduction routes that prove DPI for primitive maps and then assemble
larger channels from them. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_comp
    (ρ σ : State a) (Φ : Channel a b) (Ψ : Channel b c)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (hρΨΦ : (Ψ.applyState (Φ.applyState ρ)).matrix.PosDef)
    (hσΨΦ : (Ψ.applyState (Φ.applyState σ)).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hΦ : sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α hα hα_ne_one)
    (hΨ : sandwichedRenyi_dataProcessing_channel_statement (Φ.applyState ρ)
      (Φ.applyState σ) Ψ hρΦ hσΦ hρΨΦ hσΨΦ α hα hα_ne_one) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ (Ψ.comp Φ) hρ hσ
      (by rw [Channel.applyState_comp]; exact hρΨΦ)
      (by rw [Channel.applyState_comp]; exact hσΨΦ)
      α hα hα_ne_one := by
  have hα_pos : 0 < α := by linarith
  unfold sandwichedRenyi_dataProcessing_channel_statement at hΦ hΨ ⊢
  calc
    sandwichedRenyi ((Ψ.comp Φ).applyState ρ) ((Ψ.comp Φ).applyState σ) _ _
        α _ hα_ne_one =
      sandwichedRenyi (Ψ.applyState (Φ.applyState ρ))
        (Ψ.applyState (Φ.applyState σ)) hρΨΦ hσΨΦ α hα_pos hα_ne_one := by
          unfold sandwichedRenyi
          simp [Channel.applyState_comp]
    _ ≤ sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ)
        hρΦ hσΦ α hα_pos hα_ne_one := hΨ
    _ ≤ sandwichedRenyi ρ σ hρ hσ α hα_pos hα_ne_one := hΦ

/-- Reference-spectral pinching reduces the sandwiched Renyi expression to a
finite classical power sum in the reference eigenbasis.

This is a non-circular endpoint for the Tomamichel pinching route: once the
pinched state is known to be full-rank in the reference eigenbasis, its
sandwiched Renyi divergence against the reference state is exactly the
classical Renyi power-sum expression for the two eigenbasis distributions. -/
theorem sandwichedRenyi_referenceSpectralPinching_eq_classicalPowerSum
    (ρ σ : State a)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
        ).applyState ρ).matrix.PosDef)
    (hσ : σ.matrix.PosDef)
    (hp_pos : ∀ i, 0 < (ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let Pρ : State a :=
    ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
      ).applyState ρ
  let p : a → ℝ≥0 := ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ
  let q : a → ℝ≥0 := ProjectiveMeasurement.stateEigenvalueProb σ
  let hp_sum : ∑ i, p i = 1 := ProjectiveMeasurement.eigenbasisDiagonalProb_sum ρ σ
  let hq_sum : ∑ i, q i = 1 := ProjectiveMeasurement.stateEigenvalueProb_sum σ
  let ρdiag : State a := Classical.diagonalState p hp_sum
  let σdiag : State a := Classical.diagonalState q hq_sum
  have hρdiag_pos : ρdiag.matrix.PosDef :=
    Classical.diagonalState_posDef p hp_sum hp_pos
  have hσdiag_pos : σdiag.matrix.PosDef :=
    Classical.diagonalState_posDef q hq_sum
      (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
  have hPρ_eq : Pρ = ρdiag.unitaryConj U := by
    apply State.ext
    calc
      Pρ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((p i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [Pρ, p, U] using
              ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_matrix_eq_unitary_diagonalProb
                ρ σ
      _ = (ρdiag.unitaryConj U).matrix := by
            simp [ρdiag, State.unitaryConj, Classical.diagonalState_matrix]
  have hσ_eq : σ = σdiag.unitaryConj U := by
    apply State.ext
    calc
      σ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((q i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [q, U] using
              ProjectiveMeasurement.state_matrix_eq_unitary_diagonalEigenvalueProb σ
      _ = (σdiag.unitaryConj U).matrix := by
            simp [σdiag, State.unitaryConj, Classical.diagonalState_matrix]
  calc
    sandwichedRenyi Pρ σ hρP hσ α hα_pos hα_ne_one =
        sandwichedRenyi (ρdiag.unitaryConj U) (σdiag.unitaryConj U)
          (ρdiag.unitaryConj_posDef U hρdiag_pos)
          (σdiag.unitaryConj_posDef U hσdiag_pos)
          α hα_pos hα_ne_one := by
          unfold sandwichedRenyi
          simp [hPρ_eq, hσ_eq]
    _ = sandwichedRenyi ρdiag σdiag hρdiag_pos hσdiag_pos α hα_pos hα_ne_one := by
          exact sandwichedRenyi_unitaryConj ρdiag σdiag U hρdiag_pos hσdiag_pos
            α hα_pos hα_ne_one
    _ = (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
          simpa [ρdiag, σdiag, p, q, hp_sum, hq_sum] using
            sandwichedRenyi_diagonalState_eq_classicalPowerSum p q hp_sum hq_sum
              hp_pos (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
              α hα_pos hα_ne_one

/-- Reference-spectral pinching reduces the Petz Renyi expression to the same
finite classical power sum in the reference eigenbasis. -/
theorem petzRenyi_referenceSpectralPinching_eq_classicalPowerSum
    (ρ σ : State a)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
        ).applyState ρ).matrix.PosDef)
    (hσ : σ.matrix.PosDef)
    (hp_pos : ∀ i, 0 < (ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    petzRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let Pρ : State a :=
    ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
      ).applyState ρ
  let p : a → ℝ≥0 := ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ
  let q : a → ℝ≥0 := ProjectiveMeasurement.stateEigenvalueProb σ
  let hp_sum : ∑ i, p i = 1 := ProjectiveMeasurement.eigenbasisDiagonalProb_sum ρ σ
  let hq_sum : ∑ i, q i = 1 := ProjectiveMeasurement.stateEigenvalueProb_sum σ
  let ρdiag : State a := Classical.diagonalState p hp_sum
  let σdiag : State a := Classical.diagonalState q hq_sum
  have hρdiag_pos : ρdiag.matrix.PosDef :=
    Classical.diagonalState_posDef p hp_sum hp_pos
  have hσdiag_pos : σdiag.matrix.PosDef :=
    Classical.diagonalState_posDef q hq_sum
      (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
  have hPρ_eq : Pρ = ρdiag.unitaryConj U := by
    apply State.ext
    calc
      Pρ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((p i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [Pρ, p, U] using
              ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_matrix_eq_unitary_diagonalProb
                ρ σ
      _ = (ρdiag.unitaryConj U).matrix := by
            simp [ρdiag, State.unitaryConj, Classical.diagonalState_matrix]
  have hσ_eq : σ = σdiag.unitaryConj U := by
    apply State.ext
    calc
      σ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((q i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [q, U] using
              ProjectiveMeasurement.state_matrix_eq_unitary_diagonalEigenvalueProb σ
      _ = (σdiag.unitaryConj U).matrix := by
            simp [σdiag, State.unitaryConj, Classical.diagonalState_matrix]
  calc
    petzRenyi Pρ σ hρP hσ α hα_pos hα_ne_one =
        petzRenyi (ρdiag.unitaryConj U) (σdiag.unitaryConj U)
          (ρdiag.unitaryConj_posDef U hρdiag_pos)
          (σdiag.unitaryConj_posDef U hσdiag_pos)
          α hα_pos hα_ne_one := by
          unfold petzRenyi
          simp [hPρ_eq, hσ_eq]
    _ = petzRenyi ρdiag σdiag hρdiag_pos hσdiag_pos α hα_pos hα_ne_one := by
          exact petzRenyi_unitaryConj ρdiag σdiag U hρdiag_pos hσdiag_pos
            α hα_pos hα_ne_one
    _ = (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
          simpa [ρdiag, σdiag, p, q, hp_sum, hq_sum] using
            petzRenyi_diagonalState_eq_classicalPowerSum p q hp_sum hq_sum
              hp_pos (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
              α hα_pos hα_ne_one

/-- After pinching the first argument in the spectral basis of the full-rank
reference state, sandwiched Renyi and Petz Renyi coincide. This is the
commuting-state bridge used by the pinching proof route. -/
theorem sandwichedRenyi_referenceSpectralPinching_eq_petzRenyi
    (ρ σ : State a)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
        ).applyState ρ).matrix.PosDef)
    (hσ : σ.matrix.PosDef)
    (hp_pos : ∀ i, 0 < (ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one =
      petzRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one := by
  rw [sandwichedRenyi_referenceSpectralPinching_eq_classicalPowerSum ρ σ hρP hσ
      hp_pos α hα_pos hα_ne_one,
    petzRenyi_referenceSpectralPinching_eq_classicalPowerSum ρ σ hρP hσ
      hp_pos α hα_pos hα_ne_one]

/-- A product measurement-channel DPI instance yields the corresponding
measured-subsystem sandwiched Renyi inequality.

This bridges the source route's measurement-map language with the local channel
statement surface: proving DPI for `Channel.measure M ⊗ id` is enough to obtain
the inequality phrased using `measureSubsystemState`. -/
theorem sandwichedRenyi_measureSubsystem_le_of_dataProcessing_channel_statement
    (ρ σ : State (Prod a b)) (M : POVM c a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (hσM : (measureSubsystemState M σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hDPI : sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((Channel.measure M).prod (Channel.idChannel b)) hρ hσ
      (by simpa [measureSubsystemState] using hρM)
      (by simpa [measureSubsystemState] using hσM)
      α hα hα_ne_one) :
    sandwichedRenyi (measureSubsystemState M ρ) (measureSubsystemState M σ)
        hρM hσM α (by linarith) hα_ne_one ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one := by
  simpa [sandwichedRenyi_dataProcessing_channel_statement, measureSubsystemState] using hDPI

/-- The maximally mixed state is full-rank on a nonempty finite system. -/
theorem maximallyMixed_posDef [Nonempty a] :
    (maximallyMixed a).matrix.PosDef := by
  have hcard_pos : 0 < ((Fintype.card a : ℝ)⁻¹ : ℝ) := by
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance)
  have hcard_pos_complex : (0 : ℂ) < (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hcard_pos
  rw [maximallyMixed_matrix]
  exact (IsStrictlyPositive.smul hcard_pos_complex
    (Matrix.PosDef.isStrictlyPositive (Matrix.PosDef.one : (1 : CMatrix a).PosDef))).posDef

/-- The normalized product reference `π_A ⊗ σ_B` is full-rank whenever
`σ_B` is full-rank. -/
theorem maximallyMixed_prod_posDef [Nonempty a]
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ((maximallyMixed a).prod σ).matrix.PosDef :=
  State.prod_posDef (maximallyMixed_posDef (a := a)) hσ

/-- Conditional Renyi's unnormalized reference `I_A ⊗ σ_B` is the dimension
factor times the normalized product reference `π_A ⊗ σ_B`.

The state argument supplies nonemptiness of the left register without adding a
global typeclass precondition. This is the normalization bridge needed before
using the already-proved normalized sandwiched Renyi DPI in candidate-level
conditional Renyi arguments. -/
theorem conditionalRenyi_identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod
    (ρ : State (Prod a b)) (σ : State b) :
    identityTensorStateMatrix (a := a) σ =
      ((Fintype.card a : ℂ) •
        ((@maximallyMixed a _ _ (by
          rcases ρ.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ).matrix) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  simpa using identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod (a := a) σ

/-- Full-rank witness for the normalized product reference associated with a
conditional Renyi side-information state. -/
theorem conditionalRenyi_normalizedReference_posDef
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) :
    ((@maximallyMixed a _ _ (by
      rcases ρ.nonempty with ⟨x⟩
      exact ⟨x.1⟩)).prod σ).matrix.PosDef := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  simpa using maximallyMixed_prod_posDef (a := a) σ hσ

/-- Real powers of the conditional Renyi unnormalized reference split into the
dimension factor and the normalized product reference power.

This is the first matrix-level normalization step toward rewriting
conditional sandwiched Renyi candidates as `log₂ |A|` minus a normalized
sandwiched Renyi divergence. -/
theorem conditionalRenyi_identityTensorStateMatrix_rpow_eq_card_rpow_smul
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    CFC.rpow (identityTensorStateMatrix (a := a) σ) s =
      (((Fintype.card a : ℝ) ^ s : ℝ) : ℂ) •
        CFC.rpow
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ).matrix s := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by positivity
  have href_psd :
      (((maximallyMixed a).prod σ).matrix).PosSemidef :=
    (conditionalRenyi_normalizedReference_posDef ρ σ hσ).posSemidef
  rw [conditionalRenyi_identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod ρ σ]
  simpa using
    (cMatrix_rpow_real_smul_posSemidef_schatten
      (A := ((maximallyMixed a).prod σ).matrix)
      href_psd (lambda := (Fintype.card a : ℝ)) (s := s) hcard_nonneg)

/-- The conditional Renyi sandwich formed with `I_A ⊗ σ_B` is the corresponding
normalized-reference sandwich scaled by `|A|^s * |A|^s`.

This is the second algebraic normalization step for conditional candidates. -/
theorem conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
        CFC.rpow (identityTensorStateMatrix (a := a) σ) s =
      (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s : ℝ) •
        (CFC.rpow
            ((@maximallyMixed a _ _ (by
              rcases ρ.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ).matrix s *
          ρ.matrix *
            CFC.rpow
              ((@maximallyMixed a _ _ (by
                rcases ρ.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod σ).matrix s)) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  rw [conditionalRenyi_identityTensorStateMatrix_rpow_eq_card_rpow_smul ρ σ hσ s]
  simp [smul_smul, mul_assoc]

/-- The normalized product-reference sandwich used to compare conditional
Renyi candidates is positive semidefinite. -/
theorem conditionalRenyi_normalizedReference_sandwich_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    (CFC.rpow
        ((@maximallyMixed a _ _ (by
          rcases ρ.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ).matrix s *
      ρ.matrix *
        CFC.rpow
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ).matrix s).PosSemidef := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  let ν : CMatrix (Prod a b) := ((maximallyMixed a).prod σ).matrix
  let C : CMatrix (Prod a b) := CFC.rpow ν s
  have hν : ν.PosDef := by
    simpa [ν] using conditionalRenyi_normalizedReference_posDef ρ σ hσ
  have hC : C.PosSemidef := by
    simpa [C, ν] using (cMatrix_rpow_posDef_of_posDef hν s).posSemidef
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ.matrix * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same ρ.pos C
  rw [hCstar] at hinner
  simpa [ν, C] using hinner

/-- The unnormalized conditional-reference sandwich is positive semidefinite,
as a nonnegative scalar multiple of the normalized product-reference sandwich. -/
theorem conditionalRenyi_identityTensorStateMatrix_sandwich_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    (CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
      CFC.rpow (identityTensorStateMatrix (a := a) σ) s).PosSemidef := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  rw [conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul ρ σ hσ s]
  exact Matrix.PosSemidef.smul
    (conditionalRenyi_normalizedReference_sandwich_posSemidef ρ σ hσ s) (by positivity)

/-- The conditional-reference sandwich power trace differs from the normalized
product-reference sandwich power trace by the explicit dimension factor.

This is the trace-power version of
`conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul`. -/
theorem conditionalRenyi_identityTensorStateMatrix_sandwich_psdTracePower_eq_card_factor
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s p : ℝ) :
    psdTracePower
        (CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
          CFC.rpow (identityTensorStateMatrix (a := a) σ) s)
        (conditionalRenyi_identityTensorStateMatrix_sandwich_posSemidef ρ σ hσ s) p =
      (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ p) *
        psdTracePower
          (CFC.rpow
              ((@maximallyMixed a _ _ (by
                rcases ρ.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod σ).matrix s *
            ρ.matrix *
              CFC.rpow
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ).matrix s)
          (conditionalRenyi_normalizedReference_sandwich_posSemidef ρ σ hσ s) p := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  unfold psdTracePower
  rw [conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul ρ σ hσ s]
  rw [cMatrix_rpow_real_smul_posSemidef_schatten
    (conditionalRenyi_normalizedReference_sandwich_posSemidef ρ σ hσ s) (by positivity)]
  rw [Matrix.trace_smul]
  simp

/-- Specialization of the conditional-reference trace-power normalization to
the sandwiched Renyi exponent. The right side is the ordinary sandwiched Renyi
inner trace-power against the normalized product reference `π_A ⊗ σ_B`. -/
theorem conditionalRenyi_identityTensorStateMatrix_inner_tracePower_eq_card_factor
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    (CFC.rpow
        (CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
          CFC.rpow (identityTensorStateMatrix (a := a) σ) s) α).trace.re =
      (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ α) *
        psdTracePower
          (sandwichedRenyiInner ρ
            ((@maximallyMixed a _ _ (by
              rcases ρ.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ) α)
          (sandwichedRenyiInner_posSemidef ρ
            ((@maximallyMixed a _ _ (by
              rcases ρ.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ) α) α := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  intro s
  have h :=
    conditionalRenyi_identityTensorStateMatrix_sandwich_psdTracePower_eq_card_factor
      (ρ := ρ) (σ := σ) hσ s α
  simpa [psdTracePower, sandwichedRenyiInner] using h

/-- Conditional sandwiched Renyi candidates can be rewritten using the
normalized product reference `π_A ⊗ σ_B`, at the cost of an explicit dimension
factor inside the logarithm. This is the value-level handoff from the
subnormalized `I_A ⊗ σ_B` definition to the ordinary sandwiched divergence
kernel used by channel DPI. -/
theorem conditionalSandwichedRenyiCandidate_eq_log2_card_factor_mul_normalizedTracePower
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one =
      (-(1 / (α - 1))) *
        log2
          ((((Fintype.card a : ℝ) ^ ((1 - α) / (2 * α)) *
                (Fintype.card a : ℝ) ^ ((1 - α) / (2 * α))) ^ α) *
            psdTracePower
              (sandwichedRenyiInner ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α)
              (sandwichedRenyiInner_posSemidef ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α) α) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  dsimp [conditionalSandwichedRenyiCandidate]
  change (-(1 / (α - 1))) *
      log2
        ((CFC.rpow
          (CFC.rpow (identityTensorStateMatrix (a := a) σ) ((1 - α) / (2 * α)) *
            ρ.matrix *
              CFC.rpow (identityTensorStateMatrix (a := a) σ) ((1 - α) / (2 * α)))
          α).trace.re) = _
  rw [conditionalRenyi_identityTensorStateMatrix_inner_tracePower_eq_card_factor ρ σ hσ α]
  rfl

omit [DecidableEq a] in
/-- The dimension factor introduced by replacing `I_A ⊗ σ_B` with
`π_A ⊗ σ_B` simplifies to `|A|^(1-α)` at the sandwiched Renyi exponent. -/
theorem conditionalRenyi_card_factor_eq_rpow_card_one_sub [Nonempty a]
    {α : ℝ} (hα : 0 < α) :
    let s : ℝ := (1 - α) / (2 * α)
    (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ α) =
      (Fintype.card a : ℝ) ^ (1 - α) := by
  intro s
  have hcard : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := le_of_lt hcard
  have hs_nonneg : 0 ≤ (Fintype.card a : ℝ) ^ s :=
    Real.rpow_nonneg hcard_nonneg s
  have hsα : (s + s) * α = 1 - α := by
    dsimp [s]
    field_simp [ne_of_gt hα]
    ring
  calc
    (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ α)
        = (((Fintype.card a : ℝ) ^ (s + s)) ^ α) := by
          rw [Real.rpow_add hcard s s]
    _ = (Fintype.card a : ℝ) ^ ((s + s) * α) := by
          rw [← Real.rpow_mul hcard_nonneg (s + s) α]
    _ = (Fintype.card a : ℝ) ^ (1 - α) := by
          rw [hsα]

/-- Candidate rewrite with the dimension factor simplified to `|A|^(1-α)`. -/
theorem conditionalSandwichedRenyiCandidate_eq_log2_card_one_sub_mul_normalizedTracePower
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one =
      (-(1 / (α - 1))) *
        log2
          (((Fintype.card a : ℝ) ^ (1 - α)) *
            psdTracePower
              (sandwichedRenyiInner ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α)
              (sandwichedRenyiInner_posSemidef ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α) α) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_factor_mul_normalizedTracePower
    ρ hρ σ hσ α hα_pos hα_ne_one]
  rw [conditionalRenyi_card_factor_eq_rpow_card_one_sub (a := a) hα_pos]

/-- Base-two logarithms linearize positive real powers. -/
theorem log2_rpow_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    log2 (x ^ y) = y * log2 x := by
  unfold log2
  rw [Real.log_rpow hx]
  ring

/-- A conditional sandwiched Renyi candidate with the unnormalized reference
`I_A ⊗ σ_B` equals `log₂ |A|` minus the ordinary sandwiched Renyi divergence
against the normalized product reference `π_A ⊗ σ_B`.

This is the value-level bridge needed to convert the low-`α` conditional
duality route back into the already proved high-`β` channel DPI. -/
theorem conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one =
      log2 (Fintype.card a : ℝ) -
        sandwichedRenyi ρ
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ)
          hρ
          (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
          α hα_pos hα_ne_one := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  let ν : State (Prod a b) := (maximallyMixed a).prod σ
  have hν : ν.matrix.PosDef := by
    simpa [ν] using conditionalRenyi_normalizedReference_posDef ρ σ hσ
  have hTpos :
      0 <
        psdTracePower (sandwichedRenyiInner ρ ν α)
          (sandwichedRenyiInner_posSemidef ρ ν α) α :=
    sandwichedRenyiInner_psdTracePower_pos ρ ν hρ hν α
  have hcard : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcardpow : 0 < (Fintype.card a : ℝ) ^ (1 - α) :=
    Real.rpow_pos_of_pos hcard (1 - α)
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_one_sub_mul_normalizedTracePower
    ρ hρ σ hσ α hα_pos hα_ne_one]
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner]
  rw [log2_mul (ne_of_gt hcardpow) (ne_of_gt hTpos)]
  rw [log2_rpow_pos hcard]
  field_simp [hα_ne_one]
  ring

/-- Heterogeneous candidate comparison after normalizing the conditional
reference. This packages the value bridge in an inequality-oriented form:
to compare conditional candidates, it suffices to compare the corresponding
`log₂ dim - D̃_α(· ‖ π ⊗ σ)` quantities. -/
theorem conditionalSandwichedRenyiCandidate_le_of_normalizedReference_bound
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (hρ₁ : ρ₁.matrix.PosDef)
    (σ₁ : State b₁) (hσ₁ : σ₁.matrix.PosDef)
    (ρ₂ : State (Prod a₂ b₂)) (hρ₂ : ρ₂.matrix.PosDef)
    (σ₂ : State b₂) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbound :
      log2 (Fintype.card a₂ : ℝ) -
          sandwichedRenyi ρ₂
            ((@maximallyMixed a₂ _ _ (by
              rcases ρ₂.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ₂)
            hρ₂
            (conditionalRenyi_normalizedReference_posDef ρ₂ σ₂ hσ₂)
            α hα_pos hα_ne_one ≤
        log2 (Fintype.card a₁ : ℝ) -
          sandwichedRenyi ρ₁
            ((@maximallyMixed a₁ _ _ (by
              rcases ρ₁.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ₁)
            hρ₁
            (conditionalRenyi_normalizedReference_posDef ρ₁ σ₁ hσ₁)
            α hα_pos hα_ne_one) :
    ρ₂.conditionalSandwichedRenyiCandidate hρ₂ σ₂ hσ₂ α hα_pos hα_ne_one ≤
      ρ₁.conditionalSandwichedRenyiCandidate hρ₁ σ₁ hσ₁ α hα_pos hα_ne_one := by
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₂ hρ₂ σ₂ hσ₂ α hα_pos hα_ne_one]
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₁ hρ₁ σ₁ hσ₁ α hα_pos hα_ne_one]
  exact hbound

/-- A normalized-reference nonnegativity bound gives the standard dimensional
upper bound on each upward conditional Renyi candidate.

This is the value-level form of the source proof obligation: after rewriting
`H̃^↑_α(A|B)` candidates as `log₂ |A| - D̃_α(ρ_AB ‖ π_A ⊗ σ_B)`, ordinary
nonnegativity of the sandwiched Renyi divergence gives
`candidate ≤ log₂ |A|`. -/
theorem conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hnonneg :
      0 ≤ sandwichedRenyi ρ
        ((@maximallyMixed a _ _ (by
          rcases ρ.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ)
        hρ
        (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
        α hα_pos hα_ne_one) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one ≤
      log2 (Fintype.card a : ℝ) := by
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ hρ σ hσ α hα_pos hα_ne_one]
  linarith

/-- A pointwise normalized-reference nonnegativity theorem bounds the whole
upward conditional Renyi candidate set by `log₂ |A|`.

This packages the remaining high-parameter minimax boundedness side condition
into the mathematically standard nonnegativity obligation for ordinary
sandwiched Renyi divergence. -/
theorem conditionalSandwichedRenyiValueSet_bddAbove_log2_card_of_normalizedReference_nonneg
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hnonneg :
      ∀ σ : State b, ∀ hσ : σ.matrix.PosDef,
        0 ≤ sandwichedRenyi ρ
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ)
          hρ
          (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
          α (by linarith) hα_ne_one) :
    BddAbove (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one) :=
  conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
    ρ hρ α hα hα_ne_one
    (fun σ hσ =>
      conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
        ρ hρ σ hσ α (by linarith) hα_ne_one (hnonneg σ hσ))

/-- In the already-proved `α > 1` range, every upward conditional Renyi
candidate is bounded above by `log₂ |A|`.

This discharges the normalized-reference nonnegativity side condition using
the terminal-channel proof of ordinary sandwiched Renyi nonnegativity. -/
theorem conditionalSandwichedRenyiCandidate_le_log2_card_of_one_lt
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      log2 (Fintype.card a : ℝ) :=
  conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
    ρ hρ σ hσ α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one)
    (sandwichedRenyi_nonneg_of_one_lt
      ρ
      ((@maximallyMixed a _ _ (by
        rcases ρ.nonempty with ⟨x⟩
        exact ⟨x.1⟩)).prod σ)
      hρ
      (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
      α hα_gt_one)

/-- The upward conditional Renyi candidate set is bounded above by
`log₂ |A|` in the already-proved `α > 1` range. -/
theorem conditionalSandwichedRenyiValueSet_bddAbove_log2_card_of_one_lt
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    BddAbove
      (ρ.conditionalSandwichedRenyiValueSet hρ α (by linarith)
        (ne_of_gt hα_gt_one)) :=
  conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
    ρ hρ α (by linarith) (ne_of_gt hα_gt_one)
    (fun σ hσ =>
      conditionalSandwichedRenyiCandidate_le_log2_card_of_one_lt
        ρ hρ σ hσ α hα_gt_one)

/-- Candidate transport from a reverse channel on normalized references.

If a channel maps the output-side normalized pair
`(ρ₂, π_{A₂} ⊗ σ₂)` back to the input-side normalized pair
`(ρ₁, π_{A₁} ⊗ σ₁)`, then the already-proved high-parameter sandwiched Renyi DPI
gives the required reverse comparison of conditional candidates, up to the
explicit left-system dimension term.

This is the concrete high-`β` step consumed by the strict low-`α`
conditional-duality route. -/
theorem conditionalSandwichedRenyiCandidate_le_of_reverseChannel_normalizedReference
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (hρ₁ : ρ₁.matrix.PosDef)
    (σ₁ : State b₁) (hσ₁ : σ₁.matrix.PosDef)
    (ρ₂ : State (Prod a₂ b₂)) (hρ₂ : ρ₂.matrix.PosDef)
    (σ₂ : State b₂) (hσ₂ : σ₂.matrix.PosDef)
    (Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁))
    (hρΨ : Ψ.applyState ρ₂ = ρ₁)
    (hσΨ :
      Ψ.applyState
          ((@maximallyMixed a₂ _ _ (by
            rcases ρ₂.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ₂) =
        ((@maximallyMixed a₁ _ _ (by
          rcases ρ₁.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ₁))
    (β : ℝ) (hβ_gt_one : 1 < β)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ)) :
    ρ₂.conditionalSandwichedRenyiCandidate hρ₂ σ₂ hσ₂ β
        (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyiCandidate hρ₁ σ₁ hσ₁ β
        (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) := by
  haveI : Nonempty a₁ := by
    rcases ρ₁.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  haveI : Nonempty a₂ := by
    rcases ρ₂.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  let ν₁ : State (Prod a₁ b₁) := (maximallyMixed a₁).prod σ₁
  let ν₂ : State (Prod a₂ b₂) := (maximallyMixed a₂).prod σ₂
  have hν₁ : ν₁.matrix.PosDef := by
    simpa [ν₁] using conditionalRenyi_normalizedReference_posDef ρ₁ σ₁ hσ₁
  have hν₂ : ν₂.matrix.PosDef := by
    simpa [ν₂] using conditionalRenyi_normalizedReference_posDef ρ₂ σ₂ hσ₂
  have hρΨ_pos : (Ψ.applyState ρ₂).matrix.PosDef := by
    rw [hρΨ]
    exact hρ₁
  have hνΨ_pos : (Ψ.applyState ν₂).matrix.PosDef := by
    rw [show Ψ.applyState ν₂ = ν₁ by simpa [ν₁, ν₂] using hσΨ]
    exact hν₁
  have hDPI_stmt :
      sandwichedRenyi_dataProcessing_channel_statement ρ₂ ν₂ Ψ
        hρ₂ hν₂ hρΨ_pos hνΨ_pos β (by linarith) (ne_of_gt hβ_gt_one) :=
    sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
      ρ₂ ν₂ Ψ hρ₂ hν₂ hρΨ_pos hνΨ_pos β hβ_gt_one
  have hDPI :
      sandwichedRenyi ρ₁ ν₁ hρ₁ hν₁ β
          (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) ≤
        sandwichedRenyi ρ₂ ν₂ hρ₂ hν₂ β
          (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) := by
    unfold sandwichedRenyi_dataProcessing_channel_statement at hDPI_stmt
    simpa [ν₁, ν₂, hρΨ, hσΨ] using hDPI_stmt
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₂ hρ₂ σ₂ hσ₂ β (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one)]
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₁ hρ₁ σ₁ hσ₁ β (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one)]
  simpa [ν₁, ν₂] using sub_le_sub hdim hDPI

/-- Upward sandwiched conditional Renyi duality: for a pure tripartite state
with `AB` and `AC` marginals, `H̃^↑_α(A|B) = -H̃^↑_β(A|C)` when
`1/α + 1/β = 2`. The two bipartite arguments are the `AB` and `AC` marginals of
a common pure state (the purity condition is the documented precondition).
Statement only. -/
def conditionalSandwichedRenyi_duality_statement (ρ : State (Prod a b))
    (σ : State (Prod a c)) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β) (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (_hab : 1 / α + 1 / β = 2) : Prop :=
  conditionalSandwichedRenyi ρ hρ α hα hα1 =
    - conditionalSandwichedRenyi σ hσ β hβ hβ1

/-- The upward conditional sandwiched Renyi duality statement is symmetric
under swapping the complementary systems and the Holder-dual exponents.

This is only an algebraic statement-layer bridge: it reuses a proved instance
of the source duality equality in one direction and flips the real equality.
It does not assert or prove the missing conditional-duality theorem itself. -/
theorem conditionalSandwichedRenyi_duality_statement.symm
    (ρ : State (Prod a b)) (σ : State (Prod a c))
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hab : 1 / α + 1 / β = 2)
    (hdual :
      conditionalSandwichedRenyi_duality_statement ρ σ hρ hσ
        α β hα hβ hα1 hβ1 hab) :
    conditionalSandwichedRenyi_duality_statement
      (a := a) (b := c) (c := b) σ ρ hσ hρ
      β α hβ hα hβ1 hα1 (by simpa [add_comm] using hab) := by
  unfold conditionalSandwichedRenyi_duality_statement at hdual ⊢
  linarith

/-- Conditional-duality symmetry specialized to the low-`α` dual parameter
`β = α / (2α - 1)`.

This is the exact exponent bookkeeping needed by the `1 / 2 < α < 1` route:
once the conditional duality theorem is available in one direction, this lemma
turns it into the swapped complementary-system statement whose exponent lies in
the already-proved `β > 1` range. -/
theorem conditionalSandwichedRenyi_duality_statement.symm_dualParameter
    (ρ : State (Prod a b)) (σ : State (Prod a c))
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual :
      conditionalSandwichedRenyi_duality_statement ρ σ hρ hσ
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)) :
    conditionalSandwichedRenyi_duality_statement
      (a := a) (b := c) (c := b) σ ρ hσ hρ
      (renyiDualParameter α) α
      (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
      (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
      (by
        simpa [add_comm] using
          renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_duality_statement.symm
      ρ σ hρ hσ α (renyiDualParameter α)
      (le_of_lt hα_half) (renyiDualParameter_half_le hα_half hα_lt_one)
      (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
      (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)
      hdual

/-- Conditional-duality symmetry specialized to the dual parameter, starting
from the swapped complementary-system direction.

This is the direction used when the source proof supplies the high-`β`
conditional duality statement first: it converts
`H̃^↑_β(A|C) = -H̃^↑_α(A|B)` back to the low-`α` statement consumed by the
strict subunit monotonicity route. -/
theorem conditionalSandwichedRenyi_duality_statement.symm_swappedDualParameter
    (ρ : State (Prod a b)) (σ : State (Prod a c))
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := c) (c := b) σ ρ hσ hρ
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)) :
    conditionalSandwichedRenyi_duality_statement ρ σ hρ hσ
      α (renyiDualParameter α) (le_of_lt hα_half)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
      (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_duality_statement.symm
      σ ρ hσ hρ (renyiDualParameter α) α
      (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
      (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
      (by
        simpa [add_comm] using
          renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)
      hdual

/-- Algebraic conditional-duality handoff for the low-`α` monotonicity route.

If two low-`α` conditional entropies are related to their complementary
high-`β` conditional entropies by upward sandwiched Renyi duality, then a
monotonicity inequality on the complementary `β > 1` side transfers to the
desired low-`α` inequality after negating both sides.

This theorem does not prove conditional Renyi duality or the high-`β`
monotonicity theorem; it isolates the exact algebraic step needed once those
source-backed ingredients are available. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse
    (ρ₁ ρ₂ : State (Prod a b)) (σ₁ σ₂ : State (Prod a c))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hab : 1 / α + 1 / β = 2)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement ρ₁ σ₁ hρ₁ hσ₁
        α β hα hβ hα1 hβ1 hab)
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement ρ₂ σ₂ hρ₂ hσ₂
        α β hα hβ hα1 hβ1 hab)
    (hhigh :
      conditionalSandwichedRenyi σ₂ hσ₂ β hβ hβ1 ≤
        conditionalSandwichedRenyi σ₁ hσ₁ β hβ hβ1) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α hα hα1 ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α hα hα1 := by
  unfold conditionalSandwichedRenyi_duality_statement at hdual₁ hdual₂
  linarith

/-- Heterogeneous version of the conditional-duality handoff.

The left subsystem may change under the operation being proved monotone
(for example a measurement map changes `A` to a classical output register).
The proof is still purely algebraic: two duality equalities plus the
complementary high-`β` inequality transfer across negation. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_heterogeneous
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hab : 1 / α + 1 / β = 2)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α β hα hβ hα1 hβ1 hab)
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α β hα hβ hα1 hβ1 hab)
    (hhigh :
      conditionalSandwichedRenyi σ₂ hσ₂ β hβ hβ1 ≤
        conditionalSandwichedRenyi σ₁ hσ₁ β hβ hβ1) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α hα hα1 ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α hα hα1 := by
  unfold conditionalSandwichedRenyi_duality_statement at hdual₁ hdual₂
  linarith

/-- Conditional-duality handoff specialized to the strict low-`α` dual
parameter `β = α / (2α - 1)`.

This packages the exponent bookkeeping for the source range
`1 / 2 < α < 1`: the complementary side lies in the already-established
`β > 1` range, and a high-`β` reverse monotonicity inequality transfers to the
low-`α` side. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hhigh :
      conditionalSandwichedRenyi σ₂ hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        conditionalSandwichedRenyi σ₁ hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) :=
  conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_heterogeneous
    ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
    α (renyiDualParameter α)
    (le_of_lt hα_half)
    (renyiDualParameter_half_le hα_half hα_lt_one)
    (ne_of_lt hα_lt_one)
    (renyiDualParameter_ne_one hα_half hα_lt_one)
    (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)
    hdual₁ hdual₂ hhigh

/-- Candidate-level sufficient condition for a high-parameter conditional
Renyi reverse inequality.

This is the `sSup` handoff needed by the strict low-`α` duality route: instead
of proving an abstract conditional-entropy inequality on the complementary
side, it is enough to bound every output side-information candidate by the
input conditional entropy. -/
theorem conditionalSandwichedRenyi_le_of_forall_candidate_le_conditional
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ : 1 / 2 ≤ β) (hβ1 : β ≠ 1)
    (hcand :
      ∀ η : State b₂, ∀ hη : η.matrix.PosDef,
        ρ₂.conditionalSandwichedRenyiCandidate hρ₂ η hη β (by linarith) hβ1 ≤
          ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β hβ hβ1 ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 := by
  haveI : Nonempty b₂ := by
    rcases ρ₂.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  exact
    conditionalSandwichedRenyi_le_of_forall_candidate_le
      ρ₂ hρ₂ β hβ hβ1 hcand

/-- Candidate-transport sufficient condition for a high-parameter conditional
Renyi reverse inequality.

If every output side-information candidate can be bounded by one fixed input
candidate, then the output conditional entropy is bounded by the input
conditional entropy, provided the input candidate family is bounded above.
This is the concrete candidate-lift form consumed by the low-`α`
measurement/duality route. -/
theorem conditionalSandwichedRenyi_le_of_candidate_lift
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ : 1 / 2 ≤ β) (hβ1 : β ≠ 1)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hbdd₁ : BddAbove (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β hβ hβ1))
    (hlift :
      ∀ η₂ : State b₂, ∀ hη₂ : η₂.matrix.PosDef,
        ρ₂.conditionalSandwichedRenyiCandidate hρ₂ η₂ hη₂ β (by linarith) hβ1 ≤
          ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β hβ hβ1 ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 := by
  have hη₁_le :
      ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1 ≤
        ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 :=
    conditionalSandwichedRenyiCandidate_le_conditionalSandwichedRenyi_of_bddAbove
      ρ₁ hρ₁ η₁ hη₁ β hβ hβ1 hbdd₁
  exact
    conditionalSandwichedRenyi_le_of_forall_candidate_le_conditional
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ hβ1
      (fun η₂ hη₂ => le_trans (hlift η₂ hη₂) hη₁_le)

/-- High-parameter conditional reverse inequality from a family of reverse
channels on normalized references.

For every output side-information candidate `η₂`, assume there is a channel
that sends the output normalized pair `(ρ₂, π_{A₂} ⊗ η₂)` back to the fixed input
pair `(ρ₁, π_{A₁} ⊗ η₁)`. The high-`β` sandwiched Renyi DPI then supplies the
candidate lift required by `conditionalSandwichedRenyi_le_of_candidate_lift`. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hbdd₁ :
      BddAbove
        (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β (by linarith)
          (ne_of_gt hβ_gt_one)))
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_candidate_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β (by linarith) (ne_of_gt hβ_gt_one)
      η₁ hη₁ hbdd₁
      (fun η₂ hη₂ => by
        rcases hreverse η₂ hη₂ with ⟨Ψ, hρΨ, hηΨ⟩
        exact
          conditionalSandwichedRenyiCandidate_le_of_reverseChannel_normalizedReference
            ρ₁ hρ₁ η₁ hη₁ ρ₂ hρ₂ η₂ hη₂ Ψ hρΨ hηΨ
            β hβ_gt_one hdim)

/-- Concrete-bound version of
`conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift`.

This packages the exact data usually available in a proof sprint: a fixed input
candidate, a reverse-channel lift for every output candidate, and any finite
uniform upper bound on the input candidate family. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_bound
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    {C : ℝ}
    (hinputBound :
      ∀ η₁ : State b₁, ∀ hη₁ : η₁.matrix.PosDef,
        ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β
          (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) ≤ C)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  have hbdd₁ :
      BddAbove
        (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β (by linarith)
          (ne_of_gt hβ_gt_one)) :=
    conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
      ρ₁ hρ₁ β (by linarith) (ne_of_gt hβ_gt_one)
      (by
        intro η hη
        exact hinputBound η hη)
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one η₁ hη₁ hbdd₁ hdim hreverse

/-- Reverse-channel high-parameter conditional inequality with the input
boundedness side condition discharged by normalized-reference nonnegativity.

The remaining hypothesis is now the source-standard statement that every
ordinary sandwiched Renyi divergence
`D̃_β(ρ₁ ‖ π_A ⊗ η₁)` is nonnegative, rather than an arbitrary finite upper
bound on conditional candidates. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_nonneg
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (hinputNonneg :
      ∀ η₁' : State b₁, ∀ hη₁' : η₁'.matrix.PosDef,
        0 ≤ sandwichedRenyi ρ₁
          ((@maximallyMixed a₁ _ _ (by
            rcases ρ₁.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod η₁')
          hρ₁
          (conditionalRenyi_normalizedReference_posDef ρ₁ η₁' hη₁')
          β (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one))
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_bound
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one
      (C := log2 (Fintype.card a₁ : ℝ))
      (fun η₁' hη₁' =>
        conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
          ρ₁ hρ₁ η₁' hη₁' β (lt_trans zero_lt_one hβ_gt_one)
          (ne_of_gt hβ_gt_one) (hinputNonneg η₁' hη₁'))
      η₁ hη₁ hdim hreverse

/-- Reverse-channel high-parameter conditional inequality with no external
boundedness hypothesis.

The input candidate family is bounded by `log₂ |A₁|`, using ordinary
sandwiched Renyi nonnegativity in the proved `β > 1` range. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_one_lt
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one η₁ hη₁
      (conditionalSandwichedRenyiValueSet_bddAbove_log2_card_of_one_lt
        ρ₁ hρ₁ β hβ_gt_one)
      hdim hreverse

/-- Same-left-system form of the high-parameter reverse-channel conditional
inequality.

When the two conditional states use the same left system, the dimension
comparison required by the general lift is reflexive. This is the form needed
for channel DPI reductions whose purification/duality step does not change the
reference system. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_sameLeft_of_one_lt
    {a b₁ b₂ : Type*}
    [Fintype a] [DecidableEq a] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a b₁)) (ρ₂ : State (Prod a b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a b₂) (Prod a b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_one_lt
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one η₁ hη₁ le_rfl hreverse

/-- Strict low-`α` conditional monotonicity from conditional duality and a
reverse-channel construction on the complementary high-`β` side.

This is the reusable route behind the measurement-specific theorem below:
conditional duality reduces the strict low-`α` comparison to a high-`β`
conditional reverse inequality, and the latter is discharged by the already
proved `β > 1` sandwiched Renyi DPI applied to normalized conditional
references. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    {C : ℝ}
    (hinputBound :
      ∀ η₁' : State c₁, ∀ hη₁' : η₁'.matrix.PosDef,
        σ₁.conditionalSandwichedRenyiCandidate hσ₁ η₁' hη₁'
          (renyiDualParameter α)
          (lt_trans zero_lt_one (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)) ≤ C)
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  have hβgt : 1 < renyiDualParameter α :=
    renyiDualParameter_gt_one hα_half hα_lt_one
  have hhigh_raw :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) :=
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_bound
      σ₁ σ₂ hσ₁ hσ₂ (renyiDualParameter α) hβgt
      hinputBound η₁ hη₁ hdim hreverse
  have hhigh :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) := by
    simpa using hhigh_raw
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ hhigh

/-- Strict low-`α` conditional monotonicity with the complementary
high-`β` input boundedness reduced to ordinary normalized-reference
nonnegativity.

This is the same duality/reverse-channel route as
`conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound`,
but it packages the input candidate bound using the identity
`candidate = log₂ |A| - D̃_β(σ₁ ‖ π_A ⊗ η₁)`. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_nonneg
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hinputNonneg :
      ∀ η₁' : State c₁, ∀ hη₁' : η₁'.matrix.PosDef,
        0 ≤ sandwichedRenyi σ₁
          ((@maximallyMixed a₁ _ _ (by
            rcases σ₁.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod η₁')
          hσ₁
          (conditionalRenyi_normalizedReference_posDef σ₁ η₁' hη₁')
          (renyiDualParameter α)
          (lt_trans zero_lt_one
            (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂
      (C := log2 (Fintype.card a₁ : ℝ))
      (fun η₁' hη₁' =>
        conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
          σ₁ hσ₁ η₁' hη₁' (renyiDualParameter α)
          (lt_trans zero_lt_one
            (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one))
          (hinputNonneg η₁' hη₁'))
      η₁ hη₁ hdim hreverse

/-- Strict low-`α` conditional monotonicity from conditional duality and a
reverse-channel construction, with the high-`β` input candidate boundedness
discharged internally by `β > 1` sandwiched Renyi nonnegativity. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_one_lt
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  have hβgt : 1 < renyiDualParameter α :=
    renyiDualParameter_gt_one hα_half hα_lt_one
  have hhigh_raw :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) :=
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_one_lt
      σ₁ σ₂ hσ₁ hσ₂ (renyiDualParameter α) hβgt
      η₁ hη₁ hdim hreverse
  have hhigh :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) := by
    simpa using hhigh_raw
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ hhigh

/-- Same-left-system strict low-`α` conditional monotonicity from conditional
duality and a reverse-channel construction.

This packages the common case where the duality/recovery step preserves the
left reference system, so the dimension comparison in the general lift is
automatic. The remaining nontrivial assumptions are the conditional duality
statements and the explicit reverse-channel family on the complementary side. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_sameLeft_of_one_lt
    {a b₁ c₁ b₂ c₂ : Type*}
    [Fintype a] [DecidableEq a] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a b₁)) (ρ₂ : State (Prod a b₂))
    (σ₁ : State (Prod a c₁)) (σ₂ : State (Prod a c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a c₂) (Prod a c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_one_lt
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ η₁ hη₁ le_rfl hreverse

/-- Same-left-system strict low-`α` conditional monotonicity when the
conditional-duality inputs are supplied in the swapped high-`β` direction.

This is a convenience bridge for source proofs that state duality as
`H̃^↑_β(A|C) = -H̃^↑_α(A|B)`. The theorem converts both duality statements to
the low-`α` direction and then applies the same-left reverse-channel lift. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt
    {a b₁ c₁ b₂ c₂ : Type*}
    [Fintype a] [DecidableEq a] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a b₁)) (ρ₂ : State (Prod a b₂))
    (σ₁ : State (Prod a c₁)) (σ₂ : State (Prod a c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := c₁) (c := b₁) σ₁ ρ₁ hσ₁ hρ₁
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := c₂) (c := b₂) σ₂ ρ₂ hσ₂ hρ₂
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a c₂) (Prod a c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_sameLeft_of_one_lt
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one
      (conditionalSandwichedRenyi_duality_statement.symm_swappedDualParameter
        ρ₁ σ₁ hρ₁ hσ₁ α hα_half hα_lt_one hdual₁)
      (conditionalSandwichedRenyi_duality_statement.symm_swappedDualParameter
        ρ₂ σ₂ hρ₂ hσ₂ α hα_half hα_lt_one hdual₂)
      η₁ hη₁ hreverse

/-- Strict low-`α` conditional monotonicity from conditional duality and a
reverse-channel construction, using a raw boundedness witness for the input
high-`β` candidate value set. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hbdd₁ :
      BddAbove
        (σ₁.conditionalSandwichedRenyiValueSet hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)))
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  have hβgt : 1 < renyiDualParameter α :=
    renyiDualParameter_gt_one hα_half hα_lt_one
  have hhigh_raw :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) :=
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
      σ₁ σ₂ hσ₁ hσ₂ (renyiDualParameter α) hβgt
      η₁ hη₁ (by simpa using hbdd₁) hdim hreverse
  have hhigh :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) := by
    simpa using hhigh_raw
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ hhigh

/-- Candidate transport with a concrete uniform upper bound for the input
candidate family.

This variant avoids carrying a raw `BddAbove` proof through later DPI route
lemmas. A source proof can provide any finite uniform upper bound on the input
side-information candidates, then use the fixed-candidate lift to obtain the
high-parameter conditional reverse inequality. -/
theorem conditionalSandwichedRenyi_le_of_candidate_lift_of_forall_input_candidate_le
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ : 1 / 2 ≤ β) (hβ1 : β ≠ 1)
    {C : ℝ}
    (hinputBound :
      ∀ η₁ : State b₁, ∀ hη₁ : η₁.matrix.PosDef,
        ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1 ≤ C)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hlift :
      ∀ η₂ : State b₂, ∀ hη₂ : η₂.matrix.PosDef,
        ρ₂.conditionalSandwichedRenyiCandidate hρ₂ η₂ hη₂ β (by linarith) hβ1 ≤
          ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β hβ hβ1 ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 := by
  have hbdd₁ :
      BddAbove (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β hβ hβ1) :=
    conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
      ρ₁ hρ₁ β hβ hβ1 hinputBound
  exact
    conditionalSandwichedRenyi_le_of_candidate_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ hβ1 η₁ hη₁ hbdd₁ hlift

/-- Measurement-map monotonicity: measuring subsystem `A` does not decrease the
upward sandwiched conditional Renyi entropy `H̃^↑_α(·|B)` (a DPI instance).
Statement only. -/
def measurementMap_conditionalRenyi_monotonicity_statement (ρ : State (Prod a b))
    (hρ : ρ.matrix.PosDef) (M : POVM c a)
    (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα1 : α ≠ 1) : Prop :=
  conditionalSandwichedRenyi (measureSubsystemState M ρ) hρM α hα hα1 ≥
    conditionalSandwichedRenyi ρ hρ α hα hα1

/-- Measurement-map monotonicity obtained from conditional duality and the
complementary high-`β` reverse inequality.

This is the statement-level shell for the strict low-`α` measurement route:
once the two conditional-duality instances and the complementary `β > 1`
monotonicity inequality are available, the registered measurement monotonicity
statement follows without any further analytic work. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hhigh :
      conditionalSandwichedRenyi σOut hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        conditionalSandwichedRenyi σIn hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut hhigh

/-- Strict low-`α` measurement monotonicity from conditional duality and a
candidate-level complementary high-`β` bound.

This removes one abstraction layer from the low-`α` route: the remaining
high-parameter task can be proved by checking every full-rank side-information
candidate of the complementary output state. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_candidate_bound
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hcand :
      ∀ ηOut : State e, ∀ hηOut : ηOut.matrix.PosDef,
        σOut.conditionalSandwichedRenyiCandidate hσOut ηOut hηOut
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
          σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
            (renyiDualParameter_half_le hα_half hα_lt_one)
            (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  have hhigh :
      σOut.conditionalSandwichedRenyi hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) :=
    conditionalSandwichedRenyi_le_of_forall_candidate_le_conditional
      σIn σOut hσIn hσOut
      (renyiDualParameter α)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (renyiDualParameter_ne_one hα_half hα_lt_one)
      hcand
  exact
    measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
      ρ hρ M hρM σIn σOut hσIn hσOut α hα_half hα_lt_one
      hdualIn hdualOut hhigh

/-- Strict low-`α` measurement monotonicity from conditional duality, a fixed
candidate transport, and a concrete uniform upper bound on the input
complementary candidate family.

This is the no-raw-`BddAbove` version of the candidate-lift route. It is useful
when the remaining high-`β` source proof naturally supplies a numerical
candidate bound rather than an order-theoretic value-set boundedness proof. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_candidate_lift_of_input_bound
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    {C : ℝ}
    (hinputBound :
      ∀ ηIn' : State d, ∀ hηIn' : ηIn'.matrix.PosDef,
        σIn.conditionalSandwichedRenyiCandidate hσIn ηIn' hηIn'
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤ C)
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hlift :
      ∀ ηOut : State e, ∀ hηOut : ηOut.matrix.PosDef,
        σOut.conditionalSandwichedRenyiCandidate hσOut ηOut hηOut
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
          σIn.conditionalSandwichedRenyiCandidate hσIn ηIn hηIn
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  have hhigh :
      σOut.conditionalSandwichedRenyi hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) :=
    conditionalSandwichedRenyi_le_of_candidate_lift_of_forall_input_candidate_le
      σIn σOut hσIn hσOut
      (renyiDualParameter α)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (renyiDualParameter_ne_one hα_half hα_lt_one)
      hinputBound ηIn hηIn hlift
  exact
    measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
      ρ hρ M hρM σIn σOut hσIn hσOut α hα_half hα_lt_one
      hdualIn hdualOut hhigh

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction on the complementary high-`β` side.

Compared with
`measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_candidate_lift_of_input_bound`,
this theorem discharges the candidate lift using the high-`β` sandwiched Renyi
DPI for normalized conditional references. The remaining source-level
obligations are the two conditional-duality instances, an input candidate
boundedness witness, and the reverse channel family on complementary systems. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_of_input_bound
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    {C : ℝ}
    (hinputBound :
      ∀ ηIn' : State d, ∀ hηIn' : ηIn'.matrix.PosDef,
        σIn.conditionalSandwichedRenyiCandidate hσIn ηIn' hηIn'
            (renyiDualParameter α)
            (lt_trans zero_lt_one
              (renyiDualParameter_gt_one hα_half hα_lt_one))
            (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)) ≤ C)
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      hinputBound ηIn hηIn hdim hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction, with the input high-`β` candidate bound reduced
to ordinary nonnegativity against normalized conditional references.

This is the measurement-facing version of
`conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_nonneg`.
It leaves the proof sprint with a sharper remaining blocker: prove
`D̃_β(σIn ‖ π_A ⊗ η) ≥ 0` for the complementary high-`β` states, rather than
provide an arbitrary uniform candidate bound. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_of_input_nonneg
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hinputNonneg :
      ∀ ηIn' : State d, ∀ hηIn' : ηIn'.matrix.PosDef,
        0 ≤ sandwichedRenyi σIn
          ((@maximallyMixed a _ _ (by
            rcases σIn.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod ηIn')
          hσIn
          (conditionalRenyi_normalizedReference_posDef σIn ηIn' hηIn')
          (renyiDualParameter α)
          (lt_trans zero_lt_one
            (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_nonneg
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      hinputNonneg ηIn hηIn hdim hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction, with no external input boundedness hypothesis.

The high-`β` input candidate family is bounded internally by the proved
ordinary sandwiched Renyi nonnegativity in the `β > 1` range. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_of_one_lt
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_one_lt
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      ηIn hηIn hdim hreverse

/-- Same-left-system measurement form of the strict low-`α`
duality/reverse-channel route.

This specializes the measurement-facing theorem to measurements whose output
left register is the same type as the input left register, such as same-system
pinching measurements. In that case the dimension comparison in the general
measurement theorem is discharged by reflexivity. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_sameLeft_of_one_lt
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM a a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod a e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod a e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_sameLeft_of_one_lt
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      ηIn hηIn hreverse

/-- Same-left-system measurement monotonicity when the conditional-duality
inputs are supplied in the swapped high-`β` direction.

This is the measurement-facing companion of
`conditionalSandwichedRenyi_low_monotonicity_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt`.
It is tailored for same-system measurements, including pinching measurements,
whose source duality proof may naturally present the complementary high-`β`
entropy first. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM a a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod a e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := d) (c := b) σIn ρ hσIn hρ
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := e) (c := b) σOut (measureSubsystemState M ρ) hσOut hρM
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod a e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      ηIn hηIn hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction on the complementary high-`β` side, using a raw
boundedness witness for the input complementary candidate value set. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hbddIn :
      BddAbove
        (σIn.conditionalSandwichedRenyiValueSet hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)))
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut ηIn hηIn hbddIn hdim hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
single candidate-transport construction on the complementary high-`β` side.

This is the form closest to the source proof obligation: for every output
side-information candidate, construct or bound it by one fixed input
side-information candidate. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_candidate_lift
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hbddIn :
      BddAbove
        (σIn.conditionalSandwichedRenyiValueSet hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)))
    (hlift :
      ∀ ηOut : State e, ∀ hηOut : ηOut.matrix.PosDef,
        σOut.conditionalSandwichedRenyiCandidate hσOut ηOut hηOut
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
          σIn.conditionalSandwichedRenyiCandidate hσIn ηIn hηIn
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  have hhigh :
      σOut.conditionalSandwichedRenyi hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) :=
    conditionalSandwichedRenyi_le_of_candidate_lift
      σIn σOut hσIn hσOut
      (renyiDualParameter α)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (renyiDualParameter_ne_one hα_half hα_lt_one)
      ηIn hηIn hbddIn hlift
  exact
    measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
      ρ hρ M hρM σIn σOut hσIn hσOut α hα_half hα_lt_one
      hdualIn hdualOut hhigh

end State

end

end QIT
