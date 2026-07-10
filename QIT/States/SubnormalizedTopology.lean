/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Subnormalized
public import QIT.Util.SDP.PSDCone
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Topology and compactness for subnormalized states

This module equips `SubnormalizedState a` with the topology induced by its
density matrix and proves the finite-dimensional compactness facts needed by
smooth one-shot optimization arguments.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u

noncomputable section

noncomputable local instance instCMatrixCStarAlgebraForSubnormalizedTopology
    (n : Type u) [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

namespace SubnormalizedState

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The matrix-level subnormalized-state domain. -/
def subnormalizedMatrixSet (a : Type u) [Fintype a] : Set (CMatrix a) :=
  {M | M.PosSemidef ∧ M.trace.re ≤ 1}

omit [DecidableEq a] in
theorem mem_subnormalizedMatrixSet_iff {M : CMatrix a} :
    M ∈ subnormalizedMatrixSet a ↔ M.PosSemidef ∧ M.trace.re ≤ 1 :=
  Iff.rfl

/-- `SubnormalizedState a` carries the topology induced by its matrix field. -/
instance instTopologicalSpace : TopologicalSpace (SubnormalizedState a) :=
  TopologicalSpace.induced SubnormalizedState.matrix inferInstance

/-- The matrix projection from subnormalized states is continuous. -/
theorem continuous_matrix : Continuous (fun ρ : SubnormalizedState a => ρ.matrix) :=
  continuous_induced_dom

private theorem matrix_injective :
    Function.Injective (fun ρ : SubnormalizedState a => ρ.matrix) := by
  intro ρ σ hρσ
  exact ext hρσ

private theorem isEmbedding_matrix :
    Topology.IsEmbedding (fun ρ : SubnormalizedState a => ρ.matrix) :=
  Function.Injective.isEmbedding_induced matrix_injective

private theorem posSemidef_le_trace_re_smul_one {A : CMatrix a} (hA : A.PosSemidef) :
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
    · subst j
      simp [D, c]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast sub_nonneg.mpr (heig_le_trace i)

private theorem norm_le_trace_re_mul_norm_one_of_posSemidef {A : CMatrix a} (hA : A.PosSemidef) :
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

omit [DecidableEq a] in
/-- The matrix-level subnormalized-state domain is closed. -/
theorem subnormalizedMatrixSet_isClosed :
    IsClosed (subnormalizedMatrixSet a) := by
  classical
  have hpsd : IsClosed ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) := by
    simpa using (psdCone a).isClosed
  have htrace :
      IsClosed ({M : CMatrix a | M.trace.re ≤ 1} : Set (CMatrix a)) := by
    exact isClosed_le
      (Complex.continuous_re.comp (Continuous.matrix_trace continuous_id))
      continuous_const
  have hset :
      subnormalizedMatrixSet a =
        ({M : CMatrix a | M.PosSemidef} ∩
          {M : CMatrix a | M.trace.re ≤ 1}) := by
    ext M
    rfl
  rw [hset]
  exact hpsd.inter htrace

/-- The matrix-level subnormalized-state domain is bounded. -/
theorem subnormalizedMatrixSet_isBounded :
    Bornology.IsBounded (subnormalizedMatrixSet a) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖(1 : CMatrix a)‖, ?_⟩
  intro M hM
  rcases hM with ⟨hMpsd, hMtr⟩
  have hnorm := norm_le_trace_re_mul_norm_one_of_posSemidef (a := a) hMpsd
  have htrace_bound :
      M.trace.re * ‖(1 : CMatrix a)‖ ≤ 1 * ‖(1 : CMatrix a)‖ :=
    mul_le_mul_of_nonneg_right hMtr (norm_nonneg _)
  exact le_trans hnorm (by simpa using htrace_bound)

/-- The matrix-level subnormalized-state domain is compact. -/
theorem subnormalizedMatrixSet_isCompact :
    IsCompact (subnormalizedMatrixSet a) :=
  Metric.isCompact_of_isClosed_isBounded subnormalizedMatrixSet_isClosed
    subnormalizedMatrixSet_isBounded

private theorem matrix_image_univ :
    (fun ρ : SubnormalizedState a => ρ.matrix) '' Set.univ =
      subnormalizedMatrixSet a := by
  ext M
  constructor
  · rintro ⟨ρ, -, rfl⟩
    exact ⟨ρ.pos, ρ.trace_le_one⟩
  · intro hM
    refine ⟨⟨M, hM.1, hM.2⟩, Set.mem_univ _, rfl⟩

/-- The full type of finite-dimensional subnormalized states is compact. -/
theorem isCompact_univ :
    IsCompact (Set.univ : Set (SubnormalizedState a)) := by
  rw [isEmbedding_matrix.isCompact_iff]
  rw [matrix_image_univ]
  exact subnormalizedMatrixSet_isCompact (a := a)

theorem traceNorm_continuous_forTopology :
    Continuous (traceNorm : CMatrix a → ℝ) := by
  have hgram : Continuous (fun M : CMatrix a => star M * M) := by
    exact (Continuous.star continuous_id).matrix_mul continuous_id
  have hnonneg : ∀ M : CMatrix a, (star M * M) ∈ {A : CMatrix a | 0 ≤ A} := by
    intro M
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self M)
  have hsqrtOn :
      ContinuousOn (CFC.sqrt : CMatrix a → CMatrix a) {A : CMatrix a | 0 ≤ A} := by
    exact CFC.continuousOn_sqrt
  have hsqrt : Continuous (fun M : CMatrix a => CFC.sqrt (star M * M)) := by
    exact hsqrtOn.comp_continuous hgram hnonneg
  have htrace : Continuous (fun M : CMatrix a => (CFC.sqrt (star M * M)).trace) :=
    Continuous.matrix_trace hsqrt
  simpa [traceNorm, psdSqrt] using Complex.continuous_re.comp htrace

theorem continuous_psdSqrt_matrix :
    Continuous fun ρ : SubnormalizedState a => psdSqrt ρ.matrix := by
  have hsqrtOn :
      ContinuousOn (CFC.sqrt : CMatrix a → CMatrix a) {A : CMatrix a | 0 ≤ A} := by
    exact CFC.continuousOn_sqrt
  have hnonneg : ∀ ρ : SubnormalizedState a, ρ.matrix ∈ {A : CMatrix a | 0 ≤ A} := by
    intro ρ
    exact Matrix.nonneg_iff_posSemidef.mpr ρ.pos
  simpa [psdSqrt] using hsqrtOn.comp_continuous continuous_matrix hnonneg

/-- For fixed left input, generalized fidelity is continuous in the right
subnormalized state. -/
theorem continuous_generalizedFidelity_right (ρ : SubnormalizedState a) :
    Continuous fun σ : SubnormalizedState a => ρ.generalizedFidelity σ := by
  have hmul : Continuous fun σ : SubnormalizedState a =>
      psdSqrt ρ.matrix * psdSqrt σ.matrix :=
    continuous_const.matrix_mul continuous_psdSqrt_matrix
  have hnorm : Continuous fun σ : SubnormalizedState a =>
      traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix) :=
    traceNorm_continuous_forTopology.comp hmul
  have htrace : Continuous fun σ : SubnormalizedState a => σ.matrix.trace.re :=
    Complex.continuous_re.comp (Continuous.matrix_trace continuous_matrix)
  have hslack : Continuous fun σ : SubnormalizedState a =>
      (1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re) :=
    continuous_const.mul (continuous_const.sub htrace)
  have hsqrt : Continuous fun σ : SubnormalizedState a =>
      Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re)) :=
    Real.continuous_sqrt.comp hslack
  simpa [generalizedFidelity] using (hnorm.add hsqrt).pow 2

/-- For fixed left input, purified distance is continuous in the right
subnormalized state. -/
theorem continuous_purifiedDistance_right (ρ : SubnormalizedState a) :
    Continuous fun σ : SubnormalizedState a => ρ.purifiedDistance σ := by
  have hfid := continuous_generalizedFidelity_right (a := a) ρ
  simpa [purifiedDistance] using
    Real.continuous_sqrt.comp (continuous_const.sub hfid)

/-- A closed purified-distance ball in the subnormalized-state topology. -/
theorem purifiedBall_isClosed (ρ : SubnormalizedState a) (ε : ℝ) :
    IsClosed ({σ : SubnormalizedState a | ρ.purifiedBall ε σ}) := by
  simpa [purifiedBall] using
    isClosed_le (continuous_purifiedDistance_right (a := a) ρ) continuous_const

/-- A purified-distance ball is compact as a closed subset of the compact
subnormalized-state space. -/
theorem purifiedBall_isCompact (ρ : SubnormalizedState a) (ε : ℝ) :
    IsCompact ({σ : SubnormalizedState a | ρ.purifiedBall ε σ}) := by
  have hcompact :=
    (isCompact_univ (a := a)).inter_right (purifiedBall_isClosed (a := a) ρ ε)
  simpa [Set.univ_inter] using hcompact

end SubnormalizedState

end

end QIT
