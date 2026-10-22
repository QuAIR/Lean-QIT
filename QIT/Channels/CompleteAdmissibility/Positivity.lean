/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.CompleteAdmissibility
public import QIT.Util.Matrix.MarginalOrder

/-!
# Complete admissibility implies Choi-space complete positivity

The operational condition tests every joint quantum operation with independent
finite input and output spectators. Positive rescaling extends this test to
every positive operator; regrouping the spectator wires then gives ordinary
complete positivity on Choi space. This is the stabilized positivity requirement
in [Chiribella2008Supermaps, VersioneArchivio.tex:143-150].

The system and spectator universes remain independent. Finite spectators in
an arbitrary universe suffice because lifted finite types realize every finite
dimension. Empty system types require no separate hypothesis.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QIT.HigherOrder

universe u v w x y z

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

private theorem exists_pos_smul_partialTraceB_le_one
    {i : Type*} {o : Type*} [Fintype i] [DecidableEq i]
    [Fintype o] [DecidableEq o] (J : CMatrix (i × o)) (hJ : J.PosSemidef) :
    ∃ t : ℝ, 0 < t ∧ partialTraceB ((t : ℂ) • J) ≤ 1 := by
  let t : ℝ := 1 / (‖partialTraceB J‖ + 1)
  have hd : 0 < ‖partialTraceB J‖ + 1 := by positivity
  have ht : 0 < t := one_div_pos.mpr hd
  have htC : (0 : ℂ) ≤ (t : ℂ) := by exact_mod_cast ht.le
  refine ⟨t, ht, ?_⟩
  rw [partialTraceB_smul]
  have hn : ‖(t : ℂ) • partialTraceB J‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  simpa only [Complex.ofReal_one, one_smul] using
    (cMatrix_norm_le_iff_le_smul_one _ ((partialTraceB_posSemidef hJ).smul htC)
      1 zero_le_one).mp hn

/-- Complete admissibility preserves every positive joint Choi operator after
removing the operation trace bound by positive scalar rescaling. -/
theorem IsCompletelyAdmissible.ancillaryExtension_posSemidef
    {S : MatrixMap (a × b) (c × d)}
    (hS : IsCompletelyAdmissible.{u, v, w, x, y, z} S)
    {r : Type y} {s : Type z} [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (J : CMatrix ((a × r) × (b × s))) (hJ : J.PosSemidef) :
    (ancillaryExtension S J).PosSemidef := by
  obtain ⟨t, ht, hbound⟩ := exists_pos_smul_partialTraceB_le_one J hJ
  have htC : (0 : ℂ) ≤ (t : ℂ) := by exact_mod_cast ht.le
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hpos := (hS r s ((t : ℂ) • J) ⟨hJ.smul htC, hbound⟩).1
  change ((ancillaryExtension S) ((t : ℂ) • J)).PosSemidef at hpos
  rw [map_smul] at hpos
  simpa only [smul_smul, inv_mul_cancel₀ ht0, one_smul] using
    hpos.smul (inv_nonneg.mpr htC)

/-- Stabilized preservation of quantum operations forces complete positivity
of the linear transformation on their Choi matrices. All system and ancillary
universes are independent, and no system is assumed inhabited. -/
theorem IsCompletelyAdmissible.isCompletelyPositive
    {S : MatrixMap (a × b) (c × d)}
    (hS : IsCompletelyAdmissible.{u, v, w, x, y, z} S) :
    MatrixMap.IsCompletelyPositive S := by
  apply (MatrixMap.isCompletelyPositive_iff_mapsPositiveUnderAncilla_fin S).mpr
  intro n X hX
  let R := PUnit.{y + 1}
  let T := ULift.{z} (Fin n)
  let f : ((a × R) × (b × T)) → ((a × b) × Fin n) :=
    fun p => ((p.1.1, p.2.1), p.2.2.down)
  let g : ((c × d) × Fin n) → ((c × R) × (d × T)) :=
    fun p => ((p.1.1, PUnit.unit), (p.1.2, ULift.up p.2))
  have hpos := hS.ancillaryExtension_posSemidef (X.submatrix f f) (hX.submatrix f)
  have hresult := hpos.submatrix g
  have heq : (ancillaryExtension S (X.submatrix f f)).submatrix g g =
      MatrixMap.kron S LinearMap.id X := by
    ext p q
    rw [Matrix.submatrix_apply, MatrixMap.kron_id_apply]
    change S (ancillaryBlock (X.submatrix f f)
      (PUnit.unit, ULift.up p.2) (PUnit.unit, ULift.up q.2)) p.1 q.1 = _
    rw [MatrixMap.map_eq_sum_single]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  exact heq ▸ hresult

end
end QIT.HigherOrder
