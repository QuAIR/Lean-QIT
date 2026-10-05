/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix.MarginalOrder

/-!
# Eigenvector support for projector sandwiches

A nonzero-eigenvalue eigenvector of a projector sandwich is supported on the
projector. Positive sandwiches have a unit top eigenvector
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:435-440].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

variable {a : Type*} [Fintype a]

/-- A nonzero-eigenvalue eigenvector of an idempotent sandwich lies in the
image of the idempotent; neither positivity nor normalization is needed. -/
theorem projector_mulVec_eq_self_of_sandwich_eigenvector
    (P Q : CMatrix a) (v : a → ℂ) (z : ℂ) (hP : P * P = P)
    (hz : z ≠ 0) (hv : (P * Q * P).mulVec v = z • v) : P.mulVec v = v := by
  have hPQ : P * (P * Q * P) = P * Q * P := by
    simp only [← Matrix.mul_assoc, hP]
  have h : z • P.mulVec v = z • v := by
    calc
      _ = P.mulVec (z • v) := (Matrix.mulVec_smul _ _ _).symm
      _ = P.mulVec ((P * Q * P).mulVec v) := by rw [hv]
      _ = (P * Q * P).mulVec v := by rw [Matrix.mulVec_mulVec, hPQ]
      _ = _ := hv
  simpa [smul_smul, hz] using congrArg (fun w : a → ℂ => z⁻¹ • w) h

/-- On a supported sandwich eigenvector the right projector can be removed. -/
theorem projector_mulVec_eq_of_sandwich_eigenvector
    (P Q : CMatrix a) (v : a → ℂ) (z : ℂ) (hP : P * P = P)
    (hz : z ≠ 0) (hv : (P * Q * P).mulVec v = z • v) :
    (P * Q).mulVec v = z • v := by
  have hs := projector_mulVec_eq_self_of_sandwich_eigenvector P Q v z hP hz hv
  rw [← Matrix.mulVec_mulVec, hs] at hv
  exact hv

/-- A nonzero PSD projector sandwich has a unit eigenvector at its operator
norm, supported on the projector
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:435-440]. -/
theorem exists_unit_top_eigenvector_supported
    [DecidableEq a]
    (P Q : CMatrix a) (hP : P.IsHermitian) (hPid : P * P = P)
    (hQ : Q.PosSemidef) (hn : 0 < ‖P * Q * P‖) :
    ∃ v : EuclideanSpace ℂ a, ‖v‖ = 1 ∧
      (P * Q * P).mulVec v = (‖P * Q * P‖ : ℂ) • (v : a → ℂ) ∧
      P.mulVec v = v ∧ (P * Q).mulVec v = (‖P * Q * P‖ : ℂ) • (v : a → ℂ) := by
  classical
  cases isEmpty_or_nonempty a with
  | inl he =>
    let := he
    have hzero : P * Q * P = 0 := Subsingleton.elim _ _
    simp [hzero] at hn
  | inr he =>
    let := he
    let : CStarAlgebra (CMatrix a) := {}
    have hA : (P * Q * P).PosSemidef := by
      simpa [hP.eq] using hQ.mul_mul_conjTranspose_same P
    have hmem : ‖P * Q * P‖ ∈ spectrum ℝ (P * Q * P) :=
      CStarAlgebra.norm_mem_spectrum_of_nonneg (P * Q * P) hA.nonneg
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
    obtain ⟨i, hi⟩ := hmem
    let v := hA.isHermitian.eigenvectorBasis i
    have hv : (P * Q * P).mulVec v = (‖P * Q * P‖ : ℂ) • (v : a → ℂ) := by
      simpa [v, hi] using hA.isHermitian.mulVec_eigenvectorBasis i
    have hz : (‖P * Q * P‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    exact ⟨v, hA.isHermitian.eigenvectorBasis.orthonormal.1 i, hv,
      projector_mulVec_eq_self_of_sandwich_eigenvector P Q v _ hPid hz hv,
      projector_mulVec_eq_of_sandwich_eigenvector P Q v _ hPid hz hv⟩

end

end QIT
