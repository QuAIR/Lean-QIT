/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.StrongConverse.TensorPower
public import QIT.Coding.Quantum.PolyApprox
public import QIT.Coding.Quantum.BlowingUp

/-!
# Finite-block approximation and code conversion

The polynomial approximation is transported to the recursive Stinespring
registers and then used in the fully quantum blowing-up bound
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:616-635].
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace QIT

noncomputable section

open QuantumPolyApprox

universe u

variable {a b e : Type u} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

namespace ReferenceIsometry

/-- The polynomial approximation on the recursive receiver/environment tensor
registers, with the norm budget determined by the single-use dimensions. -/
theorem exists_tensorPower_projectorApproximation_of_sherstovNOR
    (V : ReferenceIsometry a (b × e)) {c : ℝ} (w : SherstovNORWitness c)
    {n D : ℕ} (hD : 3 ≤ D) (hn : 2 * D ≤ n) :
    ∃ T : CMatrix (TensorPower b n × TensorPower e n),
      T * (V.tensorPowerBipartite n).imageProjector = (V.tensorPowerBipartite n).imageProjector ∧
      (V.tensorPowerBipartite n).imageProjector * T = (V.tensorPowerBipartite n).imageProjector ∧
      ‖T - (V.tensorPowerBipartite n).imageProjector‖ ≤ approximationError c n D ∧
      piNorm T ≤ approximationGamma
        (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) n D := by
  obtain ⟨S, hSP, hPS, herr, hpi⟩ := exists_projectorApproximation_of_sherstovNOR
    w V.imageProjector V.imageProjector_isHermitian V.imageProjector_idempotent hD hn
  let f := (tensorPowerEquiv (a := b) n).prodCongr (tensorPowerEquiv (a := e) n)
  let T := WireFam.matReindex f.symm S
  have hT : WireFam.matReindex f T = S := (WireFam.matReindex f).apply_symm_apply S
  have hP : WireFam.matReindex f (V.tensorPowerBipartite n).imageProjector =
      TensorPower.tensorPowMatrixPair V.imageProjector n :=
    V.tensorPowerBipartite_imageProjector_reindex n
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · apply (WireFam.matReindex f).injective
    rw [WireFam.matReindex_mul, hT, hP]
    exact hSP
  · apply (WireFam.matReindex f).injective
    rw [WireFam.matReindex_mul, hT, hP]
    exact hPS
  · have heq : ‖WireFam.matReindex f (T - (V.tensorPowerBipartite n).imageProjector)‖ =
        ‖T - (V.tensorPowerBipartite n).imageProjector‖ := matrix_reindex_norm f _
    rw [WireFam.matReindex_sub, hT, hP] at heq
    rwa [← heq]
  · rw [← piNorm_matReindex_prodCongr
      (tensorPowerEquiv (a := b) n) (tensorPowerEquiv (a := e) n) T, hT]
    exact hpi

end ReferenceIsometry

namespace EntanglementGenerationCode

variable {N : Channel a b} {r t : Type u}
  [Fintype r] [DecidableEq r] [Nonempty r] [Fintype t] [DecidableEq t]

/-- A sufficiently accurate polynomial approximation converts a block generation
code into a high-fidelity transmission code through the one-shot witness.
The dimension loss uses the single-use receiver/environment norm budget. -/
theorem exists_transmissionCode_tensorPower_of_sherstovNOR
    {n D : ℕ} (C : EntanglementGenerationCode (N.tensorPower n) r t)
    (V : ReferenceIsometry a (b × e)) (hV : V.outputChannel = N)
    {c : ℝ} (w : SherstovNORWitness c)
    (hFact1 : (N.tensorPower n).HasOneShotQuantumAchievability (V.tensorPowerBipartite n))
    (hD : 3 ≤ D) (hn : 2 * D ≤ n) {ε : ℝ}
    (hf : 0 < C.fidelity)
    (hΓ : 0 < approximationGamma
      (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) n D)
    (hε : 0 < ε) (hε₁ : ε < 1)
    (happrox : approximationError c n D ≤ ε * Real.sqrt C.fidelity / 2) :
    ∃ (m : Type u), ∃ (_ : Fintype m), ∃ (_ : DecidableEq m), ∃ (_ : Nonempty m),
      ∃ C' : EntanglementTransmissionCode (N.tensorPower n) m m m,
        1 - ε ^ 2 ≤ C'.fidelity ∧
        log2 (C.dimension : ℝ) + log2 C.fidelity -
          2 * log2 (approximationGamma
            (min ((Fintype.card b : ℝ)^2) ((Fintype.card e : ℝ)^2)) n D) -
          4 * log2 (2 / ε) - 1 ≤ log2 (Fintype.card m : ℝ) := by
  obtain ⟨T, hTP, hPT, herr, hpi⟩ :=
    V.exists_tensorPower_projectorApproximation_of_sherstovNOR w hD hn
  have hVn : (V.tensorPowerBipartite n).outputChannel = N.tensorPower n := by
    rw [V.tensorPowerBipartite_outputChannel, hV]
  exact C.exists_transmissionCode_of_oneShotAchievability (V.tensorPowerBipartite n)
    hVn hFact1 T hf hΓ hε hε₁ hTP hPT hpi (herr.trans happrox)

end EntanglementGenerationCode

end

end QIT
