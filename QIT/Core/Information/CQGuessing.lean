/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Information.Smooth

/-!
# CQ guessing probability and conditional min-entropy dual program

This module sets up the finite-dimensional cq state-discrimination primal and
matrix-order dual program used to prove the normalized cq min-entropy
characterization from [Tomamichel2015FiniteResources, calculus.tex:81-89] and
[Tomamichel2015FiniteResources, calculus.tex:348-357].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

namespace Ensemble

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

/-! ## Primal and dual optimization surfaces -/

/-- The weighted quantum block `p_x rho_x` appearing in a cq ensemble. -/
def cqBlock (E : Ensemble ι b) (x : ι) : CMatrix b :=
  (E.probs x : ℂ) • (E.states x).matrix

omit [DecidableEq ι] in
@[simp]
theorem cqBlock_eq (E : Ensemble ι b) (x : ι) :
    E.cqBlock x = (E.probs x : ℂ) • (E.states x).matrix :=
  rfl

/-- The real-valued primal score of a POVM for cq guessing. -/
def cqPrimalValue (E : Ensemble ι b) (M : POVM ι b) : ℝ :=
  ((E.cqGuessingScore M : ℝ≥0) : ℝ)

@[simp]
theorem cqPrimalValue_eq (E : Ensemble ι b) (M : POVM ι b) :
    E.cqPrimalValue M = ((E.cqGuessingScore M : ℝ≥0) : ℝ) :=
  rfl

/-- The trace-form primal score of a POVM. This is the expression used by
matrix-order duality. -/
def cqPrimalTraceValue (E : Ensemble ι b) (M : POVM ι b) : ℝ :=
  ∑ x, ((E.cqBlock x * M.effects x).trace).re

omit [DecidableEq ι] in
@[simp]
theorem cqPrimalTraceValue_eq (E : Ensemble ι b) (M : POVM ι b) :
    E.cqPrimalTraceValue M = ∑ x, ((E.cqBlock x * M.effects x).trace).re :=
  rfl

/-- The probability-style cq guessing score agrees with its trace form. -/
theorem cqPrimalValue_eq_traceValue (E : Ensemble ι b) (M : POVM ι b) :
    E.cqPrimalValue M = E.cqPrimalTraceValue M := by
  classical
  simp only [cqPrimalValue, cqGuessingScore_eq, cqPrimalTraceValue, cqBlock,
    NNReal.coe_sum, NNReal.coe_mul, POVM.prob_eq_trace_re]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.trace_smul]

/-- The set of attainable cq guessing scores. -/
def cqPrimalValueSet (E : Ensemble ι b) : Set ℝ :=
  {score : ℝ | ∃ M : POVM ι b, score = E.cqPrimalValue M}

@[simp]
theorem cqPrimalValueSet_eq (E : Ensemble ι b) :
    E.cqPrimalValueSet = {score : ℝ | ∃ M : POVM ι b, score = E.cqPrimalValue M} :=
  rfl

/-- The guessing probability is the supremum of the primal value set. -/
theorem cqGuessingProbability_eq_sSup_primalValueSet (E : Ensemble ι b) :
    E.cqGuessingProbability = sSup E.cqPrimalValueSet :=
  rfl

/-- Dual feasibility for cq discrimination: find a positive semidefinite matrix
dominating every weighted ensemble block. -/
def cqDualFeasible (E : Ensemble ι b) (T : CMatrix b) : Prop :=
  T.PosSemidef ∧ ∀ x, E.cqBlock x ≤ T

omit [DecidableEq ι] in
@[simp]
theorem cqDualFeasible_eq (E : Ensemble ι b) (T : CMatrix b) :
    E.cqDualFeasible T ↔ T.PosSemidef ∧ ∀ x, E.cqBlock x ≤ T :=
  Iff.rfl

/-- The dual objective `Tr T`, read as a real number for Hermitian/psd `T`. -/
def cqDualValue (_E : Ensemble ι b) (T : CMatrix b) : ℝ :=
  T.trace.re

omit [DecidableEq ι] in
@[simp]
theorem cqDualValue_eq (E : Ensemble ι b) (T : CMatrix b) :
    E.cqDualValue T = T.trace.re :=
  rfl

/-- The set of objective values attained by dual-feasible matrices. -/
def cqDualValueSet (E : Ensemble ι b) : Set ℝ :=
  {value : ℝ | ∃ T : CMatrix b, E.cqDualFeasible T ∧ value = E.cqDualValue T}

omit [DecidableEq ι] in
@[simp]
theorem cqDualValueSet_eq (E : Ensemble ι b) :
    E.cqDualValueSet =
      {value : ℝ | ∃ T : CMatrix b, E.cqDualFeasible T ∧ value = E.cqDualValue T} :=
  rfl

/-- The dual optimum as an infimum over feasible matrix traces. -/
def cqDualOptimalValue (E : Ensemble ι b) : ℝ :=
  sInf E.cqDualValueSet

omit [DecidableEq ι] in
@[simp]
theorem cqDualOptimalValue_eq (E : Ensemble ι b) :
    E.cqDualOptimalValue = sInf E.cqDualValueSet :=
  rfl

private theorem trace_mul_posSemidef_re_nonneg {A B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B).trace).re := by
  let S := psdSqrt A
  have hpsd : (S * B * S).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    dsimp [S] at h
    rw [psdSqrt_isHermitian A] at h
    exact h
  have htrace : 0 ≤ (S * B * S).trace :=
    Matrix.PosSemidef.trace_nonneg hpsd
  have hEq : (A * B).trace = (S * B * S).trace := by
    have hsqrt : S * S = A := by
      simpa [S] using psdSqrt_mul_self_of_posSemidef hA
    rw [← hsqrt]
    calc
      ((S * S) * B).trace = (S * (S * B)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((S * B) * S).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (S * B * S).trace := by
        rw [Matrix.mul_assoc]
  rw [hEq]
  exact htrace.1

namespace Classical

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

omit [DecidableEq b] in
private theorem blockDiagonal_posSemidef (blocks : ι → CMatrix b)
    (hblocks : ∀ x, (blocks x).PosSemidef) :
    (Classical.blockDiagonal blocks).PosSemidef := by
  classical
  unfold Classical.blockDiagonal
  exact Matrix.posSemidef_sum Finset.univ fun x _ =>
    (posSemidef_single x).kronecker (hblocks x)

omit [Fintype b] [DecidableEq b] in
private theorem blockDiagonal_sub (blocks blocks' : ι → CMatrix b) :
    Classical.blockDiagonal (fun x => blocks x - blocks' x) =
      Classical.blockDiagonal blocks - Classical.blockDiagonal blocks' := by
  classical
  unfold Classical.blockDiagonal
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext xi xj
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

omit [Fintype b] [DecidableEq b] in
private theorem blockDiagonal_smul (c : ℂ) (blocks : ι → CMatrix b) :
    Classical.blockDiagonal (fun x => c • blocks x) =
      c • Classical.blockDiagonal blocks := by
  classical
  unfold Classical.blockDiagonal
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext xi xj
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

end Classical

private theorem cqState_eq_blockDiagonal_cqBlock (E : Ensemble ι b) :
    E.cqState.matrix = Classical.blockDiagonal fun x => E.cqBlock x := by
  rw [Classical.cqState_eq_blockDiagonal]
  rfl

private theorem identityTensorStateMatrix_eq_blockDiagonal (σ : State b) :
    State.identityTensorStateMatrix (a := ι) σ =
      Classical.blockDiagonal fun _ : ι => σ.matrix := by
  classical
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨x', j⟩
  by_cases hxx' : x = x'
  · subst hxx'
    have hblock :=
      congrFun (congrFun (Classical.blockDiagonal_block_self
        (fun _ : ι => σ.matrix) x) i) j
    simp only [Classical.block] at hblock
    simpa [State.identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply]
      using hblock.symm
  · simp [Classical.blockDiagonal, State.identityTensorStateMatrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, hxx']
    have hblock :=
      congrFun (congrFun (Classical.blockDiagonal_block_ne
        (fun _ : ι => σ.matrix) hxx') i) j
    simp only [Classical.block] at hblock
    exact hblock.symm

/-- Weak duality for cq guessing: every dual-feasible matrix upper-bounds every
POVM guessing score. -/
theorem cqPrimalValue_le_dualValue (E : Ensemble ι b) (M : POVM ι b) {T : CMatrix b}
    (hT : E.cqDualFeasible T) :
    E.cqPrimalValue M ≤ E.cqDualValue T := by
  classical
  rw [cqPrimalValue_eq_traceValue]
  calc
    E.cqPrimalTraceValue M ≤ ∑ x, ((T * M.effects x).trace).re := by
      simp only [cqPrimalTraceValue]
      refine Finset.sum_le_sum fun x _ => ?_
      have hdiff : (T - E.cqBlock x).PosSemidef := by
        simpa [Matrix.le_iff] using hT.2 x
      have hnonneg := trace_mul_posSemidef_re_nonneg (b := b) hdiff (M.pos x)
      have htrace :
          (((T - E.cqBlock x) * M.effects x).trace).re =
            ((T * M.effects x).trace).re -
              ((E.cqBlock x * M.effects x).trace).re := by
        simp [Matrix.sub_mul, Matrix.trace_sub]
      linarith
    _ = ((T * (∑ x, M.effects x)).trace).re := by
      rw [← Complex.re_sum]
      congr 1
      calc
        (∑ x, (T * M.effects x).trace) = (∑ x, T * M.effects x).trace := by
          rw [Matrix.trace_sum]
        _ = (T * (∑ x, M.effects x)).trace := by
          congr 1
          simpa using (Matrix.mul_sum Finset.univ M.effects T).symm
    _ = E.cqDualValue T := by
      rw [M.sum_eq_one]
      simp [cqDualValue]

/-- Every dual-feasible matrix upper-bounds every value in the primal value set. -/
theorem cqPrimalValueSet_le_dualValue (E : Ensemble ι b) {T : CMatrix b}
    (hT : E.cqDualFeasible T) {score : ℝ} (hscore : score ∈ E.cqPrimalValueSet) :
    score ≤ E.cqDualValue T := by
  rcases hscore with ⟨M, rfl⟩
  exact cqPrimalValue_le_dualValue E M hT

/-- Weak duality at the supremum level: any dual-feasible matrix upper-bounds
the cq guessing probability. -/
theorem cqGuessingProbability_le_dualValue (E : Ensemble ι b) {T : CMatrix b}
    (hT : E.cqDualFeasible T) :
    E.cqGuessingProbability ≤ E.cqDualValue T := by
  rw [cqGuessingProbability_eq_sSup_primalValueSet]
  exact Real.sSup_le
    (fun score hscore => cqPrimalValueSet_le_dualValue E hT hscore)
    (Matrix.PosSemidef.trace_nonneg hT.1).1

omit [Fintype ι] in
private theorem identityTensorStateMatrix_block_self (σ : State b) (x : ι) :
    Classical.block (State.identityTensorStateMatrix (a := ι) σ) x x = σ.matrix := by
  ext i j
  simp [Classical.block, State.identityTensorStateMatrix, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

/-- Every conditional-min-entropy feasible pair gives a feasible matrix for the
cq guessing dual program. -/
theorem cqDualFeasible_of_conditionalMinEntropyFeasible (E : Ensemble ι b) (σ : State b)
    (lam : ℝ)
    (h : State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam) :
    E.cqDualFeasible ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) := by
  classical
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    rw [Complex.zero_le_real]
    positivity
  refine ⟨σ.pos.smul hc_nonneg, fun x => ?_⟩
  rw [Matrix.le_iff]
  have hdiff :
      (c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix).PosSemidef := by
    simpa [c, State.ConditionalMinEntropyFeasible, Matrix.le_iff] using h
  have hblock := hdiff.submatrix (fun i : b => (x, i))
  have hblock_eq :
      Matrix.submatrix
          (c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix)
          (fun i : b => (x, i)) (fun i : b => (x, i)) =
        c • σ.matrix - E.cqBlock x := by
    ext i j
    have hblock_id := congrFun (congrFun (identityTensorStateMatrix_block_self (σ := σ) x) i) j
    have hblock_cq := congrFun (congrFun (Classical.cqState_block_self E x) i) j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, cqBlock, smul_eq_mul,
      Classical.block] at hblock_id hblock_cq ⊢
    rw [hblock_id, hblock_cq]
  rw [← hblock_eq]
  exact hblock

/-- Blockwise domination by the same scaled `B` state is exactly the global cq
order constraint used by conditional min-entropy. -/
theorem conditionalMinEntropyFeasible_of_cqBlock_le (E : Ensemble ι b) (σ : State b)
    (lam : ℝ)
    (hblock : ∀ x, E.cqBlock x ≤ (Real.rpow 2 (-lam) : ℂ) • σ.matrix) :
    State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam := by
  classical
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  rw [State.ConditionalMinEntropyFeasible_eq, Matrix.le_iff]
  have hblocks : ∀ x, (c • σ.matrix - E.cqBlock x).PosSemidef := by
    intro x
    simpa [c, Matrix.le_iff] using hblock x
  have hmatrix :
      (c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix) =
        Classical.blockDiagonal fun x => c • σ.matrix - E.cqBlock x := by
    calc
      c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix =
          c • Classical.blockDiagonal (fun _ : ι => σ.matrix) -
            Classical.blockDiagonal (fun x => E.cqBlock x) := by
            rw [identityTensorStateMatrix_eq_blockDiagonal, cqState_eq_blockDiagonal_cqBlock]
      _ = Classical.blockDiagonal (fun x => c • σ.matrix) -
            Classical.blockDiagonal (fun x => E.cqBlock x) := by
            rw [← Classical.blockDiagonal_smul]
      _ = Classical.blockDiagonal (fun x => c • σ.matrix - E.cqBlock x) := by
            rw [Classical.blockDiagonal_sub]
  rw [hmatrix]
  exact Classical.blockDiagonal_posSemidef (fun x => c • σ.matrix - E.cqBlock x) hblocks

/-- The state-scaled cq dual constraint implies the conditional-min-entropy
order constraint. -/
theorem conditionalMinEntropyFeasible_of_cqDualFeasible_stateScale
    (E : Ensemble ι b) (σ : State b) (lam : ℝ)
    (hT : E.cqDualFeasible ((Real.rpow 2 (-lam) : ℂ) • σ.matrix)) :
    State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam :=
  conditionalMinEntropyFeasible_of_cqBlock_le E σ lam hT.2

/-- Conditional-min-entropy feasibility is equivalent to the corresponding
state-scaled cq guessing dual feasibility. -/
theorem conditionalMinEntropyFeasible_iff_cqDualFeasible_stateScale
    (E : Ensemble ι b) (σ : State b) (lam : ℝ) :
    State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam ↔
      E.cqDualFeasible ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) :=
  ⟨cqDualFeasible_of_conditionalMinEntropyFeasible E σ lam,
    conditionalMinEntropyFeasible_of_cqDualFeasible_stateScale E σ lam⟩

/-- Any feasible conditional-min-entropy exponent gives an upper bound on the
cq guessing probability. -/
theorem cqGuessingProbability_le_rpow_neg_of_conditionalMinEntropyFeasible
    (E : Ensemble ι b) (σ : State b) (lam : ℝ)
    (h : State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam) :
    E.cqGuessingProbability ≤ Real.rpow 2 (-lam) := by
  let T : CMatrix b := (Real.rpow 2 (-lam) : ℂ) • σ.matrix
  have hT : E.cqDualFeasible T :=
    cqDualFeasible_of_conditionalMinEntropyFeasible E σ lam h
  calc
    E.cqGuessingProbability ≤ E.cqDualValue T :=
      cqGuessingProbability_le_dualValue E hT
    _ = Real.rpow 2 (-lam) := by
      simp [T, cqDualValue, Matrix.trace_smul, σ.trace_eq_one]

end Ensemble

end

end QIT
