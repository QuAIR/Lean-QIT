/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.ExtractorAnalytic
public import QIT.States.TraceNorm.PositivePart
public import QIT.Information.CQGuessing

/-!
# Public-seed trace-distance bridge for extractors

This module contains the normalized trace-distance packaging needed to compare
the full extractor output with the seed-averaged per-seed extractor outputs.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe uF uZ uS ue

noncomputable section

variable {F : Type uF} {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype F] [DecidableEq F]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype e] [DecidableEq e]

/-- The uniform extractor-output distribution on `S`. -/
def uniformExtractorOutputProb : S -> ℝ≥0 :=
  fun _ => (Fintype.card S : ℝ≥0)⁻¹

omit [DecidableEq S] in
theorem uniformExtractorOutputProb_sum :
    (∑ s : S, uniformExtractorOutputProb (S := S) s) = 1 := by
  simp [uniformExtractorOutputProb, Finset.sum_const, Fintype.card_ne_zero]

/-- The ideal uniform extractor output state on the output alphabet. -/
def uniformExtractorOutputState : State S :=
  Classical.diagonalState
    (uniformExtractorOutputProb (S := S))
    (uniformExtractorOutputProb_sum (S := S))

@[simp]
theorem uniformExtractorOutputState_matrix :
    (uniformExtractorOutputState (S := S)).matrix =
      Matrix.diagonal fun s => (uniformExtractorOutputProb (S := S) s : ℂ) :=
  rfl

/-- The ideal extractor output associated to a real `S × (F × E)` output state. -/
def idealExtractorOutputState (ρ : State (S × (F × e))) : State (S × (F × e)) :=
  (uniformExtractorOutputState (S := S)).prod ρ.marginalB

@[simp]
theorem idealExtractorOutputState_matrix (ρ : State (S × (F × e))) :
    (idealExtractorOutputState ρ).matrix =
      Matrix.kronecker (uniformExtractorOutputState (S := S)).matrix ρ.marginalB.matrix :=
  rfl

/-- Normalized secrecy distance of an extractor output from its ideal uniform-output state. -/
def extractorSecrecyDistance (ρ : State (S × (F × e))) : ℝ :=
  ρ.normalizedTraceDistance (idealExtractorOutputState ρ)

@[simp]
theorem extractorSecrecyDistance_eq_normalizedTraceDistance
    (ρ : State (S × (F × e))) :
    extractorSecrecyDistance ρ =
      ρ.normalizedTraceDistance (idealExtractorOutputState ρ) :=
  rfl

variable [Nonempty F]
variable (H : HashFamily F Z S)

/-- The side-information marginal of one fixed-seed extractor output. -/
def extractorSeedSideInfoMatrix (E : Ensemble Z e) (f : F) : CMatrix e :=
  partialTraceA (a := S) (b := e) (extractorSeedOutputMatrix H E f)

@[simp]
theorem extractorSeedSideInfoMatrix_eq_partialTraceA (E : Ensemble Z e) (f : F) :
    extractorSeedSideInfoMatrix H E f =
      partialTraceA (a := S) (b := e) (extractorSeedOutputMatrix H E f) :=
  rfl

/-- The per-seed ideal matrix: uniform extractor output tensor the seed's side information. -/
def extractorSeedIdealMatrix (E : Ensemble Z e) (f : F) : CMatrix (S × e) :=
  Matrix.kronecker (uniformExtractorOutputState (S := S)).matrix
    (extractorSeedSideInfoMatrix H E f)

@[simp]
theorem extractorSeedIdealMatrix_eq_kronecker (E : Ensemble Z e) (f : F) :
    extractorSeedIdealMatrix H E f =
      Matrix.kronecker (uniformExtractorOutputState (S := S)).matrix
        (extractorSeedSideInfoMatrix H E f) :=
  rfl

/-- Per-seed normalized trace distance to the per-seed ideal matrix. -/
def extractorSeedTraceDistance (E : Ensemble Z e) (f : F) : ℝ :=
  normalizedTraceDistance (extractorSeedOutputMatrix H E f) (extractorSeedIdealMatrix H E f)

@[simp]
theorem extractorSeedTraceDistance_eq_normalizedTraceDistance (E : Ensemble Z e) (f : F) :
    extractorSeedTraceDistance H E f =
      normalizedTraceDistance (extractorSeedOutputMatrix H E f) (extractorSeedIdealMatrix H E f) :=
  rfl

/-- Seed-averaged per-seed normalized trace distance. -/
def extractorSeedAverageTraceDistance (E : Ensemble Z e) : ℝ :=
  ∑ f, (H.prob f : ℝ) * extractorSeedTraceDistance H E f

@[simp]
theorem extractorSeedAverageTraceDistance_eq_sum (E : Ensemble Z e) :
    extractorSeedAverageTraceDistance H E =
      ∑ f, (H.prob f : ℝ) * extractorSeedTraceDistance H E f :=
  rfl

/-- Seed-averaged quadratic term used by the abstract extractor analytic bridge. -/
def extractorSeedQuadraticAverage (q : F → ℝ) : ℝ :=
  ∑ f, (H.prob f : ℝ) * q f

@[simp]
theorem extractorSeedQuadraticAverage_eq_sum (q : F → ℝ) :
    extractorSeedQuadraticAverage H q = ∑ f, (H.prob f : ℝ) * q f :=
  rfl

namespace HashFamily

private def seedBlock (M : CMatrix (S × (F × e))) (f : F) : CMatrix (S × e) :=
  fun se se' => M (se.1, (f, se.2)) (se'.1, (f, se'.2))

private theorem seedBlock_posSemidef {M : CMatrix (S × (F × e))}
    (hM : M.PosSemidef) (f : F) :
    (seedBlock (S := S) (e := e) M f).PosSemidef := by
  simpa [seedBlock] using hM.submatrix (fun se : S × e => (se.1, (f, se.2)))

private theorem seedBlock_le_one {M : CMatrix (S × (F × e))} (hM : M ≤ 1) (f : F) :
    seedBlock (S := S) (e := e) M f ≤ 1 := by
  rw [Matrix.le_iff] at hM ⊢
  have h := hM.submatrix (fun se : S × e => (se.1, (f, se.2)))
  convert h using 1
  ext x y
  rcases x with ⟨sx, ix⟩
  rcases y with ⟨sy, iy⟩
  simp [seedBlock, Matrix.sub_apply, Matrix.one_apply]

private theorem trace_mul_seed_decomp_complex {H P : CMatrix (S × (F × e))}
    (hoff : ∀ (s s' : S) (f f' : F) (i j : e),
      f ≠ f' -> H (s, (f, i)) (s', (f', j)) = 0) :
    (H * P).trace =
      ∑ f : F, ((seedBlock (S := S) (e := e) H f) * seedBlock P f).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, seedBlock, Fintype.sum_prod_type]
  calc
    (∑ s : S, ∑ f : F, ∑ i : e, ∑ s' : S, ∑ f' : F, ∑ j : e,
        H (s, f, i) (s', f', j) * P (s', f', j) (s, f, i)) =
      ∑ s : S, ∑ f : F, ∑ i : e, ∑ s' : S, ∑ j : e,
        H (s, f, i) (s', f, j) * P (s', f, j) (s, f, i) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        refine Finset.sum_congr rfl fun f _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun s' _ => ?_
        exact Finset.sum_eq_single_of_mem f (Finset.mem_univ _) (fun f' _ hf' => by
          have hne : f ≠ f' := fun h => hf' h.symm
          simp [hoff s s' f f' i, hne])
    _ = ∑ f : F, ∑ s : S, ∑ i : e, ∑ s' : S, ∑ j : e,
        H (s, f, i) (s', f, j) * P (s', f, j) (s, f, i) := by
        rw [Finset.sum_comm]

private theorem trace_mul_seed_decomp {H P : CMatrix (S × (F × e))}
    (hoff : ∀ (s s' : S) (f f' : F) (i j : e),
      f ≠ f' -> H (s, (f, i)) (s', (f', j)) = 0) :
    ((H * P).trace).re =
      ∑ f : F, (((seedBlock (S := S) (e := e) H f) * seedBlock P f).trace).re := by
  rw [trace_mul_seed_decomp_complex (S := S) (e := e) hoff]
  simp

private theorem seedBlock_isHermitian {M : CMatrix (S × (F × e))}
    (hM : M.IsHermitian) (f : F) :
    (seedBlock (S := S) (e := e) M f).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rcases x with ⟨sx, ix⟩
  rcases y with ⟨sy, iy⟩
  simpa [seedBlock, Matrix.conjTranspose] using
    congrFun (congrFun hM (sx, (f, ix))) (sy, (f, iy))

private theorem posPart_trace_seedBlock_le_sum {H : CMatrix (S × (F × e))}
    (hH : H.IsHermitian)
    (hoff : ∀ (s s' : S) (f f' : F) (i j : e),
      f ≠ f' -> H (s, (f, i)) (s', (f', j)) = 0) :
    (H⁺).trace.re ≤ ∑ f : F, ((seedBlock (S := S) (e := e) H f)⁺).trace.re := by
  classical
  let P : CMatrix (S × (F × e)) := positiveSpectralProjector H hH
  have hscore : ((H * P).trace).re = (H⁺).trace.re := by
    simpa [P] using positiveSpectralProjector_score_eq_posPart_trace H hH
  rw [← hscore]
  rw [trace_mul_seed_decomp (S := S) (e := e) (H := H) (P := P) hoff]
  refine Finset.sum_le_sum fun f _ => ?_
  have hPpos : (seedBlock (S := S) (e := e) P f).PosSemidef :=
    seedBlock_posSemidef (S := S) (e := e)
      (positiveSpectralProjector_posSemidef H hH) f
  have hPle : seedBlock (S := S) (e := e) P f ≤ 1 :=
    seedBlock_le_one (S := S) (e := e) (positiveSpectralProjector_le_one H hH) f
  exact hermitian_trace_mul_effect_le_posPart_trace
    (seedBlock (S := S) (e := e) H f) (seedBlock P f)
    (seedBlock_isHermitian (S := S) (e := e) hH f) hPpos hPle

private theorem extractorSeedOutputMatrix_trace (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f).trace = 1 := by
  unfold extractorSeedOutputMatrix
  simp only [Matrix.trace_sum, Matrix.trace_smul]
  calc
    (∑ z : Z, (E.probs z) •
        (Matrix.kronecker (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
          (E.states z).matrix).trace) =
      ∑ z : Z, ((E.probs z : ℝ≥0) : ℂ) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have htrace :
            (Matrix.kronecker (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
              (E.states z).matrix).trace = 1 := by
          simpa [Matrix.kronecker] using
            (Matrix.trace_kronecker
              (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
              (E.states z).matrix).trans
              (by rw [trace_single_one, if_pos rfl, (E.states z).trace_eq_one]; norm_num)
        rw [htrace]
        exact (Algebra.algebraMap_eq_smul_one _).symm
    _ = ↑(∑ z : Z, E.probs z) := by simp
    _ = 1 := by rw [E.weights_sum]; rfl

private theorem extractorSeedOutputMatrix_posSemidef (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f).PosSemidef := by
  unfold extractorSeedOutputMatrix
  exact Matrix.posSemidef_sum Finset.univ fun z _ =>
    (((posSemidef_single (H.hash f z)).kronecker (E.states z).pos).smul
      (NNReal.coe_nonneg (E.probs z)))

private theorem extractorSeedIdealMatrix_trace (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedIdealMatrix H E f).trace = 1 := by
  unfold extractorSeedIdealMatrix extractorSeedSideInfoMatrix
  rw [show (Matrix.kronecker (uniformExtractorOutputState (S := S)).matrix
      (partialTraceA (extractorSeedOutputMatrix H E f))).trace =
        (uniformExtractorOutputState (S := S)).matrix.trace *
          (partialTraceA (extractorSeedOutputMatrix H E f)).trace by
    simpa [Matrix.kronecker] using
      Matrix.trace_kronecker (uniformExtractorOutputState (S := S)).matrix
        (partialTraceA (extractorSeedOutputMatrix H E f))]
  rw [uniformExtractorOutputState_matrix]
  have hU : (Matrix.diagonal fun s : S => (uniformExtractorOutputProb (S := S) s : ℂ)).trace = 1 := by
    change (uniformExtractorOutputState (S := S)).matrix.trace = 1
    exact (uniformExtractorOutputState (S := S)).trace_eq_one
  rw [hU, partialTraceA_trace, extractorSeedOutputMatrix_trace H E f]
  norm_num

private theorem extractorSeedIdealMatrix_posSemidef (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedIdealMatrix H E f).PosSemidef := by
  unfold extractorSeedIdealMatrix extractorSeedSideInfoMatrix
  exact (uniformExtractorOutputState (S := S)).pos.kronecker
    (partialTraceA_posSemidef (extractorSeedOutputMatrix_posSemidef H E f))

private theorem seedDiff_trace_zero (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f).trace = 0 := by
  rw [Matrix.trace_sub, extractorSeedOutputMatrix_trace H E f,
    extractorSeedIdealMatrix_trace H E f]
  norm_num

private theorem seedDiff_isHermitian (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f).IsHermitian :=
  (extractorSeedOutputMatrix_posSemidef H E f).isHermitian.sub
    (extractorSeedIdealMatrix_posSemidef H E f).isHermitian

private theorem extractorOutputMatrix_seed_offdiag (H : HashFamily F Z S)
    (E : Ensemble Z e) {s s' : S} {f f' : F} {i j : e} (hff : f ≠ f') :
    extractorOutputMatrix H E (s, (f, i)) (s', (f', j)) = 0 := by
  unfold extractorOutputMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  refine Finset.sum_eq_zero fun g _ => ?_
  have hsingle : Matrix.single g g (1 : ℂ) f f' = 0 := by
    rw [Matrix.single_apply]
    by_cases hgf : g = f
    · subst hgf
      simp [hff]
    · simp [hgf]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hsingle]

private theorem extractorOutputMarginalB_seed_offdiag (H : HashFamily F Z S)
    (E : Ensemble Z e) {f f' : F} {i j : e} (hff : f ≠ f') :
    (extractorOutputState H E).marginalB.matrix (f, i) (f', j) = 0 := by
  simp [State.marginalB_matrix, partialTraceA, extractorOutputState_matrix,
    extractorOutputMatrix_seed_offdiag H E hff]

private theorem seedBlock_extractorOutputMatrix (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    seedBlock (S := S) (e := e) (extractorOutputMatrix H E) f =
      H.prob f • extractorSeedOutputMatrix H E f := by
  ext se se'
  simp only [seedBlock]
  have hblock := congrFun (congrFun (extractorOutputSeedBlock_eq_sum H E f) se) se'
  simp only [extractorOutputSeedBlock, Matrix.sum_apply, Matrix.smul_apply] at hblock
  rw [hblock]
  simp only [extractorSeedOutputMatrix, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  let A : ℂ :=
    Matrix.single (H.hash f z) (H.hash f z) 1 se.1 se'.1 *
      (E.states z).matrix se.2 se'.2
  change (E.probs z * H.prob f) • A = H.prob f • (E.probs z • A)
  rw [← smul_smul]
  exact smul_comm (E.probs z) (H.prob f) A

private theorem extractorOutputMarginalB_seedBlock (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (fun i j => (extractorOutputState H E).marginalB.matrix (f, i) (f, j)) =
      H.prob f • extractorSeedSideInfoMatrix H E f := by
  ext i j
  simp only [State.marginalB_matrix, partialTraceA, extractorOutputState_matrix,
    extractorSeedSideInfoMatrix, Matrix.smul_apply]
  change (∑ s : S,
      seedBlock (S := S) (e := e) (extractorOutputMatrix H E) f (s, i) (s, j)) =
    H.prob f • (∑ s : S, extractorSeedOutputMatrix H E f (s, i) (s, j))
  rw [seedBlock_extractorOutputMatrix H E f]
  simp [Matrix.smul_apply, Finset.smul_sum]

private theorem seedBlock_idealExtractorOutputMatrix (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    seedBlock (S := S) (e := e)
      (idealExtractorOutputState (extractorOutputState H E)).matrix f =
        H.prob f • extractorSeedIdealMatrix H E f := by
  ext se se'
  rcases se with ⟨s, i⟩
  rcases se' with ⟨s', j⟩
  simp only [seedBlock, idealExtractorOutputState_matrix, extractorSeedIdealMatrix,
    Matrix.smul_apply]
  have hmarg :=
    congrFun (congrFun (extractorOutputMarginalB_seedBlock H E f) i) j
  simp only [Matrix.smul_apply] at hmarg
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hmarg]
  let A : ℂ := (uniformExtractorOutputState (S := S)).matrix s s'
  let B : ℂ := extractorSeedSideInfoMatrix H E f i j
  change A * (H.prob f • B) = H.prob f • (A * B)
  simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

private theorem seedBlock_fullDiff_eq_seedDiff (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    seedBlock (S := S) (e := e)
      ((extractorOutputState H E).matrix -
        (idealExtractorOutputState (extractorOutputState H E)).matrix) f =
        H.prob f •
          (extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f) := by
  ext se se'
  simp only [seedBlock, Matrix.sub_apply, Matrix.smul_apply]
  have hout :=
    congrFun (congrFun (seedBlock_extractorOutputMatrix H E f) se) se'
  have hideal :=
    congrFun (congrFun (seedBlock_idealExtractorOutputMatrix H E f) se) se'
  simp only [seedBlock, Matrix.smul_apply] at hout hideal
  rw [extractorOutputState_matrix, hout, hideal]
  simp [sub_eq_add_neg, smul_add, smul_neg]

private theorem fullDiff_seed_offdiag (H : HashFamily F Z S) (E : Ensemble Z e)
    {s s' : S} {f f' : F} {i j : e} (hff : f ≠ f') :
    ((extractorOutputState H E).matrix -
      (idealExtractorOutputState (extractorOutputState H E)).matrix)
        (s, (f, i)) (s', (f', j)) = 0 := by
  rw [Matrix.sub_apply, extractorOutputState_matrix, idealExtractorOutputState_matrix]
  rw [extractorOutputMatrix_seed_offdiag H E hff]
  have hmarg : (extractorOutputState H E).marginalB.matrix (f, i) (f', j) = 0 :=
    extractorOutputMarginalB_seed_offdiag H E hff
  change 0 -
      (uniformExtractorOutputState (S := S)).matrix s s' *
        (extractorOutputState H E).marginalB.matrix (f, i) (f', j) = 0
  rw [hmarg]
  simp

private theorem normalizedTraceDistance_eq_posPart_trace_of_seedDiff
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) :
    normalizedTraceDistance (extractorSeedOutputMatrix H E f) (extractorSeedIdealMatrix H E f) =
      (((extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f)⁺).trace).re := by
  let D : CMatrix (S × e) := extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f
  have hnorm := traceNorm_eq_two_posPart_trace_re_of_trace_zero D
    (by simpa [D] using seedDiff_isHermitian H E f)
    (by simpa [D] using seedDiff_trace_zero H E f)
  calc
    normalizedTraceDistance (extractorSeedOutputMatrix H E f) (extractorSeedIdealMatrix H E f) =
        (1 / 2 : ℝ) * traceNorm D := by rfl
    _ = (1 / 2 : ℝ) * (2 * (D⁺).trace.re) := by rw [hnorm]
    _ = (D⁺).trace.re := by ring

private theorem trace_seedBlock_smul_mul (c : ℝ≥0) (D E : CMatrix (S × e)) :
    (((c • D) * E).trace).re = (c : ℝ) * (((D * E).trace).re) := by
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp [NNReal.smul_def]

private theorem fullDiff_posPart_trace_le_seedAverage (H : HashFamily F Z S)
    (E : Ensemble Z e) :
    ((((extractorOutputState H E).matrix -
      (idealExtractorOutputState (extractorOutputState H E)).matrix)⁺).trace).re ≤
        extractorSeedAverageTraceDistance H E := by
  classical
  let Dfull : CMatrix (S × (F × e)) :=
    (extractorOutputState H E).matrix -
      (idealExtractorOutputState (extractorOutputState H E)).matrix
  have hDfullHerm : Dfull.IsHermitian := by
    dsimp [Dfull]
    exact (extractorOutputState H E).pos.isHermitian.sub
      (idealExtractorOutputState (extractorOutputState H E)).pos.isHermitian
  let P : CMatrix (S × (F × e)) := positiveSpectralProjector Dfull hDfullHerm
  have hscore : ((Dfull * P).trace).re = (Dfull⁺).trace.re := by
    simpa [P] using positiveSpectralProjector_score_eq_posPart_trace Dfull hDfullHerm
  calc
    (Dfull⁺).trace.re = ((Dfull * P).trace).re := hscore.symm
    _ = ∑ f : F, (((seedBlock (S := S) (e := e) Dfull f) * seedBlock P f).trace).re := by
      exact trace_mul_seed_decomp (S := S) (e := e) (H := Dfull) (P := P) (by
        intro s s' f f' i j hff
        dsimp [Dfull]
        simpa using fullDiff_seed_offdiag H E (s := s) (s' := s') (f := f)
          (f' := f') (i := i) (j := j) hff)
    _ ≤ ∑ f : F, (H.prob f : ℝ) * extractorSeedTraceDistance H E f := by
      refine Finset.sum_le_sum fun f _ => ?_
      let Dseed : CMatrix (S × e) :=
        extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f
      have hblock : seedBlock (S := S) (e := e) Dfull f = H.prob f • Dseed := by
        dsimp [Dfull, Dseed]
        simpa using seedBlock_fullDiff_eq_seedDiff H E f
      rw [hblock, trace_seedBlock_smul_mul]
      have hPpos : (seedBlock (S := S) (e := e) P f).PosSemidef :=
        seedBlock_posSemidef (S := S) (e := e)
          (positiveSpectralProjector_posSemidef Dfull hDfullHerm) f
      have hPle : seedBlock (S := S) (e := e) P f ≤ 1 :=
        seedBlock_le_one (S := S) (e := e)
          (positiveSpectralProjector_le_one Dfull hDfullHerm) f
      have hseed :
          (((Dseed * seedBlock P f).trace).re) ≤ ((Dseed⁺).trace).re :=
        hermitian_trace_mul_effect_le_posPart_trace Dseed (seedBlock P f)
          (by dsimp [Dseed]; exact seedDiff_isHermitian H E f) hPpos hPle
      have hprob_nonneg : 0 ≤ (H.prob f : ℝ) := NNReal.coe_nonneg _
      exact
        (mul_le_mul_of_nonneg_left hseed hprob_nonneg).trans_eq
          (by rw [← normalizedTraceDistance_eq_posPart_trace_of_seedDiff H E f]; rfl)
    _ = extractorSeedAverageTraceDistance H E := rfl

/--
The full extractor secrecy distance is bounded by the seed-average of the
per-seed trace distances.

This is the public-seed block-diagonal trace-distance averaging bridge used by
the direct leftover-hash proof. It is intentionally extractor-shaped rather
than a general block trace-norm theorem.
-/
theorem extractorSecrecyDistance_le_seedAverageTraceDistance
    (H : HashFamily F Z S) (E : Ensemble Z e) :
    extractorSecrecyDistance (extractorOutputState H E) ≤
      extractorSeedAverageTraceDistance H E := by
  let ρ : State (S × (F × e)) := extractorOutputState H E
  let σ : State (S × (F × e)) := idealExtractorOutputState ρ
  let D : CMatrix (S × (F × e)) := ρ.matrix - σ.matrix
  have hDherm : D.IsHermitian := by
    dsimp [D, ρ, σ]
    exact (extractorOutputState H E).pos.isHermitian.sub
      (idealExtractorOutputState (extractorOutputState H E)).pos.isHermitian
  have hDtrace : D.trace = 0 := by
    change ((extractorOutputState H E).matrix -
      (idealExtractorOutputState (extractorOutputState H E)).matrix).trace = 0
    rw [Matrix.trace_sub, (extractorOutputState H E).trace_eq_one,
      (idealExtractorOutputState (extractorOutputState H E)).trace_eq_one]
    norm_num
  have hnorm := traceNorm_eq_two_posPart_trace_re_of_trace_zero D hDherm hDtrace
  calc
    extractorSecrecyDistance (extractorOutputState H E) =
        (1 / 2 : ℝ) * traceNorm D := by rfl
    _ = (1 / 2 : ℝ) * (2 * (D⁺).trace.re) := by rw [hnorm]
    _ = (D⁺).trace.re := by ring
    _ ≤ extractorSeedAverageTraceDistance H E := by
      dsimp [D, ρ, σ]
      exact fullDiff_posPart_trace_le_seedAverage H E

/--
If every fixed-seed extractor trace distance is bounded by
`sqrt (d * q f)`, the squared seed-average trace distance is bounded by the
scaled seed-average quadratic term.
-/
theorem extractorSeedAverageTraceDistance_sq_le_scaled_quadraticAverage
    (H : HashFamily F Z S) (E : Ensemble Z e) (d : ℝ) (q : F → ℝ)
    (hd : 0 ≤ d) (hq : ∀ f, 0 ≤ q f)
    (hseed : ∀ f, extractorSeedTraceDistance H E f ≤ Real.sqrt (d * q f)) :
    (extractorSeedAverageTraceDistance H E) ^ 2 ≤
      d * extractorSeedQuadraticAverage H q := by
  exact extractor_traceDistance_average_sq_le H.prob H.prob_sum d
    (fun f => extractorSeedTraceDistance H E f) q hd
    (fun f => by
      simpa [extractorSeedTraceDistance] using
        normalizedTraceDistance_nonneg (extractorSeedOutputMatrix H E f)
          (extractorSeedIdealMatrix H E f))
    hq hseed

/--
Combining public-seed trace-distance averaging with the abstract finite
Jensen/Cauchy bridge gives a squared full extractor secrecy bound.
-/
theorem extractorSecrecyDistance_sq_le_scaled_quadraticAverage
    (H : HashFamily F Z S) (E : Ensemble Z e) (d : ℝ) (q : F → ℝ)
    (hd : 0 ≤ d) (hq : ∀ f, 0 ≤ q f)
    (hseed : ∀ f, extractorSeedTraceDistance H E f ≤ Real.sqrt (d * q f)) :
    (extractorSecrecyDistance (extractorOutputState H E)) ^ 2 ≤
      d * extractorSeedQuadraticAverage H q := by
  have hsec_nonneg :
      0 ≤ extractorSecrecyDistance (extractorOutputState H E) := by
    simpa [extractorSecrecyDistance] using
      State.normalizedTraceDistance_nonneg (extractorOutputState H E)
        (idealExtractorOutputState (extractorOutputState H E))
  have hseedAvg_nonneg :
      0 ≤ extractorSeedAverageTraceDistance H E := by
    exact Finset.sum_nonneg fun f _ =>
      mul_nonneg (NNReal.coe_nonneg _) (by
        simpa [extractorSeedTraceDistance] using
          normalizedTraceDistance_nonneg (extractorSeedOutputMatrix H E f)
            (extractorSeedIdealMatrix H E f))
  have hfull_le_avg :=
    extractorSecrecyDistance_le_seedAverageTraceDistance H E
  have hsquare_full :
      (extractorSecrecyDistance (extractorOutputState H E)) ^ 2 ≤
        (extractorSeedAverageTraceDistance H E) ^ 2 :=
    (sq_le_sq₀ hsec_nonneg hseedAvg_nonneg).2 hfull_le_avg
  exact hsquare_full.trans
    (extractorSeedAverageTraceDistance_sq_le_scaled_quadraticAverage H E d q
      hd hq hseed)

end HashFamily

end

end QIT.Security
