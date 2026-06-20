/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Ensemble
public import QIT.Util.Matrix

/-!
# Classical-quantum states from ensembles

A classical-quantum (cq) state rho_XQ = Sum_x p_x |x><x|_X (x) rho_x is built
from a finite ensemble by block-diagonal embedding of each member state in the
classical register, instantiating the cq-state decomposition in the source
material [Tomamichel2015FiniteResources, prelim.tex:617-624].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a]
variable [DecidableEq ι] [DecidableEq a]

namespace Ensemble

/-- The classical-quantum state rho_XQ = Sum_x p_x |x><x|_X (x) rho_x. -/
def cqState (E : Ensemble ι a) : State (Prod ι a) where
  matrix := ∑ x, (E.probs x) • Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix
  pos := by
    exact Matrix.posSemidef_sum Finset.univ fun x _ =>
      ((posSemidef_single x).kronecker (E.states x).pos).smul (NNReal.coe_nonneg (E.probs x))
  trace_eq_one := by
    have hkr : ∀ x, (Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix).trace =
        (Matrix.single x x (1 : ℂ)).trace * (E.states x).matrix.trace := fun x =>
      Matrix.trace_kronecker _ _
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    rw [Finset.sum_congr rfl fun x _ => by rw [hkr x, trace_single_one, if_pos rfl, one_mul,
      (E.states x).trace_eq_one]]
    rw [Finset.sum_congr rfl fun x _ => (Algebra.algebraMap_eq_smul_one _).symm]
    rw [← map_sum (algebraMap ℝ≥0 ℂ) E.probs Finset.univ, E.weights_sum, map_one]

/-- The cq state's matrix is the weighted Kronecker sum. -/
@[simp]
theorem cqState_matrix (E : Ensemble ι a) :
    E.cqState.matrix =
      ∑ x, (E.probs x) • Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix := by
  rfl

/-- Tracing out the classical register gives the ensemble's average state. -/
theorem partialTraceA_cqState (E : Ensemble ι a) :
    partialTraceA (E.cqState.matrix) = E.averageState.matrix := by
  ext j j'
  simp only [cqState_matrix, averageState_matrix, partialTraceA, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
      fun x _ hx => by
        simp only [Matrix.single_apply, hx, if_false, and_self_iff, if_false, zero_mul,
          smul_zero]]
  simp only [Matrix.single_apply, and_self_iff, if_true, one_mul]

/-- Tracing out the quantum system gives the classical distribution diag(p). -/
theorem partialTraceB_cqState (E : Ensemble ι a) :
    partialTraceB (E.cqState.matrix) = Matrix.diagonal (fun x => ((E.probs x : ℂ))) := by
  ext x x'
  simp only [cqState_matrix, partialTraceB, Matrix.sum_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  by_cases h : x = x'
  · subst h
    rw [if_pos rfl]
    have key : ∀ (i : a),
        (∑ c : ι, (E.probs c • (Matrix.single c c (1 : ℂ) x x * (E.states c).matrix i i) : ℂ)) =
          (E.probs x • (E.states x).matrix i i : ℂ) := by
      intro i
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)
          fun c _ hc => by
            have hz : Matrix.single c c (1 : ℂ) x x = 0 := by
              rw [Matrix.single_apply, if_neg fun hcc => hc hcc.1]
            rw [hz, zero_mul, smul_zero]]
      simp only [Matrix.single_apply, and_self_iff, if_true, one_mul]
    simp only [key]
    rw [← Finset.smul_sum]
    show (E.probs x) • ((E.states x).matrix.trace) = ↑↑(E.probs x)
    rw [(E.states x).trace_eq_one, Algebra.smul_def, mul_one]
    rfl
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    have hz : Matrix.single j j (1 : ℂ) x x' = 0 := by
      rw [Matrix.single_apply, if_neg fun hcc => h (hcc.1.symm.trans hcc.2)]
    rw [hz, zero_mul, smul_zero]

end Ensemble

namespace Classical

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [DecidableEq ι]

/-- Extract the `(x, x')` classical block of a matrix on a classical-quantum product. -/
def block (X : CMatrix (Prod ι a)) (x x' : ι) : CMatrix a := fun i j => X (x, i) (x', j)

/-- Reconstruct a block-diagonal classical-quantum matrix from quantum blocks. -/
def blockDiagonal (blocks : ι → CMatrix a) : CMatrix (Prod ι a) :=
  ∑ x, Matrix.kronecker (Matrix.single x x (1 : ℂ)) (blocks x)

/-- Extracting a diagonal block from a block-diagonal matrix recovers that block. -/
@[simp]
theorem blockDiagonal_block_self (blocks : ι → CMatrix a) (x : ι) :
    block (blockDiagonal blocks) x x = blocks x := by
  ext i j
  simp only [block, blockDiagonal, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)
      fun y _ hy => by
        have hz : Matrix.single y y (1 : ℂ) x x = 0 := by
          rw [Matrix.single_apply, if_neg fun hyy => hy hyy.1]
        rw [hz, zero_mul]]
  simp only [Matrix.single_apply, and_self_iff, if_true, one_mul]

/-- Off-diagonal classical blocks of a block-diagonal matrix vanish. -/
@[simp]
theorem blockDiagonal_block_ne (blocks : ι → CMatrix a) {x x' : ι} (h : x ≠ x') :
    block (blockDiagonal blocks) x x' = 0 := by
  ext i j
  simp only [block, blockDiagonal, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hz : Matrix.single y y (1 : ℂ) x x' = 0 := by
    rw [Matrix.single_apply, if_neg fun hyy => h (hyy.1.symm.trans hyy.2)]
  rw [hz, zero_mul]

variable [Fintype a] [DecidableEq a]

/-- The cq-state matrix is reconstructed from the weighted diagonal quantum blocks. -/
theorem cqState_eq_blockDiagonal (E : Ensemble ι a) :
    E.cqState.matrix = blockDiagonal fun x => (E.probs x : ℂ) • (E.states x).matrix := by
  ext xi xj
  simp only [Ensemble.cqState_matrix, blockDiagonal, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Algebra.smul_def]
  rw [show (algebraMap ℝ≥0 ℂ) (E.probs x) = (E.probs x : ℂ) by rfl]
  ring

/-- The `(x, x)` block of a cq-state is the weighted quantum state for `x`. -/
@[simp]
theorem cqState_block_self (E : Ensemble ι a) (x : ι) :
    block E.cqState.matrix x x = (E.probs x : ℂ) • (E.states x).matrix := by
  rw [cqState_eq_blockDiagonal]
  exact blockDiagonal_block_self (fun y => (E.probs y : ℂ) • (E.states y).matrix) x

/-- Distinct classical labels have zero off-diagonal cq-state blocks. -/
@[simp]
theorem cqState_block_ne (E : Ensemble ι a) {x x' : ι} (h : x ≠ x') :
    block E.cqState.matrix x x' = 0 := by
  rw [cqState_eq_blockDiagonal]
  exact blockDiagonal_block_ne (fun y => (E.probs y : ℂ) • (E.states y).matrix) h

/-- A cq-state is reconstructed by placing its extracted diagonal blocks on the diagonal. -/
theorem cqState_eq_blockDiagonal_blocks (E : Ensemble ι a) :
    E.cqState.matrix = blockDiagonal fun x => block E.cqState.matrix x x := by
  rw [cqState_eq_blockDiagonal]
  apply congrArg blockDiagonal
  funext x
  symm
  exact blockDiagonal_block_self (fun y => (E.probs y : ℂ) • (E.states y).matrix) x

/-- Local classical bridge alias for the cq-state construction. -/
abbrev cqState (E : Ensemble ι a) : State (Prod ι a) := Ensemble.cqState E

/-- The cq-state matrix is the weighted Kronecker sum. -/
@[simp]
theorem cqState_matrix (E : Ensemble ι a) :
    E.cqState.matrix =
      ∑ x, (E.probs x) • Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix := by
  rfl

/-- Tracing out the classical register gives the ensemble's average state. -/
theorem partialTraceA_cqState (E : Ensemble ι a) :
    partialTraceA (E.cqState.matrix) = E.averageState.matrix := by
  simpa [cqState] using Ensemble.partialTraceA_cqState E

/-- Tracing out the quantum system gives the classical distribution diag(p). -/
theorem partialTraceB_cqState (E : Ensemble ι a) :
    partialTraceB (E.cqState.matrix) = Matrix.diagonal (fun x => ((E.probs x : ℂ))) := by
  simpa [cqState] using Ensemble.partialTraceB_cqState E

end Classical

end

end QIT
