/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Measurements.Instrument
public import QIT.Measurements.Projective
public import QIT.Channels.Stinespring

/-!
# Coordinate readout preserving the quantum output

A coordinate measurement of the second output register yields a finite quantum
instrument on the first register. Each branch is precisely a diagonal block,
equivalently projection on the observed flag followed by discarding that flag.
This supplies the final projective extraction in
[Chiribella2009Networks, comblong-pub.tex:1125-1133], whose proof performs
this coordinate extraction at lines 1213-1216.
No dimension, rank, or nonempty-system assumption is imposed.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT
universe u v w x
noncomputable section

namespace ProjectiveMeasurement

/-- The projective measurement in the coordinate basis. -/
def coordinate (ι : Type w) [Fintype ι] [DecidableEq ι] :
    ProjectiveMeasurement ι ι where
  effects i := Matrix.single i i 1
  isHermitian i := (posSemidef_single i).isHermitian
  idempotent i := by simp
  orthogonal i j hij := Matrix.single_mul_single_of_ne (c := (1 : ℂ)) i i j hij 1
  sum_eq_one := (POVM.coordinate ι).sum_eq_one

@[simp]
theorem coordinate_effects {ι : Type w} [Fintype ι] [DecidableEq ι] (i : ι) :
    (coordinate ι).effects i = Matrix.single i i 1 := rfl

end ProjectiveMeasurement

namespace MatrixMap

variable {b : Type v} {ι : Type w}
variable [Fintype b] [DecidableEq b] [Fintype ι] [DecidableEq ι]

/-- The Kraus operator which reads one coordinate of the flag and keeps the
quantum output. -/
def readoutKraus (i : ι) : Matrix b (b × ι) ℂ :=
  fun y x => if x = (y, i) then 1 else 0

/-- Observe one coordinate flag, retaining the unnormalized quantum output. -/
def readoutMap (i : ι) : MatrixMap (b × ι) b :=
  ofKraus (fun _ : Unit => readoutKraus (b := b) i)

/-- Reading the flag extracts its diagonal block for every input matrix. -/
@[simp]
theorem readoutMap_apply (i : ι) (X : CMatrix (b × ι)) :
    readoutMap i X = fun x y => X (x, i) (y, i) := by
  ext x y
  simp [readoutMap, ofKraus, readoutKraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_ite_eq']

omit [Fintype b] in
private theorem readoutProjector_eq_diagonal (i : ι) :
    Matrix.kronecker (1 : CMatrix b) (ProjectiveMeasurement.coordinate ι |>.effects i) =
      Matrix.diagonal (fun x : b × ι => if x.2 = i then (1 : ℂ) else 0) := by
  ext ⟨x, j⟩ ⟨y, k⟩
  by_cases hxy : x = y <;> by_cases hjk : j = k <;>
    by_cases hji : j = i <;> by_cases hki : k = i <;>
    simp_all [Matrix.kronecker, Matrix.single_apply, eq_comm]

/-- Readout is a von Neumann projection on the flag, followed by discarding
that flag. The identity factor preserves the quantum output. -/
theorem readoutMap_eq_partialTraceB_project (i : ι) (X : CMatrix (b × ι)) :
    readoutMap i X =
      QIT.partialTraceB
        (Matrix.kronecker (1 : CMatrix b) (ProjectiveMeasurement.coordinate ι |>.effects i) *
          X *
          Matrix.kronecker (1 : CMatrix b)
            (ProjectiveMeasurement.coordinate ι |>.effects i)) := by
  rw [readoutProjector_eq_diagonal]
  ext x y
  simp [QIT.partialTraceB, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Every coordinate readout branch is a quantum operation, including on
zero-dimensional systems. -/
theorem readoutMap_traceNonincreasingCP (i : ι) :
    TraceNonincreasingCP (readoutMap (b := b) i) where
  completelyPositive := ofKraus_isCompletelyPositive _
  traceNonincreasing X hX := by
    simp only [readoutMap_apply, Matrix.trace, Matrix.diag]
    rw [Fintype.sum_prod_type]
    simp only [Complex.re_sum]
    exact Finset.sum_le_sum fun x _ =>
      Finset.single_le_sum
        (fun j _ => (Complex.nonneg_iff.mp (hX.diag_nonneg (i := (x, j)))).1)
        (Finset.mem_univ i)

/-- Forgetting all readout outcomes is exactly discarding the flag. -/
theorem sum_readoutMap :
    (∑ i : ι, readoutMap (b := b) i) = (Channel.traceOutRight b ι).map := by
  ext X x y
  simp only [LinearMap.sum_apply, readoutMap_apply]
  exact Matrix.sum_apply x y Finset.univ (fun i => fun x y => X (x, i) (y, i))

end MatrixMap

namespace FiniteInstrument

variable {a : Type u} {b : Type v} {ι : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype ι] [DecidableEq ι]

/-- A channel with a flag output, followed by its coordinate projective
measurement, is an instrument retaining the other quantum output. -/
def readout (N : Channel a (b × ι)) : FiniteInstrument a b ι where
  branch i := (MatrixMap.readoutMap i).comp N.map
  branchTraceNonincreasingCP i :=
    (MatrixMap.readoutMap_traceNonincreasingCP i).comp
      (MatrixMap.traceNonincreasingCP_of_tracePreserving
        N.completelyPositive N.tracePreserving)
  total := (Channel.traceOutRight b ι).comp N
  sum_branch_eq_total := by
    ext X x y
    simp only [LinearMap.sum_apply, LinearMap.comp_apply,
      MatrixMap.readoutMap_apply]
    exact Matrix.sum_apply x y Finset.univ (fun i => fun x y => N.map X (x, i) (y, i))

/-- The physical outcome channel has the exact diagonal-block action on every
input operator, with no positivity or normalization restriction on that input. -/
@[simp]
theorem readout_branch_apply (N : Channel a (b × ι)) (i : ι) (X : CMatrix a) :
    (readout N).branch i X = fun x y => N.map X (x, i) (y, i) := by
  exact MatrixMap.readoutMap_apply i (N.map X)

/-- The unobserved output of readout is the original channel with its flag
discarded. -/
@[simp]
theorem readout_total (N : Channel a (b × ι)) :
    (readout N).total = (Channel.traceOutRight b ι).comp N := rfl

end FiniteInstrument

namespace ReferenceIsometry

variable {a : Type u} {b : Type v} {e : Type w} {ι : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype e] [DecidableEq e] [Fintype ι] [DecidableEq ι]

/-- Regroup the flag beside the quantum output, leaving the residual memory
last so that it can be discarded independently of the measured register. -/
def readoutEquiv : b × (e × ι) ≃ (b × ι) × e where
  toFun z := ((z.1, z.2.2), z.2.1)
  invFun z := (z.1.1, (z.2, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Projectively read a coordinate factor of the final memory of an isometry.
The other memory factor is discarded, and the quantum output is retained. -/
def readoutInstrument (V : ReferenceIsometry a (b × (e × ι))) :
    FiniteInstrument a b ι :=
  FiniteInstrument.readout (V.reindexOutput readoutEquiv).outputChannel

/-- Branch action is the projected coherent output with the unobserved memory
traced out, for every input matrix. -/
theorem readoutInstrument_branch_apply
    (V : ReferenceIsometry a (b × (e × ι))) (i : ι) (X : CMatrix a) (y z : b) :
    (V.readoutInstrument.branch i X) y z =
      ∑ k : e, (V.matrix * X * V.matrix.conjTranspose) (y, (k, i)) (z, (k, i)) := by
  simp only [readoutInstrument, FiniteInstrument.readout_branch_apply,
    ← MatrixMap.ofReferenceIsometry_apply, outputChannel_map, reindexOutput_map]
  rfl

/-- Exact outcome Choi entries of the physical projective readout, in the
repository's input-first Choi convention. -/
theorem readoutInstrument_branch_choi
    (V : ReferenceIsometry a (b × (e × ι))) (i : ι) (s t : a × b) :
    MatrixMap.choi (V.readoutInstrument.branch i) s t =
      ∑ k : e, V.matrix (s.2, (k, i)) s.1 *
        star (V.matrix (t.2, (k, i)) t.1) := by
  change V.readoutInstrument.branch i (Matrix.single s.1 t.1 1) s.2 t.2 = _
  rw [readoutInstrument_branch_apply]
  simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]

end ReferenceIsometry
end
end QIT
