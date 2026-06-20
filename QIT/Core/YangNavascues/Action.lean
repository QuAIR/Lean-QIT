/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.YangNavascues.Coherence

/-!
# Branch-sum action lemmas for the CGS Yang-Navascues local isometry

This module exposes the finite branch-sum expansion layer needed before the
final CGS density calculation.  It does not identify the sum with the residual
garbage tensor target; that calculation remains a downstream theorem.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

namespace QIT
namespace YangNavascues

universe u v w

noncomputable section

/-- Applying the ancilla Fourier is the finite Fourier sum on the ancilla register. -/
theorem ancillaFourierMatrix_mulVec_apply {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    ((ancillaFourierMatrix (H := H) d).mulVec φ) (h, k) =
      ∑ l : Fin d, fourierMatrix d k l * φ (h, l) := by
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single h]
  · simp [ancillaFourierMatrix]
  · intro h' _ hh'
    simp [ancillaFourierMatrix, Ne.symm hh']
  · intro hh
    exact (hh (Finset.mem_univ h)).elim

/-- Applying the inverse ancilla Fourier is the inverse Fourier sum on the ancilla register. -/
theorem ancillaInverseFourierMatrix_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    ((ancillaInverseFourierMatrix (H := H) d).mulVec φ) (h, k) =
      ∑ l : Fin d, inverseFourierMatrix d k l * φ (h, l) := by
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single h]
  · simp [ancillaInverseFourierMatrix]
  · intro h' _ hh'
    simp [ancillaInverseFourierMatrix, Ne.symm hh']
  · intro hh
    exact (hh (Finset.mem_univ h)).elim

/-- Applying the zero-ancilla embedding places the input vector in the zero block. -/
theorem ancillaZeroMatrix_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (zero : Fin d) (φ : H → ℂ) (h : H) (k : Fin d) :
    ((ancillaZeroMatrix (H := H) zero).mulVec φ) (h, k) =
      if k = zero then φ h else 0 := by
  by_cases hk : k = zero
  · subst k
    simp [ancillaZeroMatrix, Matrix.mulVec, dotProduct]
  · simp [ancillaZeroMatrix, Matrix.mulVec, dotProduct, hk]

/-- Applying a block-controlled operator only uses the block matching the ancilla value. -/
theorem controlledOperator_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → CMatrix H)
    (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    (controlledOperator U).mulVec φ (h, k) =
      (U k).mulVec (fun h' => φ (h', k)) h := by
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [controlledOperator]

/-- Applying a controlled unitary specializes the generic controlled-operator action. -/
theorem controlledUnitary_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → Matrix.unitaryGroup H ℂ)
    (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    (controlledUnitary U).mulVec φ (h, k) =
      (U k : CMatrix H).mulVec (fun h' => φ (h', k)) h := by
  simp [controlledUnitary, controlledOperator_mulVec_apply]

/-- Applying a controlled phase uses the phase-operator power selected by the ancilla. -/
theorem controlledPhase_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    (controlledPhase P).mulVec φ (h, k) =
      ((phaseOperator P) ^ (k : ℕ)).mulVec (fun h' => φ (h', k)) h := by
  simp [controlledPhase, controlledOperator_mulVec_apply]

/--
The explicit projection branch selected by the finite Fourier gadget.

For incomplete projection families, the complement contributes only to the
distinguished zero Fourier branch.
-/
def fourierProjectionBranch {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H) (k : Fin d) : CMatrix H :=
  P k + if k = ⟨0, NeZero.pos d⟩ then (1 - ∑ l : Fin d, P l) else 0

private theorem finEquiv_eq_natCast (d : ℕ) [NeZero d] (i : Fin d) :
    ZMod.finEquiv d i = (i : ℕ) := by
  apply ZMod.val_injective d
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
      change (i : ℕ) = ((i : ℕ) : ZMod (n + 1)).val
      rw [ZMod.val_natCast_of_lt i.isLt]

private theorem weightedProjection_mul {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H) (c e : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ i : Fin d, c i • P i) * (∑ j : Fin d, e j • P j) =
      ∑ i : Fin d, (c i * e i) • P i := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hIdem]
  · intro j _ hji
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hOrth i j (fun h => hji h.symm)]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem weightedProjection_left_complement {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (c : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ k : Fin d, c k • P k) * (1 - ∑ k : Fin d, P k) = 0 := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  calc
    (c i • P i) * (1 - ∑ k : Fin d, P k)
        = c i • (P i * (1 - ∑ k : Fin d, P k)) := by rw [Matrix.smul_mul]
    _ = 0 := by
      rw [Matrix.mul_sub]
      have hsum : P i * (∑ k : Fin d, P k) = P i := by
        rw [Matrix.mul_sum]
        rw [Finset.sum_eq_single i]
        · exact hIdem i
        · intro j _ hji
          exact hOrth i j (fun h => hji h.symm)
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      rw [hsum]
      simp

private theorem weightedProjection_right_complement {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (c : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (1 - ∑ k : Fin d, P k) * (∑ k : Fin d, c k • P k) = 0 := by
  classical
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  calc
    (1 - ∑ k : Fin d, P k) * (c i • P i)
        = c i • ((1 - ∑ k : Fin d, P k) * P i) := by rw [Matrix.mul_smul]
    _ = 0 := by
      rw [Matrix.sub_mul]
      have hsum : (∑ k : Fin d, P k) * P i = P i := by
        rw [Finset.sum_mul]
        rw [Finset.sum_eq_single i]
        · exact hIdem i
        · intro j _ hji
          exact hOrth j i hji
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      rw [hsum]
      simp

private theorem projection_complement_idempotent {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (1 - ∑ k : Fin d, P k) * (1 - ∑ k : Fin d, P k) =
      1 - ∑ k : Fin d, P k := by
  have hsum : (∑ k : Fin d, P k) * (∑ k : Fin d, P k) = ∑ k : Fin d, P k := by
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]
    rw [Finset.sum_eq_single i]
    · exact hIdem i
    · intro j _ hji
      exact hOrth j i hji
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  calc
    (1 - ∑ k : Fin d, P k) * (1 - ∑ k : Fin d, P k)
        = 1 - ∑ k : Fin d, P k - ∑ k : Fin d, P k +
            (∑ k : Fin d, P k) * (∑ k : Fin d, P k) := by noncomm_ring
    _ = 1 - ∑ k : Fin d, P k := by rw [hsum]; noncomm_ring

/-- Expansion of a CGS phase operator power on an orthogonal projection family. -/
theorem phaseOperator_pow_eq
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (n : ℕ) :
    phaseOperator P ^ n =
      (∑ m : Fin d, (fourierRoot d) ^ ((m : ℕ) * n) • P m) +
        (1 - ∑ m : Fin d, P m) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih]
      unfold phaseOperator
      have hmul := weightedProjection_mul P
        (fun m : Fin d => (fourierRoot d) ^ ((m : ℕ) * n))
        (fun m : Fin d => (fourierRoot d) ^ (m : ℕ)) hIdem hOrth
      have hlc := weightedProjection_left_complement P
        (fun m : Fin d => (fourierRoot d) ^ ((m : ℕ) * n)) hIdem hOrth
      have hrc := weightedProjection_right_complement P
        (fun m : Fin d => (fourierRoot d) ^ (m : ℕ)) hIdem hOrth
      have hc := projection_complement_idempotent P hIdem hOrth
      calc
        ((∑ m : Fin d, fourierRoot d ^ (↑m * n) • P m) + (1 - ∑ m : Fin d, P m)) *
            ((∑ k : Fin d, fourierRoot d ^ ↑k • P k) + (1 - ∑ k : Fin d, P k))
            = (∑ m : Fin d, fourierRoot d ^ (↑m * n) • P m) *
                (∑ k : Fin d, fourierRoot d ^ ↑k • P k) +
              (∑ m : Fin d, fourierRoot d ^ (↑m * n) • P m) * (1 - ∑ k : Fin d, P k) +
              ((1 - ∑ m : Fin d, P m) * (∑ k : Fin d, fourierRoot d ^ ↑k • P k) +
                (1 - ∑ m : Fin d, P m) * (1 - ∑ k : Fin d, P k)) := by
                noncomm_ring
        _ = ∑ m : Fin d, fourierRoot d ^ (↑m * (n + 1)) • P m +
              (1 - ∑ m : Fin d, P m) := by
          rw [hmul, hlc, hrc, hc]
          simp only [add_zero, zero_add]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro m _
          congr 1
          rw [Nat.mul_succ, pow_add]

theorem fourierMatrix_zero_mul_root_pow
    {d : ℕ} [NeZero d] (l m : Fin d) :
    fourierMatrix d l ⟨0, NeZero.pos d⟩ * (fourierRoot d) ^ ((m : ℕ) * (l : ℕ)) =
      fourierMatrix d l m := by
  simp [fourierMatrix, fourierRoot, ← AddChar.map_nsmul_eq_pow]
  left
  congr 1
  rw [finEquiv_eq_natCast d l, finEquiv_eq_natCast d m]
  ring

theorem inverseFourier_coeff_projection
    {d : ℕ} [NeZero d] (k m : Fin d) :
    (∑ x : Fin d,
      inverseFourierMatrix d k x *
        ((fourierRoot d) ^ ((m : ℕ) * (x : ℕ)) *
          fourierMatrix d x ⟨0, NeZero.pos d⟩)) =
      (1 : CMatrix (Fin d)) k m := by
  calc
    (∑ x : Fin d,
      inverseFourierMatrix d k x *
        ((fourierRoot d) ^ ((m : ℕ) * (x : ℕ)) *
          fourierMatrix d x ⟨0, NeZero.pos d⟩)) =
      ∑ x : Fin d, inverseFourierMatrix d k x * fourierMatrix d x m := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [mul_comm ((fourierRoot d) ^ ((m : ℕ) * (x : ℕ)))
          (fourierMatrix d x ⟨0, NeZero.pos d⟩)]
        rw [fourierMatrix_zero_mul_root_pow]
    _ = (inverseFourierMatrix d * fourierMatrix d) k m := by
        simp [Matrix.mul_apply]
    _ = (1 : CMatrix (Fin d)) k m := by
        rw [inverseFourierMatrix_mul_fourierMatrix]

theorem inverseFourier_coeff_base
    {d : ℕ} [NeZero d] (k : Fin d) :
    (∑ x : Fin d, inverseFourierMatrix d k x * fourierMatrix d x ⟨0, NeZero.pos d⟩) =
      (1 : CMatrix (Fin d)) k ⟨0, NeZero.pos d⟩ := by
  calc
    (∑ x : Fin d, inverseFourierMatrix d k x * fourierMatrix d x ⟨0, NeZero.pos d⟩) =
      (inverseFourierMatrix d * fourierMatrix d) k ⟨0, NeZero.pos d⟩ := by
        simp [Matrix.mul_apply]
    _ = (1 : CMatrix (Fin d)) k ⟨0, NeZero.pos d⟩ := by
        rw [inverseFourierMatrix_mul_fourierMatrix]

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- Alice's explicit side-branch operator after the CGS Fourier gadget collapses. -/
def aliceBranchOperator (B : SchmidtTarget.BaseReindexToFin data.target)
    (k : Fin (Fintype.card ι)) : CMatrix HA :=
  (data.aliceUnitary (B.toEquiv.symm k) : CMatrix HA) *
    data.aliceProjection.effects (B.toEquiv.symm k)

/-- The output basis type of the assembled CGS local isometry. -/
abbrev CGSOutput (ι : Type u) (HA : Type v) (HB : Type w) [Fintype ι] :=
  (HA × Fin (Fintype.card ι)) × (HB × Fin (Fintype.card ι))

/-- The full output vector after applying the assembled CGS local isometry. -/
def cgsActionVector {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    CGSOutput ι HA HB → ℂ :=
  (data.cgsLocalIsometry B W).matrix.mulVec ψ.amp

/--
The `k`th explicit branch of the CGS output vector, selected by the Alice
ancilla register after the assembled local isometry.
-/
def cgsActionBranchVector {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB))
    (k : Fin (Fintype.card ι)) : CGSOutput ι HA HB → ℂ :=
  fun x => if x.1.2 = k then data.cgsActionVector B W ψ x else 0

/-- The rank-one/cross block between two explicit CGS branches. -/
def cgsActionBranchBlock {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB))
    (i j : Fin (Fintype.card ι)) : CMatrix (CGSOutput ι HA HB) :=
  YNData.rankOneCoherence
    (data.cgsActionBranchVector B W ψ i)
    (data.cgsActionBranchVector B W ψ j)

/-- The explicit finite double-sum branch expansion of the CGS output density. -/
def cgsActionBranchSumMatrix {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    CMatrix (CGSOutput ι HA HB) :=
  ∑ i : Fin (Fintype.card ι),
    ∑ j : Fin (Fintype.card ι), data.cgsActionBranchBlock B W ψ i j

private theorem cgsActionVector_eq_sum_branches {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    data.cgsActionVector B W ψ =
      ∑ k : Fin (Fintype.card ι), data.cgsActionBranchVector B W ψ k := by
  classical
  ext x
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single x.1.2]
  · simp [cgsActionBranchVector]
  · intro k _ hk
    simp [cgsActionBranchVector, hk.symm]
  · intro hx
    exact (hx (Finset.mem_univ x.1.2)).elim

private theorem rankOneCoherence_sum_sum {α : Type*} {β : Type*} {γ : Type*}
    [Fintype β] [Fintype γ]
    (f : β → α → ℂ) (g : γ → α → ℂ) :
    YNData.rankOneCoherence (∑ i, f i) (∑ j, g j) =
      ∑ i, ∑ j, YNData.rankOneCoherence (f i) (g j) := by
  classical
  ext x y
  calc
    YNData.rankOneCoherence (∑ i, f i) (∑ j, g j) x y
        = ∑ j, ∑ i, f i x * star (g j y) := by
            simp [YNData.rankOneCoherence_apply, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i, ∑ j, f i x * star (g j y) := by
            rw [Finset.sum_comm]
    _ = (∑ i, ∑ j, YNData.rankOneCoherence (f i) (g j)) x y := by
            simp [Matrix.sum_apply, YNData.rankOneCoherence_apply]

private theorem localIsometry_applyMatrix_rankOne
    {a : Type u} {a' : Type v} {b : Type w} {b' : Type*}
    [Fintype a] [DecidableEq a] [Fintype a'] [DecidableEq a']
    [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b']
    (V : TwoQubit.LocalIsometry a a' b b') (ψ : a × b → ℂ) :
    V.applyMatrix (rankOneMatrix ψ) = rankOneMatrix (V.matrix.mulVec ψ) := by
  ext x y
  simp [TwoQubit.LocalIsometry.applyMatrix, rankOneMatrix, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose, Matrix.vecMulVec_apply,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/--
The assembled CGS local isometry sends a pure input density to the explicit
finite double-sum over its branch blocks.
-/
theorem cgsLocalIsometry_applyMatrix_eq_actionBranchSum {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    (data.cgsLocalIsometry B W).applyMatrix ψ.state.matrix =
      data.cgsActionBranchSumMatrix B W ψ := by
  classical
  rw [PureVector.state_matrix]
  rw [localIsometry_applyMatrix_rankOne]
  unfold cgsActionBranchSumMatrix cgsActionBranchBlock
  rw [← rankOneCoherence_sum_sum
    (fun k : Fin (Fintype.card ι) => data.cgsActionBranchVector B W ψ k)
    (fun k : Fin (Fintype.card ι) => data.cgsActionBranchVector B W ψ k)]
  rw [← data.cgsActionVector_eq_sum_branches B W ψ]
  rfl

end YNData

namespace BobLocalOrthogonalization

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {rho : State (HA × HB)}

variable (W : BobLocalOrthogonalization data rho)

/--
Bob's explicit side-branch operator after the CGS Fourier gadget collapses.

The complement term is present only on the target base branch, because Bob's
source-side projection family is not assumed to be complete.
-/
def bobBranchOperator (B : SchmidtTarget.BaseReindexToFin data.target)
    (k : Fin (Fintype.card ι)) : CMatrix HB :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  (data.bobUnitary (B.toEquiv.symm k) : CMatrix HB) *
    fourierProjectionBranch
      (fun l : Fin (Fintype.card ι) => (W.bobLocal (B.toEquiv.symm l)).matrix) k

@[simp]
theorem bobBranchOperator_base
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    W.bobBranchOperator B data.target.baseIndex =
      (data.bobUnitary data.target.base : CMatrix HB) *
        ((W.bobLocal data.target.base).matrix +
          (1 - ∑ l : Fin (Fintype.card ι), (W.bobLocal (B.toEquiv.symm l)).matrix)) := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hbase_symm : B.toEquiv.symm data.target.baseIndex = data.target.base := by
    apply B.toEquiv.injective
    simp [B.toEquiv_base]
  have hzero :
      data.target.baseIndex =
        (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) := by
    ext
    simp [SchmidtTarget.baseIndex]
  rw [bobBranchOperator, fourierProjectionBranch]
  rw [hbase_symm]
  rw [if_pos hzero]

@[simp]
theorem bobBranchOperator_ne_base
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (k : Fin (Fintype.card ι)) (hk : k ≠ data.target.baseIndex) :
    W.bobBranchOperator B k =
      (data.bobUnitary (B.toEquiv.symm k) : CMatrix HB) *
        (W.bobLocal (B.toEquiv.symm k)).matrix := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hzero :
      (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) =
        data.target.baseIndex := by
    ext
    simp [SchmidtTarget.baseIndex]
  have hkzero :
      k ≠ (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) := by
    intro h
    exact hk (h.trans hzero)
  have hkzero' : k ≠ (0 : Fin (Fintype.card ι)) := by
    simpa using hkzero
  simp [bobBranchOperator, fourierProjectionBranch, hkzero']

end BobLocalOrthogonalization

namespace YNPhaseAlignedConditions

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {ψ : PureVector (HA × HB)}

/--
The phase-aligned YN witness consumes the same branch-sum expansion through its
Bob-local orthogonalization witness.
-/
theorem cgsLocalIsometry_applyMatrix_eq_actionBranchSum
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    (data.cgsLocalIsometry B h.toBobLocalOrthogonalization).applyMatrix ψ.state.matrix =
      data.cgsActionBranchSumMatrix B h.toBobLocalOrthogonalization ψ :=
  data.cgsLocalIsometry_applyMatrix_eq_actionBranchSum B h.toBobLocalOrthogonalization ψ

end YNPhaseAlignedConditions

end

end YangNavascues
end QIT
