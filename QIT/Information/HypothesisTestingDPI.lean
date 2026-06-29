/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.ComparatorTest
public import QIT.Channels.Diamond
public import QIT.States.Purification.Equivalence
public import QIT.States.Purification.Canonical

/-!
# Hypothesis-testing data processing

This module proves the finite-dimensional effect-pullback route for
hypothesis-testing relative entropy and optimized hypothesis-testing mutual
information data processing.  The route is the one used in the one-shot
entanglement-assisted classical communication meta-converse
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:327-394].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

set_option linter.unusedSectionVars false

noncomputable section

private theorem posSemidef_one_sub_of_posSemidef_idempotent_forHypothesisTestingDPI
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : CMatrix ι)
    (hPpos : P.PosSemidef) (hPid : P * P = P) :
    (1 - P).PosSemidef := by
  let Q : CMatrix ι := 1 - P
  have hPherm : P.IsHermitian := hPpos.isHermitian
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    exact Matrix.IsHermitian.sub (by simp [Matrix.IsHermitian]) hPherm
  have hQid : Q * Q = Q := by
    dsimp [Q]
    calc
      (1 - P) * (1 - P) = (1 - P) * 1 - (1 - P) * P := by
        rw [Matrix.mul_sub]
      _ = (1 - P) - (1 * P - P * P) := by
        rw [Matrix.mul_one, Matrix.sub_mul]
      _ = 1 - P := by
        rw [Matrix.one_mul, hPid]
        abel
  have hPSD : (Matrix.conjTranspose Q * Q).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self Q
  convert hPSD using 1
  rw [hQherm.eq, hQid]

namespace MatrixMap

variable {a : Type u} {b : Type v} {κ : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype κ]

theorem krausAdjoint_posSemidef
    (K : κ → Matrix b a ℂ) {E : CMatrix b} (hE : E.PosSemidef) :
    (krausAdjoint K E).PosSemidef := by
  unfold krausAdjoint
  exact Matrix.posSemidef_sum Finset.univ fun k _ => by
    simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using hE.mul_mul_conjTranspose_same (Matrix.conjTranspose (K k))

theorem krausAdjoint_sub
    (K : κ → Matrix b a ℂ) (E F : CMatrix b) :
    krausAdjoint K (E - F) = krausAdjoint K E - krausAdjoint K F := by
  ext i j
  simp [krausAdjoint, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply,
    Finset.sum_sub_distrib]

theorem krausAdjoint_mono
    (K : κ → Matrix b a ℂ) {E F : CMatrix b} (hEF : E ≤ F) :
    krausAdjoint K E ≤ krausAdjoint K F := by
  rw [Matrix.le_iff] at hEF ⊢
  have hpsd := krausAdjoint_posSemidef K hEF
  simpa [krausAdjoint_sub] using hpsd

theorem krausAdjoint_one_le_of_traceNonincreasing
    (K : κ → Matrix b a ℂ)
    (hTNI : IsTraceNonincreasing (ofKraus K)) :
    krausAdjoint K (1 : CMatrix b) ≤ 1 := by
  rw [Matrix.le_iff]
  refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg ?_).2 ?_
  · exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      (krausAdjoint_posSemidef K Matrix.PosSemidef.one).isHermitian
  · intro A hA
    have hle := hTNI A hA
    have hdual :
        (((ofKraus K) A) * (1 : CMatrix b)).trace =
          (A * krausAdjoint K (1 : CMatrix b)).trace :=
      ofKraus_trace_duality K A (1 : CMatrix b)
    rw [Matrix.mul_one] at hdual
    have htrace :
        ((A * ((1 : CMatrix a) - krausAdjoint K (1 : CMatrix b))).trace).re =
          A.trace.re - ((A * krausAdjoint K (1 : CMatrix b)).trace).re := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm]
    rw [htrace]
    rw [← hdual]
    exact sub_nonneg.mpr hle

variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- A map on the target/right factor commutes with an isometry acting on the
left/reference factor. -/
theorem kron_idChannel_left_apply_applyMatrix
    (Φ : MatrixMap a b) (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix (Prod r₁ a)) :
    MatrixMap.kron (Channel.idChannel r₂).map Φ (V.applyMatrix X) =
      V.applyMatrix (MatrixMap.kron (Channel.idChannel r₁).map Φ X) := by
  ext rb rb'
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' => V.applyMatrix X (rb.1, j) (rb'.1, j')) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
            (fun j j' => X (x, j) (y, j')) := by
    ext j j'
    simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
      Matrix.mul_apply, Finset.sum_mul, mul_assoc, mul_comm]
  rw [hslice]
  have hmap :
      Φ (∑ y : r₁, ∑ x : r₁,
          (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
            (fun j j' => X (x, j) (y, j'))) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
            Φ (fun j j' => X (x, j) (y, j')) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact LinearMap.map_smul Φ (V.matrix rb.1 x * star (V.matrix rb'.1 y))
      (fun j j' => X (x, j) (y, j'))
  have hmapEntry := congrFun (congrFun hmap rb.2) rb'.2
  calc
    Φ (∑ y : r₁, ∑ x : r₁,
        (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
          (fun j j' => X (x, j) (y, j'))) rb.2 rb'.2
        = (∑ y : r₁, ∑ x : r₁,
            (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
              Φ (fun j j' => X (x, j) (y, j'))) rb.2 rb'.2 := hmapEntry
    _ = V.applyMatrix (MatrixMap.kron (Channel.idChannel r₁).map Φ X) rb rb' := by
      simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
        Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        MatrixMap.kron_idChannel_left_apply_slice, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

/-- The matrix map induced by a reference isometry agrees with
`ReferenceIsometry.applyMatrix` on the left/reference factor. -/
theorem kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrix
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod r₁ a)) :
    MatrixMap.kron (MatrixMap.ofReferenceIsometry V) (Channel.idChannel a).map X =
      V.applyMatrix X := by
  ext ra ra'
  rw [MatrixMap.kron_idChannel_apply_slice]
  change MatrixMap.ofReferenceIsometry V
      (ReferenceIsometry.targetBlock X ra.2 ra'.2) ra.1 ra'.1 =
    (V.matrix * ReferenceIsometry.targetBlock X ra.2 ra'.2 *
      Matrix.conjTranspose V.matrix) ra.1 ra'.1
  rw [MatrixMap.ofReferenceIsometry_apply]

private theorem kron_comp_apply_general
    {α β γ δ η θ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    [Fintype η] [DecidableEq η] [Fintype θ] [DecidableEq θ]
    (Φ₁ : MatrixMap α β) (Ψ₁ : MatrixMap γ δ)
    (Φ₂ : MatrixMap η α) (Ψ₂ : MatrixMap θ γ) (X : CMatrix (Prod η θ)) :
    kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) X) =
      kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) X := by
  ext bd bd'
  rw [map_eq_sum_single (kron Φ₂ Ψ₂) X]
  simp_rw [map_sum]
  simp_rw [map_smul]
  simp only [Matrix.sum_apply]
  rw [map_eq_sum_single (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂)) X]
  simp only [Matrix.sum_apply]
  change
    (∑ ef : Prod η θ, ∑ ef' : Prod η θ,
      (X ef ef' • (kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) (Matrix.single ef ef' 1)))) bd bd') =
    (∑ ef : Prod η θ, ∑ ef' : Prod η θ,
      (X ef ef' • (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) (Matrix.single ef ef' 1))) bd bd')
  refine Finset.sum_congr rfl fun ef _ => ?_
  refine Finset.sum_congr rfl fun ef' _ => ?_
  simp only [Matrix.smul_apply]
  congr 1
  cases ef with
  | mk e0 f0 =>
  cases ef' with
  | mk e1 f1 =>
  rw [single_prod_eq_kronecker_single]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rfl

end MatrixMap

namespace ReferenceIsometry

variable {a : Type u}
variable [Fintype a] [DecidableEq a]
variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

theorem applyMatrix_sub (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod r₁ a)) :
    V.applyMatrix (X - Y) = V.applyMatrix X - V.applyMatrix Y := by
  rw [← MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrix V (X - Y)]
  rw [map_sub]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrix V X]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrix V Y]

theorem applyMatrix_posSemidef (V : ReferenceIsometry r₁ r₂)
    {X : CMatrix (Prod r₁ a)} (hX : X.PosSemidef) :
    (V.applyMatrix X).PosSemidef := by
  have hCP :
      MatrixMap.IsCompletelyPositive
        (MatrixMap.kron (MatrixMap.ofReferenceIsometry V)
          (Channel.idChannel a).map) := by
    exact MatrixMap.isCompletelyPositive_kron
      (MatrixMap.ofReferenceIsometry V) (Channel.idChannel a).map
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
      (Channel.idChannel a).completelyPositive
  have hpos :=
    MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.kron (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).map) hCP X hX
  simpa [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrix V X]
    using hpos

theorem matrix_mul_conjTranspose_mul_matrix (V : ReferenceIsometry r₁ r₂)
    (B C : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
  calc
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * B * (Matrix.conjTranspose V.matrix * V.matrix) *
        C * Matrix.conjTranspose V.matrix := by
        simp only [Matrix.mul_assoc]
    _ = V.matrix * B * (1 : CMatrix r₁) * C * Matrix.conjTranspose V.matrix := by
        rw [V.isometry]
    _ = V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem targetBlock_mul (X Y : CMatrix (Prod r₁ a)) (i j : a) :
    targetBlock (X * Y) i j =
      ∑ k : a, targetBlock X i k * targetBlock Y k j := by
  ext x y
  change (X * Y) (x, i) (y, j) =
    (∑ k : a, targetBlock X i k * targetBlock Y k j) x y
  rw [Matrix.mul_apply, ← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_comm]
  rw [Matrix.sum_apply]
  simp [targetBlock, Matrix.mul_apply]

theorem applyMatrix_mul (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod r₁ a)) :
    V.applyMatrix X * V.applyMatrix Y = V.applyMatrix (X * Y) := by
  ext p q
  calc
    (V.applyMatrix X * V.applyMatrix Y) p q =
        (∑ k : a,
          ((V.matrix * targetBlock X p.2 k * Matrix.conjTranspose V.matrix) *
            (V.matrix * targetBlock Y k q.2 * Matrix.conjTranspose V.matrix)) p.1 q.1) := by
      change (∑ j : Prod r₂ a, V.applyMatrix X p j * V.applyMatrix Y j q) =
        (∑ k : a,
          ((V.matrix * targetBlock X p.2 k * Matrix.conjTranspose V.matrix) *
            (V.matrix * targetBlock Y k q.2 * Matrix.conjTranspose V.matrix)) p.1 q.1)
      rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
      simp [applyMatrix, Matrix.mul_apply]
    _ =
        (∑ k : a,
          (V.matrix * (targetBlock X p.2 k * targetBlock Y k q.2) *
            Matrix.conjTranspose V.matrix) p.1 q.1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [V.matrix_mul_conjTranspose_mul_matrix]
    _ = (V.matrix *
          (∑ k : a, targetBlock X p.2 k * targetBlock Y k q.2) *
            Matrix.conjTranspose V.matrix) p.1 q.1 := by
      have hsum :
          V.matrix *
              (∑ k : a, targetBlock X p.2 k * targetBlock Y k q.2) *
              Matrix.conjTranspose V.matrix =
            ∑ k : a,
              V.matrix * (targetBlock X p.2 k * targetBlock Y k q.2) *
                Matrix.conjTranspose V.matrix := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
      have hentry := congrFun (congrFun hsum p.1) q.1
      simpa [Matrix.sum_apply] using hentry.symm
    _ = V.applyMatrix (X * Y) p q := by
      rw [← targetBlock_mul X Y p.2 q.2]
      rfl

theorem applyMatrix_one_idempotent (V : ReferenceIsometry r₁ r₂) :
    V.applyMatrix (1 : CMatrix (Prod r₁ a)) *
      V.applyMatrix (1 : CMatrix (Prod r₁ a)) =
        V.applyMatrix (1 : CMatrix (Prod r₁ a)) := by
  rw [V.applyMatrix_mul, Matrix.mul_one]

theorem one_sub_applyMatrix_one_posSemidef (V : ReferenceIsometry r₁ r₂) :
    (1 - V.applyMatrix (1 : CMatrix (Prod r₁ a))).PosSemidef := by
  exact posSemidef_one_sub_of_posSemidef_idempotent_forHypothesisTestingDPI
    (V.applyMatrix (1 : CMatrix (Prod r₁ a)))
    (V.applyMatrix_posSemidef Matrix.PosSemidef.one)
    (V.applyMatrix_one_idempotent (a := a))

theorem applyMatrix_le_one_of_le_one (V : ReferenceIsometry r₁ r₂)
    {E : CMatrix (Prod r₁ a)} (hE : E ≤ 1) :
    V.applyMatrix E ≤ 1 := by
  rw [Matrix.le_iff]
  have hEsub : (1 - E).PosSemidef := by
    simpa [Matrix.le_iff] using hE
  have himageSub :
      (V.applyMatrix ((1 : CMatrix (Prod r₁ a)) - E)).PosSemidef :=
    V.applyMatrix_posSemidef hEsub
  have hdecomp :
      (1 : CMatrix (Prod r₂ a)) - V.applyMatrix E =
        (1 - V.applyMatrix (1 : CMatrix (Prod r₁ a))) +
          V.applyMatrix ((1 : CMatrix (Prod r₁ a)) - E) := by
    rw [V.applyMatrix_sub]
    abel
  rw [hdecomp]
  exact Matrix.PosSemidef.add
    (V.one_sub_applyMatrix_one_posSemidef (a := a)) himageSub

theorem trace_applyMatrix (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix (Prod r₁ a)) :
    (V.applyMatrix X).trace = X.trace := by
  have h := congrArg Matrix.trace (V.partialTraceA_applyMatrix X)
  simpa [partialTraceA_trace] using h

theorem trace_applyMatrix_mul_applyMatrix (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod r₁ a)) :
    ((V.applyMatrix X * V.applyMatrix Y).trace) = (X * Y).trace := by
  rw [V.applyMatrix_mul, V.trace_applyMatrix]

end ReferenceIsometry

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A chosen finite Kraus representation of a channel. -/
def kraus (Φ : Channel a b) : (Prod a b) → Matrix b a ℂ :=
  Classical.choose (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)

theorem map_eq_ofKraus (Φ : Channel a b) :
    Φ.map = MatrixMap.ofKraus (Φ.kraus) :=
  Classical.choose_spec (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)

/-- Heisenberg-picture pullback of an output effect along a channel. -/
def dualEffect (Φ : Channel a b) (E : CMatrix b) : CMatrix a :=
  MatrixMap.krausAdjoint Φ.kraus E

theorem applyState_dualEffect_trace
    (Φ : Channel a b) (ρ : State a) (E : CMatrix b) :
    (((Φ.applyState ρ).matrix * E).trace) =
      (ρ.matrix * Φ.dualEffect E).trace := by
  unfold dualEffect
  change ((Φ.map ρ.matrix) * E).trace =
    (ρ.matrix * MatrixMap.krausAdjoint Φ.kraus E).trace
  rw [Φ.map_eq_ofKraus]
  exact MatrixMap.ofKraus_trace_duality Φ.kraus ρ.matrix E

theorem effectAcceptProbability_applyState_dualEffect
    (Φ : Channel a b) (ρ : State a) (E : CMatrix b) :
    effectAcceptProbability (Φ.applyState ρ) E =
      effectAcceptProbability ρ (Φ.dualEffect E) := by
  unfold effectAcceptProbability
  rw [Φ.applyState_dualEffect_trace ρ E]

theorem dualEffect_posSemidef
    (Φ : Channel a b) {E : CMatrix b} (hE : E.PosSemidef) :
    (Φ.dualEffect E).PosSemidef := by
  exact MatrixMap.krausAdjoint_posSemidef Φ.kraus hE

theorem dualEffect_one_le (Φ : Channel a b) :
    Φ.dualEffect (1 : CMatrix b) ≤ 1 := by
  unfold dualEffect
  refine MatrixMap.krausAdjoint_one_le_of_traceNonincreasing Φ.kraus ?_
  intro X hX
  have hTNI :=
    (MatrixMap.traceNonincreasingCP_of_tracePreserving Φ.completelyPositive
      Φ.tracePreserving).traceNonincreasing X hX
  simpa [Φ.map_eq_ofKraus] using hTNI

theorem dualEffect_le_one_of_le_one
    (Φ : Channel a b) {E : CMatrix b} (hE : E ≤ 1) :
    Φ.dualEffect E ≤ 1 := by
  exact le_trans (MatrixMap.krausAdjoint_mono Φ.kraus hE) Φ.dualEffect_one_le

/-- Pull back a feasible output hypothesis-testing effect along a channel. -/
def pullbackHypothesisTestingEffect
    (Φ : Channel a b) (ρ : State a) (ε : ℝ)
    (Λ : HypothesisTestingEffect (Φ.applyState ρ) ε) :
    HypothesisTestingEffect ρ ε where
  effect := Φ.dualEffect Λ.effect
  pos := Φ.dualEffect_posSemidef Λ.pos
  le_one := Φ.dualEffect_le_one_of_le_one Λ.le_one
  accept_ge := by
    rw [← Φ.effectAcceptProbability_applyState_dualEffect ρ Λ.effect]
    exact Λ.accept_ge

@[simp]
theorem pullbackHypothesisTestingEffect_typeIIError
    (Φ : Channel a b) (ρ σ : State a) (ε : ℝ)
    (Λ : HypothesisTestingEffect (Φ.applyState ρ) ε) :
    (Φ.pullbackHypothesisTestingEffect ρ ε Λ).typeIIError σ =
      Λ.typeIIError (Φ.applyState σ) := by
  unfold pullbackHypothesisTestingEffect HypothesisTestingEffect.typeIIError
    effectTypeIIError
  rw [← Φ.effectAcceptProbability_applyState_dualEffect σ Λ.effect]

end Channel

namespace PureVector

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

/-- A pure vector purifies its target/right marginal in the local
reference-first convention.  This narrowly named copy avoids coupling the
hypothesis-testing DPI layer to the Uhlmann module. -/
theorem purifies_marginalB_forHypothesisTestingDPI (ψ : PureVector (Prod r a)) :
    ψ.Purifies ψ.state.marginalB := by
  rw [purifies_iff]
  rfl

end PureVector

namespace Channel

variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- The channel induced by a finite reference isometry. -/
def ofReferenceIsometry (V : ReferenceIsometry r₁ r₂) : Channel r₁ r₂ where
  map := MatrixMap.ofReferenceIsometry V
  completelyPositive := MatrixMap.ofReferenceIsometry_isCompletelyPositive V
  tracePreserving := MatrixMap.ofReferenceIsometry_isTracePreserving V
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)

@[simp]
theorem ofReferenceIsometry_map (V : ReferenceIsometry r₁ r₂) :
    (Channel.ofReferenceIsometry V).map = MatrixMap.ofReferenceIsometry V :=
  rfl

variable {a : Type u} [Fintype a] [DecidableEq a]

theorem ofReferenceIsometry_prod_id_applyState_matrix
    (V : ReferenceIsometry r₁ r₂) (ρ : State (Prod r₁ a)) :
    (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ).matrix =
      V.applyMatrix ρ.matrix := by
  change MatrixMap.kron (Channel.ofReferenceIsometry V).map
      (Channel.idChannel a).map ρ.matrix = V.applyMatrix ρ.matrix
  rw [Channel.ofReferenceIsometry_map]
  exact MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrix V ρ.matrix

/-- Trace out the first factor of a bipartite register, as a channel.  This is
the local discard map used in the hypothesis-testing converse bridge. -/
def traceOutAForHypothesisTestingDPI
    (r a : Type*) [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] :
    Channel (Prod r a) a where
  map := MatrixMap.partialTraceA r a
  completelyPositive :=
    (MatrixMap.partialTraceA_traceNonincreasingCP (a := r) (b := a)).completelyPositive
  tracePreserving := by
    intro X
    change (QIT.partialTraceA (a := r) (b := a) X).trace = X.trace
    exact QIT.partialTraceA_trace X
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.partialTraceA r a)
      (MatrixMap.partialTraceA_traceNonincreasingCP (a := r) (b := a)).completelyPositive

@[simp]
theorem traceOutAForHypothesisTestingDPI_map
    (r a : Type*) [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    (X : CMatrix (Prod r a)) :
    (traceOutAForHypothesisTestingDPI r a).map X =
      QIT.partialTraceA (a := r) (b := a) X :=
  rfl

theorem traceOutAForHypothesisTestingDPI_applyState
    (r a : Type*) [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    (ρ : State (Prod r a)) :
    (traceOutAForHypothesisTestingDPI r a).applyState ρ = ρ.marginalB := by
  apply State.ext
  rfl

/-- Tracing out a left reference factor commutes with applying a channel on the
right tensor factor. -/
theorem traceOutAForHypothesisTestingDPI_prod_id_applyState_id_prod
    {p : Type u} {r : Type v} {a : Type w} {b : Type x}
    [Fintype p] [DecidableEq p] [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : Channel a b) (ρ : State (Prod (Prod p r) a)) :
    ((traceOutAForHypothesisTestingDPI p r).prod (Channel.idChannel b)).applyState
        (((Channel.idChannel (Prod p r)).prod N).applyState ρ) =
      ((Channel.idChannel r).prod N).applyState
        (((traceOutAForHypothesisTestingDPI p r).prod (Channel.idChannel a)).applyState ρ) := by
  apply State.ext
  change
    MatrixMap.kron (traceOutAForHypothesisTestingDPI p r).map
        (Channel.idChannel b).map
        (MatrixMap.kron (Channel.idChannel (Prod p r)).map N.map ρ.matrix) =
      MatrixMap.kron (Channel.idChannel r).map N.map
        (MatrixMap.kron (traceOutAForHypothesisTestingDPI p r).map
          (Channel.idChannel a).map ρ.matrix)
  have hleft₁ :
      (traceOutAForHypothesisTestingDPI p r).map.comp
          (Channel.idChannel (Prod p r)).map =
        (traceOutAForHypothesisTestingDPI p r).map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hleft₂ :
      (Channel.idChannel b).map.comp N.map = N.map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hright₁ :
      (Channel.idChannel r).map.comp (traceOutAForHypothesisTestingDPI p r).map =
        (traceOutAForHypothesisTestingDPI p r).map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hright₂ :
      N.map.comp (Channel.idChannel a).map = N.map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  calc
    MatrixMap.kron (traceOutAForHypothesisTestingDPI p r).map
        (Channel.idChannel b).map
        (MatrixMap.kron (Channel.idChannel (Prod p r)).map N.map ρ.matrix) =
      MatrixMap.kron
        ((traceOutAForHypothesisTestingDPI p r).map.comp
          (Channel.idChannel (Prod p r)).map)
        ((Channel.idChannel b).map.comp N.map) ρ.matrix := by
        exact MatrixMap.kron_comp_apply_general
          (traceOutAForHypothesisTestingDPI p r).map (Channel.idChannel b).map
          (Channel.idChannel (Prod p r)).map N.map ρ.matrix
    _ = MatrixMap.kron (traceOutAForHypothesisTestingDPI p r).map N.map ρ.matrix := by
        rw [hleft₁, hleft₂]
    _ = MatrixMap.kron
        ((Channel.idChannel r).map.comp (traceOutAForHypothesisTestingDPI p r).map)
        (N.map.comp (Channel.idChannel a).map) ρ.matrix := by
        rw [hright₁, hright₂]
    _ = MatrixMap.kron (Channel.idChannel r).map N.map
        (MatrixMap.kron (traceOutAForHypothesisTestingDPI p r).map
          (Channel.idChannel a).map ρ.matrix) := by
        exact (MatrixMap.kron_comp_apply_general
          (Channel.idChannel r).map N.map
          (traceOutAForHypothesisTestingDPI p r).map (Channel.idChannel a).map
          ρ.matrix).symm

end Channel

namespace ReferenceIsometry

variable {a : Type u}
variable [Fintype a] [DecidableEq a]
variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- Push a feasible hypothesis-testing effect forward along a reference
isometry.  This is the effect-side reverse of channel pullback, valid because
an isometry embeds the whole tested subspace and preserves the trace pairing on
the image. -/
def pushForwardHypothesisTestingEffect
    (V : ReferenceIsometry r₁ r₂) (ρ : State (Prod r₁ a)) (ε : ℝ)
    (Λ : HypothesisTestingEffect ρ ε) :
    HypothesisTestingEffect
      (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ) ε where
  effect := V.applyMatrix Λ.effect
  pos := V.applyMatrix_posSemidef Λ.pos
  le_one := V.applyMatrix_le_one_of_le_one Λ.le_one
  accept_ge := by
    simpa [effectAcceptProbability, Channel.ofReferenceIsometry_prod_id_applyState_matrix,
      V.trace_applyMatrix_mul_applyMatrix] using Λ.accept_ge

@[simp]
theorem pushForwardHypothesisTestingEffect_typeIIError
    (V : ReferenceIsometry r₁ r₂) (ρ σ : State (Prod r₁ a)) (ε : ℝ)
    (Λ : HypothesisTestingEffect ρ ε) :
    (V.pushForwardHypothesisTestingEffect ρ ε Λ).typeIIError
      (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ) =
      Λ.typeIIError σ := by
  simp [pushForwardHypothesisTestingEffect, HypothesisTestingEffect.typeIIError,
    effectTypeIIError, effectAcceptProbability,
    Channel.ofReferenceIsometry_prod_id_applyState_matrix,
    V.trace_applyMatrix_mul_applyMatrix]

/-- Embed a reference register as the right summand of an enlarged reference
system.  This local copy keeps the hypothesis-testing DPI layer independent of
the Uhlmann theorem module. -/
def sumInrForHypothesisTestingDPI
    (extra : Type*) [Fintype extra] [DecidableEq extra]
    (r : Type*) [Fintype r] [DecidableEq r] :
    ReferenceIsometry r (Sum extra r) where
  matrix := fun x i =>
    match x with
    | Sum.inl _ => 0
    | Sum.inr j => if j = i then 1 else 0
  isometry := by
    classical
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, eq_comm]

end ReferenceIsometry

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

private theorem trace_reindex_mul_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (X Y : CMatrix α) :
    ((X.submatrix e.symm e.symm * Y.submatrix e.symm e.symm).trace) =
      (X * Y).trace := by
  rw [Matrix.trace, Matrix.trace]
  change (∑ i : β, ∑ j : β,
      X (e.symm i) (e.symm j) * Y (e.symm j) (e.symm i)) =
    ∑ i : α, ∑ j : α, X i j * Y j i
  trans ∑ i : α, ∑ j : β, X i (e.symm j) * Y (e.symm j) i
  · exact Fintype.sum_equiv e.symm
      (fun i : β => ∑ j : β,
        X (e.symm i) (e.symm j) * Y (e.symm j) (e.symm i))
      (fun i : α => ∑ j : β, X i (e.symm j) * Y (e.symm j) i)
      (by intro i; rfl)
  · refine Finset.sum_congr rfl ?_
    intro i _
    exact Fintype.sum_equiv e.symm
      (fun j : β => X i (e.symm j) * Y (e.symm j) i)
      (fun j : α => X i j * Y j i)
      (by intro j; rfl)

private theorem submatrix_one_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) :
    (1 : CMatrix α).submatrix e.symm e.symm = (1 : CMatrix β) := by
  ext i j
  simp [Matrix.one_apply]

private theorem submatrix_sub_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (X Y : CMatrix α) :
    (X - Y).submatrix e.symm e.symm =
      X.submatrix e.symm e.symm - Y.submatrix e.symm e.symm := by
  ext i j
  rfl

namespace HypothesisTestingEffect

variable {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
variable [Fintype β] [DecidableEq β]
variable {ρ σ : State α} {ε : ℝ}

/-- Relabel a feasible hypothesis-testing effect along a finite basis
equivalence. -/
def reindex (Λ : HypothesisTestingEffect ρ ε) (e : α ≃ β) :
    HypothesisTestingEffect (ρ.reindex e) ε where
  effect := Λ.effect.submatrix e.symm e.symm
  pos := Λ.pos.submatrix e.symm
  le_one := by
    have hle_one := Λ.le_one
    rw [Matrix.le_iff] at hle_one ⊢
    simpa [submatrix_sub_equiv e (1 : CMatrix α) Λ.effect,
      submatrix_one_equiv e] using hle_one.submatrix e.symm
  accept_ge := by
    change 1 - ε ≤
      (((ρ.matrix.submatrix e.symm e.symm) *
        (Λ.effect.submatrix e.symm e.symm)).trace).re
    rw [trace_reindex_mul_reindex e ρ.matrix Λ.effect]
    exact Λ.accept_ge

@[simp]
theorem reindex_typeIIError (Λ : HypothesisTestingEffect ρ ε)
    (e : α ≃ β) :
    (Λ.reindex e).typeIIError (σ.reindex e) = Λ.typeIIError σ := by
  unfold HypothesisTestingEffect.typeIIError effectTypeIIError effectAcceptProbability
  change (((σ.matrix.submatrix e.symm e.symm) *
      (Λ.effect.submatrix e.symm e.symm)).trace).re =
    ((σ.matrix * Λ.effect).trace).re
  rw [trace_reindex_mul_reindex e σ.matrix Λ.effect]

end HypothesisTestingEffect

namespace State

private theorem reindex_symm_reindex_forHypothesisTestingDPI
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ : State α) (e : α ≃ β) :
    (ρ.reindex e).reindex e.symm = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

theorem hypothesisTestingBeta_nonneg_of_epsilon_nonneg
    (ρ σ : State a) (ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ ρ.hypothesisTestingBeta σ ε := by
  rw [hypothesisTestingBeta_eq_sInf]
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  exact Λ.typeIIError_nonneg

theorem hypothesisTestingBeta_reindex_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≤
      ρ.hypothesisTestingBeta σ ε := by
  change (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≤
    sInf (ρ.hypothesisTestingBetaCandidateSet σ ε)
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    State.hypothesisTestingBeta_le_of_effect
      (ρ.reindex e) (σ.reindex e) ε (Λ.reindex e)
  rw [HypothesisTestingEffect.reindex_typeIIError Λ e] at hle
  exact hle

theorem hypothesisTestingBeta_le_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    ρ.hypothesisTestingBeta σ ε ≤
      (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε := by
  have h :=
    hypothesisTestingBeta_reindex_le (ρ.reindex e) (σ.reindex e) ε hε e.symm
  simpa [reindex_symm_reindex_forHypothesisTestingDPI] using h

theorem hypothesisTestingBeta_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε =
      ρ.hypothesisTestingBeta σ ε :=
  le_antisymm (hypothesisTestingBeta_reindex_le ρ σ ε hε e)
    (hypothesisTestingBeta_le_reindex ρ σ ε hε e)

theorem hypothesisTestingRelativeEntropy_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingRelativeEntropy (σ.reindex e) ε =
      ρ.hypothesisTestingRelativeEntropy σ ε := by
  rw [hypothesisTestingRelativeEntropy_eq, hypothesisTestingRelativeEntropy_eq,
    hypothesisTestingBeta_reindex ρ σ ε hε e]

theorem hypothesisTestingRelativeEntropyE_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingRelativeEntropyE (σ.reindex e) ε =
      ρ.hypothesisTestingRelativeEntropyE σ ε := by
  have hβ := hypothesisTestingBeta_reindex ρ σ ε hε e
  by_cases hzero : ρ.hypothesisTestingBeta σ ε = 0
  · have hzero' :
        (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε = 0 := by
      simpa [hβ] using hzero
    simp [hypothesisTestingRelativeEntropyE, hzero, hzero']
  · have hzero' :
        (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≠ 0 := by
      simpa [hβ] using hzero
    simp [hypothesisTestingRelativeEntropyE, hzero, hzero',
      hypothesisTestingRelativeEntropy_reindex ρ σ ε hε e]

private theorem prod_reindex_prodCongr_forHypothesisTestingDPI
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : State α) (σ : State γ) (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.prod σ).reindex (Equiv.prodCongr e f) =
      (ρ.reindex e).prod (σ.reindex f) := by
  apply State.ext
  ext i j
  simp [State.reindex, State.prod, Matrix.kronecker]

theorem hypothesisTestingMutualInformationE_reindex_prodCongr_le
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : State (Prod α γ)) (ε : ℝ) (hε : 0 ≤ ε)
    (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).hypothesisTestingMutualInformationE ε ≤
      ρ.hypothesisTestingMutualInformationE ε := by
  let ρ' : State (Prod β δ) := ρ.reindex (Equiv.prodCongr e f)
  rw [hypothesisTestingMutualInformationE_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropyE
          (ρ'.marginalA.prod (σB.reindex f)) ε ∈
        hypothesisTestingMutualInformationECandidateSet (a := β) (b := δ) ρ' ε := by
    exact ⟨σB.reindex f, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformationE ε ≤
        ρ'.hypothesisTestingRelativeEntropyE
          (ρ'.marginalA.prod (σB.reindex f)) ε := by
    rw [hypothesisTestingMutualInformationE_eq_sInf]
    exact sInf_le houtMem
  have hmarg : ρ'.marginalA = ρ.marginalA.reindex e := by
    simpa [ρ'] using State.marginalA_reindex_prodCongr ρ e f
  have hprod :
      ρ'.marginalA.prod (σB.reindex f) =
        (ρ.marginalA.prod σB).reindex (Equiv.prodCongr e f) := by
    rw [hmarg]
    exact (prod_reindex_prodCongr_forHypothesisTestingDPI
      ρ.marginalA σB e f).symm
  have hD :
      ρ'.hypothesisTestingRelativeEntropyE
          ((ρ.marginalA.prod σB).reindex (Equiv.prodCongr e f)) ε =
        ρ.hypothesisTestingRelativeEntropyE (ρ.marginalA.prod σB) ε := by
    simpa [ρ'] using
      hypothesisTestingRelativeEntropyE_reindex ρ (ρ.marginalA.prod σB) ε hε
        (Equiv.prodCongr e f)
  exact houtLe.trans (by simpa [hprod] using le_of_eq hD)

theorem hypothesisTestingMutualInformationE_reindex_prodCongr
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : State (Prod α γ)) (ε : ℝ) (hε : 0 ≤ ε)
    (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).hypothesisTestingMutualInformationE ε =
      ρ.hypothesisTestingMutualInformationE ε := by
  let ρ' : State (Prod β δ) := ρ.reindex (Equiv.prodCongr e f)
  have hforward :
      ρ'.hypothesisTestingMutualInformationE ε ≤
        ρ.hypothesisTestingMutualInformationE ε := by
    simpa [ρ'] using hypothesisTestingMutualInformationE_reindex_prodCongr_le
      ρ ε hε e f
  have hback :
      ρ.hypothesisTestingMutualInformationE ε ≤
        ρ'.hypothesisTestingMutualInformationE ε := by
    have h :=
      hypothesisTestingMutualInformationE_reindex_prodCongr_le
        ρ' ε hε e.symm f.symm
    have hreindex : ρ'.reindex (Equiv.prodCongr e.symm f.symm) = ρ := by
      apply State.ext
      ext i j
      rcases i with ⟨iα, iγ⟩
      rcases j with ⟨jα, jγ⟩
      simp [ρ', State.reindex]
    simpa [hreindex] using h
  exact le_antisymm hforward hback

/-- Canonical purification of a mixed input-reference state, re-associated so
that the original reference remains part of the reference register and the
channel input is the target register. -/
def purifiedInputForHypothesisTestingDPI
    {r : Type u} {a : Type v} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] (ρ : State (Prod r a)) :
    PureVector (Prod (Prod (Prod r a) r) a) :=
  ρ.canonicalPurification.reindex (Equiv.prodAssoc (Prod r a) r a).symm

theorem traceOut_purifiedInputForHypothesisTestingDPI
    {r : Type u} {a : Type v} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] (ρ : State (Prod r a)) :
    ((Channel.traceOutAForHypothesisTestingDPI (Prod r a) r).prod
        (Channel.idChannel a)).applyState
        (ρ.purifiedInputForHypothesisTestingDPI.state) = ρ := by
  apply State.ext
  ext x y
  rcases x with ⟨xr, xa⟩
  rcases y with ⟨yr, ya⟩
  change
    (MatrixMap.kron
        (Channel.traceOutAForHypothesisTestingDPI (Prod r a) r).map
        (Channel.idChannel a).map
        ρ.purifiedInputForHypothesisTestingDPI.state.matrix) (xr, xa) (yr, ya) =
      ρ.matrix (xr, xa) (yr, ya)
  rw [MatrixMap.kron_idChannel_apply_slice]
  change
    (QIT.partialTraceA (a := Prod r a) (b := r)
      (fun i j =>
        ρ.purifiedInputForHypothesisTestingDPI.state.matrix (i, xa) (j, ya)))
        xr yr =
      ρ.matrix (xr, xa) (yr, ya)
  change
    (∑ p : Prod r a,
      ρ.purifiedInputForHypothesisTestingDPI.state.matrix ((p, xr), xa) ((p, yr), ya)) =
      ρ.matrix (xr, xa) (yr, ya)
  have hentry :=
    congrFun (congrFun (State.canonicalPurification_matrix ρ) (xr, xa)) (yr, ya)
  rw [← hentry]
  simp [QIT.partialTraceA, purifiedInputForHypothesisTestingDPI,
    PureVector.reindex_state, State.reindex, PureVector.state_matrix,
    State.canonicalPurification]

theorem hypothesisTestingBeta_applyReferenceIsometry_le
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ σ : State (Prod r₁ a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    State.hypothesisTestingBeta
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε ≤
      ρ.hypothesisTestingBeta σ ε := by
  change
    State.hypothesisTestingBeta
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε ≤
      sInf (ρ.hypothesisTestingBetaCandidateSet σ ε)
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    State.hypothesisTestingBeta_le_of_effect
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε
        (V.pushForwardHypothesisTestingEffect ρ ε Λ)
  rw [ReferenceIsometry.pushForwardHypothesisTestingEffect_typeIIError V ρ σ ε Λ] at hle
  exact hle

theorem hypothesisTestingRelativeEntropyE_le_applyReferenceIsometry
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ σ : State (Prod r₁ a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingRelativeEntropyE σ ε ≤
      State.hypothesisTestingRelativeEntropyE
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε := by
  let ρ' : State (Prod r₂ a) :=
    ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ
  let σ' : State (Prod r₂ a) :=
    ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ
  have hβle : ρ'.hypothesisTestingBeta σ' ε ≤ ρ.hypothesisTestingBeta σ ε := by
    exact hypothesisTestingBeta_applyReferenceIsometry_le V ρ σ ε hε
  by_cases hβin_zero : ρ.hypothesisTestingBeta σ ε = 0
  · have hβout_nonneg : 0 ≤ ρ'.hypothesisTestingBeta σ' ε :=
      ρ'.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ' ε hε
    have hβout_zero : ρ'.hypothesisTestingBeta σ' ε = 0 :=
      le_antisymm (by simpa [hβin_zero] using hβle) hβout_nonneg
    simp [hypothesisTestingRelativeEntropyE, hβin_zero, hβout_zero, ρ', σ']
  · have hβin_nonneg := ρ.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ ε hε
    have hβin_pos : 0 < ρ.hypothesisTestingBeta σ ε :=
      lt_of_le_of_ne' hβin_nonneg hβin_zero
    by_cases hβout_zero : ρ'.hypothesisTestingBeta σ' ε = 0
    · simp [hypothesisTestingRelativeEntropyE, hβin_zero, hβout_zero, ρ', σ']
    · have hβout_nonneg : 0 ≤ ρ'.hypothesisTestingBeta σ' ε :=
        ρ'.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ' ε hε
      have hβout_pos : 0 < ρ'.hypothesisTestingBeta σ' ε :=
        lt_of_le_of_ne' hβout_nonneg hβout_zero
      have hlog :
          log2 (ρ'.hypothesisTestingBeta σ' ε) ≤
            log2 (ρ.hypothesisTestingBeta σ ε) := by
        unfold log2
        exact div_le_div_of_nonneg_right
          (Real.log_le_log hβout_pos hβle)
          (le_of_lt (Real.log_pos one_lt_two))
      have hrel :
          ρ.hypothesisTestingRelativeEntropy σ ε ≤
            ρ'.hypothesisTestingRelativeEntropy σ' ε := by
        rw [hypothesisTestingRelativeEntropy_eq, hypothesisTestingRelativeEntropy_eq]
        exact neg_le_neg hlog
      have hrelE :
          (ρ.hypothesisTestingRelativeEntropy σ ε : EReal) ≤
            (ρ'.hypothesisTestingRelativeEntropy σ' ε : EReal) := by
        exact_mod_cast hrel
      simpa [hypothesisTestingRelativeEntropyE, hβin_zero, hβout_zero, ρ', σ']
        using hrelE

theorem hypothesisTestingBeta_le_applyState
    (Φ : Channel a b) (ρ σ : State a) (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingBeta σ ε ≤
      (Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε := by
  rw [hypothesisTestingBeta_eq_sInf]
  refine le_csInf
    ((Φ.applyState ρ).hypothesisTestingBetaCandidateSet_nonempty_of_nonneg
      (Φ.applyState σ) ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    ρ.hypothesisTestingBeta_le_of_effect σ ε
      (Φ.pullbackHypothesisTestingEffect ρ ε Λ)
  rw [Φ.pullbackHypothesisTestingEffect_typeIIError ρ σ ε Λ] at hle
  exact hle

theorem hypothesisTestingRelativeEntropyE_applyState_le
    (Φ : Channel a b) (ρ σ : State a) (ε : ℝ) (hε : 0 ≤ ε) :
    (Φ.applyState ρ).hypothesisTestingRelativeEntropyE (Φ.applyState σ) ε ≤
      ρ.hypothesisTestingRelativeEntropyE σ ε := by
  have hβle := ρ.hypothesisTestingBeta_le_applyState Φ σ ε hε
  by_cases hβin_zero : ρ.hypothesisTestingBeta σ ε = 0
  · simp [hypothesisTestingRelativeEntropyE, hβin_zero]
  · have hβin_nonneg := ρ.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ ε hε
    have hβin_pos : 0 < ρ.hypothesisTestingBeta σ ε :=
      lt_of_le_of_ne' hβin_nonneg hβin_zero
    have hβout_pos :
        0 < (Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε :=
      lt_of_lt_of_le hβin_pos hβle
    have hβout_zero :
        (Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε ≠ 0 :=
      ne_of_gt hβout_pos
    have hlog :
        log2 (ρ.hypothesisTestingBeta σ ε) ≤
          log2 ((Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε) := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hβin_pos hβle) (le_of_lt (Real.log_pos one_lt_two))
    have hrel :
        (Φ.applyState ρ).hypothesisTestingRelativeEntropy (Φ.applyState σ) ε ≤
          ρ.hypothesisTestingRelativeEntropy σ ε := by
      rw [hypothesisTestingRelativeEntropy_eq, hypothesisTestingRelativeEntropy_eq]
      exact neg_le_neg hlog
    have hrelE :
        ((Φ.applyState ρ).hypothesisTestingRelativeEntropy
          (Φ.applyState σ) ε : EReal) ≤
            (ρ.hypothesisTestingRelativeEntropy σ ε : EReal) := by
      exact_mod_cast hrel
    simpa [hypothesisTestingRelativeEntropyE, hβin_zero, hβout_zero] using hrelE

/-- A right-local channel preserves the left marginal. -/
theorem marginalA_applyState_id_prod
    (ρ : State (Prod a b)) (D : Channel b c) :
    (((Channel.idChannel a).prod D).applyState ρ).marginalA = ρ.marginalA := by
  apply State.ext
  change partialTraceB (a := a) (b := c)
      (MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix) =
    partialTraceB (a := a) (b := b) ρ.matrix
  ext i i'
  simp only [partialTraceB]
  let S : CMatrix b := fun j j' => ρ.matrix (i, j) (i', j')
  have htrace :
      (D.map S).trace = S.trace :=
    D.tracePreserving S
  calc
    ∑ j : c, MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix (i, j) (i', j) =
        ∑ j : c, D.map S j j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simpa [S] using
            (MatrixMap.kron_idChannel_left_apply_slice (a := a)
              (Φ := D.map) (X := ρ.matrix) (ad := (i, j)) (ad' := (i', j)))
    _ = ∑ j : b, ρ.matrix (i, j) (i', j) := by
          simpa [S, Matrix.trace] using htrace

theorem idChannel_applyState (ρ : State a) :
    (Channel.idChannel a).applyState ρ = ρ := by
  apply State.ext
  change (Channel.idChannel a).map ρ.matrix = ρ.matrix
  simp [Channel.idChannel, MatrixMap.ofKraus]

theorem applyState_id_prod_prod
    (ρA : State a) (σB : State b) (D : Channel b c) :
    ((Channel.idChannel a).prod D).applyState (ρA.prod σB) =
      ρA.prod (D.applyState σB) := by
  rw [Channel.applyState_prod, idChannel_applyState]

/-- A left-local channel preserves the right marginal. -/
theorem marginalB_applyState_prod_id
    (ρ : State (Prod a b)) (D : Channel a c) :
    ((D.prod (Channel.idChannel b)).applyState ρ).marginalB = ρ.marginalB := by
  apply State.ext
  change partialTraceA (a := c) (b := b)
      (MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix) =
    partialTraceA (a := a) (b := b) ρ.matrix
  ext j j'
  simp only [partialTraceA]
  let S : CMatrix a := fun i i' => ρ.matrix (i, j) (i', j')
  have htrace :
      (D.map S).trace = S.trace :=
    D.tracePreserving S
  calc
    ∑ i : c, MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix (i, j) (i, j') =
        ∑ i : c, D.map S i i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simpa [S] using
            (MatrixMap.kron_idChannel_apply_slice (a := a) (b := c) (r := b)
              (Φ := D.map) (X := ρ.matrix) (br := (i, j)) (br' := (i, j')))
    _ = ∑ i : a, ρ.matrix (i, j) (i, j') := by
          simpa [S, Matrix.trace] using htrace

theorem applyState_prod_id_prod
    (ρA : State a) (σB : State b) (D : Channel a c) :
    (D.prod (Channel.idChannel b)).applyState (ρA.prod σB) =
      (D.applyState ρA).prod σB := by
  rw [Channel.applyState_prod, idChannel_applyState]

theorem marginalA_applyState_prod_id
    (ρ : State (Prod a b)) (D : Channel a c) :
    ((D.prod (Channel.idChannel b)).applyState ρ).marginalA =
      D.applyState ρ.marginalA := by
  apply State.ext
  change partialTraceB (a := c) (b := b)
      (MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix) =
    D.map (partialTraceB (a := a) (b := b) ρ.matrix)
  ext i i'
  simp only [partialTraceB]
  let S : b → CMatrix a := fun j => fun x x' => ρ.matrix (x, j) (x', j)
  have hsum :
      (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) =
        ∑ j : b, S j := by
    ext x x'
    change (∑ j : b, ρ.matrix (x, j) (x', j)) =
      (∑ j : b, S j) x x'
    simp only [Matrix.sum_apply]
    rfl
  change (∑ j : b,
      MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix (i, j) (i', j)) =
    D.map (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) i i'
  rw [hsum, map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa [S] using
    (MatrixMap.kron_idChannel_apply_slice (a := a) (b := c) (r := b)
      (Φ := D.map) (X := ρ.matrix) (br := (i, j)) (br' := (i', j)))

/-- Optimized extended-real hypothesis-testing mutual information does not
decrease when the first/reference register is embedded by an isometry. -/
theorem hypothesisTestingMutualInformationE_le_applyReferenceIsometry
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ : State (Prod r₁ a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingMutualInformationE ε ≤
      State.hypothesisTestingMutualInformationE
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        ε := by
  let ρ' : State (Prod r₂ a) :=
    ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ
  rw [hypothesisTestingMutualInformationE_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σA, rfl⟩
  have hinMem :
      ρ.hypothesisTestingRelativeEntropyE (ρ.marginalA.prod σA) ε ∈
        hypothesisTestingMutualInformationECandidateSet (a := r₁) (b := a) ρ ε := by
    exact ⟨σA, rfl⟩
  have hinLe :
      ρ.hypothesisTestingMutualInformationE ε ≤
        ρ.hypothesisTestingRelativeEntropyE (ρ.marginalA.prod σA) ε := by
    rw [hypothesisTestingMutualInformationE_eq_sInf]
    exact sInf_le hinMem
  have hprod :
      ρ'.marginalA.prod σA =
        ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState
          (ρ.marginalA.prod σA) := by
    simpa [ρ', marginalA_applyState_prod_id] using
      (applyState_prod_id_prod ρ.marginalA σA (Channel.ofReferenceIsometry V)).symm
  have hD :
      ρ.hypothesisTestingRelativeEntropyE (ρ.marginalA.prod σA) ε ≤
        ρ'.hypothesisTestingRelativeEntropyE (ρ'.marginalA.prod σA) ε := by
    simpa [ρ', hprod] using
      hypothesisTestingRelativeEntropyE_le_applyReferenceIsometry
        V ρ (ρ.marginalA.prod σA) ε hε
  exact hinLe.trans hD

/-- Optimized hypothesis-testing mutual information is monotone under local
post-processing on the second register, in the extended-real convention. -/
theorem hypothesisTestingMutualInformationE_dataProcessing_right
    (ρ : State (Prod a b)) (D : Channel b c) (ε : ℝ) (hε : 0 ≤ ε) :
    (((Channel.idChannel a).prod D).applyState ρ).hypothesisTestingMutualInformationE ε ≤
      ρ.hypothesisTestingMutualInformationE ε := by
  let ρ' : State (Prod a c) := ((Channel.idChannel a).prod D).applyState ρ
  rw [hypothesisTestingMutualInformationE_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have hρAmarg : ρ'.marginalA = ρ.marginalA := by
    exact marginalA_applyState_id_prod ρ D
  have hprod :
      ρ'.marginalA.prod (D.applyState σB) =
        ((Channel.idChannel a).prod D).applyState (ρ.marginalA.prod σB) := by
    rw [hρAmarg]
    exact (applyState_id_prod_prod ρ.marginalA σB D).symm
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropyE
          (ρ'.marginalA.prod (D.applyState σB)) ε ∈
        hypothesisTestingMutualInformationECandidateSet (a := a) (b := c) ρ' ε := by
    exact ⟨D.applyState σB, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformationE ε ≤
        ρ'.hypothesisTestingRelativeEntropyE
          (ρ'.marginalA.prod (D.applyState σB)) ε := by
    rw [hypothesisTestingMutualInformationE_eq_sInf]
    exact sInf_le houtMem
  have hDPI :
      ρ'.hypothesisTestingRelativeEntropyE
          (((Channel.idChannel a).prod D).applyState (ρ.marginalA.prod σB)) ε ≤
        ρ.hypothesisTestingRelativeEntropyE (ρ.marginalA.prod σB) ε := by
    exact hypothesisTestingRelativeEntropyE_applyState_le
      ((Channel.idChannel a).prod D) ρ (ρ.marginalA.prod σB) ε hε
  exact houtLe.trans (by simpa [hprod] using hDPI)

/-- Optimized hypothesis-testing mutual information is monotone under local
post-processing on the first register, in the extended-real convention. -/
theorem hypothesisTestingMutualInformationE_dataProcessing_left
    (ρ : State (Prod a b)) (D : Channel a c) (ε : ℝ) (hε : 0 ≤ ε) :
    ((D.prod (Channel.idChannel b)).applyState ρ).hypothesisTestingMutualInformationE ε ≤
      ρ.hypothesisTestingMutualInformationE ε := by
  let ρ' : State (Prod c b) := (D.prod (Channel.idChannel b)).applyState ρ
  rw [hypothesisTestingMutualInformationE_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have hρAmarg : ρ'.marginalA = D.applyState ρ.marginalA := by
    apply State.ext
    change partialTraceB (a := c) (b := b)
        (MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix) =
      D.map (partialTraceB (a := a) (b := b) ρ.matrix)
    ext i i'
    simp only [partialTraceB]
    let S : b → CMatrix a := fun j => fun x x' => ρ.matrix (x, j) (x', j)
    have hsum :
        (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) =
          ∑ j : b, S j := by
      ext x x'
      change (∑ j : b, ρ.matrix (x, j) (x', j)) =
        (∑ j : b, S j) x x'
      simp only [Matrix.sum_apply]
      rfl
    change (∑ j : b,
        MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix (i, j) (i', j)) =
      D.map (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) i i'
    rw [hsum, map_sum]
    simp only [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simpa [S] using
      (MatrixMap.kron_idChannel_apply_slice (a := a) (b := c) (r := b)
        (Φ := D.map) (X := ρ.matrix) (br := (i, j)) (br' := (i', j)))
  have hprod :
      ρ'.marginalA.prod σB =
        (D.prod (Channel.idChannel b)).applyState (ρ.marginalA.prod σB) := by
    rw [hρAmarg]
    exact (applyState_prod_id_prod ρ.marginalA σB D).symm
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropyE (ρ'.marginalA.prod σB) ε ∈
        hypothesisTestingMutualInformationECandidateSet (a := c) (b := b) ρ' ε := by
    exact ⟨σB, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformationE ε ≤
        ρ'.hypothesisTestingRelativeEntropyE (ρ'.marginalA.prod σB) ε := by
    rw [hypothesisTestingMutualInformationE_eq_sInf]
    exact sInf_le houtMem
  have hDPI :
      ρ'.hypothesisTestingRelativeEntropyE
          ((D.prod (Channel.idChannel b)).applyState (ρ.marginalA.prod σB)) ε ≤
        ρ.hypothesisTestingRelativeEntropyE (ρ.marginalA.prod σB) ε := by
    exact hypothesisTestingRelativeEntropyE_applyState_le
      (D.prod (Channel.idChannel b)) ρ (ρ.marginalA.prod σB) ε hε
  exact houtLe.trans (by simpa [hprod] using hDPI)

/-- Repartition `(M × E) × B` as `M × (B × E)`, moving side information
from the reference block to the output block while preserving the message
register as the first factor. -/
def messageOutputSideInfoEquiv
    (m e b : Type*) : Prod (Prod m e) b ≃ Prod m (Prod b e) :=
  (Equiv.prodAssoc m e b).trans
    (Equiv.prodCongr (Equiv.refl m) (Equiv.prodComm e b))

private theorem marginalA_reindex_messageOutputSideInfoEquiv
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θ : State (Prod (Prod m e) b)) :
    (θ.reindex (messageOutputSideInfoEquiv m e b)).marginalA =
      θ.marginalA.marginalA := by
  apply State.ext
  ext i j
  simp only [State.marginalA_matrix, State.reindex_matrix]
  change
    (∑ x : Prod b e, θ.matrix
      ((messageOutputSideInfoEquiv m e b).symm (i, x))
      ((messageOutputSideInfoEquiv m e b).symm (j, x))) =
    ∑ x : e, θ.marginalA.matrix (i, x) (j, x)
  rw [Fintype.sum_prod_type]
  simp [messageOutputSideInfoEquiv, State.marginalA, partialTraceB]
  rw [Finset.sum_comm]

private theorem product_reference_reindex_messageOutputSideInfoEquiv
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θME : State (Prod m e)) (σB : State b)
    (hprod : θME = θME.marginalA.prod θME.marginalB) :
    (θME.prod σB).reindex (messageOutputSideInfoEquiv m e b) =
      θME.marginalA.prod (σB.prod θME.marginalB) := by
  apply State.ext
  ext x y
  rcases x with ⟨xm, xb, xe⟩
  rcases y with ⟨ym, yb, ye⟩
  have hentry :=
    congrFun (congrFun (congrArg State.matrix hprod) (xm, xe)) (ym, ye)
  simp [State.reindex, State.prod, Matrix.kronecker,
    messageOutputSideInfoEquiv, hentry, mul_assoc, mul_left_comm, mul_comm]

theorem hypothesisTestingMutualInformationE_repartition_le_of_marginalA_eq_prod
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θ : State (Prod (Prod m e) b)) (ε : ℝ) (hε : 0 ≤ ε)
    (hprod : θ.marginalA = θ.marginalA.marginalA.prod θ.marginalA.marginalB) :
    ((θ.reindex (messageOutputSideInfoEquiv m e b)).hypothesisTestingMutualInformationE ε) ≤
      θ.hypothesisTestingMutualInformationE ε := by
  let θ' : State (Prod m (Prod b e)) :=
    θ.reindex (messageOutputSideInfoEquiv m e b)
  rw [hypothesisTestingMutualInformationE_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  let σBE : State (Prod b e) := σB.prod θ.marginalA.marginalB
  have houtMem :
      θ'.hypothesisTestingRelativeEntropyE (θ'.marginalA.prod σBE) ε ∈
        hypothesisTestingMutualInformationECandidateSet
          (a := m) (b := Prod b e) θ' ε := by
    exact ⟨σBE, rfl⟩
  have houtLe :
      θ'.hypothesisTestingMutualInformationE ε ≤
        θ'.hypothesisTestingRelativeEntropyE (θ'.marginalA.prod σBE) ε := by
    rw [hypothesisTestingMutualInformationE_eq_sInf]
    exact sInf_le houtMem
  have hmarg : θ'.marginalA = θ.marginalA.marginalA := by
    simpa [θ'] using marginalA_reindex_messageOutputSideInfoEquiv θ
  have hprodState :
      θ'.marginalA.prod σBE =
        (θ.marginalA.prod σB).reindex (messageOutputSideInfoEquiv m e b) := by
    rw [hmarg]
    exact (product_reference_reindex_messageOutputSideInfoEquiv
      θ.marginalA σB hprod).symm
  have hD :
      θ'.hypothesisTestingRelativeEntropyE
          ((θ.marginalA.prod σB).reindex (messageOutputSideInfoEquiv m e b)) ε =
        θ.hypothesisTestingRelativeEntropyE (θ.marginalA.prod σB) ε := by
    simpa [θ'] using
      hypothesisTestingRelativeEntropyE_reindex θ (θ.marginalA.prod σB) ε hε
        (messageOutputSideInfoEquiv m e b)
  exact houtLe.trans (by simpa [hprodState] using le_of_eq hD)

end State

namespace Channel

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- If a bipartite state is obtained from a channel output by local
post-processing on the output register, then its optimized extended-real
hypothesis-testing mutual information is bounded by the channel quantity.

This is the reusable channel-optimization bridge for converse arguments once a
protocol-specific construction has represented the relevant state as a
post-processed output for a pure input with the canonical input-copy reference. -/
theorem hypothesisTestingMutualInformationE_postprocess_output_le_channel
    (N : Channel a b) (D : Channel b c) (ψ : PureVector (Prod a a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    (((Channel.idChannel a).prod D).applyState
        (N.hypothesisTestingOutputState ψ)).hypothesisTestingMutualInformationE ε ≤
      N.hypothesisTestingMutualInformationE ε := by
  exact (State.hypothesisTestingMutualInformationE_dataProcessing_right
    (N.hypothesisTestingOutputState ψ) D ε hε).trans
      (N.inputHypothesisTestingMutualInformationE_le_channel ε ψ)

/-- Equality-shaped version of
`hypothesisTestingMutualInformationE_postprocess_output_le_channel`, useful when
the protocol state has first been identified with a post-processed channel
output. -/
theorem hypothesisTestingMutualInformationE_le_channel_of_eq_postprocess_output
    (N : Channel a b) (D : Channel b c) (ψ : PureVector (Prod a a))
    (ω : State (Prod a c)) (ε : ℝ) (hε : 0 ≤ ε)
    (hω : ω =
      ((Channel.idChannel a).prod D).applyState
        (N.hypothesisTestingOutputState ψ)) :
    ω.hypothesisTestingMutualInformationE ε ≤
      N.hypothesisTestingMutualInformationE ε := by
  rw [hω]
  exact N.hypothesisTestingMutualInformationE_postprocess_output_le_channel D ψ ε hε

variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- A reference isometry commutes with applying the communication channel on
the target/input register. -/
theorem hypothesisTestingOutputState_applyReferenceIsometry
    (N : Channel a b) (V : ReferenceIsometry r₁ r₂)
    (ψ : PureVector (Prod r₁ a)) :
    N.hypothesisTestingOutputState (V.applyPureVector ψ) =
      ((Channel.ofReferenceIsometry V).prod (Channel.idChannel b)).applyState
        (N.hypothesisTestingOutputState ψ) := by
  apply State.ext
  change MatrixMap.kron (Channel.idChannel r₂).map N.map
      (V.applyPureVector ψ).state.matrix =
    MatrixMap.kron (Channel.ofReferenceIsometry V).map
      (Channel.idChannel b).map
      (MatrixMap.kron (Channel.idChannel r₁).map N.map ψ.state.matrix)
  have hVstate :
      (V.applyPureVector ψ).state.matrix =
        V.applyMatrix ψ.state.matrix := by
    rw [PureVector.state_matrix, PureVector.state_matrix]
    exact V.rankOne_applyAmp ψ.amp
  rw [hVstate]
  rw [Channel.ofReferenceIsometry_map]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrix]
  exact MatrixMap.kron_idChannel_left_apply_applyMatrix N.map V ψ.state.matrix

/-- Arbitrary-reference pure inputs whose reference system contains an
input-copy reference are bounded by the channel extended-real
hypothesis-testing mutual information. -/
theorem inputHypothesisTestingMutualInformationE_le_channel_of_card_le
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε)
    (hcard : Fintype.card a ≤ Fintype.card r) :
    N.inputHypothesisTestingMutualInformationE ψ ε ≤
      N.hypothesisTestingMutualInformationE ε := by
  let φ : PureVector (Prod a a) := ψ.state.marginalB.canonicalPurification
  have hφ : φ.Purifies ψ.state.marginalB := by
    exact ψ.state.marginalB.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.marginalB :=
    ψ.purifies_marginalB_forHypothesisTestingDPI
  rcases PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.hypothesisTestingOutputState ψ =
        ((Channel.ofReferenceIsometry V).prod (Channel.idChannel b)).applyState
          (N.hypothesisTestingOutputState φ) := by
    rw [hV]
    exact N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  rw [inputHypothesisTestingMutualInformationE, hout]
  exact (State.hypothesisTestingMutualInformationE_dataProcessing_left
      (N.hypothesisTestingOutputState φ) (Channel.ofReferenceIsometry V) ε hε).trans
    (N.inputHypothesisTestingMutualInformationE_le_channel ε φ)

/-- Arbitrary-reference pure inputs are bounded by the channel optimized
extended-real hypothesis-testing mutual information.  The proof pads the
reference by an isometric embedding, uses the sufficiently-large-reference
purification bridge, and transports the hypothesis-testing mutual information
back along the isometry. -/
theorem inputHypothesisTestingMutualInformationE_le_channel_of_arbitrary_reference
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε) :
    N.inputHypothesisTestingMutualInformationE ψ ε ≤
      N.hypothesisTestingMutualInformationE ε := by
  let V : ReferenceIsometry r (Sum a r) :=
    ReferenceIsometry.sumInrForHypothesisTestingDPI a r
  let ψ' : PureVector (Prod (Sum a r) a) := V.applyPureVector ψ
  have hlarge : Fintype.card a ≤ Fintype.card (Sum a r) := by
    rw [Fintype.card_sum]
    exact Nat.le_add_right _ _
  have hleft :
      N.inputHypothesisTestingMutualInformationE ψ ε ≤
        N.inputHypothesisTestingMutualInformationE ψ' ε := by
    unfold inputHypothesisTestingMutualInformationE
    rw [N.hypothesisTestingOutputState_applyReferenceIsometry V ψ]
    exact State.hypothesisTestingMutualInformationE_le_applyReferenceIsometry
      V (N.hypothesisTestingOutputState ψ) ε hε
  have hright :
      N.inputHypothesisTestingMutualInformationE ψ' ε ≤
        N.hypothesisTestingMutualInformationE ε := by
    exact N.inputHypothesisTestingMutualInformationE_le_channel_of_card_le
      ψ' ε hε hlarge
  exact hleft.trans hright

/-- A pure channel output remains bounded by the channel optimized
extended-real hypothesis-testing mutual information after arbitrary local
post-processing on the reference register.

This is the source-shaped bridge used by meta-converse arguments: once a
protocol state is identified as a reference-side post-processing of a pure
input-reference channel output, data processing reduces it to the channel
quantity `I_H^ε(N)`.
-/
theorem hypothesisTestingMutualInformationE_referencePostprocess_output_le_channel
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    {s : Type x} [Fintype s] [DecidableEq s]
    (D : Channel r s) (ψ : PureVector (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε) :
    (((D.prod (Channel.idChannel b)).applyState
        (N.hypothesisTestingOutputState ψ)).hypothesisTestingMutualInformationE ε) ≤
      N.hypothesisTestingMutualInformationE ε := by
  exact (State.hypothesisTestingMutualInformationE_dataProcessing_left
      (N.hypothesisTestingOutputState ψ) D ε hε).trans
    (N.inputHypothesisTestingMutualInformationE_le_channel_of_arbitrary_reference ψ ε hε)

/-- Equality-shaped version of
`hypothesisTestingMutualInformationE_referencePostprocess_output_le_channel`,
for protocol constructions that first identify the tested state with a
reference-side post-processing of a pure channel output. -/
theorem hypothesisTestingMutualInformationE_le_channel_of_eq_referencePostprocess_output
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    {s : Type x} [Fintype s] [DecidableEq s]
    (D : Channel r s) (ψ : PureVector (Prod r a)) (ω : State (Prod s b))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hω : ω =
      (D.prod (Channel.idChannel b)).applyState (N.hypothesisTestingOutputState ψ)) :
    ω.hypothesisTestingMutualInformationE ε ≤
      N.hypothesisTestingMutualInformationE ε := by
  rw [hω]
  exact N.hypothesisTestingMutualInformationE_referencePostprocess_output_le_channel
    D ψ ε hε

/-- Mixed input-reference states are also bounded by the channel optimized
extended-real hypothesis-testing mutual information.

The proof purifies the mixed input-reference state, traces out the extra
purifying reference after the channel use, and then applies reference-side data
processing together with the arbitrary-reference pure-input optimization
bridge. -/
theorem mixedInputOutput_hypothesisTestingMutualInformationE_le_channel
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ρ : State (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε) :
    (((Channel.idChannel r).prod N).applyState ρ).hypothesisTestingMutualInformationE ε ≤
      N.hypothesisTestingMutualInformationE ε := by
  let ψ : PureVector (Prod (Prod (Prod r a) r) a) :=
    ρ.purifiedInputForHypothesisTestingDPI
  let D : Channel (Prod (Prod r a) r) r :=
    Channel.traceOutAForHypothesisTestingDPI (Prod r a) r
  have hstate :
      (D.prod (Channel.idChannel b)).applyState (N.hypothesisTestingOutputState ψ) =
        ((Channel.idChannel r).prod N).applyState ρ := by
    calc
      (D.prod (Channel.idChannel b)).applyState (N.hypothesisTestingOutputState ψ) =
        (D.prod (Channel.idChannel b)).applyState
          (((Channel.idChannel (Prod (Prod r a) r)).prod N).applyState ψ.state) := rfl
      _ = ((Channel.idChannel r).prod N).applyState
          (((D.prod (Channel.idChannel a)).applyState ψ.state)) := by
          exact Channel.traceOutAForHypothesisTestingDPI_prod_id_applyState_id_prod
            (p := Prod r a) (r := r) N ψ.state
      _ = ((Channel.idChannel r).prod N).applyState ρ := by
          rw [State.traceOut_purifiedInputForHypothesisTestingDPI]
  rw [← hstate]
  exact N.hypothesisTestingMutualInformationE_referencePostprocess_output_le_channel
    D ψ ε hε

end Channel

end

end QIT
