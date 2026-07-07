/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.EntanglementAssistedPetzLowerBound
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedWeakConverse
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedPetzAdditivity
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedPetzLimit
public import QIT.Coding.EntanglementAssisted.EntanglementAssistedSandwichedAdditivity
public import QIT.HypothesisTesting.PetzComparison
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.AlickiFannesWinter

/-!
# Asymptotic entanglement-assisted classical communication helpers

This module contains the tensor-power protocol lifting and rate-normalization
lemmas used in the Khatri--Wilde one-shot-to-asymptotic achievability and
converse routes [KhatriWilde2024Principles, Chapters/EA_capacity.tex:894-982]
and [KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331].

The statements here are deliberately operational: they turn concrete reliable
`n`-use entanglement-assisted classical codes into achievable asymptotic rates,
or convert eventual `n`-use log-cardinality upper bounds into the converse
witness family consumed by the final capacity proof.  The Petz--Renyi
additivity and alpha-to-one limit inputs are separate proof dependencies.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

open Filter

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private theorem log2_pow_nat (x : ℝ) (n : ℕ) :
    log2 (x ^ n) = (n : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow]
  ring

namespace PetzRenyiAlpha

/-- The left-to-one filter on the source range `0 < alpha < 1` is nontrivial:
every one-sided neighborhood of `1` contains an admissible Renyi parameter. -/
theorem leftToOne_neBot : Filter.NeBot PetzRenyiAlpha.leftToOne := by
  unfold PetzRenyiAlpha.leftToOne
  refine Filter.comap_neBot ?_
  intro t ht
  have hflt :
      (t ∩ Set.Iio (1 : ℝ)) ∩ Set.Ioi (0 : ℝ) ∈
        nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact Filter.inter_mem
      (Filter.inter_mem ht self_mem_nhdsWithin)
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one))
  haveI : Filter.NeBot (nhdsWithin (1 : ℝ) (Set.Iio 1)) :=
    nhdsWithin_Iio_neBot (α := ℝ) (a := 1) (b := 1) le_rfl
  rcases Filter.nonempty_of_mem hflt with ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · exact ⟨hx.2, hx.1.2⟩
  · exact hx.1.1

end PetzRenyiAlpha

namespace MatrixMap

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

/-- Relabel the output basis of a finite matrix map. -/
def outputReindex (Phi : MatrixMap α β) (e : β ≃ γ) : MatrixMap α γ where
  toFun X := Matrix.reindex e e (Phi X)
  map_add' X Y := by
    ext i j
    simp [Matrix.reindex_apply]
  map_smul' c X := by
    ext i j
    simp [Matrix.reindex_apply]

theorem outputReindex_isCompletelyPositive
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive (Phi.outputReindex e) := by
  change (MatrixMap.choi (Phi.outputReindex e)).PosSemidef
  have hchoi :
      MatrixMap.choi (Phi.outputReindex e) =
        (MatrixMap.choi Phi).submatrix
          (fun x : Prod α γ => (x.1, e.symm x.2))
          (fun x : Prod α γ => (x.1, e.symm x.2)) := by
    ext x y
    rfl
  rw [hchoi]
  exact hPhi.submatrix _

theorem outputReindex_isTracePreserving
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : MatrixMap.IsTracePreserving Phi) :
    MatrixMap.IsTracePreserving (Phi.outputReindex e) := by
  intro X
  change (Matrix.reindex e e (Phi X)).trace = X.trace
  rw [cMatrix_trace_reindex e, hPhi X]

theorem outputReindex_mapsPositive
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : ∀ X : CMatrix α, X.PosSemidef → (Phi X).PosSemidef) :
    ∀ X : CMatrix α, X.PosSemidef → ((Phi.outputReindex e) X).PosSemidef := by
  intro X hX
  change (Matrix.reindex e e (Phi X)).PosSemidef
  exact (hPhi X hX).submatrix e.symm

end MatrixMap

namespace MatrixMap

/-- Right-slice form of the Kronecker product of matrix maps.  It views
`(Φ ⊗ Ψ)(X)` as first applying `Φ` to each right-index slice of `X`, then
applying `Ψ` to the resulting right-index matrix. -/
theorem kron_apply_slice_right
    {a₀ : Type u} {b₀ : Type v} {a₁ : Type w} {b₁ : Type x}
    [Fintype a₀] [DecidableEq a₀] [Fintype b₀] [DecidableEq b₀]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    (Φ : MatrixMap a₀ b₀) (Ψ : MatrixMap a₁ b₁) (X : CMatrix (Prod a₀ a₁))
    (x₀ y₀ : b₀) (x₁ y₁ : b₁) :
    MatrixMap.kron Φ Ψ X (x₀, x₁) (y₀, y₁) =
      Ψ (fun j j' => Φ (fun i i' => X (i, j) (i', j')) x₀ y₀) x₁ y₁ := by
  unfold MatrixMap.kron
  rw [map_eq_sum_single Ψ
    (fun j j' => Φ (fun i i' => X (i, j) (i', j')) x₀ y₀)]
  simp only [Matrix.sum_apply]
  have hΦ : ∀ j j',
      Φ (fun i i' => X (i, j) (i', j')) x₀ y₀ =
        ∑ i : a₀, ∑ i' : a₀,
          X (i, j) (i', j') * Φ (Matrix.single i i' (1 : Complex)) x₀ y₀ := by
    intro j j'
    have h := congrFun
      (congrFun (map_eq_sum_single Φ (fun i i' => X (i, j) (i', j'))) x₀)
      y₀
    simpa [Matrix.sum_apply] using h
  simp_rw [hΦ]
  simp [Finset.sum_mul, mul_assoc]

end MatrixMap

namespace Channel

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

/-- Relabel the output basis of a finite-dimensional channel. -/
def outputReindex (Phi : Channel α β) (e : β ≃ γ) : Channel α γ where
  map := Phi.map.outputReindex e
  completelyPositive :=
    MatrixMap.outputReindex_isCompletelyPositive Phi.map e Phi.completelyPositive
  tracePreserving :=
    MatrixMap.outputReindex_isTracePreserving Phi.map e Phi.tracePreserving
  mapsPositive :=
    MatrixMap.outputReindex_mapsPositive Phi.map e Phi.mapsPositive

@[simp]
theorem outputReindex_applyState (Phi : Channel α β) (ρ : State α) (e : β ≃ γ) :
    (Phi.outputReindex e).applyState ρ = (Phi.applyState ρ).reindex e := by
  apply State.ext
  rfl

end Channel

namespace POVM

variable {α : Type u} {β : Type v} {m : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype m] [DecidableEq m]

/-- Relabel the measured system of a finite POVM. -/
def reindex (M : POVM m α) (e : α ≃ β) : POVM m β where
  effects y := Matrix.reindex e e (M.effects y)
  pos y := (M.pos y).submatrix e.symm
  sum_eq_one := by
    ext i j
    have h := congrFun (congrFun M.sum_eq_one (e.symm i)) (e.symm j)
    simpa [Matrix.sum_apply, Matrix.reindex_apply, Matrix.one_apply] using h

omit [DecidableEq m] in
@[simp]
theorem reindex_effects (M : POVM m α) (e : α ≃ β) (y : m) :
    (M.reindex e).effects y = Matrix.reindex e e (M.effects y) :=
  rfl

/-- Born probabilities are invariant under simultaneous state/effect relabeling. -/
theorem prob_reindex_state (M : POVM m α) (ρ : State α) (e : α ≃ β) (y : m) :
    ((M.reindex e).prob (ρ.reindex e) y : ℝ) = (M.prob ρ y : ℝ) := by
  rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
  change Complex.re
      (((Matrix.reindex e e ρ.matrix) *
        (Matrix.reindex e e (M.effects y))).trace) =
    Complex.re ((ρ.matrix * M.effects y).trace)
  change Complex.re
      ((((Matrix.reindexAlgEquiv ℂ ℂ e) ρ.matrix) *
        ((Matrix.reindexAlgEquiv ℂ ℂ e) (M.effects y))).trace) =
    Complex.re ((ρ.matrix * M.effects y).trace)
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e ρ.matrix (M.effects y)]
  change Complex.re ((Matrix.reindex e e (ρ.matrix * M.effects y)).trace) =
    Complex.re ((ρ.matrix * M.effects y).trace)
  rw [cMatrix_trace_reindex e]

end POVM

private theorem state_reindex_reindex_symm {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State α) (e : α ≃ β) :
    (ρ.reindex e).reindex e.symm = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

private theorem state_reindex_symm_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State β) (e : α ≃ β) :
    (ρ.reindex e.symm).reindex e = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

private theorem tensorPower_nonempty_of_nonempty {α : Type u} [Nonempty α] :
    (n : ℕ) → Nonempty (QIT.TensorPower α n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 =>
      haveI : Nonempty (QIT.TensorPower α n) := tensorPower_nonempty_of_nonempty n
      inferInstanceAs (Nonempty (Prod α (QIT.TensorPower α n)))

theorem cMatrix_rpow_reindex_nonneg {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A : CMatrix α) (hA : A.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.reindex e e A) s =
      Matrix.reindex e e (CFC.rpow A s) := by
  change (Matrix.reindex e e A) ^ s = Matrix.reindex e e (A ^ s)
  have hmap_nonneg : 0 ≤ Matrix.reindex e e A := by
    exact Matrix.nonneg_iff_posSemidef.mpr (hA.submatrix e.symm)
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.rpow_eq_cfc_real (a := Matrix.reindex e e A) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixReindexStarAlgEquiv, Matrix.reindexAlgEquiv_apply] using
    (StarAlgHomClass.map_cfc
      (cMatrixReindexStarAlgEquiv e)
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous (Matrix.reindex e e : CMatrix α -> CMatrix β)
        fun_prop)).symm

namespace State

/-- Re-associate a product-channel output so that the second channel is the
right-local channel with reference `(R × B₁)`. -/
private theorem applyState_id_prod_prod_assoc_symm
    {r : Type u} {a₁ : Type v} {b₁ : Type w} {a₂ : Type x} {b₂ : Type y}
    [Fintype r] [DecidableEq r]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ρ : State (Prod r (Prod a₁ a₂))) :
    (((Channel.idChannel r).prod (N₁.prod N₂)).applyState ρ).reindex
        (Equiv.prodAssoc r b₁ b₂).symm =
      (((Channel.idChannel (Prod r b₁)).prod N₂).applyState
        ((((Channel.idChannel r).prod (N₁.prod (Channel.idChannel a₂))).applyState ρ).reindex
          (Equiv.prodAssoc r b₁ a₂).symm)) := by
  apply State.ext
  ext x y
  rcases x with ⟨xRB1, xB2⟩
  rcases y with ⟨yRB1, yB2⟩
  rcases xRB1 with ⟨xR, xB1⟩
  rcases yRB1 with ⟨yR, yB1⟩
  simp only [Channel.applyState, Channel.prod, State.reindex_matrix,
    Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [Equiv.prodAssoc]
  simp_rw [MatrixMap.kron_idChannel_left_apply_slice]
  change MatrixMap.kron N₁.map N₂.map
      (fun j j' => ρ.matrix (xR, j) (yR, j'))
      (xB1, xB2) (yB1, yB2) =
    N₂.map
      (fun j j' =>
        (MatrixMap.kron N₁.map (Channel.idChannel a₂).map
          (fun z z' => ρ.matrix (xR, z) (yR, z')))
          (xB1, j) (yB1, j'))
      xB2 yB2
  have hslice :
      (fun j j' =>
        (MatrixMap.kron N₁.map (Channel.idChannel a₂).map
          (fun z z' => ρ.matrix (xR, z) (yR, z')))
          (xB1, j) (yB1, j')) =
        (fun j j' =>
          N₁.map (fun i i' => ρ.matrix (xR, (i, j)) (yR, (i', j'))) xB1 yB1) := by
    ext j j'
    rw [MatrixMap.kron_idChannel_apply_slice]
  rw [hslice]
  exact MatrixMap.kron_apply_slice_right
    N₁.map N₂.map (fun j j' => ρ.matrix (xR, j) (yR, j'))
    xB1 yB1 xB2 yB2

/-- The `(R × B₁)` marginal of the partially processed state is the output of
`N₁` on the corresponding mixed `(R × A₁)` input. -/
private theorem partialProductOutput_marginalAB
    {r : Type u} {a₁ : Type v} {b₁ : Type w} {a₂ : Type x}
    [Fintype r] [DecidableEq r]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂]
    (N₁ : Channel a₁ b₁) (ρ : State (Prod r (Prod a₁ a₂))) :
    (((((Channel.idChannel r).prod (N₁.prod (Channel.idChannel a₂))).applyState ρ).reindex
          (Equiv.prodAssoc r b₁ a₂).symm).marginalAB) =
      ((Channel.idChannel r).prod N₁).applyState
        ((ρ.reindex (Equiv.prodAssoc r a₁ a₂).symm).marginalAB) := by
  apply State.ext
  ext x y
  rcases x with ⟨xR, xB1⟩
  rcases y with ⟨yR, yB1⟩
  simp only [State.marginalAB, State.marginalA, QIT.partialTraceB, State.reindex_matrix,
    Channel.applyState, Channel.prod, Matrix.submatrix_apply]
  simp [Equiv.prodAssoc]
  simp_rw [MatrixMap.kron_idChannel_left_apply_slice]
  change
    (∑ x_1 : a₂,
      (MatrixMap.kron N₁.map (Channel.idChannel a₂).map
        (fun j j' => ρ.matrix (xR, j) (yR, j')))
        (xB1, x_1) (yB1, x_1)) =
      N₁.map
        (fun j j' => ∑ x_1 : a₂, ρ.matrix (xR, (j, x_1)) (yR, (j', x_1)))
        xB1 yB1
  simp_rw [MatrixMap.kron_idChannel_apply_slice]
  have hsum :=
    congrFun
      (congrFun
        (map_sum N₁.map
          (fun x_1 : a₂ => fun i i' =>
            ρ.matrix (xR, (i, x_1)) (yR, (i', x_1)))
          Finset.univ)
        xB1)
      yB1
  simp only [Matrix.sum_apply] at hsum
  have hmatrix :
      (fun j j' => ∑ x_1 : a₂, ρ.matrix (xR, (j, x_1)) (yR, (j', x_1))) =
        (∑ x_1 : a₂, fun i i' => ρ.matrix (xR, (i, x_1)) (yR, (i', x_1))) := by
    ext j j'
    simp
  rw [hmatrix]
  exact hsum.symm

private theorem vonNeumann_punit_eq_zero (ρ : State PUnit.{u + 1}) :
    ρ.vonNeumann = 0 := by
  exact le_antisymm (by simpa [log2] using vonNeumann_le_log_card ρ) (vonNeumann_nonneg ρ)

private theorem mutualInformation_punit_punit_eq_zero
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) :
    QIT.mutualInformation ρ = 0 := by
  have hA : ρ.marginalA.vonNeumann = 0 := vonNeumann_punit_eq_zero ρ.marginalA
  have hB : ρ.marginalB.vonNeumann = 0 := vonNeumann_punit_eq_zero ρ.marginalB
  have hAB : ρ.vonNeumann = 0 := by
    exact le_antisymm (by simpa [log2] using vonNeumann_le_log_card ρ) (vonNeumann_nonneg ρ)
  simp [QIT.mutualInformation, hA, hB, hAB]

/-- Mutual information is additive on repartitioned product bipartite states:
`I(A₁A₂;B₁B₂)_{ρ⊗σ} = I(A₁;B₁)_ρ + I(A₂;B₂)_σ`.

This is the entropy-form version used along the source route in
Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1044-1058. -/
theorem mutualInformation_bipartiteProduct
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ : State (Prod a₁ b₁)) (σ : State (Prod a₂ b₂)) :
    mutualInformation (ρ.bipartiteProduct σ) =
      mutualInformation ρ + mutualInformation σ := by
  unfold mutualInformation
  rw [State.bipartiteProduct_marginalA, State.bipartiteProduct_marginalB]
  rw [State.vonNeumann_prod, State.vonNeumann_prod]
  unfold State.bipartiteProduct
  rw [State.vonNeumann_reindex, State.vonNeumann_prod]
  ring

/-- Chain-rule form used for the channel mutual-information additivity upper
bound:
`I(R;B₁B₂) = I(R;B₁) + I(RB₁;B₂) - I(B₁;B₂)`.

The state is stored as `(R × B₁) × B₂`; the left side re-associates it as
`R × (B₁ × B₂)`.
This follows the source route in Khatri--Wilde,
`Chapters/EA_capacity.tex`, lines 1080-1086. -/
theorem mutualInformation_assoc_chain
    {r : Type u} {b₁ : Type v} {b₂ : Type w}
    [Fintype r] [DecidableEq r] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ : State (Prod (Prod r b₁) b₂)) :
    mutualInformation (ρ.reindex (Equiv.prodAssoc r b₁ b₂)) =
      mutualInformation ρ.marginalAB + mutualInformation ρ -
        mutualInformation ρ.marginalBC := by
  unfold mutualInformation
  have hA :
      (ρ.reindex (Equiv.prodAssoc r b₁ b₂)).marginalA =
        ρ.marginalAB.marginalA := by
    apply State.ext
    ext x y
    simp [State.reindex, State.marginalA, State.marginalAB, QIT.partialTraceB,
      Equiv.prodAssoc, Fintype.sum_prod_type]
  have hB :
      (ρ.reindex (Equiv.prodAssoc r b₁ b₂)).marginalB =
        ρ.marginalBC := by
    apply State.ext
    ext x y
    simp [State.reindex, State.marginalB, State.marginalBC, QIT.partialTraceA,
      Equiv.prodAssoc]
  rw [hA, hB, State.vonNeumann_reindex]
  rw [State.marginalAB_eq_marginalA]
  rw [State.marginalBC_marginalA_eq_marginalBOfABC,
    State.marginalBC_marginalB_eq_marginalB]
  rw [State.marginalBOfABC_eq, State.marginalAB_eq_marginalA]
  ring

/-- Chain-rule upper bound obtained from
`I(R;B₁B₂) = I(R;B₁) + I(RB₁;B₂) - I(B₁;B₂)` and nonnegativity of
mutual information. -/
theorem mutualInformation_assoc_le
    {r : Type u} {b₁ : Type v} {b₂ : Type w}
    [Fintype r] [DecidableEq r] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ : State (Prod (Prod r b₁) b₂)) :
    mutualInformation (ρ.reindex (Equiv.prodAssoc r b₁ b₂)) ≤
      mutualInformation ρ.marginalAB + mutualInformation ρ := by
  rw [State.mutualInformation_assoc_chain]
  have hnonneg : 0 ≤ mutualInformation ρ.marginalBC :=
    State.mutualInformation_nonneg ρ.marginalBC
  linarith

/-- Mutual information is additive on IID bipartite tensor powers:
`I(A^n;B^n)_{ρ^{⊗n}} = n I(A;B)_ρ`. -/
theorem mutualInformation_tensorPowerBipartite (ρ : State (Prod a b)) (n : ℕ) :
    mutualInformation (ρ.tensorPowerBipartite n) =
      (n : ℝ) * mutualInformation ρ := by
  unfold mutualInformation
  rw [ρ.tensorPowerBipartite_marginalA n,
    ρ.tensorPowerBipartite_marginalB n]
  rw [State.vonNeumann_tensorPower,
    State.vonNeumann_tensorPower,
    show vonNeumann (ρ.tensorPowerBipartite n) =
      vonNeumann ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)) from rfl,
    State.vonNeumann_reindex,
    State.vonNeumann_tensorPower]
  ring

/-- PSD-domain Petz--Renyi divergence is invariant under simultaneous finite
basis relabeling in the source range `0 <= alpha <= 1`. -/
theorem petzRenyiPSD_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : State α) (e : α ≃ β)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) :
    (ρ.reindex e).petzRenyiPSD (σ.reindex e)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      ρ.petzRenyiPSD σ alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  unfold State.petzRenyiPSD
  have halpha_nonneg : 0 ≤ alphaR := le_of_lt halpha_pos
  have hone_sub_nonneg : 0 ≤ 1 - alphaR := sub_nonneg.mpr (le_of_lt halpha_lt_one)
  rw [State.reindex_matrix, State.reindex_matrix]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (Matrix.reindex e e ρ.matrix) alphaR *
        CFC.rpow (Matrix.reindex e e σ.matrix) (1 - alphaR)).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.matrix alphaR *
        CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [cMatrix_rpow_reindex_nonneg e ρ.matrix ρ.pos halpha_nonneg]
  rw [cMatrix_rpow_reindex_nonneg e σ.matrix σ.pos hone_sub_nonneg]
  change (1 / (alphaR - 1)) *
      log2 ((((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow ρ.matrix alphaR) *
        (Matrix.reindexAlgEquiv ℂ ℂ e)
          (CFC.rpow σ.matrix (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.matrix alphaR *
        CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
    (CFC.rpow ρ.matrix alphaR) (CFC.rpow σ.matrix (1 - alphaR))]
  change (1 / (alphaR - 1)) *
      log2 (((Matrix.reindex e e
        (CFC.rpow ρ.matrix alphaR *
          CFC.rpow σ.matrix (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.matrix alphaR *
        CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [cMatrix_trace_reindex e]

/-- The product-marginal Petz coefficient is strictly positive in the source
range `0 < alpha < 1`, because the product-marginal Nussbaum--Szkola model has
nonempty common support. -/
theorem petzRenyiCoefficient_productMarginal_pos
    (ρ : State (Prod a b)) {alphaR : ℝ}
    (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) :
    0 < ρ.petzRenyiCoefficient (ρ.marginalA.prod ρ.marginalB) alphaR := by
  classical
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel ρ
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_p_supportedBy_q ρ
  have hcommon :
      Nonempty M.commonSupport :=
    BinaryHypothesisTest.ClassicalBinaryModel.commonSupport_nonempty_of_p_supportedBy_q
      (M := M) hpq
  have hpart_pos : 0 < M.chernoffPartitionNNReal alphaR :=
    BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_pos_of_commonSupport_nonempty
      (M := M) hcommon alphaR
  have hpart :
      M.chernoffPartitionNNReal alphaR = M.petzChernoffCoefficient alphaR :=
    BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
      (M := M) halpha_pos halpha_lt_one
  have hcoeff :
      M.petzChernoffCoefficient alphaR =
        ρ.petzRenyiCoefficient (ρ.marginalA.prod ρ.marginalB) alphaR := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_eq
        ρ (le_of_lt halpha_pos) (le_of_lt halpha_lt_one)
  simpa [hpart, hcoeff] using hpart_pos

/-- PSD-domain Petz--Renyi divergence is additive on IID tensor powers when
the base coefficient is positive. -/
theorem petzRenyiPSD_tensorPower
    {α : Type u} [Fintype α] [DecidableEq α] (ρ σ : State α)
    {alphaR : ℝ} (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1)
    (hcoeff : 0 < ρ.petzRenyiCoefficient σ alphaR) (n : ℕ) :
    (ρ.tensorPower n).petzRenyiPSD (σ.tensorPower n)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (n : ℝ) * ρ.petzRenyiPSD σ alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  unfold State.petzRenyiPSD
  have halpha_nonneg : 0 ≤ alphaR := le_of_lt halpha_pos
  have halpha_le_one : alphaR ≤ 1 := le_of_lt halpha_lt_one
  have htrace_tensor :
      ((CFC.rpow (ρ.tensorPower n).matrix alphaR *
          CFC.rpow (σ.tensorPower n).matrix (1 - alphaR)).trace).re =
        ((ρ.petzRenyiCoefficient σ alphaR : ℝ) ^ n) := by
    have htrace :
        ((CFC.rpow (ρ.tensorPower n).matrix alphaR *
            CFC.rpow (σ.tensorPower n).matrix (1 - alphaR)).trace).re =
          (((ρ.tensorPower n).petzRenyiCoefficient (σ.tensorPower n) alphaR : ℝ)) := by
      have h := State.petzRenyiCoefficient_trace_eq
        (ρ.tensorPower n) (σ.tensorPower n) alphaR
      have hre := congrArg Complex.re h
      simpa using hre.symm
    have hcoeff_tensor :
        (((ρ.tensorPower n).petzRenyiCoefficient
            (σ.tensorPower n) alphaR : ℝ) =
          ((ρ.petzRenyiCoefficient σ alphaR : ℝ) ^ n)) := by
      exact_mod_cast State.petzRenyiCoefficient_tensorPower
        ρ σ halpha_nonneg halpha_le_one n
    rw [htrace, hcoeff_tensor]
  have htrace_base :
      ((CFC.rpow ρ.matrix alphaR *
          CFC.rpow σ.matrix (1 - alphaR)).trace).re =
        (ρ.petzRenyiCoefficient σ alphaR : ℝ) := by
    have h := State.petzRenyiCoefficient_trace_eq ρ σ alphaR
    have hre := congrArg Complex.re h
    simpa using hre.symm
  change (1 / (alphaR - 1)) *
      log2 ((CFC.rpow (ρ.tensorPower n).matrix alphaR *
        CFC.rpow (σ.tensorPower n).matrix (1 - alphaR)).trace).re =
    (n : ℝ) *
      ((1 / (alphaR - 1)) *
        log2 ((CFC.rpow ρ.matrix alphaR *
          CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [htrace_tensor, htrace_base]
  have hcoeff_real_pos : 0 < (ρ.petzRenyiCoefficient σ alphaR : ℝ) := by
    exact_mod_cast hcoeff
  rw [log2_pow_nat (ρ.petzRenyiCoefficient σ alphaR : ℝ) n]
  ring

/-- PSD-domain barred Petz--Renyi mutual information is additive on IID
bipartite tensor powers. -/
theorem barPetzRenyiMutualInformationPSD_tensorPowerBipartite
    (ρ : State (Prod a b)) {alphaR : ℝ}
    (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).barPetzRenyiMutualInformationPSD
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (n : ℝ) *
        ρ.barPetzRenyiMutualInformationPSD
          alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  have hcomp :
      (ρ.tensorPowerBipartite n).marginalA.prod
          (ρ.tensorPowerBipartite n).marginalB =
        (ρ.marginalA.prod ρ.marginalB).tensorPowerBipartite n := by
    calc
      (ρ.tensorPowerBipartite n).marginalA.prod
          (ρ.tensorPowerBipartite n).marginalB =
        (ρ.marginalA.tensorPower n).prod
          (ρ.marginalB.tensorPower n) := by
          rw [ρ.tensorPowerBipartite_marginalA n,
            ρ.tensorPowerBipartite_marginalB n]
      _ = (ρ.marginalA.prod ρ.marginalB).tensorPowerBipartite n :=
          (State.prod_tensorPowerBipartite ρ.marginalA ρ.marginalB n).symm
  unfold State.barPetzRenyiMutualInformationPSD
  calc
    (ρ.tensorPowerBipartite n).petzRenyiPSD
        ((ρ.tensorPowerBipartite n).marginalA.prod
          (ρ.tensorPowerBipartite n).marginalB)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (ρ.tensorPowerBipartite n).petzRenyiPSD
        ((ρ.marginalA.prod ρ.marginalB).tensorPowerBipartite n)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
        unfold State.petzRenyiPSD
        rw [congrArg State.matrix hcomp]
    _ =
      (n : ℝ) *
        ρ.petzRenyiPSD (ρ.marginalA.prod ρ.marginalB)
          alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
        change
          ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)).petzRenyiPSD
            (((ρ.marginalA.prod ρ.marginalB).tensorPower n).reindex
              (tensorPowerProdEquiv a b n))
            alphaR halpha_pos (ne_of_lt halpha_lt_one) =
          (n : ℝ) *
            ρ.petzRenyiPSD (ρ.marginalA.prod ρ.marginalB)
              alphaR halpha_pos (ne_of_lt halpha_lt_one)
        rw [State.petzRenyiPSD_reindex
          (ρ.tensorPower n)
          ((ρ.marginalA.prod ρ.marginalB).tensorPower n)
          (tensorPowerProdEquiv a b n)
          alphaR halpha_pos halpha_lt_one]
        exact State.petzRenyiPSD_tensorPower ρ
          (ρ.marginalA.prod ρ.marginalB)
          halpha_pos halpha_lt_one
          (State.petzRenyiCoefficient_productMarginal_pos
            ρ halpha_pos halpha_lt_one)
          n

end State

namespace EntanglementAssistedClassicalCode

variable {N : Channel a b} {n : ℕ}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Rate normalization for a nonzero `n`-use entanglement-assisted code. -/
theorem rate_eq_log_card_div (C : EntanglementAssistedClassicalCode N n M EA EB)
    (hn : n ≠ 0) :
    C.rate = log2 (Fintype.card M : ℝ) / (n : ℝ) := by
  unfold rate entanglementAssistedMessageRate
  simp [hn]

/-- If the message set has logarithmic size at least `n * R`, then the
normalized `n`-use code rate is at least `R`. -/
theorem rate_ge_of_mul_le_log_card
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    {R : ℝ} (hn_pos : 0 < n)
    (hlog : (n : ℝ) * R ≤ log2 (Fintype.card M : ℝ)) :
    R ≤ C.rate := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
  rw [C.rate_eq_log_card_div hn_ne]
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  exact (le_div_iff₀ hn_real_pos).mpr (by simpa [mul_comm] using hlog)

/-- If the message set has logarithmic size at most `n * B`, then the
normalized `n`-use code rate is at most `B`. -/
theorem rate_le_of_log_card_le_mul
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    {B : ℝ} (hn_pos : 0 < n)
    (hlog : log2 (Fintype.card M : ℝ) ≤ (n : ℝ) * B) :
    C.rate ≤ B := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
  rw [C.rate_eq_log_card_div hn_ne]
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  exact (div_le_iff₀ hn_real_pos).mpr (by simpa [mul_comm] using hlog)

/-- Interpret a one-shot code for the block channel `N^{⊗n}` as an `n`-use
code for `N`, dropping the terminal unit register of the one-fold tensor power. -/
def liftBlockOneShot
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB) :
    EntanglementAssistedClassicalCode N n M EA EB where
  sharedState := C.sharedState
  encoder m :=
    (C.encoder m).outputReindex (tensorPowerOneEquiv (QIT.TensorPower a n))
  decoder :=
    C.decoder.reindex
      (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB))

/-- Interpret an `n`-use code for `N` as a one-shot code for the block channel
`N^{⊗n}`, adding the terminal unit register of the one-fold tensor power.

This is the converse-direction block-code bridge used to lift one-shot upper
bounds to `n`-use asymptotic upper bounds. -/
def asBlockOneShot
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB where
  sharedState := C.sharedState
  encoder m :=
    (C.encoder m).outputReindex (tensorPowerOneEquiv (QIT.TensorPower a n)).symm
  decoder :=
    C.decoder.reindex
      (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)).symm

/-- The lifted `n`-use code has normalized rate at least `R` when the block
one-shot code has rate at least `n * R`. -/
theorem liftBlockOneShot_rate_ge_of_mul_le_rate
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    {R : ℝ} (hn_pos : 0 < n) (hR : (n : ℝ) * R ≤ C.rate) :
    R ≤ C.liftBlockOneShot.rate := by
  apply C.liftBlockOneShot.rate_ge_of_mul_le_log_card hn_pos
  simpa using hR

/-- Channel-input states of the lifted block code are just the block one-shot
input states with the one-fold tensor-power register removed. -/
theorem liftBlockOneShot_channelInputState
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (m : M) :
    C.liftBlockOneShot.channelInputState m =
      (C.channelInputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower a n)) (Equiv.refl EB)) := by
  apply State.ext
  rfl

private theorem unit_map_eq_idChannel_forAsymptotic :
    (Channel.unit : Channel PUnit PUnit).map = (Channel.idChannel PUnit).map := by
  ext X i j
  cases i
  cases j
  simp [Channel.unit, MatrixMap.unit, Channel.idChannel, MatrixMap.ofKraus]

/-- Applying a one-fold tensor-power channel and then dropping the terminal unit
register agrees with dropping the unit input register first and applying the
underlying channel. -/
theorem applyState_tensorPower_one_prod_id_reindex
    {q : Type u} {r : Type v} {s : Type x}
    [Fintype q] [DecidableEq q] [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (D : Channel q r) (ρ : State (Prod (QIT.TensorPower q 1) s)) :
    (D.prod (Channel.idChannel s)).applyState
        (ρ.reindex (Equiv.prodCongr (tensorPowerOneEquiv q) (Equiv.refl s))) =
      (((D.tensorPower 1).prod (Channel.idChannel s)).applyState ρ).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv r) (Equiv.refl s)) := by
  apply State.ext
  ext x y
  rcases x with ⟨xr, xs⟩
  rcases y with ⟨yr, ys⟩
  change
    MatrixMap.kron D.map (Channel.idChannel s).map
        (ρ.reindex (Equiv.prodCongr (tensorPowerOneEquiv q) (Equiv.refl s))).matrix
        (xr, xs) (yr, ys) =
      MatrixMap.kron (D.tensorPower 1).map (Channel.idChannel s).map
        ρ.matrix ((xr, PUnit.unit), xs) ((yr, PUnit.unit), ys)
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [Channel.tensorPower_succ, Channel.tensorPower_zero]
  change
    D.map
        (fun z z' =>
          (ρ.reindex (Equiv.prodCongr (tensorPowerOneEquiv q) (Equiv.refl s))).matrix
            (z, xs) (z', ys)) xr yr =
      MatrixMap.kron D.map (Channel.unit).map
        (fun z z' => ρ.matrix (z, xs) (z', ys))
        (xr, PUnit.unit) (yr, PUnit.unit)
  rw [unit_map_eq_idChannel_forAsymptotic]
  rw [MatrixMap.kron_idChannel_apply_slice]
  change
    D.map (fun z z' => ρ.matrix ((z, PUnit.unit), xs) ((z', PUnit.unit), ys))
        xr yr =
      D.map (fun z z' => ρ.matrix ((z, PUnit.unit), xs) ((z', PUnit.unit), ys))
        xr yr
  rfl

/-- Output states of the lifted block code are the block one-shot output states
with the one-fold tensor-power register removed. -/
theorem liftBlockOneShot_outputState
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (m : M) :
    C.liftBlockOneShot.outputState m =
      (C.outputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)) := by
  rw [EntanglementAssistedClassicalCode.outputState]
  rw [C.liftBlockOneShot_channelInputState m]
  exact applyState_tensorPower_one_prod_id_reindex (N.tensorPower n) (C.channelInputState m)

/-- Lifting a one-shot block code preserves each message success probability. -/
theorem liftBlockOneShot_successProbability
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (m : M) :
    C.liftBlockOneShot.successProbability m = C.successProbability m := by
  unfold successProbability
  rw [C.liftBlockOneShot_outputState m]
  exact POVM.prob_reindex_state C.decoder (C.outputState m)
    (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)) m

/-- Lifting a reliable one-shot block code gives a reliable `n`-use code. -/
theorem liftBlockOneShot_maxErrorAtMost
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    {ε : ℝ} (hC : C.maxErrorAtMost ε) :
    C.liftBlockOneShot.maxErrorAtMost ε := by
  intro m
  unfold error
  rw [C.liftBlockOneShot_successProbability m]
  exact hC m

/-- The block one-shot view has the same logarithmic rate as the message set. -/
@[simp]
theorem asBlockOneShot_rate
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    C.asBlockOneShot.rate = log2 (Fintype.card M : ℝ) :=
  C.asBlockOneShot.rate_one

/-- Channel-input states of the block one-shot view are just the `n`-use input
states with an added one-fold tensor-power unit register. -/
theorem asBlockOneShot_channelInputState
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) :
    C.asBlockOneShot.channelInputState m =
      (C.channelInputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower a n)) (Equiv.refl EB)).symm := by
  apply State.ext
  rfl

/-- Output states of the block one-shot view are the original `n`-use output
states with an added one-fold tensor-power unit register. -/
theorem asBlockOneShot_outputState
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) :
    C.asBlockOneShot.outputState m =
      (C.outputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)).symm := by
  let ein :=
    Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower a n)) (Equiv.refl EB)
  let eout :=
    Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)
  have h :=
    applyState_tensorPower_one_prod_id_reindex
      (N.tensorPower n) (C.asBlockOneShot.channelInputState m)
  rw [C.asBlockOneShot_channelInputState m] at h
  have hinput :
      (((C.channelInputState m).reindex ein.symm).reindex ein) =
        C.channelInputState m := by
    exact state_reindex_reindex_symm (C.channelInputState m) ein.symm
  rw [hinput] at h
  have hout :
      C.outputState m =
        (C.asBlockOneShot.outputState m).reindex eout := by
    simpa [EntanglementAssistedClassicalCode.outputState] using h
  change C.asBlockOneShot.outputState m = (C.outputState m).reindex eout.symm
  calc
    C.asBlockOneShot.outputState m =
        ((C.asBlockOneShot.outputState m).reindex eout).reindex eout.symm := by
      rw [state_reindex_reindex_symm]
    _ = (C.outputState m).reindex eout.symm := by
      rw [← hout]

/-- The block one-shot view preserves each message success probability. -/
theorem asBlockOneShot_successProbability
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) :
    C.asBlockOneShot.successProbability m = C.successProbability m := by
  unfold successProbability
  rw [C.asBlockOneShot_outputState m]
  exact (POVM.prob_reindex_state C.decoder (C.outputState m)
    (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)).symm
    m)

/-- Reinterpreting an `n`-use reliable code as a one-shot block-code preserves
the maximal error bound. -/
theorem asBlockOneShot_maxErrorAtMost
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    {ε : ℝ} (hC : C.maxErrorAtMost ε) :
    C.asBlockOneShot.maxErrorAtMost ε := by
  intro m
  unfold error
  rw [C.asBlockOneShot_successProbability m]
  exact hC m

end EntanglementAssistedClassicalCode

namespace Channel

variable (N : Channel a b)

/-- Any pure input-reference objective whose reference system contains an
input-copy reference is bounded by the optimized channel mutual information.

This is the ordinary mutual-information analogue of the hypothesis-testing
arbitrary-reference bridge, and formalizes the source step
`sup_{ρ_RA} I(R;B) = I(N)` when the reference is large enough
from Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1039-1043. -/
theorem entanglementAssistedMutualInformation_le_information_of_card_le
    [Nonempty a] {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) (hcard : Fintype.card a ≤ Fintype.card r) :
    N.entanglementAssistedMutualInformation ψ ≤
      N.entanglementAssistedInformation := by
  let φ : PureVector (Prod a a) := ψ.state.marginalB.canonicalPurification
  have hφ : φ.Purifies ψ.state.marginalB :=
    ψ.state.marginalB.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.marginalB :=
    ψ.purifies_marginalB_forHypothesisTestingDPI
  rcases PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.entanglementAssistedOutputState ψ =
        ((Channel.ofReferenceIsometry V).prod (Channel.idChannel b)).applyState
          (N.entanglementAssistedOutputState φ) := by
    rw [hV]
    simpa [Channel.entanglementAssistedOutputState, Channel.hypothesisTestingOutputState]
      using N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  unfold Channel.entanglementAssistedMutualInformation
  rw [hout]
  have hdpi :=
    QIT.mutualInformation_dataProcessing_local_channels_ge
      (N.entanglementAssistedOutputState φ)
      (Channel.ofReferenceIsometry V) (Channel.idChannel b)
  exact hdpi.trans (N.entanglementAssistedMutualInformation_le_information φ)

private theorem card_le_purified_reference
    {a₀ : Type u} {r : Type w} [Fintype a₀] [Fintype r] [Nonempty r] :
    Fintype.card a₀ ≤ Fintype.card (Prod (Prod r a₀) r) := by
  have hrpos : 0 < Fintype.card r := Fintype.card_pos_iff.mpr inferInstance
  have h1 : Fintype.card a₀ ≤ Fintype.card a₀ * Fintype.card r :=
    Nat.le_mul_of_pos_right (Fintype.card a₀) hrpos
  have h2 : Fintype.card a₀ * Fintype.card r ≤
      (Fintype.card a₀ * Fintype.card r) * Fintype.card r :=
    Nat.le_mul_of_pos_right (Fintype.card a₀ * Fintype.card r) hrpos
  calc
    Fintype.card a₀ ≤ Fintype.card a₀ * Fintype.card r := h1
    _ ≤ (Fintype.card a₀ * Fintype.card r) * Fintype.card r := h2
    _ = Fintype.card (Prod (Prod r a₀) r) := by
      simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

/-- Mixed input-reference output states are bounded by the optimized channel
mutual information.

The proof purifies the mixed input-reference state, traces out the extra
purifying reference after the channel use, and applies reference-side
data processing together with the arbitrary-reference pure-input bridge.
This follows Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1039-1043. -/
theorem mixedInputOutput_mutualInformation_le_information
    [Nonempty a] {r : Type w} [Fintype r] [DecidableEq r]
    (ρ : State (Prod r a)) :
    mutualInformation (((Channel.idChannel r).prod N).applyState ρ) ≤
      N.entanglementAssistedInformation := by
  haveI : Nonempty r := by
    rcases ρ.nonempty with ⟨ra⟩
    exact ⟨ra.1⟩
  let ψ : PureVector (Prod (Prod (Prod r a) r) a) :=
    ρ.purifiedInputForHypothesisTestingDPI
  let D : Channel (Prod (Prod r a) r) r :=
    Channel.traceOutAForHypothesisTestingDPI (Prod r a) r
  have hstate :
      (D.prod (Channel.idChannel b)).applyState (N.entanglementAssistedOutputState ψ) =
        ((Channel.idChannel r).prod N).applyState ρ := by
    calc
      (D.prod (Channel.idChannel b)).applyState (N.entanglementAssistedOutputState ψ) =
        (D.prod (Channel.idChannel b)).applyState
          (((Channel.idChannel (Prod (Prod r a) r)).prod N).applyState ψ.state) := rfl
      _ = ((Channel.idChannel r).prod N).applyState
          (((D.prod (Channel.idChannel a)).applyState ψ.state)) := by
          exact Channel.traceOutAForHypothesisTestingDPI_prod_id_applyState_id_prod
            (p := Prod r a) (r := r) N ψ.state
      _ = ((Channel.idChannel r).prod N).applyState ρ := by
          rw [State.traceOut_purifiedInputForHypothesisTestingDPI]
  rw [← hstate]
  have hdpi :=
    QIT.mutualInformation_dataProcessing_local_channels_ge
      (N.entanglementAssistedOutputState ψ) D (Channel.idChannel b)
  have hcard :
      Fintype.card a ≤ Fintype.card (Prod (Prod r a) r) :=
    card_le_purified_reference (a₀ := a) (r := r)
  exact hdpi.trans (N.entanglementAssistedMutualInformation_le_information_of_card_le ψ hcard)

/-- Product pure input for the entanglement-assisted objective of a product
channel, repartitioned from `(A₁ × A₁) × (A₂ × A₂)` to
`(A₁ × A₂) × (A₁ × A₂)`. -/
def entanglementAssistedProductInput
    {a₁ : Type u} {a₂ : Type w}
    [Fintype a₁] [DecidableEq a₁] [Fintype a₂] [DecidableEq a₂]
    (ψ : PureVector (Prod a₁ a₁)) (φ : PureVector (Prod a₂ a₂)) :
    PureVector (Prod (Prod a₁ a₂) (Prod a₁ a₂)) :=
  (ψ.prod φ).reindex
    (State.bipartiteProductEquiv (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂))

/-- Applying a product channel to a repartitioned product input yields the
repartitioned product of the two individual output states. -/
private theorem applyState_prod_reindex_entanglementAssistedProductInput
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ρ : State (Prod a₁ a₁)) (σ : State (Prod a₂ a₂)) :
    (((Channel.idChannel (Prod a₁ a₂)).prod (N₁.prod N₂)).applyState
        ((ρ.prod σ).reindex
          (State.bipartiteProductEquiv
            (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂)))) =
      ((((Channel.idChannel a₁).prod N₁).applyState ρ).prod
          (((Channel.idChannel a₂).prod N₂).applyState σ)).reindex
        (State.bipartiteProductEquiv
          (a1 := a₁) (b1 := b₁) (a2 := a₂) (b2 := b₂)) := by
  apply State.ext
  ext x y
  rcases x with ⟨xR, xB⟩
  rcases y with ⟨yR, yB⟩
  rcases xR with ⟨xR1, xR2⟩
  rcases xB with ⟨xB1, xB2⟩
  rcases yR with ⟨yR1, yR2⟩
  rcases yB with ⟨yB1, yB2⟩
  simp only [Channel.applyState, Channel.prod, State.reindex_matrix,
    State.prod_matrix_kronecker, Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' =>
          (Matrix.kronecker ρ.matrix σ.matrix).submatrix
            (State.bipartiteProductEquiv
              (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂)).symm
            (State.bipartiteProductEquiv
              (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂)).symm
            (((xR1, xR2), (xB1, xB2)).1, j)
            (((yR1, yR2), (yB1, yB2)).1, j')) =
        Matrix.kronecker
          (fun i i' => ρ.matrix (xR1, i) (yR1, i'))
          (fun k k' => σ.matrix (xR2, k) (yR2, k')) := by
    ext z z'
    rcases z with ⟨z1, z2⟩
    rcases z' with ⟨z1', z2'⟩
    simp [State.bipartiteProductEquiv, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [hslice]
  change MatrixMap.kron N₁.map N₂.map
      (Matrix.kronecker
        (fun i i' => ρ.matrix (xR1, i) (yR1, i'))
        (fun k k' => σ.matrix (xR2, k) (yR2, k')))
      (xB1, xB2) (yB1, yB2) = _
  rw [MatrixMap.kron_apply_kronecker]
  simp [State.bipartiteProductEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]

/-- Product-channel entanglement-assisted output states factor on product
inputs. This is the state-level additivity step in
Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1044-1058. -/
theorem entanglementAssistedOutputState_prod
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ψ : PureVector (Prod a₁ a₁)) (φ : PureVector (Prod a₂ a₂)) :
    (N₁.prod N₂).entanglementAssistedOutputState
        (entanglementAssistedProductInput ψ φ) =
      (N₁.entanglementAssistedOutputState ψ).bipartiteProduct
        (N₂.entanglementAssistedOutputState φ) := by
  unfold Channel.entanglementAssistedOutputState entanglementAssistedProductInput
  rw [PureVector.reindex_state, PureVector.prod_state]
  exact applyState_prod_reindex_entanglementAssistedProductInput
    N₁ N₂ ψ.state φ.state

/-- Product-channel mutual information is superadditive. -/
theorem entanglementAssistedInformation_prod_lower_bound
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂) :
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation ≤
      (N₁.prod N₂).entanglementAssistedInformation := by
  obtain ⟨ψ, hψ⟩ := N₁.exists_entanglementAssistedInformation_maximizer
  obtain ⟨φ, hφ⟩ := N₂.exists_entanglementAssistedInformation_maximizer
  have hcandidate :
      (N₁.prod N₂).entanglementAssistedMutualInformation
          (entanglementAssistedProductInput ψ φ) =
        N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
    unfold Channel.entanglementAssistedMutualInformation
    rw [Channel.entanglementAssistedOutputState_prod]
    rw [State.mutualInformation_bipartiteProduct]
    change N₁.entanglementAssistedMutualInformation ψ +
        N₂.entanglementAssistedMutualInformation φ =
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation
    rw [← hψ, ← hφ]
  calc
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation =
        (N₁.prod N₂).entanglementAssistedMutualInformation
          (entanglementAssistedProductInput ψ φ) := hcandidate.symm
    _ ≤ (N₁.prod N₂).entanglementAssistedInformation :=
        (N₁.prod N₂).entanglementAssistedMutualInformation_le_information
          (entanglementAssistedProductInput ψ φ)

/-- Pointwise upper bound for the product-channel entanglement-assisted
objective:
`I(R;B₁B₂)_{(N₁⊗N₂)(ψ)} ≤ I(N₁)+I(N₂)`.

This formalizes the chain-rule argument
`I(R;B₁B₂) = I(R;B₁)+I(RB₁;B₂)-I(B₁;B₂)` together with nonnegativity and
the mixed-input optimization bridge from Khatri--Wilde,
`Chapters/EA_capacity.tex`, lines 1078-1100. -/
theorem entanglementAssistedMutualInformation_prod_le_information_add
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ψ : PureVector (Prod (Prod a₁ a₂) (Prod a₁ a₂))) :
    (N₁.prod N₂).entanglementAssistedMutualInformation ψ ≤
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  let R := Prod a₁ a₂
  let ρout : State (Prod R (Prod b₁ b₂)) :=
    (N₁.prod N₂).entanglementAssistedOutputState ψ
  let ρleft : State (Prod (Prod R b₁) b₂) :=
    ρout.reindex (Equiv.prodAssoc R b₁ b₂).symm
  let τ₂ : State (Prod (Prod R b₁) a₂) :=
    ((((Channel.idChannel R).prod (N₁.prod (Channel.idChannel a₂))).applyState ψ.state).reindex
      (Equiv.prodAssoc R b₁ a₂).symm)
  let τ₁ : State (Prod R a₁) :=
    (ψ.state.reindex (Equiv.prodAssoc R a₁ a₂).symm).marginalAB
  have hρleft :
      ρleft = (((Channel.idChannel (Prod R b₁)).prod N₂).applyState τ₂) := by
    unfold ρleft ρout τ₂ R
    rw [Channel.entanglementAssistedOutputState]
    exact State.applyState_id_prod_prod_assoc_symm N₁ N₂ ψ.state
  have hterm₁ :
      mutualInformation ρleft.marginalAB ≤ N₁.entanglementAssistedInformation := by
    rw [hρleft]
    rw [State.marginalAB_eq_marginalA]
    rw [State.marginalA_applyState_id_prod]
    change mutualInformation τ₂.marginalAB ≤ N₁.entanglementAssistedInformation
    rw [State.partialProductOutput_marginalAB]
    exact N₁.mixedInputOutput_mutualInformation_le_information τ₁
  have hterm₂ :
      mutualInformation ρleft ≤ N₂.entanglementAssistedInformation := by
    rw [hρleft]
    exact N₂.mixedInputOutput_mutualInformation_le_information τ₂
  unfold Channel.entanglementAssistedMutualInformation
  change mutualInformation ρout ≤
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation
  calc
    mutualInformation ρout =
        mutualInformation (ρleft.reindex (Equiv.prodAssoc R b₁ b₂)) := by
          change mutualInformation ρout =
            mutualInformation ((ρout.reindex (Equiv.prodAssoc R b₁ b₂).symm).reindex
              (Equiv.prodAssoc R b₁ b₂))
          rw [state_reindex_symm_reindex]
    _ ≤ mutualInformation ρleft.marginalAB + mutualInformation ρleft :=
        State.mutualInformation_assoc_le ρleft
    _ ≤ N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation :=
        add_le_add hterm₁ hterm₂

/-- Product-channel mutual information is subadditive. -/
theorem entanglementAssistedInformation_prod_upper_bound
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂) :
    (N₁.prod N₂).entanglementAssistedInformation ≤
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  obtain ⟨ψ, hψ⟩ := (N₁.prod N₂).exists_entanglementAssistedInformation_maximizer
  calc
    (N₁.prod N₂).entanglementAssistedInformation =
        (N₁.prod N₂).entanglementAssistedMutualInformation ψ := hψ
    _ ≤ N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation :=
        entanglementAssistedMutualInformation_prod_le_information_add N₁ N₂ ψ

/-- Entanglement-assisted channel mutual information is additive under product
channels:
`I(N₁ ⊗ N₂) = I(N₁) + I(N₂)`.

This is the formal statement corresponding to Khatri--Wilde,
`Chapters/EA_capacity.tex`, lines 1023-1115. -/
theorem entanglementAssistedInformation_prod
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂) :
    (N₁.prod N₂).entanglementAssistedInformation =
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  exact le_antisymm
    (entanglementAssistedInformation_prod_upper_bound N₁ N₂)
    (entanglementAssistedInformation_prod_lower_bound N₁ N₂)

private theorem entanglementAssistedInformation_unit :
    (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1}).entanglementAssistedInformation = 0 := by
  obtain ⟨ψ, hψ⟩ :=
    (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1}).exists_entanglementAssistedInformation_maximizer
  rw [hψ]
  unfold Channel.entanglementAssistedMutualInformation
  exact State.mutualInformation_punit_punit_eq_zero _

/-- Tensor-power corollary of product-channel additivity:
`I(N^{⊗n}) = n I(N)`.

This is the additivity simplification used in
Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1118-1124. -/
theorem entanglementAssistedInformation_tensorPower_eq_mul
    [Nonempty a] (n : ℕ) :
    (N.tensorPower n).entanglementAssistedInformation =
      (n : ℝ) * N.entanglementAssistedInformation := by
  induction n with
  | zero =>
      rw [Channel.tensorPower_zero]
      calc
        (Channel.unit : Channel (QIT.TensorPower a 0) (QIT.TensorPower b 0)).entanglementAssistedInformation =
            0 := by
            exact entanglementAssistedInformation_unit
        _ = ((0 : ℕ) : ℝ) * N.entanglementAssistedInformation := by norm_num
  | succ n ih =>
      haveI : Nonempty (QIT.TensorPower a n) :=
        tensorPower_nonempty_of_nonempty (α := a) n
      rw [Channel.tensorPower_succ]
      calc
        (N.prod (N.tensorPower n)).entanglementAssistedInformation =
            N.entanglementAssistedInformation +
              (N.tensorPower n).entanglementAssistedInformation :=
            Channel.entanglementAssistedInformation_prod N (N.tensorPower n)
        _ = ((n + 1 : ℕ) : ℝ) * N.entanglementAssistedInformation := by
            rw [ih]
            rw [Nat.cast_add, Nat.cast_one]
            ring

/-- On a one-dimensional system, the density matrix of any state is the scalar
identity `1`. -/
private theorem punit_state_matrix_eq_one
    (ρ : State PUnit.{u + 1}) : ρ.matrix = 1 := by
  ext i j
  rcases i with ⟨⟩
  rcases j with ⟨⟩
  show ρ.matrix PUnit.unit PUnit.unit = (1 : CMatrix PUnit.{u + 1}) PUnit.unit PUnit.unit
  rw [Matrix.one_apply, if_pos rfl]
  -- Use that the trace equals the single matrix entry for a 1-dim system.
  have htrace : ∑ k : PUnit.{u + 1}, ρ.matrix k k = 1 := ρ.trace_eq_one
  simpa using htrace

/-- On a one-dimensional bipartite system, the density matrix of any state is
the scalar identity `1`. -/
private theorem punit_punit_state_matrix_eq_one
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) : ρ.matrix = 1 := by
  ext i j
  rcases i with ⟨⟨⟩, ⟨⟩⟩
  rcases j with ⟨⟨⟩, ⟨⟩⟩
  show ρ.matrix (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
      (1 : CMatrix (Prod PUnit.{u + 1} PUnit.{v + 1})) (PUnit.unit, PUnit.unit) (PUnit.unit,
        PUnit.unit)
  rw [Matrix.one_apply, if_pos rfl]
  have htrace :
      ∑ k : Prod PUnit.{u + 1} PUnit.{v + 1}, ρ.matrix k k = 1 := ρ.trace_eq_one
  have hsum :
      (∑ k : Prod PUnit.{u + 1} PUnit.{v + 1}, ρ.matrix k k) =
        ρ.matrix (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) := by
    rw [Finset.sum_eq_single (PUnit.unit, PUnit.unit)]
    · simp
    · intro hnot
      simp at hnot
  rw [hsum] at htrace
  exact htrace

/-- On a one-dimensional bipartite system, the high-`alpha` finite
sandwiched-Renyi PSD-reference divergence of any state from the identity
matrix reference is zero, since both arguments reduce to the scalar matrix
`1` and the trace-power collapses to `Tr[1] = 1`. -/
private theorem sandwichedRenyiPSDReferenceHighAlphaFinite_unit_eq_zero_punit_punit
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) (alpha : ℝ) (_halpha : 1 < alpha) :
    State.sandwichedRenyiPSDReferenceHighAlphaFinite ρ
      (1 : CMatrix (Prod PUnit.{u + 1} PUnit.{v + 1})) Matrix.PosSemidef.one alpha = 0 := by
  have hcard :
      Fintype.card (Prod PUnit.{u + 1} PUnit.{v + 1}) = 1 := by simp
  have hρmatrix : ρ.matrix = 1 := punit_punit_state_matrix_eq_one ρ
  have htrace :
      ((Matrix.trace ((ρ.matrix : CMatrix _) ^ alpha)).re) = 1 := by
    rw [hρmatrix, CFC.one_rpow, Matrix.trace_one]
    simp [hcard]
  simp [State.sandwichedRenyiPSDReferenceHighAlphaFinite,
    State.sandwichedRenyiReferenceInner, psdTracePower, log2, CFC.one_rpow, hρmatrix]

/-- On a one-dimensional bipartite system, every state has zero sandwiched-Renyi
mutual information for `alpha > 1`: the infimum over side-information states is
squeezed below by candidate nonnegativity and above by the self-product
candidate `D~_alpha(rho || rho_A tensor rho_B) = D~_alpha(1 || 1) = 0`. -/
private theorem sandwichedRenyiMutualInformationE_punit_punit_eq_zero
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) {alpha : ℝ} (halpha : 1 < alpha) :
    ρ.sandwichedRenyiMutualInformationE alpha = 0 := by
  refine le_antisymm ?_ ?_
  · -- Upper bound: Ĩ_α(ρ) ≤ D̃_α(ρ ∥ ρ_A ⊗ ρ_B) = 0.
    have hA_matrix : ρ.marginalA.matrix = 1 := punit_state_matrix_eq_one ρ.marginalA
    have hσB_matrix : ρ.marginalB.matrix = 1 := punit_state_matrix_eq_one ρ.marginalB
    have hRef_matrix :
        (ρ.marginalA.prod ρ.marginalB).matrix =
          (1 : CMatrix (Prod PUnit.{u + 1} PUnit.{v + 1})) := by
      rw [State.prod]
      simp only [hA_matrix, hσB_matrix]
      simp [Matrix.kronecker]
    have hSupports :
        Matrix.Supports ρ.matrix (ρ.marginalA.prod ρ.marginalB).matrix := by
      rw [hRef_matrix]
      exact Matrix.Supports.of_right_posDef ρ.matrix _ Matrix.PosDef.one
    have hfinite :
        State.sandwichedRenyiPSDReferenceHighAlphaFinite ρ
          (ρ.marginalA.prod ρ.marginalB).matrix
          (ρ.marginalA.prod ρ.marginalB).pos alpha = 0 := by
      simpa [hRef_matrix] using
        sandwichedRenyiPSDReferenceHighAlphaFinite_unit_eq_zero_punit_punit
          ρ alpha halpha
    have hcandidate :
        ρ.sandwichedRenyiMutualInformationCandidateE ρ.marginalB alpha = 0 := by
      rw [State.sandwichedRenyiMutualInformationCandidateE_eq,
        State.sandwichedRenyiPSDReferenceE, if_neg (not_lt_of_ge (le_of_lt halpha)),
        State.sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports ρ
          (ρ.marginalA.prod ρ.marginalB).pos alpha hSupports]
      rw [hfinite]
      simp
    calc ρ.sandwichedRenyiMutualInformationE alpha
          ≤ ρ.sandwichedRenyiMutualInformationCandidateE ρ.marginalB alpha :=
        State.sandwichedRenyiMutualInformationE_le_candidate ρ ρ.marginalB alpha
      _ = 0 := hcandidate
  · -- Lower bound: Ĩ_α(ρ) ≥ 0 since every candidate is nonneg.
    rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
    have hnonempty :
        (ρ.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
      haveI : Nonempty PUnit.{v + 1} := ⟨PUnit.unit⟩
      exact State.sandwichedRenyiMutualInformationEValueSet_nonempty ρ alpha
    refine le_csInf hnonempty ?_
    intro _ ⟨σB, hσB⟩
    rw [← hσB]
    exact State.sandwichedRenyiMutualInformationCandidateE_nonneg ρ σB halpha

/-- The sandwiched-Renyi mutual information of the unit channel is zero.

Mirrors the Petz (von Neumann) base `entanglementAssistedInformation_unit`,
using `sandwichedRenyiMutualInformationE_punit_punit_eq_zero` in place of
`State.mutualInformation_punit_punit_eq_zero`. -/
private theorem sandwichedRenyiMutualInformationE_unit
    {alpha : ℝ} (halpha : 1 < alpha) :
    (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1}).sandwichedRenyiMutualInformationE
      alpha = 0 := by
  let unitChan := (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1})
  have hvalue :
      ∀ psi : PureVector (Prod PUnit.{u + 1} PUnit.{u + 1}),
        unitChan.inputSandwichedRenyiMutualInformationE psi alpha = 0 := by
    intro psi
    rw [Channel.inputSandwichedRenyiMutualInformationE_eq]
    exact sandwichedRenyiMutualInformationE_punit_punit_eq_zero _ halpha
  have hnonempty : (unitChan.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
    haveI : Nonempty PUnit.{u + 1} := ⟨PUnit.unit⟩
    exact unitChan.sandwichedRenyiMutualInformationEValueSet_nonempty alpha
  have hbddAbove :
      BddAbove (unitChan.sandwichedRenyiMutualInformationEValueSet alpha) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨psi, rfl⟩
    show unitChan.inputSandwichedRenyiMutualInformationE psi alpha ≤ 0
    rw [hvalue psi]
  rw [Channel.sandwichedRenyiMutualInformationE_eq_sSup]
  refine le_antisymm ?_ ?_
  · apply csSup_le hnonempty
    rintro _ ⟨psi, rfl⟩
    show unitChan.inputSandwichedRenyiMutualInformationE psi alpha ≤ 0
    rw [hvalue psi]
  · have hbasis : unitChan.inputSandwichedRenyiMutualInformationE
        PureVector.basisPureVector alpha = 0 := hvalue _
    exact le_csSup hbddAbove ⟨PureVector.basisPureVector, hbasis⟩

/-- Tensor-power scaling of the channel sandwiched-Renyi mutual information:
`Ĩ_α(N^{⊗n}) = n · Ĩ_α(N)`.

This mirrors the Petz (von Neumann) tensor-power additivity
`Channel.entanglementAssistedInformation_tensorPower_eq_mul`, with the
unconditional two-channel sandwiched additivity
`Channel.sandwichedRenyiMutualInformationE_prod_eq_add` substituted for
`Channel.entanglementAssistedInformation_prod`.  Source:
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1220-1277]. -/
theorem sandwichedRenyiMutualInformationE_tensorPower_eq_n_mul
    [Nonempty a] [Nonempty b] {alpha : ℝ} (halpha : 1 < alpha) (n : ℕ) :
    (N.tensorPower n).sandwichedRenyiMutualInformationE alpha =
      (n : ℝ) * N.sandwichedRenyiMutualInformationE alpha := by
  induction n with
  | zero =>
      rw [Channel.tensorPower_zero]
      trans 0
      · exact sandwichedRenyiMutualInformationE_unit halpha
      · simp
  | succ n ih =>
      haveI : Nonempty (QIT.TensorPower a n) :=
        tensorPower_nonempty_of_nonempty (α := a) n
      haveI : Nonempty (QIT.TensorPower b n) :=
        tensorPower_nonempty_of_nonempty (α := b) n
      have hsplit : N.tensorPower (n + 1) = N.prod (N.tensorPower n) := by
        rw [Channel.tensorPower_succ]
      have hprod : (N.prod (N.tensorPower n)).sandwichedRenyiMutualInformationE alpha =
          N.sandwichedRenyiMutualInformationE alpha +
            (N.tensorPower n).sandwichedRenyiMutualInformationE alpha :=
        Channel.sandwichedRenyiMutualInformationE_prod_eq_add N (N.tensorPower n) halpha
      rw [hsplit]
      calc
        (N.prod (N.tensorPower n)).sandwichedRenyiMutualInformationE alpha =
            N.sandwichedRenyiMutualInformationE alpha +
              (N.tensorPower n).sandwichedRenyiMutualInformationE alpha := hprod
        _ = ((n + 1 : ℕ) : ℝ) * N.sandwichedRenyiMutualInformationE alpha := by
            rw [ih]
            -- The EReal arithmetic is most robustly expressed as natural
            -- repeated addition; `EReal.nsmul_eq_mul` bridges it to finite
            -- scalar multiplication by the blocklength.
            let X := N.sandwichedRenyiMutualInformationE alpha
            change X + (((n : ℝ) : EReal) * X) =
              ((((n + 1 : ℕ) : ℝ) : EReal) * X)
            rw [EReal.coe_coe_eq_natCast n, EReal.coe_coe_eq_natCast (n + 1)]
            rw [← EReal.nsmul_eq_mul n X, ← EReal.nsmul_eq_mul (n + 1) X]
            rw [succ_nsmul]
            rw [add_comm]

namespace OneShotNonempty

/-- The unique-outcome POVM, used only to show one-shot code candidate sets are
nonempty. -/
def unitPOVM (q : Type*) [Fintype q] [DecidableEq q] : POVM PUnit q where
  effects _ := 1
  pos _ := Matrix.PosSemidef.one
  sum_eq_one := by
    ext i j
    simp

end OneShotNonempty

/-- A one-message one-shot code used only as a nonemptiness witness for the
one-shot operational supremum. -/
def trivialOneShotEntanglementAssistedCode [Nonempty a] :
    EntanglementAssistedClassicalCode N 1 PUnit PUnit PUnit where
  sharedState := State.unit.prod State.unit
  encoder _ :=
    Channel.prepare (fun _ : PUnit =>
      (PureVector.basisPureVector : PureVector (QIT.TensorPower a 1)).state)
  decoder := OneShotNonempty.unitPOVM (Prod (QIT.TensorPower b 1) PUnit)

theorem trivialOneShotEntanglementAssistedCode_maxErrorAtMost
    [Nonempty a] {ε : ℝ} (hε : 0 ≤ ε) :
    (N.trivialOneShotEntanglementAssistedCode).maxErrorAtMost ε := by
  intro m
  cases m
  unfold EntanglementAssistedClassicalCode.error
    EntanglementAssistedClassicalCode.successProbability
  have hsum :=
    POVM.sum_prob (N.trivialOneShotEntanglementAssistedCode.decoder)
      (N.trivialOneShotEntanglementAssistedCode.outputState PUnit.unit)
  have hprob :
      ((N.trivialOneShotEntanglementAssistedCode.decoder.prob
        (N.trivialOneShotEntanglementAssistedCode.outputState PUnit.unit)
        PUnit.unit) : ℝ) = 1 := by
    have hreal := congrArg (fun x : ℝ≥0 => (x : ℝ)) hsum
    simpa using hreal
  rw [hprob]
  linarith

theorem oneShotEntanglementAssistedClassicalCapacityE_candidateSet_nonempty
    [Nonempty a] {ε : ℝ} (hε : 0 ≤ ε) :
    {R : EReal |
      ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
          ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
            ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
              C.maxErrorAtMost ε ∧ R = (C.rate : EReal)}.Nonempty := by
  refine ⟨((N.trivialOneShotEntanglementAssistedCode).rate : EReal), ?_⟩
  exact ⟨PUnit, inferInstance, inferInstance, inferInstance,
    PUnit, inferInstance, inferInstance,
    PUnit, inferInstance, inferInstance,
    N.trivialOneShotEntanglementAssistedCode,
    N.trivialOneShotEntanglementAssistedCode_maxErrorAtMost hε, rfl⟩

/-- Extract a concrete one-shot entanglement-assisted code from any strict
lower bound below the extended-real one-shot capacity. -/
theorem exists_oneShotCode_rate_gt_of_lt_oneShotCapacityE
    [Nonempty a] {ε lower : ℝ} (hε : 0 ≤ ε)
    (hlower : (lower : EReal) < N.oneShotEntanglementAssistedClassicalCapacityE ε) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
            C.maxErrorAtMost ε ∧ lower < C.rate := by
  unfold oneShotEntanglementAssistedClassicalCapacityE at hlower
  obtain ⟨value, hvalue_mem, hlt⟩ :=
    exists_lt_of_lt_csSup
      (N.oneShotEntanglementAssistedClassicalCapacityE_candidateSet_nonempty hε)
      hlower
  rcases hvalue_mem with
    ⟨M, hMfin, hMdec, hMnonempty,
      EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hCerr, rfl⟩
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    C, hCerr, EReal.coe_lt_coe_iff.mp hlt⟩

/-- The single-letter channel mutual information is superadditive under
memoryless tensor powers in the direction needed for achievability:
`I(N^{⊗n}) ≥ n I(N)`. -/
theorem entanglementAssistedInformation_tensorPower_lower_bound
    [Nonempty a] (n : ℕ) :
    (n : ℝ) * N.entanglementAssistedInformation ≤
      (N.tensorPower n).entanglementAssistedInformation := by
  obtain ⟨ψ, hψ⟩ := N.exists_entanglementAssistedInformation_maximizer
  have hcandidate :
      (N.tensorPower n).entanglementAssistedMutualInformation
          (ψ.tensorPowerBipartite n) =
        (n : ℝ) * N.entanglementAssistedInformation := by
    rw [hψ]
    unfold Channel.entanglementAssistedMutualInformation
    rw [← Channel.hypothesisTestingOutputState_eq_entanglementAssistedOutputState
      (N.tensorPower n) (ψ.tensorPowerBipartite n)]
    rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
    rw [Channel.hypothesisTestingOutputState_eq_entanglementAssistedOutputState]
    exact State.mutualInformation_tensorPowerBipartite
      (N.entanglementAssistedOutputState ψ) n
  calc
    (n : ℝ) * N.entanglementAssistedInformation =
        (N.tensorPower n).entanglementAssistedMutualInformation
          (ψ.tensorPowerBipartite n) := hcandidate.symm
    _ ≤ (N.tensorPower n).entanglementAssistedInformation :=
        (N.tensorPower n).entanglementAssistedMutualInformation_le_information
          (ψ.tensorPowerBipartite n)

/-- Fixed-input PSD barred Petz--Renyi mutual information is additive under
memoryless tensor powers. -/
theorem inputBarPetzRenyiMutualInformationPSD_tensorPowerBipartite
    (ψ : PureVector (Prod a a)) (n : ℕ) (alpha : PetzRenyiAlpha) :
    (N.tensorPower n).inputBarPetzRenyiMutualInformationPSD
        (ψ.tensorPowerBipartite n)
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) =
      (n : ℝ) *
        N.inputBarPetzRenyiMutualInformationPSD
          ψ alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := by
  unfold Channel.inputBarPetzRenyiMutualInformationPSD
  rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
  exact State.barPetzRenyiMutualInformationPSD_tensorPowerBipartite
    (N.hypothesisTestingOutputState ψ) alpha.2.1 alpha.2.2 n

/-- The PSD barred Petz--Renyi channel mutual information is superadditive
under tensor powers in the direction needed by the asymptotic achievability
proof. -/
theorem barPetzRenyiMutualInformationPSD_tensorPower_lower_bound
    [Nonempty a] {n : ℕ} (hn : 0 < n) (alpha : PetzRenyiAlpha) :
    (n : ℝ) *
        N.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      (N.tensorPower n).barPetzRenyiMutualInformationPSD
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := by
  classical
  rw [N.barPetzRenyiMutualInformationPSD_eq_sSup,
    (N.tensorPower n).barPetzRenyiMutualInformationPSD_eq_sSup]
  let S := N.barPetzRenyiMutualInformationPSDValueSet
    alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
  let T := (N.tensorPower n).barPetzRenyiMutualInformationPSDValueSet
    alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
  have hne : S.Nonempty := by
    let ψ0 : PureVector (Prod a a) := PureVector.basisPureVector
    refine ⟨N.inputBarPetzRenyiMutualInformationPSD
      ψ0 alpha.1 alpha.2.1 (ne_of_lt alpha.2.2), ?_⟩
    exact ⟨ψ0, rfl⟩
  have hbddTensor : BddAbove T :=
    (N.tensorPower n).barPetzRenyiMutualInformationPSDValueSet_bddAbove alpha
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hsSup :
      sSup S ≤ sSup T / (n : ℝ) := by
    refine csSup_le hne ?_
    intro x hx
    rcases hx with ⟨ψ, rfl⟩
    have hmemT :
        (n : ℝ) *
            N.inputBarPetzRenyiMutualInformationPSD
              ψ alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ∈ T := by
      refine ⟨ψ.tensorPowerBipartite n, ?_⟩
      exact (N.inputBarPetzRenyiMutualInformationPSD_tensorPowerBipartite
        ψ n alpha).symm
    have hleT :
        (n : ℝ) *
            N.inputBarPetzRenyiMutualInformationPSD
              ψ alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤ sSup T :=
      le_csSup hbddTensor hmemT
    exact (le_div_iff₀ hnR).mpr (by simpa [mul_comm] using hleT)
  calc
    (n : ℝ) * sSup S ≤ (n : ℝ) * (sSup T / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsSup (le_of_lt hnR)
    _ = sSup T := by
      field_simp [ne_of_gt hnR]

/-- Source-shaped `n`-use lower-bound witness used for the asymptotic
achievability passage.

For a fixed blocklength `n`, the witness packages a reliable `n`-use code whose
rate is lower-bounded by a supplied expression.  The one-shot lower-bound proof
constructs these witnesses for block channels; this structure is the
operational handoff to the asymptotic achievability statement. -/
structure EntanglementAssistedNUseLowerBoundWitness
    (n : ℕ) (ε lowerBound : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type u) [Fintype EA] [DecidableEq EA]
    (EB : Type u) [Fintype EB] [DecidableEq EB] where
  code : EntanglementAssistedClassicalCode N n M EA EB
  maxError_le : code.maxErrorAtMost ε
  lowerBound_le_rate : lowerBound ≤ code.rate

/-- A reliable one-shot code for the block channel `N^{⊗n}` gives the
corresponding `n`-use lower-bound witness for `N`, with rate divided by `n`. -/
theorem nUseLowerBoundWitness_of_blockOneShotCode
    {n : ℕ} {ε lowerBound : ℝ}
    {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
    {EA : Type u} [Fintype EA] [DecidableEq EA]
    {EB : Type u} [Fintype EB] [DecidableEq EB]
    (hn_pos : 0 < n)
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (hCerr : C.maxErrorAtMost ε)
    (hCrate : (n : ℝ) * lowerBound ≤ C.rate) :
    Nonempty (N.EntanglementAssistedNUseLowerBoundWitness n ε lowerBound M EA EB) := by
  refine ⟨EntanglementAssistedNUseLowerBoundWitness.mk
    C.liftBlockOneShot
    (C.liftBlockOneShot_maxErrorAtMost hCerr)
    ?_⟩
  exact C.liftBlockOneShot_rate_ge_of_mul_le_rate hn_pos hCrate

/-- A lower-bound witness at blocklength `n` contributes an explicit reliable
`n`-use code to the operational achievability definition. -/
theorem exists_code_of_nUseLowerBoundWitness
    {n : ℕ} {ε lowerBound : ℝ}
    {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
    {EA : Type u} [Fintype EA] [DecidableEq EA]
    {EB : Type u} [Fintype EB] [DecidableEq EB]
    (W : N.EntanglementAssistedNUseLowerBoundWitness n ε lowerBound M EA EB) :
    ∃ (M' : Type u), ∃ (_ : Fintype M'), ∃ (_ : DecidableEq M'), ∃ (_ : Nonempty M'),
      ∃ (EA' : Type u), ∃ (_ : Fintype EA'), ∃ (_ : DecidableEq EA'),
        ∃ (EB' : Type u), ∃ (_ : Fintype EB'), ∃ (_ : DecidableEq EB'),
          ∃ C : EntanglementAssistedClassicalCode N n M' EA' EB',
            C.rate ≥ lowerBound ∧ C.maxErrorAtMost ε := by
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    W.code, W.lowerBound_le_rate, W.maxError_le⟩

/-- Asymptotic achievability from a family of `n`-use lower-bound witnesses.

This is the rate-normalization layer for the Khatri--Wilde asymptotic lower
bound: if, after any slack `δ`, sufficiently large blocklengths have reliable
codes with rate at least `R - δ`, then `R` is an operationally achievable
entanglement-assisted classical communication rate. -/
theorem entanglementAssisted_achievable_of_nUseLowerBoundWitness
    (R : ℝ)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
            ∃ (_ : Nonempty M),
              ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
                ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                  Nonempty (N.EntanglementAssistedNUseLowerBoundWitness
                    n ε (R - δ) M EA EB)) :
    N.IsAchievableEntanglementAssistedClassicalRate R := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, ⟨W⟩⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  exact N.exists_code_of_nUseLowerBoundWitness W

set_option maxHeartbeats 2000000

/-- Khatri--Wilde asymptotic lower bound: the channel mutual information
`I(N)` is an operationally achievable entanglement-assisted classical rate.

This theorem is the source-shaped independent lower-bound route: it combines
the one-shot PSD Petz--Renyi lower bound, tensor-power superadditivity of the
barred PSD Petz channel quantity, the `alpha -> 1^-` limit to `I(N)`, and the
block-channel lifting lemma above.  It does not use the sandwiched-Renyi DPI
or strong-converse route. -/
theorem entanglementAssistedInformation_isAchievable_of_oneShotPetzLowerBound
    [Nonempty a] :
    N.IsAchievableEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation := by
  refine N.entanglementAssisted_achievable_of_nUseLowerBoundWitness
    N.entanglementAssistedInformation ?_
  intro δ hδ ε hε
  let η : ℝ := ε / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_lt : η < ε := by
    dsimp [η]
    linarith
  have hhalfδ : 0 < δ / 2 := by positivity
  have hlim :=
    N.barPetzRenyiMutualInformationPSD_tendsto_entanglementAssistedInformation_left
  have hα_eventually :
      ∀ᶠ alpha in PetzRenyiAlpha.leftToOne,
        N.entanglementAssistedInformation - δ / 2 <
          N.barPetzRenyiMutualInformationPSD
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := by
    exact (tendsto_order.mp hlim).1
      (N.entanglementAssistedInformation - δ / 2) (by linarith)
  haveI : Filter.NeBot PetzRenyiAlpha.leftToOne := PetzRenyiAlpha.leftToOne_neBot
  obtain ⟨alpha, hα_lower⟩ := hα_eventually.exists
  let penalty : ℝ :=
    alpha.1 / (1 - alpha.1) * log2 (1 / (ε - η)) +
      log2 (4 * ε / η ^ 2)
  have hpenalty_tendsto :
      Tendsto (fun n : ℕ => penalty / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpenalty_eventually :
      ∀ᶠ n : ℕ in atTop, penalty / (n : ℝ) < δ / 2 := by
    exact hpenalty_tendsto.eventually (eventually_lt_nhds hhalfδ)
  obtain ⟨Npen, hNpen⟩ := Filter.eventually_atTop.mp hpenalty_eventually
  refine ⟨max 1 Npen, ?_⟩
  intro n hn
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_left 1 Npen) hn)
  have hn_pen : n ≥ Npen :=
    le_trans (Nat.le_max_right 1 Npen) hn
  have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hpen_div : penalty / (n : ℝ) < δ / 2 := hNpen n hn_pen
  have hpen_lt : penalty < (n : ℝ) * (δ / 2) := by
    have := (div_lt_iff₀ hnR_pos).mp hpen_div
    simpa [mul_comm, mul_left_comm] using this
  let blockN : Channel (QIT.TensorPower a n) (QIT.TensorPower b n) := N.tensorPower n
  let blockPetz : ℝ :=
    blockN.barPetzRenyiMutualInformationPSD
      alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
  have hsingle_scaled :
      (n : ℝ) * (N.entanglementAssistedInformation - δ / 2) <
        (n : ℝ) *
          N.barPetzRenyiMutualInformationPSD
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) :=
    mul_lt_mul_of_pos_left hα_lower hnR_pos
  have htensor :
      (n : ℝ) *
          N.barPetzRenyiMutualInformationPSD
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
        blockPetz := by
    dsimp [blockPetz, blockN]
    exact N.barPetzRenyiMutualInformationPSD_tensorPower_lower_bound
      hn_pos alpha
  have hblock_gt :
      (n : ℝ) * (N.entanglementAssistedInformation - δ / 2) <
        blockPetz :=
    lt_of_lt_of_le hsingle_scaled htensor
  let lowerReal : ℝ := (n : ℝ) * (N.entanglementAssistedInformation - δ)
  let oneShotLower : ℝ :=
    blockPetz -
      alpha.1 / (1 - alpha.1) * log2 (1 / (ε - η)) -
      log2 (4 * ε / η ^ 2)
  have honeShotLower_gt : lowerReal < oneShotLower := by
    dsimp [lowerReal, oneShotLower, penalty]
    linarith
  have honeShotLower_le_capacity :
      (oneShotLower : EReal) ≤
        blockN.oneShotEntanglementAssistedClassicalCapacityE ε := by
    change
      ((blockN.barPetzRenyiMutualInformationPSD
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) -
          alpha.1 / (1 - alpha.1) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
        blockN.oneShotEntanglementAssistedClassicalCapacityE ε
    exact @Channel.oneShotEntanglementAssistedClassicalCapacityE_petzPSDLowerBound
      (QIT.TensorPower a n)
      (QIT.tensorPowerFintype (a := a) n)
      (QIT.tensorPowerDecidableEq (a := a) n)
      (QIT.TensorPower b n)
      (QIT.tensorPowerFintype (a := b) n)
      (QIT.tensorPowerDecidableEq (a := b) n)
      blockN (TensorPower.nonempty (a := a) n)
      ε η alpha.1 hε hη_pos hη_lt alpha.2.1 alpha.2.2
  have hlower_lt_capacity :
      (lowerReal : EReal) <
        blockN.oneShotEntanglementAssistedClassicalCapacityE ε :=
    (EReal.coe_lt_coe_iff.mpr honeShotLower_gt).trans_le honeShotLower_le_capacity
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hCerr, hCrate_gt⟩ :=
    blockN.exists_oneShotCode_rate_gt_of_lt_oneShotCapacityE
      (le_of_lt hε) hlower_lt_capacity
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  refine ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance, ?_⟩
  let C' : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB := by
    simpa [blockN] using C
  have hCerr' : C'.maxErrorAtMost ε := by
    dsimp [C']
    simpa [blockN] using hCerr
  have hCrate_gt' : lowerReal < C'.rate := by
    dsimp [C']
    simpa [blockN] using hCrate_gt
  exact N.nUseLowerBoundWitness_of_blockOneShotCode
    hn_pos C' hCerr' (le_of_lt (by simpa [lowerReal] using hCrate_gt'))

set_option maxHeartbeats 200000

/-- Converse witness family from eventual `n`-use log-cardinality upper bounds.

This is the rate-normalization layer for the Khatri--Wilde asymptotic upper
bound and strong-converse route: once the one-shot/n-use converse estimates
show that every sufficiently long reliable protocol has
`log₂ |M| ≤ n * (I(N) + η)`, this theorem packages the result in the standard
`EntanglementAssistedConverseWitnessFamily` interface. -/
theorem entanglementAssisted_converseWitnessFamily_of_logCardUpperBounds
    (h :
      ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
            ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
              ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
                ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                  C.maxErrorAtMost ε →
                    log2 (Fintype.card M : ℝ) ≤
                      (n : ℝ) * (N.entanglementAssistedInformation + η)) :
    EntanglementAssistedConverseWitnessFamily N where
  rate_le := by
    intro η hη ε hε
    obtain ⟨N0, hN0⟩ := h η hη ε hε
    refine ⟨max 1 N0, ?_⟩
    intro n hn M _hMfin _hMdec _hMnonempty EA _hEAfin _hEAdec EB _hEBfin _hEBdec C hC
    have hn_pos : 0 < n :=
      lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_left 1 N0) hn)
    have hnN0 : n ≥ N0 :=
      le_trans (Nat.le_max_right 1 N0) hn
    exact C.rate_le_of_log_card_le_mul hn_pos (hN0 n hnN0 M EA EB C hC)

/-- Source-consistent converse witness family from eventual `n`-use
log-cardinality upper bounds.

This is the same rate-normalization layer as
`entanglementAssisted_converseWitnessFamily_of_logCardUpperBounds`, but with
the error range used by the Khatri--Wilde one-shot upper bounds:
`ε ∈ [0, 1)`.  The output is a strict rate estimate, matching the operational
strong-converse interface. -/
theorem entanglementAssisted_sourceConverseWitnessFamily_of_logCardUpperBounds
    (h :
      ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
            ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
              ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
                ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                  C.maxErrorAtMost ε →
                    log2 (Fintype.card M : ℝ) ≤
                      (n : ℝ) * (N.entanglementAssistedInformation + η)) :
    EntanglementAssistedSourceConverseWitnessFamily N where
  rate_lt := by
    intro η hη ε hε_nonneg hε_lt_one
    have hhalf : 0 < η / 2 := half_pos hη
    obtain ⟨N0, hN0⟩ := h (η / 2) hhalf ε hε_nonneg hε_lt_one
    refine ⟨max 1 N0, ?_⟩
    intro n hn M _hMfin _hMdec _hMnonempty EA _hEAfin _hEAdec EB _hEBfin _hEBdec C hC
    have hn_pos : 0 < n :=
      lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_left 1 N0) hn)
    have hnN0 : n ≥ N0 :=
      le_trans (Nat.le_max_right 1 N0) hn
    have hrate_le :
        C.rate ≤ N.entanglementAssistedInformation + η / 2 :=
      C.rate_le_of_log_card_le_mul hn_pos (hN0 n hnN0 M EA EB C hC)
    have hstrict :
        N.entanglementAssistedInformation + η / 2 <
          N.entanglementAssistedInformation + η := by
      linarith
    exact lt_of_le_of_lt hrate_le hstrict

end Channel

end

end QIT
