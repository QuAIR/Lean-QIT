/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.FlaggedInstrument
public import QIT.HigherOrder.Comb.MemoryReadout
public import QIT.HigherOrder.Comb.ReadoutAction
public import QIT.HigherOrder.Comb.Completion

/-!
# Physical realization of finite superinstruments

The source construction adjoins a classical outcome to the final output,
realizes the resulting deterministic comb, and measures that outcome register
[Chiribella2009Networks, comblong-pub.tex:1125-1133], whose construction is
at proof lines 1202-1216. Here the register is
regrouped into the terminal memory, so every ordinary quantum input and output
wire keeps its original type. The final coordinate projective measurement
preserves the quantum output. Its carrier is precisely the outcome type;
the residual unmeasured environment has an independent finite dimension.

The branch Choi operators and the physical alternating connections agree with
the source link product, including joint inputs with independent boundary
ancillas [Chiribella2009Networks, comblong-pub.tex:3302-3314]. Completing a
probabilistic comb by its positive complement gives its realization.
This is the completion argument at lines 3280-3288, derived from
[Chiribella2009Networks, comblong-pub.tex:1425-1433] and
[Chiribella2009Networks, comblong-pub.tex:3266-3268]. No support inverse,
strict positivity, scalar boundary, or inhabited wire is used.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v y z
namespace QIT.HigherOrder.Comb

/-- Read the final outcome register separately from the residual memory. -/
def terminalFlagEquiv {n : Nat} (E : Fin (n + 1) → Type u) (ι : Type u) :
    boundaryOutput E ι (Fin.last n) ≃ E (Fin.last n) × ι :=
  Equiv.cast (by simp [boundaryOutput])

/-- Encode a finite outcome type in the wire universe without restricting
its original universe or its cardinality. -/
def outcomeMemoryEquiv (ι : Type v) [Fintype ι] : Memory.{u} (Fintype.card ι) ≃ ι :=
  Equiv.ulift.trans (Fintype.equivFin ι).symm

/-- Decode the final flag while leaving the residual memory untouched. -/
def terminalOutcomeEquiv {n : Nat} (E : Fin (n + 1) → Type u)
    (ι : Type v) [Fintype ι] :
    boundaryOutput E (Memory.{u} (Fintype.card ι)) (Fin.last n) ≃ E (Fin.last n) × ι :=
  (terminalFlagEquiv E _).trans
    (Equiv.prodCongr (Equiv.refl _) (outcomeMemoryEquiv ι))

section Realization
variable {n : Nat} {I O : Fin (n + 1) → Type u} {ι : Type v}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [Fintype ι] [DecidableEq ι]

private def encodedInstrument (M : Superinstrument I O ι) :
    Superinstrument I O (Memory.{u} (Fintype.card ι)) where
  branch i := M.branch (outcomeMemoryEquiv ι i)
  branch_isProbabilistic i := M.branch_isProbabilistic (outcomeMemoryEquiv ι i)
  total := M.total
  sum_branch_eq_total := (Equiv.sum_comp (outcomeMemoryEquiv ι) M.branch).trans
    M.sum_branch_eq_total

set_option backward.isDefEq.respectTransparency false in
/-- Every finite positive-length superinstrument has one finite isometric
memory chain followed by a coordinate projective measurement on its final
outcome register. Each branch retains the quantum output and has exactly
the prescribed Choi operator. This includes singular and empty finite systems
[Chiribella2009Networks, comblong-pub.tex:1125-1133]. -/
theorem Superinstrument.exists_physical_realization (M : Superinstrument I O ι) :
    ∃ (d : Fin (n + 1) → Nat)
      (c : MemoryChain I O
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card ι)))),
      ∀ i, MatrixMap.choi
        ((c.readoutInstrument (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι)).branch i) =
          M.branch i := by
  obtain ⟨d, c, hc⟩ := (encodedInstrument M).exists_flagged_memoryChain
  refine ⟨d, c.absorbOutputSpectator, ?_⟩
  intro i
  ext p q
  rw [MemoryChain.choi_readoutInstrument]
  simp only [terminalOutcomeEquiv, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_symm,
    Equiv.refl_apply, terminalFlagEquiv, MemoryChain.kraus_absorbOutputSpectator]
  rw [← MemoryChain.choi_chainMap_apply c, hc,
    (encodedInstrument M).flaggedChoi_lift_apply]
  simp only [ite_true, encodedInstrument, Equiv.apply_symm_apply]

/-- Source-shaped finite-family realization: positivity of each branch and
recursive normalization of their sum suffice. Branch domination is derived,
not an extra hypothesis [Chiribella2009Networks, comblong-pub.tex:1125-1133]. -/
theorem positiveFamily_exists_physical_realization
    (R : ι → CMatrix (Space I O)) (hR : ∀ i, (R i).PosSemidef)
    (hS : Normalized I O (∑ i, R i)) :
    ∃ (d : Fin (n + 1) → Nat)
      (c : MemoryChain I O
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card ι)))),
      ∀ i, MatrixMap.choi
        ((c.readoutInstrument (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι)).branch i) =
          R i :=
  (Superinstrument.ofPositiveFamily R hR hS).exists_physical_realization

/-- The same fixed physical chain has exactly the prescribed linear action
on every joint input matrix, with independently typed ancillary systems.
The left side contracts the chain's actual coherent Kraus amplitudes.
For input Kraus families it is also the Choi operator of their explicit
Kraus contraction, by `MemoryChain.choi_readoutContractKraus`. -/
theorem Superinstrument.exists_physical_realization_action
    (M : Superinstrument I O ι) :
    ∃ (d : Fin (n + 1) → Nat)
      (c : MemoryChain I O
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card ι)))),
      (∀ i, MatrixMap.choi
        ((c.readoutInstrument (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι)).branch i) =
          M.branch i) ∧
      ∀ (r : Type y) (s : Type z)
        [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))) (i : ι),
        c.readoutAction (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι) i Y =
          ancillaryExtension (actionMap I O (M.branch i)) Y := by
  obtain ⟨d, c, hc⟩ := M.exists_physical_realization
  refine ⟨d, c, hc, ?_⟩
  intro r s _ _ _ _ Y i
  rw [MemoryChain.readoutAction_eq_ancillaryExtension, hc]

/-- Completion by a positive complement realizes a probabilistic comb as
one outcome of a physical two-outcome memory instrument. The deterministic
completion may be singular, using the domination definition
[Chiribella2009Networks, comblong-pub.tex:1425-1433] and its completion
argument at proof lines 3280-3288. -/
theorem IsProbabilistic.exists_physical_realization {R : CMatrix (Space I O)}
    (hR : IsProbabilistic I O R) :
    ∃ (d : Fin (n + 1) → Nat)
      (c : MemoryChain I O
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card Bool)))),
      MatrixMap.choi
        ((c.readoutInstrument
          (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) Bool)).branch false) = R := by
  obtain ⟨M, hM⟩ := hR.exists_superinstrument
  obtain ⟨d, c, hc⟩ := M.exists_physical_realization
  exact ⟨d, c, (hc false).trans hM⟩

end Realization

section JointProbabilisticInput
variable {n : Nat} {P Q : Fin (n + 1) → Type u}
  [∀ j, Fintype (P j)] [∀ j, DecidableEq (P j)]
  [∀ j, Fintype (Q j)] [∀ j, DecidableEq (Q j)]
  {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- A joint probabilistic input has a two-outcome physical realization with
the same independent boundary systems and the exact original Choi operator. -/
theorem ExtendedProbabilistic.exists_readout_memoryChain
    {Y : CMatrix (((∀ j, P j) × r) × ((∀ j, Q j) × s))}
    (hY : ExtendedProbabilistic P Q r s Y) :
    ∃ (d : Fin (n + 1) → Nat)
      (w : MemoryChain (boundaryInput P r) (boundaryOutput Q s)
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card Bool)))),
      w.jointReadoutChoi (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) Bool) false = Y := by
  obtain ⟨hY, Z, hZ, hYZ⟩ := hY
  have h : IsProbabilistic (boundaryInput P r) (boundaryOutput Q s)
      (Y.submatrix (boundaryEquiv P Q r s) (boundaryEquiv P Q r s)) := by
    refine ⟨hY.submatrix _, Z.submatrix _ _, hZ, Matrix.le_iff.mpr ?_⟩
    exact (Matrix.le_iff.mp hYZ).submatrix _
  obtain ⟨d, w, hw⟩ := h.exists_physical_realization
  refine ⟨d, w, ?_⟩
  unfold MemoryChain.jointReadoutChoi
  rw [hw]
  ext p q
  simp [WireFam.matReindex_apply, Matrix.submatrix_apply]

end JointProbabilisticInput

section CompleteRealization
variable {n : Nat} {I O : Fin (n + 2) → Type u} {ι : Type v}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [Fintype ι] [DecidableEq ι]

/-- The same instrument memory chain works for every jointly normalized
inner comb and every pair of finite boundary ancillas. The inner realization
is physically interleaved with that fixed chain; measuring the terminal flag
gives exactly the blockwise ancillary link action of each prescribed branch
[Chiribella2009Networks, comblong-pub.tex:3302-3314]. -/
theorem Superinstrument.exists_physical_realization_complete
    (M : Superinstrument I O ι) :
    ∃ (d : Fin (n + 2) → Nat)
      (c : MemoryChain I O
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card ι)))),
      (∀ i, MatrixMap.choi
        ((c.readoutInstrument (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι)).branch i) =
          M.branch i) ∧
      ∀ (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))),
        ExtendedNormalized (innerInput O) (innerOutput I) r s Y →
        ∃ (e : Fin (n + 1) → Nat)
          (w : MemoryChain (boundaryInput (innerInput O) r)
            (boundaryOutput (innerOutput I) s) (fun j => Memory.{u} (e j))),
          w.jointChoi = Y ∧
          ∀ i, MatrixMap.choi
            ((c.connectReadoutInstrument
              (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι) w).branch i) =
                ancillaryExtension (actionMap I O (M.branch i)) Y := by
  obtain ⟨d, c, hc⟩ := M.exists_physical_realization
  refine ⟨d, c, hc, ?_⟩
  intro r s _ _ _ _ Y hY
  obtain ⟨e, w, hw⟩ := (normalized_iff_exists_memoryChain _).mp hY
  have hWY : w.jointChoi = Y := by
    change WireFam.matReindex (boundaryEquiv (innerInput O) (innerOutput I) r s)
      (MatrixMap.choi w.chainMap) = Y
    rw [hw]
    ext p q
    simp [WireFam.matReindex_apply, Matrix.submatrix_apply]
  refine ⟨e, w, hWY, ?_⟩
  intro i
  rw [MemoryChain.connectReadoutInstrument_choi, hc, hWY]

/-- The physical realization of a probabilistic comb is uniform over joint
normalized inputs and independent ancillary systems, with exact output Choi
operators, obtained through its two-outcome completion. -/
theorem IsProbabilistic.exists_physical_realization_complete
    {R : CMatrix (Space I O)} (hR : IsProbabilistic I O R) :
    ∃ (d : Fin (n + 2) → Nat)
      (c : MemoryChain I O
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card Bool)))),
      MatrixMap.choi
        ((c.readoutInstrument
          (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) Bool)).branch false) = R ∧
      ∀ (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))),
        ExtendedNormalized (innerInput O) (innerOutput I) r s Y →
        ∃ (e : Fin (n + 1) → Nat)
          (w : MemoryChain (boundaryInput (innerInput O) r)
            (boundaryOutput (innerOutput I) s) (fun j => Memory.{u} (e j))),
          w.jointChoi = Y ∧
          MatrixMap.choi
            ((c.connectReadoutInstrument
              (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) Bool) w).branch false) =
                ancillaryExtension (actionMap I O R) Y := by
  obtain ⟨M, hM⟩ := hR.exists_superinstrument
  obtain ⟨d, c, hc, ha⟩ := M.exists_physical_realization_complete
  refine ⟨d, c, (hc false).trans hM, ?_⟩
  intro r s _ _ _ _ Y hY
  obtain ⟨e, w, hw, hi⟩ := ha r s Y hY
  exact ⟨e, w, hw, by simpa only [hM] using hi false⟩

/-- A fixed realization also accepts any joint probabilistic inner comb.
The inner comb is completed once, and the two terminal registers are measured
jointly. Selecting the input's designated outcome recovers its unnormalized
operator exactly; no renormalization or postselection factor is inserted. -/
theorem Superinstrument.exists_physical_realization_probabilistic
    (M : Superinstrument I O ι) :
    ∃ (d : Fin (n + 2) → Nat)
      (c : MemoryChain I O
        (boundaryOutput (fun j => Memory.{u} (d j)) (Memory.{u} (Fintype.card ι)))),
      (∀ i, MatrixMap.choi
        ((c.readoutInstrument (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι)).branch i) =
          M.branch i) ∧
      ∀ (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))),
        ExtendedProbabilistic (innerInput O) (innerOutput I) r s Y →
        ∃ (e : Fin (n + 1) → Nat)
          (w : MemoryChain (boundaryInput (innerInput O) r)
            (boundaryOutput (innerOutput I) s)
            (boundaryOutput (fun j => Memory.{u} (e j)) (Memory.{u} (Fintype.card Bool)))),
          w.jointReadoutChoi
            (terminalOutcomeEquiv (fun j => Memory.{u} (e j)) Bool) false = Y ∧
          ∀ i, MatrixMap.choi
            ((c.connectJointReadoutInstrument
              (terminalOutcomeEquiv (fun j => Memory.{u} (d j)) ι) w
              (terminalOutcomeEquiv (fun j => Memory.{u} (e j)) Bool)).branch (i, false)) =
                ancillaryExtension (actionMap I O (M.branch i)) Y := by
  obtain ⟨d, c, hc⟩ := M.exists_physical_realization
  refine ⟨d, c, hc, ?_⟩
  intro r s _ _ _ _ Y hY
  obtain ⟨e, w, hw⟩ := hY.exists_readout_memoryChain
  refine ⟨e, w, hw, ?_⟩
  intro i
  rw [MemoryChain.connectJointReadoutInstrument_choi, hc, hw]

end CompleteRealization
end QIT.HigherOrder.Comb
