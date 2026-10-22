/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.IteratedContraction

/-!
# Composition of causally scheduled quantum networks

A causal join is composed by the genuine matched-wire link product, transported
to its scheduled free boundary. The equality with iterated forward contraction
proves deterministic and probabilistic normalization closure for arbitrary finite
heterogeneous wires, including empty wire types. No output-normalization or
permuted-input-normalization assumption is introduced.

Link-product composition is that of
[Chiribella2009Networks, comblong-pub.tex:1279-1286], with the causal joining
condition at lines 1233-1243 of the same source; recursive normalization is
[Chiribella2009Networks, comblong-pub.tex:860-877].
-/

@[expose] public section

open QIT QIT.HigherOrder.Comb QIT.WireFam
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
universe u v w
namespace QIT.HigherOrder.Comb.CausalJoin

private theorem eval_heq {α : Sort v} {F : α → Sort w} (f : ∀ a, F a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by cases h; rfl

private theorem connValues_castAdd {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
    (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ab) :
    j.connValues z (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k)) =
      ((j.schedule.leftFamilyEquiv O Q (j.outA k)).trans
          (Equiv.cast (congrArg (j.schedule.family O Q)
            (connections_a_castAdd j k).symm)))
        ((Equiv.cast (connFam₁_castAdd j k)) (z (Fin.castAdd j.ba k))) := by
  apply eq_of_heq
  unfold connValues
  rw [Equiv.piCongrLeft_apply_eq_cast]
  refine (cast_heq _ _).trans ?_
  have hidx : (⟨Fin.cast (connections_length j).symm, Fin.cast (connections_length j),
      fun _ ↦ Fin.ext rfl, fun _ ↦ Fin.ext rfl⟩ :
      Fin (j.ab + j.ba) ≃ Fin j.connections.length).symm
      (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k)) =
      Fin.castAdd j.ba k := rfl
  rw [hidx]
  simp only [splitEquiv_symm_apply_castAdd, Equiv.prodCongr_apply,
    Equiv.trans_apply, Equiv.piCongrRight_apply, Prod.map, Pi.map_apply]
  rfl

private theorem connValues_natAdd {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}
    (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ba) :
    j.connValues z (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k)) =
      ((j.schedule.rightFamilyEquiv O Q (j.outB k)).trans
          (Equiv.cast (congrArg (j.schedule.family O Q)
            (connections_a_natAdd j k).symm)))
        ((j.equivBA k).symm
          ((Equiv.cast (connFam₁_natAdd j k)) (z (Fin.natAdd j.ab k)))) := by
  apply eq_of_heq
  unfold connValues
  rw [Equiv.piCongrLeft_apply_eq_cast]
  refine (cast_heq _ _).trans ?_
  have hidx : (⟨Fin.cast (connections_length j).symm, Fin.cast (connections_length j),
      fun _ ↦ Fin.ext rfl, fun _ ↦ Fin.ext rfl⟩ :
      Fin (j.ab + j.ba) ≃ Fin j.connections.length).symm
      (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k)) =
      Fin.natAdd j.ab k := rfl
  rw [hidx]
  simp only [splitEquiv_symm_apply_natAdd, Equiv.prodCongr_apply,
    Equiv.trans_apply, Equiv.piCongrRight_apply, Prod.map, Pi.map_apply]
  rfl

variable {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}

private def restoreConfig (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) :
    Space (j.schedule.family I P) (j.schedule.family O Q) :=
  (j.consumptions.fillIn (j.valuesJoinEquiv z) (j.boundaryIndexEquiv.symm p).1,
    j.consumptions.fillOut (j.valuesJoinEquiv z) (j.boundaryIndexEquiv.symm p).2)

private theorem valuesJoinEquiv_eq' (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) :
    j.valuesJoinEquiv z =
      (Consumptions.ofListAux_valuesEquiv
        (SIn := j.connections.map Connection.b) (SOut := j.connections.map Connection.a)
        [] [] j.connections j.connections_disIn j.connections_disOut
        (fun _ _ ↦ ⟨by simp, by simp⟩) (fun _ ↦ by simp)
        (fun _ ↦ by simp)).symm (j.connValues z) := rfl

private theorem restoreConfig_input_connected (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (i : Fin j.connections.length) :
    HEq ((j.restoreConfig z p).1 ((j.connections.get i).b))
      ((j.connections.get i).e (j.connValues z i)) := by
  unfold restoreConfig
  rw [valuesJoinEquiv_eq']
  exact (heq_of_eq (Consumptions.ofListAux_fillIn_get [] [] j.connections
    j.connections_disIn j.connections_disOut (fun _ _ ↦ ⟨by simp, by simp⟩)
    (fun _ ↦ by simp) (fun _ ↦ by simp) i (j.connValues z)
    (j.boundaryIndexEquiv.symm p).1)).trans (cast_heq _ _)

private theorem restoreConfig_output_connected (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (i : Fin j.connections.length) :
    HEq ((j.restoreConfig z p).2 ((j.connections.get i).a)) (j.connValues z i) := by
  unfold restoreConfig
  rw [valuesJoinEquiv_eq']
  exact (heq_of_eq (Consumptions.ofListAux_fillOut_get [] [] j.connections
    j.connections_disIn j.connections_disOut (fun _ _ ↦ ⟨by simp, by simp⟩)
    (fun _ ↦ by simp) (fun _ ↦ by simp) i (j.connValues z)
    (j.boundaryIndexEquiv.symm p).2)).trans (cast_heq _ _)

private theorem restoreConfig_input_free (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (t : Fin (nA + nB))
    (ht : t ∉ j.connections.map Connection.b) :
    HEq ((j.restoreConfig z p).1 t) (p.1 t) := by
  have h := Consumptions.ofListAux_fillIn_not_mem [] [] j.connections
    j.connections_disIn j.connections_disOut (fun _ _ ↦ ⟨by simp, by simp⟩)
    (fun _ ↦ by simp) (fun _ ↦ by simp) t (by simp) ht (j.valuesJoinEquiv z)
    (j.boundaryIndexEquiv.symm p).1
  refine (heq_of_eq h).trans ((cast_heq _ _).trans ?_)
  change HEq (cast _ (p.1 t)) (p.1 t)
  exact cast_heq _ _

private theorem connections_get_castAdd (j : CausalJoin I O P Q) (k : Fin j.ab) :
    j.connections.get (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k)) =
      ({ a := j.schedule.leftRank (j.outA k)
         b := j.schedule.rightRank (j.inB k)
         hab := j.forwardAB k
         e := (j.schedule.leftFamilyEquiv O Q (j.outA k)).symm.trans
           ((j.equivAB k).trans (j.schedule.rightFamilyEquiv I P (j.inB k))) } :
        Connection (j.schedule.family I P) (j.schedule.family O Q)) := by
  have hv : (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k)).val = k.val := rfl
  have hlt : k.val < j.connections.length := by rw [connections_length]; omega
  rw [show Fin.cast (connections_length j).symm (Fin.castAdd j.ba k) = ⟨k.val, hlt⟩ from
    Fin.ext hv]
  simp [connections, List.length_map, List.length_finRange]
  exact eval_heq (fun k ↦ (j.schedule.leftFamilyEquiv O Q (j.outA k)).symm.trans
    ((j.equivAB k).trans (j.schedule.rightFamilyEquiv I P (j.inB k)))) (by simp)

private theorem connections_get_natAdd (j : CausalJoin I O P Q) (k : Fin j.ba) :
    j.connections.get (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k)) =
      ({ a := j.schedule.rightRank (j.outB k)
         b := j.schedule.leftRank (j.inA k)
         hab := j.forwardBA k
         e := (j.schedule.rightFamilyEquiv O Q (j.outB k)).symm.trans
           ((j.equivBA k).trans (j.schedule.leftFamilyEquiv I P (j.inA k))) } :
        Connection (j.schedule.family I P) (j.schedule.family O Q)) := by
  have hv : (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k)).val = j.ab + k.val := rfl
  have hlt : j.ab + k.val < j.connections.length := by rw [connections_length]; omega
  rw [show Fin.cast (connections_length j).symm (Fin.natAdd j.ab k) = ⟨j.ab + k.val, hlt⟩ from
    Fin.ext hv]
  simp [connections, List.length_map, List.length_finRange]
  exact eval_heq (fun k ↦ (j.schedule.rightFamilyEquiv O Q (j.outB k)).symm.trans
    ((j.equivBA k).trans (j.schedule.leftFamilyEquiv I P (j.inA k)))) (by simp)

/-- Restore both original comb configurations from a free boundary and one
connected configuration, using the actual matching readback maps. -/
def rawConfig (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) : Space I O × Space P Q :=
  let b := splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
    j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)
  (splitAppendEquiv I O (j.toWireJoin.toWireMatch.read₁ (b.1, z)),
    splitAppendEquiv P Q (j.toWireJoin.toWireMatch.read₂ z b.2))

/-- Read an unconnected input-left port from the scheduled boundary. -/
theorem rawConfig_input_left_free (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nA}
    (hi : i ∉ Set.range j.inA) : HEq ((j.rawConfig z p).1.1 i)
      (p.1 (j.schedule.leftRank i)) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₁
    ((splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1, z)
    (Fin.castAdd nA i))) _
  refine (cast_heq _ _).trans ?_
  let fi := freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
    ⟨Fin.castAdd nA i, fun h ↦ hi ((first_input_range j i).mp h)⟩
  have hread := j.toWireJoin.toWireMatch.read₁_compl
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1 z fi
  have hpos : complEmb j.toWireJoin.toWireMatch.ι₁
    j.toWireJoin.toWireMatch.hι₁ fi = Fin.castAdd nA i := complEmb_freeIndex _ _ _
  refine (eval_heq _ hpos).symm.trans ((heq_of_eq hread).trans ?_)
  change HEq (cast _ (j.boundaryEquiv.symm p (Fin.castAdd _ fi))) _
  refine (cast_heq _ _).trans ?_
  exact (heq_of_eq (j.boundaryEquiv_symm_input_left p hi)).trans (cast_heq _ _)

private theorem restoreConfig_output_free (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (t : Fin (nA + nB))
    (ht : t ∉ j.connections.map Connection.a) :
    HEq ((j.restoreConfig z p).2 t) (p.2 t) := by
  have h := Consumptions.ofListAux_fillOut_not_mem [] [] j.connections
    j.connections_disIn j.connections_disOut (fun _ _ ↦ ⟨by simp, by simp⟩)
    (fun _ ↦ by simp) (fun _ ↦ by simp) t (by simp) ht (j.valuesJoinEquiv z)
    (j.boundaryIndexEquiv.symm p).2
  refine (heq_of_eq h).trans ((cast_heq _ _).trans ?_)
  change HEq (cast _ (p.2 t)) (p.2 t)
  exact cast_heq _ _

/-- Read an unconnected output-left port from the scheduled boundary. -/
theorem rawConfig_output_left_free (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nA}
    (hi : i ∉ Set.range j.outA) : HEq ((j.rawConfig z p).1.2 i)
      (p.2 (j.schedule.leftRank i)) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₁
    ((splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1, z)
    (Fin.natAdd nA i))) _
  refine (cast_heq _ _).trans ?_
  let fi := freeIndex j.toWireJoin.toWireMatch.ι₁ j.toWireJoin.toWireMatch.hι₁
    ⟨Fin.natAdd nA i, fun h ↦ hi ((first_output_range j i).mp h)⟩
  have hread := j.toWireJoin.toWireMatch.read₁_compl
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1 z fi
  have hpos : complEmb j.toWireJoin.toWireMatch.ι₁
    j.toWireJoin.toWireMatch.hι₁ fi = Fin.natAdd nA i := complEmb_freeIndex _ _ _
  refine (eval_heq _ hpos).symm.trans ((heq_of_eq hread).trans ?_)
  change HEq (cast _ (j.boundaryEquiv.symm p (Fin.castAdd _ fi))) _
  refine (cast_heq _ _).trans ?_
  exact (heq_of_eq (j.boundaryEquiv_symm_output_left p hi)).trans (cast_heq _ _)

/-- Read an unconnected input-right port from the scheduled boundary. -/
theorem rawConfig_input_right_free (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nB}
    (hi : i ∉ Set.range j.inB) : HEq ((j.rawConfig z p).2.1 i)
      (p.1 (j.schedule.rightRank i)) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₂ z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2
    (Fin.castAdd nB i))) _
  refine (cast_heq _ _).trans ?_
  let fi := freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
    ⟨Fin.castAdd nB i, fun h ↦ hi ((second_input_range j i).mp h)⟩
  have hread := j.toWireJoin.toWireMatch.read₂_compl z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2 fi
  have hpos : complEmb j.toWireJoin.toWireMatch.ι₂
    j.toWireJoin.toWireMatch.hι₂ fi = Fin.castAdd nB i := complEmb_freeIndex _ _ _
  refine (eval_heq _ hpos).symm.trans ((heq_of_eq hread).trans ?_)
  change HEq (cast _ (j.boundaryEquiv.symm p (Fin.natAdd _ fi))) _
  refine (cast_heq _ _).trans ?_
  exact (heq_of_eq (j.boundaryEquiv_symm_input_right p hi)).trans (cast_heq _ _)

/-- Read an unconnected output-right port from the scheduled boundary. -/
theorem rawConfig_output_right_free (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) {i : Fin nB}
    (hi : i ∉ Set.range j.outB) : HEq ((j.rawConfig z p).2.2 i)
      (p.2 (j.schedule.rightRank i)) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₂ z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2
    (Fin.natAdd nB i))) _
  refine (cast_heq _ _).trans ?_
  let fi := freeIndex j.toWireJoin.toWireMatch.ι₂ j.toWireJoin.toWireMatch.hι₂
    ⟨Fin.natAdd nB i, fun h ↦ hi ((second_output_range j i).mp h)⟩
  have hread := j.toWireJoin.toWireMatch.read₂_compl z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2 fi
  have hpos : complEmb j.toWireJoin.toWireMatch.ι₂
    j.toWireJoin.toWireMatch.hι₂ fi = Fin.natAdd nB i := complEmb_freeIndex _ _ _
  refine (eval_heq _ hpos).symm.trans ((heq_of_eq hread).trans ?_)
  change HEq (cast _ (j.boundaryEquiv.symm p (Fin.natAdd _ fi))) _
  refine (cast_heq _ _).trans ?_
  exact (heq_of_eq (j.boundaryEquiv_symm_output_right p hi)).trans (cast_heq _ _)

/-- Read a connected output-left port, retaining its basis identification. -/
theorem rawConfig_output_left_connected (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (k : Fin j.ab) :
    HEq ((j.rawConfig z p).1.2 (j.outA k)) (z (Fin.castAdd j.ba k)) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₁
    ((splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1, z)
    (Fin.natAdd nA (j.outA k)))) _
  refine (cast_heq _ _).trans ?_
  have h := j.toWireJoin.toWireMatch.read₁_conn
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1 z (Fin.castAdd j.ba k)
  exact (eval_heq _ (j.toWireJoin.toWireMatch_outA k)).symm.trans (heq_of_eq h)

/-- Read a connected input-left port, retaining its basis identification. -/
theorem rawConfig_input_left_connected (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (k : Fin j.ba) :
    HEq ((j.rawConfig z p).1.1 (j.inA k)) (z (Fin.natAdd j.ab k)) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₁
    ((splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1, z)
    (Fin.castAdd nA (j.inA k)))) _
  refine (cast_heq _ _).trans ?_
  have h := j.toWireJoin.toWireMatch.read₁_conn
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1 z (Fin.natAdd j.ab k)
  exact (eval_heq _ (j.toWireJoin.toWireMatch_inA k)).symm.trans (heq_of_eq h)

private theorem connection_apply_heq {n : Nat} {I O : Fin n → Type u}
    (c d : Connection I O) (h : c = d) {x : O c.a} {y : O d.a}
    (hx : HEq x y) : HEq (c.e x) (d.e y) := by
  cases h
  cases hx
  rfl

private theorem connValues_castAdd_heq (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ab) :
    HEq (j.connValues z (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k)))
      (z (Fin.castAdd j.ba k)) := by
  refine (heq_of_eq (connValues_castAdd j z k)).trans ?_
  change HEq (cast _ (cast _ (cast _ (z _)))) (z _)
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))

private theorem connValues_natAdd_heq (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ba) :
    HEq (j.connValues z (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k)))
      ((j.equivBA k).symm (cast (connFam₁_natAdd j k) (z (Fin.natAdd j.ab k)))) := by
  refine (heq_of_eq (connValues_natAdd j z k)).trans ?_
  change HEq (cast _ (cast _ ((j.equivBA k).symm _))) _
  exact (cast_heq _ _).trans (cast_heq _ _)

private theorem connection_input_castAdd (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ab) :
    HEq ((j.connections.get (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k))).e
        (j.connValues z (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k))))
      ((j.equivAB k) (cast (connFam₁_castAdd j k) (z (Fin.castAdd j.ba k)))) := by
  have hx := (heq_of_eq (connValues_castAdd j z k)).trans (cast_heq _ _)
  have h := connection_apply_heq _ _ (connections_get_castAdd j k) hx
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at h
  exact h.trans (cast_heq _ _)

private theorem connection_input_natAdd (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ba) :
    HEq ((j.connections.get (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k))).e
        (j.connValues z (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k))))
      (z (Fin.natAdd j.ab k)) := by
  have hx := (heq_of_eq (connValues_natAdd j z k)).trans (cast_heq _ _)
  have h := connection_apply_heq _ _ (connections_get_natAdd j k) hx
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  exact h.trans ((cast_heq _ _).trans (cast_heq _ _))

private theorem cast_equiv_apply_heq {α β α' β' : Type u}
    (ha : α = α') (hb : β = β') (h : (α ≃ β) = (α' ≃ β'))
    (e : α ≃ β) (x : α') : HEq ((cast h e) x) (e (cast ha.symm x)) := by
  cases ha; cases hb; rfl

private theorem eRelabel_castAdd_heq (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ab) :
    HEq (j.toWireJoin.toWireMatch.eRelabel z (Fin.castAdd j.ba k))
      ((j.equivAB k) (cast (connFam₁_castAdd j k) (z (Fin.castAdd j.ba k)))) := by
  simp only [WireMatch.eRelabel, WireJoin.toWireMatch, Fin.addCases_left]
  exact cast_equiv_apply_heq (connFam₁_castAdd j k).symm
    (by change P (j.inB k) = append P Q (j.toWireJoin.toWireMatch.ι₂ (Fin.castAdd j.ba k))
        rw [WireJoin.toWireMatch_inB, append_castAdd]) _ _ _

private theorem eRelabel_natAdd_heq (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k) (k : Fin j.ba) :
    HEq (j.toWireJoin.toWireMatch.eRelabel z (Fin.natAdd j.ab k))
      ((j.equivBA k).symm (cast (connFam₁_natAdd j k) (z (Fin.natAdd j.ab k)))) := by
  simp only [WireMatch.eRelabel, WireJoin.toWireMatch, Fin.addCases_right]
  exact cast_equiv_apply_heq (connFam₁_natAdd j k).symm
    (by change Q (j.outB k) = append P Q (j.toWireJoin.toWireMatch.ι₂ (Fin.natAdd j.ab k))
        rw [WireJoin.toWireMatch_outB, append_natAdd]) _ _ _

/-- Read a connected input-right port, retaining its basis identification. -/
theorem rawConfig_input_right_connected (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (k : Fin j.ab) :
    HEq ((j.rawConfig z p).2.1 (j.inB k))
      ((j.equivAB k) (cast (connFam₁_castAdd j k) (z (Fin.castAdd j.ba k)))) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₂ z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2
    (Fin.castAdd nB (j.inB k)))) _
  refine (cast_heq _ _).trans ?_
  have h := j.toWireJoin.toWireMatch.read₂_conn z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2 (Fin.castAdd j.ba k)
  exact (eval_heq _ (j.toWireJoin.toWireMatch_inB k)).symm.trans
    ((heq_of_eq h).trans (eRelabel_castAdd_heq j z k))

/-- Read a connected output-right port, retaining its basis identification. -/
theorem rawConfig_output_right_connected (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (k : Fin j.ba) :
    HEq ((j.rawConfig z p).2.2 (j.outB k))
      ((j.equivBA k).symm (cast (connFam₁_natAdd j k) (z (Fin.natAdd j.ab k)))) := by
  change HEq (cast _ (j.toWireJoin.toWireMatch.read₂ z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2
    (Fin.natAdd nB (j.outB k)))) _
  refine (cast_heq _ _).trans ?_
  have h := j.toWireJoin.toWireMatch.read₂_conn z
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2 (Fin.natAdd j.ab k)
  exact (eval_heq _ (j.toWireJoin.toWireMatch_outB k)).symm.trans
    ((heq_of_eq h).trans (eRelabel_natAdd_heq j z k))

private theorem restoreConfig_input_left (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (i : Fin nA) :
    HEq ((j.restoreConfig z p).1 (j.schedule.leftRank i)) ((j.rawConfig z p).1.1 i) := by
  classical
  by_cases hi : i ∈ Set.range j.inA
  · obtain ⟨k, rfl⟩ := hi
    have hc := connections_get_natAdd j k
    have hb := congrArg Connection.b hc
    have h := restoreConfig_input_connected j z p
      (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k))
    exact (eval_heq (j.restoreConfig z p).1 hb).symm.trans
      (h.trans ((connection_input_natAdd j z k).trans
        (rawConfig_input_left_connected j z p k).symm))
  · have ht : j.schedule.leftRank i ∉ j.connections.map Connection.b := by
      simpa [connections_mem_b, inputConnected] using hi
    exact (restoreConfig_input_free j z p _ ht).trans
      (rawConfig_input_left_free j z p hi).symm

private theorem restoreConfig_output_left (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (i : Fin nA) :
    HEq ((j.restoreConfig z p).2 (j.schedule.leftRank i)) ((j.rawConfig z p).1.2 i) := by
  classical
  by_cases hi : i ∈ Set.range j.outA
  · obtain ⟨k, rfl⟩ := hi
    have hc := connections_get_castAdd j k
    have ha := congrArg Connection.a hc
    have h := restoreConfig_output_connected j z p
      (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k))
    exact (eval_heq (j.restoreConfig z p).2 ha).symm.trans
      (h.trans ((connValues_castAdd_heq j z k).trans
        (rawConfig_output_left_connected j z p k).symm))
  · have ht : j.schedule.leftRank i ∉ j.connections.map Connection.a := by
      simpa [connections_mem_a, outputConnected] using hi
    exact (restoreConfig_output_free j z p _ ht).trans
      (rawConfig_output_left_free j z p hi).symm

private theorem restoreConfig_input_right (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (i : Fin nB) :
    HEq ((j.restoreConfig z p).1 (j.schedule.rightRank i)) ((j.rawConfig z p).2.1 i) := by
  classical
  by_cases hi : i ∈ Set.range j.inB
  · obtain ⟨k, rfl⟩ := hi
    have hc := connections_get_castAdd j k
    have hb := congrArg Connection.b hc
    have h := restoreConfig_input_connected j z p
      (Fin.cast (connections_length j).symm (Fin.castAdd j.ba k))
    exact (eval_heq (j.restoreConfig z p).1 hb).symm.trans
      (h.trans ((connection_input_castAdd j z k).trans
        (rawConfig_input_right_connected j z p k).symm))
  · have ht : j.schedule.rightRank i ∉ j.connections.map Connection.b := by
      simpa [connections_mem_b, inputConnected] using hi
    exact (restoreConfig_input_free j z p _ ht).trans
      (rawConfig_input_right_free j z p hi).symm

private theorem restoreConfig_output_right (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) (i : Fin nB) :
    HEq ((j.restoreConfig z p).2 (j.schedule.rightRank i)) ((j.rawConfig z p).2.2 i) := by
  classical
  by_cases hi : i ∈ Set.range j.outB
  · obtain ⟨k, rfl⟩ := hi
    have hc := connections_get_natAdd j k
    have ha := congrArg Connection.a hc
    have h := restoreConfig_output_connected j z p
      (Fin.cast (connections_length j).symm (Fin.natAdd j.ab k))
    exact (eval_heq (j.restoreConfig z p).2 ha).symm.trans
      (h.trans ((connValues_natAdd_heq j z k).trans
        (rawConfig_output_right_connected j z p k).symm))
  · have ht : j.schedule.rightRank i ∉ j.connections.map Connection.a := by
      simpa [connections_mem_a, outputConnected] using hi
    exact (restoreConfig_output_free j z p _ ht).trans
      (rawConfig_output_right_free j z p hi).symm

private theorem restoreConfig_eq_raw (j : CausalJoin I O P Q)
    (z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k)
    (p : Space j.boundaryInput j.boundaryOutput) :
    j.schedule.configEquiv I O P Q (j.restoreConfig z p) = j.rawConfig z p := by
  rw [EventSchedule.configEquiv_eq_rankConfig]
  apply Prod.ext <;> apply Prod.ext
  · funext i
    apply eq_of_heq
    change HEq (cast _ ((j.restoreConfig z p).1 (j.schedule.leftRank i))) _
    exact (cast_heq _ _).trans (restoreConfig_input_left j z p i)
  · funext i
    apply eq_of_heq
    change HEq (cast _ ((j.restoreConfig z p).2 (j.schedule.leftRank i))) _
    exact (cast_heq _ _).trans (restoreConfig_output_left j z p i)
  · funext i
    apply eq_of_heq
    change HEq (cast _ ((j.restoreConfig z p).1 (j.schedule.rightRank i))) _
    exact (cast_heq _ _).trans (restoreConfig_input_right j z p i)
  · funext i
    apply eq_of_heq
    change HEq (cast _ ((j.restoreConfig z p).2 (j.schedule.rightRank i))) _
    exact (cast_heq _ _).trans (restoreConfig_output_right j z p i)

section Operators
variable [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
  [∀ i, Fintype (P i)] [∀ i, Fintype (Q i)]

/-- The genuine matched-wire composite, on its scheduled unit-padded boundary. -/
def comp (j : CausalJoin I O P Q) (J : CMatrix (Space I O))
    (K : CMatrix (Space P Q)) : CMatrix (Space j.boundaryInput j.boundaryOutput) :=
  matReindex j.boundaryEquiv (j.toWireJoin.rawComp J K)

omit [∀ i, Fintype (P i)] [∀ i, Fintype (Q i)] in
/-- Entrywise link contraction in the original component configurations. -/
theorem comp_apply (j : CausalJoin I O P Q) (J : CMatrix (Space I O))
    (K : CMatrix (Space P Q)) (p q : Space j.boundaryInput j.boundaryOutput) :
    j.comp J K p q = ∑ z : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k,
      ∑ z' : ∀ k, j.toWireJoin.toWireMatch.connFam₁ k,
        J (j.rawConfig z' p).1 (j.rawConfig z q).1 *
          K (j.rawConfig z' p).2 (j.rawConfig z q).2 := by
  have h := j.toWireJoin.rawComp_apply J K
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).1
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm q)).1
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm p)).2
    (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
      j.toWireJoin.toWireMatch.complFam₂ (j.boundaryEquiv.symm q)).2
  have hp := (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
    j.toWireJoin.toWireMatch.complFam₂).symm_apply_apply (j.boundaryEquiv.symm p)
  have hq := (splitAppendEquiv j.toWireJoin.toWireMatch.complFam₁
    j.toWireJoin.toWireMatch.complFam₂).symm_apply_apply (j.boundaryEquiv.symm q)
  exact (congrArg₂ (j.toWireJoin.rawComp J K) hp hq).symm.trans h

omit [∀ i, Fintype (P i)] in
/-- The matched-wire link product equals the full sequence of actual forward
contractions of the scheduled tensor product. -/
theorem comp_eq_run (j : CausalJoin I O P Q) (J : CMatrix (Space I O))
    (K : CMatrix (Space P Q)) :
    j.comp J K = matReindex j.boundaryIndexEquiv (j.consumptions.run (j.schedule.tensor J K)) := by
  let : ∀ k : Fin (j.ab + j.ba), Fintype (j.toWireJoin.toWireMatch.connFam₁ k) := fun k ↦ by
    change Fintype (append I O (j.toWireJoin.toWireMatch.ι₁ k))
    infer_instance
  ext p q
  rw [comp_apply, matReindex_apply]
  have hrun := j.consumptions.run_apply
    (j.boundaryIndexEquiv.symm p) (j.boundaryIndexEquiv.symm q) (j.schedule.tensor J K)
  rw [hrun, Finset.sum_comm]
  refine Fintype.sum_equiv j.valuesJoinEquiv _ _ (fun z ↦ ?_)
  refine Fintype.sum_equiv j.valuesJoinEquiv _ _ (fun z' ↦ ?_)
  change J (j.rawConfig z p).1 (j.rawConfig z' q).1 *
      K (j.rawConfig z p).2 (j.rawConfig z' q).2 =
    j.schedule.tensor J K (j.restoreConfig z p) (j.restoreConfig z' q)
  rw [EventSchedule.tensor_apply, restoreConfig_eq_raw j z p, restoreConfig_eq_raw j z' q]

/-- Matching preserves positivity without inhabited-wire assumptions. -/
theorem comp_posSemidef (j : CausalJoin I O P Q)
    {J : CMatrix (Space I O)} {K : CMatrix (Space P Q)}
    (hJ : J.PosSemidef) (hK : K.PosSemidef) : (j.comp J K).PosSemidef :=
  matReindex_posSemidef _ (j.toWireJoin.rawComp_posSemidef hJ hK)

/-- Loewner monotonicity in the first factor for a positive second factor. -/
theorem comp_mono_left (j : CausalJoin I O P Q)
    {J J' : CMatrix (Space I O)} {K : CMatrix (Space P Q)}
    (hJ : J ≤ J') (hK : K.PosSemidef) : j.comp J K ≤ j.comp J' K := by
  classical
  unfold comp WireJoin.rawComp WireMatch.linkProduct
  exact matReindex_le _ (linkProduct_mono_left
    (matReindex_le _ (matReindex_le _ hJ))
    (matReindex_posSemidef _ (matReindex_posSemidef _ hK)))

/-- Loewner monotonicity in the second factor for a positive first factor. -/
theorem comp_mono_right (j : CausalJoin I O P Q)
    {J : CMatrix (Space I O)} {K K' : CMatrix (Space P Q)}
    (hJ : J.PosSemidef) (hK : K ≤ K') : j.comp J K ≤ j.comp J K' := by
  classical
  unfold comp WireJoin.rawComp WireMatch.linkProduct
  exact matReindex_le _ (linkProduct_mono_right
    (matReindex_posSemidef _ (matReindex_posSemidef _ hJ))
    (matReindex_le _ (matReindex_le _ hK)))

variable [∀ i, DecidableEq (I i)] [∀ i, DecidableEq (O i)]
  [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (Q i)]

/-- Composing two normalized combs along any causally scheduled directional
matching preserves recursive normalization of the actual free boundary. -/
theorem comp_normalized (j : CausalJoin I O P Q)
    {J : CMatrix (Space I O)} {K : CMatrix (Space P Q)}
    (hJ : Normalized I O J) (hK : Normalized P Q K) :
    Normalized j.boundaryInput j.boundaryOutput (j.comp J K) := by
  rw [comp_eq_run]
  exact (Normalized.reindex_iff
    (fun t ↦ Equiv.cast (congrFun (consumeList_connections_input j) t))
    (fun t ↦ Equiv.cast (congrFun (consumeList_connections_output j) t)) _).mp
      (j.consumptions.run_normalized (j.schedule.normalized_tensor hJ hK))

end Operators

section Probabilistic
variable {a b : Nat} {I O : Fin (a + 1) → Type u} {P Q : Fin (b + 1) → Type u}
  [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
  [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
  [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
  [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]

/-- Two probabilistic combs compose to a probabilistic comb. The deterministic
dominating witness is the composite of their deterministic dominating witnesses. -/
theorem comp_probabilistic (j : CausalJoin I O P Q)
    {J : CMatrix (Space I O)} {K : CMatrix (Space P Q)}
    (hJ : IsProbabilistic I O J) (hK : IsProbabilistic P Q K) :
    IsProbabilistic (n := (a + 1) + b) j.boundaryInput j.boundaryOutput (j.comp J K) := by
  obtain ⟨hJpos, J₀, hJ₀, hJJ₀⟩ := hJ
  obtain ⟨hKpos, K₀, hK₀, hKK₀⟩ := hK
  exact ⟨j.comp_posSemidef hJpos hKpos, j.comp J₀ K₀,
    j.comp_normalized hJ₀ hK₀,
    (j.comp_mono_left hJJ₀ hKpos).trans (j.comp_mono_right hJ₀.posSemidef hKK₀)⟩

end Probabilistic

end QIT.HigherOrder.Comb.CausalJoin
