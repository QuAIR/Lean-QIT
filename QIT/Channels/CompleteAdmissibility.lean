/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Map.QuantumOperation
public import QIT.Core.Channel
public import QIT.Util.Wires

/-!
# Ancillary action and complete admissibility of higher-order maps

A higher-order linear transformation is represented on input-first Choi matrices.
Its ancillary action leaves both ancillary input and ancillary output indices
untouched. These are independent finite systems, not necessarily the same size.
This is the stabilization required in
[Chiribella2008Supermaps, VersioneArchivio.tex:143-150].

This module supplies semantics and closure laws, not a realization theorem or a
finite list of normalization constraints for recursive quantum combs.
The ancillary universe parameters `y` and `z` are independent; certificates
being composed must use the same ancillary universe parameters.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT.HigherOrder

universe u v w x y z u' v'

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
variable {r : Type y} {s : Type z}
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- A fixed ancillary matrix block in an input-first bipartite Choi matrix. -/
def ancillaryBlock (J : CMatrix ((a × r) × (b × s))) (i j : r × s) :
    CMatrix (a × b) :=
  fun p q => J ((p.1, i.1), (p.2, i.2)) ((q.1, j.1), (q.2, j.2))

/-- Canonical extension by the identity supermap on the ancillary wires.
The original transformation acts on each ancillary matrix block. -/
def ancillaryExtension (S : MatrixMap (a × b) (c × d)) :
    MatrixMap ((a × r) × (b × s)) ((c × r) × (d × s)) where
  toFun J := fun p q =>
    S (ancillaryBlock J (p.1.2, p.2.2) (q.1.2, q.2.2)) (p.1.1, p.2.1) (q.1.1, q.2.1)
  map_add' J K := by
    ext p q
    change S (ancillaryBlock J _ _ + ancillaryBlock K _ _) _ _ = _
    rw [map_add]
    rfl
  map_smul' t J := by
    ext p q
    change S (t • ancillaryBlock J _ _) _ _ = _
    rw [map_smul]
    rfl

/-- The ancillary extension is precisely `S ⊗ id` after grouping the two
original Choi indices and the two ancillary indices. -/
theorem ancillaryExtension_eq_kron (S : MatrixMap (a × b) (c × d))
    (J : CMatrix ((a × r) × (b × s))) :
    ancillaryExtension S J =
      (MatrixMap.kron S (LinearMap.id : MatrixMap (r × s) (r × s))
        (J.submatrix (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
          (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))))).submatrix
        (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
        (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by
  ext p q
  rw [Matrix.submatrix_apply, MatrixMap.kron_id_apply]
  change S (ancillaryBlock J _ _) _ _ = _
  rw [MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

/-- Apply the higher-order transformation to an operation with ancillary wires. -/
def ancillaryAction (S : MatrixMap (a × b) (c × d))
    (Φ : MatrixMap (a × r) (b × s)) : MatrixMap (c × r) (d × s) :=
  MatrixMap.ofChoiMatrix (ancillaryExtension S (MatrixMap.choi Φ))

/-- The action has exactly the prescribed extended Choi matrix. -/
@[simp] theorem choi_ancillaryAction (S : MatrixMap (a × b) (c × d))
    (Φ : MatrixMap (a × r) (b × s)) :
    MatrixMap.choi (ancillaryAction S Φ) = ancillaryExtension S (MatrixMap.choi Φ) :=
  MatrixMap.choi_ofChoiMatrix _

/-- Ancillary extension of the identity supermap is the identity. -/
@[simp] theorem ancillaryExtension_id (J : CMatrix ((a × r) × (b × s))) :
    ancillaryExtension (LinearMap.id : MatrixMap (a × b) (a × b)) J = J := rfl

/-- A block of an extended transformation is the transformation of that block. -/
theorem ancillaryBlock_extension (S : MatrixMap (a × b) (c × d))
    (J : CMatrix ((a × r) × (b × s))) (i j : r × s) :
    ancillaryBlock (ancillaryExtension S J) i j = S (ancillaryBlock J i j) := rfl

/-- Extension respects higher-order composition, with the ancillary wires fixed. -/
theorem ancillaryExtension_comp {e : Type u'} {f : Type v'}
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    (T : MatrixMap (c × d) (e × f)) (S : MatrixMap (a × b) (c × d))
    (J : CMatrix ((a × r) × (b × s))) :
    ancillaryExtension (T.comp S) J = ancillaryExtension T (ancillaryExtension S J) := rfl

/-- The identity higher-order map acts identically even on joint operations. -/
@[simp] theorem ancillaryAction_id (Φ : MatrixMap (a × r) (b × s)) :
    ancillaryAction (LinearMap.id : MatrixMap (a × b) (a × b)) Φ = Φ :=
  MatrixMap.ofChoiMatrix_choi Φ

/-- Canonical ancillary action respects composition. -/
theorem ancillaryAction_comp {e : Type u'} {f : Type v'}
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    (T : MatrixMap (c × d) (e × f)) (S : MatrixMap (a × b) (c × d))
    (Φ : MatrixMap (a × r) (b × s)) :
    ancillaryAction (T.comp S) Φ = ancillaryAction T (ancillaryAction S Φ) := by
  simp only [ancillaryAction, MatrixMap.choi_ofChoiMatrix, ancillaryExtension_comp]

/-- A CP Choi-space transformation is positive on every ancillary extension.
This proves the PSD part independently of normalization/admissibility. -/
theorem ancillaryExtension_posSemidef (S : MatrixMap (a × b) (c × d))
    (hS : MatrixMap.IsCompletelyPositive S) (J : CMatrix ((a × r) × (b × s)))
    (hJ : J.PosSemidef) : (ancillaryExtension S J).PosSemidef := by
  rw [ancillaryExtension_eq_kron]
  exact (hS.mapsPositiveUnderAncilla (r × s) _ (hJ.submatrix _)).submatrix _

/-- CP of the Choi-space map gives complete positivity of the resulting
operation, for independent arbitrary finite ancillary input and output types. -/
theorem ancillaryAction_completelyPositive (S : MatrixMap (a × b) (c × d))
    (hS : MatrixMap.IsCompletelyPositive S) (Φ : MatrixMap (a × r) (b × s))
    (hΦ : MatrixMap.IsCompletelyPositive Φ) :
    MatrixMap.IsCompletelyPositive (ancillaryAction S Φ) := by
  rw [MatrixMap.IsCompletelyPositive, choi_ancillaryAction]
  exact ancillaryExtension_posSemidef S hS _ hΦ

/-- The unextended Choi-space action, for comparison with the stabilized action. -/
def action (S : MatrixMap (a × b) (c × d)) (Φ : MatrixMap a b) : MatrixMap c d :=
  MatrixMap.ofChoiMatrix (S (MatrixMap.choi Φ))

/-- Ancillary blocks of a tensor-product operation factor into its two Choi matrices. -/
theorem ancillaryBlock_choi_kron (Φ : MatrixMap a b) (Ψ : MatrixMap r s) (i j : r × s) :
    ancillaryBlock (MatrixMap.choi (MatrixMap.kron Φ Ψ)) i j =
      MatrixMap.choi Ψ i j • MatrixMap.choi Φ := by
  ext p q
  simp only [ancillaryBlock, MatrixMap.choi_kron, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The canonical action fixes the whole ancillary operation on tensor products;
it does not assume joint inputs are product operations. -/
theorem ancillaryAction_kron (S : MatrixMap (a × b) (c × d))
    (Φ : MatrixMap a b) (Ψ : MatrixMap r s) :
    ancillaryAction S (MatrixMap.kron Φ Ψ) = MatrixMap.kron (action S Φ) Ψ := by
  apply MatrixMap.choi_inj
  rw [choi_ancillaryAction]
  ext p q
  change S (ancillaryBlock (MatrixMap.choi (MatrixMap.kron Φ Ψ)) _ _) _ _ = _
  rw [ancillaryBlock_choi_kron, map_smul]
  simp only [MatrixMap.choi_kron, action, MatrixMap.choi_ofChoiMatrix, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The ancillary action is natural under arbitrary relabeling of the spectator
indices, in particular the split/append/permutation equivalences of wire families. -/
theorem ancillaryExtension_reindex {r' : Type u'} {s' : Type v'}
    [Fintype r'] [DecidableEq r'] [Fintype s'] [DecidableEq s']
    (S : MatrixMap (a × b) (c × d)) (J : CMatrix ((a × r) × (b × s)))
    (f : r' → r) (g : s' → s) :
    ancillaryExtension S (J.submatrix (Prod.map (Prod.map id f) (Prod.map id g))
      (Prod.map (Prod.map id f) (Prod.map id g))) =
      (ancillaryExtension S J).submatrix (Prod.map (Prod.map id f) (Prod.map id g))
        (Prod.map (Prod.map id f) (Prod.map id g)) := rfl

/-- A family of admissible Choi operators, parameterized by independent finite
ancillary input and output systems. Recursive higher-order objects may supply
their own family rather than replacing the ancillary action. -/
abbrev AncillaryPredicate (a : Type u) (b : Type v) (r : Type y) (s : Type z) :=
  CMatrix ((a × r) × (b × s)) → Prop

/-- Complete preservation of arbitrary source and target admissibility families.
The quantifiers include empty systems and all finite heterogeneous wire products. -/
def CompletelyPreserves (S : MatrixMap (a × b) (c × d))
    (P : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate a b r s)
    (Q : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate c d r s) : Prop :=
  ∀ (r : Type y) (s : Type z) [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s] (J : CMatrix ((a × r) × (b × s))),
    P r s J → Q r s (ancillaryExtension S J)

/-- Quantum-operation Choi operators, including subnormalized and zero operations. -/
def operationPredicate : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate a b r s :=
  fun _ _ _ _ _ _ J => J.PosSemidef ∧ partialTraceB J ≤ 1

/-- Channel Choi operators: the same positivity condition with exact normalization. -/
def channelPredicate : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate a b r s :=
  fun _ _ _ _ _ _ J => J.PosSemidef ∧ partialTraceB J = 1

/-- Complete admissibility on quantum operations is preservation of their Choi
cone and trace bound under every independent finite ancillary extension. -/
def IsCompletelyAdmissible (S : MatrixMap (a × b) (c × d)) : Prop :=
  CompletelyPreserves S operationPredicate.{u, v, y, z} operationPredicate

/-- Deterministic complete admissibility additionally preserves channels under
all ancillary extensions. This is a predicate for downstream superchannel APIs. -/
def IsCompletelyDeterministic (S : MatrixMap (a × b) (c × d)) : Prop :=
  IsCompletelyAdmissible.{u, v, w, x, y, z} S ∧
    CompletelyPreserves S channelPredicate.{u, v, y, z} channelPredicate

/-- Complete preservation composes for arbitrary admissibility families. -/
theorem CompletelyPreserves.comp {e : Type u'} {f : Type v'}
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    {T : MatrixMap (c × d) (e × f)} {S : MatrixMap (a × b) (c × d)}
    {P : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate a b r s}
    {Q : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate c d r s}
    {R : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate e f r s}
    (hT : CompletelyPreserves T Q R) (hS : CompletelyPreserves S P Q) :
    CompletelyPreserves (T.comp S) P R := by
  intro r s _ _ _ _ J hJ
  rw [ancillaryExtension_comp]
  exact hT r s _ (hS r s J hJ)

/-- Identity preserves any ancillary admissibility family. -/
theorem completelyPreserves_id (P : ∀ (r : Type y) (s : Type z), [Fintype r] → [DecidableEq r] →
      [Fintype s] → [DecidableEq s] → AncillaryPredicate a b r s) :
    CompletelyPreserves (LinearMap.id : MatrixMap (a × b) (a × b)) P P := by
  intro r s _ _ _ _ J hJ
  exact hJ

/-- Extract operation preservation from complete admissibility using the
independent Choi characterization of trace-nonincreasing CP maps. -/
theorem IsCompletelyAdmissible.operation {S : MatrixMap (a × b) (c × d)}
    (hS : IsCompletelyAdmissible.{u, v, w, x, y, z} S)
    (Φ : MatrixMap (a × r) (b × s)) (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    MatrixMap.TraceNonincreasingCP (ancillaryAction S Φ) := by
  apply MatrixMap.traceNonincreasingCP_iff_choi _ |>.mpr
  rw [choi_ancillaryAction]
  exact hS r s _ ((MatrixMap.traceNonincreasingCP_iff_choi Φ).mp hΦ)

/-- The Choi predicate is equivalent to preservation of actual quantum operations
on every joint input, not merely on product operations or unextended channels. -/
theorem isCompletelyAdmissible_iff_operations (S : MatrixMap (a × b) (c × d)) :
    IsCompletelyAdmissible.{u, v, w, x, y, z} S ↔
      ∀ (r : Type y) (s : Type z) [Fintype r] [DecidableEq r]
        [Fintype s] [DecidableEq s] (Φ : MatrixMap (a × r) (b × s)),
        MatrixMap.TraceNonincreasingCP Φ →
          MatrixMap.TraceNonincreasingCP (ancillaryAction S Φ) := by
  constructor
  · intro h r s _ _ _ _ Φ hΦ
    exact h.operation Φ hΦ
  · intro h r s _ _ _ _ J hJ
    have hΦ : MatrixMap.TraceNonincreasingCP (MatrixMap.ofChoiMatrix J) := by
      rw [MatrixMap.traceNonincreasingCP_iff_choi, MatrixMap.choi_ofChoiMatrix]
      exact hJ
    have hout := (MatrixMap.traceNonincreasingCP_iff_choi _).mp (h r s _ hΦ)
    change (ancillaryExtension S J).PosSemidef ∧ partialTraceB (ancillaryExtension S J) ≤ 1
    simpa only [choi_ancillaryAction, MatrixMap.choi_ofChoiMatrix] using hout

/-- Completely admissible transformations compose. -/
theorem IsCompletelyAdmissible.comp {e : Type u'} {f : Type v'}
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    {T : MatrixMap (c × d) (e × f)} {S : MatrixMap (a × b) (c × d)}
    (hT : IsCompletelyAdmissible.{w, x, u', v', y, z} T)
    (hS : IsCompletelyAdmissible.{u, v, w, x, y, z} S) :
    IsCompletelyAdmissible.{u, v, u', v', y, z} (T.comp S) :=
  CompletelyPreserves.comp hT hS

/-- Bundle the channel produced by a deterministic transformation acting on a
joint channel. Complete positivity and trace preservation are proved from Choi data. -/
def IsCompletelyDeterministic.channel {S : MatrixMap (a × b) (c × d)}
    (hS : IsCompletelyDeterministic.{u, v, w, x, y, z} S)
    (N : Channel (a × r) (b × s)) : Channel (c × r) (d × s) where
  map := ancillaryAction S N.map
  completelyPositive := by
    rw [MatrixMap.IsCompletelyPositive, choi_ancillaryAction]
    exact (hS.2 r s _ ⟨N.completelyPositive,
      (MatrixMap.isTracePreserving_iff_partialTraceB_choi N.map).mp N.tracePreserving⟩).1
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (by
    rw [MatrixMap.IsCompletelyPositive, choi_ancillaryAction]
    exact (hS.2 r s _ ⟨N.completelyPositive,
      (MatrixMap.isTracePreserving_iff_partialTraceB_choi N.map).mp N.tracePreserving⟩).1)
  tracePreserving := by
    rw [MatrixMap.isTracePreserving_iff_partialTraceB_choi, choi_ancillaryAction]
    exact (hS.2 r s _ ⟨N.completelyPositive,
      (MatrixMap.isTracePreserving_iff_partialTraceB_choi N.map).mp N.tracePreserving⟩).2

/-- Deterministic complete admissibility is closed under composition. -/
theorem IsCompletelyDeterministic.comp {e : Type u'} {f : Type v'}
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    {T : MatrixMap (c × d) (e × f)} {S : MatrixMap (a × b) (c × d)}
    (hT : IsCompletelyDeterministic.{w, x, u', v', y, z} T)
    (hS : IsCompletelyDeterministic.{u, v, w, x, y, z} S) :
    IsCompletelyDeterministic.{u, v, u', v', y, z} (T.comp S) :=
  ⟨hT.1.comp hS.1, hT.2.comp hS.2⟩

/-- Identity is completely deterministic for every finite ancillary system. -/
theorem isCompletelyDeterministic_id :
    IsCompletelyDeterministic.{u, v, u, v, y, z}
      (LinearMap.id : MatrixMap (a × b) (a × b)) :=
  ⟨completelyPreserves_id _, completelyPreserves_id _⟩

/-- The zero transformation is a valid probabilistic operation transformation. -/
theorem isCompletelyAdmissible_zero :
    IsCompletelyAdmissible.{u, v, w, x, y, z} (0 : MatrixMap (a × b) (c × d)) := by
  intro r s _ _ _ _ J _
  change (0 : CMatrix ((c × r) × (d × s))).PosSemidef ∧ _
  refine ⟨Matrix.PosSemidef.zero, ?_⟩
  have hz : partialTraceB (0 : CMatrix ((c × r) × (d × s))) = 0 := by
    ext i j
    exact Finset.sum_const_zero
  change partialTraceB (0 : CMatrix ((c × r) × (d × s))) ≤ 1
  rw [hz]
  exact Matrix.PosSemidef.one.nonneg

/-- Explicit specialization to arbitrary finite heterogeneous ancillary wire
families. Neither the number of input/output wires nor their dimensions must match. -/
theorem IsCompletelyAdmissible.wireFamily {S : MatrixMap (a × b) (c × d)}
    (hS : IsCompletelyAdmissible.{u, v, w, x, y, z} S) {m n : Nat}
    (R : Fin m → Type y) (T : Fin n → Type z)
    [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (Φ : MatrixMap (a × (∀ i, R i)) (b × (∀ i, T i)))
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    MatrixMap.TraceNonincreasingCP (ancillaryAction S Φ) := hS.operation Φ hΦ

end
end QIT.HigherOrder
