/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.CompleteAdmissibility

/-!
# Relabeling and ancillary universes

Complete channel preservation does not depend on the universes used to quantify
finite ancillary systems. Each finite system can be relabeled by a lifted finite
ordinal, and the ancillary extension is natural under these relabelings.
This includes empty ancillary input and output systems.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT.HigherOrder

universe u v w x y z u' v' y' z'

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
/-- Partial trace commutes with independent equivalences on the retained and
traced systems. The traced equivalence reindexes the entire finite sum. -/
theorem partialTraceB_submatrix_prodEquiv {a' : Type u'} {b' : Type v'}
    [Fintype b']
    (J : CMatrix (a × b)) (e : a' ≃ a) (f : b' ≃ b) :
    partialTraceB (J.submatrix (Equiv.prodCongr e f) (Equiv.prodCongr e f)) =
      (partialTraceB J).submatrix e e := by
  ext i j
  exact Equiv.sum_comp f (fun k => J (e i, k) (e j, k))

omit [Fintype a] [DecidableEq b] in
/-- Relabeling both ancillary systems preserves the channel Choi predicate. -/
theorem channelPredicate_submatrix_ancillary
    {r : Type y} {s : Type z} {r' : Type y'} {s' : Type z'}
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    [Fintype r'] [DecidableEq r'] [Fintype s'] [DecidableEq s']
    (J : CMatrix ((a × r) × (b × s))) (e : r' ≃ r) (f : s' ≃ s)
    (hJ : channelPredicate r s J) :
    channelPredicate r' s'
      (J.submatrix (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl a) e)
        (Equiv.prodCongr (Equiv.refl b) f))
        (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl a) e)
          (Equiv.prodCongr (Equiv.refl b) f))) := by
  refine ⟨hJ.1.submatrix _, ?_⟩
  rw [partialTraceB_submatrix_prodEquiv, hJ.2, Matrix.submatrix_one_equiv]

/-- Complete preservation of channels is independent of the ancillary universe
levels: arbitrary finite systems can be transported through lifted finite ordinals. -/
theorem CompletelyPreserves.channels_changeUniverse
    {S : MatrixMap (a × b) (c × d)}
    (hS : CompletelyPreserves S channelPredicate.{u, v, y, z} channelPredicate) :
    CompletelyPreserves S channelPredicate.{u, v, y', z'} channelPredicate := by
  intro r s _ _ _ _ J hJ
  let r₀ := ULift.{y} (Fin (Fintype.card r))
  let s₀ := ULift.{z} (Fin (Fintype.card s))
  let e : r₀ ≃ r := Equiv.ulift.trans (Fintype.equivFin r).symm
  let f : s₀ ≃ s := Equiv.ulift.trans (Fintype.equivFin s).symm
  let inEquiv := Equiv.prodCongr (Equiv.prodCongr (Equiv.refl a) e)
    (Equiv.prodCongr (Equiv.refl b) f)
  let outEquiv := Equiv.prodCongr (Equiv.prodCongr (Equiv.refl c) e)
    (Equiv.prodCongr (Equiv.refl d) f)
  let J₀ := J.submatrix inEquiv inEquiv
  have hJ₀ : channelPredicate r₀ s₀ J₀ :=
    channelPredicate_submatrix_ancillary J e f hJ
  have hK := hS r₀ s₀ J₀ hJ₀
  have hExt : ancillaryExtension S J₀ =
      (ancillaryExtension S J).submatrix outEquiv outEquiv :=
    ancillaryExtension_reindex S J e f
  have hback := channelPredicate_submatrix_ancillary
    (ancillaryExtension S J₀) e.symm f.symm hK
  rw [hExt] at hback
  change channelPredicate r s
    (((ancillaryExtension S J).submatrix outEquiv outEquiv).submatrix
      outEquiv.symm outEquiv.symm) at hback
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] using hback

end

end QIT.HigherOrder
