/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Basic
public import QIT.Core.Map.LinkProductPositivity

/-!
# Directional matching of comb boundaries

A `WireJoin` connects outputs of either comb to inputs of the other, with
no repeated endpoint. It describes the algebraic contraction only: causal
ordering and normalization of an exposed boundary are separate properties.
The resulting matrix retains the exact complement layout of `WireMatch`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder.Comb
open QIT.WireFam

/-- Two disjoint directional groups of output-to-input connections. Endpoints
in different groups occupy different input/output blocks, so the individual
injectivity conditions also exclude all repeated endpoints in the flattened
matching. Neither acyclicity nor normalization is asserted by this data. -/
structure WireJoin {nA nB : Nat} (I O : Fin nA → Type u) (P Q : Fin nB → Type u) where
  /-- Number of connections from the first comb to the second. -/
  ab : Nat
  /-- Number of connections from the second comb to the first. -/
  ba : Nat
  outA : Fin ab → Fin nA
  inB : Fin ab → Fin nB
  outB : Fin ba → Fin nB
  inA : Fin ba → Fin nA
  outA_injective : Function.Injective outA
  inB_injective : Function.Injective inB
  outB_injective : Function.Injective outB
  inA_injective : Function.Injective inA
  equivAB : ∀ k, O (outA k) ≃ P (inB k)
  equivBA : ∀ k, Q (outB k) ≃ I (inA k)

namespace WireJoin
variable {nA nB : Nat} {I O : Fin nA → Type u} {P Q : Fin nB → Type u}

/-- Flatten the directional connections into the general matching API. The
first block connects `O` to `P`; the second connects `I` to `Q`, reversing the
basis equivalence of the corresponding output-to-input connection. -/
def toWireMatch (j : WireJoin I O P Q) : WireMatch (append I O) (append P Q) where
  s := j.ab + j.ba
  ι₁ := Fin.addCases (fun k => Fin.natAdd nA (j.outA k))
    (fun k => Fin.castAdd nA (j.inA k))
  ι₂ := Fin.addCases (fun k => Fin.castAdd nB (j.inB k))
    (fun k => Fin.natAdd nB (j.outB k))
  hι₁ := by
    intro k l h
    induction k using Fin.addCases with
    | left k =>
      induction l using Fin.addCases with
      | left l =>
        simp only [Fin.addCases_left, Fin.natAdd_inj] at h
        exact congrArg (Fin.castAdd j.ba) (j.outA_injective h)
      | right l =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
    | right k =>
      induction l using Fin.addCases with
      | left l =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      | right l =>
        simp only [Fin.addCases_right, Fin.castAdd_inj] at h
        exact congrArg (Fin.natAdd j.ab) (j.inA_injective h)
  hι₂ := by
    intro k l h
    induction k using Fin.addCases with
    | left k =>
      induction l using Fin.addCases with
      | left l =>
        simp only [Fin.addCases_left, Fin.castAdd_inj] at h
        exact congrArg (Fin.castAdd j.ba) (j.inB_injective h)
      | right l =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
    | right k =>
      induction l using Fin.addCases with
      | left l =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      | right l =>
        simp only [Fin.addCases_right, Fin.natAdd_inj] at h
        exact congrArg (Fin.natAdd j.ab) (j.outB_injective h)
  e := by
    intro k
    induction k using Fin.addCases with
    | left k =>
      simp only [Fin.addCases_left, append_natAdd, append_castAdd]
      exact j.equivAB k
    | right k =>
      simp only [Fin.addCases_right, append_natAdd, append_castAdd]
      exact (j.equivBA k).symm

/-- The first group selects the first comb's outputs. -/
@[simp] theorem toWireMatch_outA (j : WireJoin I O P Q) (k : Fin j.ab) :
    j.toWireMatch.ι₁ (Fin.castAdd j.ba k) = Fin.natAdd nA (j.outA k) := by
  simp [toWireMatch]

/-- The first group selects the second comb's inputs. -/
@[simp] theorem toWireMatch_inB (j : WireJoin I O P Q) (k : Fin j.ab) :
    j.toWireMatch.ι₂ (Fin.castAdd j.ba k) = Fin.castAdd nB (j.inB k) := by
  simp [toWireMatch]

/-- The second group selects the first comb's inputs. -/
@[simp] theorem toWireMatch_inA (j : WireJoin I O P Q) (k : Fin j.ba) :
    j.toWireMatch.ι₁ (Fin.natAdd j.ab k) = Fin.castAdd nA (j.inA k) := by
  simp [toWireMatch]

/-- The second group selects the second comb's outputs. -/
@[simp] theorem toWireMatch_outB (j : WireJoin I O P Q) (k : Fin j.ba) :
    j.toWireMatch.ι₂ (Fin.natAdd j.ab k) = Fin.natAdd nB (j.outB k) := by
  simp [toWireMatch]

/-- The exact array of unconnected first-comb and second-comb wires. This is
not a paired input/output boundary. -/
abbrev RawSpace (j : WireJoin I O P Q) :=
  ∀ i, append j.toWireMatch.complFam₁ j.toWireMatch.complFam₂ i

/-- Contract the selected output/input pairs by the general link product,
retaining its complement layout without claiming normalized comb structure. -/
def rawComp [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
    (j : WireJoin I O P Q) (J : CMatrix (Space I O)) (K : CMatrix (Space P Q)) :
    CMatrix j.RawSpace :=
  j.toWireMatch.linkProduct (matReindex (splitAppendEquiv I O).symm J)
    (matReindex (splitAppendEquiv P Q).symm K)

/-- Positivity survives the matching contraction. Empty wire types are allowed. -/
theorem rawComp_posSemidef [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
    [∀ i, Fintype (P i)] [∀ i, Fintype (Q i)]
    (j : WireJoin I O P Q) {J : CMatrix (Space I O)} {K : CMatrix (Space P Q)}
    (hJ : J.PosSemidef) (hK : K.PosSemidef) : (j.rawComp J K).PosSemidef := by
  classical
  unfold rawComp WireMatch.linkProduct
  exact linkProduct_posSemidef
    (matReindex_posSemidef _ (matReindex_posSemidef _ hJ))
    (matReindex_posSemidef _ (matReindex_posSemidef _ hK))

/-- Entrywise contraction in the original two comb configurations. -/
theorem rawComp_apply [∀ i, Fintype (I i)] [∀ i, Fintype (O i)]
    (j : WireJoin I O P Q) (J : CMatrix (Space I O)) (K : CMatrix (Space P Q))
    (g g' : ∀ i, j.toWireMatch.complFam₁ i)
    (w w' : ∀ i, j.toWireMatch.complFam₂ i) :
    j.rawComp J K
        ((splitAppendEquiv j.toWireMatch.complFam₁ j.toWireMatch.complFam₂).symm (g, w))
        ((splitAppendEquiv j.toWireMatch.complFam₁ j.toWireMatch.complFam₂).symm (g', w')) =
      ∑ z : ∀ k, j.toWireMatch.connFam₁ k, ∑ z' : ∀ k, j.toWireMatch.connFam₁ k,
        J (splitAppendEquiv I O (j.toWireMatch.read₁ (g, z')))
          (splitAppendEquiv I O (j.toWireMatch.read₁ (g', z))) *
        K (splitAppendEquiv P Q (j.toWireMatch.read₂ z' w))
          (splitAppendEquiv P Q (j.toWireMatch.read₂ z w')) := by
  rw [rawComp, WireMatch.linkProduct_apply]
  rfl

end WireJoin
end QIT.HigherOrder.Comb
end
