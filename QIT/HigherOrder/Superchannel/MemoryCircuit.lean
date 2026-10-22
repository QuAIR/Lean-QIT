/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HigherOrder.Comb.Realization
public import QIT.Channels.Superchannel.Circuit

/-!
# Two-tooth memory chains as pre- and post-processing circuits

The two links of a memory chain are the preprocessing and postprocessing
isometries of a one-slot superchannel. Explicit equivalences identify the
single inner input and output configurations with ordinary system labels.
The postprocessing input places the slot output before the carried memory,
matching `prePostAction` and the source formula's inserted operation tensored
with the identity on memory.

The resulting circuit has exactly the comb action on every linear input map,
not only channels. The proof sums internal memory amplitudes coherently before
discarding the terminal environment. Empty wires and memories are allowed.
This specializes the finite memory-chain realization to the circuit in
[Chiribella2008Supermaps, VersioneArchivio.tex:340-349].
-/

@[expose] public section

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
universe u
namespace QIT.HigherOrder.MemoryChain
open Comb

variable {I O E : Fin 2 → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  {a b : Type u} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

/-- The first link, with its output wire read through an explicit equivalence
from one-wire configurations to the inserted operation's input system. -/
def preIsometry (c : MemoryChain I O E)
    (ea : (∀ j, innerInput O j) ≃ a) : ReferenceIsometry (I 0) (a × E 0) :=
  linkCongr (c.link 0) (Equiv.refl _)
    (Equiv.prodCongr ((oneConfigEquiv (innerInput O)).symm.trans ea) (Equiv.refl _))

/-- The second link, with the inserted operation's output placed before memory.
The permutation changes coordinates only; this is the original link isometry. -/
def postIsometry (c : MemoryChain I O E)
    (eb : (∀ j, innerOutput I j) ≃ b) :
    ReferenceIsometry (b × E 0) (O 1 × E 1) :=
  linkCongr (c.link 1)
    ((Equiv.prodComm _ _).trans
      (Equiv.prodCongr ((oneConfigEquiv (innerOutput I)).symm.trans eb) (Equiv.refl _)))
    (Equiv.refl _)

/-- Preprocessing matrix entries are the first link entries. -/
@[simp] theorem preIsometry_matrix (c : MemoryChain I O E)
    (ea : (∀ j, innerInput O j) ≃ a) (x : a) (m : E 0) (i : I 0) :
    (c.preIsometry ea).matrix (x, m) i =
      (c.link 0).matrix (ea.symm x 0, m) i := rfl

/-- Postprocessing matrix entries expose the memory/slot permutation. -/
@[simp] theorem postIsometry_matrix (c : MemoryChain I O E)
    (eb : (∀ j, innerOutput I j) ≃ b) (y : b) (m : E 0) (o : O 1) (e : E 1) :
    (c.postIsometry eb).matrix (o, e) (y, m) =
      (c.link 1).matrix (o, e) (m, eb.symm y 0) := rfl

/-- A two-link amplitude sums the shared memory coherently while retaining
the final environment label. -/
theorem kraus_two (c : MemoryChain I O E)
    (ea : (∀ j, innerInput O j) ≃ a)
    (eb : (∀ j, innerOutput I j) ≃ b)
    (x : a) (y : b) (i : I 0) (o : O 1) (e : E 1) :
    c.kraus e (Fin.snoc (ea.symm x) o) (Fin.cons i (eb.symm y)) =
      ∑ m, (c.preIsometry ea).matrix (x, m) i *
        (c.postIsometry eb).matrix (o, e) (y, m) := by
  rw [MemoryChain.kraus_step]
  simp only [MemoryChain.kraus_one, Fin.init_snoc, Fin.snoc_last,
    Fin.cons_last, preIsometry_matrix, postIsometry_matrix]
  rfl

/-- The comb action in ordinary system coordinates is the contraction of
the two-link amplitudes, with no positivity assumption on the input matrix. -/
theorem actionMap_reindexed_apply (c : MemoryChain I O E)
    (ea : (∀ j, innerInput O j) ≃ a)
    (eb : (∀ j, innerOutput I j) ≃ b)
    (X : CMatrix (a × b)) (i i' : I 0) (o o' : O 1) :
    actionMap I O (MatrixMap.choi c.chainMap)
      (X.submatrix (Equiv.prodCongr ea eb) (Equiv.prodCongr ea eb))
        (i, o) (i', o') =
      ∑ x : a × b, ∑ x' : a × b,
        X x x' * ∑ e,
          (∑ m, (c.preIsometry ea).matrix (x.1, m) i *
            (c.postIsometry eb).matrix (o, e) (x.2, m)) *
          star (∑ m, (c.preIsometry ea).matrix (x'.1, m) i' *
            (c.postIsometry eb).matrix (o', e) (x'.2, m)) := by
  change (∑ x : Space (innerInput O) (innerOutput I),
    ∑ x' : Space (innerInput O) (innerOutput I),
      X ((Equiv.prodCongr ea eb) x) ((Equiv.prodCongr ea eb) x') *
        MatrixMap.choi c.chainMap (Fin.cons i x.2, Fin.snoc x.1 o)
          (Fin.cons i' x'.2, Fin.snoc x'.1 o')) = _
  rw [← Equiv.sum_comp (Equiv.prodCongr ea eb).symm]
  apply Finset.sum_congr rfl
  rintro ⟨x, y⟩ _
  rw [← Equiv.sum_comp (Equiv.prodCongr ea eb).symm]
  apply Finset.sum_congr rfl
  rintro ⟨x', y'⟩ _
  simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.apply_symm_apply, MemoryChain.choi_chainMap_apply, kraus_two]
  rfl

private theorem sum_circuit_shuffle {A B C D E F G : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] [Fintype G]
    (H : A → B → C → D → E → F → G → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, H a b c d e f g) =
      ∑ b, ∑ g, ∑ d, ∑ f, ∑ e, ∑ a, ∑ c, H a b c d e f g := by
  let t : (A × B × C × D × E × F × G) ≃ (B × G × D × F × E × A × C) :=
    { toFun := fun ⟨a, b, c, d, e, f, g⟩ ↦ (b, g, d, f, e, a, c)
      invFun := fun ⟨b, g, d, f, e, a, c⟩ ↦ (a, b, c, d, e, f, g)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let K : (A × B × C × D × E × F × G) → ℂ :=
    fun ⟨a, b, c, d, e, f, g⟩ ↦ H a b c d e f g
  simpa only [Fintype.sum_prod_type, t, K, Equiv.symm_mk, Equiv.coe_fn_mk] using
    (Equiv.sum_comp t.symm K).symm

private theorem ofReferenceIsometry_single_apply {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (V : ReferenceIsometry A B) (i i' : A) (o o' : B) :
    MatrixMap.ofReferenceIsometry V (Matrix.single i i' 1) o o' =
      V.matrix o i * star (V.matrix o' i') := by
  rw [MatrixMap.ofReferenceIsometry_apply]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
    Matrix.of_apply, mul_ite, ite_and]

/-- Preprocessing, the inserted operation tensored with the identity on memory,
and postprocessing with final discard recover the entire comb action. The
identity holds for every linear input operation, including all trace-decreasing
quantum operations [Chiribella2008Supermaps, VersioneArchivio.tex:340-349]. -/
theorem prePostAction_eq_reindexedAction (c : MemoryChain I O E)
    (ea : (∀ j, innerInput O j) ≃ a)
    (eb : (∀ j, innerOutput I j) ≃ b)
    (Φ : MatrixMap a b) :
    prePostAction (MatrixMap.ofReferenceIsometry (c.preIsometry ea))
      (c.postIsometry eb).outputChannel.map Φ =
    MatrixMap.ofChoiMatrix (actionMap I O (MatrixMap.choi c.chainMap)
      ((MatrixMap.choi Φ).submatrix (Equiv.prodCongr ea eb) (Equiv.prodCongr ea eb))) := by
  apply MatrixMap.choi_inj
  rw [MatrixMap.choi_ofChoiMatrix]
  ext p q
  rcases p with ⟨i, o⟩
  rcases q with ⟨i', o'⟩
  rw [choi_prePostAction_apply, c.actionMap_reindexed_apply ea eb]
  simp only [ofReferenceIsometry_single_apply]
  have hpost (z z' : b × E 0) :
      (c.postIsometry eb).outputChannel.map (Matrix.single z z' 1) o o' =
        ∑ e, (c.postIsometry eb).matrix (o, e) z *
          star ((c.postIsometry eb).matrix (o', e) z') :=
    outputChannel_choi_apply (c.postIsometry eb) z z' o o'
  simp only [hpost, Fintype.sum_prod_type, MatrixMap.choi,
    star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [sum_circuit_shuffle]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

end QIT.HigherOrder.MemoryChain
