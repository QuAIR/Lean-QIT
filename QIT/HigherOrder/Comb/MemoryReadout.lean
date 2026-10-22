/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.MemoryConnection
public import QIT.Measurements.Readout

/-!
# Projective readout of a common finite memory chain

A coordinate factor of the terminal memory can be measured without changing
the chain's quantum outputs. After physical connection to an inner memory
chain, every outcome is exactly the corresponding complete ancillary action.
The coherent contraction is performed before the final projective readout
[Chiribella2009Networks, comblong-pub.tex:1125-1133] (projective extraction
at proof lines 1213-1216) and
[Chiribella2009Networks, comblong-pub.tex:3302-3314].
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
universe u v w x y
namespace QIT.HigherOrder
open Comb

section Readout

variable {n : Nat} {I O E : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  {K : Type v} {ι : Type w}
  [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]

/-- Measure a coordinate flag in the terminal memory of a fixed chain,
discarding only the remaining memory and retaining every quantum output. -/
def MemoryChain.readoutInstrument (c : MemoryChain I O E)
    (e : E (Fin.last n) ≃ K × ι) : FiniteInstrument (∀ j, I j) (∀ j, O j) ι :=
  (c.coherentIsometry.reindexOutput
    (Equiv.prodCongr (Equiv.refl _) e)).readoutInstrument

/-- The Choi operator of a terminal flag outcome is the Gram matrix of the
coherent Kraus amplitudes with that flag fixed. -/
theorem MemoryChain.choi_readoutInstrument (c : MemoryChain I O E)
    (e : E (Fin.last n) ≃ K × ι) (i : ι) (p q : Space I O) :
    MatrixMap.choi ((c.readoutInstrument e).branch i) p q =
      ∑ k : K, c.kraus (e.symm (k, i)) p.2 p.1 *
        star (c.kraus (e.symm (k, i)) q.2 q.1) := by
  rw [MemoryChain.readoutInstrument, ReferenceIsometry.readoutInstrument_branch_choi]
  rfl

end Readout

/-- Keep the two residual memories together and expose the outer flag as the
last factor. No memory coordinate is identified or discarded by this map. -/
def readoutMemoryEquiv {A B K ι : Type*} (e : A ≃ K × ι) :
    A × B ≃ (K × B) × ι where
  toFun p := (((e p.1).1, p.2), (e p.1).2)
  invFun p := (e.symm (p.1.1, p.2), p.1.2)
  left_inv p := by simp
  right_inv p := by simp

section Connection

variable {n : Nat} {I O E : Fin (n + 2) → Type u} {F : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
  {K : Type v} {ι : Type w}
  [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
  {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Physically alternate the two memory chains, then projectively measure the
outer terminal flag while retaining both boundary spectator systems. -/
def MemoryChain.connectReadoutInstrument (c : MemoryChain I O E)
    (e : E (Fin.last (n + 1)) ≃ K × ι)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F) :
    FiniteInstrument (I 0 × r) (O (Fin.last (n + 1)) × s) ι :=
  ((c.connectIsometry d).reindexOutput
    (Equiv.prodCongr (Equiv.refl _) (readoutMemoryEquiv e))).readoutInstrument

private theorem readout_sum_swap_pairs {A B C D E F : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    (H : A → B → C → D → E → F → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, H a b c d e f) =
      ∑ e, ∑ f, ∑ c, ∑ d, ∑ a, ∑ b, H a b c d e f := by
  let L : (A × B) → (C × D) → (E × F) → ℂ :=
    fun x y z ↦ H x.1 x.2 y.1 y.2 z.1 z.2
  have h : (∑ x, ∑ y, ∑ z, L x y z) = ∑ z, ∑ y, ∑ x, L x y z := by
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type, L] using h

set_option backward.isDefEq.respectTransparency false in
/-- Every outcome of the connected projective readout has exactly the
complete ancillary action of the same outcome of the fixed outer chain.
The inner channel may have arbitrary independent and jointly correlated
boundary spectator systems. -/
theorem MemoryChain.connectReadoutInstrument_choi (c : MemoryChain I O E)
    (e : E (Fin.last (n + 1)) ≃ K × ι)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F) (i : ι) :
    MatrixMap.choi ((c.connectReadoutInstrument e d).branch i) =
      ancillaryExtension
        (actionMap I O (MatrixMap.choi ((c.readoutInstrument e).branch i))) d.jointChoi := by
  classical
  ext p q
  rcases p with ⟨⟨a₀, ρ⟩, ⟨bₙ, σ⟩⟩
  rcases q with ⟨⟨a₀', ρ'⟩, ⟨bₙ', σ'⟩⟩
  rw [MemoryChain.connectReadoutInstrument, ReferenceIsometry.readoutInstrument_branch_choi]
  change (∑ k : K × F (Fin.last n),
    (c.connectIsometry d).matrix ((bₙ, σ), (e.symm (k.1, i), k.2)) (a₀, ρ) *
      star ((c.connectIsometry d).matrix
        ((bₙ', σ'), (e.symm (k.1, i), k.2)) (a₀', ρ'))) = _
  simp only [Fintype.sum_prod_type, MemoryChain.connectIsometry_matrix]
  change _ = ∑ z : Space (innerInput O) (innerOutput I),
    ∑ z' : Space (innerInput O) (innerOutput I),
      d.jointChoi ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ')) *
        MatrixMap.choi ((c.readoutInstrument e).branch i)
          (Fin.cons a₀ z.2, Fin.snoc z.1 bₙ)
          (Fin.cons a₀' z'.2, Fin.snoc z'.1 bₙ')
  simp only [Fintype.sum_prod_type, MemoryChain.jointChoi_apply,
    MemoryChain.choi_readoutInstrument, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [readout_sum_swap_pairs]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a' _
  apply Finset.sum_congr rfl
  intro b' _
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_congr rfl fun f _ ↦ by ring

end Connection

section UnitConnection

variable {n : Nat} {I O E : Fin (n + 2) → Type u} {F : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
  {K : Type v} {ι : Type w}
  [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
/-- With trivial spectators, the same connected outcome is exactly the
existing shared-wire link action, retaining its entire output Choi matrix. -/
theorem MemoryChain.connectReadoutInstrument_choi_linkAction (c : MemoryChain I O E)
    (e : E (Fin.last (n + 1)) ≃ K × ι)
    (d : MemoryChain (boundaryInput (innerInput O) PUnit)
      (boundaryOutput (innerOutput I) PUnit) F) (i : ι) :
    (MatrixMap.choi ((c.connectReadoutInstrument e d).branch i)).submatrix
      (fun p ↦ ((p.1, PUnit.unit), (p.2, PUnit.unit)))
      (fun p ↦ ((p.1, PUnit.unit), (p.2, PUnit.unit))) =
      linkAction I O (MatrixMap.choi ((c.readoutInstrument e).branch i))
        (fun z z' ↦ d.jointChoi ((z.1, PUnit.unit), (z.2, PUnit.unit))
          ((z'.1, PUnit.unit), (z'.2, PUnit.unit))) := by
  rw [MemoryChain.connectReadoutInstrument_choi, ← actionMap_eq_linkAction]
  rfl

end UnitConnection

section JointReadoutChoi

variable {m : Nat} {P Q F : Fin (m + 1) → Type u}
  [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]
  [∀ k, Fintype (Q k)] [∀ k, DecidableEq (Q k)]
  [∀ k, Fintype (F k)] [∀ k, DecidableEq (F k)]
  {L : Type v} {κ : Type w}
  [Fintype L] [DecidableEq L] [Fintype κ] [DecidableEq κ]
  {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- The Choi operator of an inner terminal-flag outcome, with independent
boundary systems grouped according to the complete ancillary-action convention. -/
def MemoryChain.jointReadoutChoi
    (d : MemoryChain (boundaryInput P r) (boundaryOutput Q s) F)
    (f : F (Fin.last m) ≃ L × κ) (j : κ) :
    CMatrix (((∀ k, P k) × r) × ((∀ k, Q k) × s)) :=
  WireFam.matReindex (boundaryEquiv P Q r s)
    (MatrixMap.choi ((d.readoutInstrument f).branch j))

/-- Boundary-grouped outcome Choi entries retain coherence in every wire
and spectator coordinate while fixing only the measured terminal flag. -/
theorem MemoryChain.jointReadoutChoi_apply
    (d : MemoryChain (boundaryInput P r) (boundaryOutput Q s) F)
    (f : F (Fin.last m) ≃ L × κ) (j : κ)
    (a a' : ∀ k, P k) (b b' : ∀ k, Q k)
    (ρ ρ' : r) (σ σ' : s) :
    d.jointReadoutChoi f j ((a, ρ), (b, σ)) ((a', ρ'), (b', σ')) =
      ∑ l : L, d.kraus (f.symm (l, j)) (boundaryOutputLift Q b σ)
          (boundaryInputLift P a ρ) *
        star (d.kraus (f.symm (l, j)) (boundaryOutputLift Q b' σ')
          (boundaryInputLift P a' ρ')) := by
  have hi (a : ∀ k, P k) (ρ : r) :
      (boundaryInputEquiv P r).symm (a, ρ) = boundaryInputLift P a ρ := by
    apply (boundaryInputEquiv P r).injective
    rw [Equiv.apply_symm_apply, boundaryInputEquiv_lift]
  have ho (b : ∀ k, Q k) (σ : s) :
      (boundaryOutputEquiv Q s).symm (b, σ) = boundaryOutputLift Q b σ := by
    apply (boundaryOutputEquiv Q s).injective
    rw [Equiv.apply_symm_apply, boundaryOutputEquiv_lift]
  simp only [MemoryChain.jointReadoutChoi, WireFam.matReindex_apply, boundaryEquiv,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    MemoryChain.choi_readoutInstrument, hi, ho]

end JointReadoutChoi

/-- Separate both terminal flags from both unobserved memories by a finite
basis equivalence, preserving every coherent amplitude. -/
def jointReadoutMemoryEquiv {A B K L ι κ : Type*}
    (e : A ≃ K × ι) (f : B ≃ L × κ) : A × B ≃ (K × L) × (ι × κ) where
  toFun p := (((e p.1).1, (f p.2).1), ((e p.1).2, (f p.2).2))
  invFun p := (e.symm (p.1.1, p.2.1), f.symm (p.1.2, p.2.2))
  left_inv p := by simp
  right_inv p := by simp

section JointConnection

variable {n : Nat} {I O E : Fin (n + 2) → Type u} {F : Fin (n + 1) → Type u}
  [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
  [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
  [∀ k, Fintype (E k)] [∀ k, DecidableEq (E k)]
  [∀ k, Fintype (F k)] [∀ k, DecidableEq (F k)]
  {K : Type v} {ι : Type w} {L : Type x} {κ : Type y}
  [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L] [Fintype κ] [DecidableEq κ]
  {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Physically connect two chains before the joint coordinate measurement of
their terminal flags. Both residual memories are discarded, while the quantum
output and its independent spectator are retained. -/
def MemoryChain.connectJointReadoutInstrument (c : MemoryChain I O E)
    (e : E (Fin.last (n + 1)) ≃ K × ι)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F)
    (f : F (Fin.last n) ≃ L × κ) :
    FiniteInstrument (I 0 × r) (O (Fin.last (n + 1)) × s) (ι × κ) :=
  ((c.connectIsometry d).reindexOutput
    (Equiv.prodCongr (Equiv.refl _) (jointReadoutMemoryEquiv e f))).readoutInstrument

set_option backward.isDefEq.respectTransparency false in
/-- The joint physical outcome equals the complete ancillary action of the
outer outcome on the inner outcome. Selecting an inner flag preserves the
unnormalized operator, including its boundary spectator correlations. -/
theorem MemoryChain.connectJointReadoutInstrument_choi (c : MemoryChain I O E)
    (e : E (Fin.last (n + 1)) ≃ K × ι)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F)
    (f : F (Fin.last n) ≃ L × κ) (i : ι) (j : κ) :
    MatrixMap.choi ((c.connectJointReadoutInstrument e d f).branch (i, j)) =
      ancillaryExtension
        (actionMap I O (MatrixMap.choi ((c.readoutInstrument e).branch i)))
        (d.jointReadoutChoi f j) := by
  classical
  ext p q
  rcases p with ⟨⟨a₀, ρ⟩, ⟨bₙ, σ⟩⟩
  rcases q with ⟨⟨a₀', ρ'⟩, ⟨bₙ', σ'⟩⟩
  rw [MemoryChain.connectJointReadoutInstrument,
    ReferenceIsometry.readoutInstrument_branch_choi]
  change (∑ k : K × L,
    (c.connectIsometry d).matrix
      ((bₙ, σ), (e.symm (k.1, i), f.symm (k.2, j))) (a₀, ρ) *
      star ((c.connectIsometry d).matrix
        ((bₙ', σ'), (e.symm (k.1, i), f.symm (k.2, j))) (a₀', ρ'))) = _
  simp only [Fintype.sum_prod_type, MemoryChain.connectIsometry_matrix]
  change _ = ∑ z : Space (innerInput O) (innerOutput I),
    ∑ z' : Space (innerInput O) (innerOutput I),
      d.jointReadoutChoi f j ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ')) *
        MatrixMap.choi ((c.readoutInstrument e).branch i)
          (Fin.cons a₀ z.2, Fin.snoc z.1 bₙ)
          (Fin.cons a₀' z'.2, Fin.snoc z'.1 bₙ')
  simp only [Fintype.sum_prod_type, MemoryChain.jointReadoutChoi_apply,
    MemoryChain.choi_readoutInstrument, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [readout_sum_swap_pairs]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a' _
  apply Finset.sum_congr rfl
  intro b' _
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_congr rfl fun l _ ↦ by ring

end JointConnection

end QIT.HigherOrder
