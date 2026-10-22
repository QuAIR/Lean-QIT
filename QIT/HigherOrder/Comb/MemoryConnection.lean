/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Characterization
public import QIT.Channels.MemoryChain
public import QIT.Channels.Stinespring

/-!
# Physical connections of finite memory chains

Connections compose the local isometries in causal order and discard only
terminal memories. The Choi/action equality is a theorem about this composition.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
universe u
namespace QIT.HigherOrder
open Comb

variable {n : Nat} {I O E : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- Chain Choi entries in the input/output configuration convention. -/
theorem MemoryChain.choi_chainMap_apply (c : MemoryChain I O E)
    (i i' : ∀ j, I j) (o o' : ∀ j, O j) :
    MatrixMap.choi c.chainMap (i, o) (i', o') =
      ∑ e, c.kraus e o i * star (c.kraus e o' i') := by
  simp only [MemoryChain.chainMap, MatrixMap.choi_ofKraus,
    Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply]

section BoundaryMemory

variable {s : Type u} [Fintype s] [DecidableEq s]

/-- A boundary output spectator can be carried in the last memory instead. -/
def boundaryMemoryEquiv (O E : Fin (n + 1) → Type u) (s : Type u)
    (j : Fin (n + 1)) : boundaryOutput O s j × E j ≃ O j × boundaryOutput E s j := by
  induction j using Fin.lastCases with
  | last =>
    let eO : boundaryOutput O s (Fin.last n) ≃ O (Fin.last n) × s :=
      Equiv.cast (by simp [boundaryOutput])
    let eE : boundaryOutput E s (Fin.last n) ≃ E (Fin.last n) × s :=
      Equiv.cast (by simp [boundaryOutput])
    let shuffle : (O (Fin.last n) × s) × E (Fin.last n) ≃
        O (Fin.last n) × (E (Fin.last n) × s) :=
      { toFun := fun p ↦ (p.1.1, (p.2, p.1.2))
        invFun := fun p ↦ ((p.1, p.2.2), p.2.1)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact (Equiv.prodCongr eO (Equiv.refl _)).trans
      (shuffle.trans (Equiv.prodCongr (Equiv.refl _) eE.symm))
  | cast k =>
    exact Equiv.prodCongr
      (Equiv.cast (show boundaryOutput O s k.castSucc = O k.castSucc by
        simp [boundaryOutput]))
      (Equiv.cast (show boundaryOutput E s k.castSucc = E k.castSucc by
        simp [boundaryOutput]).symm)

/-- Moving the output spectator into the terminal environment changes no
local operation: it only regroups the final output factors. -/
def MemoryChain.absorbOutputSpectator
    (d : MemoryChain I (boundaryOutput O s) E) :
    MemoryChain I O (boundaryOutput E s) where
  link := Fin.cases
    (MemoryChain.linkCongr (d.link 0) (Equiv.refl _) (boundaryMemoryEquiv O E s 0))
    (fun k ↦ MemoryChain.linkCongr (d.link k.succ)
      (Equiv.prodCongr (Equiv.cast
        (show boundaryOutput E s k.castSucc = E k.castSucc by simp [boundaryOutput]).symm)
        (Equiv.refl _))
      (boundaryMemoryEquiv O E s k.succ))

end BoundaryMemory

section Interleaving

variable {B M F₀ C F D E₁ : Type u}
  [Fintype B] [DecidableEq B] [Fintype M] [DecidableEq M]
  [Fintype F₀] [DecidableEq F₀] [Fintype C] [DecidableEq C]
  [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
  [Fintype E₁] [DecidableEq E₁]

/-- Consume the current outer output with an inner interaction, then the next
outer interaction, carrying the other memory past each operation. -/
def interleavedStep (W : ReferenceIsometry (F₀ × B) (C × F))
    (V : ReferenceIsometry (M × C) (D × E₁)) :
    ReferenceIsometry (B × (M × F₀)) (D × (E₁ × F)) :=
  MemoryChain.linkCongr
    ((V.prod (ReferenceIsometry.ofInjective (id : F → F) Function.injective_id)).comp
      (MemoryChain.linkCongr
        ((ReferenceIsometry.ofInjective (id : M → M) Function.injective_id).prod W)
        { toFun := fun p ↦ (p.2.2, (p.1, p.2.1))
          invFun := fun p ↦ (p.2.1, (p.2.2, p.1))
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
        (Equiv.prodAssoc M C F).symm))
    (Equiv.refl _) (Equiv.prodAssoc D E₁ F)

/-- Matrix entries of the physical two-interaction step. -/
theorem interleavedStep_matrix (W : ReferenceIsometry (F₀ × B) (C × F))
    (V : ReferenceIsometry (M × C) (D × E₁)) (b : B) (m : M) (f₀ : F₀)
    (d : D) (e : E₁) (f : F) :
    (interleavedStep W V).matrix (d, (e, f)) (b, (m, f₀)) =
      ∑ c, W.matrix (c, f) (f₀, b) * V.matrix (d, e) (m, c) := by
  change (∑ p : (M × C) × F,
    (V.matrix (d, e) p.1 * (if f = p.2 then (1 : ℂ) else 0)) *
      ((if p.1.1 = m then 1 else 0) * W.matrix (p.1.2, p.2) (f₀, b))) = _
  simp [Fintype.sum_prod_type, mul_comm]

end Interleaving

section OpenConnection

variable {r : Type u} [Fintype r] [DecidableEq r]

/-- The boundary input family restricts to the corresponding prefix. -/
def boundaryInputPrefixEquiv {n : Nat} (P : Fin (n + 2) → Type u) (r : Type u)
    (j : Fin (n + 1)) : boundaryInput P r j.castSucc ≃
      boundaryInput (fun k : Fin (n + 1) ↦ P k.castSucc) r j :=
  Fin.cases (Equiv.refl _) (fun _ ↦ Equiv.refl _) j

/-- Interleave chains when the inner chain's final spectator is included in
its terminal memory. This definition is built solely from local isometry
composition, tensor products and explicit permutations. -/
def MemoryChain.connectOpenIsometry :
    {n : Nat} → {I O E : Fin (n + 2) → Type u} → {F : Fin (n + 1) → Type u} →
    [∀ j, Fintype (I j)] → [∀ j, DecidableEq (I j)] →
    [∀ j, Fintype (O j)] → [∀ j, DecidableEq (O j)] →
    [∀ j, Fintype (E j)] → [∀ j, DecidableEq (E j)] →
    [∀ j, Fintype (F j)] → [∀ j, DecidableEq (F j)] →
    MemoryChain I O E →
    MemoryChain (boundaryInput (innerInput O) r) (innerOutput I) F →
    ReferenceIsometry (I 0 × r) (O (Fin.last (n + 1)) ×
      (E (Fin.last (n + 1)) × F (Fin.last n)))
  | 0, _I, O, E, _F, _, _, _, _, _, _, _, _, c, d =>
      (interleavedStep
        (MemoryChain.linkCongr (d.link 0) (Equiv.prodComm _ _) (Equiv.refl _))
        (c.link 1)).comp
        (MemoryChain.linkCongr
          ((c.link 0).prod (ReferenceIsometry.ofInjective (id : r → r)
            Function.injective_id))
          (Equiv.refl _) (Equiv.prodAssoc (O 0) (E 0) r))
  | n + 1, _I, O, _E, _F, _, _, _, _, _, _, _, _, c, d =>
      (interleavedStep (d.link (Fin.last (n + 1))) (c.link (Fin.last (n + 2)))).comp
        (c.dropLast.connectOpenIsometry
          (d.dropLast.reindexWires (boundaryInputPrefixEquiv (innerInput O) r)
            (fun _ ↦ Equiv.refl _)))

end OpenConnection

section Connection

variable {n : Nat} {I O E : Fin (n + 2) → Type u} {F : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
  {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Actual alternating composition `V₀,W₀,V₁,…,Wₙ,Vₙ₊₁`. The input
spectator enters only the first inner interaction; the output spectator
bypasses the last outer interaction. No memory is discarded here. -/
def MemoryChain.connectIsometry (c : MemoryChain I O E)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F) :
    ReferenceIsometry (I 0 × r) ((O (Fin.last (n + 1)) × s) ×
      (E (Fin.last (n + 1)) × F (Fin.last n))) :=
  MemoryChain.linkCongr (c.connectOpenIsometry d.absorbOutputSpectator) (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
      (Equiv.cast (show boundaryOutput F s (Fin.last n) = (F (Fin.last n) × s) by
        simp [boundaryOutput])))).trans
      { toFun := fun p ↦ ((p.1, p.2.2.2), (p.2.1, p.2.2.1))
        invFun := fun p ↦ (p.1.1, (p.2.1, (p.2.2, p.1.2)))
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

/-- The physical connection discards precisely the two terminal memories. -/
def MemoryChain.connectChannel (c : MemoryChain I O E)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F) :
    Channel (I 0 × r) (O (Fin.last (n + 1)) × s) :=
  (c.connectIsometry d).outputChannel

end Connection

section BoundaryAmplitudes

/-- Attach the final output spectator in explicit source-wire coordinates. -/
def boundaryOutputLift (W : Fin (n + 1) → Type u) {s : Type u}
    (w : ∀ j, W j) (σ : s) : ∀ j, boundaryOutput W s j :=
  Fin.snoc
    (fun j : Fin n ↦ (Equiv.cast (show boundaryOutput W s j.castSucc = W j.castSucc by
      simp [boundaryOutput])).symm (w j.castSucc))
    ((Equiv.cast (show boundaryOutput W s (Fin.last n) = (W (Fin.last n) × s) by
      simp [boundaryOutput])).symm (w (Fin.last n), σ))

/-- The explicit lift is the inverse boundary-output coordinate map. -/
theorem boundaryOutputEquiv_lift (W : Fin (n + 1) → Type u) {s : Type u}
    (w : ∀ j, W j) (σ : s) : boundaryOutputEquiv W s (boundaryOutputLift W w σ) = (w, σ) := by
  have hcore : (Equiv.piCongrRight fun j : Fin n ↦
      Equiv.cast (show boundaryOutput W s j.castSucc = W j.castSucc by simp [boundaryOutput]))
      (fun j ↦ (Equiv.cast (show boundaryOutput W s j.castSucc = W j.castSucc by
        simp [boundaryOutput])).symm (w j.castSucc)) = Fin.init w := by
    funext j
    exact (Equiv.cast _).apply_symm_apply _
  simp only [boundaryOutputLift, boundaryOutputEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Fin.snocEquiv_symm_apply,
    Fin.snoc_last, Fin.init_snoc, Equiv.apply_symm_apply]
  rw [hcore]
  change (Fin.snoc (Fin.init w) (w (Fin.last n)), σ) = (w, σ)
  rw [Fin.snoc_init_self]

/-- Local regrouping agrees with lifting the same output spectator along
the terminal memory wire. -/
theorem boundaryMemoryEquiv_lift (O E : Fin (n + 1) → Type u) {s : Type u}
    (o : ∀ j, O j) (e : ∀ j, E j) (σ : s) (j : Fin (n + 1)) :
    boundaryMemoryEquiv O E s j (boundaryOutputLift O o σ j, e j) =
      (o j, boundaryOutputLift E e σ j) := by
  cases j using Fin.lastCases with
  | last =>
    simp [boundaryMemoryEquiv, boundaryOutputLift]
  | cast j =>
    simp [boundaryMemoryEquiv, boundaryOutputLift]
    rfl

/-- Reading a nonfinal memory after the boundary lift removes the transport. -/
theorem boundaryOutputLift_castSucc (W : Fin (n + 1) → Type u) {s : Type u}
    (w : ∀ j, W j) (σ : s) (j : Fin n) :
    (Equiv.cast (show boundaryOutput W s j.castSucc = W j.castSucc by
      simp [boundaryOutput])) (boundaryOutputLift W w σ j.castSucc) = w j.castSucc := by
  simp only [boundaryOutputLift, Fin.snoc_castSucc]
  exact (Equiv.cast _).apply_symm_apply _

variable {s : Type u} [Fintype s] [DecidableEq s]

/-- Moving the final spectator into memory preserves every coherent path amplitude. -/
theorem MemoryChain.krausEntry_absorbOutputSpectator
    (d : MemoryChain I (boundaryOutput O s) E) (α : ∀ j, E j) (o : ∀ j, O j)
    (i : ∀ j, I j) (σ : s) (j : Fin (n + 1)) :
    d.absorbOutputSpectator.krausEntry (boundaryOutputLift E α σ) o i j =
      d.krausEntry α (boundaryOutputLift O o σ) i j := by
  have hout := congrArg (boundaryMemoryEquiv O E s j).symm
    (boundaryMemoryEquiv_lift O E o α σ j)
  simp only [Equiv.symm_apply_apply] at hout
  cases j using Fin.cases with
  | zero =>
    rw [MemoryChain.krausEntry_zero, MemoryChain.krausEntry_zero]
    change (d.link 0).matrix
      ((boundaryMemoryEquiv O E s 0).symm (o 0, boundaryOutputLift E α σ 0)) (i 0) = _
    rw [← hout]
  | succ j =>
    rw [MemoryChain.krausEntry_succ, MemoryChain.krausEntry_succ]
    change (d.link j.succ).matrix
      ((boundaryMemoryEquiv O E s j.succ).symm (o j.succ, boundaryOutputLift E α σ j.succ))
      ((Equiv.cast (show boundaryOutput E s j.castSucc = E j.castSucc by
        simp [boundaryOutput])) (boundaryOutputLift E α σ j.castSucc), i j.succ) = _
    rw [← hout, boundaryOutputLift_castSucc]

/-- Coherent Kraus amplitudes after retaining the output spectator in memory. -/
theorem MemoryChain.kraus_absorbOutputSpectator
    (d : MemoryChain I (boundaryOutput O s) E) (e : E (Fin.last n))
    (o : ∀ j, O j) (i : ∀ j, I j) (σ : s) :
    d.absorbOutputSpectator.kraus
      ((Equiv.cast (show boundaryOutput E s (Fin.last n) = (E (Fin.last n) × s) by
        simp [boundaryOutput])).symm (e, σ)) o i =
      d.kraus e (boundaryOutputLift O o σ) i := by
  let t : (∀ j : Fin n, E j.castSucc) ≃ (∀ j : Fin n, boundaryOutput E s j.castSucc) :=
    Equiv.piCongrRight fun j ↦ (Equiv.cast
      (show boundaryOutput E s j.castSucc = E j.castSucc by simp [boundaryOutput])).symm
  rw [MemoryChain.kraus_apply, MemoryChain.kraus_apply, ← Equiv.sum_comp t]
  apply Finset.sum_congr rfl
  intro α _
  have hmem : Fin.snoc (t α)
      ((Equiv.cast (show boundaryOutput E s (Fin.last n) = (E (Fin.last n) × s) by
        simp [boundaryOutput])).symm (e, σ)) = boundaryOutputLift E (Fin.snoc α e) σ := by
    funext j
    cases j using Fin.lastCases <;> simp [t, boundaryOutputLift]
  rw [hmem]
  exact Finset.prod_congr rfl fun j _ ↦ d.krausEntry_absorbOutputSpectator _ _ _ _ j

end BoundaryAmplitudes

section CoherentConnection

/-- The inverse input boundary equivalence, with the spectator entering once. -/
def boundaryInputLift (W : Fin (n + 1) → Type u) {r : Type u}
    (w : ∀ j, W j) (ρ : r) : ∀ j, boundaryInput W r j :=
  Fin.cons (w 0, ρ) (fun j ↦ w j.succ)

theorem boundaryInputEquiv_lift (W : Fin (n + 1) → Type u) {r : Type u}
    (w : ∀ j, W j) (ρ : r) : boundaryInputEquiv W r (boundaryInputLift W w ρ) = (w, ρ) := by
  change (Fin.cons (w 0) (Fin.tail w), ρ) = (w, ρ)
  rw [Fin.cons_self_tail]

private theorem init_cons {n : Nat} {W : Fin (n + 2) → Type u}
    (w : W 0) (v : ∀ j : Fin (n + 1), W j.succ) :
    Fin.init (Fin.cons w v) =
      Fin.cons (α := fun j : Fin (n + 1) ↦ W j.castSucc) w (Fin.init v) := by
  funext j
  cases j using Fin.cases <;> rfl

private theorem inputLift_prefix_symm {n : Nat} (W : Fin (n + 2) → Type u) {r : Type u}
    (w : ∀ j, W j) (ρ : r) :
    (fun j : Fin (n + 1) ↦ (boundaryInputPrefixEquiv W r j).symm
      (boundaryInputLift (fun k : Fin (n + 1) ↦ W k.castSucc) (Fin.init w) ρ j)) =
        Fin.init (boundaryInputLift W w ρ) := by
  funext j
  cases j using Fin.cases <;> rfl

private theorem inputLift_init_snoc {n : Nat} (W : Fin (n + 2) → Type u) {r : Type u}
    (a : ∀ j : Fin (n + 1), W j.castSucc) (z : W (Fin.last (n + 1))) (ρ : r) :
    Fin.init (boundaryInputLift W (Fin.snoc a z) ρ) =
      (fun j ↦ (boundaryInputPrefixEquiv W r j).symm
        (boundaryInputLift (fun k : Fin (n + 1) ↦ W k.castSucc) a ρ j)) := by
  simpa only [Fin.init_snoc] using (inputLift_prefix_symm W (Fin.snoc a z) ρ).symm

private theorem inputLift_last_snoc {n : Nat} (W : Fin (n + 2) → Type u) {r : Type u}
    (a : ∀ j : Fin (n + 1), W j.castSucc) (z : W (Fin.last (n + 1))) (ρ : r) :
    boundaryInputLift W (Fin.snoc a z) ρ (Fin.last (n + 1)) = z := by
  change (Fin.snoc a z) (Fin.last (n + 1)) = z
  exact Fin.snoc_last _ _

private theorem sum_shuffle_five {A B C D E : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    (H : A → B → C → D → E → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, H a b c d e) =
      ∑ d, ∑ c, ∑ e, ∑ b, ∑ a, H a b c d e := by
  conv_lhs =>
    arg 2; ext a
    arg 2; ext b
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]

private theorem sum_swap_pairs {A B C D E F : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    (H : A → B → C → D → E → F → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, H a b c d e f) =
      ∑ e, ∑ f, ∑ c, ∑ d, ∑ a, ∑ b, H a b c d e f := by
  let K : (A × B) → (C × D) → (E × F) → ℂ :=
    fun x y z ↦ H x.1 x.2 y.1 y.2 z.1 z.2
  have h : (∑ x, ∑ y, ∑ z, K x y z) = ∑ z, ∑ y, ∑ x, K x y z := by
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type, K] using h

private theorem interleavedStep_comp_matrix {A B M F₀ C F D E₁ : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype M] [DecidableEq M] [Fintype F₀] [DecidableEq F₀]
    [Fintype C] [DecidableEq C] [Fintype F] [DecidableEq F]
    [Fintype D] [DecidableEq D] [Fintype E₁] [DecidableEq E₁]
    (P : ReferenceIsometry A (B × (M × F₀)))
    (W : ReferenceIsometry (F₀ × B) (C × F))
    (V : ReferenceIsometry (M × C) (D × E₁))
    (a : A) (d : D) (e : E₁) (f : F) :
    ((interleavedStep W V).comp P).matrix (d, (e, f)) a =
      ∑ b, ∑ m, ∑ f₀, ∑ c, P.matrix (b, (m, f₀)) a *
        W.matrix (c, f) (f₀, b) * V.matrix (d, e) (m, c) := by
  change (∑ p, (interleavedStep W V).matrix (d, (e, f)) p * P.matrix p a) = _
  simp only [Fintype.sum_prod_type, interleavedStep_matrix, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro f₀ _
  exact Finset.sum_congr rfl fun c _ ↦ by ring

variable {n : Nat} {I O E : Fin (n + 2) → Type u} {F : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
  {r : Type u} [Fintype r] [DecidableEq r]

set_option backward.isDefEq.respectTransparency false in
/-- Coherent amplitudes of the actual alternating composition. Internal
wires are summed before the terminal environment is discarded. -/
theorem MemoryChain.connectOpenIsometry_matrix (c : MemoryChain I O E)
    (d : MemoryChain (boundaryInput (innerInput O) r) (innerOutput I) F)
    (i : I 0) (ρ : r) (o : O (Fin.last (n + 1)))
    (e : E (Fin.last (n + 1))) (f : F (Fin.last n)) :
    (c.connectOpenIsometry d).matrix (o, (e, f)) (i, ρ) =
      ∑ a : ∀ j, innerInput O j, ∑ b : ∀ j, innerOutput I j,
        c.kraus e (Fin.snoc a o) (Fin.cons i b) *
          d.kraus f b (boundaryInputLift (innerInput O) a ρ) := by
  classical
  induction n with
  | zero =>
    rw [MemoryChain.connectOpenIsometry, interleavedStep_comp_matrix]
    change (∑ a, ∑ m, ∑ ρ', ∑ b,
      ((c.link 0).matrix (a, m) i * (if ρ' = ρ then (1 : ℂ) else 0)) *
        (d.link 0).matrix (b, f) (a, ρ') * (c.link 1).matrix (o, e) (m, b)) = _
    conv_rhs =>
      rw [← Fintype.sum_prod_type',
        ← Equiv.sum_comp (Equiv.prodCongr (Equiv.piUnique (innerInput O)).symm
          (Equiv.piUnique (innerOutput I)).symm)]
    simp only [Fintype.sum_prod_type]
    simp only [Equiv.prodCongr_apply, Prod.map_apply]
    simp only [c.kraus_step, MemoryChain.kraus_one, Fin.init_snoc,
      Fin.snoc_last, Fin.cons_last, Fin.cons_zero, boundaryInputLift]
    simp only [Finset.sum_mul]
    change (∑ a, ∑ m, ∑ ρ', ∑ b,
      ((c.link 0).matrix (a, m) i * (if ρ' = ρ then (1 : ℂ) else 0)) *
        (d.link 0).matrix (b, f) (a, ρ') * (c.link 1).matrix (o, e) (m, b)) =
      ∑ a, ∑ b, ∑ m, (c.link 0).matrix (a, m) i *
        (c.link 1).matrix (o, e) (m, b) * (d.link 0).matrix (b, f) (a, ρ)
    apply Finset.sum_congr rfl
    intro a _
    conv_lhs => arg 2; ext m; rw [Finset.sum_comm]
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  | succ n ih =>
    rw [MemoryChain.connectOpenIsometry, interleavedStep_comp_matrix]
    simp_rw [ih]
    conv_rhs =>
      rw [← Fintype.sum_prod_type',
        ← Equiv.sum_comp (Equiv.prodCongr (Fin.snocEquiv (innerInput O))
          (Fin.snocEquiv (innerOutput I)))]
    simp only [Fintype.sum_prod_type, Equiv.prodCongr_apply, Prod.map_apply,
      Fin.snocEquiv, Equiv.coe_fn_mk]
    simp only [c.kraus_step, d.kraus_step,
      Fin.init_snoc, Fin.snoc_last, init_cons, Fin.cons_last]
    let d' := d.dropLast.reindexWires (boundaryInputPrefixEquiv (innerInput O) r)
      (fun _ ↦ Equiv.refl _)
    have hd (f₀ : F (Fin.last n).castSucc) (b : ∀ j : Fin (n + 1), I j.succ.castSucc)
        (a : ∀ j : Fin (n + 1), O j.castSucc.castSucc) (z : O (Fin.last (n + 1)).castSucc) :
        d.dropLast.kraus f₀ b (Fin.init (boundaryInputLift (innerInput O) (Fin.snoc a z) ρ)) =
          d'.kraus f₀ b (boundaryInputLift (innerInput (fun j ↦ O j.castSucc)) a ρ) := by
      rw [MemoryChain.kraus_reindexWires, inputLift_init_snoc]
      rfl
    simp only [hd, inputLift_last_snoc]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [sum_shuffle_five]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b₀ _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro f₀ _
    exact Finset.sum_congr rfl fun m _ ↦ by ring

end CoherentConnection

section ConnectionSemantics

variable {n : Nat} {I O E : Fin (n + 2) → Type u} {F : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
  {r s : Type u} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- The connected isometry coherently contracts the free wires of both chains,
with independent input and output spectator coordinates. -/
theorem MemoryChain.connectIsometry_matrix (c : MemoryChain I O E)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F)
    (i : I 0) (ρ : r) (o : O (Fin.last (n + 1))) (σ : s)
    (e : E (Fin.last (n + 1))) (f : F (Fin.last n)) :
    (c.connectIsometry d).matrix ((o, σ), (e, f)) (i, ρ) =
      ∑ a : ∀ j, innerInput O j, ∑ b : ∀ j, innerOutput I j,
        c.kraus e (Fin.snoc a o) (Fin.cons i b) *
          d.kraus f (boundaryOutputLift (innerOutput I) b σ)
            (boundaryInputLift (innerInput O) a ρ) := by
  change (c.connectOpenIsometry d.absorbOutputSpectator).matrix
    (o, (e, (Equiv.cast (show boundaryOutput F s (Fin.last n) = (F (Fin.last n) × s) by
      simp [boundaryOutput])).symm (f, σ))) (i, ρ) = _
  rw [MemoryChain.connectOpenIsometry_matrix]
  simp_rw [MemoryChain.kraus_absorbOutputSpectator]

/-- The inner memory channel's Choi matrix with independent boundary systems
grouped according to the complete admissibility convention. -/
def MemoryChain.jointChoi
    {m : Nat} {P Q F : Fin (m + 1) → Type u}
    [∀ j, Fintype (P j)] [∀ j, DecidableEq (P j)]
    [∀ j, Fintype (Q j)] [∀ j, DecidableEq (Q j)]
    [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
    (d : MemoryChain (boundaryInput (P) r)
      (boundaryOutput (Q) s) F) :
    CMatrix (((∀ j, P j) × r) × ((∀ j, Q j) × s)) :=
  WireFam.matReindex (boundaryEquiv (P) (Q) r s)
    (MatrixMap.choi d.chainMap)

/-- Boundary-grouped Choi entries are products of the two coherent amplitudes. -/
theorem MemoryChain.jointChoi_apply
    {m : Nat} {P Q F : Fin (m + 1) → Type u}
    [∀ j, Fintype (P j)] [∀ j, DecidableEq (P j)]
    [∀ j, Fintype (Q j)] [∀ j, DecidableEq (Q j)]
    [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
    (d : MemoryChain (boundaryInput (P) r)
      (boundaryOutput (Q) s) F)
    (a a' : ∀ j, P j) (b b' : ∀ j, Q j)
    (ρ ρ' : r) (σ σ' : s) :
    d.jointChoi ((a, ρ), (b, σ)) ((a', ρ'), (b', σ')) =
      ∑ f, d.kraus f (boundaryOutputLift (Q) b σ)
          (boundaryInputLift (P) a ρ) *
        star (d.kraus f (boundaryOutputLift (Q) b' σ')
          (boundaryInputLift (P) a' ρ')) := by
  have hi (a : ∀ j, P j) (ρ : r) :
      (boundaryInputEquiv (P) r).symm (a, ρ) =
        boundaryInputLift (P) a ρ := by
    apply (boundaryInputEquiv (P) r).injective
    rw [Equiv.apply_symm_apply, boundaryInputEquiv_lift]
  have ho (b : ∀ j, Q j) (σ : s) :
      (boundaryOutputEquiv (Q) s).symm (b, σ) =
        boundaryOutputLift (Q) b σ := by
    apply (boundaryOutputEquiv (Q) s).injective
    rw [Equiv.apply_symm_apply, boundaryOutputEquiv_lift]
  simp only [MemoryChain.jointChoi, WireFam.matReindex_apply, boundaryEquiv,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    MemoryChain.choi_chainMap_apply, hi, ho]

/-- Environment slices of any isometry give its output channel Choi entries. -/
theorem outputChannel_choi_apply {A B R : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R] (V : ReferenceIsometry A (B × R))
    (a a' : A) (b b' : B) :
    MatrixMap.choi V.outputChannel.map (a, b) (a', b') =
      ∑ e, V.matrix (b, e) a * star (V.matrix (b', e) a') := by
  classical
  rw [MatrixMap.choi, ReferenceIsometry.outputChannel_map]
  simp [partialTraceB, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
    Matrix.of_apply, mul_ite, ite_and]

set_option backward.isDefEq.respectTransparency false in
/-- The channel obtained by actual alternating isometries has exactly the
existing ancillary Choi-space action [Chiribella2009Networks,
comblong-pub.tex:1924-1934]. -/
theorem MemoryChain.connectChannel_choi (c : MemoryChain I O E)
    (d : MemoryChain (boundaryInput (innerInput O) r)
      (boundaryOutput (innerOutput I) s) F) :
    MatrixMap.choi (c.connectChannel d).map =
      ancillaryExtension (actionMap I O (MatrixMap.choi c.chainMap)) d.jointChoi := by
  classical
  ext p q
  rcases p with ⟨⟨i, ρ⟩, ⟨o, σ⟩⟩
  rcases q with ⟨⟨i', ρ'⟩, ⟨o', σ'⟩⟩
  rw [MemoryChain.connectChannel, outputChannel_choi_apply]
  simp only [Fintype.sum_prod_type, MemoryChain.connectIsometry_matrix]
  change _ = ∑ z : Space (innerInput O) (innerOutput I),
    ∑ z' : Space (innerInput O) (innerOutput I),
      d.jointChoi ((z.1, ρ), (z.2, σ)) ((z'.1, ρ'), (z'.2, σ')) *
        MatrixMap.choi c.chainMap (Fin.cons i z.2, Fin.snoc z.1 o)
          (Fin.cons i' z'.2, Fin.snoc z'.1 o')
  simp only [Fintype.sum_prod_type, MemoryChain.jointChoi_apply,
    MemoryChain.choi_chainMap_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_swap_pairs]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a' _
  apply Finset.sum_congr rfl
  intro b' _
  apply Finset.sum_congr rfl
  intro e _
  exact Finset.sum_congr rfl fun f _ ↦ by ring

end ConnectionSemantics

section UnitConnection

variable {n : Nat} {I O E : Fin (n + 2) → Type u} {F : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]

set_option backward.isDefEq.respectTransparency false in
/-- For trivial spectators the same physical channel has exactly the existing
shared-wire link product, read through the canonical unit-wire inclusions. -/
theorem MemoryChain.connectChannel_choi_linkAction (c : MemoryChain I O E)
    (d : MemoryChain (boundaryInput (innerInput O) PUnit)
      (boundaryOutput (innerOutput I) PUnit) F) :
    (MatrixMap.choi (c.connectChannel d).map).submatrix
      (fun p ↦ ((p.1, PUnit.unit), (p.2, PUnit.unit)))
      (fun p ↦ ((p.1, PUnit.unit), (p.2, PUnit.unit))) =
      linkAction I O (MatrixMap.choi c.chainMap)
        (fun z z' ↦ d.jointChoi ((z.1, PUnit.unit), (z.2, PUnit.unit))
          ((z'.1, PUnit.unit), (z'.2, PUnit.unit))) := by
  rw [MemoryChain.connectChannel_choi, ← actionMap_eq_linkAction]
  rfl

end UnitConnection

end QIT.HigherOrder
