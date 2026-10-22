/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.Util.Wires.LinkProduct

/-!
# Associativity of three matched wire families

Three factors are partitioned into their private wires and the disjoint AB,
AC, and BC connection groups. Both binary groupings retain every pending
connection and every private wire. Arbitrary original port orders and
pointwise basis identifications are represented by `PortPartition`; no
configuration-readback or operator equality is assumed.

The three-group identity is reduced to the existing `WireFam.linkProduct_assoc`
by carrying the AC group through the middle factor with identity deltas.
Associativity is reused, not reproved by rearranging contraction sums.
`partition_linkProduct` identifies actual `WireMatch.linkProduct` operators
with these coordinates using only endpoint and per-wire basis equations.

The construction realizes the no-triple-overlap associativity property in
[Chiribella2009Networks, comblong-pub.tex:342-355]. It is algebraic and needs no
positivity, normalization, wire inhabitance, or causal-order hypothesis; in
particular it applies to the directional acyclic network compositions of
[Chiribella2009Networks, comblong-pub.tex:1279-1286]. Empty wire families and
empty individual wire types are permitted.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
universe u
namespace QIT.WireFam
namespace MatchedWire
/-- A configuration space viewed as one aggregate wire. -/
abbrev block (α : Type u) : Fin 1 → Type u := fun _ ↦ α

/-- Two aggregate wires in product coordinates. -/
def pairEquiv (α β : Type u) : (∀ i, append (block α) (block β) i) ≃ α × β :=
  (splitAppendEquiv _ _).trans
    ((Equiv.piUnique (block α)).prodCongr (Equiv.piUnique (block β)))

/-- The actual core link product in product coordinates. -/
def productLink {α β γ : Type u} [Fintype β]
    (M : CMatrix (α × β)) (N : CMatrix (β × γ)) : CMatrix (α × γ) :=
  matReindex (pairEquiv α γ)
    (linkProduct (block α) (block β) (block γ)
      (matReindex (pairEquiv α β).symm M) (matReindex (pairEquiv β γ).symm N))

/-- Entrywise contraction, with independent shared row and column values. -/
theorem productLink_apply {α β γ : Type u} [Fintype β]
    (M : CMatrix (α × β)) (N : CMatrix (β × γ)) (a a' : α) (c c' : γ) :
    productLink M N (a, c) (a', c') =
      ∑ b, ∑ b', M (a, b') (a', b) * N (b', c) (b, c') := by
  simp only [productLink, matReindex_apply, pairEquiv, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply]
  rw [linkProduct_apply]
  simp only [Equiv.piUnique_symm_apply]
  exact Fintype.sum_equiv (Equiv.piUnique (block β)) _ _ (fun b ↦
    Fintype.sum_equiv (Equiv.piUnique (block β)) _ _ (fun b' ↦ rfl))

/-- Product-coordinate associativity transported from `WireFam.linkProduct_assoc`. -/
theorem productLink_assoc {α β γ δ : Type u} [Fintype β] [Fintype γ]
    (M : CMatrix (α × β)) (N : CMatrix (β × γ)) (P : CMatrix (γ × δ)) :
    productLink (productLink M N) P = productLink M (productLink N P) := by
  unfold productLink
  simp only [matReindex_symm_matReindex]
  exact congrArg (matReindex (pairEquiv α δ))
    (linkProduct_assoc (block α) (block β) (block γ) (block δ) _ _ _)

/-- Gather the private blocks and the pending shared blocks separately. -/
def gather (A B C D : Type u) : (A × B) × (C × D) ≃ (A × C) × (B × D) :=
  Equiv.prodProdProdComm A B C D

/-- Put the AB and AC groups together while retaining A's private block. -/
def leftOrder (A X Y : Type u) : (A × Y) × X ≃ A × (X × Y) where
  toFun p := (p.1.1, (p.2, p.1.2))
  invFun p := ((p.1, p.2.2), p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Contract AB first, retaining AC and BC, then contract AC and BC with C.
Here `X`, `Y`, `Z` are the AB, AC, BC configurations respectively. -/
def triangleLeft {A B C X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]
    (M : CMatrix ((A × Y) × X)) (N : CMatrix (X × (B × Z)))
    (P : CMatrix ((Y × Z) × C)) : CMatrix ((A × B) × C) :=
  productLink (matReindex (gather A Y B Z) (productLink M N)) P

/-- Contract BC first, retaining AB and AC, then contract AB and AC with A.
All three private configurations remain on the final boundary. -/
def triangleRight {A B C X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]
    (M : CMatrix ((A × Y) × X)) (N : CMatrix (X × (B × Z)))
    (P : CMatrix ((Y × Z) × C)) : CMatrix (A × (B × C)) :=
  productLink (matReindex (leftOrder A X Y) M)
    (matReindex (gather X B Y C)
      (productLink (matReindex (Equiv.prodAssoc X B Z).symm N)
        (matReindex (midSwapEquiv Y Z C) P)))

private def carry {B X Y Z : Type u} [DecidableEq Y]
    (N : CMatrix (X × (B × Z))) (b b' : B) : CMatrix ((X × Y) × (Y × Z)) :=
  fun p q ↦ if p.1.2 = p.2.1 ∧ q.1.2 = q.2.1 then
    N (p.1.1, (b, p.2.2)) (q.1.1, (b', q.2.2)) else 0

private theorem carry_left {A B X Y Z : Type u} [Fintype X] [Fintype Y] [DecidableEq Y]
    (M : CMatrix ((A × Y) × X)) (N : CMatrix (X × (B × Z)))
    (a a' : A) (b b' : B) (y y' : Y) (z z' : Z) :
    productLink (matReindex (leftOrder A X Y) M) (carry N b b')
      (a, (y, z)) (a', (y', z')) =
    productLink M N ((a, y), (b, z)) ((a', y'), (b', z')) := by
  simp only [productLink_apply, Fintype.sum_prod_type, matReindex_apply, leftOrder,
    carry]
  simp [ite_and]

private theorem carry_right {B C X Y Z : Type u} [Fintype Y] [Fintype Z] [DecidableEq Y]
    (N : CMatrix (X × (B × Z))) (P : CMatrix ((Y × Z) × C))
    (x x' : X) (b b' : B) (y y' : Y) (c c' : C) :
    productLink (carry N b b') P ((x, y), c) ((x', y'), c') =
      productLink (matReindex (Equiv.prodAssoc X B Z).symm N)
        (matReindex (midSwapEquiv Y Z C) P)
        ((x, b), (y, c)) ((x', b'), (y', c')) := by
  simp only [productLink_apply, Fintype.sum_prod_type, matReindex_apply,
    Equiv.symm_symm, Equiv.prodAssoc_apply, midSwapEquiv, carry]
  simp [ite_and]

/-- Associativity for all three disjoint connection groups, with explicit
final-boundary reindex. The proof reuses the existing chain associativity
through an identity-delta carry of AC. -/
theorem triangle_assoc {A B C X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]
    (M : CMatrix ((A × Y) × X)) (N : CMatrix (X × (B × Z)))
    (P : CMatrix ((Y × Z) × C)) :
    matReindex (Equiv.prodAssoc A B C) (triangleLeft M N P) = triangleRight M N P := by
  classical
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  have h := congrFun (congrFun (productLink_assoc
    (matReindex (leftOrder A X Y) M) (carry (Y := Y) N b b') P) (a, c)) (a', c')
  have hL : triangleLeft M N P ((a, b), c) ((a', b'), c') =
      productLink (productLink (matReindex (leftOrder A X Y) M) (carry N b b')) P
        (a, c) (a', c') := by
    rw [triangleLeft, productLink_apply, productLink_apply]
    apply Finset.sum_congr rfl
    rintro ⟨y, z⟩ _
    apply Finset.sum_congr rfl
    rintro ⟨y', z'⟩ _
    rw [carry_left]
    rfl
  have hR : productLink (matReindex (leftOrder A X Y) M)
      (productLink (carry N b b') P) (a, c) (a', c') =
      triangleRight M N P (a, (b, c)) (a', (b', c')) := by
    rw [triangleRight, productLink_apply, productLink_apply]
    apply Finset.sum_congr rfl
    rintro ⟨x, y⟩ _
    apply Finset.sum_congr rfl
    rintro ⟨x', y'⟩ _
    rw [carry_right]
    rfl
  exact hL.trans (h.trans hR)

/-- Product coordinates of an actual matching; all maps are the matching's
canonical transports, not additional compatibility assumptions. -/
theorem wireMatch_coordinates {a b : Nat} {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) [∀ k, Fintype (m.connFam₁ k)]
    (M : CMatrix (∀ i, W₁ i)) (N : CMatrix (∀ i, W₂ i)) :
    matReindex (splitAppendEquiv m.complFam₁ m.complFam₂) (m.linkProduct M N) =
      productLink
        (matReindex (m.eM.trans (splitAppendEquiv m.complFam₁ m.connFam₁)) M)
        (matReindex ((m.eN.trans m.eTransportEquiv).trans
          (splitAppendEquiv m.connFam₁ m.complFam₂)) N) := by
  ext ⟨g, w⟩ ⟨g', w'⟩
  rw [matReindex_apply, m.linkProduct_apply, productLink_apply]
  simp only [matReindex_apply, Equiv.symm_trans_apply,
    WireMatch.eTransportEquiv_symm_pack,
    WireMatch.read₁, WireMatch.read₂]

/-- Relabeling private and shared configurations commutes with contraction. -/
theorem productLink_reindex {A A' X X' B B' : Type u} [Fintype X] [Fintype X']
    (eA : A ≃ A') (eX : X ≃ X') (eB : B ≃ B')
    (M : CMatrix (A × X)) (N : CMatrix (X × B)) :
    productLink (matReindex (eA.prodCongr eX) M) (matReindex (eX.prodCongr eB) N) =
      matReindex (eA.prodCongr eB) (productLink M N) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [productLink_apply, matReindex_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply]
  exact Fintype.sum_equiv eX.symm _ _ (fun x ↦
    Fintype.sum_equiv eX.symm _ _ (fun x' ↦ rfl))

/-- Unit padding contributes exactly one shared value, never a dimension
factor. An empty individual wire type is not confused with unit padding. -/
theorem productLink_unique {A U C : Type u} [Fintype U] [Unique U]
    (M : CMatrix (A × U)) (N : CMatrix (U × C)) (a a' : A) (c c' : C) :
    productLink M N (a, c) (a', c') =
      M (a, default) (a', default) * N (default, c) (default, c') := by
  simp [productLink_apply]

/-- A partition of actual port positions into two named blocks, including
pointwise basis identifications. Every original port occurs exactly once. -/
structure PortPartition {n l r : Nat} (W : Fin n → Type u)
    (L : Fin l → Type u) (R : Fin r → Type u) where
  index : Fin n ≃ (Fin l ⊕ Fin r)
  wire : ∀ i, W i ≃ Sum.elim L R (index i)

namespace PortPartition
variable {n l r : Nat} {W : Fin n → Type u} {L : Fin l → Type u} {R : Fin r → Type u}

/-- Repack actual ports into the partition's two configuration blocks. -/
def configEquiv (p : PortPartition W L R) :
    (∀ i, W i) ≃ (∀ i, L i) × (∀ i, R i) :=
  (Equiv.piCongrRight p.wire).trans
    ((Equiv.piCongrLeft (Sum.elim L R) p.index).trans (Equiv.sumPiEquivProdPi _))

/-- The left block reads precisely its original ports, with their basis maps. -/
theorem configEquiv_left (p : PortPartition W L R) (f : ∀ i, W i) (i : Fin l) :
    (p.configEquiv f).1 i =
      cast (by simp) (p.wire (p.index.symm (Sum.inl i)) (f (p.index.symm (Sum.inl i)))) := by
  change Equiv.piCongrLeft (Sum.elim L R) p.index (fun k ↦ p.wire k (f k)) (Sum.inl i) = _
  exact Equiv.piCongrLeft_apply_eq_cast _ _

/-- The right block reads precisely its original ports, with their basis maps. -/
theorem configEquiv_right (p : PortPartition W L R) (f : ∀ i, W i) (i : Fin r) :
    (p.configEquiv f).2 i =
      cast (by simp) (p.wire (p.index.symm (Sum.inr i)) (f (p.index.symm (Sum.inr i)))) := by
  change Equiv.piCongrLeft (Sum.elim L R) p.index (fun k ↦ p.wire k (f k)) (Sum.inr i) = _
  exact Equiv.piCongrLeft_apply_eq_cast _ _

/-- Split the first partition block into two pending/private blocks. -/
def leftTriple {a b c : Nat} {W : Fin n → Type u}
    {A : Fin a → Type u} {B : Fin b → Type u} {C : Fin c → Type u}
    (p : PortPartition W (append A B) C) :
    (∀ i, W i) ≃ ((∀ i, A i) × (∀ i, B i)) × (∀ i, C i) :=
  p.configEquiv.trans ((splitAppendEquiv A B).prodCongr (Equiv.refl _))

/-- Split the second partition block into two pending/private blocks. -/
def rightTriple {a b c : Nat} {W : Fin n → Type u}
    {A : Fin a → Type u} {B : Fin b → Type u} {C : Fin c → Type u}
    (p : PortPartition W A (append B C)) :
    (∀ i, W i) ≃ (∀ i, A i) × ((∀ i, B i) × (∀ i, C i)) :=
  p.configEquiv.trans ((Equiv.refl _).prodCongr (splitAppendEquiv B C))

/-- The basis map at an original port known to be in the left block. -/
def atLeft (p : PortPartition W L R) (t : Fin n) {i : Fin l}
    (h : p.index t = Sum.inl i) : W t ≃ L i :=
  (p.wire t).trans (Equiv.cast (congrArg (Sum.elim L R) h))

/-- The basis map at an original port known to be in the right block. -/
def atRight (p : PortPartition W L R) (t : Fin n) {i : Fin r}
    (h : p.index t = Sum.inr i) : W t ≃ R i :=
  (p.wire t).trans (Equiv.cast (congrArg (Sum.elim L R) h))

/-- Restore an original left-block port from the named configurations. -/
theorem configEquiv_symm_left (p : PortPartition W L R) (x : ∀ i, L i) (y : ∀ i, R i)
    (t : Fin n) {i : Fin l} (h : p.index t = Sum.inl i) :
    p.configEquiv.symm (x, y) t = (p.atLeft t h).symm (x i) := by
  change (p.wire t).symm ((Equiv.sumPiEquivProdPi (Sum.elim L R)).symm (x, y) (p.index t)) = _
  unfold atLeft
  rw [Equiv.symm_trans_apply]
  apply congrArg (p.wire t).symm
  have hs {s : Fin l ⊕ Fin r} (h : s = Sum.inl i) :
      (Equiv.sumPiEquivProdPi (Sum.elim L R)).symm (x, y) s =
        (Equiv.cast (congrArg (Sum.elim L R) h)).symm (x i) := by
    cases h
    rfl
  exact hs h

/-- Restore an original right-block port from the named configurations. -/
theorem configEquiv_symm_right (p : PortPartition W L R) (x : ∀ i, L i) (y : ∀ i, R i)
    (t : Fin n) {i : Fin r} (h : p.index t = Sum.inr i) :
    p.configEquiv.symm (x, y) t = (p.atRight t h).symm (y i) := by
  change (p.wire t).symm ((Equiv.sumPiEquivProdPi (Sum.elim L R)).symm (x, y) (p.index t)) = _
  unfold atRight
  rw [Equiv.symm_trans_apply]
  apply congrArg (p.wire t).symm
  have hs {s : Fin l ⊕ Fin r} (h : s = Sum.inr i) :
      (Equiv.sumPiEquivProdPi (Sum.elim L R)).symm (x, y) s =
        (Equiv.cast (congrArg (Sum.elim L R) h)).symm (y i) := by
    cases h
    rfl
  exact hs h

/-- Complement enumeration is equivalent to the subtype of unmatched ports. -/
def freePortsEquiv {n s : Nat} (ι : Fin s → Fin n) (hi : Function.Injective ι) :
    Fin (n - s) ≃ {t // t ∉ Set.range ι} :=
  Equiv.ofBijective
    (fun k ↦ ⟨complEmb ι hi k, by
      rintro ⟨j, hj⟩
      exact disjoint_conn_compl ι hi j k hj⟩)
    (by
      constructor
      · intro k k' h
        have hh : complEmb ι hi k = complEmb ι hi k' :=
          congrArg (fun t : {t : Fin n // t ∉ Set.range ι} ↦ t.val) h
        exact (Finset.orderEmbOfFin (complFinset ι hi) (card_complFinset ι hi)).injective hh
      · intro ⟨t, ht⟩
        rcases exists_conn_or_compl ι hi t with h | ⟨k, hk⟩
        · exact (ht h).elim
        · exact ⟨k, Subtype.ext hk⟩)

/-- A partition's private positions are exactly the matching complement. -/
def privatePortsEquiv (p : PortPartition W L R) (ι : Fin r → Fin n)
    (h : ∀ k, p.index (ι k) = Sum.inr k) :
    Fin l ≃ {t // t ∉ Set.range ι} :=
  Equiv.ofBijective
    (fun i ↦ ⟨p.index.symm (Sum.inl i), by
      rintro ⟨k, hk⟩
      have he := congrArg p.index hk
      simp only [h, Equiv.apply_symm_apply] at he
      cases he⟩)
    (by
      constructor
      · intro i j he
        exact Sum.inl_injective (p.index.symm.injective (congrArg Subtype.val he))
      · intro ⟨t, ht⟩
        cases he : p.index t with
        | inl i => exact ⟨i, Subtype.ext ((p.index.symm_apply_eq).mpr he.symm)⟩
        | inr k =>
          exact (ht ⟨k, p.index.injective ((h k).trans he.symm)⟩).elim)

/-- Reindex the matching's complement positions into the private block. -/
def remainingIndex (p : PortPartition W L R) (ι : Fin r → Fin n)
    (hi : Function.Injective ι) (h : ∀ k, p.index (ι k) = Sum.inr k) :
    Fin (n - r) ≃ Fin l :=
  (freePortsEquiv ι hi).trans (p.privatePortsEquiv ι h).symm

/-- A complement position retains its original private-block label. -/
theorem remainingIndex_spec (p : PortPartition W L R) (ι : Fin r → Fin n)
    (hi : Function.Injective ι) (h : ∀ k, p.index (ι k) = Sum.inr k) (j : Fin (n - r)) :
    p.index (complEmb ι hi j) = Sum.inl (p.remainingIndex ι hi h j) := by
  have he := (p.privatePortsEquiv ι h).apply_symm_apply (freePortsEquiv ι hi j)
  have hv : p.index.symm (Sum.inl (p.remainingIndex ι hi h j)) = complEmb ι hi j :=
    congrArg (fun t : {t // t ∉ Set.range ι} ↦ t.val) he
  exact (congrArg p.index hv).symm.trans (p.index.apply_symm_apply _)

/-- Actual complement configurations are exactly the named private configurations. -/
def remainingEquiv (p : PortPartition W L R) (ι : Fin r → Fin n)
    (hi : Function.Injective ι) (h : ∀ k, p.index (ι k) = Sum.inr k) :
    (∀ j, W (complEmb ι hi j)) ≃ (∀ i, L i) :=
  Equiv.piCongr (p.remainingIndex ι hi h)
    (fun j ↦ p.atLeft (complEmb ι hi j) (p.remainingIndex_spec ι hi h j))

/-- Complement readback follows from the port equivalence and basis maps. -/
theorem remainingEquiv_apply (p : PortPartition W L R) (ι : Fin r → Fin n)
    (hi : Function.Injective ι) (h : ∀ k, p.index (ι k) = Sum.inr k)
    (g : ∀ j, W (complEmb ι hi j)) (j : Fin (n - r)) :
    p.remainingEquiv ι hi h g (p.remainingIndex ι hi h j) =
      p.atLeft (complEmb ι hi j) (p.remainingIndex_spec ι hi h j) (g j) :=
  Equiv.piCongr_apply_apply _ _ _ _

section Regrouping
variable {a b c : Nat} {A : Fin a → Type u} {B : Fin b → Type u} {C : Fin c → Type u}

/-- Exchange the private and shared blocks by their actual port labels. -/
def swap (p : PortPartition W A B) : PortPartition W B A where
  index := p.index.trans (Equiv.sumComm _ _)
  wire i := (p.wire i).trans (Equiv.cast (by cases h : p.index i <;> simp [h]))

private theorem cast_join {α β γ : Type u} (h₁ : α = β) (h₂ : β = γ)
    (h₃ : α = γ) (x : α) : cast h₂ (cast h₁ x) = cast h₃ x := by
  cases h₁; cases h₂; rfl

private theorem cast_three_one {α β γ δ : Type u} (h₁ : α = β) (h₂ : β = γ)
    (h₃ : γ = δ) (h₄ : α = δ) (x : α) :
    cast h₃ (cast h₂ (cast h₁ x)) = cast h₄ x := by
  cases h₁; cases h₂; cases h₃; rfl

private theorem cast_three_two {α β γ δ ε : Type u} (h₁ : α = β) (h₂ : β = γ)
    (h₃ : γ = δ) (h₄ : α = ε) (h₅ : ε = δ) (x : α) :
    cast h₃ (cast h₂ (cast h₁ x)) = cast h₅ (cast h₄ x) := by
  cases h₁; cases h₂; cases h₃; cases h₄; rfl

private theorem cast_two_two {α β γ δ : Type u} (h₁ : α = β) (h₂ : β = γ)
    (h₃ : α = δ) (h₄ : δ = γ) (x : α) :
    cast h₂ (cast h₁ x) = cast h₄ (cast h₃ x) := by
  cases h₁; cases h₂; cases h₃; rfl

/-- Swapping the port partition swaps its two configuration blocks. -/
theorem configEquiv_swap (p : PortPartition W A B) :
    p.swap.configEquiv = p.configEquiv.trans (Equiv.prodComm _ _) := by
  apply Equiv.symm_bijective.injective
  ext ⟨x, y⟩ i
  change p.swap.configEquiv.symm (x,y) i = p.configEquiv.symm (y,x) i
  cases h : p.index i with
  | inl j =>
    rw [p.swap.configEquiv_symm_right (i := j) x y i (by simp [swap, h]),
      p.configEquiv_symm_left y x i h]
    change (p.wire i).symm (cast _ (cast _ (y j))) = (p.wire i).symm (cast _ (y j))
    exact congrArg (p.wire i).symm (cast_join _ _ _ _)
  | inr j =>
    rw [p.swap.configEquiv_symm_left (i := j) x y i (by simp [swap, h]),
      p.configEquiv_symm_right y x i h]
    change (p.wire i).symm (cast _ (cast _ (x j))) = (p.wire i).symm (cast _ (x j))
    exact congrArg (p.wire i).symm (cast_join _ _ _ _)

/-- The canonical reassociation of three finite port-index blocks. -/
def assocIndex (a b c : Nat) : (Fin a ⊕ Fin (b + c)) ≃ (Fin (a + b) ⊕ Fin c) :=
  ((Equiv.refl _).sumCongr finSumFinEquiv.symm).trans
    ((Equiv.sumAssoc _ _ _).symm.trans (finSumFinEquiv.sumCongr (Equiv.refl _)))

/-- Reassociate three port classes without changing any port or basis value. -/
def assoc (p : PortPartition W A (append B C)) : PortPartition W (append A B) C where
  index := p.index.trans (assocIndex a b c)
  wire i := (p.wire i).trans (Equiv.cast (by
    cases h : p.index i with
    | inl j => simp [assocIndex, h]
    | inr j => induction j using Fin.addCases <;> simp [assocIndex, h]))

/-- The reassociated partition has exactly the reassociated configuration map. -/
theorem leftTriple_assoc (p : PortPartition W A (append B C)) :
    p.assoc.leftTriple = p.rightTriple.trans (Equiv.prodAssoc _ _ _).symm := by
  apply Equiv.symm_bijective.injective
  ext ⟨⟨x,y⟩,z⟩ i
  change p.assoc.configEquiv.symm ((splitAppendEquiv A B).symm (x,y),z) i =
    p.configEquiv.symm (x,(splitAppendEquiv B C).symm (y,z)) i
  cases h : p.index i with
  | inl j =>
    rw [p.assoc.configEquiv_symm_left (i := Fin.castAdd b j) _ _ i
          (by simp [assoc, assocIndex, h]),
      p.configEquiv_symm_left _ _ i h]
    simp only [splitAppendEquiv_symm_apply, Fin.addCases_left]
    change (p.wire i).symm (cast _ (cast _ (cast _ (x j)))) =
      (p.wire i).symm (cast _ (x j))
    exact congrArg (p.wire i).symm (cast_three_one _ _ _ _ _)
  | inr j =>
    induction j using Fin.addCases with
    | left j =>
      rw [p.assoc.configEquiv_symm_left (i := Fin.natAdd a j) _ _ i
          (by simp [assoc, assocIndex, h]),
        p.configEquiv_symm_right _ _ i h]
      simp only [splitAppendEquiv_symm_apply, Fin.addCases_left, Fin.addCases_right]
      change (p.wire i).symm (cast _ (cast _ (cast _ (y j)))) =
        (p.wire i).symm (cast _ (cast _ (y j)))
      exact congrArg (p.wire i).symm (cast_three_two _ _ _ _ _ _)
    | right j =>
      rw [p.assoc.configEquiv_symm_right (i := j) _ _ i
          (by simp [assoc, assocIndex, h]),
        p.configEquiv_symm_right _ _ i h]
      simp only [splitAppendEquiv_symm_apply, Fin.addCases_right]
      change (p.wire i).symm (cast _ (cast _ (z j))) =
        (p.wire i).symm (cast _ (cast _ (z j)))
      exact congrArg (p.wire i).symm (cast_two_two _ _ _ _ _)

/-- Exchange the second and third blocks of three finite port-index blocks. -/
def middleIndex (a b c : Nat) : (Fin (a + b) ⊕ Fin c) ≃ (Fin (a + c) ⊕ Fin b) :=
  (finSumFinEquiv.symm.sumCongr (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans
      (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans
        ((Equiv.sumAssoc _ _ _).symm.trans (finSumFinEquiv.sumCongr (Equiv.refl _)))))

/-- Exchange the second and third port classes, retaining the first class. -/
def swapMiddle (p : PortPartition W (append A B) C) : PortPartition W (append A C) B where
  index := p.index.trans (middleIndex a b c)
  wire i := (p.wire i).trans (Equiv.cast (by
    cases h : p.index i with
    | inl j => induction j using Fin.addCases <;> simp [middleIndex, h]
    | inr j => simp [middleIndex, h]))

/-- The second/third port exchange agrees with the explicit configuration transport. -/
theorem leftTriple_swapMiddle (p : PortPartition W (append A B) C) :
    p.swapMiddle.leftTriple = p.leftTriple.trans
      ((midSwapEquiv (∀ i, A i) (∀ i, B i) (∀ i, C i)).trans (Equiv.prodComm _ _)) := by
  apply Equiv.symm_bijective.injective
  ext ⟨⟨x,z⟩,y⟩ i
  change p.swapMiddle.configEquiv.symm ((splitAppendEquiv A C).symm (x,z),y) i =
    p.configEquiv.symm ((splitAppendEquiv A B).symm (x,y),z) i
  cases h : p.index i with
  | inl j =>
    induction j using Fin.addCases with
    | left j =>
      rw [p.swapMiddle.configEquiv_symm_left (i := Fin.castAdd c j) _ _ i
          (by simp [swapMiddle, middleIndex, h]),
        p.configEquiv_symm_left _ _ i h]
      simp only [splitAppendEquiv_symm_apply, Fin.addCases_left]
      change (p.wire i).symm (cast _ (cast _ (cast _ (x j)))) =
        (p.wire i).symm (cast _ (cast _ (x j)))
      exact congrArg (p.wire i).symm (cast_three_two _ _ _ _ _ _)
    | right j =>
      rw [p.swapMiddle.configEquiv_symm_right (i := j) _ _ i
          (by simp [swapMiddle, middleIndex, h]),
        p.configEquiv_symm_left _ _ i h]
      simp only [splitAppendEquiv_symm_apply, Fin.addCases_right]
      change (p.wire i).symm (cast _ (cast _ (y j))) =
        (p.wire i).symm (cast _ (cast _ (y j)))
      exact congrArg (p.wire i).symm (cast_two_two _ _ _ _ _)
  | inr j =>
    rw [p.swapMiddle.configEquiv_symm_left (i := Fin.natAdd a j) _ _ i
          (by simp [swapMiddle, middleIndex, h]),
      p.configEquiv_symm_right _ _ i h]
    simp only [splitAppendEquiv_symm_apply, Fin.addCases_right]
    change (p.wire i).symm (cast _ (cast _ (cast _ (z j)))) =
      (p.wire i).symm (cast _ (z j))
    exact congrArg (p.wire i).symm (cast_three_one _ _ _ _ _)

end Regrouping

end PortPartition


section PartitionedMatch
variable {a b l r : Nat} {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
  {L : Fin l → Type u} {R : Fin r → Type u}

/-- Readback from a structural partition of the first factor's ports. -/
theorem partition_read₁ (m : WireMatch W₁ W₂) {S : Fin m.s → Type u}
    (p : PortPartition W₁ L S)
    (hp : ∀ k, p.index (m.ι₁ k) = Sum.inr k)
    (g : ∀ j, m.complFam₁ j) (z : ∀ k, m.connFam₁ k) :
    m.read₁ (g, z) = p.configEquiv.symm
      (p.remainingEquiv m.ι₁ m.hι₁ hp g,
       (Equiv.piCongrRight fun k ↦ p.atRight (m.ι₁ k) (hp k)) z) := by
  funext t
  rcases exists_conn_or_compl m.ι₁ m.hι₁ t with ⟨k, rfl⟩ | ⟨j, rfl⟩
  · rw [m.read₁_conn, p.configEquiv_symm_right _ _ _ (hp k)]
    exact ((p.atRight (m.ι₁ k) (hp k)).symm_apply_apply (z k)).symm
  · rw [m.read₁_compl, p.configEquiv_symm_left _ _ _
      (p.remainingIndex_spec m.ι₁ m.hι₁ hp j), p.remainingEquiv_apply]
    exact ((p.atLeft _ _).symm_apply_apply (g j)).symm

/-- Readback from the second factor's partition. Compatibility is only a
per-wire basis equation at the actual matched endpoint. -/
theorem partition_read₂ (m : WireMatch W₁ W₂) {S : Fin m.s → Type u}
    (p : PortPartition W₁ L S)
    (q : PortPartition W₂ R S)
    (hp : ∀ k, p.index (m.ι₁ k) = Sum.inr k)
    (hq : ∀ k, q.index (m.ι₂ k) = Sum.inr k)
    (he : ∀ k, (m.e k).trans (q.atRight (m.ι₂ k) (hq k)) =
      p.atRight (m.ι₁ k) (hp k))
    (z : ∀ k, m.connFam₁ k) (w : ∀ j, m.complFam₂ j) :
    m.read₂ z w = q.configEquiv.symm
      (q.remainingEquiv m.ι₂ m.hι₂ hq w,
       (Equiv.piCongrRight fun k ↦ p.atRight (m.ι₁ k) (hp k)) z) := by
  funext t
  rcases exists_conn_or_compl m.ι₂ m.hι₂ t with ⟨k, rfl⟩ | ⟨j, rfl⟩
  · rw [m.read₂_conn, q.configEquiv_symm_right _ _ _ (hq k)]
    apply (q.atRight (m.ι₂ k) (hq k)).injective
    rw [Equiv.apply_symm_apply]
    exact congrArg (fun e : m.connFam₁ k ≃ S k ↦ e (z k)) (he k)
  · rw [m.read₂_compl, q.configEquiv_symm_left _ _ _
      (q.remainingIndex_spec m.ι₂ m.hι₂ hq j), q.remainingEquiv_apply]
    exact ((q.atLeft _ _).symm_apply_apply (w j)).symm

/-- The actual matching's complement boundary, expressed in the two private
configuration blocks; this is constructed from the port partitions. -/
def partitionBoundaryEquiv (m : WireMatch W₁ W₂) {S : Fin m.s → Type u}
    (p : PortPartition W₁ L S) (q : PortPartition W₂ R S)
    (hp : ∀ k, p.index (m.ι₁ k) = Sum.inr k)
    (hq : ∀ k, q.index (m.ι₂ k) = Sum.inr k) :
    (∀ i, append m.complFam₁ m.complFam₂ i) ≃ (∀ i, L i) × (∀ i, R i) :=
  (splitAppendEquiv m.complFam₁ m.complFam₂).trans
    ((p.remainingEquiv m.ι₁ m.hι₁ hp).prodCongr
      (q.remainingEquiv m.ι₂ m.hι₂ hq))

/-- The actual matching contraction in the coordinates of two port partitions.
Only endpoint and fiber-equivalence equations are assumed. -/
theorem partition_linkProduct (m : WireMatch W₁ W₂) {S : Fin m.s → Type u}
    (p : PortPartition W₁ L S) (q : PortPartition W₂ R S)
    (hp : ∀ k, p.index (m.ι₁ k) = Sum.inr k)
    (hq : ∀ k, q.index (m.ι₂ k) = Sum.inr k)
    (he : ∀ k, (m.e k).trans (q.atRight (m.ι₂ k) (hq k)) =
      p.atRight (m.ι₁ k) (hp k))
    [∀ k, Fintype (m.connFam₁ k)] [∀ k, Fintype (S k)]
    (M : CMatrix (∀ i, W₁ i)) (N : CMatrix (∀ i, W₂ i)) :
    matReindex (partitionBoundaryEquiv m p q hp hq) (m.linkProduct M N) =
    productLink (matReindex p.configEquiv M)
      (matReindex (q.configEquiv.trans (Equiv.prodComm _ _)) N) := by
  classical
  ext ⟨g, w⟩ ⟨g', w'⟩
  rw [matReindex_apply]
  change m.linkProduct M N
    ((splitAppendEquiv m.complFam₁ m.complFam₂).symm
      ((p.remainingEquiv m.ι₁ m.hι₁ hp).symm g,
       (q.remainingEquiv m.ι₂ m.hι₂ hq).symm w))
    ((splitAppendEquiv m.complFam₁ m.complFam₂).symm
      ((p.remainingEquiv m.ι₁ m.hι₁ hp).symm g',
       (q.remainingEquiv m.ι₂ m.hι₂ hq).symm w')) = _
  rw [m.linkProduct_apply, productLink_apply]
  let e := Equiv.piCongrRight (fun k ↦ p.atRight (m.ι₁ k) (hp k))
  apply Fintype.sum_equiv e
  intro z
  apply Fintype.sum_equiv e
  intro z'
  rw [partition_read₁ m p hp, partition_read₁ m p hp,
    partition_read₂ m p q hp hq he, partition_read₂ m p q hp hq he]
  simp only [Equiv.apply_symm_apply, matReindex_apply, Equiv.symm_trans_apply]
  rfl
end PartitionedMatch

/-- Reindex coherence for arbitrary original port orders. The partitions
supply only positions and per-wire basis identifications. -/
theorem partition_triangle_assoc {a b c ra rb rc x y z : Nat}
    {WA : Fin a → Type u} {WB : Fin b → Type u} {WC : Fin c → Type u}
    {A : Fin ra → Type u} {B : Fin rb → Type u} {C : Fin rc → Type u}
    {X : Fin x → Type u} {Y : Fin y → Type u} {Z : Fin z → Type u}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (pA : PortPartition WA (append A Y) X)
    (pB : PortPartition WB X (append B Z))
    (pC : PortPartition WC (append Y Z) C)
    (M : CMatrix (∀ i, WA i)) (N : CMatrix (∀ i, WB i)) (P : CMatrix (∀ i, WC i)) :
    matReindex (Equiv.prodAssoc (∀ i, A i) (∀ i, B i) (∀ i, C i))
      (triangleLeft (matReindex pA.leftTriple M) (matReindex pB.rightTriple N)
        (matReindex pC.leftTriple P)) =
      triangleRight (matReindex pA.leftTriple M) (matReindex pB.rightTriple N)
        (matReindex pC.leftTriple P) :=
  triangle_assoc _ _ _
end MatchedWire
end QIT.WireFam

end
