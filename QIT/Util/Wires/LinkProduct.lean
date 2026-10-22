/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Wires
public import QIT.Util.Wires.Contraction

/-!
# The link product over heterogeneous wire families

This module realizes the link product of joint matrices over heterogeneous
finite wire families (`QIT.Util.Wires`): the composition rule that connects
two joint matrices along a shared final/initial block of wires, with no
common dimension across wires. The general definition for operators on
arbitrary (generally overlapping) wire index sets is
[Chiribella2009Networks, comblong-pub.tex:315-327]; the original circuit
formulation via the composition rule is
[Chiribella2007Architecture, qcombs-2.tex:223-235].

* **Core definition.** `linkProduct R₁ S R₂ M N` connects `M` on
  `append R₁ S` with `N` on `append S R₂` along the shared block `S`: the
  shared block sits at the end of the first family and at the front of the
  second, and the output lives on `append R₁ R₂`. The shared block of the
  first factor enters transposed (`M (g, z') (g', z)` in the entrywise form
  `linkProduct_apply`), matching the transpose-on-first-factor convention of
  the sources. Linearity in each factor (`linkProduct_add/smul/sub_left/right`)
  is entrywise `Finset` algebra.

* **Shared-block transpose.** `transposeShared R₁ S M` is the partial
  transpose of the shared block of `M`, packaged through `splitAppendEquiv`;
  it is involutive (`transposeShared_involutive`) and, at a single shared
  wire, it is exactly the coordinate `transposeAt` at the last wire
  (`matReindex_splitAppendEquiv_transposeAt`), connecting this layer to the
  contraction layer of `QIT.Util.Wires.Contraction`.

* **Engine bridge.** `linkProduct_eq_engine` expresses the link product as
  the two-system partial trace of a tensor-fashion product:
  `partialTraceA (matReindex midSwapEquiv (engineProduct R₁ S R₂ M N))`,
  where the first factor enters through `QIT.partialTransposeB`. This is the
  shape in which the sources compose Choi operators of higher-order maps
  [Chiribella2009Networks, comblong-pub.tex:295-302].

* **Calibration.** At an empty shared block the link product degenerates to
  the kronecker product of the two factors projected on their private wires
  (`linkProduct_empty`); with both private blocks empty the output is a
  scalar matrix carrying the sum `∑ M (z', default) (z, default) * N (z',
  default) (z, default)` (`linkProduct_full_apply`, `linkProduct_full_trace`).

* **Permutation record.** `linkProduct_permute_left/right` show that
  permuting the private block of one factor permutes the private block of the
  output, and `linkProduct_permute_shared` shows that permuting the shared
  block of both factors simultaneously is invisible (sum reindexing only).
  More generally, `linkProduct_shared_relabel` shows that relabeling the
  shared block of both factors along an arbitrary equivalence of the shared
  configuration spaces (`relabelLeft`/`relabelRight`) is likewise invisible.

* **General matching layer.** `WireMatch W₁ W₂` records a matching of two
  heterogeneous families along `s` connected wire pairs: injective position
  maps on each side (the no-double-connection condition) plus a per-pair
  basis identification `e` directed from the first family to the second.
  `WireMatch.linkProduct m M N` transports both factors into the canonical
  layout (private-then-connected for the first, connected-then-private for
  the second) and applies the core link product; `WireMatch.linkProduct_apply`
  is the entrywise reading through `read₁`/`read₂`, with the shared block of
  the first factor transposed and the second factor read along `e`.
  `WireMatch.symm` reverses a matching, swapping the two sides and inverting
  the basis identifications.

Per [Chiribella2009Networks, comblong-pub.tex:342-355], the swap relation
`M * N = E (N * M) E` holds for arbitrary operators, associativity holds
under the no-triple-overlap condition on the three wire sets, Hermiticity
preservation holds for Hermitian factors, and positivity preservation holds
for positive semidefinite factors (the source proves the last through the
CP Choi correspondence). The swap relation is realized here as
`linkProduct_swap` on the core layer and as `WireMatch.linkProduct_symm` on
the matching layer; associativity is realized on the core layer as
`linkProduct_assoc`, where the wire blocks of the append layout are
disjoint by construction; Hermiticity preservation is realized as
`linkProduct_isHermitian`; and the block-flip/permutation coherence squares
are realized as `appendFlipEquiv_permute_left/right`. Positivity
preservation is deliberately not realized here: it is deferred to the
Choi-composition layer of the library, and no PSD claim is made for
arbitrary matrices.

## Main definitions

* `QIT.WireFam.linkProduct`
* `QIT.WireFam.transposeShared`
* `QIT.WireFam.engineProduct`
* `QIT.WireFam.WireMatch`
* `QIT.WireFam.WireMatch.linkProduct`
* `QIT.WireFam.WireMatch.symm`

## Tags

link product, wire family, composition rule, quantum comb
-/

open scoped BigOperators ComplexOrder MatrixOrder

universe u

@[expose] public section

namespace QIT

namespace WireFam

variable {a b r₁ s r₂ t : ℕ}

/-! ## The core link product -/

/-- The link product of `M` on `append R₁ S` and `N` on `append S R₂` along
the shared block `S`: the shared configurations are contracted, with the
shared block of the first factor transposed (row configuration carrying
`z'`, column carrying `z`), per the general definition
[Chiribella2009Networks, comblong-pub.tex:315-327] and the circuit
composition rule [Chiribella2007Architecture, qcombs-2.tex:223-235]. -/
def linkProduct (R₁ : Fin r₁ → Type u) (S : Fin s → Type u) (R₂ : Fin r₂ → Type u)
    [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i))
    (N : CMatrix (∀ i, append S R₂ i)) : CMatrix (∀ i, append R₁ R₂ i) :=
  fun p q =>
    ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k,
      M ((splitAppendEquiv R₁ S).symm ((splitAppendEquiv R₁ R₂ p).1, z'))
        ((splitAppendEquiv R₁ S).symm ((splitAppendEquiv R₁ R₂ q).1, z)) *
      N ((splitAppendEquiv S R₂).symm (z', (splitAppendEquiv R₁ R₂ p).2))
        ((splitAppendEquiv S R₂).symm (z, (splitAppendEquiv R₁ R₂ q).2))

/-- Entrywise form of `linkProduct` at packaged configurations: the shared
block of the first factor enters transposed. -/
theorem linkProduct_apply (R₁ : Fin r₁ → Type u) (S : Fin s → Type u) (R₂ : Fin r₂ → Type u)
    [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i))
    (g g' : ∀ i, R₁ i) (w w' : ∀ j, R₂ j) :
    linkProduct R₁ S R₂ M N ((splitAppendEquiv R₁ R₂).symm (g, w))
        ((splitAppendEquiv R₁ R₂).symm (g', w')) =
      ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k,
        M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
          N ((splitAppendEquiv S R₂).symm (z', w)) ((splitAppendEquiv S R₂).symm (z, w')) := by
  simp only [linkProduct]
  rw [Equiv.apply_symm_apply (splitAppendEquiv R₁ R₂) (g, w),
    Equiv.apply_symm_apply (splitAppendEquiv R₁ R₂) (g', w')]

/-! ## Associativity of the core link product -/

/-- Associativity of the core link product: for factors on three consecutive
append layouts `append R₁ S`, `append S R₂`, `append R₂ T`, both groupings
contract the shared blocks `S` and `R₂` to the same four-fold sum. The wire
blocks of the append layout are pairwise disjoint by construction, so the
no-triple-overlap condition of the source is automatic on the core layer
[Chiribella2009Networks, comblong-pub.tex:342-355]. -/
theorem linkProduct_assoc (R₁ : Fin r₁ → Type u) (S : Fin s → Type u) (R₂ : Fin r₂ → Type u)
    (T : Fin t → Type u) [∀ k, Fintype (S k)] [∀ j, Fintype (R₂ j)]
    (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i))
    (P : CMatrix (∀ i, append R₂ T i)) :
    linkProduct R₁ R₂ T (linkProduct R₁ S R₂ M N) P =
      linkProduct R₁ S T M (linkProduct S R₂ T N P) := by
  ext p q
  rcases hp : splitAppendEquiv R₁ T p with ⟨g, u⟩
  rcases hq : splitAppendEquiv R₁ T q with ⟨g', u'⟩
  have hp2 : p = (splitAppendEquiv R₁ T).symm (g, u) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ T).symm (g', u') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2]
  simp only [linkProduct_apply]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  -- Normalize the instance annotations on `∑`/`·*·` to the canonical
  -- `Complex.instAddCommMonoid`/`Complex.instMul`: the simp normal form of
  -- `Finset.sum_mul`/`mul_sum` leaves the algebra-hierarchy projection paths
  -- of the elaborated `ℂ` instances in place, and the four-fold `sum_comm`
  -- chain below is keyed to the canonical instances. The `rfl` equalities are
  -- definitional, but the exact projection paths are an elaboration artifact
  -- of the current Mathlib instance graph; after a Mathlib bump, re-derive
  -- them from the new goal rather than adjusting by hand.
  rw [(rfl : (@NonUnitalNonAssocSemiring.toAddCommMonoid ℂ (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ℂ (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ℂ (@NonUnitalCommRing.toNonUnitalNonAssocCommRing ℂ Complex.instNonUnitalCommRing)))) = Complex.instAddCommMonoid),
    (rfl : @instHMul ℂ (@Semigroup.toMul ℂ (@SemigroupWithZero.toSemigroup ℂ (@NonUnitalSemiring.toSemigroupWithZero ℂ (@NonUnitalCommSemiring.toNonUnitalSemiring ℂ (@NonUnitalCommRing.toNonUnitalCommSemiring ℂ Complex.instNonUnitalCommRing))))) = @instHMul ℂ Complex.instMul),
    (rfl : @instHMul ℂ (@Distrib.toMul ℂ (@NonUnitalNonAssocSemiring.toDistrib ℂ (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ℂ (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ℂ (@NonUnitalCommRing.toNonUnitalNonAssocCommRing ℂ Complex.instNonUnitalCommRing))))) = @instHMul ℂ Complex.instMul)]
  have hstep1 : ∑ y : ∀ j, R₂ j, ∑ y' : ∀ j, R₂ j, ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) =
      ∑ y : ∀ j, R₂ j, ∑ z : ∀ k, S k, ∑ y' : ∀ j, R₂ j, ∑ z' : ∀ k, S k,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) :=
    Finset.sum_congr rfl fun y _ => Finset.sum_comm
  have hstep2 : ∑ y : ∀ j, R₂ j, ∑ z : ∀ k, S k, ∑ y' : ∀ j, R₂ j, ∑ z' : ∀ k, S k,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) =
      ∑ z : ∀ k, S k, ∑ y : ∀ j, R₂ j, ∑ y' : ∀ j, R₂ j, ∑ z' : ∀ k, S k,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) :=
    Finset.sum_comm
  have hstep3 : ∑ z : ∀ k, S k, ∑ y : ∀ j, R₂ j, ∑ y' : ∀ j, R₂ j, ∑ z' : ∀ k, S k,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) =
      ∑ z : ∀ k, S k, ∑ y : ∀ j, R₂ j, ∑ z' : ∀ k, S k, ∑ y' : ∀ j, R₂ j,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) :=
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm
  have hstep4 : ∑ z : ∀ k, S k, ∑ y : ∀ j, R₂ j, ∑ z' : ∀ k, S k, ∑ y' : ∀ j, R₂ j,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) =
      ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k, ∑ y : ∀ j, R₂ j, ∑ y' : ∀ j, R₂ j,
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
        (N ((splitAppendEquiv S R₂).symm (z', y')) ((splitAppendEquiv S R₂).symm (z, y)) *
          P ((splitAppendEquiv R₂ T).symm (y', u)) ((splitAppendEquiv R₂ T).symm (y, u'))) :=
    Finset.sum_congr rfl fun z _ => Finset.sum_comm
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

/-! ## Linearity in each factor -/

/-- The link product is additive in the first factor. -/
theorem linkProduct_add_left (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (M M' : CMatrix (∀ i, append R₁ S i))
    (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ (M + M') N = linkProduct R₁ S R₂ M N + linkProduct R₁ S R₂ M' N := by
  ext p q
  simp only [linkProduct, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The link product is additive in the second factor. -/
theorem linkProduct_add_right (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i))
    (N N' : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ M (N + N') = linkProduct R₁ S R₂ M N + linkProduct R₁ S R₂ M N' := by
  ext p q
  simp only [linkProduct, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- The link product is homogeneous in the first factor. -/
theorem linkProduct_smul_left (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (c : ℂ) (M : CMatrix (∀ i, append R₁ S i))
    (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ (c • M) N = c • linkProduct R₁ S R₂ M N := by
  ext p q
  simp only [linkProduct, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The link product is homogeneous in the second factor. -/
theorem linkProduct_smul_right (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (c : ℂ) (M : CMatrix (∀ i, append R₁ S i))
    (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ M (c • N) = c • linkProduct R₁ S R₂ M N := by
  ext p q
  simp only [linkProduct, Matrix.smul_apply, smul_eq_mul, mul_left_comm, Finset.mul_sum]

/-- The link product is subtractive in the first factor. -/
theorem linkProduct_sub_left (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (M M' : CMatrix (∀ i, append R₁ S i))
    (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ (M - M') N = linkProduct R₁ S R₂ M N - linkProduct R₁ S R₂ M' N := by
  ext p q
  simp only [linkProduct, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The link product is subtractive in the second factor. -/
theorem linkProduct_sub_right (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i))
    (N N' : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ M (N - N') = linkProduct R₁ S R₂ M N - linkProduct R₁ S R₂ M N' := by
  ext p q
  simp only [linkProduct, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-! ## Conjugate transpose and Hermitian closure -/

/-- The conjugate transpose passes through the link product factorwise: the
transpose built into the shared-block contraction absorbs the factor
reversal, so the factors stay in place. Entrywise this is the pairwise
swap of the contracted pair [Chiribella2009Networks, comblong-pub.tex:342-355]. -/
theorem linkProduct_conjTranspose (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i))
    (N : CMatrix (∀ i, append S R₂ i)) :
    Matrix.conjTranspose (linkProduct R₁ S R₂ M N) =
      linkProduct R₁ S R₂ (Matrix.conjTranspose M) (Matrix.conjTranspose N) := by
  ext p q
  rcases hp : splitAppendEquiv R₁ R₂ p with ⟨g, w⟩
  rcases hq : splitAppendEquiv R₁ R₂ q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv R₁ R₂).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ R₂).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [Matrix.conjTranspose_apply, hp2, hq2]
  simp only [linkProduct_apply, star_sum, star_mul, Matrix.conjTranspose_apply]
  have hcanon : ∑ x : ∀ k, S k, ∑ x' : ∀ k, S k,
      star (N ((splitAppendEquiv S R₂).symm (x', w')) ((splitAppendEquiv S R₂).symm (x, w))) *
        star (M ((splitAppendEquiv R₁ S).symm (g', x')) ((splitAppendEquiv R₁ S).symm (g, x))) =
      ∑ x : ∀ k, S k, ∑ x' : ∀ k, S k,
      star (M ((splitAppendEquiv R₁ S).symm (g', x')) ((splitAppendEquiv R₁ S).symm (g, x))) *
        star (N ((splitAppendEquiv S R₂).symm (x', w')) ((splitAppendEquiv S R₂).symm (x, w))) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => mul_comm _ _
  have hswap : ∑ x : ∀ k, S k, ∑ x' : ∀ k, S k,
      star (M ((splitAppendEquiv R₁ S).symm (g', x')) ((splitAppendEquiv R₁ S).symm (g, x))) *
        star (N ((splitAppendEquiv S R₂).symm (x', w')) ((splitAppendEquiv S R₂).symm (x, w))) =
      ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k,
      star (M ((splitAppendEquiv R₁ S).symm (g', z)) ((splitAppendEquiv R₁ S).symm (g, z'))) *
        star (N ((splitAppendEquiv S R₂).symm (z, w')) ((splitAppendEquiv S R₂).symm (z', w))) :=
    Finset.sum_comm
  exact hcanon.trans hswap

/-- The link product of Hermitian factors is Hermitian
[Chiribella2009Networks, comblong-pub.tex:342-355]. -/
theorem linkProduct_isHermitian (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] {M : CMatrix (∀ i, append R₁ S i)}
    {N : CMatrix (∀ i, append S R₂ i)} (hM : M.IsHermitian) (hN : N.IsHermitian) :
    (linkProduct R₁ S R₂ M N).IsHermitian := by
  rw [Matrix.IsHermitian, linkProduct_conjTranspose, hM, hN]

/-! ## Partial transpose on the shared block -/

/-- Partial transpose on the shared block of the first operand, packaged
through `splitAppendEquiv`. -/
def transposeShared (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (M : CMatrix (∀ i, append R₁ S i)) : CMatrix (∀ i, append R₁ S i) :=
  matReindex (splitAppendEquiv R₁ S).symm
    (QIT.partialTransposeB (matReindex (splitAppendEquiv R₁ S) M))

/-- Entrywise form of `transposeShared`: the shared-block values of the row
and column configurations are exchanged. -/
@[simp]
theorem transposeShared_apply (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (M : CMatrix (∀ i, append R₁ S i)) (g g' : ∀ i, R₁ i) (z z' : ∀ k, S k) :
    transposeShared R₁ S M ((splitAppendEquiv R₁ S).symm (g, z))
        ((splitAppendEquiv R₁ S).symm (g', z')) =
      M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) := by
  simp only [transposeShared, matReindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    QIT.partialTransposeB_apply]

/-- The shared-block transpose is involutive. -/
@[simp]
theorem transposeShared_involutive (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (M : CMatrix (∀ i, append R₁ S i)) :
    transposeShared R₁ S (transposeShared R₁ S M) = M := by
  have hcancel : ∀ Z : CMatrix ((∀ i, R₁ i) × (∀ k, S k)),
      matReindex (splitAppendEquiv R₁ S) (matReindex (splitAppendEquiv R₁ S).symm Z) = Z := by
    intro Z
    rw [← matReindex_trans_apply, Equiv.symm_trans_self, matReindex_refl]
  have hcancel' : ∀ Z : CMatrix (∀ i, append R₁ S i),
      matReindex (splitAppendEquiv R₁ S).symm (matReindex (splitAppendEquiv R₁ S) Z) = Z := by
    intro Z
    rw [← matReindex_trans_apply, Equiv.self_trans_symm, matReindex_refl]
  simp only [transposeShared]
  rw [hcancel, QIT.partialTransposeB_involutive, hcancel']

/-- Entrywise form of `transposeShared` at raw points: the shared-block values
of the row and column configurations are exchanged. -/
theorem transposeShared_apply' (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (M : CMatrix (∀ i, append R₁ S i)) (x y : ∀ i, append R₁ S i) :
    transposeShared R₁ S M x y = M ((splitAppendEquiv R₁ S).symm
        ((splitAppendEquiv R₁ S x).1, (splitAppendEquiv R₁ S y).2))
      ((splitAppendEquiv R₁ S).symm ((splitAppendEquiv R₁ S y).1,
        (splitAppendEquiv R₁ S x).2)) :=
  rfl

/-! ## The single-shared-wire connector to the contraction layer -/

/-- The shared-block configuration of a single shared wire, read as a value on
the last wire of the appended family. -/
def sharedWireLast (R₁ : Fin r₁ → Type u) (S : Fin 1 → Type u) (z : ∀ k : Fin 1, S k) :
    append R₁ S (Fin.last (n := r₁)) :=
  lastWireEquiv (append R₁ S) (fun j => Equiv.cast (append_natAdd R₁ S j).symm (z j))

/-- The first-family configuration of a single shared wire, read in the
succAbove-kept coordinates of the last wire. -/
def keptConfigLast (R₁ : Fin r₁ → Type u) (S : Fin 1 → Type u) (g : ∀ i, R₁ i) :
    ∀ j : Fin r₁, append R₁ S ((Fin.last (n := r₁)).succAbove j) :=
  lastKeepEquiv (append R₁ S) (fun i => Equiv.cast (append_castAdd R₁ S i).symm (g i))

/-- Assembly bridge at a single shared wire: splitting `symm (g, z)` is
inserting the wire value at the last position. -/
theorem splitAppendEquiv_symm_eq_insertNth (R₁ : Fin r₁ → Type u) (S : Fin 1 → Type u)
    (g : ∀ i, R₁ i) (z : ∀ k : Fin 1, S k) :
    (splitAppendEquiv R₁ S).symm (g, z) =
      Fin.insertNth (Fin.last (n := r₁)) (sharedWireLast R₁ S z) (keptConfigLast R₁ S g) := by
  rw [splitAppendEquiv_symm_apply, ← addCases_last]
  rw [keptConfigLast, Equiv.symm_apply_apply, sharedWireLast, Equiv.symm_apply_apply]

/-- THE single-shared-wire connector: at a single shared wire,
`transposeShared` is the coordinate partial transpose at the last wire,
packaged through `splitAppendEquiv`. -/
theorem matReindex_splitAppendEquiv_transposeAt (R₁ : Fin r₁ → Type u) (S : Fin 1 → Type u)
    (M : CMatrix (∀ i, append R₁ S i)) :
    matReindex (splitAppendEquiv R₁ S) (transposeAt (append R₁ S) (Fin.last (n := r₁)) M) =
      QIT.partialTransposeB (matReindex (splitAppendEquiv R₁ S) M) := by
  ext ⟨g, z⟩ ⟨g', z'⟩
  simp only [matReindex_apply, transposeAt_apply, QIT.partialTransposeB_apply]
  rw [splitAppendEquiv_symm_eq_insertNth R₁ S g z,
    splitAppendEquiv_symm_eq_insertNth R₁ S g' z',
    splitAppendEquiv_symm_eq_insertNth R₁ S g z',
    splitAppendEquiv_symm_eq_insertNth R₁ S g' z]
  simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]

/-! ## The engine bridge: partial trace of a tensor-fashion product -/

/-- Move the middle factor of a nested triple to the front. -/
def midSwapEquiv (α β γ : Type*) : (α × β) × γ ≃ β × (α × γ) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reading through `midSwapEquiv.symm`: the middle factor returns to its
nested position. -/
theorem midSwapEquiv_symm_apply (α β γ : Type*) (q : β × (α × γ)) :
    (midSwapEquiv α β γ).symm q = ((q.2.1, q.1), q.2.2) := rfl

/-- The tensor-fashion product of the partially transposed first factor with
the second factor, on the packaged triple layout. -/
def engineProduct (R₁ : Fin r₁ → Type u) (S : Fin s → Type u) (R₂ : Fin r₂ → Type u)
    [∀ k, Fintype (S k)] [∀ i, Fintype (R₁ i)] [∀ j, Fintype (R₂ j)]
    [∀ i, DecidableEq (R₁ i)] [∀ j, DecidableEq (R₂ j)]
    (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    CMatrix (((∀ i, R₁ i) × (∀ k, S k)) × (∀ j, R₂ j)) :=
  Matrix.kronecker (QIT.partialTransposeB (matReindex (splitAppendEquiv R₁ S) M))
      (1 : CMatrix (∀ j, R₂ j)) *
    matReindex (Equiv.prodAssoc (∀ i, R₁ i) (∀ k, S k) (∀ j, R₂ j)).symm
      (Matrix.kronecker (1 : CMatrix (∀ i, R₁ i)) (matReindex (splitAppendEquiv S R₂) N))

/-- Engine bridge: the link product is the two-system partial trace of the
tensor-fashion product of the partially transposed first factor with the
second factor, in the shape in which the sources compose Choi operators
[Chiribella2009Networks, comblong-pub.tex:295-302]. -/
theorem linkProduct_eq_engine (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] [∀ i, Fintype (R₁ i)]
    [∀ j, Fintype (R₂ j)] [∀ i, DecidableEq (R₁ i)] [∀ j, DecidableEq (R₂ j)]
    (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ M N =
      matReindex (splitAppendEquiv R₁ R₂).symm
        (QIT.partialTraceA (matReindex (midSwapEquiv _ _ _) (engineProduct R₁ S R₂ M N))) := by
  ext p q
  rw [matReindex_apply, Equiv.symm_symm]
  rcases hp : splitAppendEquiv R₁ R₂ p with ⟨g, w⟩
  rcases hq : splitAppendEquiv R₁ R₂ q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv R₁ R₂).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ R₂).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, linkProduct_apply]
  simp only [QIT.partialTraceA, matReindex_apply, midSwapEquiv_symm_apply, engineProduct,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply,
    QIT.partialTransposeB_apply, Equiv.symm_symm, Equiv.prodAssoc_apply,
    Fintype.sum_prod_type]
  -- Collapse of the innermost `R₂`-sum: the identity delta selects `b = w`.
  have hR₂ : ∀ (t : ∀ k, S k) (g₁ : ∀ l, R₁ l) (y : ∀ k, S k),
      ∑ b : ∀ j, R₂ j,
        (M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (g₁, t)) *
            (if w = b then (1 : ℂ) else 0)) *
          ((if g₁ = g' then (1 : ℂ) else 0) *
            N ((splitAppendEquiv S R₂).symm (y, b)) ((splitAppendEquiv S R₂).symm (t, w'))) =
      M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (g₁, t)) *
        ((if g₁ = g' then (1 : ℂ) else 0) *
          N ((splitAppendEquiv S R₂).symm (y, w)) ((splitAppendEquiv S R₂).symm (t, w'))) := by
    intro t g₁ y
    refine (Finset.sum_eq_single w ?_ ?_).trans ?_
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hcon
      exact absurd (Finset.mem_univ w) hcon
    · simp
  -- Collapse of the `R₁`-sum: the identity delta selects `a = g'`.
  have hR₁ : ∀ (y : ∀ k, S k) (t : ∀ k, S k),
      ∑ a : ∀ l, R₁ l,
        M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (a, t)) *
          ((if a = g' then (1 : ℂ) else 0) *
            N ((splitAppendEquiv S R₂).symm (y, w)) ((splitAppendEquiv S R₂).symm (t, w'))) =
      M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (g', t)) *
        N ((splitAppendEquiv S R₂).symm (y, w)) ((splitAppendEquiv S R₂).symm (t, w')) := by
    intro y t
    refine (Finset.sum_eq_single g' ?_ ?_).trans ?_
    · intro b _ hb
      simp [hb]
    · intro hcon
      exact absurd (Finset.mem_univ g') hcon
    · simp
  -- Assemble: collapse the `R₂`-delta, commute the `R₁`/`S` sums, collapse the
  -- `R₁`-delta; the remaining double `S`-sum is the entrywise link product.
  symm
  calc (∑ i : ∀ k, S k, ∑ x : ∀ l, R₁ l, ∑ y : ∀ k, S k, ∑ b : ∀ j, R₂ j,
          (M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (x, i)) *
              (if w = b then (1 : ℂ) else 0)) *
            ((if x = g' then (1 : ℂ) else 0) *
              N ((splitAppendEquiv S R₂).symm (y, b)) ((splitAppendEquiv S R₂).symm (i, w')))) =
        ∑ i : ∀ k, S k, ∑ x : ∀ l, R₁ l, ∑ y : ∀ k, S k,
          M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (x, i)) *
            ((if x = g' then (1 : ℂ) else 0) *
              N ((splitAppendEquiv S R₂).symm (y, w)) ((splitAppendEquiv S R₂).symm (i, w'))) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => hR₂ i x y
    _ = ∑ i : ∀ k, S k, ∑ y : ∀ k, S k, ∑ x : ∀ l, R₁ l,
          M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (x, i)) *
            ((if x = g' then (1 : ℂ) else 0) *
              N ((splitAppendEquiv S R₂).symm (y, w)) ((splitAppendEquiv S R₂).symm (i, w'))) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : ∀ k, S k, ∑ y : ∀ k, S k,
          M ((splitAppendEquiv R₁ S).symm (g, y)) ((splitAppendEquiv R₁ S).symm (g', i)) *
            N ((splitAppendEquiv S R₂).symm (y, w)) ((splitAppendEquiv S R₂).symm (i, w')) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun y _ => hR₁ y i
    _ = ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k,
          M ((splitAppendEquiv R₁ S).symm (g, z')) ((splitAppendEquiv R₁ S).symm (g', z)) *
            N ((splitAppendEquiv S R₂).symm (z', w)) ((splitAppendEquiv S R₂).symm (z, w')) :=
      rfl

/-! ## Calibration -/

instance instUniqueAppendEmpty {R₁ R₂ : Fin 0 → Type u} :
    Unique (∀ i : Fin (0 + 0), append R₁ R₂ i) :=
  inferInstanceAs (Unique (∀ i : Fin 0, append R₁ R₂ i))

/-- At an empty shared block, the link product is the kronecker product of
the two factors, each projected onto its private wires, repackaged through
the split transport: the `tensorLink` degeneration of the general
definition [Chiribella2009Networks, comblong-pub.tex:315-327]. -/
theorem linkProduct_empty (R₁ : Fin r₁ → Type u) (S : Fin 0 → Type u) (R₂ : Fin r₂ → Type u)
    [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ M N =
      matReindex (splitAppendEquiv R₁ R₂).symm
        (Matrix.kronecker
          (matReindex ((splitAppendEquiv R₁ S).trans (Equiv.prodUnique _ _)) M)
          (matReindex ((splitAppendEquiv S R₂).trans
            ((Equiv.prodComm _ _).trans (Equiv.prodUnique _ _))) N)) := by
  ext p q
  rw [matReindex_apply, Equiv.symm_symm]
  rcases hp : splitAppendEquiv R₁ R₂ p with ⟨g, w⟩
  rcases hq : splitAppendEquiv R₁ R₂ q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv R₁ R₂).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ R₂).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, linkProduct_apply]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- With both private blocks empty, the unique output entry of the link
product is the full contraction of the two shared-only factors. -/
theorem linkProduct_full_apply (R₁ : Fin 0 → Type u) (S : Fin s → Type u) (R₂ : Fin 0 → Type u)
    [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ M N ((splitAppendEquiv R₁ R₂).symm (default, default))
        ((splitAppendEquiv R₁ R₂).symm (default, default)) =
      ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k,
        M ((splitAppendEquiv R₁ S).symm (default, z')) ((splitAppendEquiv R₁ S).symm (default, z)) *
          N ((splitAppendEquiv S R₂).symm (z', default)) ((splitAppendEquiv S R₂).symm (z, default)) := by
  rw [linkProduct_apply]

/-- Trace form of the fully contracted calibration: the scalar
`linkProduct` at empty private blocks is the trace of the tensor-fashion
product of the second factor with the shared-transposed first factor. -/
theorem linkProduct_full_trace (R₁ : Fin 0 → Type u) (S : Fin s → Type u) (R₂ : Fin 0 → Type u)
    [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    (linkProduct R₁ S R₂ M N).trace =
      ∑ z : ∀ k, S k, ∑ z' : ∀ k, S k,
        M ((splitAppendEquiv R₁ S).symm (default, z')) ((splitAppendEquiv R₁ S).symm (default, z)) *
          N ((splitAppendEquiv S R₂).symm (z', default)) ((splitAppendEquiv S R₂).symm (z, default)) := by
  simp only [Matrix.trace, Matrix.diag, Finset.univ_unique, Finset.sum_singleton]
  have hu : (splitAppendEquiv R₁ R₂).symm (default, default) = default := Subsingleton.elim _ _
  rw [← hu, linkProduct_full_apply]

/-! ## Permutation compatibility -/

/-- Permuting the first block of an append family: split, permute the first
component, reassemble. -/
def permuteAppendLeftEquiv (R₁ : Fin r₁ → Type u) (T : Fin t → Type u) (σ : Fin r₁ ≃ Fin r₁) :
    (∀ i, append R₁ T i) ≃ (∀ i, append (permute R₁ σ) T i) :=
  Equiv.trans (splitAppendEquiv R₁ T)
    (Equiv.trans ((permuteEquiv R₁ σ).prodCongr (Equiv.refl _))
      (splitAppendEquiv (permute R₁ σ) T).symm)

/-- Permuting the second block of an append family. -/
def permuteAppendRightEquiv (S : Fin s → Type u) (T : Fin t → Type u) (τ : Fin t ≃ Fin t) :
    (∀ i, append S T i) ≃ (∀ i, append S (permute T τ) i) :=
  Equiv.trans (splitAppendEquiv S T)
    (Equiv.trans ((Equiv.refl _).prodCongr (permuteEquiv T τ))
      (splitAppendEquiv S (permute T τ)).symm)

/-- Reading a permuted-first-block packaged point back through
`permuteAppendLeftEquiv`: the shared block is untouched. -/
theorem permuteAppendLeftEquiv_symm_pack (R₁ : Fin r₁ → Type u) (T : Fin t → Type u)
    (σ : Fin r₁ ≃ Fin r₁) (g : ∀ i, permute R₁ σ i) (z : ∀ j, T j) :
    (permuteAppendLeftEquiv R₁ T σ).symm
        ((splitAppendEquiv (permute R₁ σ) T).symm (g, z)) =
      (splitAppendEquiv R₁ T).symm ((permuteEquiv R₁ σ).symm g, z) := by
  simp [permuteAppendLeftEquiv, Equiv.trans_apply]

/-- Reading a permuted-second-block packaged point back through
`permuteAppendRightEquiv`: the first block is untouched. -/
theorem permuteAppendRightEquiv_symm_pack (S : Fin s → Type u) (T : Fin t → Type u)
    (τ : Fin t ≃ Fin t) (z : ∀ k, S k) (w : ∀ j, permute T τ j) :
    (permuteAppendRightEquiv S T τ).symm
        ((splitAppendEquiv S (permute T τ)).symm (z, w)) =
      (splitAppendEquiv S T).symm (z, (permuteEquiv T τ).symm w) := by
  simp [permuteAppendRightEquiv, Equiv.trans_apply]

/-- Permuting the private block of the first factor permutes the private block
of the output. -/
theorem linkProduct_permute_left (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (σ : Fin r₁ ≃ Fin r₁)
    (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct (permute R₁ σ) S R₂ (matReindex (permuteAppendLeftEquiv R₁ S σ) M) N =
      matReindex (permuteAppendLeftEquiv R₁ R₂ σ) (linkProduct R₁ S R₂ M N) := by
  ext p q
  rw [matReindex_apply]
  rcases hp : splitAppendEquiv (permute R₁ σ) R₂ p with ⟨g, w⟩
  rcases hq : splitAppendEquiv (permute R₁ σ) R₂ q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv (permute R₁ σ) R₂).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv (permute R₁ σ) R₂).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, linkProduct_apply]
  simp only [matReindex_apply, permuteAppendLeftEquiv_symm_pack]
  rw [linkProduct_apply]

/-- Permuting the private block of the second factor permutes the private block
of the output. -/
theorem linkProduct_permute_right (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (τ : Fin r₂ ≃ Fin r₂)
    (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S (permute R₂ τ) M (matReindex (permuteAppendRightEquiv S R₂ τ) N) =
      matReindex (permuteAppendRightEquiv R₁ R₂ τ) (linkProduct R₁ S R₂ M N) := by
  ext p q
  rw [matReindex_apply]
  rcases hp : splitAppendEquiv R₁ (permute R₂ τ) p with ⟨g, w⟩
  rcases hq : splitAppendEquiv R₁ (permute R₂ τ) q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv R₁ (permute R₂ τ)).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ (permute R₂ τ)).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, linkProduct_apply]
  simp only [matReindex_apply, permuteAppendRightEquiv_symm_pack]
  rw [linkProduct_apply]

/-- Permuting the shared block of both factors simultaneously leaves the link
product unchanged: it only reindexes the contracted sums. -/
theorem linkProduct_permute_shared (R₁ : Fin r₁ → Type u) (S : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] (τ : Fin s ≃ Fin s)
    (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ (permute S τ) R₂
        (matReindex (permuteAppendRightEquiv R₁ S τ) M)
        (matReindex (permuteAppendLeftEquiv S R₂ τ) N) =
      linkProduct R₁ S R₂ M N := by
  ext p q
  rcases hp : splitAppendEquiv R₁ R₂ p with ⟨g, w⟩
  rcases hq : splitAppendEquiv R₁ R₂ q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv R₁ R₂).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ R₂).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, linkProduct_apply, linkProduct_apply]
  simp only [matReindex_apply, permuteAppendRightEquiv_symm_pack,
    permuteAppendLeftEquiv_symm_pack]
  calc ∑ z : ∀ k, permute S τ k, ∑ z' : ∀ k, permute S τ k,
        M ((splitAppendEquiv R₁ S).symm (g, (permuteEquiv S τ).symm z'))
            ((splitAppendEquiv R₁ S).symm (g', (permuteEquiv S τ).symm z)) *
          N ((splitAppendEquiv S R₂).symm ((permuteEquiv S τ).symm z', w))
            ((splitAppendEquiv S R₂).symm ((permuteEquiv S τ).symm z, w')) =
      ∑ z : ∀ k, permute S τ k, ∑ y' : ∀ k, S k,
        M ((splitAppendEquiv R₁ S).symm (g, y'))
            ((splitAppendEquiv R₁ S).symm (g', (permuteEquiv S τ).symm z)) *
          N ((splitAppendEquiv S R₂).symm (y', w))
            ((splitAppendEquiv S R₂).symm ((permuteEquiv S τ).symm z, w')) :=
        Finset.sum_congr rfl fun z _ =>
          Equiv.sum_comp (permuteEquiv S τ).symm
            (fun y' => M ((splitAppendEquiv R₁ S).symm (g, y'))
              ((splitAppendEquiv R₁ S).symm (g', (permuteEquiv S τ).symm z)) *
              N ((splitAppendEquiv S R₂).symm (y', w))
                ((splitAppendEquiv S R₂).symm ((permuteEquiv S τ).symm z, w')))
    _ = ∑ y : ∀ k, S k, ∑ y' : ∀ k, S k,
        M ((splitAppendEquiv R₁ S).symm (g, y')) ((splitAppendEquiv R₁ S).symm (g', y)) *
          N ((splitAppendEquiv S R₂).symm (y', w)) ((splitAppendEquiv S R₂).symm (y, w')) :=
        Equiv.sum_comp (permuteEquiv S τ).symm
          (fun y => ∑ y' : ∀ k, S k,
            M ((splitAppendEquiv R₁ S).symm (g, y')) ((splitAppendEquiv R₁ S).symm (g', y)) *
              N ((splitAppendEquiv S R₂).symm (y', w)) ((splitAppendEquiv S R₂).symm (y, w')))

/-! ## Shared-block relabeling -/

/-- Relabeling the shared block of a first factor along `E`. -/
def relabelLeft (R₁ : Fin r₁ → Type u) {S S' : Fin s → Type u} (E : (∀ k, S k) ≃ (∀ k, S' k)) :
    (∀ i, append R₁ S i) ≃ (∀ i, append R₁ S' i) :=
  (splitAppendEquiv R₁ S).trans
    (((Equiv.refl _).prodCongr E).trans (splitAppendEquiv R₁ S').symm)

/-- Relabeling the shared block of a second factor along `E`. -/
def relabelRight {S S' : Fin s → Type u} (R₂ : Fin r₂ → Type u) (E : (∀ k, S k) ≃ (∀ k, S' k)) :
    (∀ i, append S R₂ i) ≃ (∀ i, append S' R₂ i) :=
  (splitAppendEquiv S R₂).trans
    ((E.prodCongr (Equiv.refl _)).trans (splitAppendEquiv S' R₂).symm)

/-- Reading a shared-relabeled packaged point back through `relabelLeft`: the
private block is untouched and the shared block reads along `E.symm`. -/
theorem relabelLeft_symm_pack (R₁ : Fin r₁ → Type u) {S S' : Fin s → Type u}
    (E : (∀ k, S k) ≃ (∀ k, S' k)) (g : ∀ i, R₁ i) (z' : ∀ k, S' k) :
    (relabelLeft R₁ E).symm ((splitAppendEquiv R₁ S').symm (g, z')) =
      (splitAppendEquiv R₁ S).symm (g, E.symm z') := by
  simp [relabelLeft]

/-- Reading a shared-relabeled packaged point back through `relabelRight`: the
private block is untouched and the shared block reads along `E.symm`. -/
theorem relabelRight_symm_pack {S S' : Fin s → Type u} (R₂ : Fin r₂ → Type u)
    (E : (∀ k, S k) ≃ (∀ k, S' k)) (z' : ∀ k, S' k) (w : ∀ j, R₂ j) :
    (relabelRight R₂ E).symm ((splitAppendEquiv S' R₂).symm (z', w)) =
      (splitAppendEquiv S R₂).symm (E.symm z', w) := by
  simp [relabelRight]

/-- Relabeling the shared block of both factors along the same equivalence
leaves the link product unchanged: like `linkProduct_permute_shared`, it only
reindexes the contracted sums. -/
theorem linkProduct_shared_relabel (R₁ : Fin r₁ → Type u) (S S' : Fin s → Type u)
    (R₂ : Fin r₂ → Type u) [∀ k, Fintype (S k)] [∀ k, Fintype (S' k)]
    (E : (∀ k, S k) ≃ (∀ k, S' k)) (M : CMatrix (∀ i, append R₁ S i))
    (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S' R₂ (matReindex (relabelLeft R₁ E) M)
        (matReindex (relabelRight R₂ E) N) =
      linkProduct R₁ S R₂ M N := by
  ext p q
  rcases hp : splitAppendEquiv R₁ R₂ p with ⟨g, w⟩
  rcases hq : splitAppendEquiv R₁ R₂ q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv R₁ R₂).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ R₂).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, linkProduct_apply, linkProduct_apply]
  simp only [matReindex_apply, relabelLeft_symm_pack, relabelRight_symm_pack]
  calc ∑ z : ∀ k, S' k, ∑ z' : ∀ k, S' k,
        M ((splitAppendEquiv R₁ S).symm (g, E.symm z'))
            ((splitAppendEquiv R₁ S).symm (g', E.symm z)) *
          N ((splitAppendEquiv S R₂).symm (E.symm z', w))
            ((splitAppendEquiv S R₂).symm (E.symm z, w')) =
      ∑ z : ∀ k, S' k, ∑ y' : ∀ k, S k,
        M ((splitAppendEquiv R₁ S).symm (g, y'))
            ((splitAppendEquiv R₁ S).symm (g', E.symm z)) *
          N ((splitAppendEquiv S R₂).symm (y', w))
            ((splitAppendEquiv S R₂).symm (E.symm z, w')) :=
        Finset.sum_congr rfl fun z _ =>
          Equiv.sum_comp E.symm
            (fun y' => M ((splitAppendEquiv R₁ S).symm (g, y'))
                ((splitAppendEquiv R₁ S).symm (g', E.symm z)) *
              N ((splitAppendEquiv S R₂).symm (y', w))
                ((splitAppendEquiv S R₂).symm (E.symm z, w')))
    _ = ∑ y : ∀ k, S k, ∑ y' : ∀ k, S k,
        M ((splitAppendEquiv R₁ S).symm (g, y'))
            ((splitAppendEquiv R₁ S).symm (g', y)) *
          N ((splitAppendEquiv S R₂).symm (y', w))
            ((splitAppendEquiv S R₂).symm (y, w')) :=
        Equiv.sum_comp E.symm
          (fun y => ∑ y' : ∀ k, S k,
            M ((splitAppendEquiv R₁ S).symm (g, y'))
                ((splitAppendEquiv R₁ S).symm (g', y)) *
              N ((splitAppendEquiv S R₂).symm (y', w))
                ((splitAppendEquiv S R₂).symm (y, w')))

/-! ## Complement enumeration of an injective wire injection -/

/-- An injective injection of `s` wires into `a` positions forces `s ≤ a`. -/
theorem inj_fin_le (ι : Fin s → Fin a) (hι : Function.Injective ι) : s ≤ a := by
  have h := Fintype.card_le_of_injective ι hι
  simpa using h

/-- Length arithmetic of the complement enumeration. -/
theorem conn_add_compl (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    s + (a - s) = a := by
  have := inj_fin_le ι hι
  omega

/-- The complement of the image of an injective wire injection. -/
def complFinset (ι : Fin s → Fin a) (_hι : Function.Injective ι) : Finset (Fin a) :=
  Finset.univ \ Finset.image ι Finset.univ

/-- The complement of `s` connected wires among `a` positions has `a - s`
elements. -/
theorem card_complFinset (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    (complFinset ι hι).card = a - s := by
  rw [complFinset, Finset.card_sdiff]
  simp [Finset.card_image_of_injective _ hι]

/-- The order-preserving enumeration of the complement wires. -/
def complEmb (ι : Fin s → Fin a) (hι : Function.Injective ι) : Fin (a - s) → Fin a := fun i =>
  Finset.orderEmbOfFin (complFinset ι hι) (card_complFinset ι hι) i

private theorem complEmb_injective (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    Function.Injective (complEmb ι hι) :=
  fun _ _ h => (Finset.orderEmbOfFin _ _).injective h

private theorem complEmb_mem (ι : Fin s → Fin a) (hι : Function.Injective ι)
    (i : Fin (a - s)) :
    complEmb ι hι i ∈ complFinset ι hι :=
  Finset.orderEmbOfFin_mem _ _ i

/-- Membership in the complement: a wire is a complement wire iff no connected
wire hits it. -/
theorem mem_complFinset {ι : Fin s → Fin a} (hι : Function.Injective ι) {j : Fin a} :
    j ∈ complFinset ι hι ↔ ∀ k, ι k ≠ j := by
  simp [complFinset, Finset.mem_sdiff]

/-- Connected and complement wires are disjoint. -/
theorem disjoint_conn_compl (ι : Fin s → Fin a) (hι : Function.Injective ι) (k : Fin s)
    (i : Fin (a - s)) : ι k ≠ complEmb ι hι i :=
  (mem_complFinset hι).mp (complEmb_mem ι hι i) k

/-- Every wire is either connected or complement. -/
theorem exists_conn_or_compl (ι : Fin s → Fin a) (hι : Function.Injective ι) (j : Fin a) :
    (∃ k, ι k = j) ∨ ∃ i, complEmb ι hι i = j := by
  rcases Classical.em (∃ k : Fin s, ι k = j) with h | h
  · exact Or.inl h
  · right
    have him : j ∉ Finset.image ι Finset.univ := by
      intro hm
      exact h (by simpa using hm)
    have hj : j ∈ complFinset ι hι := by
      simp [complFinset, Finset.mem_sdiff, him]
    have hmem : j ∈ Set.range ⇑((complFinset ι hι).orderEmbOfFin (card_complFinset ι hι)) := by
      rw [Finset.range_orderEmbOfFin]
      simpa using hj
    exact hmem

/-! ## The sort permutation: connected wires first -/

/-- The connected positions of the sort order. -/
def posConn (ι : Fin s → Fin a) (hι : Function.Injective ι) : Fin s → Fin a := fun k =>
  finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)

/-- The complement positions of the sort order. -/
def posCompl (ι : Fin s → Fin a) (hι : Function.Injective ι) : Fin (a - s) → Fin a := fun i =>
  finCongr (conn_add_compl ι hι) (Fin.natAdd s i)

private theorem assemble_injective (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    Function.Injective (Fin.addCases ι (complEmb ι hι)) := by
  intro x y h
  induction x using Fin.addCases with
  | left k =>
    induction y using Fin.addCases with
    | left k' =>
      simp only [Fin.addCases_left] at h
      exact congrArg (Fin.castAdd (a - s)) (hι h)
    | right i' =>
      simp only [Fin.addCases_left, Fin.addCases_right] at h
      exact absurd h (disjoint_conn_compl ι hι k i')
  | right i =>
    induction y using Fin.addCases with
    | left k' =>
      simp only [Fin.addCases_left, Fin.addCases_right] at h
      exact absurd h.symm (disjoint_conn_compl ι hι k' i)
    | right i' =>
      simp only [Fin.addCases_right] at h
      exact congrArg (Fin.natAdd s) (complEmb_injective ι hι h)

private theorem assemble_surjective (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    Function.Surjective (Fin.addCases ι (complEmb ι hι)) := by
  intro j
  rcases exists_conn_or_compl ι hι j with ⟨k, hk⟩ | ⟨i, hi⟩
  · refine ⟨Fin.castAdd (a - s) k, ?_⟩
    simp only [Fin.addCases_left]
    exact hk
  · refine ⟨Fin.natAdd s i, ?_⟩
    simp only [Fin.addCases_right]
    exact hi

/-- The connected-then-complement assembly `Fin.addCases ι (complEmb ι hι)` is
bijective. -/
theorem assemble_bijective (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    Function.Bijective (Fin.addCases ι (complEmb ι hι)) :=
  ⟨assemble_injective ι hι, assemble_surjective ι hι⟩

/-- The sort permutation of `Fin a` listing the connected wires first (in `ι`
order) and the complement wires last. -/
noncomputable def sortPerm (ι : Fin s → Fin a) (hι : Function.Injective ι) : Fin a ≃ Fin a :=
  (finCongr (conn_add_compl ι hι)).symm.trans
    (Equiv.ofBijective (Fin.addCases ι (complEmb ι hι)) (assemble_bijective ι hι))

/-- Computation rule: connected positions carry the connected wires. -/
theorem sortPerm_conn (ι : Fin s → Fin a) (hι : Function.Injective ι) (k : Fin s) :
    sortPerm ι hι (posConn ι hι k) = ι k := by
  simp only [sortPerm, Equiv.trans_apply, posConn]
  rw [Equiv.symm_apply_apply]
  show (Fin.addCases ι (complEmb ι hι) (Fin.castAdd (a - s) k) : Fin a) = ι k
  rw [Fin.addCases_left]

/-- Computation rule: complement positions carry the complement wires. -/
theorem sortPerm_compl (ι : Fin s → Fin a) (hι : Function.Injective ι) (i : Fin (a - s)) :
    sortPerm ι hι (posCompl ι hι i) = complEmb ι hι i := by
  simp only [sortPerm, Equiv.trans_apply, posCompl]
  rw [Equiv.symm_apply_apply]
  show (Fin.addCases ι (complEmb ι hι) (Fin.natAdd s i) : Fin a) = complEmb ι hι i
  rw [Fin.addCases_right]

/-! ## Packaging a sorted family as an append family -/

/-- Flipping the two blocks of an append family. -/
def appendFlipEquiv (R : Fin r₁ → Type u) (T : Fin t → Type u) :
    (∀ i, append R T i) ≃ (∀ i, append T R i) :=
  (splitAppendEquiv R T).trans
    ((Equiv.prodComm _ _).trans (splitAppendEquiv T R).symm)

/-- Reading a packaged point through `appendFlipEquiv`: the packaged pair
swaps its components. -/
theorem appendFlipEquiv_pack (R : Fin r₁ → Type u) (T : Fin t → Type u)
    (r : ∀ i, R i) (w : ∀ j, T j) :
    appendFlipEquiv R T ((splitAppendEquiv R T).symm (r, w)) =
      (splitAppendEquiv T R).symm (w, r) := by
  simp [appendFlipEquiv, Equiv.trans_apply]

/-- Reading a block-flipped packaged point back through
`(appendFlipEquiv R T).symm`. -/
theorem appendFlipEquiv_symm_pack (R : Fin r₁ → Type u) (T : Fin t → Type u)
    (w : ∀ j, T j) (r : ∀ i, R i) :
    (appendFlipEquiv R T).symm ((splitAppendEquiv T R).symm (w, r)) =
      (splitAppendEquiv R T).symm (r, w) := by
  simp [appendFlipEquiv]

/-- Unpacking the append family `append connFam complFam` into the sorted
(connected-first) permuted family, up to the canonical per-slot transports
along the sort computation rules; packaging a sorted family back is the
`.symm`, as used by the `WireMatch` transports. -/
def sortPackEquiv (W : Fin a → Type u) (ι : Fin s → Fin a) (hι : Function.Injective ι) :
    (∀ i, append (fun k => W (ι k)) (fun j => W (complEmb ι hι j)) i) ≃
      (∀ i, permute W (sortPerm ι hι) i) :=
  (splitAppendEquiv _ _).trans
    (((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr
      (Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm).trans
      ((splitEquiv (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm.trans
        (Equiv.piCongrLeft _ (finCongr (conn_add_compl ι hι)))))

/-! ## The swap relation -/

/-- The swap relation for the link product: contracting `M` and `N` along the
shared block `S` equals, up to flipping both factors blockwise, contracting
`N` and `M` in the opposite roles. The relation `M * N = E (N * M) E` holds
for arbitrary operators, entrywise
[Chiribella2009Networks, comblong-pub.tex:342-355],
[Chiribella2007Architecture, qcombs-2.tex:223-235]. -/
theorem linkProduct_swap (R₁ : Fin r₁ → Type u) (S : Fin s → Type u) (R₂ : Fin r₂ → Type u)
    [∀ k, Fintype (S k)] (M : CMatrix (∀ i, append R₁ S i)) (N : CMatrix (∀ i, append S R₂ i)) :
    linkProduct R₁ S R₂ M N =
      matReindex (appendFlipEquiv R₂ R₁)
        (linkProduct R₂ S R₁ (matReindex (appendFlipEquiv S R₂) N)
          (matReindex (appendFlipEquiv R₁ S) M)) := by
  ext p q
  rcases hp : splitAppendEquiv R₁ R₂ p with ⟨g, w⟩
  rcases hq : splitAppendEquiv R₁ R₂ q with ⟨g', w'⟩
  have hp2 : p = (splitAppendEquiv R₁ R₂).symm (g, w) :=
    ((Equiv.symm_apply_apply _ p).symm).trans (congrArg _ hp)
  have hq2 : q = (splitAppendEquiv R₁ R₂).symm (g', w') :=
    ((Equiv.symm_apply_apply _ q).symm).trans (congrArg _ hq)
  rw [hp2, hq2, linkProduct_apply]
  simp only [matReindex_apply, appendFlipEquiv_symm_pack, linkProduct_apply]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => mul_comm _ _

/-- Coherence square: permuting the first block and then flipping equals
flipping and then permuting the same block in its new second position. -/
theorem appendFlipEquiv_permute_left (R : Fin r₁ → Type u) (T : Fin t → Type u)
    (σ : Fin r₁ ≃ Fin r₁) :
    (permuteAppendLeftEquiv R T σ).trans (appendFlipEquiv (permute R σ) T) =
      (appendFlipEquiv R T).trans (permuteAppendRightEquiv T R σ) := by
  ext x
  simp [permuteAppendLeftEquiv, permuteAppendRightEquiv, appendFlipEquiv,
    Equiv.trans_apply]
  rcases (splitAppendEquiv R T) x with ⟨r, w⟩
  simp

/-- Coherence square: permuting the second block and then flipping equals
flipping and then permuting the same block in its new first position. -/
theorem appendFlipEquiv_permute_right (S : Fin s → Type u) (T : Fin t → Type u)
    (τ : Fin t ≃ Fin t) :
    (permuteAppendRightEquiv S T τ).trans (appendFlipEquiv S (permute T τ)) =
      (appendFlipEquiv S T).trans (permuteAppendLeftEquiv T S τ) := by
  ext x
  simp [permuteAppendRightEquiv, permuteAppendLeftEquiv, appendFlipEquiv,
    Equiv.trans_apply]
  rcases (splitAppendEquiv S T) x with ⟨z, w⟩
  simp

/-! ## The general matching layer -/

/-- A matching of two heterogeneous wire families along `s` shared wires: the
connected-wire injections on each side (injectivity is the no-double-connection
condition) and a per-wire basis identification, directed from the first family
to the second. -/
structure WireMatch {a b : ℕ} (W₁ : Fin a → Type u) (W₂ : Fin b → Type u) where
  /-- The number of connected wire pairs. -/
  s : ℕ
  /-- Which wires of the first family are connected. -/
  ι₁ : Fin s → Fin a
  /-- Which wires of the second family are connected. -/
  ι₂ : Fin s → Fin b
  /-- No wire of the first family is connected twice. -/
  hι₁ : Function.Injective ι₁
  /-- No wire of the second family is connected twice. -/
  hι₂ : Function.Injective ι₂
  /-- The basis identification of each connected pair, first to second family. -/
  e : ∀ k, W₁ (ι₁ k) ≃ W₂ (ι₂ k)

/-- The connected wire family of the first side. -/
abbrev WireMatch.connFam₁ {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    Fin m.s → Type u := fun k => W₁ (m.ι₁ k)

/-- The connected wire family of the second side. -/
abbrev WireMatch.connFam₂ {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    Fin m.s → Type u := fun k => W₂ (m.ι₂ k)

/-- The private (unconnected) wire family of the first side. -/
abbrev WireMatch.complFam₁ {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    Fin (a - m.s) → Type u := fun j => W₁ (complEmb m.ι₁ m.hι₁ j)

/-- The private (unconnected) wire family of the second side. -/
abbrev WireMatch.complFam₂ {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    Fin (b - m.s) → Type u := fun j => W₂ (complEmb m.ι₂ m.hι₂ j)

/-- Transport of the first factor from its native layout into the canonical
private-then-connected layout. -/
noncomputable def WireMatch.eM {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    (∀ i, W₁ i) ≃ (∀ i, append m.complFam₁ m.connFam₁ i) :=
  (permuteEquiv W₁ (sortPerm m.ι₁ m.hι₁)).trans
    ((sortPackEquiv W₁ m.ι₁ m.hι₁).symm.trans (appendFlipEquiv m.complFam₁ m.connFam₁).symm)

/-- Transport of the second factor from its native layout into the canonical
connected-then-private layout. -/
noncomputable def WireMatch.eN {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    (∀ i, W₂ i) ≃ (∀ i, append m.connFam₂ m.complFam₂ i) :=
  (permuteEquiv W₂ (sortPerm m.ι₂ m.hι₂)).trans (sortPackEquiv W₂ m.ι₂ m.hι₂).symm

/-- Transport relabeling the second factor's connected wires along `e⁻¹` into
the first family's connected types. -/
def WireMatch.eTransportEquiv {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    (∀ i, append m.connFam₂ m.complFam₂ i) ≃ (∀ i, append m.connFam₁ m.complFam₂ i) :=
  (splitAppendEquiv m.connFam₂ m.complFam₂).trans
    (((Equiv.piCongrRight fun k => (m.e k).symm).prodCongr (Equiv.refl _)).trans
      (splitAppendEquiv m.connFam₁ m.complFam₂).symm)

/-- The general link product over a wire matching: transport both factors into
the canonical layout and apply the core link product, per the general
definition [Chiribella2009Networks, comblong-pub.tex:315-327]. The transpose
acts on the first family's connected block before any `e`-transport, and the
`e`-identifications only relabel the second factor. -/
noncomputable def WireMatch.linkProduct {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) [∀ k, Fintype (m.connFam₁ k)] (M : CMatrix (∀ i, W₁ i))
    (N : CMatrix (∀ i, W₂ i)) :
    CMatrix (∀ i, append m.complFam₁ m.complFam₂ i) :=
  _root_.QIT.WireFam.linkProduct m.complFam₁ m.connFam₁ m.complFam₂
    (matReindex m.eM M)
    (matReindex (m.eN.trans m.eTransportEquiv) N)

/-- Definitional unfolding of `WireMatch.linkProduct` into the core link
product, for downstream consumers. -/
theorem WireMatch.linkProduct_eq_core {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) [∀ k, Fintype (m.connFam₁ k)]
    (M : CMatrix (∀ i, W₁ i)) (N : CMatrix (∀ i, W₂ i)) :
    m.linkProduct M N =
      _root_.QIT.WireFam.linkProduct m.complFam₁ m.connFam₁ m.complFam₂
        (matReindex m.eM M) (matReindex (m.eN.trans m.eTransportEquiv) N) := rfl

/-- Reading a first-factor configuration through the canonical transport. -/
noncomputable def WireMatch.read₁ {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) (P : (∀ j, m.complFam₁ j) × (∀ k, m.connFam₁ k)) : (∀ i, W₁ i) :=
  m.eM.symm ((splitAppendEquiv m.complFam₁ m.connFam₁).symm P)

/-- Relabeling a connected configuration from the first family's types to the
second family's along `e`. -/
def WireMatch.eRelabel {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂)
    (z : ∀ k, m.connFam₁ k) : (∀ k, m.connFam₂ k) :=
  fun k => m.e k (z k)

/-- Reading a second-factor configuration through the canonical transport. -/
noncomputable def WireMatch.read₂ {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) (z : ∀ k, m.connFam₁ k) (w : ∀ j, m.complFam₂ j) : (∀ i, W₂ i) :=
  m.eN.symm ((splitAppendEquiv m.connFam₂ m.complFam₂).symm (m.eRelabel z, w))

/-- Reading a packaged point back through `eTransportEquiv.symm`: the
connected block relabels along `e` and the private block is untouched. -/
theorem WireMatch.eTransportEquiv_symm_pack {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) (z : ∀ k, m.connFam₁ k) (w : ∀ j, m.complFam₂ j) :
    m.eTransportEquiv.symm
        ((splitAppendEquiv m.connFam₁ m.complFam₂).symm (z, w)) =
      (splitAppendEquiv m.connFam₂ m.complFam₂).symm (m.eRelabel z, w) := by
  have hz : (Equiv.piCongrRight fun k => (m.e k).symm) (m.eRelabel z) = z := by
    funext k
    simp only [WireMatch.eRelabel, Equiv.piCongrRight_apply, Pi.map_apply,
      Equiv.symm_apply_apply]
  have hf : m.eTransportEquiv
      ((splitAppendEquiv m.connFam₂ m.complFam₂).symm (m.eRelabel z, w)) =
      (splitAppendEquiv m.connFam₁ m.complFam₂).symm (z, w) := by
    simp only [WireMatch.eTransportEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.apply_symm_apply, Prod.map_apply]
    rw [hz]
  rw [← hf, Equiv.symm_apply_apply]

/-- Entrywise action of the general link product: the first factor is read with
its shared block transposed, the second through the basis identifications `e`. -/
theorem WireMatch.linkProduct_apply {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) [∀ k, Fintype (m.connFam₁ k)]
    (M : CMatrix (∀ i, W₁ i)) (N : CMatrix (∀ i, W₂ i))
    (g g' : ∀ j, m.complFam₁ j) (w w' : ∀ j, m.complFam₂ j) :
    m.linkProduct M N ((splitAppendEquiv m.complFam₁ m.complFam₂).symm (g, w))
        ((splitAppendEquiv m.complFam₁ m.complFam₂).symm (g', w')) =
      ∑ z : ∀ k, m.connFam₁ k, ∑ z' : ∀ k, m.connFam₁ k,
        M (m.read₁ (g, z')) (m.read₁ (g', z)) * N (m.read₂ z' w) (m.read₂ z w') := by
  rw [WireMatch.linkProduct, _root_.QIT.WireFam.linkProduct_apply]
  simp only [matReindex_apply, Equiv.symm_trans_apply,
    WireMatch.eTransportEquiv_symm_pack, WireMatch.read₁, WireMatch.read₂]

/-! ## Position readback of the canonical transports -/

/-- The connected-block readback function of `sortPackEquiv`: the inverse of
the pointwise sort-permutation cast, applied to the connected block. -/
private def sortPackConnRead (W : Fin a → Type u) (ι : Fin s → Fin a) (hι : Function.Injective ι)
    (g : ∀ k, W (ι k)) :
    ∀ i, permute W (sortPerm ι hι) (posConn ι hι i) :=
  (Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g

/-- The complement-block readback function of `sortPackEquiv`. -/
private def sortPackComplRead (W : Fin a → Type u) (ι : Fin s → Fin a) (hι : Function.Injective ι)
    (h : ∀ j, W (complEmb ι hι j)) :
    ∀ j, permute W (sortPerm ι hι) (posCompl ι hι j) :=
  (Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h

/-- Evaluation of the reassembly stage of `sortPackEquiv` at any position: the
`piCongrLeft` component reads the case-split tuple back at the packed index. -/
private theorem piCongrLeft_addCases_pack (W : Fin a → Type u) (ι : Fin s → Fin a)
    (hι : Function.Injective ι) (g : ∀ k, W (ι k)) (h : ∀ j, W (complEmb ι hι j))
    (q : Fin (s + (a - s))) :
    (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
      (Fin.addCases (sortPackConnRead W ι hι g) (sortPackComplRead W ι hι h))
      (finCongr (conn_add_compl ι hι) q) =
      Fin.addCases (sortPackConnRead W ι hι g) (sortPackComplRead W ι hι h) q := rfl

/-- Computation of `sortPackEquiv` on a packaged configuration at a connected
position, stated with the position in unfolded form: the value is the connected
block's entry read back through the sort-permutation cast. -/
private theorem sortPack_pack_posConn (W : Fin a → Type u) (ι : Fin s → Fin a)
    (hι : Function.Injective ι) (g : ∀ k, W (ι k)) (h : ∀ j, W (complEmb ι hι j))
    (k : Fin s) :
    sortPackEquiv W ι hι
        ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)) =
      cast (congrArg W (sortPerm_conn ι hι k)).symm (g k) := by
  have hev : ((Fin.addCases (sortPackConnRead W ι hι g) (sortPackComplRead W ι hι h)
        (Fin.castAdd (a - s) k) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)))) =
    (Equiv.cast (congrArg W (sortPerm_conn ι hι k))).symm (g k) :=
    Fin.addCases_left k
  have h3 : (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
      (Fin.addCases
        ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
        ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h))
      (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)) =
    ((Equiv.cast (congrArg W (sortPerm_conn ι hι k))).symm (g k) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k))) :=
    (piCongrLeft_addCases_pack W ι hι g h (Fin.castAdd (a - s) k)).trans hev
  have h1 : sortPackEquiv W ι hι
        ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)) =
      (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        ((splitEquiv
            (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i =>
              Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr
            (Equiv.piCongrRight fun j =>
              Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm) (g, h)))
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)) := by
    show (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        ((splitEquiv (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr (Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm)
            ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j)) ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))))))
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)) = _
    rw [Equiv.apply_symm_apply]
  have h2 : (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        ((splitEquiv
            (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i =>
              Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr
            (Equiv.piCongrRight fun j =>
              Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm) (g, h)))
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)) =
      (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        (Fin.addCases
          ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
          ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h))
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k)) := by
    have hA : ((splitEquiv (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr
            (Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm) (g, h))) =
        Fin.addCases ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
          ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h) :=
      splitEquiv_symm_apply (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))
        ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
        ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h)
    rw [hA]
  have h4 : ((Equiv.cast (congrArg W (sortPerm_conn ι hι k))).symm (g k) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k))) =
    (cast (congrArg W (sortPerm_conn ι hι k)).symm (g k) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.castAdd (a - s) k))) := rfl
  exact ((h1.trans h2).trans h3).trans h4

/-- `posConn`-indexed form of the connected-position computation rule. -/
private theorem sortPack_pack_posConn' (W : Fin a → Type u) (ι : Fin s → Fin a)
    (hι : Function.Injective ι) (g : ∀ k, W (ι k)) (h : ∀ j, W (complEmb ι hι j))
    (k : Fin s) :
    sortPackEquiv W ι hι
        ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))
        (posConn ι hι k) =
      cast (congrArg W (sortPerm_conn ι hι k)).symm (g k) :=
  sortPack_pack_posConn W ι hι g h k

/-- Computation of `sortPackEquiv` on a packaged configuration at a complement
position, in unfolded form. -/
private theorem sortPack_pack_posCompl (W : Fin a → Type u) (ι : Fin s → Fin a)
    (hι : Function.Injective ι) (g : ∀ k, W (ι k)) (h : ∀ j, W (complEmb ι hι j))
    (j : Fin (a - s)) :
    sortPackEquiv W ι hι
        ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)) =
      cast (congrArg W (sortPerm_compl ι hι j)).symm (h j) := by
  have hev : ((Fin.addCases (sortPackConnRead W ι hι g) (sortPackComplRead W ι hι h)
        (Fin.natAdd s j) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)))) =
    (Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm (h j) :=
    Fin.addCases_right j
  have h3 : (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
      (Fin.addCases
        ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
        ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h))
      (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)) =
    ((Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm (h j) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j))) :=
    (piCongrLeft_addCases_pack W ι hι g h (Fin.natAdd s j)).trans hev
  have h1 : sortPackEquiv W ι hι
        ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)) =
      (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        ((splitEquiv
            (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i =>
              Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr
            (Equiv.piCongrRight fun j =>
              Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm) (g, h)))
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)) := by
    show (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        ((splitEquiv (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr (Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm)
            ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j)) ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))))))
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)) = _
    rw [Equiv.apply_symm_apply]
  have h2 : (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        ((splitEquiv
            (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i =>
              Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr
            (Equiv.piCongrRight fun j =>
              Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm) (g, h)))
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)) =
      (Equiv.piCongrLeft (permute W (sortPerm ι hι)) (finCongr (conn_add_compl ι hι)))
        (Fin.addCases
          ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
          ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h))
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j)) := by
    have hA : ((splitEquiv (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))).symm
          (((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm.prodCongr
            (Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm) (g, h))) =
        Fin.addCases ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
          ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h) :=
      splitEquiv_symm_apply (fun p => permute W (sortPerm ι hι) (finCongr (conn_add_compl ι hι) p))
        ((Equiv.piCongrRight fun i => Equiv.cast (congrArg W (sortPerm_conn ι hι i))).symm g)
        ((Equiv.piCongrRight fun j => Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm h)
    rw [hA]
  have h4 : ((Equiv.cast (congrArg W (sortPerm_compl ι hι j))).symm (h j) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j))) =
    (cast (congrArg W (sortPerm_compl ι hι j)).symm (h j) :
      permute W (sortPerm ι hι)
        (finCongr (conn_add_compl ι hι) (Fin.natAdd s j))) := rfl
  exact ((h1.trans h2).trans h3).trans h4

/-- `posCompl`-indexed form of the complement-position computation rule. -/
private theorem sortPack_pack_posCompl' (W : Fin a → Type u) (ι : Fin s → Fin a)
    (hι : Function.Injective ι) (g : ∀ k, W (ι k)) (h : ∀ j, W (complEmb ι hι j))
    (j : Fin (a - s)) :
    sortPackEquiv W ι hι
        ((splitAppendEquiv (fun k => W (ι k)) (fun j => W (complEmb ι hι j))).symm (g, h))
        (posCompl ι hι j) =
      cast (congrArg W (sortPerm_compl ι hι j)).symm (h j) :=
  sortPack_pack_posCompl W ι hι g h j

/-- Cast cancellation: casting along an equation and back returns the original
value. -/
private theorem cast_cast_cancel {A B : Type u} (h : A = B) (x : B) :
    cast h (cast h.symm x) = x := by
  cases h
  rfl

/-- Transport along an index equation, restated with an explicit family cast:
the two transports differ only in motive shape, and cancel against each other
in composed form. -/
private theorem transport_eq_cast {b : ℕ} {X : Fin b → Type u} {x y : Fin b}
    (h : x = y) (v : X x) :
    h ▸ v = cast (congrArg X h) v := by
  cases h
  rfl

/-- Cancellation rule for inverse-permutation readback: if the packaged sort
value at the inverse image of a position is a cast entry along the
permutation's defining equation at that position, then reading the inverse
permutation equiv at the position returns the entry.  The index normalization
happens by substitution on variables, before any transport is load-bearing;
the two transports cancel because their proofs prove the same equation. -/
private theorem permuteEquiv_symm_cast_cancel {b : ℕ} {W₂ : Fin b → Type u}
    {σ : Fin b ≃ Fin b} {u : ∀ q, W₂ (σ q)} {i₀ y : Fin b}
    (hyp : σ.symm i₀ = y) (hpc : σ y = i₀) (v : W₂ i₀)
    (hSP : u y = cast (congrArg W₂ hpc).symm v) :
    (permuteEquiv W₂ σ).symm u i₀ = v := by
  subst hyp
  rw [permuteEquiv_symm_apply, hSP, transport_eq_cast]
  exact cast_cast_cancel (congrArg W₂ hpc) v

/-- Evaluation of the first-factor readback at a connected wire: the value is
the connected entry. -/
theorem WireMatch.read₁_conn {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) (g : ∀ j, m.complFam₁ j) (z : ∀ k, m.connFam₁ k)
    (k : Fin m.s) :
    m.read₁ (g, z) (m.ι₁ k) = z k := by
  have hpos : (sortPerm m.ι₁ m.hι₁).symm (m.ι₁ k) = posConn m.ι₁ m.hι₁ k :=
    ((sortPerm m.ι₁ m.hι₁).symm_apply_eq).mpr (sortPerm_conn m.ι₁ m.hι₁ k).symm
  show (permuteEquiv W₁ (sortPerm m.ι₁ m.hι₁)).symm
      (sortPackEquiv W₁ m.ι₁ m.hι₁
        (appendFlipEquiv m.complFam₁ m.connFam₁
          ((splitAppendEquiv m.complFam₁ m.connFam₁).symm (g, z)))) (m.ι₁ k) = _
  rw [appendFlipEquiv_pack m.complFam₁ m.connFam₁ g z]
  exact permuteEquiv_symm_cast_cancel hpos (sortPerm_conn m.ι₁ m.hι₁ k)
    (z k) (sortPack_pack_posConn' W₁ m.ι₁ m.hι₁ z g k)

/-- Evaluation of the first-factor readback at a private wire: the value is
the private entry. -/
theorem WireMatch.read₁_compl {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) (g : ∀ j, m.complFam₁ j) (z : ∀ k, m.connFam₁ k)
    (j : Fin (a - m.s)) :
    m.read₁ (g, z) (complEmb m.ι₁ m.hι₁ j) = g j := by
  have hpos : (sortPerm m.ι₁ m.hι₁).symm (complEmb m.ι₁ m.hι₁ j) =
      posCompl m.ι₁ m.hι₁ j :=
    ((sortPerm m.ι₁ m.hι₁).symm_apply_eq).mpr (sortPerm_compl m.ι₁ m.hι₁ j).symm
  show (permuteEquiv W₁ (sortPerm m.ι₁ m.hι₁)).symm
      (sortPackEquiv W₁ m.ι₁ m.hι₁
        (appendFlipEquiv m.complFam₁ m.connFam₁
          ((splitAppendEquiv m.complFam₁ m.connFam₁).symm (g, z))))
      (complEmb m.ι₁ m.hι₁ j) = _
  rw [appendFlipEquiv_pack m.complFam₁ m.connFam₁ g z]
  exact permuteEquiv_symm_cast_cancel hpos (sortPerm_compl m.ι₁ m.hι₁ j)
    (g j) (sortPack_pack_posCompl' W₁ m.ι₁ m.hι₁ z g j)

/-- Evaluation of the second-factor readback at a connected wire: the value is
the relabeled connected entry. -/
theorem WireMatch.read₂_conn {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) (z : ∀ k, m.connFam₁ k) (w : ∀ j, m.complFam₂ j)
    (k : Fin m.s) :
    m.read₂ z w (m.ι₂ k) = m.eRelabel z k := by
  have hpos : (sortPerm m.ι₂ m.hι₂).symm (m.ι₂ k) = posConn m.ι₂ m.hι₂ k :=
    ((sortPerm m.ι₂ m.hι₂).symm_apply_eq).mpr (sortPerm_conn m.ι₂ m.hι₂ k).symm
  show (permuteEquiv W₂ (sortPerm m.ι₂ m.hι₂)).symm
      (sortPackEquiv W₂ m.ι₂ m.hι₂
        ((splitAppendEquiv m.connFam₂ m.complFam₂).symm (m.eRelabel z, w))) (m.ι₂ k) = _
  exact permuteEquiv_symm_cast_cancel hpos (sortPerm_conn m.ι₂ m.hι₂ k)
    (m.eRelabel z k) (sortPack_pack_posConn' W₂ m.ι₂ m.hι₂ (m.eRelabel z) w k)

/-- Evaluation of the second-factor readback at a private wire: the value is
the private entry. -/
theorem WireMatch.read₂_compl {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) (z : ∀ k, m.connFam₁ k) (w : ∀ j, m.complFam₂ j)
    (j : Fin (b - m.s)) :
    m.read₂ z w (complEmb m.ι₂ m.hι₂ j) = w j := by
  have hpos : (sortPerm m.ι₂ m.hι₂).symm (complEmb m.ι₂ m.hι₂ j) =
      posCompl m.ι₂ m.hι₂ j :=
    ((sortPerm m.ι₂ m.hι₂).symm_apply_eq).mpr (sortPerm_compl m.ι₂ m.hι₂ j).symm
  show (permuteEquiv W₂ (sortPerm m.ι₂ m.hι₂)).symm
      (sortPackEquiv W₂ m.ι₂ m.hι₂
        ((splitAppendEquiv m.connFam₂ m.complFam₂).symm (m.eRelabel z, w)))
      (complEmb m.ι₂ m.hι₂ j) = _
  exact permuteEquiv_symm_cast_cancel hpos (sortPerm_compl m.ι₂ m.hι₂ j)
    (w j) (sortPack_pack_posCompl' W₂ m.ι₂ m.hι₂ (m.eRelabel z) w j)

/-- The reversed matching: the same connected wire pairs with the two sides
swapped and the basis identifications inverted. The injectivity hypotheses
swap sides accordingly, so the reversed no-double-connection condition is
exactly the original one on the other side.

The `@[reducible]` attribute is load-bearing: the reversed-transport
computation rules (`WireMatch.symm_eM`/`WireMatch.symm_eN`) and
`WireMatch.linkProduct_symm` rely on reducible projection unfolding
(`m.symm.ι₁ ≡ m.ι₂`, `m.symm.s ≡ m.s`) for `rw` type-correctness and for
`Fintype (m.symm.connFam₁ k)` instance synthesis; removing it breaks those
proofs. -/
@[reducible]
def WireMatch.symm {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    WireMatch W₂ W₁ where
  s := m.s
  ι₁ := m.ι₂
  ι₂ := m.ι₁
  hι₁ := m.hι₂
  hι₂ := m.hι₁
  e := fun k => (m.e k).symm

/-- Reversing a matching twice returns the original matching. -/
theorem WireMatch.symm_symm {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) : m.symm.symm = m := rfl

/-! ## The reversed matching and the matched swap -/

/-- Pointwise inverse of a componentwise equiv family. -/
theorem piCongrRight_symm {ι : Type*} {α β : ι → Type u} (F : ∀ i, α i ≃ β i) :
    (Equiv.piCongrRight F).symm = Equiv.piCongrRight (fun i => (F i).symm) :=
  Equiv.ext fun _z => funext fun _i => rfl

/-- The first-side transport of the reversed matching is the second-side
transport of the original matching followed by the block flip. -/
theorem WireMatch.symm_eM {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    m.symm.eM = m.eN.trans (appendFlipEquiv m.complFam₂ m.connFam₂).symm := by
  rw [WireMatch.eM, WireMatch.eN, ← Equiv.trans_assoc]

/-- The second-side transport of the reversed matching is the first-side
transport of the original matching followed by the block flip. -/
theorem WireMatch.symm_eN {W₁ : Fin a → Type u} {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    m.symm.eN = m.eM.trans (appendFlipEquiv m.complFam₁ m.connFam₁) := by
  rw [WireMatch.eN, WireMatch.eM, ← Equiv.trans_assoc, Equiv.trans_assoc,
    Equiv.symm_trans_self, Equiv.trans_refl]

/-- The reversed `e`-transport is the shared-block relabeling of the second
factor along `e`. -/
theorem WireMatch.eTransportEquiv_symm {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) :
    (m.eTransportEquiv).symm = relabelRight m.complFam₂ (Equiv.piCongrRight m.e) := by
  ext x
  simp [relabelRight, WireMatch.eTransportEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.symm_symm, piCongrRight_symm]

/-- Flipping, transporting through the reversed matching, and flipping back
relabels the connected block along `e`. -/
private theorem WireMatch.symm_eTransportEquiv_flip_flip {W₁ : Fin a → Type u}
    {W₂ : Fin b → Type u} (m : WireMatch W₁ W₂) :
    (appendFlipEquiv m.complFam₁ m.connFam₁).trans
        ((m.symm.eTransportEquiv).trans (appendFlipEquiv m.connFam₂ m.complFam₁)) =
      relabelLeft m.complFam₁ (Equiv.piCongrRight m.e) := by
  ext x
  simp [relabelLeft, appendFlipEquiv, WireMatch.eTransportEquiv, WireMatch.symm,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.symm_symm]
  rcases (splitAppendEquiv m.complFam₁ m.connFam₁) x with ⟨g, z⟩
  simp

/-- The matched swap: composing over the reversed matching is the block flip
of the original composition. Entrywise this is the swap relation
[Chiribella2009Networks, comblong-pub.tex:342-355] transported along the
matching and its reversal. -/
theorem WireMatch.linkProduct_symm {W₁ : Fin a → Type u} {W₂ : Fin b → Type u}
    (m : WireMatch W₁ W₂) [∀ k, Fintype (m.connFam₁ k)] [∀ k, Fintype (m.connFam₂ k)]
    (M : CMatrix (∀ i, W₁ i)) (N : CMatrix (∀ i, W₂ i)) :
    m.symm.linkProduct N M =
      matReindex (appendFlipEquiv m.complFam₁ m.complFam₂) (m.linkProduct M N) := by
  rw [WireMatch.linkProduct_eq_core, WireMatch.linkProduct_eq_core, linkProduct_swap,
    ← linkProduct_shared_relabel m.complFam₁ m.connFam₁ m.connFam₂ m.complFam₂
      (Equiv.piCongrRight m.e) (matReindex m.eM M) (matReindex (m.eN.trans m.eTransportEquiv) N)]
  refine congrArg (matReindex (appendFlipEquiv m.complFam₁ m.complFam₂)) ?_
  have hi1 : (m.symm.eN.trans m.symm.eTransportEquiv).trans
        (appendFlipEquiv m.connFam₂ m.complFam₁) =
      m.eM.trans (relabelLeft m.complFam₁ (Equiv.piCongrRight m.e)) := by
    rw [WireMatch.symm_eN, Equiv.trans_assoc, Equiv.trans_assoc,
      WireMatch.symm_eTransportEquiv_flip_flip]
  have hi2 : m.symm.eM.trans (appendFlipEquiv m.complFam₂ m.connFam₂) =
      (m.eN.trans m.eTransportEquiv).trans
        (relabelRight m.complFam₂ (Equiv.piCongrRight m.e)) := by
    rw [WireMatch.symm_eM, Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl,
      ← WireMatch.eTransportEquiv_symm, Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.trans_refl]
  have hF1 : matReindex (appendFlipEquiv m.connFam₂ m.complFam₁)
      (matReindex (m.symm.eN.trans m.symm.eTransportEquiv) M) =
      matReindex (relabelLeft m.complFam₁ (Equiv.piCongrRight m.e)) (matReindex m.eM M) := by
    rw [← matReindex_trans_apply, ← matReindex_trans_apply, hi1]
  have hF2 : matReindex (appendFlipEquiv m.complFam₂ m.connFam₂) (matReindex m.symm.eM N) =
      matReindex (relabelRight m.complFam₂ (Equiv.piCongrRight m.e))
        (matReindex (m.eN.trans m.eTransportEquiv) N) := by
    rw [← matReindex_trans_apply, ← matReindex_trans_apply, hi2]
  rw [hF1, hF2]

end WireFam

end QIT
