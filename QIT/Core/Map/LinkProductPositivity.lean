/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Map.ChoiComposition

/-!
# Positivity closure of the link product

The link product of positive semidefinite factors over a shared wire family is
positive semidefinite
[Chiribella2009Networks, comblong-pub.tex:342-355].

The proof follows the source route of that theorem: each factor is read as the
Choi matrix of a linear map through the inverse Choi construction
(`MatrixMap.ofChoiMatrix`), the two maps are completely positive because their
Choi matrices are positive semidefinite
(`MatrixMap.ofChoiMatrix_isCompletelyPositive`; complete positivity *is* Choi
positive semidefiniteness in this library, `MatrixMap.IsCompletelyPositive`),
the composition of completely positive maps is completely positive
(`MatrixMap.isCompletelyPositive_comp`), and the family-form bridge
(`MatrixMap.choi_comp_eq_linkProduct`, the realization of
[Chiribella2009Networks, comblong-pub.tex:295-302]) identifies the link
product with the Choi matrix of the composition. Positivity transports across
the wire-package reindexings by `matReindex_posSemidef`.

## Main results

* `QIT.WireFam.linkProduct_posSemidef`: the link product of positive
  semidefinite factors is positive semidefinite.

## Tags

link product, positive semidefinite, complete positivity, Choi matrix
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

namespace WireFam

variable {m s r : ℕ}
variable {A : Fin m → Type u} {B : Fin s → Type u} {C : Fin r → Type u}
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ k, Fintype (B k)] [∀ k, DecidableEq (B k)]
variable [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]

/-- The link product of positive semidefinite factors is positive semidefinite
[Chiribella2009Networks, comblong-pub.tex:342-355], proved along the source
proof route of that theorem: the factors are read as Choi matrices of
completely positive maps, whose composition is completely positive, and the
family-form bridge `MatrixMap.choi_comp_eq_linkProduct` identifies the link
product with the Choi matrix of the composition. -/
theorem linkProduct_posSemidef {M : CMatrix (∀ i, append A B i)}
    {N : CMatrix (∀ i, append B C i)}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    (linkProduct A B C M N).PosSemidef := by
  have hcp : MatrixMap.IsCompletelyPositive
      ((MatrixMap.ofChoiMatrix (matReindex (splitAppendEquiv B C) N)).comp
        (MatrixMap.ofChoiMatrix (matReindex (splitAppendEquiv A B) M))) :=
    MatrixMap.isCompletelyPositive_comp _ _
      (MatrixMap.ofChoiMatrix_isCompletelyPositive (matReindex_posSemidef _ hN))
      (MatrixMap.ofChoiMatrix_isCompletelyPositive (matReindex_posSemidef _ hM))
  have hpsd : (MatrixMap.choi ((MatrixMap.ofChoiMatrix
        (matReindex (splitAppendEquiv B C) N)).comp
      (MatrixMap.ofChoiMatrix (matReindex (splitAppendEquiv A B) M)))).PosSemidef :=
    hcp
  have hlink : linkProduct A B C M N =
      matReindex (splitAppendEquiv A C).symm
        (MatrixMap.choi ((MatrixMap.ofChoiMatrix
          (matReindex (splitAppendEquiv B C) N)).comp
        (MatrixMap.ofChoiMatrix (matReindex (splitAppendEquiv A B) M)))) := by
    rw [MatrixMap.choi_comp_eq_linkProduct, MatrixMap.choi_ofChoiMatrix,
      MatrixMap.choi_ofChoiMatrix, matReindex_symm_matReindex,
      matReindex_symm_matReindex]
  rw [hlink]
  exact matReindex_posSemidef _ hpsd

end WireFam

end

end QIT
