/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.CompleteAdmissibility
public import QIT.Channels.Diamond

/-!
# Pre- and post-processing circuits with independent spectators

A memory wire passes from the preprocessing map to the postprocessing map
beside the inserted operation. The active wire precedes the memory in both maps:
`P : c → a × B` and `Q : b × B → d`. This is the channel form of the
isometric circuit in [Chiribella2008Supermaps, VersioneArchivio.tex:340-349].

The ancillary circuit is an actual composition of tensor-product maps and
basis permutations. The input spectator bypasses preprocessing, and the
output spectator bypasses postprocessing. Its Choi blocks agree with those
of the ordinary circuit on every linear inserted operation. Consequently,
an ordinary realization identity extends to the existing `ancillaryAction`
without assuming product inputs, positivity, normalization, or inhabited
systems. The physical wires, memory, and two spectators have independent
universe parameters.
-/

@[expose] public section

namespace QIT.HigherOrder

universe u v w x y z t

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x} {B : Type t}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
  [Fintype B] [DecidableEq B]
variable {r : Type y} {s : Type z}
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Insert a linear operation between preprocessing and postprocessing while
carrying the memory unchanged. This is the channel form of the circuit in
[Chiribella2008Supermaps, VersioneArchivio.tex:340-349]. -/
def prePostAction (P : MatrixMap c (a × B)) (Q : MatrixMap (b × B) d)
    (Φ : MatrixMap a b) : MatrixMap c d :=
  Q.comp ((MatrixMap.kron Φ LinearMap.id).comp P)

/-- The physical circuit applies preprocessing, the inserted operation beside
identity on the memory, and postprocessing, in that order. -/
theorem prePostAction_apply (P : MatrixMap c (a × B)) (Q : MatrixMap (b × B) d)
    (Φ : MatrixMap a b) (X : CMatrix c) :
    prePostAction P Q Φ X = Q (MatrixMap.kron Φ LinearMap.id (P X)) := rfl

/-- Exchange the memory and spectator positions while leaving the active wire
first: `((x, m), ρ) ↦ ((x, ρ), m)`. -/
def prePostShuffle (a : Type u) (B : Type t) (r : Type y) :
    ((a × B) × r) ≃ ((a × r) × B) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The matrix map of a basis permutation used to route the circuit wires. -/
def prePostReindex {A : Type u} {C : Type v}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (e : A ≃ C) : MatrixMap A C :=
  (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap

/-- Routing a wire reads the input matrix in the inverse basis coordinates. -/
@[simp] theorem prePostReindex_apply {A : Type u} {C : Type v}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (e : A ≃ C) (X : CMatrix A) :
    prePostReindex e X = X.submatrix e.symm e.symm := rfl

/-- The circuit's algebraic reindexing is exactly the ordinary permutation
channel, so the routing itself is completely positive and trace preserving. -/
theorem prePostReindex_eq_channelReindex {A : Type u} {C : Type v}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (e : A ≃ C) : prePostReindex e = (Channel.reindex e).map := by
  ext X i j
  symm
  change ((Channel.reindex e).map X) i j = X (e.symm i) (e.symm j)
  simp [Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · change (∑ k : A, (if i = e k then 1 else 0) * X k (e.symm j)) *
        star (if j = e (e.symm j) then 1 else 0) =
      X (e.symm i) (e.symm j)
    rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro x _ hx
      have hne : i ≠ e x := by
        intro hi
        apply hx
        simp [hi]
      simp [hne]
    · simp
  · intro x _ hx
    have hne : j ≠ e x := by
      intro hj
      apply hx
      simp [hj]
    simp only [mul_eq_zero]
    right
    show star (if j = e x then 1 else 0) = 0
    simp [hne]
  · simp

/-- The physical circuit on an arbitrary joint operation. The first shuffle
routes the input spectator into the inserted operation; the second routes its
output spectator past postprocessing. The memory is untouched in between. -/
def prePostAncillaryAction (P : MatrixMap c (a × B)) (Q : MatrixMap (b × B) d)
    (Φ : MatrixMap (a × r) (b × s)) : MatrixMap (c × r) (d × s) :=
  (MatrixMap.kron Q LinearMap.id).comp
    ((prePostReindex (prePostShuffle b B s).symm).comp
      ((MatrixMap.kron Φ LinearMap.id).comp
        ((prePostReindex (prePostShuffle a B r)).comp
          (MatrixMap.kron P LinearMap.id))))

set_option backward.isDefEq.respectTransparency false in
private theorem kron_id_apply_slice {A : Type u} {C : Type v} {R : Type w}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype R] [DecidableEq R]
    (Ψ : MatrixMap A C) (X : CMatrix (A × R)) (i j : C) (ρ ρ' : R) :
    MatrixMap.kron Ψ LinearMap.id X (i, ρ) (j, ρ') =
      Ψ (fun a a' => X (a, ρ) (a', ρ')) i j := by
  rw [MatrixMap.kron_id_apply, MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- Matrix-unit expansion of the ordinary circuit. This follows from
`MatrixMap.map_eq_sum_single` and the identity-factor tensor action. -/
theorem choi_prePostAction_apply
    (P : MatrixMap c (a × B)) (Q : MatrixMap (b × B) d) (Φ : MatrixMap a b)
    (i i' : c) (j j' : d) :
    MatrixMap.choi (prePostAction P Q Φ) (i, j) (i', j') =
      ∑ z : b × B, ∑ z' : b × B,
        (∑ x : a, ∑ x' : a,
          P (Matrix.single i i' 1) (x, z.2) (x', z'.2) *
            Φ (Matrix.single x x' 1) z.1 z'.1) *
          Q (Matrix.single z z' 1) j j' := by
  change Q (MatrixMap.kron Φ LinearMap.id (P (Matrix.single i i' 1))) j j' = _
  rw [MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro z' _
  rcases z with ⟨j₀, m⟩
  rcases z' with ⟨j₁, m'⟩
  rw [MatrixMap.kron_id_apply]

private theorem ancillaryBlock_map_apply
    (Φ : MatrixMap (a × r) (b × s)) (X : CMatrix a)
    (ρ ρ' : r) (σ σ' : s) (j j' : b) :
    Φ (Matrix.kronecker X (Matrix.single ρ ρ' 1)) (j, σ) (j', σ') =
      MatrixMap.ofChoiMatrix
        (ancillaryBlock (MatrixMap.choi Φ) (ρ, σ) (ρ', σ')) X j j' := by
  rw [MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, MatrixMap.ofChoiMatrix_apply, ancillaryBlock, MatrixMap.choi]
  simp [Matrix.single, mul_ite, ite_mul, ite_and]

/-- Every spectator Choi block of the physical circuit is the ordinary
circuit on the corresponding block operation. Both off-diagonal spectator
indices are retained, and no positivity assumption is used. -/
theorem ancillaryBlock_choi_prePostAncillaryAction
    (P : MatrixMap c (a × B)) (Q : MatrixMap (b × B) d)
    (Φ : MatrixMap (a × r) (b × s)) (p q : r × s) :
    ancillaryBlock (MatrixMap.choi (prePostAncillaryAction P Q Φ)) p q =
      MatrixMap.choi (prePostAction P Q
        (MatrixMap.ofChoiMatrix (ancillaryBlock (MatrixMap.choi Φ) p q))) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  rcases p with ⟨ρ, σ⟩
  rcases q with ⟨ρ', σ'⟩
  change (MatrixMap.kron Q LinearMap.id
    (prePostReindex (prePostShuffle b B s).symm
      (MatrixMap.kron Φ LinearMap.id
        (prePostReindex (prePostShuffle a B r)
          (MatrixMap.kron P LinearMap.id (Matrix.single (i, ρ) (i', ρ') 1))))))
      (j, σ) (j', σ') =
    Q (MatrixMap.kron
      (MatrixMap.ofChoiMatrix (ancillaryBlock (MatrixMap.choi Φ) (ρ, σ) (ρ', σ')))
      LinearMap.id (P (Matrix.single i i' 1))) j j'
  rw [kron_id_apply_slice]
  apply congrArg (fun X => Q X j j')
  ext z z'
  change MatrixMap.kron Φ LinearMap.id
      (prePostReindex (prePostShuffle a B r)
        (MatrixMap.kron P LinearMap.id (Matrix.single (i, ρ) (i', ρ') 1)))
      ((z.1, σ), z.2) ((z'.1, σ'), z'.2) = _
  rw [kron_id_apply_slice, kron_id_apply_slice,
    single_prod_eq_kronecker_single, MatrixMap.kron_apply_kronecker]
  change Φ (Matrix.kronecker
      (fun a a' => P (Matrix.single i i' 1) (a, z.2) (a', z'.2))
      (Matrix.single ρ ρ' 1)) (z.1, σ) (z'.1, σ') = _
  exact ancillaryBlock_map_apply Φ _ ρ ρ' σ σ' z.1 z'.1

/-- An ordinary pre/post realization determines the same physical circuit on
every joint linear operation with independent ancillary input and output
systems. This is the blockwise extension of `ancillaryAction`. -/
theorem ancillaryAction_eq_prePostAncillaryAction
    (S : MatrixMap (a × b) (c × d))
    (P : MatrixMap c (a × B)) (Q : MatrixMap (b × B) d)
    (h : ∀ Ψ : MatrixMap a b, action S Ψ = prePostAction P Q Ψ)
    (Φ : MatrixMap (a × r) (b × s)) :
    ancillaryAction S Φ = prePostAncillaryAction P Q Φ := by
  apply MatrixMap.choi_inj
  rw [choi_ancillaryAction]
  ext x y
  have hb := ancillaryBlock_choi_prePostAncillaryAction P Q Φ
    (x.1.2, x.2.2) (y.1.2, y.2.2)
  rw [← h, action, MatrixMap.choi_ofChoiMatrix,
    MatrixMap.choi_ofChoiMatrix] at hb
  exact (congrFun (congrFun hb (x.1.1, x.2.1)) (y.1.1, y.2.1)).symm

end
end QIT.HigherOrder
