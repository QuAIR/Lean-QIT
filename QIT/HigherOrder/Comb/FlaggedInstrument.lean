/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Instrument
public import QIT.HigherOrder.Comb.Realization

/-!
# A classical final output for a finite superinstrument

The positive branch operators form one block-diagonal Choi operator when the
last output carries an additional outcome register. Tracing that register
recovers the instrument total, so the same recursive normalization witness
realizes this flagged operator by a single isometric memory chain. This is
the construction in the proof (lines 1202-1216) of
[Chiribella2009Networks, comblong-pub.tex:1125-1133].
It uses no inverse, rank condition, or inhabited-wire assumption.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder.Comb
open QIT.WireFam

namespace Superinstrument

section PositiveFamily
variable {n : Nat} {I O : Fin (n + 1) → Type u} {ι : Type v}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι]

/-- A positive family with normalized sum is a superinstrument; domination
by that common total follows from positivity of the remaining branches.
These are exactly the hypotheses of
[Chiribella2009Networks, comblong-pub.tex:1125-1133]. -/
def ofPositiveFamily (R : ι → CMatrix (Space I O))
    (hR : ∀ i, (R i).PosSemidef) (hS : Normalized I O (∑ i, R i)) :
    Superinstrument I O ι where
  branch := R
  branch_isProbabilistic i := by
    classical
    refine ⟨hR i, ∑ j, R j, hS, ?_⟩
    rw [Matrix.le_iff]
    have hsum : (∑ j, R j) - R i = ∑ j ∈ Finset.univ.erase i, R j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      abel
    rw [hsum]
    exact Matrix.posSemidef_sum (Finset.univ.erase i) fun j _ => hR j
  total := ⟨∑ i, R i, hS⟩
  sum_branch_eq_total := rfl

/-- Constructing the instrument preserves every source branch exactly. -/
@[simp] theorem ofPositiveFamily_branch (R : ι → CMatrix (Space I O))
    (hR : ∀ i, (R i).PosSemidef) (hS : Normalized I O (∑ i, R i)) (i : ι) :
    (ofPositiveFamily R hR hS).branch i = R i := rfl

/-- The instrument total is the given sum, without a different completion. -/
@[simp] theorem ofPositiveFamily_total_choi (R : ι → CMatrix (Space I O))
    (hR : ∀ i, (R i).PosSemidef) (hS : Normalized I O (∑ i, R i)) :
    (ofPositiveFamily R hR hS).total.choi = ∑ i, R i := rfl

end PositiveFamily

variable {n : Nat} (I O : Fin (n + 1) → Type u) (ι : Type u)

/-- Separate the outcome register from the original input-first Choi coordinates. -/
def flaggedSpaceEquiv : Space I (boundaryOutput O ι) ≃ Space I O × ι :=
  (Equiv.prodCongr (Equiv.refl _) (boundaryOutputEquiv O ι)).trans
    (Equiv.prodAssoc _ _ _).symm

variable {I O ι}
variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι] [DecidableEq ι]

/-- The final classical flag labels the original branch Choi operators. -/
def flaggedChoi (M : Superinstrument I O ι) :
    CMatrix (Space I (boundaryOutput O ι)) :=
  matReindex (flaggedSpaceEquiv I O ι).symm (Matrix.blockDiagonal M.branch)

/-- Every matrix entry of the flagged operator is an exact branch entry or zero. -/
theorem flaggedChoi_apply (M : Superinstrument I O ι)
    (p q : Space I (boundaryOutput O ι)) :
    M.flaggedChoi p q =
      if (flaggedSpaceEquiv I O ι p).2 = (flaggedSpaceEquiv I O ι q).2 then
        M.branch (flaggedSpaceEquiv I O ι p).2
          (flaggedSpaceEquiv I O ι p).1 (flaggedSpaceEquiv I O ι q).1 else 0 := by
  simp [flaggedChoi, matReindex_apply, Matrix.blockDiagonal_apply]

/-- In the original wire coordinates, equal flags recover the original branch exactly. -/
theorem flaggedChoi_lift_apply (M : Superinstrument I O ι)
    (x y : ∀ j, I j) (o p : ∀ j, O j) (i j : ι) :
    M.flaggedChoi (x, boundaryOutputLift O o i)
      (y, boundaryOutputLift O p j) =
        if i = j then M.branch i (x, o) (y, p) else 0 := by
  rw [flaggedChoi_apply]
  simp [flaggedSpaceEquiv, boundaryOutputEquiv_lift]

/-- A finite family of positive branches gives a positive flagged operator,
including singular branches and empty finite carriers. -/
theorem flaggedChoi_posSemidef (M : Superinstrument I O ι) :
    M.flaggedChoi.PosSemidef := by
  apply (matReindex_posSemidef_iff _ _).mpr
  let B := Matrix.blockDiagonal (fun i => psdSqrt (M.branch i))
  have h : B * B.conjTranspose = Matrix.blockDiagonal M.branch := by
    dsimp [B]
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext i
    rw [(psdSqrt_isHermitian (M.branch i)).eq,
      psdSqrt_mul_self_of_posSemidef (M.branch_posSemidef i)]
  rw [← h]
  exact Matrix.posSemidef_self_mul_conjTranspose B

private def flaggedPrefixEquiv (O : Fin (n + 1) → Type u) (ι : Type u) (j : Fin n) :
    O j.castSucc ≃ boundaryOutput O ι j.castSucc :=
  (Equiv.cast (by simp [boundaryOutput])).symm

private def flaggedLastEquiv (O : Fin (n + 1) → Type u) (ι : Type u) :
    boundaryOutput O ι (Fin.last n) ≃ O (Fin.last n) × ι :=
  Equiv.cast (by simp [boundaryOutput])

private theorem flagged_snoc_lift (O : Fin (n + 1) → Type u) (ι : Type u)
    (o : ∀ j : Fin n, boundaryOutput O ι j.castSucc) (z : O (Fin.last n)) (i : ι) :
    Fin.snoc o ((flaggedLastEquiv O ι).symm (z, i)) =
      boundaryOutputLift O
        (Fin.snoc (fun j => (flaggedPrefixEquiv O ι j).symm (o j)) z) i := by
  funext j
  cases j using Fin.lastCases with
  | last => simp [boundaryOutputLift, flaggedLastEquiv]
  | cast j =>
    simp only [boundaryOutputLift, Fin.snoc_castSucc, flaggedPrefixEquiv, Equiv.symm_symm]
    exact ((Equiv.cast _).symm_apply_apply (o j)).symm

/-- The flagged operator satisfies the full original recursion: tracing the
last output and the outcome register recovers the same normalized prefix. -/
theorem flaggedChoi_normalized (M : Superinstrument I O ι) :
    Normalized I (boundaryOutput O ι) M.flaggedChoi := by
  obtain ⟨_, K, hK, ht⟩ := M.sum_branch_normalized
  let eI := fun j : Fin n => Equiv.refl (I j.castSucc)
  let eO := flaggedPrefixEquiv O ι
  refine ⟨M.flaggedChoi_posSemidef, matReindex (spaceEquiv eI eO) K,
    (Normalized.reindex_iff eI eO K).mp hK, ?_⟩
  intro x y o p
  let o₀ := fun j => (eO j).symm (o j)
  let p₀ := fun j => (eO j).symm (p j)
  have hsum :
      (∑ z, M.flaggedChoi (x, Fin.snoc o z) (y, Fin.snoc p z)) =
      ∑ z : O (Fin.last n), (∑ i, M.branch i) (x, Fin.snoc o₀ z) (y, Fin.snoc p₀ z) := by
    rw [← (flaggedLastEquiv O ι).symm.sum_comp]
    simp_rw [Fintype.sum_prod_type, flagged_snoc_lift, flaggedChoi_lift_apply, ite_true]
    simp only [Matrix.sum_apply]
    rfl
  rw [hsum, ht]
  congr 1

/-- One fixed causal chain realizes the entire flagged family before any
input operation or outcome is chosen. -/
theorem exists_flagged_memoryChain (M : Superinstrument I O ι) :
    ∃ (d : Fin (n + 1) → Nat)
      (c : MemoryChain I (boundaryOutput O ι) (fun j => Memory.{u} (d j))),
      MatrixMap.choi c.chainMap = M.flaggedChoi :=
  (normalized_iff_exists_memoryChain _).mp M.flaggedChoi_normalized

end Superinstrument
end QIT.HigherOrder.Comb
