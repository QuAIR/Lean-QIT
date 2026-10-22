/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Tester.Boundary

/-!
# Arbitrary singleton boundary wires

Transport the canonical `PUnit` boundaries to arbitrary finite singleton
carriers. `Unique` supplies both nonemptiness and uniqueness: an empty carrier
is not a one-dimensional boundary. This is the explicit wire identification in
[Chiribella2009Networks, comblong-pub.tex:3431-3437]; scalar entries use the
Born convention [Chiribella2009Networks, comblong-pub.tex:3422-3427].
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder.Tester
open QIT.WireFam

/-- Insert an arbitrary initial boundary before the original outputs. -/
def boundaryInput {n : Nat} (A : Type u) (O : Fin n → Type u) : Fin (n+1) → Type u :=
  Fin.cons A O
/-- Insert an arbitrary final boundary after the original inputs. -/
def boundaryOutput {n : Nat} (B : Type u) (I : Fin n → Type u) : Fin (n+1) → Type u :=
  Fin.snoc I B

instance {n : Nat} (A : Type u) (O : Fin n → Type u) [Fintype A] [∀ j, Fintype (O j)] :
    ∀ j, Fintype (boundaryInput A O j) := by
  intro j; cases j using Fin.cases <;> simp [boundaryInput] <;> infer_instance
instance {n : Nat} (A : Type u) (O : Fin n → Type u) [DecidableEq A] [∀ j, DecidableEq (O j)] :
    ∀ j, DecidableEq (boundaryInput A O j) := by
  intro j; cases j using Fin.cases <;> simp [boundaryInput] <;> infer_instance
instance {n : Nat} (B : Type u) (I : Fin n → Type u) [Fintype B] [∀ j, Fintype (I j)] :
    ∀ j, Fintype (boundaryOutput B I j) := by
  intro j; cases j using Fin.lastCases <;> simp [boundaryOutput] <;> infer_instance
instance {n : Nat} (B : Type u) (I : Fin n → Type u) [DecidableEq B] [∀ j, DecidableEq (I j)] :
    ∀ j, DecidableEq (boundaryOutput B I j) := by
  intro j; cases j using Fin.lastCases <;> simp [boundaryOutput] <;> infer_instance
instance {n : Nat} (A : Type u) (O : Fin n → Type u) [Unique A] :
    Unique (boundaryInput A O 0) := by change Unique A; infer_instance
instance {n : Nat} (B : Type u) (I : Fin n → Type u) [Unique B] :
    Unique (boundaryOutput B I (Fin.last n)) := by simp [boundaryOutput]; infer_instance

/-- Initial singleton transport, identity on every original output wire. -/
def boundaryInputEquiv {n : Nat} (A : Type u) (O : Fin n → Type u) [Unique A]
    (j : Fin (n+1)) : paddedInput O j ≃ boundaryInput A O j := by
  cases j using Fin.cases
  · exact Equiv.ofUnique _ _
  · exact Equiv.refl _

/-- Final singleton transport, identity on every original input wire. -/
def boundaryOutputEquiv {n : Nat} (B : Type u) (I : Fin n → Type u) [Unique B]
    (j : Fin (n+1)) : paddedOutput I j ≃ boundaryOutput B I j := by
  cases j using Fin.lastCases
  · exact (Equiv.cast (by simp [paddedOutput])).trans
      ((Equiv.ofUnique PUnit.{u+1} B).trans (Equiv.cast (by simp [boundaryOutput])))
  · exact Equiv.cast (by simp [paddedOutput, boundaryOutput])

/-- The ordinary comb wire equivalence from canonical to arbitrary boundaries. -/
def boundarySpaceEquiv {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] : Comb.Space (paddedInput O) (paddedOutput I) ≃
      Comb.Space (boundaryInput A O) (boundaryOutput B I) :=
  Comb.spaceEquiv (boundaryInputEquiv A O) (boundaryOutputEquiv B I)

/-- Insert two arbitrary singleton boundaries by genuine wire equivalences. -/
def paddingWithEquiv {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] : Comb.Space I O ≃
      Comb.Space (boundaryInput A O) (boundaryOutput B I) :=
  (paddingEquiv I O).trans (boundarySpaceEquiv I O A B)

/-- Padding with arbitrary singleton boundaries. -/
def padWith {n : Nat} (I O : Fin n → Type u) (A B : Type u) [Unique A] [Unique B] :=
  matReindex (paddingWithEquiv I O A B)
/-- Remove arbitrary singleton boundaries. -/
def unpadWith {n : Nat} (I O : Fin n → Type u) (A B : Type u) [Unique A] [Unique B] :=
  matReindex (paddingWithEquiv I O A B).symm

@[simp] theorem unpadWith_padWith {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (T : CMatrix (Comb.Space I O)) :
    unpadWith I O A B (padWith I O A B T) = T := matReindex_symm_matReindex _ _
@[simp] theorem padWith_unpadWith {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (T : CMatrix (Comb.Space (boundaryInput A O) (boundaryOutput B I))) :
    padWith I O A B (unpadWith I O A B T) = T := matReindex_matReindex_symm _ _

/-- Explicit comparison with canonical padding. -/
theorem padWith_eq_reindex_pad {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (T : CMatrix (Comb.Space I O)) :
    padWith I O A B T = matReindex (boundarySpaceEquiv I O A B) (pad I O T) :=
  matReindex_trans_apply _ _ _

@[simp] theorem padWith_add {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (T U : CMatrix (Comb.Space I O)) :
    padWith I O A B (T+U) = padWith I O A B T + padWith I O A B U := matReindex_add _ _ _
@[simp] theorem padWith_smul {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (z : ℂ) (T : CMatrix (Comb.Space I O)) :
    padWith I O A B (z • T) = z • padWith I O A B T := rfl
@[simp] theorem padWith_sum {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] {ι : Type v} (s : Finset ι) (T : ι → CMatrix (Comb.Space I O)) :
    padWith I O A B (∑ a ∈ s, T a) = ∑ a ∈ s, padWith I O A B (T a) := by
  ext p q; simp [padWith, matReindex_apply, Matrix.sum_apply]
@[simp] theorem padWith_posSemidef_iff {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (T : CMatrix (Comb.Space I O)) :
    (padWith I O A B T).PosSemidef ↔ T.PosSemidef := matReindex_posSemidef_iff _ _
@[simp] theorem unpadWith_posSemidef_iff {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (T : CMatrix (Comb.Space (boundaryInput A O) (boundaryOutput B I))) :
    (unpadWith I O A B T).PosSemidef ↔ T.PosSemidef := matReindex_posSemidef_iff _ _

@[simp] theorem padWith_zero {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] : padWith I O A B 0 = 0 := rfl
@[simp] theorem unpadWith_zero {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] : unpadWith I O A B 0 = 0 := rfl
@[simp] theorem unpadWith_add {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (T U : CMatrix (Comb.Space (boundaryInput A O) (boundaryOutput B I))) :
    unpadWith I O A B (T+U) = unpadWith I O A B T + unpadWith I O A B U := matReindex_add _ _ _
@[simp] theorem unpadWith_smul {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (z : ℂ)
    (T : CMatrix (Comb.Space (boundaryInput A O) (boundaryOutput B I))) :
    unpadWith I O A B (z • T) = z • unpadWith I O A B T := rfl
@[simp] theorem unpadWith_sum {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] {ι : Type v} (s : Finset ι)
    (T : ι → CMatrix (Comb.Space (boundaryInput A O) (boundaryOutput B I))) :
    unpadWith I O A B (∑ a ∈ s, T a) = ∑ a ∈ s, unpadWith I O A B (T a) := by
  ext p q; simp [unpadWith, matReindex_apply, Matrix.sum_apply]

/-- Arbitrary singleton padding is a complex-linear equivalence. -/
def padWithLinearEquiv {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] : CMatrix (Comb.Space I O) ≃ₗ[ℂ]
      CMatrix (Comb.Space (boundaryInput A O) (boundaryOutput B I)) where
  toEquiv := padWith I O A B
  map_add' := padWith_add I O A B
  map_smul' := padWith_smul I O A B

/-- The original comb remains the inner comb with arbitrary boundary carriers. -/
def innerWithEquiv {n : Nat} (I O : Fin n → Type u) (A B : Type u) :
    Comb.Space I O ≃ Comb.Space (Comb.innerInput (boundaryOutput B I))
      (Comb.innerOutput (boundaryInput A O)) :=
  Comb.spaceEquiv (fun j => Equiv.cast (by simp [boundaryOutput]))
    (fun j => Equiv.cast (by simp [boundaryInput]))

/-- Transport an original input operator to the actual generic inner wires. -/
def innerPadWith {n : Nat} (I O : Fin n → Type u) (A B : Type u) :=
  matReindex (innerWithEquiv I O A B)

private theorem cast_cycle {α β γ : Type u} (h₁ : α = β) (h₂ : β = γ)
    (h₃ : γ = α) (x : α) : cast h₃ (cast h₂ (cast h₁ x)) = x := by
  cases h₁; cases h₂; rfl

/-- Dropping arbitrary scalar endpoints recovers the same inner configuration. -/
theorem paddingWithEquiv_symm_action {n : Nat} (I O : Fin n → Type u) (A B : Type u)
    [Unique A] [Unique B] (p : Comb.Space I O)
    (a : boundaryInput A O 0 × boundaryOutput B I (Fin.last n)) :
    (paddingWithEquiv I O A B).symm
      ((Comb.actionEquiv (boundaryInput A O) (boundaryOutput B I)).symm
        (innerWithEquiv I O A B p, a)) = p := by
  apply Prod.ext
  · funext j
    change (innerInputEquiv I j).symm ((boundaryOutputEquiv B I j.castSucc).symm
      ((Fin.snoc (innerWithEquiv I O A B p).1 a.2) j.castSucc)) = p.1 j
    simp only [Fin.snoc_castSucc]
    simp [boundaryOutputEquiv, innerWithEquiv, Comb.spaceEquiv,
      innerInputEquiv, boundaryOutput, paddedOutput]
    change cast _ (cast _ (cast _ (p.1 j))) = p.1 j
    exact cast_cycle _ _ _ _
  · funext j
    rfl

section Finite
variable {n : Nat} (I O : Fin n → Type u) (A B : Type u)
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [Fintype A] [DecidableEq A] [Unique A] [Fintype B] [DecidableEq B] [Unique B]

/-- Recursive normalization is independent of the chosen singleton carrier. -/
theorem normalized_padWith_iff (T : CMatrix (Comb.Space I O)) :
    Comb.Normalized (boundaryInput A O) (boundaryOutput B I) (padWith I O A B T) ↔
      Normalized I O T := by
  rw [padWith_eq_reindex_pad, boundarySpaceEquiv]
  rw [← Comb.Normalized.reindex_iff]
  exact normalized_pad_iff I O T

omit [Unique A] [Unique B] in
/-- The identified inner input retains its original recursive normalization. -/
theorem normalized_innerPadWith_iff (R : CMatrix (Comb.Space I O)) :
    Comb.Normalized (Comb.innerInput (boundaryOutput B I))
      (Comb.innerOutput (boundaryInput A O)) (innerPadWith I O A B R) ↔
        Comb.Normalized I O R :=
  (Comb.Normalized.reindex_iff _ _ R).symm

/-- Arbitrary singleton boundary action retains the original Born scalar. -/
theorem actionMap_padWith_apply (T R : CMatrix (Comb.Space I O))
    (a b : boundaryInput A O 0 × boundaryOutput B I (Fin.last n)) :
    Comb.actionMap (boundaryInput A O) (boundaryOutput B I) (padWith I O A B T)
      (innerPadWith I O A B R) a b = pairing T R := by
  change (∑ x, ∑ y, innerPadWith I O A B R x y *
    matReindex (Comb.actionEquiv (boundaryInput A O) (boundaryOutput B I))
      (padWith I O A B T) (x,a) (y,b)) = _
  rw [← (innerWithEquiv I O A B).sum_comp]
  simp_rw [← (innerWithEquiv I O A B).sum_comp]
  simp only [innerPadWith, padWith, matReindex_apply, Equiv.symm_apply_apply,
    paddingWithEquiv_symm_action]
  simp only [pairing, mul_comm]

/-- The link-product action has the same scalar entries on any singleton boundaries. -/
theorem linkAction_padWith_apply (T R : CMatrix (Comb.Space I O))
    (a b : boundaryInput A O 0 × boundaryOutput B I (Fin.last n)) :
    Comb.linkAction (boundaryInput A O) (boundaryOutput B I) (padWith I O A B T)
      (innerPadWith I O A B R) a b = pairing T R := by
  rw [← Comb.actionMap_eq_linkAction]
  exact actionMap_padWith_apply I O A B T R a b

/-- The boundary-output trace introduces no dimension factor for any singleton. -/
theorem actionTrace_padWith_apply (T R : CMatrix (Comb.Space I O))
    (a b : boundaryInput A O 0) :
    Comb.actionTrace (padWith I O A B T) (innerPadWith I O A B R) a b = pairing T R := by
  simp [Comb.actionTrace_apply, partialTraceB, actionMap_padWith_apply]

end Finite
end QIT.HigherOrder.Tester
