/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.Core.Map.QuantumOperation
public import QIT.Util.Wires

/-!
# Recursive normalization of finite quantum combs

Configurations are in input-block/output-block order: `I j` is source wire
`H_(2j)` and `O j` is `H_(2j+1)`. The last output is traced and the last
input is an identity factor. The internal empty prefix is the scalar one,
not a public zero-comb. This is the normalization condition in
[Chiribella2007Architecture, qcombs-2.tex:296-308] and
[Chiribella2009Networks, comblong-pub.tex:1504-1514].

`DeterministicComb` packages this positive, recursively normalized operator.
Its equivalence with the independently defined admissible-map semantics is
not definitional and is not asserted here.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder
namespace Comb

/-- Input-first configurations of heterogeneous, ordered input/output pairs. -/
abbrev Space {n : Nat} (I O : Fin n → Type u) := (∀ j, I j) × (∀ j, O j)

/-- Recursive output-trace constraints, including positivity at each prefix.
The equation is entrywise to expose the identity on the final input without
assuming any wire is inhabited. At the empty prefix the operator is one. -/
def Normalized : {n : Nat} → (I O : Fin n → Type u) →
    [∀ j, Fintype (I j)] → [∀ j, DecidableEq (I j)] →
    [∀ j, Fintype (O j)] → [∀ j, DecidableEq (O j)] → CMatrix (Space I O) → Prop
  | 0, _, _, _, _, _, _, J => J = 1
  | n + 1, I, O, _, _, _, _, J => J.PosSemidef ∧
      ∃ K : CMatrix (Space (fun j : Fin n => I j.castSucc) (fun j => O j.castSucc)),
        Normalized _ _ K ∧ ∀ (i i' : ∀ j, I j) (o o' : ∀ j : Fin n, O j.castSucc),
          (∑ z, J (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
            if i (Fin.last n) = i' (Fin.last n) then
              K ((fun j => i j.castSucc), o) ((fun j => i' j.castSucc), o') else 0

/-- The recursive scalar endpoint is exactly one. -/
theorem normalized_zero (I O : Fin 0 → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] (J : CMatrix (Space I O)) :
    Normalized I O J ↔ J = 1 := Iff.rfl

/-- Positive-length normalized operators are positive semidefinite. -/
theorem Normalized.posSemidef {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {J : CMatrix (Space I O)} (h : Normalized I O J) : J.PosSemidef := h.1

/-- For one tooth the recursion is exactly the ordinary channel Choi constraint. -/
theorem normalized_one_iff {I O : Fin 1 → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (J : CMatrix (Space I O)) :
    Normalized I O J ↔ J.PosSemidef ∧ partialTraceB J = 1 := by
  classical
  have hsum (i i' : ∀ j, I j) (o o' : ∀ j : Fin 0, O j.castSucc) :
      (∑ z, J (i, Fin.snoc o z) (i', Fin.snoc o' z)) = partialTraceB J i i' := by
    have ho : o = o' := Subsingleton.elim _ _
    subst o'
    let e : O (Fin.last 0) ≃ (∀ j, O j) :=
      { toFun := fun z => Fin.snoc o z
        invFun := fun f => f (Fin.last 0)
        left_inv := fun _ => Fin.snoc_last _ _
        right_inv := fun f => by
          have hf : o = Fin.init f := Subsingleton.elim _ _
          simpa only [hf] using Fin.snoc_init_self f }
    exact e.sum_comp (fun z => J (i, z) (i', z))
  have heq (i i' : ∀ j, I j) : i 0 = i' 0 ↔ i = i' := by
    constructor
    · intro h
      funext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      exact h
    · rintro rfl; rfl
  constructor
  · rintro ⟨hpos, K, hK, htrace⟩
    refine ⟨hpos, ?_⟩
    change K = 1 at hK
    subst K
    ext i i'
    simpa [hsum, Matrix.one_apply, heq, Subsingleton.elim (fun j : Fin 0 => i j.castSucc) (fun j => i' j.castSucc)] using
      htrace i i' (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
  · rintro ⟨hpos, htrace⟩
    refine ⟨hpos, 1, rfl, ?_⟩
    intro i i' o o'
    simp [hsum, htrace, Matrix.one_apply, heq, Subsingleton.elim o o',
      Subsingleton.elim (fun j : Fin 0 => i j.castSucc) (fun j => i' j.castSucc)]

/-- Probabilistic normalization is domination by a normalized deterministic
operator, including singular and zero operators; no inverse is used.
[Chiribella2009Networks, comblong-pub.tex:1425-1433]. -/
def IsProbabilistic {n : Nat} (I O : Fin (n + 1) → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] (J : CMatrix (Space I O)) : Prop :=
  J.PosSemidef ∧ ∃ K, Normalized I O K ∧ J ≤ K

/-- Every deterministic normalized operator is a probabilistic one. -/
theorem Normalized.isProbabilistic {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {J : CMatrix (Space I O)} (h : Normalized I O J) : IsProbabilistic I O J :=
  ⟨h.posSemidef, J, h, le_rfl⟩

end Comb

/-- A positive-length deterministic comb in recursive normalization form.
The public length is `Nat.succ n`; the scalar prefix is internal to
`Comb.Normalized`. Admissible-map characterization is a separate theorem. -/
structure DeterministicComb {n : Nat} (I O : Fin (n + 1) → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] where
  choi : CMatrix (Comb.Space I O)
  normalized : Comb.Normalized I O choi

/-- Positivity of the bundled comb, with no additional hypotheses. -/
theorem DeterministicComb.posSemidef {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] (R : DeterministicComb I O) :
    R.choi.PosSemidef := R.normalized.posSemidef

end QIT.HigherOrder
