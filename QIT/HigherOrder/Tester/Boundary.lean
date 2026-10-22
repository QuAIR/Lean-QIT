/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Tester
public import QIT.HigherOrder.Comb.Characterization

/-!
# Singleton boundary transport for testers

The added wires identify the source tester with an ordinary comb, without a
transpose or dimension factor. The scalar action is the full-transpose Born
pairing [Chiribella2009Networks, comblong-pub.tex:3422-3427], as used in the
instrument equivalence [Chiribella2009Networks, comblong-pub.tex:3431-3437].
Recursive normalization follows the trace constraints
[Chiribella2009Networks, comblong-pub.tex:1504-1514].
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v
namespace QIT.HigherOrder.Tester
open QIT.WireFam

/-- Add the initial scalar input before the original outputs. -/
def paddedInput {n : Nat} (O : Fin n → Type u) : Fin (n+1) → Type u :=
  Fin.cons PUnit.{u+1} O
/-- Add the final scalar output after the original inputs. -/
def paddedOutput {n : Nat} (I : Fin n → Type u) : Fin (n+1) → Type u :=
  Fin.snoc I PUnit.{u+1}

instance {n : Nat} (O : Fin n → Type u) [∀ j, Fintype (O j)] :
    ∀ j, Fintype (paddedInput O j) := by
  intro j; cases j using Fin.cases <;> simp [paddedInput] <;> infer_instance
instance {n : Nat} (O : Fin n → Type u) [∀ j, DecidableEq (O j)] :
    ∀ j, DecidableEq (paddedInput O j) := by
  intro j; cases j using Fin.cases <;> simp [paddedInput] <;> infer_instance
instance {n : Nat} (I : Fin n → Type u) [∀ j, Fintype (I j)] :
    ∀ j, Fintype (paddedOutput I j) := by
  intro j; cases j using Fin.lastCases <;> simp [paddedOutput] <;> infer_instance
instance {n : Nat} (I : Fin n → Type u) [∀ j, DecidableEq (I j)] :
    ∀ j, DecidableEq (paddedOutput I j) := by
  intro j; cases j using Fin.lastCases <;> simp [paddedOutput] <;> infer_instance

instance {n : Nat} (O : Fin n → Type u) : Unique (paddedInput O 0) := by
  change Unique PUnit; infer_instance
instance {n : Nat} (I : Fin n → Type u) : Unique (paddedOutput I (Fin.last n)) := by
  simp [paddedOutput]; infer_instance

/-- The original input wires are precisely the inner inputs. -/
def innerInputEquiv {n : Nat} (I : Fin n → Type u) (j : Fin n) :
    I j ≃ Comb.innerInput (paddedOutput I) j := Equiv.cast (by simp [paddedOutput])
/-- The original output wires are precisely the inner outputs. -/
def innerOutputEquiv {n : Nat} (O : Fin n → Type u) (j : Fin n) :
    O j ≃ Comb.innerOutput (paddedInput O) j := Equiv.cast (by simp [paddedInput])

/-- The actual inner configuration equivalence preserves the original I/O order. -/
def innerEquiv {n : Nat} (I O : Fin n → Type u) : Comb.Space I O ≃
    Comb.Space (Comb.innerInput (paddedOutput I)) (Comb.innerOutput (paddedInput O)) :=
  Comb.spaceEquiv (innerInputEquiv I) (innerOutputEquiv O)

/-- Input-first configurations with the two scalar boundaries inserted. -/
def paddingEquiv {n : Nat} (I O : Fin n → Type u) :
    Comb.Space I O ≃ Comb.Space (paddedInput O) (paddedOutput I) :=
  { toFun := fun p => (Comb.actionEquiv (paddedInput O) (paddedOutput I)).symm
      (innerEquiv I O p, (default, default))
    invFun := fun p => (innerEquiv I O).symm
      ((Comb.actionEquiv (paddedInput O) (paddedOutput I)) p).1
    left_inv := by intro p; simp
    right_inv := by
      intro p
      apply (Comb.actionEquiv (paddedInput O) (paddedOutput I)).injective
      simp only [Equiv.apply_symm_apply]
      exact Prod.ext rfl (Subsingleton.elim _ _) }

/-- Explicit insertion formula: original outputs follow the initial unit,
and original inputs precede the final unit. The casts identify inner wires. -/
@[simp] theorem paddingEquiv_apply {n : Nat} (I O : Fin n → Type u) (p : Comb.Space I O) :
    paddingEquiv I O p = (Fin.cons PUnit.unit p.2,
      Fin.snoc ((Equiv.piCongrRight (innerInputEquiv I)) p.1) default) := rfl

/-- Transport the operator by the explicit wire equivalence. -/
def pad {n : Nat} (I O : Fin n → Type u) := matReindex (paddingEquiv I O)
/-- Remove the two scalar boundary wires. -/
def unpad {n : Nat} (I O : Fin n → Type u) := matReindex (paddingEquiv I O).symm
/-- Transport an input comb to the identified padded inner wires. -/
def innerPad {n : Nat} (I O : Fin n → Type u) := matReindex (innerEquiv I O)
/-- Recover an input comb from the padded inner wires. -/
def innerUnpad {n : Nat} (I O : Fin n → Type u) := matReindex (innerEquiv I O).symm

@[simp] theorem unpad_pad {n : Nat} (I O : Fin n → Type u) (T : CMatrix (Comb.Space I O)) :
    unpad I O (pad I O T) = T := matReindex_symm_matReindex _ _
@[simp] theorem pad_unpad {n : Nat} (I O : Fin n → Type u)
    (T : CMatrix (Comb.Space (paddedInput O) (paddedOutput I))) :
    pad I O (unpad I O T) = T := matReindex_matReindex_symm _ _
@[simp] theorem innerUnpad_innerPad {n : Nat} (I O : Fin n → Type u)
    (R : CMatrix (Comb.Space I O)) : innerUnpad I O (innerPad I O R) = R :=
  matReindex_symm_matReindex _ _
@[simp] theorem innerPad_innerUnpad {n : Nat} (I O : Fin n → Type u)
    (R : CMatrix (Comb.Space (Comb.innerInput (paddedOutput I))
      (Comb.innerOutput (paddedInput O)))) : innerPad I O (innerUnpad I O R) = R :=
  matReindex_matReindex_symm _ _

@[simp] theorem pad_add {n : Nat} (I O : Fin n → Type u) (A B : CMatrix (Comb.Space I O)) :
    pad I O (A+B) = pad I O A + pad I O B := matReindex_add _ _ _
@[simp] theorem pad_smul {n : Nat} (I O : Fin n → Type u) (z : ℂ)
    (A : CMatrix (Comb.Space I O)) : pad I O (z • A) = z • pad I O A := rfl
@[simp] theorem pad_sum {n : Nat} (I O : Fin n → Type u) {ι : Type v}
    (s : Finset ι) (A : ι → CMatrix (Comb.Space I O)) :
    pad I O (∑ a ∈ s, A a) = ∑ a ∈ s, pad I O (A a) := by
  ext p q; simp [pad, matReindex_apply, Matrix.sum_apply]

@[simp] theorem pad_zero {n : Nat} (I O : Fin n → Type u) : pad I O 0 = 0 := rfl
@[simp] theorem unpad_zero {n : Nat} (I O : Fin n → Type u) : unpad I O 0 = 0 := rfl
@[simp] theorem unpad_add {n : Nat} (I O : Fin n → Type u)
    (A B : CMatrix (Comb.Space (paddedInput O) (paddedOutput I))) :
    unpad I O (A+B) = unpad I O A + unpad I O B := matReindex_add _ _ _
@[simp] theorem unpad_smul {n : Nat} (I O : Fin n → Type u) (z : ℂ)
    (A : CMatrix (Comb.Space (paddedInput O) (paddedOutput I))) :
    unpad I O (z • A) = z • unpad I O A := rfl
@[simp] theorem unpad_sum {n : Nat} (I O : Fin n → Type u) {ι : Type v}
    (s : Finset ι) (A : ι → CMatrix (Comb.Space (paddedInput O) (paddedOutput I))) :
    unpad I O (∑ a ∈ s, A a) = ∑ a ∈ s, unpad I O (A a) := by
  ext p q; simp [unpad, matReindex_apply, Matrix.sum_apply]

/-- Padding is a complex-linear equivalence, with `unpad` as inverse. -/
def padLinearEquiv {n : Nat} (I O : Fin n → Type u) :
    CMatrix (Comb.Space I O) ≃ₗ[ℂ] CMatrix (Comb.Space (paddedInput O) (paddedOutput I)) where
  toEquiv := pad I O
  map_add' := pad_add I O
  map_smul' := pad_smul I O

/-- One scalar input, with no final scalar output yet. -/
def halfEquiv {n : Nat} (I : Fin (n+1) → Type u) (O : Fin n → Type u) :
    ((∀ j, I j) × (∀ j, O j)) ≃ Comb.Space (paddedInput O) I where
  toFun p := (Fin.cons PUnit.unit p.2, p.1)
  invFun p := (p.2, Fin.tail p.1)
  left_inv p := by exact Prod.ext rfl (by funext j; rfl)
  right_inv p := by
    apply Prod.ext
    · have h : p.1 0 = PUnit.unit := Subsingleton.elim _ _
      simpa only [h] using Fin.cons_self_tail p.1
    · rfl

/-- Operator transport for the intermediate half-step. -/
def halfPad {n : Nat} (I : Fin (n+1) → Type u) (O : Fin n → Type u) :=
  matReindex (halfEquiv I O)

@[simp] theorem halfPad_apply {n : Nat} (I : Fin (n+1) → Type u) (O : Fin n → Type u)
    (Θ : CMatrix ((∀ j, I j) × (∀ j, O j))) (p q : Comb.Space (paddedInput O) I) :
    halfPad I O Θ p q = Θ (p.2, Fin.tail p.1) (q.2, Fin.tail q.1) := rfl

@[simp] theorem tail_cons_padded {n : Nat} (O : Fin n → Type u) (o : ∀ j, O j) :
    Fin.tail (Fin.cons PUnit.unit o : ∀ j, paddedInput O j) = o := rfl

/-- Prefixing commutes with insertion of the initial scalar wire. -/
def inputPrefixEquiv {n : Nat} (O : Fin (n+1) → Type u) (j : Fin (n+1)) :
    paddedInput (fun k : Fin n => O k.castSucc) j ≃ paddedInput O j.castSucc :=
  Equiv.cast (by cases j using Fin.cases <;> simp [paddedInput])

private def previousHalfEquiv {n : Nat} (I : Fin (n+2) → Type u)
    (O : Fin (n+1) → Type u) :
    ((∀ j : Fin (n+1), I j.castSucc) × (∀ j : Fin n, O j.castSucc)) ≃
      Comb.Space (fun j : Fin (n+1) => paddedInput O j.castSucc)
        (fun j : Fin (n+1) => I j.castSucc) :=
  (halfEquiv (fun j => I j.castSucc) (fun j => O j.castSucc)).trans
    (Comb.spaceEquiv (inputPrefixEquiv O) (fun _ => Equiv.refl _))

private theorem previousHalfEquiv_symm_init {n : Nat} (I : Fin (n+2) → Type u)
    (O : Fin (n+1) → Type u) (o : ∀ j, O j) (i : ∀ j : Fin (n+1), I j.castSucc) :
    (previousHalfEquiv I O).symm (Fin.init (Fin.cons PUnit.unit o), i) =
      (i, Fin.init o) := by
  apply Prod.ext
  · rfl
  · funext j
    change (inputPrefixEquiv O j.succ).symm
      ((Fin.cons PUnit.unit o) j.succ.castSucc) = o j.castSucc
    rfl

/-- The half-step comb recursion is the tester recursion after tracing its
last original input. This statement includes empty original wire carriers. -/
theorem normalized_halfPad_iff {n : Nat} (I : Fin (n+1) → Type u) (O : Fin n → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (Θ : CMatrix ((∀ j, I j) × (∀ j, O j))) :
    Comb.Normalized (paddedInput O) I (halfPad I O Θ) ↔
      Θ.PosSemidef ∧ Normalized (fun j : Fin n => I j.castSucc) O
        (fun p q => ∑ z, Θ (Fin.snoc p.1 z, p.2) (Fin.snoc q.1 z, q.2)) := by
  classical
  induction n with
  | zero =>
    constructor
    · rintro ⟨hpos, K, hK, htrace⟩
      refine ⟨(matReindex_posSemidef_iff _ _).mp hpos, ?_⟩
      change K = 1 at hK
      subst K
      change _ = 1
      ext p q
      have hpq : p = q := Subsingleton.elim _ _
      subst q
      have h := htrace (Fin.cons PUnit.unit p.2) (Fin.cons PUnit.unit p.2) p.1 p.1
      simpa [halfPad_apply, Matrix.one_apply, tail_cons_padded] using h
    · rintro ⟨hpos, htrace⟩
      refine ⟨matReindex_posSemidef _ hpos, 1, rfl, ?_⟩
      intro i i' o o'
      have hii : i = i' := by
        funext j
        cases j using Fin.cases
        · exact Subsingleton.elim _ _
        · rename_i j; exact Fin.elim0 j
      have hoo : o = o' := Subsingleton.elim _ _
      subst i'; subst o'
      change _ = 1 at htrace
      have h := congrFun (congrFun htrace (o, Fin.tail i)) (o, Fin.tail i)
      simpa [halfPad_apply, Matrix.one_apply] using h
  | succ n ih =>
    have hprevious (Ξ : CMatrix ((∀ j : Fin (n+1), I j.castSucc) ×
        (∀ j : Fin n, O j.castSucc))) :
        Comb.Normalized (fun j : Fin (n+1) => paddedInput O j.castSucc)
          (fun j : Fin (n+1) => I j.castSucc) (matReindex (previousHalfEquiv I O) Ξ) ↔
        Ξ.PosSemidef ∧ Normalized (fun j : Fin n => I j.castSucc.castSucc)
          (fun j : Fin n => O j.castSucc)
          (fun p q => ∑ z, Ξ (Fin.snoc p.1 z, p.2) (Fin.snoc q.1 z, q.2)) := by
      rw [previousHalfEquiv, matReindex_trans_apply]
      rw [← Comb.Normalized.reindex_iff]
      exact ih _ _ Ξ
    constructor
    · rintro ⟨hpos, K, hK, htrace⟩
      let Ξ := matReindex (previousHalfEquiv I O).symm K
      have hk : matReindex (previousHalfEquiv I O) Ξ = K := matReindex_matReindex_symm _ _
      have hΞ := (hprevious Ξ).mp (hk.symm ▸ hK)
      refine ⟨(matReindex_posSemidef_iff _ _).mp hpos, Ξ, hΞ.1, ?_, hΞ.2⟩
      intro i i' o o'
      have h := htrace (Fin.cons PUnit.unit o) (Fin.cons PUnit.unit o') i i'
      rw [← hk] at h
      change (∑ z, Θ (Fin.snoc i z, o) (Fin.snoc i' z, o')) =
        if o (Fin.last n) = o' (Fin.last n) then
          Ξ ((previousHalfEquiv I O).symm (Fin.init (Fin.cons PUnit.unit o), i))
            ((previousHalfEquiv I O).symm (Fin.init (Fin.cons PUnit.unit o'), i')) else 0 at h
      simpa only [previousHalfEquiv_symm_init] using h
    · rintro ⟨hpos, Ξ, hΞ, htrace, hrec⟩
      refine ⟨matReindex_posSemidef _ hpos, matReindex (previousHalfEquiv I O) Ξ,
        (hprevious Ξ).mpr ⟨hΞ, hrec⟩, ?_⟩
      intro i i' o o'
      have hi : i = Fin.cons PUnit.unit (Fin.tail i) := by
        have hz : i 0 = PUnit.unit := Subsingleton.elim _ _
        simpa only [hz] using (Fin.cons_self_tail i).symm
      have hi' : i' = Fin.cons PUnit.unit (Fin.tail i') := by
        have hz : i' 0 = PUnit.unit := Subsingleton.elim _ _
        simpa only [hz] using (Fin.cons_self_tail i').symm
      conv_lhs => rw [hi, hi']
      conv_rhs => rw [hi, hi']
      change (∑ z, Θ (Fin.snoc o z, Fin.tail i) (Fin.snoc o' z, Fin.tail i')) =
        if (Fin.tail i) (Fin.last n) = (Fin.tail i') (Fin.last n) then
          Ξ ((previousHalfEquiv I O).symm (Fin.init (Fin.cons PUnit.unit (Fin.tail i)), o))
            ((previousHalfEquiv I O).symm (Fin.init (Fin.cons PUnit.unit (Fin.tail i')), o')) else 0
      erw [previousHalfEquiv_symm_init, previousHalfEquiv_symm_init]
      exact htrace o o' (Fin.tail i) (Fin.tail i')

/-- Configuration transport on the prefix before the final scalar output. -/
def fullPrefixEquiv {n : Nat} (I O : Fin (n+1) → Type u) :
    ((∀ j, I j) × (∀ j : Fin n, O j.castSucc)) ≃
      Comb.Space (fun j : Fin (n+1) => paddedInput O j.castSucc)
        (fun j : Fin (n+1) => paddedOutput I j.castSucc) :=
  (halfEquiv I (fun j => O j.castSucc)).trans
    (Comb.spaceEquiv (inputPrefixEquiv O) (innerInputEquiv I))

private theorem fullPrefixEquiv_symm_init {n : Nat} (I O : Fin (n+1) → Type u)
    (o : ∀ j, O j) (i : ∀ j, I j) :
    (fullPrefixEquiv I O).symm (Fin.init (Fin.cons PUnit.unit o),
      (Equiv.piCongrRight (innerInputEquiv I)) i) = (i, Fin.init o) := by
  apply Prod.ext
  · change (Equiv.piCongrRight (innerInputEquiv I)).symm
      ((Equiv.piCongrRight (innerInputEquiv I)) i) = i
    exact Equiv.symm_apply_apply _ _
  · funext j
    change (inputPrefixEquiv O j.succ).symm
      ((Fin.cons PUnit.unit o) j.succ.castSucc) = o j.castSucc
    rfl

/-- Padding evaluates to the original matrix after dropping scalar endpoints. -/
theorem pad_snoc_apply {n : Nat} (I O : Fin n → Type u)
    (T : CMatrix (Comb.Space I O)) (a b : ∀ j, paddedInput O j)
    (i i' : ∀ j : Fin n, paddedOutput I j.castSucc)
    (z z' : paddedOutput I (Fin.last n)) :
    pad I O T (a, Fin.snoc i z) (b, Fin.snoc i' z') =
      T ((Equiv.piCongrRight (innerInputEquiv I)).symm i, Fin.tail a)
        ((Equiv.piCongrRight (innerInputEquiv I)).symm i', Fin.tail b) := by
  change T ((Equiv.piCongrRight (innerInputEquiv I)).symm (Fin.init (Fin.snoc i z)), Fin.tail a)
    ((Equiv.piCongrRight (innerInputEquiv I)).symm (Fin.init (Fin.snoc i' z')), Fin.tail b) = _
  rw [Fin.init_snoc, Fin.init_snoc]

/-- Positivity follows from the positive half-step witness and an output
identity, including a zero-dimensional final output. -/
theorem Normalized.posSemidef {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {T : CMatrix (Comb.Space I O)} (hT : Normalized I O T) : T.PosSemidef := by
  classical
  cases n with
  | zero => change T = 1 at hT; subst T; exact Matrix.PosSemidef.one
  | succ n =>
    obtain ⟨Θ, hΘ, heq, _⟩ := hT
    have hmat : T = matReindex (Comb.finalOutputEquiv (I := I) (O := O)).symm
        (Matrix.kronecker Θ (1 : CMatrix (O (Fin.last n)))) := by
      ext p q
      rw [heq]
      change (if p.2 (Fin.last n) = q.2 (Fin.last n) then
        Θ (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0) =
        Θ (p.1, Fin.init p.2) (q.1, Fin.init q.2) *
          (1 : CMatrix (O (Fin.last n))) (p.2 (Fin.last n)) (q.2 (Fin.last n))
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [hmat]
    exact matReindex_posSemidef _ (hΘ.kronecker Matrix.PosSemidef.one)

section Finite
variable {n : Nat} (I O : Fin n → Type u)
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
@[simp] theorem pad_posSemidef_iff (T : CMatrix (Comb.Space I O)) :
    (pad I O T).PosSemidef ↔ T.PosSemidef := matReindex_posSemidef_iff _ _
omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
@[simp] theorem unpad_posSemidef_iff
    (T : CMatrix (Comb.Space (paddedInput O) (paddedOutput I))) :
    (unpad I O T).PosSemidef ↔ T.PosSemidef := matReindex_posSemidef_iff _ _

/-- Normalization of the inner comb is ordinary original-wire normalization. -/
theorem normalized_innerPad_iff (R : CMatrix (Comb.Space I O)) :
    Comb.Normalized (Comb.innerInput (paddedOutput I)) (Comb.innerOutput (paddedInput O))
      (innerPad I O R) ↔ Comb.Normalized I O R :=
  (Comb.Normalized.reindex_iff (innerInputEquiv I) (innerOutputEquiv O) R).symm

/-- Removing the explicit inner-wire identification preserves normalization. -/
theorem normalized_innerUnpad_iff
    (R : CMatrix (Comb.Space (Comb.innerInput (paddedOutput I))
      (Comb.innerOutput (paddedInput O)))) :
    Comb.Normalized I O (innerUnpad I O R) ↔
      Comb.Normalized (Comb.innerInput (paddedOutput I))
        (Comb.innerOutput (paddedInput O)) R := by
  rw [← normalized_innerPad_iff, innerPad_innerUnpad]

/-- The padded comb's recursive trace constraints are exactly the original
operator's dual tester recursion. The internal scalar case is included. -/
theorem normalized_pad_iff (T : CMatrix (Comb.Space I O)) :
    Comb.Normalized (paddedInput O) (paddedOutput I) (pad I O T) ↔ Normalized I O T := by
  classical
  cases n with
  | zero =>
    constructor
    · rintro ⟨_, K, hK, htrace⟩
      change K = 1 at hK
      subst K
      change T = 1
      ext p q
      have hpq : p = q := Subsingleton.elim _ _
      subst q
      have h := htrace (Fin.cons PUnit.unit p.2) (Fin.cons PUnit.unit p.2)
        ((Equiv.piCongrRight (innerInputEquiv I)) p.1)
        ((Equiv.piCongrRight (innerInputEquiv I)) p.1)
      simpa only [pad_snoc_apply, Equiv.symm_apply_apply, tail_cons_padded,
        Fintype.sum_unique, Matrix.one_apply, ite_true] using h
    · intro hT
      have hpos := hT.posSemidef
      change T = 1 at hT
      refine ⟨(pad_posSemidef_iff I O T).mpr hpos, 1, rfl, ?_⟩
      intro a b i i'
      have hab : a (Fin.last 0) = b (Fin.last 0) := by
        change a 0 = b 0
        exact Subsingleton.elim _ _
      have hp : ((Equiv.piCongrRight (innerInputEquiv I)).symm i, Fin.tail a) =
        ((Equiv.piCongrRight (innerInputEquiv I)).symm i', Fin.tail b) := Subsingleton.elim _ _
      simp only [pad_snoc_apply, hT, Fintype.sum_unique, Matrix.one_apply, hab, ite_true]
      exact ite_eq_left hp
  | succ n =>
    have hprefix (Θ : CMatrix ((∀ j, I j) × (∀ j : Fin n, O j.castSucc))) :
        Comb.Normalized (fun j : Fin (n+1) => paddedInput O j.castSucc)
          (fun j : Fin (n+1) => paddedOutput I j.castSucc)
          (matReindex (fullPrefixEquiv I O) Θ) ↔
        Θ.PosSemidef ∧ Normalized (fun j : Fin n => I j.castSucc)
          (fun j : Fin n => O j.castSucc)
          (fun p q => ∑ z, Θ (Fin.snoc p.1 z, p.2) (Fin.snoc q.1 z, q.2)) := by
      rw [fullPrefixEquiv, matReindex_trans_apply]
      rw [← Comb.Normalized.reindex_iff]
      exact normalized_halfPad_iff _ _ Θ
    constructor
    · rintro ⟨_, K, hK, htrace⟩
      let Θ := matReindex (fullPrefixEquiv I O).symm K
      have hk : matReindex (fullPrefixEquiv I O) Θ = K := matReindex_matReindex_symm _ _
      have hΘ := (hprefix Θ).mp (hk.symm ▸ hK)
      refine ⟨Θ, hΘ.1, ?_, hΘ.2⟩
      intro i i' o o'
      have h := htrace (Fin.cons PUnit.unit o) (Fin.cons PUnit.unit o')
        ((Equiv.piCongrRight (innerInputEquiv I)) i)
        ((Equiv.piCongrRight (innerInputEquiv I)) i')
      rw [← hk] at h
      simp only [pad_snoc_apply, Equiv.symm_apply_apply, tail_cons_padded,
        Fintype.sum_unique, matReindex_apply] at h
      change T (i,o) (i',o') = if o (Fin.last n) = o' (Fin.last n) then
        Θ ((fullPrefixEquiv I O).symm (Fin.init (Fin.cons PUnit.unit o),
          (Equiv.piCongrRight (innerInputEquiv I)) i))
          ((fullPrefixEquiv I O).symm (Fin.init (Fin.cons PUnit.unit o'),
          (Equiv.piCongrRight (innerInputEquiv I)) i')) else 0 at h
      simpa only [fullPrefixEquiv_symm_init] using h
    · intro hT
      have hpos := hT.posSemidef
      obtain ⟨Θ, hΘ, htrace, hrec⟩ := hT
      refine ⟨(pad_posSemidef_iff I O T).mpr hpos,
        matReindex (fullPrefixEquiv I O) Θ, (hprefix Θ).mpr ⟨hΘ, hrec⟩, ?_⟩
      intro a b i i'
      obtain ⟨i, rfl⟩ := (Equiv.piCongrRight (innerInputEquiv I)).surjective i
      obtain ⟨i', rfl⟩ := (Equiv.piCongrRight (innerInputEquiv I)).surjective i'
      have ha : a = Fin.cons PUnit.unit (Fin.tail a) := by
        have hz : a 0 = PUnit.unit := Subsingleton.elim _ _
        simpa only [hz] using (Fin.cons_self_tail a).symm
      have hb : b = Fin.cons PUnit.unit (Fin.tail b) := by
        have hz : b 0 = PUnit.unit := Subsingleton.elim _ _
        simpa only [hz] using (Fin.cons_self_tail b).symm
      conv_lhs => rw [ha, hb]
      conv_rhs => rw [ha, hb]
      simp only [pad_snoc_apply, Equiv.symm_apply_apply, Fintype.sum_unique,
        matReindex_apply]
      change T (i, Fin.tail a) (i', Fin.tail b) =
        if (Fin.tail a) (Fin.last n) = (Fin.tail b) (Fin.last n) then
        Θ ((fullPrefixEquiv I O).symm (Fin.init (Fin.cons PUnit.unit (Fin.tail a)),
          (Equiv.piCongrRight (innerInputEquiv I)) i))
          ((fullPrefixEquiv I O).symm (Fin.init (Fin.cons PUnit.unit (Fin.tail b)),
          (Equiv.piCongrRight (innerInputEquiv I)) i')) else 0
      erw [fullPrefixEquiv_symm_init, fullPrefixEquiv_symm_init]
      exact htrace i i' (Fin.tail a) (Fin.tail b)

/-- Every entry of the padded scalar action is the original Born pairing. -/
theorem actionMap_pad_apply (T R : CMatrix (Comb.Space I O))
    (a b : paddedInput O 0 × paddedOutput I (Fin.last n)) :
    Comb.actionMap (paddedInput O) (paddedOutput I) (pad I O T)
      (innerPad I O R) a b = pairing T R := by
  change (∑ x, ∑ y, innerPad I O R x y *
    matReindex (Comb.actionEquiv (paddedInput O) (paddedOutput I))
      (pad I O T) (x,a) (y,b)) = _
  rw [← (innerEquiv I O).sum_comp]
  simp_rw [← (innerEquiv I O).sum_comp]
  simp [innerPad, pad, matReindex_apply, paddingEquiv, pairing,
    mul_comm]

/-- The link-product action has the same scalar Born entries. -/
theorem linkAction_pad_apply (T R : CMatrix (Comb.Space I O))
    (a b : paddedInput O 0 × paddedOutput I (Fin.last n)) :
    Comb.linkAction (paddedInput O) (paddedOutput I) (pad I O T)
      (innerPad I O R) a b = pairing T R := by
  rw [← Comb.actionMap_eq_linkAction]
  exact actionMap_pad_apply I O T R a b

/-- Tracing the scalar output introduces no dimension factor. -/
theorem actionTrace_pad_apply (T R : CMatrix (Comb.Space I O))
    (a b : paddedInput O 0) :
    Comb.actionTrace (pad I O T) (innerPad I O R) a b = pairing T R := by
  simp [Comb.actionTrace_apply, partialTraceB, actionMap_pad_apply]

end Finite
end QIT.HigherOrder.Tester
