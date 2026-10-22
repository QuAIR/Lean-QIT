/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.Closure
public import QIT.HigherOrder.Comb.Compression
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-!
# Choi characterization of deterministic quantum combs

`normalized_iff_isDeterministicMap` relates independent recursive normalization
and complete admissible-map semantics through the actual Choi-space action.
`isDeterministicMap_iff_normalized_choi` gives the corresponding statement for
an arbitrary matrix map; `normalized_one_iff_channel` is the one-tooth endpoint.

Necessity follows the proof at comblong-pub.tex lines 1530-1689 of
[Chiribella2009Networks, comblong-pub.tex:1504-1514]. A constant channel-trace
observation factors through the last inner-output marginal. Choi matrix units
then force the last-input identity factor, whose positive predecessor is tested
by appending a state-preparation channel. The induction needs only ordinary
normalized inputs; the already proved forward direction recovers complete
preservation for every joint input with independent input and output spectators.

No wire is assumed inhabited in the characterization. In the degenerate case,
trace preservation forces all outputs before the first empty input to be
inhabited, which supplies a normalized reference with the same empty carrier.
This argument avoids selecting a state on an empty system. The equivalence
characterizes admissible maps; circuit realization is a separate theorem.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder.Comb

variable {n : Nat} {I O : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- A positive operator with the same final-output marginal as a normalized
comb has the same recursive normalization witness. No wire needs to be inhabited. -/
theorem Normalized.of_output_marginal_eq
    {A B : CMatrix (Space I O)} (hA : Normalized I O A) (hB : B.PosSemidef)
    (h : ∀ (i i' : ∀ j, I j) (o o' : ∀ j : Fin n, O j.castSucc),
      (∑ z, B (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
        ∑ z, A (i, Fin.snoc o z) (i', Fin.snoc o' z)) :
    Normalized I O B := by
  obtain ⟨_, K, hK, htrace⟩ := hA
  exact ⟨hB, K, hK, fun i i' o o' ↦ (h i i' o o').trans (htrace i i' o o')⟩

/-- Two positive operators with equal final-output marginal have a common
positive completion whenever the first is probabilistic. This is the source's
`lemtwoprob` argument (comblong-pub.tex lines 1544-1553); it also covers singular
and zero operators. -/
theorem IsProbabilistic.exists_common_completion
    {A B : CMatrix (Space I O)} (hA : IsProbabilistic I O A) (hB : B.PosSemidef)
    (h : ∀ (i i' : ∀ j, I j) (o o' : ∀ j : Fin n, O j.castSucc),
      (∑ z, B (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
        ∑ z, A (i, Fin.snoc o z) (i', Fin.snoc o' z)) :
    ∃ T : CMatrix (Space I O), T.PosSemidef ∧
      Normalized I O (A + T) ∧ Normalized I O (B + T) := by
  obtain ⟨_, D, hD, hAD⟩ := hA
  refine ⟨D - A, Matrix.le_iff.mp hAD, ?_, ?_⟩
  · simpa only [add_sub_cancel] using hD
  · apply hD.of_output_marginal_eq (hB.add (Matrix.le_iff.mp hAD))
    intro i i' o o'
    simp only [Matrix.add_apply, Matrix.sub_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [h]
    abel

/-- A linear observation that is constant on deterministic combs cannot
distinguish probabilistic operators with the same final-output marginal.
This is the cancellation step in the necessity proof. -/
theorem IsProbabilistic.map_eq_of_output_marginal_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : CMatrix (Space I O) →ₗ[ℂ] V) (v : V)
    (hF : ∀ D, Normalized I O D → F D = v)
    {A B : CMatrix (Space I O)} (hA : IsProbabilistic I O A) (hB : B.PosSemidef)
    (h : ∀ (i i' : ∀ j, I j) (o o' : ∀ j : Fin n, O j.castSucc),
      (∑ z, B (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
        ∑ z, A (i, Fin.snoc o z) (i', Fin.snoc o' z)) : F A = F B := by
  obtain ⟨T, _, hAT, hBT⟩ := hA.exists_common_completion hB h
  have heq := (hF _ hAT).trans (hF _ hBT).symm
  simpa only [map_add, add_left_inj] using heq

/-- The maximally mixed output reference comb. Only output wires need to be
inhabited; inputs may be empty.
[Chiribella2009Networks, comblong-pub.tex:1504-1514]. -/
theorem normalized_scalar_identity {n : Nat} (I O : Fin n → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)] :
    Normalized I O (((∏ j, (Fintype.card (O j) : ℝ)⁻¹) : ℝ) •
      (1 : CMatrix (Space I O))) := by
  classical
  induction n with
  | zero => simp [Normalized]
  | succ n ih =>
    refine ⟨Matrix.PosSemidef.one.smul (Finset.prod_nonneg fun j _ ↦ inv_nonneg.mpr
      (Nat.cast_nonneg _)), _, ih (fun j ↦ I j.castSucc) (fun j ↦ O j.castSucc), ?_⟩
    intro i i' o o'
    have hc : (Fintype.card (O (Fin.last n)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Matrix.smul_apply, Matrix.one_apply,
      Complex.real_smul, Prod.mk.injEq, Fin.snoc_inj, and_true]
    by_cases hi : i = i'
    · subst i'
      by_cases ho : o = o'
      · subst o'
        simp only [and_self, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fin.prod_univ_castSucc]
        push_cast
        field_simp
      · simp [ho]
    · have hpair : ¬ ((fun j : Fin n ↦ i j.castSucc) = (fun j : Fin n ↦ i' j.castSucc) ∧
          i (Fin.last n) = i' (Fin.last n)) := by
        intro h
        apply hi
        rw [← Fin.snoc_init_self i, ← Fin.snoc_init_self i']
        exact congrArg₂ Fin.snoc h.1 h.2
      simp only [hi, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]
      by_cases ht : i (Fin.last n) = i' (Fin.last n)
      · have hp : (fun j : Fin n ↦ i j.castSucc) ≠ (fun j : Fin n ↦ i' j.castSucc) :=
          fun h ↦ hpair ⟨h, ht⟩
        simp [ht, hp]
      · simp [ht]


open scoped Matrix.Norms.L2Operator in
private theorem exists_pos_smul_le_scalar_identity {a : Type u} [Fintype a] [DecidableEq a]
    (A : CMatrix a) (hA : A.PosSemidef) (c : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧ t • A ≤ c • (1 : CMatrix a) := by
  let t := c / (‖A‖ + 1)
  have hd : 0 < ‖A‖ + 1 := by positivity
  have ht : 0 < t := div_pos hc hd
  refine ⟨t, ht, ?_⟩
  have hpos := hA.smul ht.le
  have hb : ‖t • A‖ ≤ c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  let : CStarAlgebra (CMatrix a) := {}
  have hs : algebraMap ℝ (CMatrix a) c = c • (1 : CMatrix a) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h, Complex.real_smul]
  rw [← hs]
  exact (CStarAlgebra.norm_le_iff_le_algebraMap (t • A) hc.le hpos.nonneg).mp hb

/-- Positive operators can be rescaled to probabilistic combs using the
maximally mixed output reference.
[Chiribella2009Networks, comblong-pub.tex:1504-1514]. -/
theorem exists_pos_smul_isProbabilistic [∀ j, Nonempty (O j)]
    (A : CMatrix (Space I O)) (hA : A.PosSemidef) :
    ∃ t : ℝ, 0 < t ∧ IsProbabilistic I O (t • A) := by
  let c : ℝ := ∏ j, (Fintype.card (O j) : ℝ)⁻¹
  have hc : 0 < c := Finset.prod_pos fun j _ ↦ inv_pos.mpr
    (Nat.cast_pos.mpr Fintype.card_pos)
  obtain ⟨t, ht, hbound⟩ := exists_pos_smul_le_scalar_identity A hA c hc
  exact ⟨t, ht, hA.smul ht.le, c • 1, normalized_scalar_identity I O, hbound⟩

/-- Constant deterministic observations factor through the final-output
marginal on the entire positive cone, rather than only on probabilistic combs.
[Chiribella2009Networks, comblong-pub.tex:1504-1514]. -/
theorem map_eq_of_posSemidef_output_marginal_eq [∀ j, Nonempty (O j)]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : CMatrix (Space I O) →ₗ[ℂ] V) (v : V)
    (hF : ∀ D, Normalized I O D → F D = v)
    {A B : CMatrix (Space I O)} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : ∀ (i i' : ∀ j, I j) (o o' : ∀ j : Fin n, O j.castSucc),
      (∑ z, B (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
        ∑ z, A (i, Fin.snoc o z) (i', Fin.snoc o' z)) : F A = F B := by
  obtain ⟨t, ht, hprob⟩ := exists_pos_smul_isProbabilistic A hA
  have hscaled := hprob.map_eq_of_output_marginal_eq F v hF (hB.smul ht.le)
    (fun i i' o o' ↦ by
      simp only [Matrix.smul_apply, ← Finset.smul_sum]
      exact congrArg (t • ·) (h i i' o o'))
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul] at hscaled
  exact smul_right_injective V (show (t : ℂ) ≠ 0 by exact_mod_cast ht.ne') hscaled

/-- Group the final output separately for marginalization and state preparation. -/
def finalOutputEquiv : Space I O ≃
    ((∀ j, I j) × (∀ j : Fin n, O j.castSucc)) × O (Fin.last n) where
  toFun p := ((p.1, Fin.init p.2), p.2 (Fin.last n))
  invFun p := (p.1.1, Fin.snoc p.1.2 p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- Trace the final output without changing the remaining wire order. -/
def outputMarginal : CMatrix (Space I O) →ₗ[ℂ]
    CMatrix ((∀ j, I j) × (∀ j : Fin n, O j.castSucc)) where
  toFun A := diagonalSum (fun p z ↦ (p.1, Fin.snoc p.2 z)) A
  map_add' A B := by ext p q; simp [diagonalSum, Finset.sum_add_distrib]
  map_smul' c A := by ext p q; simp [diagonalSum, Finset.mul_sum]

/-- Prepare a basis state on the final output, retaining the given marginal. -/
def prepareOutput (c : O (Fin.last n)) :
    CMatrix ((∀ j, I j) × (∀ j : Fin n, O j.castSucc)) →ₗ[ℂ]
      CMatrix (Space I O) where
  toFun B := fun p q ↦ if p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
    B (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0
  map_add' A B := by
    ext p q
    change (if p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
      A (p.1, Fin.init p.2) (q.1, Fin.init q.2) +
        B (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0) =
      (if p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
        A (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0) +
      (if p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
        B (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0)
    split_ifs <;> simp
  map_smul' z A := by
    ext p q
    change (if p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
      z * A (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0) =
      z * (if p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
        A (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0)
    split_ifs <;> simp

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Fintype (O j)] in
@[simp] theorem prepareOutput_apply (c : O (Fin.last n))
    (B : CMatrix ((∀ j, I j) × (∀ j : Fin n, O j.castSucc))) (p q : Space I O) :
    prepareOutput c B p q = if p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
      B (p.1, Fin.init p.2) (q.1, Fin.init q.2) else 0 := rfl

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- Taking an output marginal preserves positivity. -/
theorem outputMarginal_posSemidef {A : CMatrix (Space I O)} (hA : A.PosSemidef) :
    (outputMarginal A).PosSemidef := diagonalSum_posSemidef _ hA

omit [∀ j, DecidableEq (I j)] in
/-- Preparing a pure output state preserves positivity, also for singular marginals. -/
theorem prepareOutput_posSemidef (c : O (Fin.last n))
    {B : CMatrix ((∀ j, I j) × (∀ j : Fin n, O j.castSucc))} (hB : B.PosSemidef) :
    (prepareOutput c B).PosSemidef := by
  classical
  have hp := (hB.kronecker (rankOneMatrix_pos (Pi.single c (1 : ℂ)))).submatrix
    (finalOutputEquiv (I := I) (O := O))
  convert hp using 1
  ext p q
  simp only [prepareOutput_apply, Matrix.submatrix_apply,
    Matrix.kronecker_apply, finalOutputEquiv, Equiv.coe_fn_mk, rankOneMatrix_apply]
  by_cases h : p.2 (Fin.last n) = c <;> by_cases h' : q.2 (Fin.last n) = c <;>
    simp [h, h']

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] in
@[simp] theorem outputMarginal_prepareOutput (c : O (Fin.last n))
    (B : CMatrix ((∀ j, I j) × (∀ j : Fin n, O j.castSucc))) :
    outputMarginal (prepareOutput c B) = B := by
  classical
  ext p q
  change (∑ z, prepareOutput c B (p.1, Fin.snoc p.2 z) (q.1, Fin.snoc q.2 z)) = _
  simp only [prepareOutput_apply, Fin.snoc_last, Fin.init_snoc, and_self]
  simp

/-- A complex-linear map is determined by its values on positive operators. -/
theorem linearMap_ext_posSemidef {a : Type u} [Fintype a] [DecidableEq a]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F G : CMatrix a →ₗ[ℂ] V)
    (h : ∀ A, A.PosSemidef → F A = G A) : F = G := by
  open scoped Matrix.Norms.L2Operator in
    apply LinearMap.ext_on CStarAlgebra.span_nonneg
  intro A hA
  exact h A (Matrix.nonneg_iff_posSemidef.mp hA)

/-- A constant deterministic observation factors through the output marginal
on all matrices, including non-Hermitian matrix units. -/
theorem map_eq_prepareOutput_marginal [∀ j, Nonempty (O j)]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : CMatrix (Space I O) →ₗ[ℂ] V) (v : V)
    (hF : ∀ D, Normalized I O D → F D = v) (c : O (Fin.last n))
    (A : CMatrix (Space I O)) : F A = F (prepareOutput c (outputMarginal A)) := by
  have heq : F = F.comp ((prepareOutput c).comp outputMarginal) := by
    apply linearMap_ext_posSemidef
    intro B hB
    apply map_eq_of_posSemidef_output_marginal_eq F v hF hB
      (prepareOutput_posSemidef c (outputMarginal_posSemidef hB))
    intro i i' o o'
    exact congrFun (congrFun (outputMarginal_prepareOutput c (outputMarginal B)) (i, o))
      (i', o')
  exact LinearMap.congr_fun heq A

private def inputUnitEquiv (A : Fin (n + 1) → Type u) (j : Fin (n + 1)) :
    boundaryInput A PUnit j ≃ A j :=
  Fin.cases (Equiv.prodPUnit _) (fun _ ↦ Equiv.refl _) j

private def outputUnitEquiv (A : Fin (n + 1) → Type u) (j : Fin (n + 1)) :
    boundaryOutput A PUnit j ≃ A j := by
  cases j using Fin.lastCases with
  | last =>
    have h : boundaryOutput A PUnit (Fin.last n) = (A (Fin.last n) × PUnit.{u + 1}) := by
      simp [boundaryOutput]
    exact (Equiv.cast h).trans (Equiv.prodPUnit _)
  | cast k => exact Equiv.cast (by simp [boundaryOutput])

private theorem inputUnitEquiv_read (A : Fin (n + 1) → Type u)
    (x : ∀ j, boundaryInput A PUnit j) :
    (fun j ↦ inputUnitEquiv A j (x j)) = (boundaryInputEquiv A PUnit x).1 := by
  funext j
  cases j using Fin.cases <;> simp [inputUnitEquiv, boundaryInputEquiv] <;> rfl

private theorem outputUnitEquiv_read (A : Fin (n + 1) → Type u)
    (x : ∀ j, boundaryOutput A PUnit j) :
    (fun j ↦ outputUnitEquiv A j (x j)) = (boundaryOutputEquiv A PUnit x).1 := by
  funext j
  cases j using Fin.lastCases <;> simp [outputUnitEquiv, boundaryOutputEquiv]
  rfl

/-- Unit spectators recover the original normalization predicate. -/
theorem Normalized.extendedUnit {X : CMatrix (Space I O)} (hX : Normalized I O X) :
    ExtendedNormalized I O PUnit PUnit
      (fun p q ↦ X (p.1.1, p.2.1) (q.1.1, q.2.1)) := by
  let e := spaceEquiv (inputUnitEquiv I) (outputUnitEquiv O)
  have hmat : WireFam.matReindex e (X.submatrix e e) = X := by
    ext p q
    change X (e (e.symm p)) (e (e.symm q)) = X p q
    simp
  have h := (Normalized.reindex_iff (inputUnitEquiv I) (outputUnitEquiv O)
    (X.submatrix e e)).mpr (hmat.symm ▸ hX)
  change Normalized _ _ _
  convert h using 1
  ext p q
  change X ((boundaryEquiv I O PUnit PUnit p).1.1,
    (boundaryEquiv I O PUnit PUnit p).2.1)
      ((boundaryEquiv I O PUnit PUnit q).1.1,
        (boundaryEquiv I O PUnit PUnit q).2.1) = X (e p) (e q)
  change X ((boundaryInputEquiv I PUnit p.1).1, (boundaryOutputEquiv O PUnit p.2).1)
      ((boundaryInputEquiv I PUnit q.1).1, (boundaryOutputEquiv O PUnit q.2).1) =
    X ((fun j ↦ inputUnitEquiv I j (p.1 j)), (fun j ↦ outputUnitEquiv O j (p.2 j)))
      ((fun j ↦ inputUnitEquiv I j (q.1 j)), (fun j ↦ outputUnitEquiv O j (q.2 j)))
  rw [inputUnitEquiv_read, outputUnitEquiv_read, inputUnitEquiv_read, outputUnitEquiv_read]

/-- Complete deterministic preservation includes ordinary deterministic inputs.
The unit spectators are removed by actual reindexing and singleton summation. -/
theorem IsDeterministicMap.unextended {n : Nat} {I O : Fin (n + 2) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {S : MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O (Fin.last (n + 1)))}
    (hS : IsDeterministicMap I O S)
    {X : CMatrix (Space (innerInput O) (innerOutput I))}
    (hX : Normalized (innerInput O) (innerOutput I) X) :
    partialTraceB (S X) = 1 := by
  have h := (IsDeterministicMap.channel I O hS PUnit PUnit _ hX.extendedUnit).2
  ext a a'
  have he := congrFun (congrFun h (a, PUnit.unit)) (a', PUnit.unit)
  change (∑ z : O (Fin.last (n + 1)) × PUnit,
    S X (a, z.1) (a', z.1)) = (1 : CMatrix (I 0 × PUnit)) (a, PUnit.unit)
      (a', PUnit.unit) at he
  change (∑ z, S X (a, z) (a', z)) = if a = a' then 1 else 0
  simpa only [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
    Matrix.one_apply, Prod.mk.injEq, and_true] using he

private theorem partialTraceB_single {a b : Type u} [Fintype b]
    [DecidableEq a] [DecidableEq b] (x y : a × b) :
    partialTraceB (Matrix.single x y (1 : ℂ)) =
      if x.2 = y.2 then Matrix.single x.1 y.1 (1 : ℂ) else 0 := by
  classical
  rcases x with ⟨x, z⟩
  rcases y with ⟨y, w⟩
  ext p q
  change (∑ t, Matrix.single (x, z) (y, w) (1 : ℂ) (p, t) (q, t)) = _
  by_cases h : z = w
  · subst w
    simp only [↓reduceIte, Matrix.single_apply, Prod.mk.injEq]
    by_cases hp : x = p <;> by_cases hq : y = q <;>
      simp [hp, hq]
  · rw [ite_eq_right h]
    change (∑ t, Matrix.single (x, z) (y, w) (1 : ℂ) (p, t) (q, t)) = 0
    apply Finset.sum_eq_zero
    intro t _
    apply Matrix.single_apply_of_ne
    rintro ⟨h₁, h₂⟩
    exact h ((congrArg Prod.snd h₁).trans (congrArg Prod.snd h₂).symm)

omit [∀ j, Fintype (I j)] in
private theorem outputMarginal_single (x y : Space I O) :
    outputMarginal (Matrix.single x y (1 : ℂ)) =
      if x.2 (Fin.last n) = y.2 (Fin.last n) then
        Matrix.single (x.1, Fin.init x.2) (y.1, Fin.init y.2) (1 : ℂ) else 0 := by
  change partialTraceB ((Matrix.single x y (1 : ℂ)).submatrix
    (finalOutputEquiv (I := I) (O := O)).symm
    (finalOutputEquiv (I := I) (O := O)).symm) = _
  rw [Matrix.submatrix_single_equiv, partialTraceB_single]
  rfl

omit [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] in
private theorem prepareOutput_single (c : O (Fin.last n))
    (x y : (∀ j, I j) × (∀ j : Fin n, O j.castSucc)) :
    prepareOutput c (Matrix.single x y (1 : ℂ)) =
      Matrix.single (x.1, Fin.snoc x.2 c) (y.1, Fin.snoc y.2 c) (1 : ℂ) := by
  classical
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  ext p q
  rcases p with ⟨i, o⟩
  rcases q with ⟨i', o'⟩
  rw [← Fin.snoc_init_self o, ← Fin.snoc_init_self o']
  simp only [prepareOutput_apply, Fin.snoc_last, Fin.init_snoc]
  by_cases h : o (Fin.last n) = c ∧ o' (Fin.last n) = c
  · obtain ⟨h, h'⟩ := h
    simp [h, h', Matrix.single_apply, Prod.mk.injEq, Fin.snoc_inj]
  · rw [ite_eq_right h]
    symm
    apply Matrix.single_apply_of_ne
    rintro ⟨h₁, h₂⟩
    apply h
    constructor
    · simpa only [Fin.snoc_last] using (congrArg (fun p ↦ p.2 (Fin.last n)) h₁).symm
    · simpa only [Fin.snoc_last] using (congrArg (fun p ↦ p.2 (Fin.last n)) h₂).symm

private theorem map_single_eq_prepareOutput [∀ j, Nonempty (O j)]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : CMatrix (Space I O) →ₗ[ℂ] V) (v : V)
    (hF : ∀ D, Normalized I O D → F D = v) (c : O (Fin.last n))
    (x y : Space I O) :
    F (Matrix.single x y (1 : ℂ)) =
      if x.2 (Fin.last n) = y.2 (Fin.last n) then
        F (Matrix.single (x.1, Fin.snoc (Fin.init x.2) c)
          (y.1, Fin.snoc (Fin.init y.2) c) (1 : ℂ)) else 0 := by
  rw [map_eq_prepareOutput_marginal F v hF c (Matrix.single x y (1 : ℂ)),
    outputMarginal_single]
  split_ifs
  · rw [prepareOutput_single]
  · simp only [map_zero]

/-- The final channel-output trace of the Choi-space action. -/
def actionTrace (J : CMatrix (Space I O)) :
    CMatrix (Space (innerInput O) (innerOutput I)) →ₗ[ℂ] CMatrix (I 0) where
  toFun X := partialTraceB (actionMap I O J X)
  map_add' X Y := by rw [map_add, partialTraceB_add]
  map_smul' c X := by simp only [map_smul, partialTraceB_smul, RingHom.id_apply]

@[simp] theorem actionTrace_apply (J : CMatrix (Space I O))
    (X : CMatrix (Space (innerInput O) (innerOutput I))) :
    actionTrace J X = partialTraceB (actionMap I O J X) := rfl

private theorem actionTrace_single (J : CMatrix (Space I O))
    (x y : Space (innerInput O) (innerOutput I)) (a a' : I 0) :
    actionTrace J (Matrix.single x y (1 : ℂ)) a a' =
      ∑ b, J (Fin.cons a x.2, Fin.snoc x.1 b) (Fin.cons a' y.2, Fin.snoc y.1 b) := by
  change (∑ b, actionMap I O J (Matrix.single x y (1 : ℂ)) (a, b) (a', b)) = _
  apply Finset.sum_congr rfl
  intro b _
  exact congrFun (congrFun (choi_actionMap I O J) (x, (a, b))) (y, (a', b))

/-- The positive predecessor candidate obtained by preparing the removed input
in a basis state and tracing the removed output. -/
def predecessor (J : CMatrix (Space I O)) (c : I (Fin.last n)) :
    CMatrix (Space (fun j : Fin n ↦ I j.castSucc) (fun j ↦ O j.castSucc)) :=
  diagonalSum (fun p z ↦ (Fin.snoc p.1 c, Fin.snoc p.2 z)) J

omit [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, DecidableEq (O j)] in
/-- The predecessor candidate is a positive compression of the original operator. -/
theorem predecessor_posSemidef {J : CMatrix (Space I O)} (hJ : J.PosSemidef)
    (c : I (Fin.last n)) : (predecessor J c).PosSemidef := diagonalSum_posSemidef _ hJ

private theorem cons_snoc_init_tail {n : Nat} {A : Fin (n + 2) → Type u}
    (i : ∀ j, A j) (c : A (Fin.last (n + 1))) :
    Fin.cons (i 0) (Fin.snoc (Fin.init (Fin.tail i)) c) = Fin.snoc (Fin.init i) c := by
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp
  · cases k using Fin.cases with
    | zero => rfl
    | succ k =>
      change (Fin.snoc (Fin.init (Fin.tail i)) c) k.castSucc =
        (Fin.snoc (Fin.init i) c) k.succ.castSucc
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl

/-- Constancy of the channel trace forces the last-input identity factor.
The predecessor is an explicit positive compression, rather than an assumed
operator identity. This is the Choi-inverse step of the source's necessity proof. -/
theorem output_marginal_eq_predecessor {n : Nat} {I O : Fin (n + 2) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j : Fin (n + 1), Nonempty (I j.succ)]
    (J : CMatrix (Space I O))
    (hJ : ∀ X, Normalized (innerInput O) (innerOutput I) X → actionTrace J X = 1)
    (c : I (Fin.last (n + 1)))
    (i i' : ∀ j, I j) (o o' : ∀ j : Fin (n + 1), O j.castSucc) :
    (∑ z, J (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
      if i (Fin.last (n + 1)) = i' (Fin.last (n + 1)) then
        predecessor J c (Fin.init i, o) (Fin.init i', o') else 0 := by
  have heq := map_single_eq_prepareOutput (actionTrace J) 1 hJ c
    (o, Fin.tail i) (o', Fin.tail i')
  have hlast : (Fin.tail i) (Fin.last n) = i (Fin.last (n + 1)) := by rfl
  have hlast' : (Fin.tail i') (Fin.last n) = i' (Fin.last (n + 1)) := by rfl
  simp only [hlast, hlast'] at heq
  by_cases h : i (Fin.last (n + 1)) = i' (Fin.last (n + 1))
  · rw [ite_eq_left h] at heq ⊢
    have he := congrFun (congrFun heq (i 0)) (i' 0)
    simpa only [actionTrace_single, Fin.cons_self_tail, cons_snoc_init_tail,
      predecessor, diagonalSum] using he
  · rw [ite_eq_right h] at heq ⊢
    have he := congrFun (congrFun heq (i 0)) (i' 0)
    simpa only [actionTrace_single, Fin.cons_self_tail, Matrix.zero_apply] using he

/-- Append a channel that ignores its input and prepares a fixed pure output. -/
def appendState (c : O (Fin.last n)) :
    CMatrix (Space (fun j : Fin n ↦ I j.castSucc) (fun j ↦ O j.castSucc)) →ₗ[ℂ]
      CMatrix (Space I O) where
  toFun R := fun p q ↦
    R (Fin.init p.1, Fin.init p.2) (Fin.init q.1, Fin.init q.2) *
      (1 : CMatrix (I (Fin.last n))) (p.1 (Fin.last n)) (q.1 (Fin.last n)) *
      rankOneMatrix (Pi.single c (1 : ℂ)) (p.2 (Fin.last n)) (q.2 (Fin.last n))
  map_add' R T := by
    ext p q
    change (R _ _ + T _ _) * _ * _ = R _ _ * _ * _ + T _ _ * _ * _
    ring
  map_smul' z R := by
    ext p q
    change (z * R _ _) * _ * _ = z * (R _ _ * _ * _)
    ring

omit [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] in
private theorem appendState_apply (c : O (Fin.last n))
    (R : CMatrix (Space (fun j : Fin n ↦ I j.castSucc) (fun j ↦ O j.castSucc)))
    (p q : Space I O) :
    appendState c R p q = if p.1 (Fin.last n) = q.1 (Fin.last n) ∧
      p.2 (Fin.last n) = c ∧ q.2 (Fin.last n) = c then
        R (Fin.init p.1, Fin.init p.2) (Fin.init q.1, Fin.init q.2) else 0 := by
  classical
  change R _ _ * (1 : CMatrix (I (Fin.last n))) _ _ * rankOneMatrix _ _ _ = _
  simp only [Matrix.one_apply, rankOneMatrix_apply]
  by_cases h₁ : p.1 (Fin.last n) = q.1 (Fin.last n) <;>
    by_cases h₂ : p.2 (Fin.last n) = c <;> by_cases h₃ : q.2 (Fin.last n) = c <;>
      simp [h₁, h₂, h₃]

/-- The appended preparation is positive for every positive predecessor. -/
theorem appendState_posSemidef (c : O (Fin.last n))
    {R : CMatrix (Space (fun j : Fin n ↦ I j.castSucc) (fun j ↦ O j.castSucc))}
    (hR : R.PosSemidef) : (appendState c R).PosSemidef := by
  have hp := (hR.kronecker (Matrix.PosSemidef.one.kronecker
    (rankOneMatrix_pos (Pi.single c (1 : ℂ))))).submatrix
      (fun p : Space I O ↦ ((Fin.init p.1, Fin.init p.2),
        (p.1 (Fin.last n), p.2 (Fin.last n))))
  convert hp using 1
  ext p q
  exact mul_assoc _ _ _

/-- Appending a state-preparation channel is a genuine deterministic extension,
including the internal scalar predecessor. -/
theorem Normalized.appendState (c : O (Fin.last n))
    {R : CMatrix (Space (fun j : Fin n ↦ I j.castSucc) (fun j ↦ O j.castSucc))}
    (hR : Normalized _ _ R) : Normalized I O (Comb.appendState c R) := by
  have hpos : R.PosSemidef := by
    cases n with
    | zero => change R = 1 at hR; rw [hR]; exact Matrix.PosSemidef.one
    | succ n => exact hR.posSemidef
  refine ⟨appendState_posSemidef c hpos, R, hR, ?_⟩
  intro i i' o o'
  simp only [appendState_apply, Fin.snoc_last, Fin.init_snoc]
  by_cases h : i (Fin.last n) = i' (Fin.last n) <;> simp [h]
  rfl

omit [∀ j, Fintype (O j)] in
private theorem appendState_single (c : O (Fin.last n))
    (x y : Space (fun j : Fin n ↦ I j.castSucc) (fun j ↦ O j.castSucc)) :
    appendState c (Matrix.single x y (1 : ℂ)) =
      ∑ z : I (Fin.last n), Matrix.single (Fin.snoc x.1 z, Fin.snoc x.2 c)
        (Fin.snoc y.1 z, Fin.snoc y.2 c) (1 : ℂ) := by
  classical
  ext p q
  rcases p with ⟨i, o⟩
  rcases q with ⟨i', o'⟩
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rw [← Fin.snoc_init_self i, ← Fin.snoc_init_self i',
    ← Fin.snoc_init_self o, ← Fin.snoc_init_self o']
  rw [Matrix.sum_apply]
  symm
  rw [Finset.sum_eq_single (i (Fin.last n))]
  · simp only [appendState_apply, Fin.snoc_last, Fin.init_snoc,
      Matrix.single_apply, Prod.mk.injEq, Fin.snoc_inj]
    split_ifs <;> aesop
  · intro z _ hz
    apply Matrix.single_apply_of_ne
    rintro ⟨h₁, _⟩
    exact hz (by simpa only [Fin.snoc_last] using congrArg (fun p ↦ p.1 (Fin.last n)) h₁)
  · simp

private theorem cons_snoc_comm {n : Nat} {A : Fin (n + 2) → Type u}
    (a : A 0) (v : ∀ j : Fin n, A j.succ.castSucc) (c : A (Fin.last (n + 1))) :
    Fin.cons a (Fin.snoc v c) = Fin.snoc (Fin.cons a v) c := by
  funext j
  cases j using Fin.cases with
  | zero => simp; rfl
  | succ j =>
    cases j using Fin.lastCases with
    | last => simp
    | cast k =>
      rw [Fin.cons_succ]
      simp [← Fin.castSucc_succ]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The smaller trace observation is the original observation after a genuine
state-preparation extension of the inserted comb. -/
theorem actionTrace_predecessor {n : Nat} {I O : Fin (n + 2) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (J : CMatrix (Space I O)) (c : I (Fin.last (n + 1))) :
    actionTrace (I := fun j : Fin (n + 1) ↦ I j.castSucc)
        (O := fun j ↦ O j.castSucc) (predecessor J c) =
      (actionTrace J).comp (appendState (I := innerInput O) (O := innerOutput I) c) := by
  apply MatrixMap.choi_inj
  ext p q
  rcases p with ⟨x, a⟩
  rcases q with ⟨y, a'⟩
  change actionTrace (predecessor J c) (Matrix.single x y (1 : ℂ)) a a' =
    actionTrace J (appendState (I := innerInput O) (O := innerOutput I) c
      (Matrix.single x y (1 : ℂ))) a a'
  rw [appendState_single, map_sum]
  simp only [Matrix.sum_apply]
  simp only [actionTrace_single]
  change (∑ z, ∑ b, J (Fin.snoc (Fin.cons a x.2) c, Fin.snoc (Fin.snoc x.1 z) b)
      (Fin.snoc (Fin.cons a' y.2) c, Fin.snoc (Fin.snoc y.1 z) b)) = _
  simp only [cons_snoc_comm]

private theorem normalized_of_actionTrace_one {I O : Fin 1 → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (J : CMatrix (Space I O)) (hpos : J.PosSemidef)
    (hJ : ∀ X, Normalized (innerInput O) (innerOutput I) X → actionTrace J X = 1) :
    Normalized I O J := by
  classical
  let x : Space (innerInput O) (innerOutput I) := ((fun j ↦ Fin.elim0 j), (fun j ↦ Fin.elim0 j))
  have hs : Matrix.single x x (1 : ℂ) = (1 : CMatrix (Space (innerInput O) (innerOutput I))) := by
    ext p q
    have hp : p = x := Subsingleton.elim _ _
    have hq : q = x := Subsingleton.elim _ _
    subst p; subst q
    simp
  have ht := hJ _ (show Normalized _ _ (Matrix.single x x (1 : ℂ)) from hs)
  refine ⟨hpos, 1, rfl, ?_⟩
  intro i i' o o'
  have he := congrFun (congrFun ht (i 0)) (i' 0)
  rw [actionTrace_single] at he
  have hi : Fin.cons (i 0) x.2 = i := by ext j; fin_cases j; rfl
  have hi' : Fin.cons (i' 0) x.2 = i' := by ext j; fin_cases j; rfl
  have ho : o = x.1 := Subsingleton.elim _ _
  have ho' : o' = x.1 := Subsingleton.elim _ _
  have hscalar : (1 : CMatrix (Space (fun j : Fin 0 ↦ I j.castSucc)
      (fun j ↦ O j.castSucc))) (Fin.init i, o) (Fin.init i', o') = 1 := by
    rw [Matrix.one_apply]
    exact ite_eq_left (Subsingleton.elim _ _)
  change (∑ z, J (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
    if i (Fin.last 0) = i' (Fin.last 0) then
      (1 : CMatrix (Space (fun j : Fin 0 ↦ I j.castSucc)
        (fun j ↦ O j.castSucc))) (Fin.init i, o) (Fin.init i', o') else 0
  rw [hscalar]
  rw [hi, hi'] at he
  simp only [ho, ho']
  convert he using 1
  rfl

/-- Necessity of the recursive constraints when all input wires are inhabited.
Output wires remain arbitrary. Degenerate input systems are handled separately. -/
theorem normalized_of_actionTrace_of_nonempty {n : Nat} {I O : Fin (n + 1) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (I j)]
    (J : CMatrix (Space I O)) (hpos : J.PosSemidef)
    (hJ : ∀ X, Normalized (innerInput O) (innerOutput I) X → actionTrace J X = 1) :
    Normalized I O J := by
  induction n with
  | zero => exact normalized_of_actionTrace_one J hpos hJ
  | succ n ih =>
    let c : I (Fin.last (n + 1)) := Classical.choice inferInstance
    refine ⟨hpos, predecessor J c, ?_, output_marginal_eq_predecessor J hJ c⟩
    apply ih (predecessor J c) (predecessor_posSemidef hpos c)
    intro X hX
    rw [actionTrace_predecessor]
    exact hJ _ (Normalized.appendState (I := innerInput O) (O := innerOutput I) c hX)

private theorem normalized_reference_of_prefix {n : Nat} (I O : Fin n → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (h : ∀ k, (∀ j, j.val ≤ k.val → Nonempty (I j)) → Nonempty (O k)) :
    Normalized I O ((∏ j, (Fintype.card (O j) : ℝ)⁻¹) • (1 : CMatrix (Space I O))) := by
  classical
  induction n with
  | zero => simp [Normalized]
  | succ n ih =>
    by_cases hi : ∀ j, Nonempty (I j)
    · have := hi
      let : ∀ j, Nonempty (O j) := fun k ↦ h k (fun j _ ↦ hi j)
      exact normalized_scalar_identity I O
    · have hempty (i : ∀ j, I j) : False := hi (fun j ↦ ⟨i j⟩)
      refine ⟨Matrix.PosSemidef.one.smul (Finset.prod_nonneg fun j _ ↦
        inv_nonneg.mpr (Nat.cast_nonneg _)), _,
        ih (fun j ↦ I j.castSucc) (fun j ↦ O j.castSucc) ?_, ?_⟩
      · intro k hk
        apply h k.castSucc
        intro j hj
        have hlt : j.val < n := Nat.lt_of_le_of_lt hj k.isLt
        exact hk ⟨j.val, hlt⟩ hj
      · intro i
        exact (hempty i).elim

private theorem actionTrace_zero : actionTrace (0 : CMatrix (Space I O)) = 0 := by
  apply MatrixMap.choi_inj
  ext p q
  change actionTrace (0 : CMatrix (Space I O)) (Matrix.single p.1 q.1 (1 : ℂ)) p.2 q.2 = 0
  rw [actionTrace_single]
  simp

/-- A deterministic trace observation forces every output before the first
empty input to be inhabited. This excludes vacuous positive-dimensional
channels while retaining empty-system semantics. -/
theorem nonempty_output_of_actionTrace
    (J : CMatrix (Space I O))
    (hJ : ∀ X, Normalized (innerInput O) (innerOutput I) X → actionTrace J X = 1)
    (k : Fin (n + 1)) (hI : ∀ j, j.val ≤ k.val → Nonempty (I j)) :
    Nonempty (O k) := by
  classical
  by_contra hO
  have hinner : ∀ l : Fin n,
      (∀ j : Fin n, j.val ≤ l.val → Nonempty (innerInput O j)) →
        Nonempty (innerOutput I l) := by
    intro l hl
    by_cases hlt : l.val < k.val
    · exact hI l.succ (by simpa only [Fin.val_succ] using Nat.succ_le_of_lt hlt)
    · have hkn : k.val < n := Nat.lt_of_le_of_lt (Nat.le_of_not_gt hlt) l.isLt
      exact (hO (hl ⟨k.val, hkn⟩ (Nat.le_of_not_gt hlt))).elim
  have hzero : J = 0 := by
    ext p q
    exact (hO ⟨p.2 k⟩).elim
  have ht := hJ _ (normalized_reference_of_prefix (innerInput O) (innerOutput I) hinner)
  rw [hzero, actionTrace_zero, LinearMap.zero_apply] at ht
  obtain ⟨a⟩ := hI 0 (Nat.zero_le _)
  have he := congrFun (congrFun ht a) a
  exact zero_ne_one (by simpa only [Matrix.zero_apply, Matrix.one_apply, ↓reduceIte] using he)

/-- The necessity direction, with no inhabitance, rank, or equal-dimension
assumption on the heterogeneous wires. -/
theorem normalized_of_actionTrace
    (J : CMatrix (Space I O)) (hpos : J.PosSemidef)
    (hJ : ∀ X, Normalized (innerInput O) (innerOutput I) X → actionTrace J X = 1) :
    Normalized I O J := by
  classical
  by_cases hi : ∀ j, Nonempty (I j)
  · have := hi
    exact normalized_of_actionTrace_of_nonempty J hpos hJ
  · have heq : J = (∏ j, (Fintype.card (O j) : ℝ)⁻¹) •
        (1 : CMatrix (Space I O)) := by
      ext p q
      exact (hi (fun j ↦ ⟨p.1 j⟩)).elim
    rw [heq]
    exact normalized_reference_of_prefix I O (nonempty_output_of_actionTrace J hJ)

/-- The non-definitional Choi characterization of deterministic combs.
Complete admissibility quantifies over all joint inner combs with independent
finite input and output spectators. Recursive normalization is equivalent to
that operational property; neither predicate is defined in terms of the other.
[Chiribella2009Networks, comblong-pub.tex:1504-1514] and
[Chiribella2007Architecture, qcombs-2.tex:310-321]. -/
theorem normalized_iff_isDeterministicMap {n : Nat} (I O : Fin (n + 2) → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] (J : CMatrix (Space I O)) :
    Normalized I O J ↔ IsDeterministicMap I O (actionMap I O J) := by
  constructor
  · exact Normalized.isDeterministicMap
  · intro h
    exact normalized_of_actionTrace J ((actionMap_cp_iff I O J).mp h.1)
      (fun _ hX ↦ h.unextended hX)

/-- The one-tooth endpoint is the ordinary completely positive,
trace-preserving Choi characterization. -/
theorem normalized_one_iff_channel {I O : Fin 1 → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] (J : CMatrix (Space I O)) :
    Normalized I O J ↔ MatrixMap.IsCompletelyPositive (MatrixMap.ofChoiMatrix J) ∧
      MatrixMap.IsTracePreserving (MatrixMap.ofChoiMatrix J) := by
  rw [normalized_one_iff, MatrixMap.IsCompletelyPositive, MatrixMap.choi_ofChoiMatrix,
    MatrixMap.isTracePreserving_iff_partialTraceB_choi, MatrixMap.choi_ofChoiMatrix]

/-- Every independently admissible map has exactly its reindexed Choi operator
as a recursively normalized comb, and every such Choi operator is admissible. -/
theorem isDeterministicMap_iff_normalized_choi {n : Nat} (I O : Fin (n + 2) → Type u)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (S : MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O (Fin.last (n + 1)))) :
    IsDeterministicMap I O S ↔
      Normalized I O (WireFam.matReindex (actionEquiv I O).symm (MatrixMap.choi S)) := by
  have hrep : actionMap I O
      (WireFam.matReindex (actionEquiv I O).symm (MatrixMap.choi S)) = S := by
    apply MatrixMap.choi_inj
    rw [choi_actionMap, WireFam.matReindex_matReindex_symm]
  rw [normalized_iff_isDeterministicMap, hrep]

end QIT.HigherOrder.Comb
