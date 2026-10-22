/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.MemoryConnection

/-!
# Finite memory realizations of deterministic combs

`normalized_iff_exists_memoryChain` realizes every positive-length normalized
comb exactly, using a dimension vector and `ULift (Fin d)` memory carriers.
`Normalized.exists_memoryChannel` gives the ordinary channel formulation.
All free wires may have different finite dimensions, including zero.

The single-step extension compares unnormalized Kraus amplitudes. Padding the
new environment extends the reference isometry on its entire domain, including
zero-dimensional systems, without requiring a minimal Kraus representation.
The induction chooses an empty final memory whenever accumulated input is empty;
this supplies the dimension bound when the next output system is empty.

`IsDeterministicMap.exists_memoryChain` chooses one fixed outer chain before
the independent ancillary systems and the joint normalized input are selected.
Its connected channel is the alternating composition from `MemoryConnection`,
with exact ancillary Choi-action equality. No minimal-memory dimension is asserted.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
universe u
namespace QIT.HigherOrder.Comb

section Extension

variable {a M C D κ : Type u}
  [Fintype a] [DecidableEq a] [Fintype M] [DecidableEq M]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype κ] [DecidableEq κ]

/-- Zero padding of the new Kraus environment by the entire incoming domain. -/
def paddedAmplitude (B : Matrix (a × C) (D × κ) ℂ) :
    Matrix (a × C) (D × (κ ⊕ (M × C))) ℂ :=
  fun x y ↦ Sum.elim (fun k ↦ B x (y.1, k)) (fun _ ↦ 0) y.2

/-- One coherent extension of a Kraus amplitude family. The only dimension
condition needed when the new output is empty is emptiness of the incoming
domain. The extra environment summand supplies the dimension bound otherwise.
This is the padded form of the source's isometry step
[Chiribella2009Networks, comblong-pub.tex:1037-1057]. -/
theorem exists_padded_step_isometry
    (A : Matrix a M ℂ) (B : Matrix (a × C) (D × κ) ℂ)
    (hGram : ∀ x y c c',
      (∑ d, ∑ k, B (x, c) (d, k) * star (B (y, c') (d, k))) =
        if c = c' then ∑ m, A x m * star (A y m) else 0)
    (hEmpty : IsEmpty D → IsEmpty (M × C)) :
    ∃ V : ReferenceIsometry (M × C) (D × (κ ⊕ (M × C))),
      ∀ x c d e, paddedAmplitude (M := M) B (x, c) (d, e) =
        ∑ m, A x m * V.matrix (d, e) (m, c) := by
  classical
  let A' : Matrix (a × C) (M × C) ℂ :=
    fun x y ↦ if x.2 = y.2 then A x.1 y.1 else 0
  have hcard : Fintype.card (M × C) ≤ Fintype.card (D × (κ ⊕ (M × C))) := by
    cases isEmpty_or_nonempty D with
    | inl hd =>
      let := hEmpty hd
      simp
    | inr hd =>
      let := hd
      exact Fintype.card_le_of_injective
        (fun x : M × C ↦ (Classical.choice hd, Sum.inr x))
        (fun _ _ h ↦ Sum.inr_injective (congrArg Prod.snd h))
  have hAA (x y : a × C) :
      (A' * A'ᴴ) x y = if x.2 = y.2 then ∑ m, A x.1 m * star (A y.1 m) else 0 := by
    change (∑ p : M × C, A' x p * star (A' y p)) = _
    simp only [A', Fintype.sum_prod_type]
    by_cases h : x.2 = y.2
    · simp [← h]
    · simp [h, ite_mul, apply_ite, eq_comm]
  have hBB (x y : a × C) :
      (paddedAmplitude (M := M) B * (paddedAmplitude (M := M) B)ᴴ) x y =
        ∑ d, ∑ k, B x (d, k) * star (B y (d, k)) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, paddedAmplitude,
      Fintype.sum_prod_type, Fintype.sum_sum_type]
  have hEq : A' * A'ᴴ = paddedAmplitude (M := M) B * (paddedAmplitude (M := M) B)ᴴ := by
    ext x y
    rw [hAA, hBB]
    exact (hGram x.1 y.1 x.2 y.2).symm
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      A' (paddedAmplitude (M := M) B) hEq hcard
  refine ⟨V, ?_⟩
  intro x c d e
  have h := congrFun (congrFun hV (x, c)) (d, e)
  change paddedAmplitude B (x, c) (d, e) =
    ∑ p : M × C, A' (x, c) p * V.matrix (d, e) p at h
  simpa [A', Fintype.sum_prod_type, ite_mul] using h

end Extension

/-- Tracing all output wires of a recursively normalized operator gives the
identity on its entire input configuration, including empty configurations. -/
theorem Normalized.partialTraceB {n : Nat} {I O : Fin n → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {J : CMatrix (Space I O)} (hJ : Normalized I O J) : partialTraceB J = 1 := by
  classical
  induction n with
  | zero =>
    change J = 1 at hJ
    subst J
    ext i i'
    simp [QIT.partialTraceB, Matrix.one_apply, Subsingleton.elim i i']
  | succ n ih =>
    obtain ⟨_, K, hK, htrace⟩ := hJ
    have hKT := ih hK
    ext i i'
    change (∑ o, J (i, o) (i', o)) = _
    rw [← Equiv.sum_comp (Fin.snocEquiv O)]
    rw [Fintype.sum_prod_type]
    change (∑ z, ∑ o, J (i, Fin.snoc o z) (i', Fin.snoc o z)) = _
    rw [Finset.sum_comm]
    simp_rw [htrace]
    by_cases hl : i (Fin.last n) = i' (Fin.last n)
    · simp only [hl, ↓reduceIte]
      change QIT.partialTraceB K (Fin.init i) (Fin.init i') = _
      rw [hKT]
      have heq : Fin.init i = Fin.init i' ↔ i = i' := by
        constructor
        · intro h
          rw [← Fin.snoc_init_self i, ← Fin.snoc_init_self i', h, hl]
        · rintro rfl; rfl
      simp [Matrix.one_apply, heq]
    · have hi : i ≠ i' := fun h ↦ hl (congrFun h _)
      simp [hl, hi]

variable {n : Nat} {I O : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The ordinary channel associated to a normalized comb's global Choi matrix. -/
def Normalized.toChannel {J : CMatrix (Space I O)} (hJ : Normalized I O J) :
    Channel (∀ j, I j) (∀ j, O j) where
  map := MatrixMap.ofChoiMatrix J
  completelyPositive := MatrixMap.ofChoiMatrix_isCompletelyPositive hJ.posSemidef
  tracePreserving := MatrixMap.isTracePreserving_iff_partialTraceB_choi _ |>.mpr
    (by rw [MatrixMap.choi_ofChoiMatrix]; exact hJ.partialTraceB)
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _
    (MatrixMap.ofChoiMatrix_isCompletelyPositive hJ.posSemidef)

@[simp] theorem Normalized.choi_toChannel {J : CMatrix (Space I O)}
    (hJ : Normalized I O J) : MatrixMap.choi hJ.toChannel.map = J :=
  MatrixMap.choi_ofChoiMatrix J

end QIT.HigherOrder.Comb

namespace QIT.HigherOrder

variable {n : Nat} {I O E : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- Every causal memory chain satisfies the recursive comb constraints
[Chiribella2009Networks, comblong-pub.tex:986-997]. -/
theorem MemoryChain.normalized (c : MemoryChain I O E) :
    Comb.Normalized I O (MatrixMap.choi c.chainMap) := by
  classical
  induction n with
  | zero =>
    exact (Comb.normalized_one_iff _).mpr
      ⟨c.chainMap_isCompletelyPositive,
        (MatrixMap.isTracePreserving_iff_partialTraceB_choi _).mp
          c.chainMap_isTracePreserving⟩
  | succ n ih =>
    refine ⟨c.chainMap_isCompletelyPositive, MatrixMap.choi c.dropLast.chainMap,
      ih c.dropLast, ?_⟩
    intro i i' o o'
    simp only [MemoryChain.choi_chainMap_apply, MemoryChain.kraus_step,
      Fin.init_snoc, Fin.snoc_last]
    have h := coherent_step_inner (c.link (Fin.last (n + 1)))
      (fun m ↦ c.dropLast.kraus m o (Fin.init i))
      (fun m ↦ c.dropLast.kraus m o' (Fin.init i'))
      (i (Fin.last (n + 1))) (i' (Fin.last (n + 1)))
    by_cases heq : i (Fin.last (n + 1)) = i' (Fin.last (n + 1))
    · simp only [heq, ↓reduceIte, one_mul] at h ⊢
      exact h
    · simp only [heq, ↓reduceIte, zero_mul] at h ⊢
      exact h

section Extend

variable {n : Nat} {I O : Fin (n + 2) → Type u}
  {E : Fin (n + 1) → Type u} {F : Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  [Fintype F] [DecidableEq F]

/-- Appending a family's last member reconstructs the original family. -/
def snocFamilyEquiv (W : Fin (n + 2) → Type u) (j : Fin (n + 2)) :
    snocFam (fun k : Fin (n + 1) ↦ W k.castSucc) (W (Fin.last (n + 1))) j ≃ W j :=
  Fin.lastCases (Equiv.cast (snocFam_last _ _))
    (fun k ↦ Equiv.cast (snocFam_castSucc _ _ k)) j

/-- Extending a prefix chain on the original, unsplit wire family. -/
def MemoryChain.extend
    (c : MemoryChain (fun j ↦ I j.castSucc) (fun j ↦ O j.castSucc) E)
    (V : ReferenceIsometry (E (Fin.last n) × I (Fin.last (n + 1)))
      (O (Fin.last (n + 1)) × F)) : MemoryChain I O (snocFam E F) :=
  (c.snoc V).reindexWires (snocFamilyEquiv I) (snocFamilyEquiv O)

/-- The extension coherently contracts the predecessor memory. -/
theorem MemoryChain.kraus_extend
    (c : MemoryChain (fun j ↦ I j.castSucc) (fun j ↦ O j.castSucc) E)
    (V : ReferenceIsometry (E (Fin.last n) × I (Fin.last (n + 1)))
      (O (Fin.last (n + 1)) × F))
    (e : snocFam E F (Fin.last (n + 1))) (o : ∀ j, O j) (i : ∀ j, I j) :
    (c.extend V).kraus e o i = ∑ m,
      c.kraus m (Fin.init o) (Fin.init i) *
        V.matrix (o (Fin.last (n + 1)), cast (snocFam_last E F) e)
          (m, i (Fin.last (n + 1))) := by
  rw [MemoryChain.extend, MemoryChain.kraus_reindexWires, MemoryChain.kraus_snoc]
  have hp (W : Fin (n + 2) → Type u) (w : ∀ j, W j) :
      (fun j : Fin (n + 1) ↦ cast (snocFam_castSucc _ _ j)
        ((snocFamilyEquiv W j.castSucc).symm (w j.castSucc))) = Fin.init w := by
    funext j
    simp only [snocFamilyEquiv, Fin.lastCases_castSucc]
    exact (Equiv.cast (snocFam_castSucc (fun k : Fin (n + 1) ↦ W k.castSucc)
      (W (Fin.last (n + 1))) j)).apply_symm_apply _
  have hl (W : Fin (n + 2) → Type u) (w : ∀ j, W j) :
      cast (snocFam_last _ _)
        ((snocFamilyEquiv W (Fin.last (n + 1))).symm (w (Fin.last (n + 1)))) =
          w (Fin.last (n + 1)) := by
    simp only [snocFamilyEquiv, Fin.lastCases_last]
    exact (Equiv.cast (snocFam_last (fun k : Fin (n + 1) ↦ W k.castSucc)
      (W (Fin.last (n + 1))))).apply_symm_apply _
  rw [hp O o, hp I i, hl O o, hl I i]

end Extend

/-- A one-link chain, with no incoming memory. -/
def MemoryChain.single {I O : Fin 1 → Type u} {F : Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [Fintype F] [DecidableEq F]
    (V : ReferenceIsometry (I 0) (O 0 × F)) : MemoryChain I O (fun _ ↦ F) where
  link := Fin.cases V (fun j ↦ Fin.elim0 j)

/-- Relabelling memories preserves the global channel Choi coordinates too. -/
theorem MemoryChain.choi_chainMap_reindexMemory (c : MemoryChain I O E)
    {F : Fin (n + 1) → Type u} [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
    (e : ∀ j, E j ≃ F j) :
    MatrixMap.choi (c.reindexMemory e).chainMap = MatrixMap.choi c.chainMap := by
  rw [← MemoryChain.chainChoi_eq_choi, MemoryChain.chainChoi_reindexMemory,
    MemoryChain.chainChoi_eq_choi]

end QIT.HigherOrder

namespace QIT.HigherOrder.Comb

/-- Standard finite memory carriers, including dimension zero. -/
abbrev Memory (d : Nat) := ULift.{u} (Fin d)

variable {n : Nat} {I O : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- Any finite chain can use dimension-labelled lifted finite memories. -/
theorem MemoryChain.exists_standardMemory {E : Fin (n + 1) → Type u}
    [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)] (c : MemoryChain I O E) :
    ∃ (d : Fin (n + 1) → Nat) (c' : MemoryChain I O (fun j ↦ Memory.{u} (d j))),
      MatrixMap.choi c'.chainMap = MatrixMap.choi c.chainMap ∧
      (IsEmpty (E (Fin.last n)) → IsEmpty (Memory.{u} (d (Fin.last n)))) := by
  let d := fun j ↦ Fintype.card (E j)
  let e : ∀ j, E j ≃ Memory.{u} (d j) :=
    fun j ↦ (Fintype.equivFin (E j)).trans Equiv.ulift.symm
  refine ⟨d, c.reindexMemory e, c.choi_chainMap_reindexMemory e, ?_⟩
  intro h
  exact ⟨fun x ↦ h.false ((e _).symm x)⟩

/-- A normalized channel cannot have an empty output and an inhabited input. -/
theorem Normalized.isEmpty_input {J : CMatrix (Space I O)}
    (hJ : Normalized I O J) [IsEmpty (∀ j, O j)] : IsEmpty (∀ j, I j) := by
  refine ⟨fun i ↦ ?_⟩
  have h := congrFun (congrFun hJ.partialTraceB i) i
  simp [QIT.partialTraceB] at h

/-- Empty accumulated input is propagated to the incoming memory domain. -/
private theorem isEmpty_incoming {a M C : Type u}
    (hM : IsEmpty a → IsEmpty M) (h : IsEmpty (a × C)) : IsEmpty (M × C) := by
  cases isEmpty_or_nonempty a with
  | inl ha =>
    let := hM ha
    infer_instance
  | inr ha =>
    exact ⟨fun p ↦ h.false (Classical.choice ha, p.2)⟩

/-- The global channel's chosen Kraus amplitudes recover its normalized Choi. -/
theorem Normalized.kraus_choi {J : CMatrix (Space I O)} (hJ : Normalized I O J)
    (i i' : ∀ j, I j) (o o' : ∀ j, O j) :
    (∑ k, hJ.toChannel.kraus k o i * star (hJ.toChannel.kraus k o' i')) =
      J (i, o) (i', o') := by
  have h := (congrArg MatrixMap.choi hJ.toChannel.map_eq_ofKraus).symm.trans
    hJ.choi_toChannel
  simpa only [MatrixMap.choi_ofKraus, Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply]
    using congrFun (congrFun h (i, o)) (i', o')

section Step

variable {I O : Fin (n + 2) → Type u} {E : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- The padded final environment chosen by the induction step. -/
abbrev StepMemory (I O : Fin (n + 2) → Type u) (E : Fin (n + 1) → Type u) :=
  Space I O ⊕ (E (Fin.last n) × I (Fin.last (n + 1)))

/-- A normalized successor extends any predecessor realization satisfying
the empty-input invariant, and recovers the full operator exactly. -/
theorem exists_memory_step {J : CMatrix (Space I O)} (hJ : Normalized I O J)
    {K : CMatrix (Space (fun j : Fin (n + 1) ↦ I j.castSucc)
      (fun j ↦ O j.castSucc))}
    (htrace : ∀ (i i' : ∀ j, I j) (o o' : ∀ j : Fin (n + 1), O j.castSucc),
      (∑ z, J (i, Fin.snoc o z) (i', Fin.snoc o' z)) =
        if i (Fin.last (n + 1)) = i' (Fin.last (n + 1)) then
          K (Fin.init i, o) (Fin.init i', o') else 0)
    (c : MemoryChain (fun j ↦ I j.castSucc) (fun j ↦ O j.castSucc) E)
    (hc : MatrixMap.choi c.chainMap = K)
    (hE : IsEmpty (∀ j : Fin (n + 1), I j.castSucc) → IsEmpty (E (Fin.last n))) :
    ∃ V : ReferenceIsometry (E (Fin.last n) × I (Fin.last (n + 1)))
        (O (Fin.last (n + 1)) × StepMemory I O E),
      MatrixMap.choi (c.extend V).chainMap = J ∧
      (IsEmpty (∀ j, I j) → IsEmpty (StepMemory I O E)) := by
  classical
  let A : Matrix (Space (fun j : Fin (n + 1) ↦ I j.castSucc)
      (fun j ↦ O j.castSucc)) (E (Fin.last n)) ℂ := fun x m ↦ c.kraus m x.2 x.1
  let B : Matrix (Space (fun j : Fin (n + 1) ↦ I j.castSucc)
      (fun j ↦ O j.castSucc) × I (Fin.last (n + 1)))
      (O (Fin.last (n + 1)) × Space I O) ℂ :=
    fun x y ↦ hJ.toChannel.kraus y.2 (Fin.snoc x.1.2 y.1) (Fin.snoc x.1.1 x.2)
  have hin (h : IsEmpty (∀ j, I j)) : IsEmpty (E (Fin.last n) × I (Fin.last (n + 1))) :=
    isEmpty_incoming hE ⟨fun p ↦ h.false (Fin.snoc p.1 p.2)⟩
  have hdim (h : IsEmpty (O (Fin.last (n + 1)))) :
      IsEmpty (E (Fin.last n) × I (Fin.last (n + 1))) := by
    let : IsEmpty (∀ j, O j) := ⟨fun o ↦ h.false (o (Fin.last (n + 1)))⟩
    exact hin hJ.isEmpty_input
  have hGram : ∀ x y a b,
      (∑ d, ∑ k, B (x, a) (d, k) * star (B (y, b) (d, k))) =
        if a = b then ∑ m, A x m * star (A y m) else 0 := by
    intro x y a b
    simp only [B, hJ.kraus_choi]
    rw [htrace]
    simp only [Fin.snoc_last, Fin.init_snoc]
    rw [← hc]
    simp only [MemoryChain.choi_chainMap_apply, A]
  obtain ⟨V, hV⟩ := exists_padded_step_isometry A B hGram hdim
  refine ⟨V, ?_, ?_⟩
  · ext p q
    rcases p with ⟨i, o⟩
    rcases q with ⟨i', o'⟩
    rw [MemoryChain.choi_chainMap_apply,
      ← Equiv.sum_comp (Equiv.cast (snocFam_last E (StepMemory I O E))).symm]
    simp only [MemoryChain.kraus_extend]
    have hcast (e : StepMemory I O E) :
        cast (snocFam_last E (StepMemory I O E))
          ((Equiv.cast (snocFam_last E (StepMemory I O E))).symm e) = e :=
      (Equiv.cast _).apply_symm_apply _
    simp_rw [hcast]
    have hv (i : ∀ j, I j) (o : ∀ j, O j) (e : StepMemory I O E) :
        (∑ m, c.kraus m (Fin.init o) (Fin.init i) *
          V.matrix (o (Fin.last (n + 1)), e) (m, i (Fin.last (n + 1)))) =
          paddedAmplitude B ((Fin.init i, Fin.init o), i (Fin.last (n + 1)))
            (o (Fin.last (n + 1)), e) :=
      (hV (Fin.init i, Fin.init o) (i (Fin.last (n + 1)))
        (o (Fin.last (n + 1))) e).symm
    simp_rw [hv]
    simpa only [paddedAmplitude, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      B, Fin.snoc_init_self, star_zero, mul_zero, Finset.sum_const_zero, add_zero] using
        hJ.kraus_choi i i' o o'
  · intro h
    let : IsEmpty (Space I O) := ⟨fun p ↦ h.false p.1⟩
    let := hin h
    infer_instance

end Step

/-- Evaluation is the configuration equivalence for a single heterogeneous wire. -/
def oneConfigEquiv (W : Fin 1 → Type u) : (∀ j, W j) ≃ W 0 where
  toFun w := w 0
  invFun z j := (Fin.fin_one_eq_zero j).symm ▸ z
  left_inv w := by
    funext j
    have hj := Fin.fin_one_eq_zero j
    subst j
    rfl
  right_inv _ := rfl

/-- A single normalized tooth is realized by its ordinary Stinespring dilation. -/
theorem exists_memory_one {I O : Fin 1 → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {J : CMatrix (Space I O)} (hJ : Normalized I O J) :
    ∃ (d : Fin 1 → Nat) (c : MemoryChain I O (fun j ↦ Memory.{u} (d j))),
      MatrixMap.choi c.chainMap = J ∧
      (IsEmpty (∀ j, I j) → IsEmpty (Memory.{u} (d 0))) := by
  let N := hJ.toChannel
  let V := MemoryChain.linkCongr N.krausStinespring (oneConfigEquiv I)
    (Equiv.prodCongr (oneConfigEquiv O) (Equiv.refl (Space I O)))
  let c := MemoryChain.single V
  have hk (e : Space I O) (o : ∀ j, O j) (i : ∀ j, I j) : c.kraus e o i = N.kraus e o i := by
    rw [MemoryChain.kraus_one]
    change N.krausStinespring.matrix ((oneConfigEquiv O).symm (o 0), e)
      ((oneConfigEquiv I).symm (i 0)) = _
    rw [show (oneConfigEquiv O).symm (o 0) = o from (oneConfigEquiv O).symm_apply_apply o,
      show (oneConfigEquiv I).symm (i 0) = i from (oneConfigEquiv I).symm_apply_apply i]
    rfl
  have hc : MatrixMap.choi c.chainMap = J := by
    ext p q
    rw [MemoryChain.choi_chainMap_apply]
    simp_rw [hk]
    exact hJ.kraus_choi _ _ _ _
  obtain ⟨d, c', hcc, hempty⟩ := MemoryChain.exists_standardMemory c
  refine ⟨d, c', hcc.trans hc, ?_⟩
  intro h
  apply hempty
  exact ⟨fun p ↦ h.false p.1⟩

/-- The strengthened realization induction retains an empty terminal memory
whenever the accumulated input configuration is empty. -/
theorem Normalized.exists_memoryChain_with_empty {J : CMatrix (Space I O)}
    (hJ : Normalized I O J) :
    ∃ (d : Fin (n + 1) → Nat) (c : MemoryChain I O (fun j ↦ Memory.{u} (d j))),
      MatrixMap.choi c.chainMap = J ∧
      (IsEmpty (∀ j, I j) → IsEmpty (Memory.{u} (d (Fin.last n)))) := by
  classical
  induction n with
  | zero => exact exists_memory_one hJ
  | succ n ih =>
    obtain ⟨hpos, K, hK, ht⟩ := hJ
    obtain ⟨d, c, hc, he⟩ := ih hK
    obtain ⟨V, hV, hempty⟩ := exists_memory_step ⟨hpos, K, hK, ht⟩ ht c hc he
    obtain ⟨d', c', hcc, hstd⟩ := MemoryChain.exists_standardMemory (c.extend V)
    refine ⟨d', c', hcc.trans hV, ?_⟩
    intro h
    apply hstd
    exact ⟨fun e ↦ (hempty h).false (cast (snocFam_last _ _) e)⟩

/-- A positive-length comb is normalized exactly when it is the Choi operator
of a finite heterogeneous causal memory chain. All finite wires, including
empty wires, are allowed. The dimensions are existence witnesses, with no
minimality claim [Chiribella2009Networks, comblong-pub.tex:986-997]. -/
theorem normalized_iff_exists_memoryChain (J : CMatrix (Space I O)) :
    Normalized I O J ↔
      ∃ (d : Fin (n + 1) → Nat) (c : MemoryChain I O (fun j ↦ Memory.{u} (d j))),
        MatrixMap.choi c.chainMap = J := by
  constructor
  · intro h
    obtain ⟨d, c, hc, _⟩ := h.exists_memoryChain_with_empty
    exact ⟨d, c, hc⟩
  · rintro ⟨d, c, rfl⟩
    exact c.normalized

/-- Every normalized comb is exactly the Choi matrix of the memory channel
of its realizing chain [Chiribella2009Networks, comblong-pub.tex:1891-1892]. -/
theorem Normalized.exists_memoryChannel {J : CMatrix (Space I O)}
    (hJ : Normalized I O J) :
    ∃ (d : Fin (n + 1) → Nat) (c : MemoryChain I O (fun j ↦ Memory.{u} (d j))),
      MatrixMap.choi c.channel.map = J :=
  (normalized_iff_exists_memoryChain J).mp hJ

/-- A single fixed outer memory chain realizes an independently admissible
map on every joint normalized input, for every independent pair of finite
boundary systems. The outer chain is chosen before either boundary system or
input. Each connected channel is the physical alternating composition, and
its Choi matrix is exactly the existing ancillary action
[Chiribella2009Networks, comblong-pub.tex:1924-1934]. -/
theorem IsDeterministicMap.exists_memoryChain {n : Nat} {I O : Fin (n + 2) → Type u}
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    {S : MatrixMap (Space (innerInput O) (innerOutput I)) (I 0 × O (Fin.last (n + 1)))}
    (hS : IsDeterministicMap I O S) :
    ∃ (d : Fin (n + 2) → Nat) (c : MemoryChain I O (fun j ↦ Memory.{u} (d j))),
      actionMap I O (MatrixMap.choi c.chainMap) = S ∧
      ∀ (r s : Type u) [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
        (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))),
        ExtendedNormalized (innerInput O) (innerOutput I) r s Y →
        ∃ (e : Fin (n + 1) → Nat)
          (w : MemoryChain (boundaryInput (innerInput O) r)
            (boundaryOutput (innerOutput I) s) (fun j ↦ Memory.{u} (e j))),
          w.jointChoi = Y ∧
          MatrixMap.choi (c.connectChannel w).map = ancillaryExtension S Y := by
  classical
  have hnorm := (isDeterministicMap_iff_normalized_choi I O S).mp hS
  obtain ⟨d, c, hc⟩ := (normalized_iff_exists_memoryChain _).mp hnorm
  have hcS : actionMap I O (MatrixMap.choi c.chainMap) = S := by
    apply MatrixMap.choi_inj
    rw [choi_actionMap, hc, WireFam.matReindex_matReindex_symm]
  refine ⟨d, c, hcS, ?_⟩
  intro r s _ _ _ _ Y hY
  obtain ⟨e, w, hw⟩ := (normalized_iff_exists_memoryChain _).mp hY
  have hWY : w.jointChoi = Y := by
    change WireFam.matReindex (boundaryEquiv (innerInput O) (innerOutput I) r s)
      (MatrixMap.choi w.chainMap) = Y
    rw [hw]
    ext p q
    simp [WireFam.matReindex_apply, Matrix.submatrix_apply]
  refine ⟨e, w, hWY, ?_⟩
  rw [MemoryChain.connectChannel_choi, hcS, hWY]

end QIT.HigherOrder.Comb
