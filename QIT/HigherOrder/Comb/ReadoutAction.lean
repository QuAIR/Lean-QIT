/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Comb.MemoryReadout

/-!
# Linear contraction of a measured memory network

The fixed terminal flag of a memory network defines an action by contracting
its actual coherent Kraus amplitudes with the input operator. This agrees with
the source link action on every matrix, and with explicit contraction of every
finite Kraus family, including families without trace normalization.
The latter statement asserts completely positive linear action; arbitrary
rescalings of an input are not claimed to be trace-nonincreasing operations.
No causal realizability is assumed for those arbitrary Kraus families.
Actual alternating isometries for admissible inputs are supplied separately
by the connected instrument theorems in `MemoryReadout`.

The source instrument formula is
[Chiribella2009Networks, comblong-pub.tex:3302-3314], using the final projective
extraction at lines 1213-1216 and the shared-wire link convention at lines
315-327. Independent finite ancillary systems are retained throughout.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u v w x y z
namespace QIT.HigherOrder
open Comb

variable {n : Nat} {I O E : Fin (n + 1) → Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
  {K : Type v} {ι : Type w}
  [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
  {r : Type x} {s : Type y}
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Contract an arbitrary joint input operator against the coherent amplitudes
of a fixed flag outcome. The unobserved terminal memory is summed incoherently;
each inner wire is contracted coherently before taking the Gram product. -/
def MemoryChain.readoutAction (c : MemoryChain I O E)
    (e : E (Fin.last n) ≃ K × ι) (i : ι)
    (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))) :
    CMatrix ((I 0 × r) × (O (Fin.last n) × s)) :=
  fun p q =>
    ∑ a : Space (innerInput O) (innerOutput I),
      ∑ b : Space (innerInput O) (innerOutput I),
        Y ((a.1, p.1.2), (a.2, p.2.2)) ((b.1, q.1.2), (b.2, q.2.2)) *
          ∑ k : K,
            c.kraus (e.symm (k, i)) (Fin.snoc a.1 p.2.1) (Fin.cons p.1.1 a.2) *
              star (c.kraus (e.symm (k, i)) (Fin.snoc b.1 q.2.1) (Fin.cons q.1.1 b.2))

/-- The actual memory-amplitude contraction is the complete ancillary link
action of the measured branch, on every input matrix. -/
theorem MemoryChain.readoutAction_eq_ancillaryExtension (c : MemoryChain I O E)
    (e : E (Fin.last n) ≃ K × ι) (i : ι)
    (Y : CMatrix (((∀ j, innerInput O j) × r) × ((∀ j, innerOutput I j) × s))) :
    c.readoutAction e i Y =
      ancillaryExtension
        (actionMap I O (MatrixMap.choi ((c.readoutInstrument e).branch i))) Y := by
  ext p q
  change _ = ∑ a : Space (innerInput O) (innerOutput I),
    ∑ b : Space (innerInput O) (innerOutput I),
      Y ((a.1, p.1.2), (a.2, p.2.2)) ((b.1, q.1.2), (b.2, q.2.2)) *
        MatrixMap.choi ((c.readoutInstrument e).branch i)
          (Fin.cons p.1.1 a.2, Fin.snoc a.1 p.2.1)
          (Fin.cons q.1.1 b.2, Fin.snoc b.1 q.2.1)
  simp only [MemoryChain.readoutAction, MemoryChain.choi_readoutInstrument]

set_option backward.isDefEq.respectTransparency false in
/-- With trivial spectators the same amplitude contraction is the repository's
shared-wire link product, including its partial-transpose convention. -/
theorem MemoryChain.readoutAction_eq_linkAction (c : MemoryChain I O E)
    (e : E (Fin.last n) ≃ K × ι) (i : ι)
    (Y : CMatrix (Space (innerInput O) (innerOutput I))) :
    (c.readoutAction e i
      (fun p q : ((∀ j, innerInput O j) × PUnit) ×
        ((∀ j, innerOutput I j) × PUnit) => Y (p.1.1, p.2.1) (q.1.1, q.2.1))).submatrix
      (fun p => ((p.1, PUnit.unit), (p.2, PUnit.unit)))
      (fun p => ((p.1, PUnit.unit), (p.2, PUnit.unit))) =
        linkAction I O (MatrixMap.choi ((c.readoutInstrument e).branch i)) Y := by
  rw [MemoryChain.readoutAction_eq_ancillaryExtension, ← actionMap_eq_linkAction]
  rfl

variable {κ : Type z} [Fintype κ]

/-- Contract each input Kraus operator through the actual memory network,
fixing the final observed flag and retaining the residual memory as a Kraus
index. No normalization is imposed on the input Kraus family. -/
def MemoryChain.readoutContractKraus (c : MemoryChain I O E)
    (e : E (Fin.last n) ≃ K × ι)
    (L : κ → Matrix ((∀ j, innerOutput I j) × s) ((∀ j, innerInput O j) × r) ℂ)
    (i : ι) (t : K × κ) : Matrix (O (Fin.last n) × s) (I 0 × r) ℂ :=
  fun p q => ∑ a : Space (innerInput O) (innerOutput I),
    c.kraus (e.symm (t.1, i)) (Fin.snoc a.1 p.1) (Fin.cons q.1 a.2) *
      L t.2 (a.2, p.2) (a.1, q.2)

private theorem sum_exchange_pairs {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (Finset.univ : Finset (A × B)))
      (t := (Finset.univ : Finset (C × D)))
      (f := fun p q => f p.1 p.2 q.1 q.2))

omit [DecidableEq K] [Fintype ι] [DecidableEq ι] in
/-- Contracting an arbitrary Kraus family and then forming its Choi operator
agrees with the all-matrix amplitude contraction. -/
theorem MemoryChain.choi_readoutContractKraus (c : MemoryChain I O E)
    (e : E (Fin.last n) ≃ K × ι)
    (L : κ → Matrix ((∀ j, innerOutput I j) × s) ((∀ j, innerInput O j) × r) ℂ)
    (i : ι) :
    MatrixMap.choi (MatrixMap.ofKraus (c.readoutContractKraus e L i)) =
      c.readoutAction e i (MatrixMap.choi (MatrixMap.ofKraus L)) := by
  rw [MatrixMap.choi_ofKraus]
  ext p q
  simp only [Matrix.sum_apply, Matrix.vecMulVec]
  rw [Fintype.sum_prod_type]
  simp only [MemoryChain.readoutContractKraus,
    star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  change _ = ∑ a : Space (innerInput O) (innerOutput I),
    ∑ b : Space (innerInput O) (innerOutput I),
      MatrixMap.choi (MatrixMap.ofKraus L)
        ((a.1, p.1.2), (a.2, p.2.2)) ((b.1, q.1.2), (b.2, q.2.2)) *
        ∑ k : K,
          c.kraus (e.symm (k, i)) (Fin.snoc a.1 p.2.1) (Fin.cons p.1.1 a.2) *
            star (c.kraus (e.symm (k, i)) (Fin.snoc b.1 q.2.1) (Fin.cons q.1.1 b.2))
  rw [MatrixMap.choi_ofKraus]
  simp only [Matrix.sum_apply, Matrix.vecMulVec, Finset.sum_mul, Finset.mul_sum]
  rw [sum_exchange_pairs]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.sum_congr rfl fun k _ => by
    simp only [Matrix.of_apply]
    ring

/-- The explicit Kraus contraction of every finite input Kraus family is
the complete ancillary action prescribed by the measured branch Choi operator. -/
theorem MemoryChain.choi_readoutContractKraus_eq_ancillaryExtension
    (c : MemoryChain I O E) (e : E (Fin.last n) ≃ K × ι)
    (L : κ → Matrix ((∀ j, innerOutput I j) × s) ((∀ j, innerInput O j) × r) ℂ)
    (i : ι) :
    MatrixMap.choi (MatrixMap.ofKraus (c.readoutContractKraus e L i)) =
      ancillaryExtension
        (actionMap I O (MatrixMap.choi ((c.readoutInstrument e).branch i)))
        (MatrixMap.choi (MatrixMap.ofKraus L)) := by
  rw [MemoryChain.choi_readoutContractKraus,
    MemoryChain.readoutAction_eq_ancillaryExtension]

/-- Equality also holds as a linear map on arbitrary quantum input operators,
not just at the level of the resulting Choi matrices. -/
theorem MemoryChain.readoutContractMap_eq_ancillaryAction
    (c : MemoryChain I O E) (e : E (Fin.last n) ≃ K × ι)
    (L : κ → Matrix ((∀ j, innerOutput I j) × s) ((∀ j, innerInput O j) × r) ℂ)
    (i : ι) :
    MatrixMap.ofKraus (c.readoutContractKraus e L i) =
      ancillaryAction
        (actionMap I O (MatrixMap.choi ((c.readoutInstrument e).branch i)))
        (MatrixMap.ofKraus L) := by
  apply MatrixMap.choi_inj
  rw [choi_ancillaryAction, MemoryChain.choi_readoutContractKraus_eq_ancillaryExtension]

end QIT.HigherOrder
