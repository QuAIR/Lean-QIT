/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

public import QIT.HigherOrder.Tester.Instrument
public import QIT.HigherOrder.Comb.Realization
public import QIT.Measurements.Projective

/-!
# Physical realization of finite quantum testers

The final output records the outcome in an orthonormal basis. Its positive
block-diagonal Choi operator is normalized because its output trace is the
tester total. Deterministic comb realization then supplies a causal sequence
of isometries, with a scalar initial input and exactly one output basis vector
per outcome. This proves [Chiribella2009Networks, comblong-pub.tex:3453-3456]
using the operational Born rule
[Chiribella2009Networks, comblong-pub.tex:3422-3427] and deterministic network
realization [Chiribella2009Networks, comblong-pub.tex:986-997]. No inverse or
square-root factorization of the tester total is assumed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
universe u
namespace QIT.HigherOrder
namespace Tester
open QIT.WireFam

variable {n : Nat} (I O : Fin (n+1) → Type u) (ι : Type u)

/-- The original input wires remain the inner inputs of the readout comb. -/
def readoutInputEquiv (j : Fin (n+1)) :
    I j ≃ Comb.innerInput (boundaryOutput ι I) j :=
  Equiv.cast (by simp [boundaryOutput])

/-- Identify the original comb with the inner wires of its readout network. -/
def readoutInnerEquiv : Comb.Space I O ≃
    Comb.Space (Comb.innerInput (boundaryOutput ι I)) (Comb.innerOutput (paddedInput O)) :=
  Comb.spaceEquiv (readoutInputEquiv I ι) (innerOutputEquiv O)

/-- Remove the scalar initial wire and identify the final output with its outcome. -/
def readoutEndpointEquiv :
    (paddedInput O 0 × boundaryOutput ι I (Fin.last (n+1))) ≃ ι :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.cast (by simp [boundaryOutput]))).trans
    (Equiv.punitProd ι)

/-- The readout basis consists of the original comb basis and the outcome label. -/
def readoutSpaceEquiv : Comb.Space (paddedInput O) (boundaryOutput ι I) ≃
    Comb.Space I O × ι :=
  (Comb.actionEquiv _ _).trans
    (Equiv.prodCongr (readoutInnerEquiv I O ι).symm (readoutEndpointEquiv I O ι))

variable [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι] [DecidableEq ι]

/-- Transport an input comb to the readout network's actual inner wires. -/
def readoutInnerPad := matReindex (readoutInnerEquiv I O ι)

/-- Inner transport preserves the full deterministic normalization. -/
theorem normalized_readoutInnerPad_iff (R : CMatrix (Comb.Space I O)) :
    Comb.Normalized _ _ (readoutInnerPad I O ι R) ↔ Comb.Normalized I O R :=
  (Comb.Normalized.reindex_iff (readoutInputEquiv I ι) (innerOutputEquiv O) R).symm

/-- A positive family gives a positive flagged operator, including zero-dimensional blocks. -/
theorem blockDiagonal_posSemidef (P : ι → CMatrix (Comb.Space I O))
    (hP : ∀ i, (P i).PosSemidef) : (Matrix.blockDiagonal P).PosSemidef := by
  let B := Matrix.blockDiagonal (fun i => psdSqrt (P i))
  have h : B * B.conjTranspose = Matrix.blockDiagonal P := by
    dsimp [B]
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext i
    rw [(psdSqrt_isHermitian (P i)).eq, psdSqrt_mul_self_of_posSemidef (hP i)]
  rw [← h]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- The final measurement reads a rank-one orthonormal basis projector. -/
def readoutMeasurement : ProjectiveMeasurement ι ι where
  effects i := Matrix.single i i 1
  isHermitian i := (posSemidef_single i).isHermitian
  idempotent i := by simp
  orthogonal i j hij := Matrix.single_mul_single_of_ne (c := (1 : ℂ)) i i j hij 1
  sum_eq_one := (POVM.coordinate ι).sum_eq_one

/-- The actual network link action, with its scalar initial boundary removed. -/
def readoutMatrix
    (J : CMatrix (Comb.Space (paddedInput O) (boundaryOutput ι I)))
    (R : CMatrix (Comb.Space I O)) : CMatrix ι :=
  (Comb.linkAction (paddedInput O) (boundaryOutput ι I) J
    (readoutInnerPad I O ι R)).submatrix
      (readoutEndpointEquiv I O ι).symm (readoutEndpointEquiv I O ι).symm

omit [∀ j, DecidableEq (O j)] in
/-- The preparation input is one-dimensional. -/
theorem readout_initial_dimension : Fintype.card (paddedInput O 0) = 1 := by
  exact Fintype.card_unique

omit [∀ j, DecidableEq (I j)] [DecidableEq ι] in
/-- The measured output has exactly one dimension per outcome, with no extra flag. -/
theorem readout_final_dimension :
    Fintype.card (boundaryOutput ι I (Fin.last (n+1))) = Fintype.card ι := by
  exact Fintype.card_congr (Equiv.cast (by simp [boundaryOutput]))

/-- An isometry with a scalar input prepares its normalized column vector. -/
def preparationOfIsometry {A B : Type u} [Fintype A] [DecidableEq A] [Unique A]
    [Fintype B] [DecidableEq B] (V : ReferenceIsometry A B) : PureVector B where
  amp b := V.matrix b default
  trace_rankOne_eq_one := by
    change (∑ b, V.matrix b default * star (V.matrix b default)) = 1
    simpa using V.sum_mul_star default default

/-- The first isometry on the scalar input prepares a normalized pure vector
on the first emitted system and its memory. -/
def firstPreparation {E : Fin (n+2) → Type u}
    [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
    (c : MemoryChain (paddedInput O) (boundaryOutput ι I) E) :
    PureVector (boundaryOutput ι I 0 × E 0) := by
  letI : Unique (linkDom (paddedInput O) E 0) := by change Unique PUnit; infer_instance
  exact preparationOfIsometry (c.link 0)

end Tester

namespace QuantumTester
open Tester QIT.WireFam
variable {n : Nat} {I O : Fin (n+1) → Type u} {ι : Type u}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype ι] [DecidableEq ι]

/-- The positive Choi operator recording each tester outcome at the final output. -/
def readoutChoi (T : QuantumTester I O ι) :
    CMatrix (Comb.Space (paddedInput O) (boundaryOutput ι I)) :=
  matReindex (readoutSpaceEquiv I O ι).symm (Matrix.blockDiagonal T.operator)

/-- Positivity is proved branch by branch, without a rank assumption on the total. -/
theorem readoutChoi_posSemidef (T : QuantumTester I O ι) : T.readoutChoi.PosSemidef :=
  (matReindex_posSemidef_iff _ _).mpr
    (blockDiagonal_posSemidef I O ι T.operator T.operator_posSemidef)

/-- The complete complex action is diagonal in the outcome basis and reproduces
the original full-transpose Born pairing on every matrix input. -/
theorem readoutChoi_action (T : QuantumTester I O ι) (R : CMatrix (Comb.Space I O))
    (a b : paddedInput O 0 × boundaryOutput ι I (Fin.last (n+1))) :
    Comb.actionMap (paddedInput O) (boundaryOutput ι I) T.readoutChoi
      (readoutInnerPad I O ι R) a b =
      if readoutEndpointEquiv I O ι a = readoutEndpointEquiv I O ι b then
        pairing (T.operator (readoutEndpointEquiv I O ι a)) R else 0 := by
  change (∑ x, ∑ y, readoutInnerPad I O ι R x y *
    matReindex (Comb.actionEquiv _ _) T.readoutChoi (x,a) (y,b)) = _
  rw [← (readoutInnerEquiv I O ι).sum_comp]
  simp_rw [← (readoutInnerEquiv I O ι).sum_comp]
  by_cases h : readoutEndpointEquiv I O ι a = readoutEndpointEquiv I O ι b
  · simp [readoutInnerPad, readoutChoi, readoutSpaceEquiv, matReindex_apply,
      Matrix.blockDiagonal_apply, h, pairing, mul_comm]
  · simp [readoutInnerPad, readoutChoi, readoutSpaceEquiv, matReindex_apply,
      Matrix.blockDiagonal_apply, h]

/-- Tracing the classical output gives the original normalized tester total. -/
theorem readoutChoi_actionTrace (T : QuantumTester I O ι)
    (R : CMatrix (Comb.Space I O)) (a b : paddedInput O 0) :
    Comb.actionTrace T.readoutChoi (readoutInnerPad I O ι R) a b =
      pairing (∑ i, T.operator i) R := by
  change (∑ z, Comb.actionMap _ _ T.readoutChoi (readoutInnerPad I O ι R)
    (a,z) (b,z)) = _
  simp only [T.readoutChoi_action]
  have he (z : boundaryOutput ι I (Fin.last (n+1))) :
      readoutEndpointEquiv I O ι (a,z) = readoutEndpointEquiv I O ι (b,z) := by
    congr 1
  simp only [he, ite_true, pairing_sum_left]
  exact (Equiv.cast (by simp [boundaryOutput]) :
    boundaryOutput ι I (Fin.last (n+1)) ≃ ι).sum_comp
      (fun i => pairing (T.operator i) R)

/-- The flagged operator is an actual normalized deterministic comb. -/
theorem readoutChoi_normalized (T : QuantumTester I O ι) :
    Comb.Normalized (paddedInput O) (boundaryOutput ι I) T.readoutChoi := by
  apply Comb.normalized_of_actionTrace _ T.readoutChoi_posSemidef
  intro X hX
  let R := matReindex (readoutInnerEquiv I O ι).symm X
  have hpad : readoutInnerPad I O ι R = X := matReindex_matReindex_symm _ _
  have hR : Comb.Normalized I O R :=
    (normalized_readoutInnerPad_iff I O ι R).mp (hpad.symm ▸ hX)
  rw [← hpad]
  ext a b
  rw [T.readoutChoi_actionTrace, T.normalized.pairing_eq_one hR]
  simp [Matrix.one_apply, Subsingleton.elim a b]

/-- A fixed causal isometric network realizes all outcomes simultaneously.
The network is chosen before the input comb, whose link action is exactly the
diagonal classical Born distribution, including the full complex values. -/
theorem exists_readout_memoryChain (T : QuantumTester I O ι) :
    ∃ (d : Fin (n+2) → Nat)
      (c : MemoryChain (paddedInput O) (boundaryOutput ι I)
        (fun j => Comb.Memory.{u} (d j))),
      MatrixMap.choi c.chainMap = T.readoutChoi ∧
      ∀ (R : CMatrix (Comb.Space I O))
        (a b : paddedInput O 0 × boundaryOutput ι I (Fin.last (n+1))),
        Comb.linkAction (paddedInput O) (boundaryOutput ι I)
          (MatrixMap.choi c.chainMap) (readoutInnerPad I O ι R) a b =
          if readoutEndpointEquiv I O ι a = readoutEndpointEquiv I O ι b then
            pairing (T.operator (readoutEndpointEquiv I O ι a)) R else 0 := by
  obtain ⟨d, c, hc⟩ := (Comb.normalized_iff_exists_memoryChain _).mp T.readoutChoi_normalized
  refine ⟨d, c, hc, ?_⟩
  intro R a b
  rw [hc, ← Comb.actionMap_eq_linkAction]
  exact T.readoutChoi_action R a b

/-- The readout matrix has exactly the source's diagonal Born entries. -/
theorem readoutMatrix_apply (T : QuantumTester I O ι)
    (R : CMatrix (Comb.Space I O)) (i j : ι) :
    readoutMatrix I O ι T.readoutChoi R i j =
      if i = j then pairing (T.operator i) R else 0 := by
  unfold readoutMatrix
  rw [Matrix.submatrix_apply, ← Comb.actionMap_eq_linkAction, T.readoutChoi_action]
  simp only [Equiv.apply_symm_apply]

/-- The output of the fixed readout network on any deterministic input is a state. -/
def readoutState (T : QuantumTester I O ι) (R : DeterministicComb I O) : State ι where
  matrix := readoutMatrix I O ι T.readoutChoi R.choi
  pos := by
    apply Matrix.PosSemidef.submatrix
    apply Comb.linkAction_posSemidef _ _ _ _ T.readoutChoi_posSemidef
    exact (matReindex_posSemidef_iff _ _).mpr R.posSemidef
  trace_eq_one := by
    change (∑ i, readoutMatrix I O ι T.readoutChoi R.choi i i) = 1
    simp only [T.readoutMatrix_apply, ite_true]
    rw [← pairing_sum_left]
    exact T.normalized.pairing_eq_one R.normalized

/-- The final von Neumann measurement recovers the full complex Born trace. -/
theorem readoutState_measurement (T : QuantumTester I O ι) (R : DeterministicComb I O)
    (i : ι) :
    Matrix.trace ((T.readoutState R).matrix * (readoutMeasurement ι).effects i) =
      Matrix.trace ((T.operator i).transpose * R.choi) := by
  change Matrix.trace (readoutMatrix I O ι T.readoutChoi R.choi * Matrix.single i i 1) = _
  rw [Matrix.trace_mul_single, T.readoutMatrix_apply]
  simp only [ite_true, MulOpposite.op_one, one_smul, pairing_eq_trace]

/-- Ordinary measurement probabilities agree with the tester probabilities. -/
theorem readoutState_probability (T : QuantumTester I O ι) (R : DeterministicComb I O)
    (i : ι) :
    ((readoutMeasurement ι).toPOVM.prob (T.readoutState R) i : ℝ) =
      T.probability i R := by
  rw [POVM.prob_eq_trace_re]
  exact congrArg Complex.re (T.readoutState_measurement R i)

/-- Every finite quantum tester has a single physical realization: a causal
isometric memory chain with one-dimensional initial input, a pure initial
preparation, and an outcome-dimensional final projective measurement. The
same chain works for every deterministic input and preserves each complex
Born probability [Chiribella2009Networks, comblong-pub.tex:3453-3456]. -/
theorem exists_physical_realization (T : QuantumTester I O ι) :
    ∃ (d : Fin (n+2) → Nat)
      (c : MemoryChain (paddedInput O) (boundaryOutput ι I)
        (fun j => Comb.Memory.{u} (d j)))
      (ψ : PureVector (boundaryOutput ι I 0 × Comb.Memory.{u} (d 0))),
      MatrixMap.choi c.chainMap = T.readoutChoi ∧
      (∀ z, ψ.amp z = (c.link 0).matrix z PUnit.unit) ∧
      ∀ R : DeterministicComb I O, ∃ ρ : State ι,
        ρ.matrix = readoutMatrix I O ι (MatrixMap.choi c.chainMap) R.choi ∧
        ∀ i, Matrix.trace (ρ.matrix * (readoutMeasurement ι).effects i) =
          Matrix.trace ((T.operator i).transpose * R.choi) := by
  obtain ⟨d, c, hc, _⟩ := T.exists_readout_memoryChain
  refine ⟨d, c, firstPreparation I O ι c, hc, fun _ => rfl, ?_⟩
  intro R
  refine ⟨T.readoutState R, ?_, T.readoutState_measurement R⟩
  rw [hc]
  rfl

end QuantumTester
end QIT.HigherOrder
