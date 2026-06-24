/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.SymmetricSubspace
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Unitary Haar twirling on finite tensor powers

This module provides the finite-dimensional unitary Haar averaging support
needed by Renner's Schur-projection step
[Renner2007Symmetry, sub.tex:733-747].

The scope is deliberately narrow: unitary groups of finite matrix algebras,
their normalized Haar measure, tensor-power unitary actions, and the twirl
operator used by the de Finetti proof route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

local instance unitaryTwirlCMatrixContinuousENorm {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

namespace Matrix

/-- The Borel measurable structure on finite complex matrix spaces, using the
L2-operator norm topology. -/
noncomputable instance cMatrixMeasurableSpace :
    MeasurableSpace (Matrix a a ℂ) :=
  borel (Matrix a a ℂ)

/-- The Borel-space witness for finite complex matrix spaces. -/
instance cMatrixBorelSpace :
    BorelSpace (Matrix a a ℂ) :=
  ⟨rfl⟩

/-- Finite complex matrix spaces are locally compact in the L2-operator norm. -/
instance cMatrixLocallyCompactSpace :
    LocallyCompactSpace (Matrix a a ℂ) :=
  locallyCompact_of_proper

private theorem unitaryGroup_mem_cstar_unitary {U : Matrix a a ℂ}
    (hU : U ∈ Matrix.unitaryGroup a ℂ) :
    U ∈ unitary (Matrix a a ℂ) := by
  exact ⟨Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.mem_unitaryGroup_iff.mp hU⟩

private theorem unitaryGroup_isClosed :
    IsClosed ({U : Matrix a a ℂ | U ∈ Matrix.unitaryGroup a ℂ}) := by
  have hset :
      ({U : Matrix a a ℂ | U ∈ Matrix.unitaryGroup a ℂ}) =
        {U | U * star U = 1} := by
    ext U
    exact Matrix.mem_unitaryGroup_iff
  rw [hset]
  exact isClosed_eq (by fun_prop) continuous_const

private theorem unitaryGroup_isBounded [Nonempty a] :
    Bornology.IsBounded ({U : Matrix a a ℂ | U ∈ Matrix.unitaryGroup a ℂ}) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  intro U hU
  rw [CStarRing.norm_of_mem_unitary (unitaryGroup_mem_cstar_unitary hU)]

/-- The finite-dimensional matrix unitary group is compact. -/
theorem unitaryGroup_isCompact [Nonempty a] :
    IsCompact ({U : Matrix a a ℂ | U ∈ Matrix.unitaryGroup a ℂ}) :=
  Metric.isCompact_of_isClosed_isBounded unitaryGroup_isClosed unitaryGroup_isBounded

/-- Compact-space instance for finite-dimensional matrix unitary groups. -/
instance unitaryGroupCompactSpace [Nonempty a] :
    CompactSpace (Matrix.unitaryGroup a ℂ) :=
  isCompact_iff_compactSpace.mp unitaryGroup_isCompact

/-- Local-compactness instance inherited from compactness. -/
instance unitaryGroupLocallyCompactSpace [Nonempty a] :
    LocallyCompactSpace (Matrix.unitaryGroup a ℂ) :=
  inferInstance

/-- Inversion on the matrix unitary group is continuous, because it is matrix
adjoint on the ambient finite matrix space. -/
instance unitaryGroupContinuousInv :
    ContinuousInv (Matrix.unitaryGroup a ℂ) where
  continuous_inv := by
    rw [continuous_induced_rng]
    change Continuous
      (fun U : Matrix.unitaryGroup a ℂ =>
        ((U⁻¹ : Matrix.unitaryGroup a ℂ) : Matrix a a ℂ))
    have h :
        (fun U : Matrix.unitaryGroup a ℂ =>
          ((U⁻¹ : Matrix.unitaryGroup a ℂ) : Matrix a a ℂ)) =
          fun U : Matrix.unitaryGroup a ℂ => star (U : Matrix a a ℂ) := by
      funext U
      rfl
    rw [h]
    exact continuous_star.comp continuous_subtype_val

/-- Topological-group instance for finite-dimensional matrix unitary groups. -/
instance unitaryGroupTopologicalGroup :
    IsTopologicalGroup (Matrix.unitaryGroup a ℂ) where

end Matrix

/-- The normalized Haar measure on the finite-dimensional unitary group.  We
choose the Haar measure normalized on the compact set `univ`, so the total
mass is one. -/
def unitaryHaarMeasure [Nonempty a] : Measure (Matrix.unitaryGroup a ℂ) :=
  MeasureTheory.Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup a ℂ))

theorem unitaryHaarMeasure_univ [Nonempty a] :
    unitaryHaarMeasure (a := a) Set.univ = 1 := by
  simpa [unitaryHaarMeasure] using
    (MeasureTheory.Measure.haarMeasure_self
      (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup a ℂ))))

instance unitaryHaarMeasure_isProbabilityMeasure [Nonempty a] :
    IsProbabilityMeasure (unitaryHaarMeasure (a := a)) :=
  ⟨unitaryHaarMeasure_univ (a := a)⟩

instance unitaryHaarMeasure_isMulLeftInvariant [Nonempty a] :
    MeasureTheory.Measure.IsMulLeftInvariant (unitaryHaarMeasure (a := a)) := by
  dsimp [unitaryHaarMeasure]
  infer_instance

/-- Tensor power of a one-copy unitary under the repository's recursive
`TensorPower` convention. -/
def unitaryTensorPowerMatrix (U : Matrix.unitaryGroup a ℂ) :
    (n : ℕ) → Matrix.unitaryGroup (TensorPower a n) ℂ
  | 0 => 1
  | n + 1 =>
      let Un := unitaryTensorPowerMatrix U n
      ⟨Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)),
        Matrix.kronecker_mem_unitary U.2 Un.2⟩

@[simp]
theorem unitaryTensorPowerMatrix_zero (U : Matrix.unitaryGroup a ℂ) :
    unitaryTensorPowerMatrix U 0 = 1 := rfl

theorem unitaryTensorPowerMatrix_succ (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    unitaryTensorPowerMatrix U (n + 1) =
      ⟨Matrix.kronecker (U : CMatrix a)
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)),
        Matrix.kronecker_mem_unitary U.2 (unitaryTensorPowerMatrix U n).2⟩ := rfl

@[simp]
theorem unitaryTensorPowerMatrix_mul (U V : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    unitaryTensorPowerMatrix (U * V) n =
      unitaryTensorPowerMatrix U n * unitaryTensorPowerMatrix V n := by
  induction n with
  | zero =>
      simp [unitaryTensorPowerMatrix]
  | succ n ih =>
      apply Subtype.ext
      change Matrix.kronecker ((U * V : Matrix.unitaryGroup a ℂ) : CMatrix a)
            (unitaryTensorPowerMatrix (U * V) n : CMatrix (TensorPower a n)) =
        ((Matrix.kronecker (U : CMatrix a)
              (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))) *
          (Matrix.kronecker (V : CMatrix a)
              (unitaryTensorPowerMatrix V n : CMatrix (TensorPower a n))))
      rw [ih]
      simpa using
        (Matrix.mul_kronecker_mul (U : CMatrix a) (V : CMatrix a)
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
          (unitaryTensorPowerMatrix V n : CMatrix (TensorPower a n)))

@[simp]
theorem unitaryTensorPowerMatrix_one (n : ℕ) :
    unitaryTensorPowerMatrix (a := a) 1 n = 1 := by
  let X : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    unitaryTensorPowerMatrix (a := a) 1 n
  have hX : X = X * X := by
    simpa [X] using
      (unitaryTensorPowerMatrix_mul (a := a) (1 : Matrix.unitaryGroup a ℂ) 1 n)
  calc
    X = X⁻¹ * (X * X) := by simp
    _ = X⁻¹ * X := by rw [← hX]
    _ = 1 := by simp

@[simp]
theorem unitaryTensorPowerMatrix_inv (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    unitaryTensorPowerMatrix U⁻¹ n = (unitaryTensorPowerMatrix U n)⁻¹ := by
  apply Eq.symm
  exact inv_eq_of_mul_eq_one_left (by simp [← unitaryTensorPowerMatrix_mul])

theorem unitaryTensorPowerMatrix_conjTranspose (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)).conjTranspose =
      (unitaryTensorPowerMatrix U⁻¹ n : CMatrix (TensorPower a n)) := by
  rw [← Matrix.star_eq_conjTranspose, unitaryTensorPowerMatrix_inv]
  rfl

theorem unitaryTensorPowerMatrix_star_mul_self (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) =
      1 := by
  exact Matrix.UnitaryGroup.star_mul_self (unitaryTensorPowerMatrix U n)

theorem unitaryTensorPowerMatrix_apply_eq_fin_prod (U : Matrix.unitaryGroup a ℂ) :
    ∀ (n : ℕ) (x y : TensorPower a n),
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) x y =
        ∏ i : Fin n, (U : CMatrix a)
          ((tensorPowerEquiv n x) i) ((tensorPowerEquiv n y) i)
  | 0, x, y => by
      cases x
      cases y
      rfl
  | n + 1, (x0, xs), (y0, ys) => by
      change (U : CMatrix a) x0 y0 *
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) xs ys =
        ∏ i : Fin (n + 1), (U : CMatrix a)
          ((tensorPowerEquiv (n + 1) (x0, xs)) i)
          ((tensorPowerEquiv (n + 1) (y0, ys)) i)
      rw [unitaryTensorPowerMatrix_apply_eq_fin_prod U n xs ys, Fin.prod_univ_succ]
      simp

theorem unitaryTensorPowerMatrix_permEquiv_apply (U : Matrix.unitaryGroup a ℂ)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x y : TensorPower a n) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
        ((permEquiv (a := a) n σ) x) y =
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
        x ((permEquiv (a := a) n σ.symm) y) := by
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod,
    unitaryTensorPowerMatrix_apply_eq_fin_prod]
  rw [tensorPowerEquiv_permEquiv]
  rw [tensorPowerEquiv_permEquiv]
  simp only [Equiv.Perm.inv_def]
  let e : Fin n ≃ Fin n := σ.symm
  have h := Fintype.prod_equiv e
    (fun i : Fin n => (U : CMatrix a)
      ((tensorPowerEquiv n x) (σ⁻¹ i)) ((tensorPowerEquiv n y) i))
    (fun i : Fin n => (U : CMatrix a)
      ((tensorPowerEquiv n x) i) ((tensorPowerEquiv n y) (σ i))) ?_
  · simpa [e] using h
  intro i
  simp [e]

theorem permutationMatrix_mul_unitaryTensorPowerMatrix
    (U : Matrix.unitaryGroup a ℂ) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permutationMatrix (a := a) n σ *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) =
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
        permutationMatrix (a := a) n σ := by
  ext x y
  calc
    (permutationMatrix (a := a) n σ *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))) x y
        = (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
            ((permEquiv (a := a) n σ) x) y := by
          simp [Matrix.mul_apply, permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix]
    _ = (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
          x ((permEquiv (a := a) n σ.symm) y) := by
          rw [unitaryTensorPowerMatrix_permEquiv_apply]
    _ = ((unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
          permutationMatrix (a := a) n σ) x y := by
          simp only [Matrix.mul_apply, permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix]
          rw [Finset.sum_eq_single ((permEquiv (a := a) n σ).symm y)]
          · simp
          · intro b _ hb
            simp
            intro hby
            exact False.elim
              (hb ((Equiv.apply_eq_iff_eq_symm_apply
                (permEquiv (a := a) n σ)).mp hby))
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ _))

theorem symmetricProjectionMatrix_mul_unitaryTensorPowerMatrix
    (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    symmetricProjectionMatrix (a := a) n *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) =
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
        symmetricProjectionMatrix (a := a) n := by
  calc
    symmetricProjectionMatrix (a := a) n *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
        = (((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ) *
              (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
          rw [symmetricProjectionMatrix_eq_perm_average]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n),
            permutationMatrix (a := a) n σ *
              (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
          rw [Matrix.smul_mul, Matrix.sum_mul]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n),
            (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
              permutationMatrix (a := a) n σ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro σ _
          rw [permutationMatrix_mul_unitaryTensorPowerMatrix]
    _ = (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
          (((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ) := by
          rw [Matrix.mul_smul, Matrix.mul_sum]
    _ = (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
          symmetricProjectionMatrix (a := a) n := by
          rw [symmetricProjectionMatrix_eq_perm_average]

theorem unitaryTensorPowerMatrix_mul_symmetricProjectionMatrix
    (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
        symmetricProjectionMatrix (a := a) n =
      symmetricProjectionMatrix (a := a) n *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  rw [symmetricProjectionMatrix_mul_unitaryTensorPowerMatrix]

/-- A diagonal unitary with prescribed unit-modulus diagonal entries. -/
def diagonalPhaseUnitary (phase : a → ℂ)
    (hphase : ∀ z, phase z * star (phase z) = 1) :
    Matrix.unitaryGroup a ℂ :=
  ⟨Matrix.diagonal phase, by
    rw [Matrix.mem_unitaryGroup_iff]
    calc
      Matrix.diagonal phase * star (Matrix.diagonal phase)
          = Matrix.diagonal phase * Matrix.diagonal (fun i => star (phase i)) := by
              congr
              ext i j
              by_cases hij : i = j
              · subst j
                simp [Matrix.diagonal]
              · have hji : ¬ j = i := fun h => hij h.symm
                simp [Matrix.diagonal, hij, hji]
      _ = Matrix.diagonal (fun i => phase i * star (phase i)) := by
              rw [Matrix.diagonal_mul_diagonal]
      _ = 1 := by
              ext i j
              by_cases hij : i = j
              · subst j
                simpa [Matrix.diagonal] using hphase i
              · simp [Matrix.diagonal, hij]⟩

@[simp]
theorem diagonalPhaseUnitary_apply (phase : a → ℂ)
    (hphase : ∀ z, phase z * star (phase z) = 1) (i j : a) :
    (diagonalPhaseUnitary (a := a) phase hphase : CMatrix a) i j =
      if i = j then phase i else 0 := by
  by_cases hij : i = j <;> simp [diagonalPhaseUnitary, Matrix.diagonal, hij]

/-- The character by which a diagonal phase unitary acts on the profile vector
indexed by `p`. -/
def profilePhaseCharacter (phase : a → ℂ) {n : ℕ}
    (p : TensorPowerProfile a n) : ℂ :=
  ∏ z : a, phase z ^ p.1 z

@[simp]
theorem profilePhaseCharacter_zero (phase : a → ℂ)
    (p : TensorPowerProfile a 0) :
    profilePhaseCharacter (a := a) phase p = 1 := by
  unfold profilePhaseCharacter
  have hzero : p.1 = fun _ : a => 0 := by
    funext z
    exact Nat.eq_zero_of_le_zero (by simpa using TensorPowerProfile.coord_le_length (a := a) p z)
  simp [hzero]

theorem profilePhaseCharacter_diagonal_single_root
    (ω : ℂ) {n : ℕ} (p : TensorPowerProfile a n) (z : a) :
    profilePhaseCharacter (a := a) (fun w => if w = z then ω else 1) p =
      ω ^ p.1 z := by
  classical
  unfold profilePhaseCharacter
  rw [Finset.prod_eq_single z]
  · simp
  · intro w _ hwz
    simp [hwz]
  · intro hz
    exfalso
    exact hz (Finset.mem_univ z)

private theorem circle_mul_star_self (z : Circle) :
    (z : ℂ) * star (z : ℂ) = 1 := by
  have h : (Complex.normSq (z : ℂ) : ℂ) = star (z : ℂ) * (z : ℂ) :=
    Complex.normSq_eq_conj_mul_self
  rw [Circle.normSq_coe] at h
  have h' : star (z : ℂ) * (z : ℂ) = 1 := by
    simpa [Complex.star_def] using h.symm
  rw [mul_comm]
  exact h'

private theorem stdAddChar_mul_star_self (N : ℕ) [NeZero N] (j : ZMod N) :
    ZMod.stdAddChar j * star (ZMod.stdAddChar j) = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact circle_mul_star_self (ZMod.toCircle j)

private theorem stdAddChar_pow_ne_of_lt
    {N r s : ℕ} [NeZero N] (hr : r < N) (hs : s < N) (hrs : r ≠ s) :
    ZMod.stdAddChar (1 : ZMod N) ^ r ≠ ZMod.stdAddChar (1 : ZMod N) ^ s := by
  intro h
  have hmap : ZMod.stdAddChar ((r : ZMod N)) = ZMod.stdAddChar ((s : ZMod N)) := by
    rw [← AddChar.map_nsmul_eq_pow ZMod.stdAddChar r (1 : ZMod N),
      ← AddChar.map_nsmul_eq_pow ZMod.stdAddChar s (1 : ZMod N)] at h
    simpa using h
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply] at hmap
  have hcircle : ZMod.toCircle ((r : ZMod N)) = ZMod.toCircle ((s : ZMod N)) :=
    Circle.coe_injective hmap
  have hz : (r : ZMod N) = (s : ZMod N) := ZMod.injective_toCircle hcircle
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hr, ZMod.val_natCast_of_lt hs] at hval
  exact hrs hval

theorem profilePhaseCharacter_separates
    {n : ℕ} {p q : TensorPowerProfile a n} (hpq : p ≠ q) :
    ∃ phase : a → ℂ, (∀ z, phase z * star (phase z) = 1) ∧
      profilePhaseCharacter (a := a) phase p ≠
        profilePhaseCharacter (a := a) phase q := by
  classical
  have hprofile : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  obtain ⟨z, hz⟩ : ∃ z : a, p.1 z ≠ q.1 z := by
    by_contra h
    apply hprofile
    funext z
    by_contra hz
    exact h ⟨z, hz⟩
  let root : ℂ := ZMod.stdAddChar (1 : ZMod (n + 1))
  refine ⟨fun w => if w = z then root else 1, ?_, ?_⟩
  · intro w
    by_cases hw : w = z
    · subst w
      simpa [root] using stdAddChar_mul_star_self (n + 1) (1 : ZMod (n + 1))
    · simp [hw]
  · rw [profilePhaseCharacter_diagonal_single_root, profilePhaseCharacter_diagonal_single_root]
    exact stdAddChar_pow_ne_of_lt
      (N := n + 1) (r := p.1 z) (s := q.1 z)
      (Nat.lt_succ_of_le (TensorPowerProfile.coord_le_length (a := a) p z))
      (Nat.lt_succ_of_le (TensorPowerProfile.coord_le_length (a := a) q z))
      hz

/-- Tensor-word phase accumulated by a diagonal phase unitary. -/
def tensorWordPhase (phase : a → ℂ) :
    (n : ℕ) → TensorPower a n → ℂ
  | 0, _ => 1
  | n + 1, x => phase x.1 * tensorWordPhase phase n x.2

@[simp]
theorem tensorWordPhase_zero (phase : a → ℂ) (x : TensorPower a 0) :
    tensorWordPhase (a := a) phase 0 x = 1 := by
  cases x
  rfl

@[simp]
theorem tensorWordPhase_succ (phase : a → ℂ) (n : ℕ)
    (x : TensorPower a (n + 1)) :
    tensorWordPhase (a := a) phase (n + 1) x =
      phase x.1 * tensorWordPhase (a := a) phase n x.2 := rfl

/-- Matrix entries of a tensor-power diagonal phase unitary are diagonal, with
the accumulated phase on each tensor word. -/
theorem unitaryTensorPowerMatrix_diagonalPhase_apply (phase : a → ℂ)
    (hphase : ∀ z, phase z * star (phase z) = 1) :
    ∀ (n : ℕ) (x y : TensorPower a n),
      (unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
          CMatrix (TensorPower a n)) x y =
        if x = y then tensorWordPhase (a := a) phase n x else 0
  | 0, x, y => by
      cases x
      cases y
      rfl
  | n + 1, x, y => by
      cases x with
      | mk x0 xs =>
      cases y with
      | mk y0 ys =>
      simp only [unitaryTensorPowerMatrix_succ]
      change (Matrix.kronecker
          (diagonalPhaseUnitary (a := a) phase hphase : CMatrix a)
          (unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
            CMatrix (TensorPower a n))) (x0, xs) (y0, ys) =
        if (x0, xs) = (y0, ys) then
          tensorWordPhase (a := a) phase (n + 1) (x0, xs) else 0
      change (diagonalPhaseUnitary (a := a) phase hphase : CMatrix a) x0 y0 *
          (unitaryTensorPowerMatrix
            (diagonalPhaseUnitary (a := a) phase hphase) n :
              CMatrix (TensorPower a n)) xs ys =
        if (x0, xs) = (y0, ys) then
          tensorWordPhase (a := a) phase (n + 1) (x0, xs) else 0
      rw [unitaryTensorPowerMatrix_diagonalPhase_apply phase hphase n xs ys]
      by_cases h0 : x0 = y0
      · subst y0
        by_cases hs : xs = ys
        · subst ys
          simp [tensorWordPhase]
        · simp [diagonalPhaseUnitary_apply, hs]
      · have hpair : (x0, xs) ≠ (y0, ys) := by
          intro h
          exact h0 (Prod.mk.inj h).1
        simp [diagonalPhaseUnitary_apply, h0, hpair]

/-- Recursive tensor-word phases agree with the product over tensor positions. -/
theorem tensorWordPhase_eq_fin_prod (phase : a → ℂ) :
    ∀ (n : ℕ) (x : TensorPower a n),
      tensorWordPhase (a := a) phase n x =
        ∏ i : Fin n, phase ((tensorPowerEquiv n x) i)
  | 0, x => by
      cases x
      simp [tensorWordPhase]
  | n + 1, x => by
      cases x with
      | mk x0 xs =>
      rw [tensorWordPhase_succ, tensorWordPhase_eq_fin_prod phase n xs,
        Fin.prod_univ_succ]
      simp

/-- Tensor-word phases depend only on the realized profile. -/
theorem tensorWordPhase_eq_profilePhaseCharacter_of_typeProfile
    (phase : a → ℂ) {n : ℕ} (p : TensorPowerProfile a n)
    {x : TensorPower a n} (hx : tensorPowerTypeProfile (a := a) n x = p.1) :
    tensorWordPhase (a := a) phase n x =
      profilePhaseCharacter (a := a) phase p := by
  rw [tensorWordPhase_eq_fin_prod]
  unfold profilePhaseCharacter
  rw [← Finset.prod_fiberwise'
    (g := fun i : Fin n => (tensorPowerEquiv n x) i) (f := phase)]
  congr
  ext z
  rw [Finset.prod_const]
  congr
  have hcount :
      Fintype.card {i // tensorPowerEquiv n x i = z} = p.1 z := by
    simpa [tensorPowerTypeProfile] using congrFun hx z
  simpa [Fintype.card_subtype] using hcount

/-- Tensor-word phases are profile-character phases on a profile class. -/
theorem tensorWordPhase_eq_profilePhaseCharacter_of_mem_class
    (phase : a → ℂ) {n : ℕ} (p : TensorPowerProfile a n)
    {x : TensorPower a n} (hx : x ∈ tensorPowerProfileClass (a := a) p) :
    tensorWordPhase (a := a) phase n x =
      profilePhaseCharacter (a := a) phase p :=
  tensorWordPhase_eq_profilePhaseCharacter_of_typeProfile (a := a) phase p
    ((mem_tensorPowerProfileClass (a := a) p x).mp hx)

/-- A diagonal phase unitary acts on a normalized profile vector by the
corresponding profile character. -/
theorem diagonalPhaseUnitary_tensorPower_mulVec_profileUnitVector
    (phase : a → ℂ) (hphase : ∀ z, phase z * star (phase z) = 1)
    {n : ℕ} (p : TensorPowerProfile a n) :
    (unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
        CMatrix (TensorPower a n)).mulVec
      (tensorPowerProfileUnitVector (a := a) p) =
        profilePhaseCharacter (a := a) phase p •
          tensorPowerProfileUnitVector (a := a) p := by
  ext x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
  rw [Finset.sum_eq_single x]
  · rw [unitaryTensorPowerMatrix_diagonalPhase_apply]
    by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
    · rw [if_pos rfl]
      rw [tensorWordPhase_eq_profilePhaseCharacter_of_mem_class (a := a) phase p hx]
      ring
    · simp [tensorPowerProfileUnitVector, hx]
  · intro y _ hyx
    have hxy : x ≠ y := fun h => hyx h.symm
    rw [unitaryTensorPowerMatrix_diagonalPhase_apply]
    simp [hxy]
  · intro hx
    simp at hx

/-- Matrix coefficient in the Hilbert-normalized profile-vector basis. -/
noncomputable def profileMatrixCoeff {n : ℕ}
    (B : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) : ℂ :=
  dotProduct (star (tensorPowerProfileUnitVector (a := a) p))
    (B.mulVec (tensorPowerProfileUnitVector (a := a) q))

/-- Matrix coefficient in the normalized profile-vector basis.  This is a
semantically named alias used for transition coefficients of explicit
unitaries. -/
noncomputable def profileVectorCoeff {n : ℕ}
    (M : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) : ℂ :=
  profileMatrixCoeff (a := a) M p q

@[simp]
theorem profileVectorCoeff_eq_profileMatrixCoeff {n : ℕ}
    (M : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) :
    profileVectorCoeff (a := a) M p q = profileMatrixCoeff (a := a) M p q := rfl

@[simp]
theorem profileVectorCoeff_one {n : ℕ} (p q : TensorPowerProfile a n) :
    profileVectorCoeff (a := a) (1 : CMatrix (TensorPower a n)) p q =
      if p = q then 1 else 0 := by
  unfold profileVectorCoeff profileMatrixCoeff
  simpa [Matrix.mulVec, dotProduct, Matrix.one_apply] using
    tensorPowerProfileUnitVector_inner (a := a) p q

private theorem diagonalPhase_conj_apply
    (phase : a → ℂ) (hphase : ∀ z, phase z * star (phase z) = 1)
    {n : ℕ} (B : CMatrix (TensorPower a n)) (x y : TensorPower a n) :
    (((unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
          CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
          CMatrix (TensorPower a n))) x y) =
      tensorWordPhase (a := a) phase n x * B x y *
        star (tensorWordPhase (a := a) phase n y) := by
  classical
  let U : CMatrix (TensorPower a n) :=
    (unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
      CMatrix (TensorPower a n))
  change ((U * B * star U) x y) =
      tensorWordPhase (a := a) phase n x * B x y *
        star (tensorWordPhase (a := a) phase n y)
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single y]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single x]
    · have hUx : U x x = tensorWordPhase (a := a) phase n x := by
        dsimp [U]
        rw [unitaryTensorPowerMatrix_diagonalPhase_apply]
        simp
      have hUy : star U y y = star (tensorWordPhase (a := a) phase n y) := by
        rw [Matrix.star_apply]
        congr 1
        dsimp [U]
        rw [unitaryTensorPowerMatrix_diagonalPhase_apply]
        simp
      simp [hUx, hUy, mul_assoc]
    · intro z _ hzx
      have hxz : x ≠ z := fun h => hzx h.symm
      have hU : U x z = 0 := by
        dsimp [U]
        rw [unitaryTensorPowerMatrix_diagonalPhase_apply]
        simp [hxz]
      simp [hU]
    · intro hx
      simp at hx
  · intro z _ hzy
    have hyz : y ≠ z := fun h => hzy h.symm
    have hU : star U z y = 0 := by
      rw [Matrix.star_apply]
      have hdiag : U y z = 0 := by
        dsimp [U]
        rw [unitaryTensorPowerMatrix_diagonalPhase_apply]
        simp [hyz]
      simp [hdiag]
    simp [hU]
  · intro hy
    simp at hy

private theorem profileUnitVector_star_left_phase_mul
    (phase : a → ℂ) {n : ℕ} (p : TensorPowerProfile a n) (x : TensorPower a n) :
    star (tensorPowerProfileUnitVector (a := a) p x) *
        tensorWordPhase (a := a) phase n x =
      star (tensorPowerProfileUnitVector (a := a) p x) *
        profilePhaseCharacter (a := a) phase p := by
  classical
  by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
  · rw [tensorWordPhase_eq_profilePhaseCharacter_of_mem_class (a := a) phase p hx]
  · simp [tensorPowerProfileUnitVector, hx]

private theorem profileUnitVector_starPhase_mul
    (phase : a → ℂ) {n : ℕ} (p : TensorPowerProfile a n) (x : TensorPower a n) :
    star (tensorWordPhase (a := a) phase n x) *
        tensorPowerProfileUnitVector (a := a) p x =
      star (profilePhaseCharacter (a := a) phase p) *
        tensorPowerProfileUnitVector (a := a) p x := by
  classical
  by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
  · rw [tensorWordPhase_eq_profilePhaseCharacter_of_mem_class (a := a) phase p hx]
  · simp [tensorPowerProfileUnitVector, hx]

private theorem profileMatrixCoeff_diagonal_conj
    (phase : a → ℂ) (hphase : ∀ z, phase z * star (phase z) = 1)
    {n : ℕ} (B : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) :
    profileMatrixCoeff
      ((unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
          CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix (diagonalPhaseUnitary (a := a) phase hphase) n :
          CMatrix (TensorPower a n))) p q =
      profilePhaseCharacter (a := a) phase p *
        star (profilePhaseCharacter (a := a) phase q) * profileMatrixCoeff B p q := by
  classical
  unfold profileMatrixCoeff
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [diagonalPhase_conj_apply]
  calc
    ∑ x, star (tensorPowerProfileUnitVector p x) *
        ∑ y, (tensorWordPhase phase n x * B x y *
            star (tensorWordPhase phase n y)) * tensorPowerProfileUnitVector q y
        = ∑ x, ∑ y,
            (star (tensorPowerProfileUnitVector p x) * tensorWordPhase phase n x) *
              B x y * (star (tensorWordPhase phase n y) *
                tensorPowerProfileUnitVector q y) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ x, ∑ y,
            (star (tensorPowerProfileUnitVector p x) * profilePhaseCharacter phase p) *
              B x y * (star (profilePhaseCharacter phase q) *
                tensorPowerProfileUnitVector q y) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          rw [profileUnitVector_star_left_phase_mul (a := a) phase p x,
            profileUnitVector_starPhase_mul (a := a) phase q y]
    _ = profilePhaseCharacter phase p * star (profilePhaseCharacter phase q) *
          ∑ x, star (tensorPowerProfileUnitVector p x) *
            ∑ y, B x y * tensorPowerProfileUnitVector q y := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          ring

private theorem profilePhaseCharacter_mul_star_self
    (phase : a → ℂ) (hphase : ∀ z, phase z * star (phase z) = 1)
    {n : ℕ} (p : TensorPowerProfile a n) :
    profilePhaseCharacter (a := a) phase p *
        star (profilePhaseCharacter (a := a) phase p) = 1 := by
  classical
  unfold profilePhaseCharacter
  change (∏ z, phase z ^ p.1 z) *
      (starRingEnd ℂ) (∏ z, phase z ^ p.1 z) = 1
  rw [map_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro z _
  rw [map_pow]
  rw [← mul_pow]
  have hz : phase z * (starRingEnd ℂ) (phase z) = 1 := by
    simpa using hphase z
  rw [hz]
  simp

private theorem profilePhaseCharacter_mul_star_ne_one_of_ne
    (phase : a → ℂ) (hphase : ∀ z, phase z * star (phase z) = 1)
    {n : ℕ} {p q : TensorPowerProfile a n}
    (hpq : profilePhaseCharacter (a := a) phase p ≠
      profilePhaseCharacter (a := a) phase q) :
    profilePhaseCharacter (a := a) phase p *
        star (profilePhaseCharacter (a := a) phase q) ≠ 1 := by
  intro h
  apply hpq
  calc
    profilePhaseCharacter (a := a) phase p
        = profilePhaseCharacter (a := a) phase p * 1 := by simp
    _ = profilePhaseCharacter (a := a) phase p *
          (star (profilePhaseCharacter (a := a) phase q) *
            profilePhaseCharacter (a := a) phase q) := by
            rw [mul_comm (star (profilePhaseCharacter (a := a) phase q)),
              profilePhaseCharacter_mul_star_self (a := a) phase hphase q]
    _ = (profilePhaseCharacter (a := a) phase p *
            star (profilePhaseCharacter (a := a) phase q)) *
              profilePhaseCharacter (a := a) phase q := by ring
    _ = profilePhaseCharacter (a := a) phase q := by
            rw [h]
            simp

theorem unitaryInvariant_profileMatrixCoeff_eq_zero_of_ne
    {n : ℕ} (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    {p q : TensorPowerProfile a n} (hpq : p ≠ q) :
    profileMatrixCoeff B p q = 0 := by
  classical
  obtain ⟨phase, hphase, hsep⟩ :=
    profilePhaseCharacter_separates (a := a) (n := n) (p := p) (q := q) hpq
  let factor :=
    profilePhaseCharacter (a := a) phase p *
      star (profilePhaseCharacter (a := a) phase q)
  have hcoeff := profileMatrixCoeff_diagonal_conj (a := a) phase hphase B p q
  rw [hinv (diagonalPhaseUnitary (a := a) phase hphase)] at hcoeff
  change profileMatrixCoeff B p q = factor * profileMatrixCoeff B p q at hcoeff
  have hfactor : factor ≠ 1 := by
    exact profilePhaseCharacter_mul_star_ne_one_of_ne (a := a) phase hphase hsep
  have hnonzero : 1 - factor ≠ 0 := by
    intro hzero
    apply hfactor
    exact (sub_eq_zero.mp hzero).symm
  have hmul : (1 - factor) * profileMatrixCoeff B p q = 0 := by
    rw [sub_mul, one_mul]
    rw [← hcoeff]
    ring
  exact (mul_eq_zero.mp hmul).resolve_left hnonzero

private theorem unitaryTensorPowerMatrix_mul_star_self (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) =
      1 := by
  simpa using Matrix.UnitaryGroup.star_mul_self (unitaryTensorPowerMatrix U n)⁻¹

theorem unitaryInvariant_commutes_unitaryTensorPowerMatrix
    {n : ℕ} (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B =
      B * (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  let Un : CMatrix (TensorPower a n) := unitaryTensorPowerMatrix U n
  have h := hinv U
  have hmul : (Un * B * star Un) * Un = B * Un := by
    rw [h]
  calc
    Un * B = Un * B * 1 := by simp
    _ = Un * B * (star Un * Un) := by
          rw [unitaryTensorPowerMatrix_star_mul_self (a := a) U n]
    _ = (Un * B * star Un) * Un := by simp [mul_assoc]
    _ = B * Un := hmul

theorem unitaryInvariant_compressed_commutes_unitaryTensorPowerMatrix
    {n : ℕ} (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
        (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n) =
      (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n) *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  let Un : CMatrix (TensorPower a n) := unitaryTensorPowerMatrix U n
  have hPB : Un * B = B * Un :=
    unitaryInvariant_commutes_unitaryTensorPowerMatrix (a := a) B hinv U
  have hPU : P * Un = Un * P := by
    simpa [P, Un] using symmetricProjectionMatrix_mul_unitaryTensorPowerMatrix (a := a) U n
  have hUP : Un * P = P * Un := by
    simpa [P, Un] using unitaryTensorPowerMatrix_mul_symmetricProjectionMatrix (a := a) U n
  calc
    Un * (P * B * P) = (Un * P) * B * P := by
      simp [Matrix.mul_assoc]
    _ = (P * Un) * B * P := by rw [hUP]
    _ = P * (Un * B) * P := by
      simp [Matrix.mul_assoc]
    _ = P * (B * Un) * P := by rw [hPB]
    _ = P * B * (Un * P) := by simp [Matrix.mul_assoc]
    _ = P * B * (P * Un) := by rw [hUP]
    _ = (P * B * P) * Un := by simp [Matrix.mul_assoc]

/-- Adjacent tensor-power profiles, oriented so that `q` is obtained from `p`
by moving one occurrence from coordinate `i` to coordinate `j`. -/
structure ProfileAdjacentMove {n : ℕ}
    (p q : TensorPowerProfile a n) (i j : a) : Prop where
  ne : i ≠ j
  source_pos : 0 < p.1 i
  coord_i : q.1 i = p.1 i - 1
  coord_j : q.1 j = p.1 j + 1
  coord_other : ∀ z : a, z ≠ i → z ≠ j → q.1 z = p.1 z

namespace ProfileAdjacentMove

theorem symm {n : ℕ} {p q : TensorPowerProfile a n} {i j : a}
    (h : ProfileAdjacentMove (a := a) p q i j) :
    ProfileAdjacentMove (a := a) q p j i where
  ne := h.ne.symm
  source_pos := by
    rw [h.coord_j]
    exact Nat.succ_pos _
  coord_i := by
    rw [h.coord_j]
    simp
  coord_j := by
    rw [h.coord_i]
    exact (Nat.sub_add_cancel h.source_pos).symm
  coord_other := by
    intro z hzj hzi
    exact (h.coord_other z hzi hzj).symm

end ProfileAdjacentMove

/-- Matrix entry for the real two-level rotation in the `i,j` coordinate
plane.  The public bundled unitary below uses the identity when `i = j`. -/
def twoLevelRotationEntry (i j : a) (θ : ℝ) (x y : a) : ℂ :=
  if x = i ∧ y = i then Complex.cos (θ : ℂ)
  else if x = i ∧ y = j then -Complex.sin (θ : ℂ)
  else if x = j ∧ y = i then Complex.sin (θ : ℂ)
  else if x = j ∧ y = j then Complex.cos (θ : ℂ)
  else if x = y then 1 else 0

/-- The matrix underlying a two-level real rotation. -/
def twoLevelRotationMatrix (i j : a) (θ : ℝ) : CMatrix a :=
  if i = j then 1 else Matrix.of (twoLevelRotationEntry i j θ)

private theorem twoLevelRotationEntry_row_i_support {i j : a} (hij : i ≠ j)
    (θ : ℝ) (k : a) (hki : k ≠ i) (hkj : k ≠ j) :
    twoLevelRotationEntry i j θ i k = 0 := by
  have hik : ¬ i = k := fun h => hki h.symm
  simp [twoLevelRotationEntry, hij, hki, hkj, hik]

private theorem twoLevelRotationEntry_row_j_support {i j : a} (hij : i ≠ j)
    (θ : ℝ) (k : a) (hki : k ≠ i) (hkj : k ≠ j) :
    twoLevelRotationEntry i j θ j k = 0 := by
  have hji : j ≠ i := fun h => hij h.symm
  have hjk : ¬ j = k := fun h => hkj h.symm
  simp [twoLevelRotationEntry, hji, hki, hkj, hjk]

private theorem twoLevelRotationEntry_row_other {i j : a} (θ : ℝ)
    {x k : a} (hxi : x ≠ i) (hxj : x ≠ j) :
    twoLevelRotationEntry i j θ x k = if x = k then 1 else 0 := by
  simp [twoLevelRotationEntry, hxi, hxj]

private theorem complex_cos_star_eq_self (θ : ℝ) :
    (starRingEnd ℂ) (Complex.cos (θ : ℂ)) = Complex.cos (θ : ℂ) := by
  rw [← Complex.cos_conj]
  simp

private theorem complex_sin_star_eq_self (θ : ℝ) :
    (starRingEnd ℂ) (Complex.sin (θ : ℂ)) = Complex.sin (θ : ℂ) := by
  rw [← Complex.sin_conj]
  simp

private theorem twoLevelRotationEntry_row_i_norm (i j : a) (hij : i ≠ j)
    (θ : ℝ) :
    (∑ k : a, twoLevelRotationEntry i j θ i k *
      star (twoLevelRotationEntry i j θ i k)) = 1 := by
  classical
  have hji : j ≠ i := fun h => hij h.symm
  let f : a → ℂ := fun k =>
    twoLevelRotationEntry i j θ i k * star (twoLevelRotationEntry i j θ i k)
  change (∑ k ∈ (Finset.univ : Finset a), f k) = 1
  rw [Finset.sum_eq_add_sum_diff_singleton i f (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton j f]
  · have hzero : ∑ x ∈ ((Finset.univ : Finset a).erase i).erase j, f x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      have hxi : x ≠ i := hx.2
      have hxj : x ≠ j := hx.1
      simp [f, twoLevelRotationEntry_row_i_support hij θ x hxi hxj]
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase]
    rw [hzero]
    simp [f, twoLevelRotationEntry, hji]
    rw [complex_cos_star_eq_self, complex_sin_star_eq_self]
    simpa [pow_two] using Complex.cos_sq_add_sin_sq (θ : ℂ)
  · intro hjnot
    exfalso
    simp [hji] at hjnot

private theorem twoLevelRotationEntry_row_j_norm (i j : a) (hij : i ≠ j)
    (θ : ℝ) :
    (∑ k : a, twoLevelRotationEntry i j θ j k *
      star (twoLevelRotationEntry i j θ j k)) = 1 := by
  classical
  have hji : j ≠ i := fun h => hij h.symm
  let f : a → ℂ := fun k =>
    twoLevelRotationEntry i j θ j k * star (twoLevelRotationEntry i j θ j k)
  change (∑ k ∈ (Finset.univ : Finset a), f k) = 1
  rw [Finset.sum_eq_add_sum_diff_singleton i f (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton j f]
  · have hzero : ∑ x ∈ ((Finset.univ : Finset a).erase i).erase j, f x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      have hxi : x ≠ i := hx.2
      have hxj : x ≠ j := hx.1
      simp [f, twoLevelRotationEntry_row_j_support hij θ x hxi hxj]
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase]
    rw [hzero]
    simp [f, twoLevelRotationEntry, hji]
    rw [complex_cos_star_eq_self, complex_sin_star_eq_self]
    simpa [pow_two, add_comm, add_left_comm, add_assoc] using
      Complex.cos_sq_add_sin_sq (θ : ℂ)
  · intro hjnot
    exfalso
    simp [hji] at hjnot

private theorem twoLevelRotationEntry_row_i_j_orthogonal (i j : a)
    (hij : i ≠ j) (θ : ℝ) :
    (∑ k : a, twoLevelRotationEntry i j θ i k *
      star (twoLevelRotationEntry i j θ j k)) = 0 := by
  classical
  have hji : j ≠ i := fun h => hij h.symm
  let f : a → ℂ := fun k =>
    twoLevelRotationEntry i j θ i k * star (twoLevelRotationEntry i j θ j k)
  change (∑ k ∈ (Finset.univ : Finset a), f k) = 0
  rw [Finset.sum_eq_add_sum_diff_singleton i f (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton j f]
  · have hzero : ∑ x ∈ ((Finset.univ : Finset a).erase i).erase j, f x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      have hxi : x ≠ i := hx.2
      have hxj : x ≠ j := hx.1
      simp [f, twoLevelRotationEntry_row_i_support hij θ x hxi hxj]
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase]
    rw [hzero]
    simp [f, twoLevelRotationEntry, hij, hji]
    rw [complex_cos_star_eq_self, complex_sin_star_eq_self]
    ring
  · intro hjnot
    exfalso
    simp [hji] at hjnot

private theorem twoLevelRotationEntry_row_j_i_orthogonal (i j : a)
    (hij : i ≠ j) (θ : ℝ) :
    (∑ k : a, twoLevelRotationEntry i j θ j k *
      star (twoLevelRotationEntry i j θ i k)) = 0 := by
  classical
  have hji : j ≠ i := fun h => hij h.symm
  let f : a → ℂ := fun k =>
    twoLevelRotationEntry i j θ j k * star (twoLevelRotationEntry i j θ i k)
  change (∑ k ∈ (Finset.univ : Finset a), f k) = 0
  rw [Finset.sum_eq_add_sum_diff_singleton i f (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton j f]
  · have hzero : ∑ x ∈ ((Finset.univ : Finset a).erase i).erase j, f x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      have hxi : x ≠ i := hx.2
      have hxj : x ≠ j := hx.1
      simp [f, twoLevelRotationEntry_row_j_support hij θ x hxi hxj]
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase]
    rw [hzero]
    simp [f, twoLevelRotationEntry, hji]
    rw [complex_cos_star_eq_self, complex_sin_star_eq_self]
    ring
  · intro hjnot
    exfalso
    simp [hji] at hjnot

private theorem twoLevelRotationEntry_row_i_other_orthogonal (i j : a)
    (hij : i ≠ j) (θ : ℝ) {y : a} (hyi : y ≠ i) (hyj : y ≠ j) :
    (∑ k : a, twoLevelRotationEntry i j θ i k *
      star (twoLevelRotationEntry i j θ y k)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k = i
  · subst k
    simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hyi hyj, hyi]
  · by_cases hkj : k = j
    · subst k
      simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hyi hyj, hyj]
    · simp [twoLevelRotationEntry_row_i_support hij θ k hki hkj]

private theorem twoLevelRotationEntry_row_j_other_orthogonal (i j : a)
    (hij : i ≠ j) (θ : ℝ) {y : a} (hyi : y ≠ i) (hyj : y ≠ j) :
    (∑ k : a, twoLevelRotationEntry i j θ j k *
      star (twoLevelRotationEntry i j θ y k)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k = i
  · subst k
    simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hyi hyj, hyi]
  · by_cases hkj : k = j
    · subst k
      simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hyi hyj, hyj]
    · simp [twoLevelRotationEntry_row_j_support hij θ k hki hkj]

private theorem twoLevelRotationEntry_row_other_i_orthogonal (i j : a)
    (hij : i ≠ j) (θ : ℝ) {x : a} (hxi : x ≠ i) (hxj : x ≠ j) :
    (∑ k : a, twoLevelRotationEntry i j θ x k *
      star (twoLevelRotationEntry i j θ i k)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k = i
  · subst k
    simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hxi hxj, hxi]
  · by_cases hkj : k = j
    · subst k
      simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hxi hxj, hxj]
    · simp [twoLevelRotationEntry_row_i_support hij θ k hki hkj]

private theorem twoLevelRotationEntry_row_other_j_orthogonal (i j : a)
    (hij : i ≠ j) (θ : ℝ) {x : a} (hxi : x ≠ i) (hxj : x ≠ j) :
    (∑ k : a, twoLevelRotationEntry i j θ x k *
      star (twoLevelRotationEntry i j θ j k)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k = i
  · subst k
    simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hxi hxj, hxi]
  · by_cases hkj : k = j
    · subst k
      simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hxi hxj, hxj]
    · simp [twoLevelRotationEntry_row_j_support hij θ k hki hkj]

private theorem twoLevelRotationEntry_row_other_inner (i j : a) (θ : ℝ)
    {x y : a} (hxi : x ≠ i) (hxj : x ≠ j) (hyi : y ≠ i) (hyj : y ≠ j) :
    (∑ k : a, twoLevelRotationEntry i j θ x k *
      star (twoLevelRotationEntry i j θ y k)) = if x = y then 1 else 0 := by
  classical
  simp [twoLevelRotationEntry_row_other (i := i) (j := j) θ hxi hxj,
    twoLevelRotationEntry_row_other (i := i) (j := j) θ hyi hyj]

private theorem twoLevelRotationEntry_row_inner (i j : a) (hij : i ≠ j)
    (θ : ℝ) (x y : a) :
    (∑ k : a, twoLevelRotationEntry i j θ x k *
      star (twoLevelRotationEntry i j θ y k)) = if x = y then 1 else 0 := by
  classical
  by_cases hxi : x = i
  · subst x
    by_cases hyi : y = i
    · subst y
      rw [twoLevelRotationEntry_row_i_norm (a := a) i j hij θ]
      simp
    · by_cases hyj : y = j
      · subst y
        rw [twoLevelRotationEntry_row_i_j_orthogonal (a := a) i j hij θ]
        simp [hij]
      · rw [twoLevelRotationEntry_row_i_other_orthogonal (a := a) i j hij θ
          (hyi := hyi) (hyj := hyj)]
        have hiy : ¬ i = y := fun h => hyi h.symm
        simp [hiy]
  · by_cases hxj : x = j
    · subst x
      by_cases hyi : y = i
      · subst y
        rw [twoLevelRotationEntry_row_j_i_orthogonal (a := a) i j hij θ]
        simp [hij.symm]
      · by_cases hyj : y = j
        · subst y
          rw [twoLevelRotationEntry_row_j_norm (a := a) i j hij θ]
          simp
        · rw [twoLevelRotationEntry_row_j_other_orthogonal (a := a) i j hij θ
            (hyi := hyi) (hyj := hyj)]
          have hjy : ¬ j = y := fun h => hyj h.symm
          simp [hjy]
    · by_cases hyi : y = i
      · subst y
        rw [twoLevelRotationEntry_row_other_i_orthogonal (a := a) i j hij θ
          (hxi := hxi) (hxj := hxj)]
        simp [hxi]
      · by_cases hyj : y = j
        · subst y
          rw [twoLevelRotationEntry_row_other_j_orthogonal (a := a) i j hij θ
            (hxi := hxi) (hxj := hxj)]
          simp [hxj]
        · exact twoLevelRotationEntry_row_other_inner (a := a) i j θ
            (hxi := hxi) (hxj := hxj) (hyi := hyi) (hyj := hyj)

theorem twoLevelRotationMatrix_mem_unitaryGroup (i j : a) (θ : ℝ) :
    twoLevelRotationMatrix (a := a) i j θ ∈ Matrix.unitaryGroup a ℂ := by
  classical
  unfold twoLevelRotationMatrix
  by_cases hij : i = j
  · simp [hij]
  rw [if_neg hij, Matrix.mem_unitaryGroup_iff]
  ext x y
  simp only [Matrix.mul_apply, Matrix.of_apply]
  simpa [Matrix.one_apply] using
    twoLevelRotationEntry_row_inner (a := a) i j hij θ x y

/-- The elementary two-level real rotation on the span of two basis states. -/
def twoLevelRotationUnitary (i j : a) (θ : ℝ) :
    Matrix.unitaryGroup a ℂ :=
  ⟨twoLevelRotationMatrix (a := a) i j θ,
    twoLevelRotationMatrix_mem_unitaryGroup (a := a) i j θ⟩

/-- The infinitesimal generator of the two-level rotation in the `i,j`
coordinate plane.  It is the derivative at `θ = 0` of
`twoLevelRotationMatrix i j θ`. -/
def twoLevelGeneratorEntry (i j : a) (x y : a) : ℂ :=
  if x = i ∧ y = j then -1
  else if x = j ∧ y = i then 1
  else 0

/-- The one-copy two-level infinitesimal generator. -/
def twoLevelGeneratorMatrix (i j : a) : CMatrix a :=
  if i = j then 0 else Matrix.of (twoLevelGeneratorEntry i j)

@[simp]
theorem twoLevelGeneratorMatrix_apply {i j x y : a} (hij : i ≠ j) :
    twoLevelGeneratorMatrix (a := a) i j x y =
      twoLevelGeneratorEntry i j x y := by
  simp [twoLevelGeneratorMatrix, hij]

@[simp]
theorem twoLevelGeneratorEntry_self_left (i j : a) :
    twoLevelGeneratorEntry i j i j = -1 := by
  by_cases hij : i = j
  · subst j
    simp [twoLevelGeneratorEntry]
  · simp [twoLevelGeneratorEntry, hij]

@[simp]
theorem twoLevelGeneratorEntry_self_right {i j : a} (hij : i ≠ j) :
    twoLevelGeneratorEntry i j j i = 1 := by
  simp [twoLevelGeneratorEntry, hij, hij.symm]

theorem twoLevelRotationEntry_hasDerivAt_zero {i j : a} (hij : i ≠ j) (x y : a) :
    HasDerivAt (fun θ : ℝ => twoLevelRotationEntry i j θ x y)
      (twoLevelGeneratorEntry i j x y) 0 := by
  unfold twoLevelRotationEntry twoLevelGeneratorEntry
  by_cases h1 : x = i ∧ y = i
  · rcases h1 with ⟨rfl, rfl⟩
    simp [hij]
    simpa using (Complex.hasDerivAt_cos (0 : ℂ)).comp_ofReal
  · by_cases h2 : x = i ∧ y = j
    · rcases h2 with ⟨rfl, rfl⟩
      simp [hij.symm]
      have hsin := (Complex.hasDerivAt_sin (0 : ℂ)).comp_ofReal
      simpa using hsin.neg
    · by_cases h3 : x = j ∧ y = i
      · rcases h3 with ⟨rfl, rfl⟩
        simp [hij, hij.symm]
        simpa using (Complex.hasDerivAt_sin (0 : ℂ)).comp_ofReal
      · by_cases h4 : x = j ∧ y = j
        · rcases h4 with ⟨rfl, rfl⟩
          simp [hij.symm]
          simpa using (Complex.hasDerivAt_cos (0 : ℂ)).comp_ofReal
        · by_cases h5 : x = y
          · have hyi : y ≠ i := by
              intro hyi
              exact h1 ⟨by simpa [h5, hyi], hyi⟩
            have hyj : y ≠ j := by
              intro hyj
              exact h4 ⟨by simpa [h5, hyj], hyj⟩
            simpa [hyi, hyj, h5] using
              hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℂ))
          · simpa [h1, h2, h3, h4, h5] using
              hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℂ))

theorem twoLevelRotationEntry_zero_apply {i j : a} (hij : i ≠ j) (x y : a) :
    twoLevelRotationEntry i j 0 x y = if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    by_cases hxi : x = i
    · subst x
      simp [twoLevelRotationEntry]
    · by_cases hxj : x = j
      · subst x
        simp [twoLevelRotationEntry, hij.symm]
      · simp [twoLevelRotationEntry, hxi, hxj]
  · have h1 : ¬ (x = i ∧ y = i) := by
      rintro ⟨rfl, rfl⟩
      exact hxy rfl
    have h4 : ¬ (x = j ∧ y = j) := by
      rintro ⟨rfl, rfl⟩
      exact hxy rfl
    simp [twoLevelRotationEntry, h1, h4, hxy]

private theorem twoLevelGeneratorEntry_ne_zero_cases {i j x y : a}
    (h : twoLevelGeneratorEntry i j x y ≠ 0) :
    (x = i ∧ y = j) ∨ (x = j ∧ y = i) := by
  classical
  unfold twoLevelGeneratorEntry at h
  by_cases hleft : x = i ∧ y = j
  · exact Or.inl hleft
  · by_cases hright : x = j ∧ y = i
    · exact Or.inr hright
    · simp [hleft, hright] at h

private theorem twoLevelGeneratorEntry_eq_neg_one_of_left {i j x y : a}
    (hxy : x = i ∧ y = j) :
    twoLevelGeneratorEntry i j x y = -1 := by
  rcases hxy with ⟨rfl, rfl⟩
  simp

private theorem twoLevelGeneratorEntry_eq_one_of_right {i j x y : a}
    (hij : i ≠ j) (hxy : x = j ∧ y = i) :
    twoLevelGeneratorEntry i j x y = 1 := by
  rcases hxy with ⟨rfl, rfl⟩
  exact twoLevelGeneratorEntry_self_right (a := a) hij

/-- The tensor-power infinitesimal generator induced by the two-level
one-copy generator.  It is written directly on tensor words: sum over the
single tensor coordinate where the generator acts. -/
def twoLevelTensorGeneratorMatrix (i j : a) (n : ℕ) : CMatrix (TensorPower a n) :=
  Matrix.of fun x y =>
    ∑ r : Fin n,
      (∏ s : Fin n, if s = r then (1 : ℂ)
        else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) *
      twoLevelGeneratorEntry i j
        (tensorPowerEquiv n x r) (tensorPowerEquiv n y r)

@[simp]
theorem twoLevelTensorGeneratorMatrix_zero (i j : a) :
    twoLevelTensorGeneratorMatrix (a := a) i j 0 = 0 := by
  ext x y
  simp [twoLevelTensorGeneratorMatrix]

theorem twoLevelTensorGeneratorMatrix_apply (i j : a) (n : ℕ)
    (x y : TensorPower a n) :
    twoLevelTensorGeneratorMatrix (a := a) i j n x y =
      ∑ r : Fin n,
        (∏ s : Fin n, if s = r then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) *
        twoLevelGeneratorEntry i j
          (tensorPowerEquiv n x r) (tensorPowerEquiv n y r) := rfl

theorem unitaryTensorPowerMatrix_twoLevelRotation_hasDerivAt_zero
    {i j : a} (hij : i ≠ j) (n : ℕ) (x y : TensorPower a n) :
    HasDerivAt
      (fun θ : ℝ =>
        (unitaryTensorPowerMatrix (twoLevelRotationUnitary (a := a) i j θ) n :
          CMatrix (TensorPower a n)) x y)
      (twoLevelTensorGeneratorMatrix (a := a) i j n x y) 0 := by
  have hentryFun :
      (fun θ : ℝ =>
        (unitaryTensorPowerMatrix (twoLevelRotationUnitary (a := a) i j θ) n :
          CMatrix (TensorPower a n)) x y) =
        (∏ r : Fin n, fun θ : ℝ =>
          (twoLevelRotationUnitary (a := a) i j θ : CMatrix a)
            ((tensorPowerEquiv n x) r) ((tensorPowerEquiv n y) r)) := by
    funext θ
    rw [unitaryTensorPowerMatrix_apply_eq_fin_prod]
    simp [Finset.prod_apply]
  rw [hentryFun]
  have hfun :
      (∏ r : Fin n, fun θ : ℝ =>
          (twoLevelRotationUnitary (a := a) i j θ : CMatrix a)
            ((tensorPowerEquiv n x) r) ((tensorPowerEquiv n y) r)) =
        (∏ r : Fin n, fun θ : ℝ =>
          twoLevelRotationEntry i j θ
            ((tensorPowerEquiv n x) r) ((tensorPowerEquiv n y) r)) := by
    refine Finset.prod_congr rfl ?_
    intro r _
    funext θ
    simp [twoLevelRotationUnitary, twoLevelRotationMatrix, hij]
  rw [hfun]
  have hderiv : HasDerivAt
      (∏ r : Fin n, fun θ : ℝ =>
        twoLevelRotationEntry i j θ
          ((tensorPowerEquiv n x) r) ((tensorPowerEquiv n y) r))
      (∑ r : Fin n,
        (∏ s ∈ (Finset.univ : Finset (Fin n)).erase r,
          twoLevelRotationEntry i j 0
            ((tensorPowerEquiv n x) s) ((tensorPowerEquiv n y) s)) *
          twoLevelGeneratorEntry i j
            ((tensorPowerEquiv n x) r) ((tensorPowerEquiv n y) r)) 0 := by
    simpa using HasDerivAt.finsetProd (u := (Finset.univ : Finset (Fin n)))
      (x := (0 : ℝ))
      (f := fun r θ => twoLevelRotationEntry i j θ
        ((tensorPowerEquiv n x) r) ((tensorPowerEquiv n y) r))
      (f' := fun r => twoLevelGeneratorEntry i j
        ((tensorPowerEquiv n x) r) ((tensorPowerEquiv n y) r))
      (by
        intro r _
        exact twoLevelRotationEntry_hasDerivAt_zero (a := a) hij _ _)
  rw [twoLevelTensorGeneratorMatrix_apply]
  convert hderiv using 1
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [← Finset.prod_erase (s := (Finset.univ : Finset (Fin n))) (a := r)]
  · congr 1
    refine Finset.prod_congr rfl ?_
    intro s hs
    have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
    simp [twoLevelRotationEntry_zero_apply (a := a) hij, hsr]
  · simp

theorem commutes_twoLevelTensorGeneratorMatrix_of_commutes_twoLevelRotation
    {i j : a} (hij : i ≠ j) (n : ℕ) (C : CMatrix (TensorPower a n))
    (hcommRot : ∀ θ : ℝ,
      (unitaryTensorPowerMatrix (twoLevelRotationUnitary (a := a) i j θ) n :
          CMatrix (TensorPower a n)) * C =
        C * (unitaryTensorPowerMatrix (twoLevelRotationUnitary (a := a) i j θ) n :
          CMatrix (TensorPower a n))) :
    twoLevelTensorGeneratorMatrix (a := a) i j n * C =
      C * twoLevelTensorGeneratorMatrix (a := a) i j n := by
  ext x y
  let G : CMatrix (TensorPower a n) := twoLevelTensorGeneratorMatrix (a := a) i j n
  let R : ℝ → CMatrix (TensorPower a n) := fun θ =>
    unitaryTensorPowerMatrix (twoLevelRotationUnitary (a := a) i j θ) n
  have hleft : HasDerivAt (fun θ : ℝ => (R θ * C) x y) ((G * C) x y) 0 := by
    simp only [Matrix.mul_apply]
    have hsum : HasDerivAt
        (∑ z : TensorPower a n, fun θ : ℝ => R θ x z * C z y)
        (∑ z : TensorPower a n, G x z * C z y) 0 := by
      exact HasDerivAt.sum (u := (Finset.univ : Finset (TensorPower a n))) (x := (0 : ℝ))
        (A := fun z θ => R θ x z * C z y)
        (A' := fun z => G x z * C z y)
        (by
          intro z _
          exact (unitaryTensorPowerMatrix_twoLevelRotation_hasDerivAt_zero
            (a := a) hij n x z).mul_const (C z y))
    have hfun : (fun θ : ℝ => ∑ z : TensorPower a n, R θ x z * C z y) =ᶠ[nhds (0 : ℝ)]
        (∑ z : TensorPower a n, fun θ : ℝ => R θ x z * C z y) := by
      filter_upwards with θ
      simp [Finset.sum_apply]
    simpa [G, R, Matrix.mul_apply] using hsum.congr_of_eventuallyEq hfun
  have hright : HasDerivAt (fun θ : ℝ => (C * R θ) x y) ((C * G) x y) 0 := by
    simp only [Matrix.mul_apply]
    have hsum : HasDerivAt
        (∑ z : TensorPower a n, fun θ : ℝ => C x z * R θ z y)
        (∑ z : TensorPower a n, C x z * G z y) 0 := by
      exact HasDerivAt.sum (u := (Finset.univ : Finset (TensorPower a n))) (x := (0 : ℝ))
        (A := fun z θ => C x z * R θ z y)
        (A' := fun z => C x z * G z y)
        (by
          intro z _
          exact (unitaryTensorPowerMatrix_twoLevelRotation_hasDerivAt_zero
            (a := a) hij n z y).const_mul (C x z))
    have hfun : (fun θ : ℝ => ∑ z : TensorPower a n, C x z * R θ z y) =ᶠ[nhds (0 : ℝ)]
        (∑ z : TensorPower a n, fun θ : ℝ => C x z * R θ z y) := by
      filter_upwards with θ
      simp [Finset.sum_apply]
    simpa [G, R, Matrix.mul_apply] using hsum.congr_of_eventuallyEq hfun
  have heq : (fun θ : ℝ => (R θ * C) x y) =ᶠ[nhds (0 : ℝ)]
      (fun θ : ℝ => (C * R θ) x y) := by
    filter_upwards with θ
    exact congrFun (congrFun (hcommRot θ) x) y
  have hright' : HasDerivAt (fun θ : ℝ => (R θ * C) x y) ((C * G) x y) 0 :=
    hright.congr_of_eventuallyEq heq
  exact hleft.unique hright'

theorem unitaryInvariant_compressed_commutes_twoLevelTensorGeneratorMatrix
    {n : ℕ} (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    {i j : a} (hij : i ≠ j) :
    twoLevelTensorGeneratorMatrix (a := a) i j n *
        (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n) =
      (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n) *
        twoLevelTensorGeneratorMatrix (a := a) i j n := by
  exact commutes_twoLevelTensorGeneratorMatrix_of_commutes_twoLevelRotation
    (a := a) hij n (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n)
    (by
      intro θ
      exact unitaryInvariant_compressed_commutes_unitaryTensorPowerMatrix
        (a := a) B hinv (twoLevelRotationUnitary (a := a) i j θ))

/-- Update one tensor coordinate in the `TensorPower a n ≃ (Fin n → a)`
coordinates and return to the recursive tensor-power representation. -/
def tensorPowerUpdate (n : ℕ) (x : TensorPower a n) (r : Fin n) (z : a) :
    TensorPower a n :=
  (tensorPowerEquiv (a := a) n).symm
    (Function.update (tensorPowerEquiv (a := a) n x) r z)

@[simp]
theorem tensorPowerEquiv_tensorPowerUpdate_self (n : ℕ)
    (x : TensorPower a n) (r : Fin n) (z : a) :
    tensorPowerEquiv (a := a) n (tensorPowerUpdate (a := a) n x r z) r = z := by
  simp [tensorPowerUpdate]

@[simp]
theorem tensorPowerEquiv_tensorPowerUpdate_of_ne (n : ℕ)
    (x : TensorPower a n) {r s : Fin n} (hrs : s ≠ r) (z : a) :
    tensorPowerEquiv (a := a) n (tensorPowerUpdate (a := a) n x r z) s =
      tensorPowerEquiv (a := a) n x s := by
  simp [tensorPowerUpdate, Function.update_of_ne hrs]

theorem twoLevelTensorGeneratorMatrix_apply_single_j_to_i {i j : a} (hij : i ≠ j)
    {n : ℕ} (x y : TensorPower a n) (r : Fin n)
    (hx : tensorPowerEquiv n x r = i)
    (hy : tensorPowerEquiv n y r = j)
    (hsame : ∀ s : Fin n, s ≠ r →
      tensorPowerEquiv n x s = tensorPowerEquiv n y s) :
    twoLevelTensorGeneratorMatrix (a := a) i j n x y = -1 := by
  classical
  rw [twoLevelTensorGeneratorMatrix_apply]
  rw [Finset.sum_eq_single r]
  · have hprod :
        (∏ s : Fin n, if s = r then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 1 := by
      apply Finset.prod_eq_one
      intro s _
      by_cases hsr : s = r
      · simp [hsr]
      · simp [hsr, hsame s hsr]
    rw [hprod, hx, hy]
    simp [twoLevelGeneratorEntry, hij]
  · intro t _ htr
    have hprod_zero :
        (∏ s : Fin n, if s = t then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      have hrt : ¬ r = t := fun h => htr h.symm
      have hxy_ne : tensorPowerEquiv n x r ≠ tensorPowerEquiv n y r := by
        rw [hx, hy]
        exact hij
      simp [hrt, hxy_ne]
    rw [hprod_zero]
    simp
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

theorem twoLevelTensorGeneratorMatrix_update_j_to_i {i j : a} (hij : i ≠ j)
    {n : ℕ} (y : TensorPower a n) (r : Fin n)
    (hy : tensorPowerEquiv (a := a) n y r = j) :
    twoLevelTensorGeneratorMatrix (a := a) i j n
        (tensorPowerUpdate (a := a) n y r i) y = -1 := by
  apply twoLevelTensorGeneratorMatrix_apply_single_j_to_i (a := a) hij
  · exact tensorPowerEquiv_tensorPowerUpdate_self (a := a) n y r i
  · exact hy
  · intro s hsr
    simp [tensorPowerEquiv_tensorPowerUpdate_of_ne (a := a) n y hsr i]

theorem twoLevelTensorGeneratorMatrix_apply_single_i_to_j {i j : a} (hij : i ≠ j)
    {n : ℕ} (x y : TensorPower a n) (r : Fin n)
    (hx : tensorPowerEquiv n x r = j)
    (hy : tensorPowerEquiv n y r = i)
    (hsame : ∀ s : Fin n, s ≠ r →
      tensorPowerEquiv n x s = tensorPowerEquiv n y s) :
    twoLevelTensorGeneratorMatrix (a := a) i j n x y = 1 := by
  classical
  rw [twoLevelTensorGeneratorMatrix_apply]
  rw [Finset.sum_eq_single r]
  · have hprod :
        (∏ s : Fin n, if s = r then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 1 := by
      apply Finset.prod_eq_one
      intro s _
      by_cases hsr : s = r
      · simp [hsr]
      · simp [hsr, hsame s hsr]
    rw [hprod, hx, hy]
    simp [twoLevelGeneratorEntry, hij, hij.symm]
  · intro t _ htr
    have hprod_zero :
        (∏ s : Fin n, if s = t then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      have hrt : ¬ r = t := fun h => htr h.symm
      have hxy_ne : tensorPowerEquiv n x r ≠ tensorPowerEquiv n y r := by
        rw [hx, hy]
        exact hij.symm
      simp [hrt, hxy_ne]
    rw [hprod_zero]
    simp
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

theorem twoLevelTensorGeneratorMatrix_update_i_to_j {i j : a} (hij : i ≠ j)
    {n : ℕ} (y : TensorPower a n) (r : Fin n)
    (hy : tensorPowerEquiv (a := a) n y r = i) :
    twoLevelTensorGeneratorMatrix (a := a) i j n
        (tensorPowerUpdate (a := a) n y r j) y = 1 := by
  apply twoLevelTensorGeneratorMatrix_apply_single_i_to_j (a := a) hij
  · exact tensorPowerEquiv_tensorPowerUpdate_self (a := a) n y r j
  · exact hy
  · intro s hsr
    simp [tensorPowerEquiv_tensorPowerUpdate_of_ne (a := a) n y hsr j]

private theorem fin_card_filter_update_eq_add_one
    {n : ℕ} (f : Fin n → a) (r : Fin n) {i j : a}
    (hij : i ≠ j) (hr : f r = j) :
    Fintype.card {s : Fin n // Function.update f r i s = i} =
      Fintype.card {s : Fin n // f s = i} + 1 := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  let S : Finset (Fin n) := Finset.univ.filter fun s => f s = i
  have hr_not_mem : r ∉ S := by
    simp [S, hr, hij.symm]
  have hset :
      (Finset.univ.filter fun s : Fin n => Function.update f r i s = i) =
        insert r S := by
    ext s
    constructor
    · intro hs
      by_cases hsr : s = r
      · subst s
        simp
      · apply Finset.mem_insert_of_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have hfi : f s = i := by
          simpa [Function.update_of_ne hsr] using hs
        simpa [S, hfi]
    · intro hs
      rcases Finset.mem_insert.mp hs with hsr | hsS
      · subst s
        simp
      · have hsr : s ≠ r := by
          intro h
          subst s
          exact hr_not_mem hsS
        have hfi : f s = i := by
          simpa [S] using hsS
        simpa [Function.update_of_ne hsr, hfi]
  rw [hset, Finset.card_insert_of_notMem hr_not_mem]

private theorem fin_card_filter_update_removed_add_one
    {n : ℕ} (f : Fin n → a) (r : Fin n) {i j : a}
    (hij : i ≠ j) (hr : f r = j) :
    Fintype.card {s : Fin n // Function.update f r i s = j} + 1 =
      Fintype.card {s : Fin n // f s = j} := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  let S : Finset (Fin n) := Finset.univ.filter fun s => Function.update f r i s = j
  have hr_not_mem : r ∉ S := by
    simp [S, hij]
  have hset :
      (Finset.univ.filter fun s : Fin n => f s = j) =
        insert r S := by
    ext s
    constructor
    · intro hs
      by_cases hsr : s = r
      · subst s
        simp
      · apply Finset.mem_insert_of_mem
        simpa [S, Function.update_of_ne hsr] using hs
    · intro hs
      rcases Finset.mem_insert.mp hs with hsr | hsS
      · subst s
        simpa [hr]
      · have hsr : s ≠ r := by
          intro h
          subst s
          exact hr_not_mem hsS
        have hupd : Function.update f r i s = j := by
          simpa [S] using hsS
        simpa [Function.update_of_ne hsr] using hupd
  rw [hset, Finset.card_insert_of_notMem hr_not_mem]

private theorem fin_card_filter_update_other
    {n : ℕ} (f : Fin n → a) (r : Fin n) {i j z : a}
    (hzi : z ≠ i) (hzj : z ≠ j) (hr : f r = j) :
    Fintype.card {s : Fin n // Function.update f r i s = z} =
      Fintype.card {s : Fin n // f s = z} := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hset :
      (Finset.univ.filter fun s : Fin n => Function.update f r i s = z) =
        Finset.univ.filter fun s : Fin n => f s = z := by
    ext s
    constructor
    · intro hs
      by_cases hsr : s = r
      · subst s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have hiz : i = z := by
          simpa using hs
        exact (hzi hiz.symm).elim
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        simpa [Function.update_of_ne hsr] using hs
    · intro hs
      by_cases hsr : s = r
      · subst s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have hjz : j = z := by
          simpa [hr] using hs
        exact (hzj hjz.symm).elim
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        simpa [Function.update_of_ne hsr] using hs
  rw [hset]

theorem tensorPowerTypeProfile_tensorPowerUpdate_same {n : ℕ}
    (y : TensorPower a n) (r : Fin n) {i j : a}
    (hij : i ≠ j) (hy : tensorPowerEquiv (a := a) n y r = j) :
    tensorPowerTypeProfile (a := a) n
        (tensorPowerUpdate (a := a) n y r i) i =
      tensorPowerTypeProfile (a := a) n y i + 1 := by
  unfold tensorPowerTypeProfile
  simpa [tensorPowerUpdate] using
    fin_card_filter_update_eq_add_one (a := a)
      (tensorPowerEquiv (a := a) n y) r hij hy

theorem tensorPowerTypeProfile_tensorPowerUpdate_removed {n : ℕ}
    (y : TensorPower a n) (r : Fin n) {i j : a}
    (hij : i ≠ j) (hy : tensorPowerEquiv (a := a) n y r = j) :
    tensorPowerTypeProfile (a := a) n
        (tensorPowerUpdate (a := a) n y r i) j + 1 =
      tensorPowerTypeProfile (a := a) n y j := by
  unfold tensorPowerTypeProfile
  simpa [tensorPowerUpdate] using
    fin_card_filter_update_removed_add_one (a := a)
      (tensorPowerEquiv (a := a) n y) r hij hy

theorem tensorPowerTypeProfile_tensorPowerUpdate_other {n : ℕ}
    (y : TensorPower a n) (r : Fin n) {i j z : a}
    (hzi : z ≠ i) (hzj : z ≠ j)
    (hy : tensorPowerEquiv (a := a) n y r = j) :
    tensorPowerTypeProfile (a := a) n
        (tensorPowerUpdate (a := a) n y r i) z =
      tensorPowerTypeProfile (a := a) n y z := by
  unfold tensorPowerTypeProfile
  simpa [tensorPowerUpdate] using
    fin_card_filter_update_other (a := a)
      (tensorPowerEquiv (a := a) n y) r hzi hzj hy

theorem exists_tensorPower_coordinate_eq_of_profile_pos {n : ℕ}
    {p : TensorPowerProfile a n} {y : TensorPower a n}
    (hy : y ∈ tensorPowerProfileClass (a := a) p)
    {z : a} (hz : 0 < p.1 z) :
    ∃ r : Fin n, tensorPowerEquiv (a := a) n y r = z := by
  have hprofile := (mem_tensorPowerProfileClass (a := a) p y).mp hy
  have hzProfile : 0 < tensorPowerTypeProfile (a := a) n y z := by
    rw [congrFun hprofile z]
    exact hz
  have hcard : 0 < Fintype.card {r : Fin n // tensorPowerEquiv (a := a) n y r = z} := by
    simpa [tensorPowerTypeProfile] using hzProfile
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp hcard
  exact ⟨r.1, r.2⟩

theorem tensorPowerUpdate_mem_profileClass_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j)
    {y : TensorPower a n}
    (hyq : y ∈ tensorPowerProfileClass (a := a) q)
    {r : Fin n} (hyr : tensorPowerEquiv (a := a) n y r = j) :
    tensorPowerUpdate (a := a) n y r i ∈ tensorPowerProfileClass (a := a) p := by
  rw [mem_tensorPowerProfileClass]
  funext z
  have hqprofile := (mem_tensorPowerProfileClass (a := a) q y).mp hyq
  by_cases hzi : z = i
  · subst z
    have hsame := tensorPowerTypeProfile_tensorPowerUpdate_same (a := a) y r hadj.ne hyr
    have hyi : tensorPowerTypeProfile (a := a) n y i = q.1 i := congrFun hqprofile i
    calc
      tensorPowerTypeProfile (a := a) n (tensorPowerUpdate (a := a) n y r i) i
          = tensorPowerTypeProfile (a := a) n y i + 1 := hsame
      _ = q.1 i + 1 := by rw [hyi]
      _ = p.1 i := by
        rw [hadj.coord_i]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hadj.source_pos)
  · by_cases hzj : z = j
    · subst z
      have hremoved := tensorPowerTypeProfile_tensorPowerUpdate_removed (a := a) y r hadj.ne hyr
      have hyj : tensorPowerTypeProfile (a := a) n y j = q.1 j := congrFun hqprofile j
      apply Nat.succ.inj
      calc
        tensorPowerTypeProfile (a := a) n (tensorPowerUpdate (a := a) n y r i) j + 1
            = tensorPowerTypeProfile (a := a) n y j := hremoved
        _ = q.1 j := by rw [hyj]
        _ = p.1 j + 1 := hadj.coord_j
    · have hother := tensorPowerTypeProfile_tensorPowerUpdate_other (a := a) y r hzi hzj hyr
      have hyz : tensorPowerTypeProfile (a := a) n y z = q.1 z := congrFun hqprofile z
      calc
        tensorPowerTypeProfile (a := a) n (tensorPowerUpdate (a := a) n y r i) z
            = tensorPowerTypeProfile (a := a) n y z := hother
        _ = q.1 z := by rw [hyz]
        _ = p.1 z := hadj.coord_other z hzi hzj

theorem exists_update_to_adjacent_profileClass {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j)
    {y : TensorPower a n}
    (hyq : y ∈ tensorPowerProfileClass (a := a) q) :
    ∃ r : Fin n,
      tensorPowerEquiv (a := a) n y r = j ∧
        tensorPowerUpdate (a := a) n y r i ∈ tensorPowerProfileClass (a := a) p := by
  have hqj_pos : 0 < q.1 j := by
    rw [hadj.coord_j]
    exact Nat.succ_pos _
  obtain ⟨r, hyr⟩ :=
    exists_tensorPower_coordinate_eq_of_profile_pos (a := a) hyq (z := j) hqj_pos
  exact ⟨r, hyr, tensorPowerUpdate_mem_profileClass_of_adjacent (a := a) hadj hyq hyr⟩

theorem tensorPowerUpdate_mem_profileClass_to_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j)
    {x : TensorPower a n}
    (hxp : x ∈ tensorPowerProfileClass (a := a) p)
    {r : Fin n} (hxr : tensorPowerEquiv (a := a) n x r = i) :
    tensorPowerUpdate (a := a) n x r j ∈ tensorPowerProfileClass (a := a) q := by
  rw [mem_tensorPowerProfileClass]
  funext z
  have hpprofile := (mem_tensorPowerProfileClass (a := a) p x).mp hxp
  by_cases hzi : z = i
  · subst z
    have hremoved := tensorPowerTypeProfile_tensorPowerUpdate_removed
      (a := a) x r hadj.ne.symm hxr
    have hxi : tensorPowerTypeProfile (a := a) n x i = p.1 i := congrFun hpprofile i
    apply Nat.succ.inj
    calc
      tensorPowerTypeProfile (a := a) n (tensorPowerUpdate (a := a) n x r j) i + 1
          = tensorPowerTypeProfile (a := a) n x i := hremoved
      _ = p.1 i := by rw [hxi]
      _ = q.1 i + 1 := by
        rw [hadj.coord_i]
        exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hadj.source_pos)).symm
  · by_cases hzj : z = j
    · subst z
      have hsame := tensorPowerTypeProfile_tensorPowerUpdate_same
        (a := a) x r hadj.ne.symm hxr
      have hxj : tensorPowerTypeProfile (a := a) n x j = p.1 j := congrFun hpprofile j
      calc
        tensorPowerTypeProfile (a := a) n (tensorPowerUpdate (a := a) n x r j) j
            = tensorPowerTypeProfile (a := a) n x j + 1 := hsame
        _ = p.1 j + 1 := by rw [hxj]
        _ = q.1 j := hadj.coord_j.symm
    · have hother := tensorPowerTypeProfile_tensorPowerUpdate_other
        (a := a) x r hzj hzi hxr
      have hxz : tensorPowerTypeProfile (a := a) n x z = p.1 z := congrFun hpprofile z
      calc
        tensorPowerTypeProfile (a := a) n (tensorPowerUpdate (a := a) n x r j) z
            = tensorPowerTypeProfile (a := a) n x z := hother
        _ = p.1 z := by rw [hxz]
        _ = q.1 z := (hadj.coord_other z hzi hzj).symm

theorem exists_update_from_adjacent_profileClass {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j)
    {x : TensorPower a n}
    (hxp : x ∈ tensorPowerProfileClass (a := a) p) :
    ∃ r : Fin n,
      tensorPowerEquiv (a := a) n x r = i ∧
        tensorPowerUpdate (a := a) n x r j ∈ tensorPowerProfileClass (a := a) q := by
  obtain ⟨r, hxr⟩ :=
    exists_tensorPower_coordinate_eq_of_profile_pos (a := a) hxp hadj.source_pos
  exact ⟨r, hxr, tensorPowerUpdate_mem_profileClass_to_adjacent (a := a) hadj hxp hxr⟩

theorem exists_profileClass_pair_twoLevelTensorGenerator_ne_zero_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j) :
    ∃ x : TensorPower a n, x ∈ tensorPowerProfileClass (a := a) p ∧
      ∃ y : TensorPower a n, y ∈ tensorPowerProfileClass (a := a) q ∧
        twoLevelTensorGeneratorMatrix (a := a) i j n x y ≠ 0 := by
  let y : TensorPower a n := q.rep
  have hyq : y ∈ tensorPowerProfileClass (a := a) q :=
    TensorPowerProfile.rep_mem_class (a := a) q
  obtain ⟨r, hyr, hxmem⟩ :=
    exists_update_to_adjacent_profileClass (a := a) hadj hyq
  refine ⟨tensorPowerUpdate (a := a) n y r i, hxmem, y, hyq, ?_⟩
  have hentry := twoLevelTensorGeneratorMatrix_update_j_to_i (a := a) hadj.ne y r hyr
  rw [hentry]
  norm_num

theorem twoLevelTensorGeneratorMatrix_eq_neg_one_of_adjacent_profileClasses_of_ne {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j)
    {x y : TensorPower a n}
    (hxp : x ∈ tensorPowerProfileClass (a := a) p)
    (hyq : y ∈ tensorPowerProfileClass (a := a) q)
    (hne : twoLevelTensorGeneratorMatrix (a := a) i j n x y ≠ 0) :
    twoLevelTensorGeneratorMatrix (a := a) i j n x y = -1 := by
  classical
  rw [twoLevelTensorGeneratorMatrix_apply] at hne ⊢
  obtain ⟨r, -, hrterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hprod_entry := mul_ne_zero_iff.mp hrterm
  have hprod_ne :
      (∏ s : Fin n, if s = r then (1 : ℂ)
        else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) ≠ 0 :=
    hprod_entry.1
  have hentry_ne :
      twoLevelGeneratorEntry i j
        (tensorPowerEquiv n x r) (tensorPowerEquiv n y r) ≠ 0 :=
    hprod_entry.2
  have hsame : ∀ s : Fin n, s ≠ r →
      tensorPowerEquiv (a := a) n x s = tensorPowerEquiv (a := a) n y s := by
    intro s hsr
    have hs_ne :=
      (Finset.prod_ne_zero_iff.mp hprod_ne) s (Finset.mem_univ s)
    by_contra hxy
    have hfactor :
        (if s = r then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 0 := by
      simp [hsr, hxy]
    exact hs_ne hfactor
  rcases twoLevelGeneratorEntry_ne_zero_cases (a := a) hentry_ne with hleft | hright
  · rw [Finset.sum_eq_single r]
    · have hprod :
          (∏ s : Fin n, if s = r then (1 : ℂ)
            else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 1 := by
        apply Finset.prod_eq_one
        intro s _
        by_cases hsr : s = r
        · simp [hsr]
        · simp [hsr, hsame s hsr]
      rw [hprod, twoLevelGeneratorEntry_eq_neg_one_of_left (a := a) hleft]
      simp
    · intro t _ htr
      have hprod_zero :
          (∏ s : Fin n, if s = t then (1 : ℂ)
            else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ r)
        have hrt : ¬ r = t := fun h => htr h.symm
        have hxy_ne : tensorPowerEquiv n x r ≠ tensorPowerEquiv n y r := by
          rcases hleft with ⟨hxri, hyrj⟩
          rw [hxri, hyrj]
          exact hadj.ne
        simp [hrt, hxy_ne]
      rw [hprod_zero]
      simp
    · intro hr
      exact (hr (Finset.mem_univ r)).elim
  · exfalso
    rcases hright with ⟨hxrj, hyri⟩
    have hy_eq_update :
        y = tensorPowerUpdate (a := a) n x r i := by
      apply (tensorPowerEquiv (a := a) n).injective
      funext s
      by_cases hsr : s = r
      · subst s
        simp [hyri]
      · simp [tensorPowerEquiv_tensorPowerUpdate_of_ne (a := a) n x hsr i,
          (hsame s hsr).symm]
    have hqprofile := (mem_tensorPowerProfileClass (a := a) q y).mp hyq
    have hpprofile := (mem_tensorPowerProfileClass (a := a) p x).mp hxp
    have hupdate_same :=
      tensorPowerTypeProfile_tensorPowerUpdate_same (a := a) x r hadj.ne hxrj
    have hqi :
        q.1 i = p.1 i + 1 := by
      calc
        q.1 i = tensorPowerTypeProfile (a := a) n y i := by
          exact (congrFun hqprofile i).symm
        _ = tensorPowerTypeProfile (a := a) n
              (tensorPowerUpdate (a := a) n x r i) i := by rw [hy_eq_update]
        _ = tensorPowerTypeProfile (a := a) n x i + 1 := hupdate_same
        _ = p.1 i + 1 := by rw [congrFun hpprofile i]
    have hqi' : q.1 i = p.1 i - 1 := hadj.coord_i
    omega

private theorem finset_sum_ne_zero_of_zero_or_neg_one
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ x ∈ s, f x = 0 ∨ f x = -1)
    (hex : ∃ x ∈ s, f x = -1) :
    (∑ x ∈ s, f x) ≠ 0 := by
  classical
  let t : Finset ι := s.filter fun x => f x = -1
  have ht_nonempty : t.Nonempty := by
    rcases hex with ⟨x, hxs, hx⟩
    exact ⟨x, by simp [t, hxs, hx]⟩
  have hsum :
      (∑ x ∈ s, f x) = - (t.card : ℂ) := by
    calc
      (∑ x ∈ s, f x)
          = ∑ x ∈ s, if f x = -1 then (-1 : ℂ) else 0 := by
              apply Finset.sum_congr rfl
              intro x hxs
              rcases hf x hxs with hx0 | hxneg
              · simp [hx0]
              · simp [hxneg]
      _ = ∑ x ∈ t, (-1 : ℂ) := by
              rw [← Finset.sum_filter]
      _ = - (t.card : ℂ) := by
              simp
  rw [hsum]
  have ht_card_pos : 0 < t.card := Finset.card_pos.mpr ht_nonempty
  have hcard_ne : ((t.card : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt ht_card_pos
  simpa using (neg_ne_zero.mpr hcard_ne)

theorem tensorPowerProfileUnitVector_ne_zero_of_mem_class {n : ℕ}
    (p : TensorPowerProfile a n) {x : TensorPower a n}
    (hx : x ∈ tensorPowerProfileClass (a := a) p) :
    tensorPowerProfileUnitVector (a := a) p x ≠ 0 := by
  have hpos : 0 < ((tensorPowerProfileClass (a := a) p).card : ℝ) := by
    exact_mod_cast TensorPowerProfile.class_card_pos (a := a) p
  have hsqrt_ne : (Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [tensorPowerProfileUnitVector, hx, hsqrt_ne]

theorem exists_profileCoeff_summand_ne_zero_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j) :
    ∃ x : TensorPower a n, x ∈ tensorPowerProfileClass (a := a) p ∧
      ∃ y : TensorPower a n, y ∈ tensorPowerProfileClass (a := a) q ∧
        star (tensorPowerProfileUnitVector (a := a) p x) *
            (twoLevelTensorGeneratorMatrix (a := a) i j n x y *
              tensorPowerProfileUnitVector (a := a) q y) ≠ 0 := by
  obtain ⟨x, hx, y, hy, hG⟩ :=
    exists_profileClass_pair_twoLevelTensorGenerator_ne_zero_of_adjacent (a := a) hadj
  refine ⟨x, hx, y, hy, ?_⟩
  have hvp : star (tensorPowerProfileUnitVector (a := a) p x) ≠ 0 := by
    exact star_ne_zero.mpr (tensorPowerProfileUnitVector_ne_zero_of_mem_class (a := a) p hx)
  have hvq : tensorPowerProfileUnitVector (a := a) q y ≠ 0 :=
    tensorPowerProfileUnitVector_ne_zero_of_mem_class (a := a) q hy
  exact mul_ne_zero hvp (mul_ne_zero hG hvq)

noncomputable def profileClassMatrixEntrySum {n : ℕ}
    (M : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) : ℂ :=
  ∑ x ∈ tensorPowerProfileClass (a := a) p,
    ∑ y ∈ tensorPowerProfileClass (a := a) q, M x y

theorem profileMatrixCoeff_eq_inv_sqrt_mul_profileClassMatrixEntrySum {n : ℕ}
    (M : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) :
    profileMatrixCoeff (a := a) M p q =
      ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹) *
        ((Real.sqrt ((tensorPowerProfileClass (a := a) q).card : ℝ) : ℂ)⁻¹) *
          profileClassMatrixEntrySum (a := a) M p q := by
  classical
  unfold profileMatrixCoeff profileClassMatrixEntrySum
  simp only [Matrix.mulVec, dotProduct]
  let cp : ℂ := ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹)
  let cq : ℂ := ((Real.sqrt ((tensorPowerProfileClass (a := a) q).card : ℝ) : ℂ)⁻¹)
  have hstar_cp : star cp = cp := by
    simp [cp]
  calc
    ∑ x, star (tensorPowerProfileUnitVector (a := a) p x) *
        ∑ y, M x y * tensorPowerProfileUnitVector (a := a) q y
        = ∑ x,
            (if x ∈ tensorPowerProfileClass (a := a) p then cp else 0) *
              ∑ y, M x y *
                (if y ∈ tensorPowerProfileClass (a := a) q then cq else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
          · simp [tensorPowerProfileUnitVector, hx, cp, cq, hstar_cp]
          · simp [tensorPowerProfileUnitVector, hx]
    _ = ∑ x ∈ tensorPowerProfileClass (a := a) p,
            cp * ∑ y ∈ tensorPowerProfileClass (a := a) q, M x y * cq := by
          simp [Finset.sum_filter, mul_assoc]
    _ = cp * cq *
          ∑ x ∈ tensorPowerProfileClass (a := a) p,
            ∑ y ∈ tensorPowerProfileClass (a := a) q, M x y := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]

theorem profileClassMatrixEntrySum_twoLevelTensorGenerator_ne_zero_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j) :
    profileClassMatrixEntrySum (a := a)
      (twoLevelTensorGeneratorMatrix (a := a) i j n) p q ≠ 0 := by
  classical
  unfold profileClassMatrixEntrySum
  rw [← Finset.sum_product']
  refine finset_sum_ne_zero_of_zero_or_neg_one
    ((tensorPowerProfileClass (a := a) p).product
      (tensorPowerProfileClass (a := a) q))
    (fun xy : TensorPower a n × TensorPower a n =>
      twoLevelTensorGeneratorMatrix (a := a) i j n xy.1 xy.2) ?_ ?_
  · intro xy hxy
    rcases Finset.mem_product.mp hxy with ⟨hx, hy⟩
    by_cases hG : twoLevelTensorGeneratorMatrix (a := a) i j n xy.1 xy.2 = 0
    · exact Or.inl hG
    · exact Or.inr
        (twoLevelTensorGeneratorMatrix_eq_neg_one_of_adjacent_profileClasses_of_ne
          (a := a) hadj hx hy hG)
  · obtain ⟨x, hx, y, hy, hG⟩ :=
      exists_profileClass_pair_twoLevelTensorGenerator_ne_zero_of_adjacent (a := a) hadj
    refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
    exact twoLevelTensorGeneratorMatrix_eq_neg_one_of_adjacent_profileClasses_of_ne
      (a := a) hadj hx hy hG

theorem profileVectorCoeff_twoLevelTensorGenerator_ne_zero_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j) :
    profileVectorCoeff (a := a)
      (twoLevelTensorGeneratorMatrix (a := a) i j n) p q ≠ 0 := by
  classical
  rw [profileVectorCoeff_eq_profileMatrixCoeff]
  rw [profileMatrixCoeff_eq_inv_sqrt_mul_profileClassMatrixEntrySum]
  have hp_pos : 0 < ((tensorPowerProfileClass (a := a) p).card : ℝ) := by
    exact_mod_cast TensorPowerProfile.class_card_pos (a := a) p
  have hq_pos : 0 < ((tensorPowerProfileClass (a := a) q).card : ℝ) := by
    exact_mod_cast TensorPowerProfile.class_card_pos (a := a) q
  have hp_ne :
      ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹) ≠ 0 := by
    apply inv_ne_zero
    norm_cast
    exact ne_of_gt (Real.sqrt_pos.2 hp_pos)
  have hq_ne :
      ((Real.sqrt ((tensorPowerProfileClass (a := a) q).card : ℝ) : ℂ)⁻¹) ≠ 0 := by
    apply inv_ne_zero
    norm_cast
    exact ne_of_gt (Real.sqrt_pos.2 hq_pos)
  exact mul_ne_zero (mul_ne_zero hp_ne hq_ne)
    (profileClassMatrixEntrySum_twoLevelTensorGenerator_ne_zero_of_adjacent
      (a := a) hadj)

theorem symmetricProjectionMatrix_mulVec_profileUnitVector {n : ℕ}
    (p : TensorPowerProfile a n) :
    (symmetricProjectionMatrix (a := a) n).mulVec
        (tensorPowerProfileUnitVector (a := a) p) =
      tensorPowerProfileUnitVector (a := a) p := by
  exact (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self (a := a) n
    (tensorPowerProfileUnitVector (a := a) p)).mp
    (by
      have hvec : tensorPowerProfileVector (a := a) p ∈ symmetricSubspace (a := a) n :=
        tensorPowerProfileVector_mem (a := a) p
      have hpos : 0 < ((tensorPowerProfileClass (a := a) p).card : ℝ) := by
        exact_mod_cast TensorPowerProfile.class_card_pos (a := a) p
      have hsqrt_ne :
          (Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ) ≠ 0 := by
        norm_cast
        exact ne_of_gt (Real.sqrt_pos.2 hpos)
      have hunit :
          tensorPowerProfileUnitVector (a := a) p =
            ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹ *
              ((tensorPowerProfileClass (a := a) p).card : ℂ)) •
                tensorPowerProfileVector (a := a) p := by
        have hcard_ne :
            ((tensorPowerProfileClass (a := a) p).card : ℂ) ≠ 0 := by
          exact_mod_cast TensorPowerProfile.class_card_ne_zero (a := a) p
        ext x
        by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
        · simp [tensorPowerProfileUnitVector, tensorPowerProfileVector_eq_inv_card_of_mem_class
            (a := a) p hx, hx, smul_eq_mul, hsqrt_ne, mul_assoc]
          field_simp [hcard_ne]
        · simp [tensorPowerProfileUnitVector, tensorPowerProfileVector_eq_zero_of_not_mem_class
            (a := a) p hx, hx]
      rw [hunit]
      have hvecSub :
          tensorPowerProfileVector (a := a) p ∈ symmetricSubmodule (a := a) n := by
        rw [mem_symmetricSubmodule_iff]
        exact hvec
      have hscaledSub :
          ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹ *
              ((tensorPowerProfileClass (a := a) p).card : ℂ)) •
                tensorPowerProfileVector (a := a) p ∈ symmetricSubmodule (a := a) n :=
        Submodule.smul_mem _ _ hvecSub
      exact (mem_symmetricSubmodule_iff (a := a) n _).mp hscaledSub)

theorem rankOneMatrix_mulVec_eq_dotProduct_smul {ι : Type u} [Fintype ι]
    (v w : ι → ℂ) :
    (rankOneMatrix v).mulVec w = dotProduct (star v) w • v := by
  ext i
  simp [Matrix.mulVec, rankOneMatrix_apply, dotProduct, Finset.mul_sum, mul_assoc,
    mul_comm, mul_left_comm]

theorem symmetricProjectionMatrix_mulVec_eq_sum_profileUnitVector {n : ℕ}
    (w : TensorPower a n → ℂ) :
    (symmetricProjectionMatrix (a := a) n).mulVec w =
      ∑ p : TensorPowerProfile a n,
        dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w •
          tensorPowerProfileUnitVector (a := a) p := by
  rw [symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector]
  calc
    (∑ p : TensorPowerProfile a n,
        rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)).mulVec w =
        ∑ p : TensorPowerProfile a n,
          (rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)).mulVec w := by
          ext x
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y _
          have hentry :
              (∑ p : TensorPowerProfile a n,
                rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)) x y =
              ∑ p : TensorPowerProfile a n,
                rankOneMatrix (tensorPowerProfileUnitVector (a := a) p) x y := by
            calc
              ((∑ p : TensorPowerProfile a n,
                  rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)) x) y =
                  ((∑ p : TensorPowerProfile a n,
                    (rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)) x) y) := by
                    exact congrFun
                      (Finset.sum_apply x Finset.univ
                        (fun p : TensorPowerProfile a n =>
                          rankOneMatrix (tensorPowerProfileUnitVector (a := a) p))) y
              _ = ∑ p : TensorPowerProfile a n,
                  rankOneMatrix (tensorPowerProfileUnitVector (a := a) p) x y := by
                    exact Finset.sum_apply y Finset.univ
                      (fun p : TensorPowerProfile a n =>
                        (rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)) x)
          rw [hentry]
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (TensorPowerProfile a n)))
              (f := fun p : TensorPowerProfile a n =>
                rankOneMatrix (tensorPowerProfileUnitVector (a := a) p) x y)
              (a := w y))
    _ = ∑ p : TensorPowerProfile a n,
        dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w •
          tensorPowerProfileUnitVector (a := a) p := by
          refine Finset.sum_congr rfl ?_
          intro p _
          exact rankOneMatrix_mulVec_eq_dotProduct_smul
            (tensorPowerProfileUnitVector (a := a) p) w

theorem profileMatrixCoeff_mul_of_right_profile_eigen {n : ℕ}
    (M B : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) (d : ℂ)
    (hBq : B.mulVec (tensorPowerProfileUnitVector (a := a) q) =
      d • tensorPowerProfileUnitVector (a := a) q) :
    profileMatrixCoeff (a := a) (M * B) p q =
      d * profileMatrixCoeff (a := a) M p q := by
  unfold profileMatrixCoeff
  rw [← Matrix.mulVec_mulVec]
  rw [hBq]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm,
    mul_left_comm]

theorem profileMatrixCoeff_mul_symmetricProjectionMatrix_right {n : ℕ}
    (B : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) :
    profileMatrixCoeff (a := a) (B * symmetricProjectionMatrix (a := a) n) p q =
      profileMatrixCoeff (a := a) B p q := by
  simpa using
    profileMatrixCoeff_mul_of_right_profile_eigen (a := a) B
      (symmetricProjectionMatrix (a := a) n) p q 1
      (by
        simp [symmetricProjectionMatrix_mulVec_profileUnitVector (a := a) q])

theorem profileMatrixCoeff_mul_of_left_profile_eigenfunctional {n : ℕ}
    (M B : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) (d : ℂ)
    (hBp : ∀ w : TensorPower a n → ℂ,
      dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) (B.mulVec w) =
        d * dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w) :
    profileMatrixCoeff (a := a) (B * M) p q =
      d * profileMatrixCoeff (a := a) M p q := by
  unfold profileMatrixCoeff
  rw [← Matrix.mulVec_mulVec]
  exact hBp (M.mulVec (tensorPowerProfileUnitVector (a := a) q))

theorem symmetricProjectionMatrix_profileUnitVector_left_functional {n : ℕ}
    (p : TensorPowerProfile a n) (w : TensorPower a n → ℂ) :
    dotProduct (star (tensorPowerProfileUnitVector (a := a) p))
        ((symmetricProjectionMatrix (a := a) n).mulVec w) =
      dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w := by
  classical
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  let v : TensorPower a n → ℂ := tensorPowerProfileUnitVector (a := a) p
  have hPv : P.mulVec v = v := by
    simpa [P, v] using symmetricProjectionMatrix_mulVec_profileUnitVector (a := a) p
  have hPherm : P.conjTranspose = P := by
    simpa [P] using symmetricProjectionMatrix_conjTranspose (a := a) n
  have hleft : Matrix.vecMul (star v) P = star v := by
    have hstar : star (P.mulVec v) = star v := congrArg star hPv
    rw [Matrix.star_mulVec] at hstar
    simpa [hPherm] using hstar
  calc
    dotProduct (star v) (P.mulVec w) = dotProduct (Matrix.vecMul (star v) P) w := by
      rw [Matrix.dotProduct_mulVec]
    _ = dotProduct (star v) w := by
      rw [hleft]

theorem profileMatrixCoeff_symmetricProjectionMatrix_mul_left {n : ℕ}
    (B : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) :
    profileMatrixCoeff (a := a) (symmetricProjectionMatrix (a := a) n * B) p q =
      profileMatrixCoeff (a := a) B p q := by
  simpa using
    profileMatrixCoeff_mul_of_left_profile_eigenfunctional (a := a) B
      (symmetricProjectionMatrix (a := a) n) p q 1
      (by
        intro w
        simp [symmetricProjectionMatrix_profileUnitVector_left_functional (a := a) p w])

theorem profileMatrixCoeff_symmetricProjectionMatrix_mul_right {n : ℕ}
    (B : CMatrix (TensorPower a n)) (p q : TensorPowerProfile a n) :
    profileMatrixCoeff (a := a) (symmetricProjectionMatrix (a := a) n * B *
        symmetricProjectionMatrix (a := a) n) p q =
      profileMatrixCoeff (a := a) B p q := by
  rw [profileMatrixCoeff_mul_symmetricProjectionMatrix_right,
    profileMatrixCoeff_symmetricProjectionMatrix_mul_left]

private theorem dotProduct_mulVec_sum_smul {ι κ : Type u} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (u : ι → ℂ) (M : CMatrix ι)
    (c : κ → ℂ) (v : κ → ι → ℂ) :
    dotProduct u (M.mulVec (∑ k : κ, c k • v k)) =
      ∑ k : κ, c k * dotProduct u (M.mulVec (v k)) := by
  classical
  calc
    dotProduct u (M.mulVec (∑ k : κ, c k • v k))
        = dotProduct u (∑ k : κ, M.mulVec (c k • v k)) := by
          rw [Matrix.mulVec_sum]
    _ = ∑ k : κ, dotProduct u (M.mulVec (c k • v k)) := by
          rw [dotProduct_sum]
    _ = ∑ k : κ, c k * dotProduct u (M.mulVec (v k)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Matrix.mulVec_smul, dotProduct_smul]
          rfl

theorem compressed_mulVec_profileUnitVector_eq_diagonal_smul_of_offProfile_zero {n : ℕ}
    (B : CMatrix (TensorPower a n)) (q : TensorPowerProfile a n)
    (hoff : ∀ p : TensorPowerProfile a n, p ≠ q → profileMatrixCoeff (a := a) B p q = 0) :
    (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n).mulVec
        (tensorPowerProfileUnitVector (a := a) q) =
      profileMatrixCoeff (a := a) B q q • tensorPowerProfileUnitVector (a := a) q := by
  classical
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  let vq : TensorPower a n → ℂ := tensorPowerProfileUnitVector (a := a) q
  calc
    (P * B * P).mulVec vq = P.mulVec ((B * P).mulVec vq) := by
      rw [Matrix.mul_assoc]
      rw [Matrix.mulVec_mulVec]
    _ = ∑ p : TensorPowerProfile a n,
          profileMatrixCoeff (a := a) (B * P) p q •
            tensorPowerProfileUnitVector (a := a) p := by
      rw [symmetricProjectionMatrix_mulVec_eq_sum_profileUnitVector]
      rfl
    _ = ∑ p : TensorPowerProfile a n,
          profileMatrixCoeff (a := a) B p q •
            tensorPowerProfileUnitVector (a := a) p := by
      refine Finset.sum_congr rfl ?_
      intro p _
      rw [profileMatrixCoeff_mul_symmetricProjectionMatrix_right]
    _ = profileMatrixCoeff (a := a) B q q • tensorPowerProfileUnitVector (a := a) q := by
      rw [Finset.sum_eq_single q]
      · intro p _ hpq
        rw [hoff p hpq]
        simp
      · intro hq
        exact False.elim (hq (Finset.mem_univ q))

theorem compressed_left_profile_functional_eq_diagonal_mul_of_offProfile_zero {n : ℕ}
    (B : CMatrix (TensorPower a n)) (p : TensorPowerProfile a n)
    (hoff : ∀ q : TensorPowerProfile a n, q ≠ p → profileMatrixCoeff (a := a) B p q = 0) :
    ∀ w : TensorPower a n → ℂ,
      dotProduct (star (tensorPowerProfileUnitVector (a := a) p))
          ((symmetricProjectionMatrix (a := a) n * B *
              symmetricProjectionMatrix (a := a) n).mulVec w) =
        profileMatrixCoeff (a := a) B p p *
          dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w := by
  classical
  intro w
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  let C : CMatrix (TensorPower a n) := P * B * P
  let vp : TensorPower a n → ℂ := tensorPowerProfileUnitVector (a := a) p
  have hCP : C * P = C := by
    calc
      C * P = P * B * (P * P) := by
        simp [C, P, Matrix.mul_assoc]
      _ = C := by
        rw [symmetricProjectionMatrix_idempotent (a := a) n]
  have hCw : C.mulVec w = C.mulVec (P.mulVec w) := by
    calc
      C.mulVec w = (C * P).mulVec w := by rw [hCP]
      _ = C.mulVec (P.mulVec w) := by rw [Matrix.mulVec_mulVec]
  have hcoeffC : ∀ q : TensorPowerProfile a n,
      profileMatrixCoeff (a := a) C p q = profileMatrixCoeff (a := a) B p q := by
    intro q
    simp [C, P, profileMatrixCoeff_symmetricProjectionMatrix_mul_right]
  calc
    dotProduct (star vp) (C.mulVec w)
        = dotProduct (star vp) (C.mulVec (P.mulVec w)) := by rw [hCw]
    _ = dotProduct (star vp)
          (C.mulVec
            (∑ q : TensorPowerProfile a n,
              dotProduct (star (tensorPowerProfileUnitVector (a := a) q)) w •
                tensorPowerProfileUnitVector (a := a) q)) := by
          rw [symmetricProjectionMatrix_mulVec_eq_sum_profileUnitVector]
    _ = ∑ q : TensorPowerProfile a n,
          dotProduct (star (tensorPowerProfileUnitVector (a := a) q)) w *
            profileMatrixCoeff (a := a) C p q := by
          simpa [profileMatrixCoeff, vp] using
            dotProduct_mulVec_sum_smul
              (ι := TensorPower a n) (κ := TensorPowerProfile a n)
              (u := star vp) (M := C)
              (c := fun q : TensorPowerProfile a n =>
                dotProduct (star (tensorPowerProfileUnitVector (a := a) q)) w)
              (v := fun q : TensorPowerProfile a n =>
                tensorPowerProfileUnitVector (a := a) q)
    _ = ∑ q : TensorPowerProfile a n,
          dotProduct (star (tensorPowerProfileUnitVector (a := a) q)) w *
            profileMatrixCoeff (a := a) B p q := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [hcoeffC q]
    _ = dotProduct (star vp) w * profileMatrixCoeff (a := a) B p p := by
          rw [Finset.sum_eq_single p]
          · intro q _ hqp
            rw [hoff q hqp]
            simp
          · intro hp
            exact False.elim (hp (Finset.mem_univ p))
    _ = profileMatrixCoeff (a := a) B p p * dotProduct (star vp) w := by
          ring

theorem adjacent_profileMatrixCoeff_eq_of_commuting_generator {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (B : CMatrix (TensorPower a n))
    (hcomm :
      twoLevelTensorGeneratorMatrix (a := a) i j n * B =
        B * twoLevelTensorGeneratorMatrix (a := a) i j n)
    (hBq :
      B.mulVec (tensorPowerProfileUnitVector (a := a) q) =
        profileMatrixCoeff (a := a) B q q • tensorPowerProfileUnitVector (a := a) q)
    (hBp : ∀ w : TensorPower a n → ℂ,
      dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) (B.mulVec w) =
        profileMatrixCoeff (a := a) B p p *
          dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w)
    (hG : profileVectorCoeff (a := a) (twoLevelTensorGeneratorMatrix (a := a) i j n) p q ≠ 0) :
    profileMatrixCoeff (a := a) B p p = profileMatrixCoeff (a := a) B q q := by
  let G : CMatrix (TensorPower a n) := twoLevelTensorGeneratorMatrix (a := a) i j n
  have hcoeff :
      profileMatrixCoeff (a := a) (G * B) p q =
        profileMatrixCoeff (a := a) (B * G) p q := by
    rw [hcomm]
  have hleft :
      profileMatrixCoeff (a := a) (G * B) p q =
        profileMatrixCoeff (a := a) B q q * profileMatrixCoeff (a := a) G p q :=
    profileMatrixCoeff_mul_of_right_profile_eigen (a := a) G B p q
      (profileMatrixCoeff (a := a) B q q) hBq
  have hright :
      profileMatrixCoeff (a := a) (B * G) p q =
        profileMatrixCoeff (a := a) B p p * profileMatrixCoeff (a := a) G p q :=
    profileMatrixCoeff_mul_of_left_profile_eigenfunctional (a := a) G B p q
      (profileMatrixCoeff (a := a) B p p) hBp
  have hmul :
      profileMatrixCoeff (a := a) B q q * profileMatrixCoeff (a := a) G p q =
        profileMatrixCoeff (a := a) B p p * profileMatrixCoeff (a := a) G p q := by
    rw [← hleft, hcoeff, hright]
  have hG' : profileMatrixCoeff (a := a) G p q ≠ 0 := by
    simpa [G, profileVectorCoeff_eq_profileMatrixCoeff] using hG
  exact (mul_right_cancel₀ hG' hmul).symm

theorem adjacent_profileMatrixCoeff_eq_of_commuting_generator_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (B : CMatrix (TensorPower a n))
    (hadj : ProfileAdjacentMove (a := a) p q i j)
    (hcomm :
      twoLevelTensorGeneratorMatrix (a := a) i j n * B =
        B * twoLevelTensorGeneratorMatrix (a := a) i j n)
    (hBq :
      B.mulVec (tensorPowerProfileUnitVector (a := a) q) =
        profileMatrixCoeff (a := a) B q q • tensorPowerProfileUnitVector (a := a) q)
    (hBp : ∀ w : TensorPower a n → ℂ,
      dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) (B.mulVec w) =
        profileMatrixCoeff (a := a) B p p *
          dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w) :
    profileMatrixCoeff (a := a) B p p = profileMatrixCoeff (a := a) B q q :=
  adjacent_profileMatrixCoeff_eq_of_commuting_generator (a := a) B hcomm hBq hBp
    (profileVectorCoeff_twoLevelTensorGenerator_ne_zero_of_adjacent (a := a) hadj)

theorem compressed_adjacent_profileMatrixCoeff_eq_of_commuting_generator_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (B : CMatrix (TensorPower a n))
    (hadj : ProfileAdjacentMove (a := a) p q i j)
    (hcomm :
      twoLevelTensorGeneratorMatrix (a := a) i j n *
          (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n) =
        (symmetricProjectionMatrix (a := a) n * B * symmetricProjectionMatrix (a := a) n) *
          twoLevelTensorGeneratorMatrix (a := a) i j n)
    (hoff_col : ∀ r : TensorPowerProfile a n,
      r ≠ q → profileMatrixCoeff (a := a) B r q = 0)
    (hoff_row : ∀ r : TensorPowerProfile a n,
      r ≠ p → profileMatrixCoeff (a := a) B p r = 0) :
    profileMatrixCoeff (a := a) B p p = profileMatrixCoeff (a := a) B q q := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  let C : CMatrix (TensorPower a n) := P * B * P
  have hBq :
      C.mulVec (tensorPowerProfileUnitVector (a := a) q) =
        profileMatrixCoeff (a := a) C q q • tensorPowerProfileUnitVector (a := a) q := by
    have h :=
      compressed_mulVec_profileUnitVector_eq_diagonal_smul_of_offProfile_zero
        (a := a) B q hoff_col
    simpa [C, P, profileMatrixCoeff_symmetricProjectionMatrix_mul_right] using h
  have hBp : ∀ w : TensorPower a n → ℂ,
      dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) (C.mulVec w) =
        profileMatrixCoeff (a := a) C p p *
          dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) w := by
    have h :=
      compressed_left_profile_functional_eq_diagonal_mul_of_offProfile_zero
        (a := a) B p hoff_row
    intro w
    simpa [C, P, profileMatrixCoeff_symmetricProjectionMatrix_mul_right] using h w
  have hdiagC :
      profileMatrixCoeff (a := a) C p p = profileMatrixCoeff (a := a) C q q :=
    adjacent_profileMatrixCoeff_eq_of_commuting_generator_of_adjacent
      (a := a) C hadj hcomm hBq hBp
  simpa [C, P, profileMatrixCoeff_symmetricProjectionMatrix_mul_right] using hdiagC

theorem unitaryInvariant_adjacent_profileMatrixCoeff_eq_of_adjacent {n : ℕ}
    {p q : TensorPowerProfile a n} {i j : a}
    (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    (hadj : ProfileAdjacentMove (a := a) p q i j) :
    profileMatrixCoeff (a := a) B p p = profileMatrixCoeff (a := a) B q q := by
  exact compressed_adjacent_profileMatrixCoeff_eq_of_commuting_generator_of_adjacent
    (a := a) B hadj
    (unitaryInvariant_compressed_commutes_twoLevelTensorGeneratorMatrix
      (a := a) B hinv hadj.ne)
    (fun r hrq => unitaryInvariant_profileMatrixCoeff_eq_zero_of_ne
      (a := a) B hinv hrq)
    (fun r hrp => unitaryInvariant_profileMatrixCoeff_eq_zero_of_ne
      (a := a) B hinv hrp.symm)

/-- The one-copy matrix unit sending the basis vector `i` to the basis vector
`j`.  This is the one-way part of the two-level infinitesimal generator and is
used to propagate the highest-weight vector through symmetric profiles without
creating a backward term. -/
def oneWayGeneratorEntry (i j : a) (x y : a) : ℂ :=
  if x = j ∧ y = i then 1 else 0

/-- The infinitesimal tensor generator obtained by applying the one-copy matrix
unit `i ↦ j` in exactly one tensor coordinate. -/
def oneWayTensorGeneratorMatrix (i j : a) (n : ℕ) : CMatrix (TensorPower a n) :=
  Matrix.of fun x y =>
    ∑ r : Fin n,
      oneWayGeneratorEntry i j
        (tensorPowerEquiv (a := a) n x r)
        (tensorPowerEquiv (a := a) n y r) *
        ∏ s : Fin n,
          if s = r then (1 : ℂ)
          else if tensorPowerEquiv (a := a) n x s =
              tensorPowerEquiv (a := a) n y s then 1 else 0

theorem oneWayTensorGeneratorMatrix_apply_single_i_to_j {i j : a} (hij : i ≠ j)
    {n : ℕ} (x y : TensorPower a n) (r : Fin n)
    (hx : tensorPowerEquiv n x r = j)
    (hy : tensorPowerEquiv n y r = i)
    (hsame : ∀ s : Fin n, s ≠ r →
      tensorPowerEquiv n x s = tensorPowerEquiv n y s) :
    oneWayTensorGeneratorMatrix (a := a) i j n x y = 1 := by
  classical
  rw [oneWayTensorGeneratorMatrix]
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single r]
  · have hprod :
        (∏ s : Fin n, if s = r then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 1 := by
      apply Finset.prod_eq_one
      intro s _
      by_cases hsr : s = r
      · simp [hsr]
      · simp [hsr, hsame s hsr]
    rw [hprod, hx, hy]
    simp [oneWayGeneratorEntry, hij]
  · intro t _ htr
    have hprod_zero :
        (∏ s : Fin n, if s = t then (1 : ℂ)
          else if tensorPowerEquiv n x s = tensorPowerEquiv n y s then 1 else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      have hrt : ¬ r = t := fun h => htr h.symm
      have hxy_ne : tensorPowerEquiv n x r ≠ tensorPowerEquiv n y r := by
        rw [hx, hy]
        exact hij.symm
      simp [hrt, hxy_ne]
    rw [hprod_zero]
    simp
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

theorem oneWayTensorGeneratorMatrix_update_i_to_j {i j : a} (hij : i ≠ j)
    {n : ℕ} (y : TensorPower a n) (r : Fin n)
    (hy : tensorPowerEquiv (a := a) n y r = i) :
    oneWayTensorGeneratorMatrix (a := a) i j n
        (tensorPowerUpdate (a := a) n y r j) y = 1 := by
  apply oneWayTensorGeneratorMatrix_apply_single_i_to_j (a := a) hij
  · exact tensorPowerEquiv_tensorPowerUpdate_self (a := a) n y r j
  · exact hy
  · intro s hsr
    simp [tensorPowerEquiv_tensorPowerUpdate_of_ne (a := a) n y hsr j]

/-- The coordinate projection onto the raw tensor-word type class of a profile. -/
def profileClassComponent {n : ℕ} (p : TensorPowerProfile a n)
    (f : TensorPower a n → ℂ) : TensorPower a n → ℂ :=
  fun x => if x ∈ tensorPowerProfileClass (a := a) p then f x else 0

theorem profileClassComponent_profileUnitVector_same {n : ℕ}
    (p : TensorPowerProfile a n) :
    profileClassComponent (a := a) p (tensorPowerProfileUnitVector (a := a) p) =
      tensorPowerProfileUnitVector (a := a) p := by
  ext x
  by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
  · simp [profileClassComponent, hx]
  · simp [profileClassComponent, tensorPowerProfileUnitVector, hx]

theorem profileClassComponent_profileUnitVector_ne {n : ℕ}
    {p q : TensorPowerProfile a n} (hpq : p ≠ q) :
    profileClassComponent (a := a) p (tensorPowerProfileUnitVector (a := a) q) = 0 := by
  ext x
  by_cases hxp : x ∈ tensorPowerProfileClass (a := a) p
  · have hxq : x ∉ tensorPowerProfileClass (a := a) q := by
      intro hxq
      apply hpq
      apply Subtype.ext
      exact ((mem_tensorPowerProfileClass (a := a) p x).mp hxp).symm.trans
        ((mem_tensorPowerProfileClass (a := a) q x).mp hxq)
    simp [profileClassComponent, tensorPowerProfileUnitVector, hxp, hxq]
  · simp [profileClassComponent, hxp]

def constantTensorPowerWord (z₀ : a) (n : ℕ) : TensorPower a n :=
  (tensorPowerEquiv (a := a) n).symm (fun _ => z₀)

@[simp]
theorem tensorPowerEquiv_constantTensorPowerWord (z₀ : a) (n : ℕ) (r : Fin n) :
    tensorPowerEquiv (a := a) n (constantTensorPowerWord (a := a) z₀ n) r = z₀ := by
  simp [constantTensorPowerWord]

def constantTensorPowerProfile (z₀ : a) (n : ℕ) : TensorPowerProfile a n :=
  ⟨tensorPowerTypeProfile (a := a) n (constantTensorPowerWord (a := a) z₀ n),
    tensorPowerTypeProfile_mem_profiles (a := a) n
      (constantTensorPowerWord (a := a) z₀ n)⟩

theorem tensorPowerProfileClass_constant_eq_singleton (z₀ : a) (n : ℕ) :
    tensorPowerProfileClass (a := a) (constantTensorPowerProfile (a := a) z₀ n) =
      {constantTensorPowerWord (a := a) z₀ n} := by
  classical
  ext x
  constructor
  · intro hx
    have hprofile := (mem_tensorPowerProfileClass
      (a := a) (constantTensorPowerProfile (a := a) z₀ n) x).mp hx
    have hxconst : x = constantTensorPowerWord (a := a) z₀ n := by
      apply (tensorPowerEquiv (a := a) n).injective
      funext r
      by_contra hne
      have hpos :
          0 < tensorPowerTypeProfile (a := a) n x (tensorPowerEquiv (a := a) n x r) := by
        rw [tensorPowerTypeProfile_apply]
        exact Fintype.card_pos_iff.mpr ⟨⟨r, rfl⟩⟩
      have hzero :
          tensorPowerTypeProfile (a := a) n
              (constantTensorPowerWord (a := a) z₀ n)
              (tensorPowerEquiv (a := a) n x r) = 0 := by
        rw [tensorPowerTypeProfile_apply]
        exact Fintype.card_eq_zero_iff.mpr
          ⟨fun s => by
            have hs := s.property
            simp [tensorPowerEquiv_constantTensorPowerWord (a := a) z₀ n s.1] at hs
            have hconst :
                tensorPowerEquiv (a := a) n
                    (constantTensorPowerWord (a := a) z₀ n) r = z₀ :=
              tensorPowerEquiv_constantTensorPowerWord (a := a) z₀ n r
            exact hne (by rw [hconst]; exact hs.symm)⟩
      have hsame := congrFun hprofile (tensorPowerEquiv (a := a) n x r)
      change tensorPowerTypeProfile (a := a) n x (tensorPowerEquiv (a := a) n x r) =
        tensorPowerTypeProfile (a := a) n
          (constantTensorPowerWord (a := a) z₀ n)
          (tensorPowerEquiv (a := a) n x r) at hsame
      rw [hzero] at hsame
      rw [hsame] at hpos
      exact Nat.not_lt_zero _ hpos
    simp [hxconst]
  · intro hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    rw [mem_tensorPowerProfileClass]
    rfl

theorem constantTensorPowerProfile_class_card (z₀ : a) (n : ℕ) :
    (tensorPowerProfileClass (a := a)
      (constantTensorPowerProfile (a := a) z₀ n)).card = 1 := by
  rw [tensorPowerProfileClass_constant_eq_singleton]
  simp

theorem tensorPowerProfileUnitVector_constant_apply_self (z₀ : a) (n : ℕ) :
    tensorPowerProfileUnitVector (a := a) (constantTensorPowerProfile (a := a) z₀ n)
        (constantTensorPowerWord (a := a) z₀ n) = 1 := by
  simp [tensorPowerProfileUnitVector, tensorPowerProfileClass_constant_eq_singleton,
    constantTensorPowerProfile_class_card]

theorem tensorPowerProfileUnitVector_constant_apply_of_ne (z₀ : a) (n : ℕ)
    {x : TensorPower a n} (hx : x ≠ constantTensorPowerWord (a := a) z₀ n) :
    tensorPowerProfileUnitVector (a := a) (constantTensorPowerProfile (a := a) z₀ n) x = 0 := by
  have hnot :
      x ∉ tensorPowerProfileClass (a := a)
        (constantTensorPowerProfile (a := a) z₀ n) := by
    rw [tensorPowerProfileClass_constant_eq_singleton]
    simpa using hx
  simp [tensorPowerProfileUnitVector, hnot]

def profileBaseDistance {n : ℕ} (z₀ : a) (p : TensorPowerProfile a n) : ℕ :=
  ∑ z : a, if z = z₀ then 0 else p.1 z

theorem exists_nonbase_pos_of_profileBaseDistance_pos {n : ℕ}
    {z₀ : a} {p : TensorPowerProfile a n}
    (hpos : 0 < profileBaseDistance (a := a) z₀ p) :
    ∃ z : a, z ≠ z₀ ∧ 0 < p.1 z := by
  classical
  unfold profileBaseDistance at hpos
  have hnonneg : ∀ z ∈ (Finset.univ : Finset a),
      0 ≤ (if z = z₀ then 0 else p.1 z) := by
    intro z hz
    exact Nat.zero_le _
  obtain ⟨z, hzmem, hzpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos
  by_cases hzz₀ : z = z₀
  · simp [hzz₀] at hzpos
  · simp [hzz₀] at hzpos
    exact ⟨z, hzz₀, hzpos⟩

theorem profileClassComponent_symmetric_eq_profileCoeff_smul {n : ℕ}
    {p : TensorPowerProfile a n} {f : TensorPower a n → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) n) :
    profileClassComponent (a := a) p f =
      dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) f •
        tensorPowerProfileUnitVector (a := a) p := by
  classical
  have hPf :
      (symmetricProjectionMatrix (a := a) n).mulVec f = f :=
    (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self (a := a) n f).mp hf
  ext x
  have hexp := symmetricProjectionMatrix_mulVec_eq_sum_profileUnitVector (a := a) (n := n) f
  have hsum :
      f = ∑ q : TensorPowerProfile a n,
        dotProduct (star (tensorPowerProfileUnitVector (a := a) q)) f •
          tensorPowerProfileUnitVector (a := a) q := by
    rw [hPf] at hexp
    exact hexp
  by_cases hxp : x ∈ tensorPowerProfileClass (a := a) p
  · calc
      profileClassComponent (a := a) p f x = f x := by simp [profileClassComponent, hxp]
      _ = (∑ q : TensorPowerProfile a n,
            dotProduct (star (tensorPowerProfileUnitVector (a := a) q)) f •
              tensorPowerProfileUnitVector (a := a) q) x := by exact congrFun hsum x
      _ = (dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) f •
              tensorPowerProfileUnitVector (a := a) p) x := by
            have hsumx :
                (∑ q : TensorPowerProfile a n,
                    dotProduct (star (tensorPowerProfileUnitVector (a := a) q)) f •
                      tensorPowerProfileUnitVector (a := a) q) x =
                  (dotProduct (star (tensorPowerProfileUnitVector (a := a) p)) f •
                      tensorPowerProfileUnitVector (a := a) p) x := by
              rw [Finset.sum_apply]
              apply Finset.sum_eq_single_of_mem p (Finset.mem_univ p)
              intro q _ hqp
              have hxq : x ∉ tensorPowerProfileClass (a := a) q := by
                intro hxq
                apply hqp
                apply Subtype.ext
                exact ((mem_tensorPowerProfileClass (a := a) q x).mp hxq).symm.trans
                  ((mem_tensorPowerProfileClass (a := a) p x).mp hxp)
              simp [tensorPowerProfileUnitVector, hxq]
            exact hsumx
  · simp [profileClassComponent, tensorPowerProfileUnitVector, hxp]

theorem unitaryInvariant_matrix_entry_eq_zero_of_typeProfile_ne {n : ℕ}
    (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    {x y : TensorPower a n}
    (hxy : tensorPowerTypeProfile (a := a) n x ≠ tensorPowerTypeProfile (a := a) n y) :
    B x y = 0 := by
  classical
  let px : TensorPowerProfile a n :=
    ⟨tensorPowerTypeProfile (a := a) n x, tensorPowerTypeProfile_mem_profiles (a := a) n x⟩
  let py : TensorPowerProfile a n :=
    ⟨tensorPowerTypeProfile (a := a) n y, tensorPowerTypeProfile_mem_profiles (a := a) n y⟩
  have hpxy : px ≠ py := by
    intro h
    apply hxy
    exact congrArg Subtype.val h
  obtain ⟨phase, hphase, hsep⟩ :=
    profilePhaseCharacter_separates (a := a) (n := n) (p := px) (q := py) hpxy
  let factor :=
    profilePhaseCharacter (a := a) phase px *
      star (profilePhaseCharacter (a := a) phase py)
  have hentry := diagonalPhase_conj_apply (a := a) phase hphase B x y
  rw [hinv (diagonalPhaseUnitary (a := a) phase hphase)] at hentry
  have hxmem : x ∈ tensorPowerProfileClass (a := a) px := by
    simp [px, mem_tensorPowerProfileClass]
  have hymem : y ∈ tensorPowerProfileClass (a := a) py := by
    simp [py, mem_tensorPowerProfileClass]
  have hxphase :
      tensorWordPhase (a := a) phase n x =
        profilePhaseCharacter (a := a) phase px :=
    tensorWordPhase_eq_profilePhaseCharacter_of_mem_class (a := a) phase px hxmem
  have hyphase :
      tensorWordPhase (a := a) phase n y =
        profilePhaseCharacter (a := a) phase py :=
    tensorWordPhase_eq_profilePhaseCharacter_of_mem_class (a := a) phase py hymem
  change B x y =
      tensorWordPhase (a := a) phase n x * B x y *
        star (tensorWordPhase (a := a) phase n y) at hentry
  rw [hxphase, hyphase] at hentry
  have hentry' : B x y = factor * B x y := by
    calc
      B x y = profilePhaseCharacter (a := a) phase px * B x y *
          star (profilePhaseCharacter (a := a) phase py) := hentry
      _ = factor * B x y := by
          dsimp [factor]
          ring
  have hfactor : factor ≠ 1 := by
    exact profilePhaseCharacter_mul_star_ne_one_of_ne (a := a) phase hphase hsep
  have hnonzero : 1 - factor ≠ 0 := by
    intro hzero
    apply hfactor
    exact (sub_eq_zero.mp hzero).symm
  have hmul : (1 - factor) * B x y = 0 := by
    rw [sub_mul, one_mul]
    rw [← hentry']
    ring
  exact (mul_eq_zero.mp hmul).resolve_left hnonzero

theorem unitaryInvariant_mulVec_supported_on_profileClass {n : ℕ}
    (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    {p : TensorPowerProfile a n} {f : TensorPower a n → ℂ}
    (hf : ∀ y, y ∉ tensorPowerProfileClass (a := a) p → f y = 0)
    {x : TensorPower a n} (hx : x ∉ tensorPowerProfileClass (a := a) p) :
    B.mulVec f x = 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hyp : y ∈ tensorPowerProfileClass (a := a) p
  · have hxprof_ne :
        tensorPowerTypeProfile (a := a) n x ≠ tensorPowerTypeProfile (a := a) n y := by
      intro hprof
      apply hx
      rw [mem_tensorPowerProfileClass]
      exact hprof.trans ((mem_tensorPowerProfileClass (a := a) p y).mp hyp)
    rw [unitaryInvariant_matrix_entry_eq_zero_of_typeProfile_ne (a := a) B hinv hxprof_ne]
    simp
  · rw [hf y hyp]
    simp

theorem unitaryInvariant_profileClassComponent_mulVec {n : ℕ}
    (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    (p : TensorPowerProfile a n) (f : TensorPower a n → ℂ) :
    profileClassComponent (a := a) p (B.mulVec f) =
      B.mulVec (profileClassComponent (a := a) p f) := by
  classical
  ext x
  by_cases hxp : x ∈ tensorPowerProfileClass (a := a) p
  · simp only [profileClassComponent, hxp, if_true]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hyp : y ∈ tensorPowerProfileClass (a := a) p
    · simp [profileClassComponent, hyp]
    · have hprof_ne :
          tensorPowerTypeProfile (a := a) n x ≠ tensorPowerTypeProfile (a := a) n y := by
        intro hprof
        apply hyp
        rw [mem_tensorPowerProfileClass]
        exact hprof.symm.trans ((mem_tensorPowerProfileClass (a := a) p x).mp hxp)
      rw [unitaryInvariant_matrix_entry_eq_zero_of_typeProfile_ne (a := a) B hinv hprof_ne]
      simp [profileClassComponent, hyp]
  · have hleft :
        profileClassComponent (a := a) p (B.mulVec f) x = 0 := by
      simp [profileClassComponent, hxp]
    have hright :
        B.mulVec (profileClassComponent (a := a) p f) x = 0 := by
      apply unitaryInvariant_mulVec_supported_on_profileClass (a := a) (p := p) B hinv
      · intro y hy
        simp [profileClassComponent, hy]
      · exact hxp
    rw [hleft, hright]

theorem unitaryInvariant_mulVec_constantProfileUnitVector_eq_diagonal_smul {n : ℕ}
    (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    (z₀ : a) :
    B.mulVec (tensorPowerProfileUnitVector (a := a)
        (constantTensorPowerProfile (a := a) z₀ n)) =
      profileMatrixCoeff (a := a) B
        (constantTensorPowerProfile (a := a) z₀ n)
        (constantTensorPowerProfile (a := a) z₀ n) •
        tensorPowerProfileUnitVector (a := a)
          (constantTensorPowerProfile (a := a) z₀ n) := by
  classical
  let p : TensorPowerProfile a n := constantTensorPowerProfile (a := a) z₀ n
  let x₀ : TensorPower a n := constantTensorPowerWord (a := a) z₀ n
  let vp : TensorPower a n → ℂ := tensorPowerProfileUnitVector (a := a) p
  have hvp_x₀ : vp x₀ = 1 := by
    dsimp [vp, p, x₀]
    exact tensorPowerProfileUnitVector_constant_apply_self (a := a) z₀ n
  have hsupport :
      ∀ x, x ∉ tensorPowerProfileClass (a := a) p → B.mulVec vp x = 0 := by
    intro x hx
    apply unitaryInvariant_mulVec_supported_on_profileClass (a := a) (p := p) B hinv
    · intro y hy
      simp [vp, tensorPowerProfileUnitVector, hy]
    · exact hx
  have hcoeff : profileMatrixCoeff (a := a) B p p = B.mulVec vp x₀ := by
    unfold profileMatrixCoeff
    simp only [dotProduct]
    rw [Finset.sum_eq_single x₀]
    · change star (vp x₀) * B.mulVec vp x₀ = B.mulVec vp x₀
      rw [hvp_x₀]
      simp
    · intro y _ hy
      have hyv : vp y = 0 := by
        dsimp [vp, p, x₀]
        exact tensorPowerProfileUnitVector_constant_apply_of_ne (a := a) z₀ n hy
      change star (vp y) * B.mulVec vp y = 0
      rw [hyv]
      simp
    · intro hx₀
      exact False.elim (hx₀ (Finset.mem_univ x₀))
  ext x
  by_cases hx : x = x₀
  · subst x
    rw [hcoeff]
    change B.mulVec vp x₀ = (B.mulVec vp x₀ • vp) x₀
    simp [Pi.smul_apply, hvp_x₀]
  · have hxnot : x ∉ tensorPowerProfileClass (a := a) p := by
      dsimp [p]
      rw [tensorPowerProfileClass_constant_eq_singleton]
      simpa using hx
    rw [hsupport x hxnot]
    have hvp_x : vp x = 0 := by
      dsimp [vp, p, x₀]
      exact tensorPowerProfileUnitVector_constant_apply_of_ne (a := a) z₀ n hx
    change 0 = (profileMatrixCoeff (a := a) B p p • vp) x
    simp [Pi.smul_apply, hvp_x]

theorem twoLevelTensorGeneratorMatrix_commutes_symmetricProjectionMatrix
    {i j : a} (hij : i ≠ j) (n : ℕ) :
    twoLevelTensorGeneratorMatrix (a := a) i j n *
        symmetricProjectionMatrix (a := a) n =
      symmetricProjectionMatrix (a := a) n *
        twoLevelTensorGeneratorMatrix (a := a) i j n := by
  exact commutes_twoLevelTensorGeneratorMatrix_of_commutes_twoLevelRotation
    (a := a) hij n (symmetricProjectionMatrix (a := a) n)
    (by
      intro θ
      exact unitaryTensorPowerMatrix_mul_symmetricProjectionMatrix
        (a := a) (twoLevelRotationUnitary (a := a) i j θ) n)

theorem twoLevelTensorGeneratorMatrix_mulVec_mem_symmetric_of_mem {n : ℕ}
    {i j : a} (hij : i ≠ j) {f : TensorPower a n → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) n) :
    (twoLevelTensorGeneratorMatrix (a := a) i j n).mulVec f ∈
      symmetricSubspace (a := a) n := by
  classical
  rw [mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self]
  have hfP :
      (symmetricProjectionMatrix (a := a) n).mulVec f = f :=
    (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self (a := a) n f).mp hf
  let G : CMatrix (TensorPower a n) := twoLevelTensorGeneratorMatrix (a := a) i j n
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have hcomm : G * P = P * G :=
    twoLevelTensorGeneratorMatrix_commutes_symmetricProjectionMatrix (a := a) hij n
  calc
    P.mulVec (G.mulVec f) = (P * G).mulVec f := by rw [Matrix.mulVec_mulVec]
    _ = (G * P).mulVec f := by rw [← hcomm]
    _ = G.mulVec (P.mulVec f) := by rw [Matrix.mulVec_mulVec]
    _ = G.mulVec f := by rw [hfP]

theorem twoLevelTensorGeneratorMatrix_mulVec_profileUnitVector_mem_symmetric {n : ℕ}
    {i j : a} (hij : i ≠ j) (q : TensorPowerProfile a n) :
    (twoLevelTensorGeneratorMatrix (a := a) i j n).mulVec
        (tensorPowerProfileUnitVector (a := a) q) ∈ symmetricSubspace (a := a) n := by
  apply twoLevelTensorGeneratorMatrix_mulVec_mem_symmetric_of_mem (a := a) hij
  exact (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self (a := a) n
    (tensorPowerProfileUnitVector (a := a) q)).mpr
    (symmetricProjectionMatrix_mulVec_profileUnitVector (a := a) q)

theorem profileClassComponent_twoLevelTensorGeneratorMatrix_mulVec_profileUnitVector
    {n : ℕ} {i j : a} (hij : i ≠ j)
    (p q : TensorPowerProfile a n) :
    profileClassComponent (a := a) p
        ((twoLevelTensorGeneratorMatrix (a := a) i j n).mulVec
          (tensorPowerProfileUnitVector (a := a) q)) =
      profileVectorCoeff (a := a) (twoLevelTensorGeneratorMatrix (a := a) i j n) p q •
        tensorPowerProfileUnitVector (a := a) p := by
  have hsym :=
    twoLevelTensorGeneratorMatrix_mulVec_profileUnitVector_mem_symmetric
      (a := a) hij q
  simpa [profileVectorCoeff_eq_profileMatrixCoeff, profileMatrixCoeff] using
    profileClassComponent_symmetric_eq_profileCoeff_smul
      (a := a) (p := p) (f :=
        (twoLevelTensorGeneratorMatrix (a := a) i j n).mulVec
          (tensorPowerProfileUnitVector (a := a) q)) hsym

private theorem smul_fun_cancel {ι : Type u} {c : ℂ} (hc : c ≠ 0)
    {f g : ι → ℂ} (h : c • f = c • g) : f = g := by
  ext x
  exact mul_left_cancel₀ hc (congrFun h x)

theorem unitaryInvariant_profileUnitVector_eigen_of_adjacent {n : ℕ}
    (B : CMatrix (TensorPower a n))
    (hinv : ∀ U : Matrix.unitaryGroup a ℂ,
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * B *
        star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) = B)
    {p q : TensorPowerProfile a n} {i j : a}
    (hadj : ProfileAdjacentMove (a := a) p q i j) {lam : ℂ}
    (hq : B.mulVec (tensorPowerProfileUnitVector (a := a) q) =
      lam • tensorPowerProfileUnitVector (a := a) q) :
    B.mulVec (tensorPowerProfileUnitVector (a := a) p) =
      lam • tensorPowerProfileUnitVector (a := a) p := by
  classical
  let G : CMatrix (TensorPower a n) := twoLevelTensorGeneratorMatrix (a := a) i j n
  let vp : TensorPower a n → ℂ := tensorPowerProfileUnitVector (a := a) p
  let vq : TensorPower a n → ℂ := tensorPowerProfileUnitVector (a := a) q
  let c : ℂ := profileVectorCoeff (a := a) G p q
  have hc : c ≠ 0 := by
    simpa [c, G] using
      profileVectorCoeff_twoLevelTensorGenerator_ne_zero_of_adjacent (a := a) hadj
  have hcomm : G * B = B * G := by
    exact commutes_twoLevelTensorGeneratorMatrix_of_commutes_twoLevelRotation
      (a := a) hadj.ne n B
      (by
        intro θ
        exact unitaryInvariant_commutes_unitaryTensorPowerMatrix
          (a := a) B hinv (twoLevelRotationUnitary (a := a) i j θ))
  have hBGvq : B.mulVec (G.mulVec vq) = lam • G.mulVec vq := by
    calc
      B.mulVec (G.mulVec vq) = (B * G).mulVec vq := by rw [Matrix.mulVec_mulVec]
      _ = (G * B).mulVec vq := by rw [← hcomm]
      _ = G.mulVec (B.mulVec vq) := by rw [Matrix.mulVec_mulVec]
      _ = G.mulVec (lam • vq) := by rw [hq]
      _ = lam • G.mulVec vq := by rw [Matrix.mulVec_smul]
  have hcomp :
      profileClassComponent (a := a) p (B.mulVec (G.mulVec vq)) =
        lam • profileClassComponent (a := a) p (G.mulVec vq) := by
    rw [hBGvq]
    ext x
    by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
    · simp [profileClassComponent, hx]
    · simp [profileClassComponent, hx]
  have hcompB :
      B.mulVec (profileClassComponent (a := a) p (G.mulVec vq)) =
        lam • profileClassComponent (a := a) p (G.mulVec vq) := by
    rw [← unitaryInvariant_profileClassComponent_mulVec (a := a) B hinv p (G.mulVec vq)]
    exact hcomp
  have hcompG :
      profileClassComponent (a := a) p (G.mulVec vq) = c • vp := by
    simpa [G, vp, vq, c] using
      profileClassComponent_twoLevelTensorGeneratorMatrix_mulVec_profileUnitVector
        (a := a) hadj.ne p q
  have hcv :
      B.mulVec (c • vp) = lam • (c • vp) := by
    rw [← hcompG]
    exact hcompB
  have hcancel : c • B.mulVec vp = c • (lam • vp) := by
    simpa [Matrix.mulVec_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hcv
  exact smul_fun_cancel hc hcancel

private theorem unitaryTensorPowerMatrix_continuous (n : ℕ) :
    Continuous fun U : Matrix.unitaryGroup a ℂ =>
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  induction n with
  | zero =>
      exact continuous_const
  | succ n ih =>
      change Continuous fun U : Matrix.unitaryGroup a ℂ =>
        Matrix.kronecker (U : CMatrix a)
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
      refine continuous_pi ?_
      intro i
      refine continuous_pi ?_
      intro j
      exact ((continuous_apply j.1).comp ((continuous_apply i.1).comp continuous_subtype_val)).mul
        ((continuous_apply j.2).comp ((continuous_apply i.2).comp ih))

/-- The pointwise integrand of the finite-dimensional unitary Haar twirl. -/
def unitaryTwirlIntegrand (n : ℕ) (A : CMatrix (TensorPower a n))
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (TensorPower a n) :=
  (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) * A *
    star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))

theorem unitaryTwirl_integrand_continuous (n : ℕ) (A : CMatrix (TensorPower a n)) :
    Continuous (unitaryTwirlIntegrand (a := a) n A) := by
  unfold unitaryTwirlIntegrand
  simpa [mul_assoc] using
    ((unitaryTensorPowerMatrix_continuous (a := a) n).matrix_mul continuous_const).matrix_mul
      (Continuous.star (unitaryTensorPowerMatrix_continuous (a := a) n))

theorem unitaryTwirl_integrand_integrable [Nonempty a] (n : ℕ)
    (A : CMatrix (TensorPower a n)) :
    Integrable (unitaryTwirlIntegrand (a := a) n A) (unitaryHaarMeasure (a := a)) :=
  (unitaryTwirl_integrand_continuous (a := a) n A).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Unitary Haar twirl of an operator on `TensorPower a n`. -/
def unitaryTwirl [Nonempty a] (n : ℕ) (A : CMatrix (TensorPower a n)) :
    CMatrix (TensorPower a n) :=
  ∫ U : Matrix.unitaryGroup a ℂ,
    unitaryTwirlIntegrand (a := a) n A U
    ∂unitaryHaarMeasure (a := a)

private noncomputable def cMatrixEntryCLM {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i j : ι) : CMatrix ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℝ] ℂ)

private noncomputable def cMatrixEntryCLM_complex {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i j : ι) : CMatrix ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℂ] ℂ)

private noncomputable def cMatrixQuadraticCLM {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) : CMatrix ι →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (x i) * x j) • cMatrixEntryCLM_complex (ι := ι) i j

private theorem cMatrixQuadraticCLM_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (A : CMatrix ι) :
    cMatrixQuadraticCLM x A = dotProduct (star x) (Matrix.mulVec A x) := by
  simp [cMatrixQuadraticCLM, cMatrixEntryCLM_complex, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

private noncomputable def cMatrixConjTransposeCLM {ι : Type u} [Fintype ι] [DecidableEq ι] :
    CMatrix ι →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A.conjTranspose
       map_add' := by
        intro A B
        rw [Matrix.conjTranspose_add]
       map_smul' := by
        intro c A
        rw [Matrix.conjTranspose_smul]
        simp } :
      CMatrix ι →ₗ[ℝ] CMatrix ι)

private theorem integral_apply_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type u} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (i j : ι) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  simpa [cMatrixEntryCLM] using
    ((cMatrixEntryCLM (ι := ι) i j).integral_comp_comm hf).symm

private theorem integrable_apply_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type u} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (i j : ι) :
    Integrable (fun x => f x i j) μ :=
  (cMatrixEntryCLM (ι := ι) i j).integrable_comp hf

private theorem integral_matrix_mul_left [Nonempty a] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : CMatrix ι) {f : Matrix.unitaryGroup a ℂ → CMatrix ι}
    (hf : Integrable f (unitaryHaarMeasure (a := a))) :
    ∫ U, C * f U ∂unitaryHaarMeasure (a := a) =
      C * ∫ U, f U ∂unitaryHaarMeasure (a := a) := by
  ext i j
  rw [integral_apply_apply (hf := hf.const_mul C)]
  simp only [Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [integral_const_mul, ← integral_apply_apply (hf := hf) k j]
  intro k _
  exact (integrable_apply_apply (hf := hf) k j).const_mul _

private theorem integral_matrix_mul_right [Nonempty a] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {f : Matrix.unitaryGroup a ℂ → CMatrix ι}
    (hf : Integrable f (unitaryHaarMeasure (a := a))) (C : CMatrix ι) :
    ∫ U, f U * C ∂unitaryHaarMeasure (a := a) =
      (∫ U, f U ∂unitaryHaarMeasure (a := a)) * C := by
  ext i j
  rw [integral_apply_apply (hf := hf.mul_const C)]
  simp only [Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [integral_mul_const, ← integral_apply_apply (hf := hf) i k]
  intro k _
  exact (integrable_apply_apply (hf := hf) i k).mul_const _

private theorem integral_matrix_conjTranspose [Nonempty a]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {f : Matrix.unitaryGroup a ℂ → CMatrix ι}
    (hf : Integrable f (unitaryHaarMeasure (a := a))) :
    (∫ U, f U ∂unitaryHaarMeasure (a := a)).conjTranspose =
      ∫ U, (f U).conjTranspose ∂unitaryHaarMeasure (a := a) := by
  simpa using
    ((cMatrixConjTransposeCLM (ι := ι)).integral_comp_comm hf).symm

theorem unitaryTwirl_conj_invariant [Nonempty a] (n : ℕ)
    (A : CMatrix (TensorPower a n)) (V : Matrix.unitaryGroup a ℂ) :
    (unitaryTensorPowerMatrix V n : CMatrix (TensorPower a n)) *
        unitaryTwirl n A *
        star (unitaryTensorPowerMatrix V n : CMatrix (TensorPower a n)) =
      unitaryTwirl n A := by
  let f : Matrix.unitaryGroup a ℂ → CMatrix (TensorPower a n) :=
    unitaryTwirlIntegrand (a := a) n A
  have hf : Integrable f (unitaryHaarMeasure (a := a)) :=
    unitaryTwirl_integrand_integrable (a := a) n A
  let Vn : CMatrix (TensorPower a n) := unitaryTensorPowerMatrix V n
  have htranslate :
      (∫ U : Matrix.unitaryGroup a ℂ,
          Vn * f U * star Vn
          ∂unitaryHaarMeasure (a := a)) =
        ∫ U : Matrix.unitaryGroup a ℂ,
          unitaryTwirlIntegrand (a := a) n A (V * U)
          ∂unitaryHaarMeasure (a := a) := by
    congr 1
    funext U
    simp [f, Vn, unitaryTwirlIntegrand, unitaryTensorPowerMatrix_mul, mul_assoc]
  calc
    Vn * unitaryTwirl n A * star Vn
        = (∫ U, Vn * f U ∂unitaryHaarMeasure (a := a)) * star Vn := by
          rw [unitaryTwirl, integral_matrix_mul_left (a := a) (C := Vn) (hf := hf)]
    _ = ∫ U, Vn * f U * star Vn ∂unitaryHaarMeasure (a := a) := by
          rw [integral_matrix_mul_right (a := a) (hf := hf.const_mul Vn) (C := star Vn)]
    _ = ∫ U : Matrix.unitaryGroup a ℂ,
          unitaryTwirlIntegrand (a := a) n A (V * U)
          ∂unitaryHaarMeasure (a := a) := htranslate
    _ = unitaryTwirl n A := by
          simpa [unitaryTwirl, f] using
            (MeasureTheory.integral_mul_left_eq_self
              (μ := unitaryHaarMeasure (a := a)) f V)

theorem unitaryTwirl_trace [Nonempty a] (n : ℕ) (A : CMatrix (TensorPower a n)) :
    (unitaryTwirl n A).trace = A.trace := by
  rw [unitaryTwirl]
  have hf : Integrable (unitaryTwirlIntegrand (a := a) n A)
      (unitaryHaarMeasure (a := a)) :=
    unitaryTwirl_integrand_integrable (a := a) n A
  calc
    (∫ U : Matrix.unitaryGroup a ℂ, unitaryTwirlIntegrand (a := a) n A U
        ∂unitaryHaarMeasure (a := a)).trace
        = ∑ i, ∫ U : Matrix.unitaryGroup a ℂ,
            unitaryTwirlIntegrand (a := a) n A U i i
            ∂unitaryHaarMeasure (a := a) := by
          simp [Matrix.trace, integral_apply_apply (hf := hf)]
    _ = ∫ U : Matrix.unitaryGroup a ℂ,
          (unitaryTwirlIntegrand (a := a) n A U).trace
          ∂unitaryHaarMeasure (a := a) := by
          change (∑ i, ∫ U : Matrix.unitaryGroup a ℂ,
              unitaryTwirlIntegrand (a := a) n A U i i
              ∂unitaryHaarMeasure (a := a)) =
            ∫ U : Matrix.unitaryGroup a ℂ,
              ∑ i, unitaryTwirlIntegrand (a := a) n A U i i
              ∂unitaryHaarMeasure (a := a)
          exact (MeasureTheory.integral_finsetSum Finset.univ
            (fun i _ => integrable_apply_apply (hf := hf) i i)).symm
    _ = ∫ _U : Matrix.unitaryGroup a ℂ, A.trace
          ∂unitaryHaarMeasure (a := a) := by
          congr 1
          funext U
          simp [unitaryTwirlIntegrand, Matrix.trace_mul_cycle]
    _ = A.trace := by
          simp

theorem unitaryTwirl_conjTranspose [Nonempty a] (n : ℕ)
    (A : CMatrix (TensorPower a n)) :
    (unitaryTwirl n A).conjTranspose = unitaryTwirl n A.conjTranspose := by
  rw [unitaryTwirl, unitaryTwirl]
  have hf : Integrable (unitaryTwirlIntegrand (a := a) n A)
      (unitaryHaarMeasure (a := a)) :=
    unitaryTwirl_integrand_integrable (a := a) n A
  rw [integral_matrix_conjTranspose (a := a) (hf := hf)]
  congr 1
  funext U
  simp [unitaryTwirlIntegrand, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    mul_assoc]

theorem unitaryTwirl_isHermitian_of_isHermitian [Nonempty a] (n : ℕ)
    {A : CMatrix (TensorPower a n)} (hA : A.IsHermitian) :
    (unitaryTwirl n A).IsHermitian := by
  rw [Matrix.IsHermitian, unitaryTwirl_conjTranspose, hA.eq]

private theorem unitaryTwirlIntegrand_posSemidef (n : ℕ)
    {A : CMatrix (TensorPower a n)} (hA : A.PosSemidef)
    (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTwirlIntegrand (a := a) n A U).PosSemidef := by
  simpa [unitaryTwirlIntegrand, Matrix.star_eq_conjTranspose, mul_assoc] using
    hA.mul_mul_conjTranspose_same
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))

private theorem integral_dotProduct_mulVec [Nonempty a]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {f : Matrix.unitaryGroup a ℂ → CMatrix ι}
    (hf : Integrable f (unitaryHaarMeasure (a := a))) (x : ι → ℂ) :
    dotProduct (star x)
        (Matrix.mulVec (∫ U, f U ∂unitaryHaarMeasure (a := a)) x) =
      ∫ U, dotProduct (star x) (Matrix.mulVec (f U) x)
        ∂unitaryHaarMeasure (a := a) := by
  simp_rw [← cMatrixQuadraticCLM_apply x]
  exact
    ((cMatrixQuadraticCLM x).integral_comp_comm hf).symm

theorem unitaryTwirl_posSemidef_of_posSemidef [Nonempty a] (n : ℕ)
    {A : CMatrix (TensorPower a n)} (hA : A.PosSemidef) :
    (unitaryTwirl n A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (unitaryTwirl_isHermitian_of_isHermitian (a := a) n hA.isHermitian) ?_
  intro x
  have hf : Integrable (unitaryTwirlIntegrand (a := a) n A)
      (unitaryHaarMeasure (a := a)) :=
    unitaryTwirl_integrand_integrable (a := a) n A
  rw [unitaryTwirl, integral_dotProduct_mulVec (a := a) (hf := hf) x]
  refine integral_nonneg fun U => ?_
  exact (unitaryTwirlIntegrand_posSemidef (a := a) n hA U).dotProduct_mulVec_nonneg x

end

end QIT
