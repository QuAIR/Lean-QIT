/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State

/-!
# Matrix maps

Finite-dimensional linear maps between matrix spaces. The Choi matrix is the
finite-dimensional representation used to state complete positivity, following
the finite-resource Choi characterization and inverse formula
[Tomamichel2015FiniteResources, prelim.tex:915-931].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A complex-linear map between finite matrix spaces. -/
abbrev MatrixMap (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :=
  CMatrix a →ₗ[Complex] CMatrix b

namespace MatrixMap

/-- Choi matrix of a finite-dimensional matrix map. -/
def choi (Phi : MatrixMap a b) : CMatrix (Prod a b) :=
  fun ij kl => Phi (Matrix.single ij.1 kl.1 (1 : Complex)) ij.2 kl.2

/-- Choi-positive formulation of complete positivity. -/
def IsCompletelyPositive (Phi : MatrixMap a b) : Prop :=
  (choi Phi).PosSemidef

/-- Trace-preserving condition. -/
def IsTracePreserving (Phi : MatrixMap a b) : Prop :=
  forall X : CMatrix a, (Phi X).trace = X.trace

/-- The matrix map whose Choi matrix is the prescribed finite matrix.

This is the explicit inverse to `MatrixMap.choi`, obtained by expanding the
input matrix in matrix units. -/
def ofChoiMatrix (J : CMatrix (Prod a b)) : MatrixMap a b where
  toFun X := fun j j' => ∑ i : a, ∑ i' : a, X i i' * J (i, j) (i', j')
  map_add' X Y := by
    ext j j'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext j j'
    simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem ofChoiMatrix_apply (J : CMatrix (Prod a b)) (X : CMatrix a)
    (j j' : b) :
    ofChoiMatrix J X j j' =
      ∑ i : a, ∑ i' : a, X i i' * J (i, j) (i', j') := by
  rfl

/-- `ofChoiMatrix` is a right inverse to the Choi construction. -/
theorem choi_ofChoiMatrix (J : CMatrix (Prod a b)) :
    choi (ofChoiMatrix J) = J := by
  ext ij kl
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨i', j'⟩
  simp only [choi, ofChoiMatrix, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i']
    · simp [Matrix.single]
    · intro y _ hy
      have hy' : i' ≠ y := hy.symm
      simp [Matrix.single, hy']
    · intro hnot
      simp at hnot
  · intro x _ hx
    have hxi : i ≠ x := hx.symm
    simp [Matrix.single, hxi]
  · intro hnot
    simp at hnot

/-- A positive semidefinite Choi matrix defines a completely positive map. -/
theorem ofChoiMatrix_isCompletelyPositive {J : CMatrix (Prod a b)}
    (hJ : J.PosSemidef) :
    IsCompletelyPositive (ofChoiMatrix J) := by
  rwa [IsCompletelyPositive, choi_ofChoiMatrix]

/-- The unique linear matrix map between unit systems. -/
def unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1} where
  toFun X := fun _ _ => X PUnit.unit PUnit.unit
  map_add' X Y := by
    ext i j
    rfl
  map_smul' r X := by
    ext i j
    rfl

/-- The unit-system matrix map is Choi-positive. -/
theorem unit_isCompletelyPositive :
    IsCompletelyPositive (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) := by
  change (choi (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1})).PosSemidef
  have hchoi :
      choi (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) =
        (1 : CMatrix (PUnit.{u + 1} × PUnit.{v + 1})) := by
    ext x y
    cases x
    cases y
    simp [choi, unit, Matrix.single]
  rw [hchoi]
  exact Matrix.PosSemidef.one

/-- The unit-system matrix map is trace-preserving. -/
theorem unit_isTracePreserving :
    IsTracePreserving (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) := by
  intro X
  simp [unit, Matrix.trace]

/-- The unit-system matrix map preserves positive semidefinite matrices. -/
theorem unit_mapsPositive :
    forall X : CMatrix PUnit.{u + 1}, X.PosSemidef ->
      ((unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) X).PosSemidef := by
  intro X hX
  have hsub :
      (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) X =
        X.submatrix (fun _ : PUnit.{v + 1} => PUnit.unit)
          (fun _ : PUnit.{v + 1} => PUnit.unit) := by
    ext i j
    rfl
  rw [hsub]
  exact hX.submatrix _

/-- Expand a matrix map over matrix units. -/
theorem map_eq_sum_single (Phi : MatrixMap a b) (X : CMatrix a) :
    Phi X = ∑ i : a, ∑ i' : a,
      X i i' • Phi (Matrix.single i i' (1 : Complex)) := by
  calc
    Phi X = Phi (∑ i : a, ∑ i' : a, Matrix.single i i' (X i i')) := by
      congr
      exact Matrix.matrix_eq_sum_single X
    _ = ∑ i : a, ∑ i' : a,
        X i i' • Phi (Matrix.single i i' (1 : Complex)) := by
      simp only [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro i' _
      have hsingle :
          Matrix.single i i' (X i i') =
            X i i' • Matrix.single i i' (1 : Complex) := by
        ext r s
        simp [Matrix.single]
      rw [hsingle, map_smul]

/-- Trace expansion of a matrix map over matrix units. -/
theorem trace_map_eq_sum_single (Phi : MatrixMap a b) (X : CMatrix a) :
    (Phi X).trace = ∑ i : a, ∑ i' : a,
      X i i' * (Phi (Matrix.single i i' (1 : Complex))).trace := by
  rw [map_eq_sum_single Phi X]
  simp [Matrix.trace_sum, Matrix.trace_smul]

/-- Kraus-form matrix map `X ↦ ∑ k, K k * X * (K k)ᴴ`. -/
def ofKraus {κ : Type w} [Fintype κ] (K : κ -> Matrix b a Complex) : MatrixMap a b where
  toFun X := ∑ k : κ, K k * X * (K k).conjTranspose
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    ext i j
    simp [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum]

/-- Kraus-form maps preserve positive semidefinite matrices. -/
theorem ofKraus_mapsPositive {κ : Type w} [Fintype κ] (K : κ -> Matrix b a Complex) :
    forall X : CMatrix a, X.PosSemidef -> (ofKraus K X).PosSemidef := by
  intro X hX
  rw [ofKraus]
  exact Matrix.posSemidef_sum Finset.univ
    (fun k _ => hX.mul_mul_conjTranspose_same (K k))

/-- Heisenberg adjoint of a Kraus-form map. -/
def krausAdjoint {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (E : CMatrix b) : CMatrix a :=
  ∑ k : κ, Matrix.conjTranspose (K k) * E * K k

/-- Trace duality between a Kraus map and its Heisenberg adjoint. -/
theorem ofKraus_trace_duality {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (X : CMatrix a) (E : CMatrix b) :
    (((ofKraus K) X) * E).trace = (X * krausAdjoint K E).trace := by
  simp [ofKraus, krausAdjoint, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  let Kk : Matrix b a ℂ := K k
  let KkH : Matrix a b ℂ := Matrix.conjTranspose Kk
  calc
    ((K k * X * Matrix.conjTranspose (K k)) * E).trace =
        ((Kk * X * KkH) * E).trace := by rfl
    _ = (E * (Kk * X * KkH)).trace := by rw [Matrix.trace_mul_comm]
    _ = ((E * Kk) * (X * KkH)).trace := by
          simp only [Matrix.mul_assoc]
    _ = ((X * KkH) * (E * Kk)).trace := by rw [Matrix.trace_mul_comm]
    _ = (X * (KkH * E * Kk)).trace := by
          simp only [Matrix.mul_assoc]
    _ = (X * (Matrix.conjTranspose (K k) * E * K k)).trace := by rfl

/-- A trace-preserving Kraus map has unital Heisenberg adjoint. -/
theorem krausAdjoint_one_of_tracePreserving {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K)) :
    krausAdjoint K (1 : CMatrix b) = 1 := by
  apply Matrix.ext
  intro i j
  let X : CMatrix a := Matrix.single j i (1 : ℂ)
  have htrace := hTP X
  have hdual :
      (((ofKraus K) X) * (1 : CMatrix b)).trace =
        (X * krausAdjoint K (1 : CMatrix b)).trace :=
    ofKraus_trace_duality K X (1 : CMatrix b)
  rw [Matrix.mul_one] at hdual
  rw [hdual] at htrace
  have hsingle_trace :
      (X * krausAdjoint K (1 : CMatrix b)).trace =
        (krausAdjoint K (1 : CMatrix b)) i j := by
    simp [X, Matrix.trace_single_mul]
  have hXtrace : X.trace = if j = i then (1 : ℂ) else 0 := by
    by_cases hji : j = i
    · subst hji
      simp [X, Matrix.trace, Matrix.single]
    · have hij : i ≠ j := by
        intro hij
        exact hji hij.symm
      simp [X, Matrix.trace, Matrix.single, hji, hij]
  have hOne : (1 : CMatrix a) i j = if j = i then (1 : ℂ) else 0 := by
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : i ≠ j := by
        intro hij
        exact hji hij.symm
      simp [hji, hij]
  calc
    krausAdjoint K (1 : CMatrix b) i j =
        (X * krausAdjoint K (1 : CMatrix b)).trace := hsingle_trace.symm
    _ = X.trace := htrace
    _ = (1 : CMatrix a) i j := by rw [hXtrace, hOne]

/-- Choi matrix of a Kraus-form matrix map, as a sum of rank-one projectors. -/
theorem choi_ofKraus {κ : Type w} [Fintype κ] (K : κ -> Matrix b a Complex) :
    choi (ofKraus K) =
      ∑ k : κ, Matrix.vecMulVec
        (fun x : a × b => K k x.2 x.1)
        (fun x : a × b => star (K k x.2 x.1)) := by
  ext x y
  simp only [choi, ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.single,
    Matrix.vecMulVec]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine (Finset.sum_eq_single y.1 ?_ ?_).trans ?_
  · intro y' _ hy'
    simp [hy', eq_comm]
  · intro hnot
    simp at hnot
  · have hsum :
        (∑ x' : a, K k x.2 x' *
          (if x.1 = x' ∧ y.1 = y.1 then (1 : Complex) else 0)) =
          K k x.2 x.1 := by
      calc
        (∑ x' : a, K k x.2 x' *
          (if x.1 = x' ∧ y.1 = y.1 then (1 : Complex) else 0)) =
            K k x.2 x.1 *
              (if x.1 = x.1 ∧ y.1 = y.1 then (1 : Complex) else 0) := by
          refine Finset.sum_eq_single x.1 ?_ ?_
          · intro x' _ hx'
            have hxne : x.1 ≠ x' := by
              intro h
              exact hx' h.symm
            simp [hxne]
          · intro hnot
            simp at hnot
        _ = K k x.2 x.1 := by
          simp
    rw [hsum]

/-- Choi matrices determine finite-dimensional matrix maps. -/
theorem choi_inj {Phi Psi : MatrixMap a b} (h : choi Phi = choi Psi) :
    Phi = Psi := by
  apply LinearMap.ext
  intro X
  rw [map_eq_sum_single Phi X, map_eq_sum_single Psi X]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro i' _
  have hbasis :
      Phi (Matrix.single i i' (1 : Complex)) =
        Psi (Matrix.single i i' (1 : Complex)) := by
    ext p q
    have hij := congrFun (congrFun h (i, p)) (i', q)
    simpa [choi] using hij
  rw [hbasis]

/-- Choi-positive maps have a finite Kraus representation
[Wilde2011Qst, qit-notes.tex:8242-8262]. -/
theorem exists_kraus_of_choi_psd (Phi : MatrixMap a b)
    (hPhi : IsCompletelyPositive Phi) :
    ∃ K : (a × b) -> Matrix b a Complex, Phi = ofKraus K := by
  let K : (a × b) -> Matrix b a Complex := fun k y x =>
    (hPhi.1.eigenvectorUnitary.val : Matrix (a × b) (a × b) Complex) (x, y) k *
      (Real.sqrt (hPhi.1.eigenvalues k) : Complex)
  use K
  apply choi_inj
  rw [choi_ofKraus]
  convert Matrix.IsHermitian.spectral_theorem hPhi.1 using 1
  ext x y
  simp [K, Matrix.mul_apply, Matrix.vecMulVec]
  ring_nf
  simp [Matrix.sum_apply, Matrix.diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsqrt :
      ((Real.sqrt (hPhi.1.eigenvalues k) : Complex) ^ 2) =
        (hPhi.1.eigenvalues k : Complex) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (hPhi.eigenvalues_nonneg k)]
  rw [hsqrt]

/-- Choi-positive complete positivity maps positive semidefinite inputs to
positive semidefinite outputs via the finite Kraus representation. -/
theorem isCompletelyPositive_mapsPositive (Phi : MatrixMap a b)
    (hPhi : IsCompletelyPositive Phi) :
    forall X : CMatrix a, X.PosSemidef -> (Phi X).PosSemidef := by
  obtain ⟨K, hK⟩ := exists_kraus_of_choi_psd Phi hPhi
  intro X hX
  rw [hK]
  exact ofKraus_mapsPositive K X hX

variable {c : Type w} {d : Type x}
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Matrix-map Kronecker product. This is the linear-map layer for
tensor-product channels [HolevoGiovannetti2012QuantumChannels,
arxive.tex:965-974]. -/
def kron (Phi : MatrixMap a b) (Psi : MatrixMap c d) : MatrixMap (Prod a c) (Prod b d) where
  toFun X := fun bd bd' =>
    Finset.univ.sum fun j : c =>
    Finset.univ.sum fun j' : c =>
    Finset.univ.sum fun i : a =>
    Finset.univ.sum fun i' : a =>
      X (i, j) (i', j') * Phi (Matrix.single i i' (1 : Complex)) bd.1 bd'.1 *
        Psi (Matrix.single j j' (1 : Complex)) bd.2 bd'.2
  map_add' X Y := by
    ext bd bd'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    ext bd bd'
    simp [mul_assoc, Finset.mul_sum]

/-- The Kronecker product of matrix maps acts componentwise on Kronecker
products of matrices. -/
theorem kron_apply_kronecker (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (X : CMatrix a) (Y : CMatrix c) :
    kron Phi Psi (Matrix.kronecker X Y) =
      Matrix.kronecker (Phi X) (Psi Y) := by
  ext bd bd'
  have hPhi := congrFun (congrFun (map_eq_sum_single Phi X) bd.1) bd'.1
  have hPsi := congrFun (congrFun (map_eq_sum_single Psi Y) bd.2) bd'.2
  simp only [Matrix.sum_apply] at hPhi hPsi
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hPhi, hPsi]
  simp [kron, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Trace of the product map on a product matrix unit. -/
theorem trace_kron_single (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (i i' : a) (j j' : c) :
    (kron Phi Psi (Matrix.single (i, j) (i', j') (1 : Complex))).trace =
      (Phi (Matrix.single i i' (1 : Complex))).trace *
        (Psi (Matrix.single j j' (1 : Complex))).trace := by
  rw [single_prod_eq_kronecker_single, kron_apply_kronecker]
  exact Matrix.trace_kronecker _ _

/-- Trace preservation is stable under the Kronecker product of matrix maps. -/
theorem isTracePreserving_kron (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (hPhi : IsTracePreserving Phi) (hPsi : IsTracePreserving Psi) :
    IsTracePreserving (kron Phi Psi) := by
  intro X
  rw [trace_map_eq_sum_single (kron Phi Psi) X]
  calc
    (∑ ac : Prod a c, ∑ ac' : Prod a c,
        X ac ac' * (kron Phi Psi
          (Matrix.single ac ac' (1 : Complex))).trace) =
        ∑ ac : Prod a c, ∑ ac' : Prod a c,
          X ac ac' * ((if ac.1 = ac'.1 then (1 : Complex) else 0) *
            (if ac.2 = ac'.2 then (1 : Complex) else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro ac _
      refine Finset.sum_congr rfl ?_
      intro ac' _
      cases ac with
      | mk i j =>
        cases ac' with
        | mk i' j' =>
          rw [trace_kron_single, hPhi, hPsi, trace_single_one, trace_single_one]
    _ = X.trace := sum_delta_trace X

/-- Choi matrix of a Kronecker product of matrix maps, up to the product-index
reordering between `((a × c) × (b × d))` and `((a × b) × (c × d))`. -/
theorem choi_kron (Phi : MatrixMap a b) (Psi : MatrixMap c d) :
    choi (kron Phi Psi) =
      (Matrix.kronecker (choi Phi) (choi Psi)).submatrix
        (fun x : (a × c) × (b × d) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
        (fun x : (a × c) × (b × d) => ((x.1.1, x.2.1), (x.1.2, x.2.2))) := by
  ext acbd acbd'
  simp only [choi, Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [single_prod_eq_kronecker_single acbd.1.1 acbd'.1.1 acbd.1.2 acbd'.1.2,
    kron_apply_kronecker]
  rfl

/-- Complete positivity is stable under the Kronecker product of matrix maps
in the Choi-positive formulation. -/
theorem isCompletelyPositive_kron (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (hPhi : IsCompletelyPositive Phi) (hPsi : IsCompletelyPositive Psi) :
    IsCompletelyPositive (kron Phi Psi) := by
  rw [IsCompletelyPositive, choi_kron]
  exact (hPhi.kronecker hPsi).submatrix _

end MatrixMap

end

end QIT
