/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.System
public import QIT.Util.Matrix

/-!
# Finite-dimensional states

Density states are positive semidefinite complex matrices with trace one.
Product states are represented by Kronecker products, matching tensor-product
state notation in the source material [Tomamichel2015FiniteResources,
prelim.tex:38-43], product-state usage in [Wilde2011Qst,
qit-notes.tex:7294-7299], and IID factorization in [Wilde2011Qst,
qit-notes.tex:1888-1920].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

/-- A finite-dimensional density state. -/
structure State (a : Type u) [Fintype a] [DecidableEq a] where
  matrix : CMatrix a
  pos : matrix.PosSemidef
  trace_eq_one : matrix.trace = 1

namespace State

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Density states are equal when their matrices are equal. -/
@[ext]
theorem ext {rho sigma : State a} (h : rho.matrix = sigma.matrix) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- The unique density state on the unit system. -/
def unit : State PUnit where
  matrix := 1
  pos := Matrix.PosSemidef.one
  trace_eq_one := by
    rw [Matrix.trace_one]
    norm_num

/-- Product state as a Kronecker product. -/
def prod (rho : State a) (sigma : State b) : State (Prod a b) where
  matrix := Matrix.kronecker rho.matrix sigma.matrix
  pos := rho.pos.kronecker sigma.pos
  trace_eq_one := by
    change (Matrix.kroneckerMap (fun x y => x * y) rho.matrix sigma.matrix).trace = 1
    rw [Matrix.trace_kronecker, rho.trace_eq_one, sigma.trace_eq_one]
    norm_num

/-- `Tr_A (rho_A tensor sigma_B) = sigma_B`. -/
theorem partialTraceA_prod (rho : State a) (sigma : State b) :
    partialTraceA (a := a) (b := b) (rho.prod sigma).matrix = sigma.matrix := by
  rw [prod, partialTraceA_kronecker, rho.trace_eq_one]
  ext j j'
  simp [matrixScale]

/-- `Tr_B (rho_A tensor sigma_B) = rho_A`. -/
theorem partialTraceB_prod (rho : State a) (sigma : State b) :
    partialTraceB (a := a) (b := b) (rho.prod sigma).matrix = rho.matrix := by
  rw [prod, partialTraceB_kronecker, sigma.trace_eq_one]
  ext i i'
  simp [matrixScale]

/-- Marginal state on the first subsystem. -/
def marginalA (rho : State (Prod a b)) : State a where
  matrix := partialTraceB (a := a) (b := b) rho.matrix
  pos := partialTraceB_posSemidef rho.pos
  trace_eq_one := by
    rw [partialTraceB_trace, rho.trace_eq_one]

/-- Marginal state on the second subsystem. -/
def marginalB (rho : State (Prod a b)) : State b where
  matrix := partialTraceA (a := a) (b := b) rho.matrix
  pos := partialTraceA_posSemidef rho.pos
  trace_eq_one := by
    rw [partialTraceA_trace, rho.trace_eq_one]

@[simp]
theorem marginalA_matrix (rho : State (Prod a b)) :
    rho.marginalA.matrix = partialTraceB (a := a) (b := b) rho.matrix := rfl

@[simp]
theorem marginalB_matrix (rho : State (Prod a b)) :
    rho.marginalB.matrix = partialTraceA (a := a) (b := b) rho.matrix := rfl

variable [Fintype c] [DecidableEq c]

/-- Marginal state on `AB` from a left-associated tripartite state `ABC`. -/
def marginalAB (rho : State (Prod (Prod a b) c)) : State (Prod a b) :=
  marginalA rho

/-- Marginal state on `BC` from a left-associated tripartite state `ABC`. -/
def marginalBC (rho : State (Prod (Prod a b) c)) : State (Prod b c) where
  matrix := fun bc bc' =>
    Finset.univ.sum fun i : a => rho.matrix ((i, bc.1), bc.2) ((i, bc'.1), bc'.2)
  pos := by
    let block : a → CMatrix (Prod b c) := fun i =>
      rho.matrix.submatrix
        (fun bc : Prod b c => ((i, bc.1), bc.2))
        (fun bc : Prod b c => ((i, bc.1), bc.2))
    have hsum : (∑ i : a, block i).PosSemidef := by
      classical
      refine Finset.induction_on (s := Finset.univ) ?_ ?_
      · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix (Prod b c)).PosSemidef)
      · intro i s his hs
        simpa [Finset.sum_insert his, block] using
          (rho.pos.submatrix (fun bc : Prod b c => ((i, bc.1), bc.2))).add hs
    convert hsum using 1
    ext bc bc'
    simp [block, Matrix.sum_apply]
  trace_eq_one := by
    rw [← rho.trace_eq_one]
    rw [Matrix.trace]
    change
      (∑ bc : Prod b c, ∑ i : a,
        rho.matrix ((i, bc.1), bc.2) ((i, bc.1), bc.2)) =
      ∑ x : Prod (Prod a b) c, rho.matrix x x
    calc
      (∑ bc : Prod b c, ∑ i : a,
          rho.matrix ((i, bc.1), bc.2) ((i, bc.1), bc.2)) =
          ∑ i : a, ∑ bc : Prod b c,
            rho.matrix ((i, bc.1), bc.2) ((i, bc.1), bc.2) := by
        rw [Finset.sum_comm]
      _ = ∑ x : Prod (Prod a b) c, rho.matrix x x := by
        simp [Fintype.sum_prod_type]

/-- Marginal state on `B` from a left-associated tripartite state `ABC`. -/
def marginalBOfABC (rho : State (Prod (Prod a b) c)) : State b :=
  rho.marginalAB.marginalB

@[simp]
theorem marginalAB_eq_marginalA (rho : State (Prod (Prod a b) c)) :
    rho.marginalAB = rho.marginalA := rfl

@[simp]
theorem marginalBOfABC_eq (rho : State (Prod (Prod a b) c)) :
    rho.marginalBOfABC = rho.marginalAB.marginalB := rfl

/-- IID tensor power of a density state. -/
def tensorPower (rho : State a) : (n : Nat) -> State (TensorPower a n)
  | 0 => unit
  | n + 1 => rho.prod (tensorPower rho n)

/-- The zeroth tensor power is the unit-system state. -/
theorem tensorPower_zero (rho : State a) :
    tensorPower rho 0 = unit := rfl

/-- Successor tensor powers unfold as a product with one more IID factor. -/
theorem tensorPower_succ (rho : State a) (n : Nat) :
    tensorPower rho (n + 1) = rho.prod (tensorPower rho n) := rfl

end State

end

end QIT
